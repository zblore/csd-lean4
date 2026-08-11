/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4
open Lean

/-!
# check-citation-use: does the cited theorem actually do the work?

**Run by `scripts/check-citation-use.sh`. Not part of any lake target** — this is a
checker, not library content.

## What this closes

`check-claim-provenance.sh` mode 4 forces a reason given for a formal restriction to
**name a witness**. That leaves one residue, which the prose audit recorded as needing a
human reader: *a reason that cites a **real** theorem which does not actually support it.*

Part of that residue is mechanisable after all. If a cited theorem genuinely explains why
a result is restricted, the proof should **use** it. A reason clause naming `T` where `T`
is nowhere in the declaration's dependency graph is a claim the Lean itself disagrees
with — and that is checkable, though only from inside Lean, since it needs proof terms
rather than text.

## ⚠️ What it does NOT close

A citation that *is* used but does not establish the stated reason. That is about the
meaning of prose and stays with the reader. This checker narrows the residue; it does not
eliminate it. See `specs/prose-audit.md`.

## Two implementation notes worth keeping

* **`ConstantInfo.value?` returns `none` for theorems** under the module system, so a
  naive traversal silently reports *everything* as unused — which is exactly what the
  first run of this checker did, flagging proofs that demonstrably used their citations.
  The proof term is still reachable via the `.thmInfo` constructor directly.
* The check is **sentence-scoped**. Citations elsewhere in a docstring are navigation
  ("see", "compare", "unlike", "superseded by"), not claims about what the proof uses;
  applying the rule to a whole docstring produces mostly false positives.
-/

namespace CitationUse

def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- Navigation and honesty markers. A clause carrying one of these is not asserting that
the proof depends on what it names. -/
def hasMarker (d : String) : Bool :=
  let s := d.toLower
  (has d "⚠") || (has s "not proved") || (has s "posited") || (has s "intuition") ||
  (has s "informal") || (has s "motivation") || (has s "see ") || (has s "cf.") ||
  (has s "contrast") || (has s "unlike") || (has s "analogue") || (has s "superseded") ||
  (has s "compare") || (has s "predecessor") || (has s "successor")

/-- The same reason/restriction shape `check-claim-provenance.sh` mode 4 uses. Keep the two
in step: this checker validates exactly the citations that guard forces authors to write. -/
def isReason (d : String) : Bool :=
  let s := d.toLower
  ((has s "because") || (has s "since ") || (has s "the reason") || (has s "owing to")) &&
  ((has s "restrict") || (has s "excluded") || (has s "by hand") || (has s "genericity") ||
   (has s "hgen") || (has s "must be stated") || (has s "degenerate"))

/-- Backticked tokens that look like Lean identifiers. -/
def cites (d : String) : List String :=
  let rec go (parts : List String) (i : Nat) (acc : List String) : List String :=
    match parts with
    | [] => acc
    | p :: rest =>
      let keep := i % 2 == 1 && p.any (· == '_') && !(p.any (· == ' ')) && p.length > 3
      go rest (i + 1) (if keep then p :: acc else acc)
  go (d.splitOn "`") 0 []

partial def tryP (env : Environment) (n : Name) (p : Name) : Option Name :=
  if env.contains (p ++ n) then some (p ++ n)
  else match p with
       | .anonymous => none
       | _ => tryP env n p.getPrefix

/-- Is `xs` a suffix of `ys` (as name components)? -/
def isSuffix (xs ys : List Name) : Bool :=
  xs.length ≤ ys.length && (ys.drop (ys.length - xs.length)) == xs

/-- Index of every constant by its LAST name component, built once. Citations here are
routinely written module-qualified (`ContextFixedA7.joint_degenerate_of_sum_eq_one`) or
root-qualified (`Measure.restrict_eq_zero`) rather than as full Lean names, so plain
namespace-walking resolves neither. -/
def suffixIndex (env : Environment) : Std.HashMap Name (Array Name) :=
  env.constants.fold (fun acc n _ =>
    if n.isInternal then acc
    else match n.components.getLast? with
      | none => acc
      | some last => acc.insert last ((acc.getD last #[]).push n)) {}

/-- Resolve a cited string: exact, then owner's enclosing namespaces, then unique suffix
match. Ambiguous suffixes resolve to `none` — guessing between candidates would make the
checker's verdict depend on declaration order. -/
def resolve (env : Environment) (idx : Std.HashMap Name (Array Name))
    (owner : Name) (s : String) : Option Name :=
  let n := s.toName
  if env.contains n then some n
  else match tryP env n owner.getPrefix with
    | some m => some m
    | none =>
      let comps := n.components
      match comps.getLast? with
      | none => none
      | some last =>
        let cands := (idx.getD last #[]).filter (fun c => isSuffix comps c.components)
        if cands.size == 1 then cands[0]? else none

/-- Which of `targets` are reachable from `start` through type and proof-term references. -/
partial def reach (env : Environment) (targets : Std.HashSet Name)
    (stack : List Name) (seen found : Std.HashSet Name) : Std.HashSet Name :=
  match stack with
  | [] => found
  | n :: rest =>
    if seen.contains n then reach env targets rest seen found
    else
      let seen := seen.insert n
      let found := if targets.contains n then found.insert n else found
      if found.size == targets.size then found
      else match env.find? n with
        | none => reach env targets rest seen found
        | some ci =>
          -- NB: `ConstantInfo.value?` is `none` for THEOREMS under the module system.
          -- The proof term is still reachable via `.thmInfo` directly. Getting this wrong
          -- makes the checker report every citation as unused.
          let val : Option Expr := match ci with
            | .thmInfo v => some v.value
            | _ => ci.value?
          let more := ci.type.getUsedConstants ++
            (match val with | some v => v.getUsedConstants | none => #[])
          reach env targets (more.toList ++ rest) seen found

end CitationUse

open CitationUse in
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  let decls := env.constants.fold (fun (acc : Array Name) n _ =>
    if (`CSD).isPrefixOf n && !n.isInternal then acc.push n else acc) #[]
  let idx := suffixIndex env
  let mut nblocks := 0
  let mut bad : Array String := #[]
  let mut unresolved : Array String := #[]
  for n in decls do
    if let some doc ← findDocString? env n then
      let mut reasonCites : List String := []
      for sent in doc.splitOn ". " do
        if isReason sent && !hasMarker sent then
          reasonCites := reasonCites ++ cites sent
      -- Unresolvable citations are reported but NOT fatal: hypothesis names (`h_flow_π`)
      -- are legitimately backticked and resolve to nothing. Found while negative-testing
      -- this checker -- the first probe cited a real theorem under the wrong namespace and
      -- was silently skipped, which is a worse failure than an unused citation.
      for c in reasonCites do
        if (resolve env idx n c).isNone then
          unresolved := unresolved.push s!"  {n}: reason cites `{c}`, which resolves to nothing"
      let targets := reasonCites.filterMap (resolve env idx n)
        |>.foldl (fun (s : Std.HashSet Name) m => s.insert m) {}
      if !targets.isEmpty then
        nblocks := nblocks + 1
        let found := reach env targets [n] {} {}
        for t in targets.toList do
          unless found.contains t do
            bad := bad.push s!"  {n}\n      reason cites, but the proof does NOT use: {t}"
  unless unresolved.isEmpty do
    IO.println "WARN reason clauses cite names that resolve to no constant (hypothesis names"
    IO.println "     are expected here; a typo or a deleted theorem is not):"
    for u in unresolved do IO.println u
  if bad.isEmpty then
    IO.println s!"check-citation-use: OK ({nblocks} reason-clauses with citations, all used)"
  else
    IO.println "FAIL a reason clause names a theorem the proof never uses. Either the reason"
    IO.println "     is wrong, or the citation is navigation and should say so (\"see\","
    IO.println "     \"compare\", \"unlike\", \"superseded by\")."
    for b in bad do IO.println b
    throwError "check-citation-use: {bad.size} unused reason citation(s)"

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4
open Lean

/-!
# check-duplicates: is this already proved somewhere in the corpus?

**Run by `scripts/check-duplicates.sh`. Not part of any lake target.**

## The gap this closes

The corpus is large enough that a lemma can be proved twice without anyone noticing, and
twice on one day is the observed rate rather than the worst case. Both of these happened on
2026-10-12:

* `arenaKick_mk` was written into `CV/ArenaBridge.lean` and **already existed** in
  `CV/CompositeArena.lean`, `FieldConfig`-indexed, with a docstring saying it belonged
  upstream. The compiler caught it only because the two were in the same namespace.
* `Matrix.reindex_mul` and `Matrix.trace_reindex` were being re-derived inline at each site,
  with `CompositeArena.trace_compositeReindex` as a one-off.

Nothing in the gate set looks for this. `check-mathlib-absence.sh` asks whether a staged name
exists **upstream**; this asks whether it exists **here**, twice.

## What it reports

1. **Same statement, different names.** Every `CSD.*` theorem's type, with binder names
   erased so alpha-equivalent statements compare equal, grouped by that type. A group of two or
   more is one statement proved under several names. This is the finding that matters: it is
   exact, so a hit is never a false positive, only sometimes deliberate.
2. **Same final name component, different namespaces.** `foo.bar.baz_mk` and `foo.qux.baz_mk`
   live together happily in Lean and are usually a sign that one of them wants generalising.
   This is a weaker signal and is reported separately.

## What it does not do

It does not look for statements that are *nearly* the same, which is where most real
duplication lives (an `ι`-generic lemma against its `Fin N` instance). Nothing here would have
caught `reindex_mul`, because no declaration existed to compare — the duplication was inside
proofs. Catching that needs a tactic-level measure nobody has, and pretending otherwise would
make this script a false reassurance. It catches exact repeats, which is a real class and the
one that has actually bitten.

Advisory: it prints and exits 0, with the counts pinned in `check-duplicates.sh` so a NEW
duplicate fails the ratchet.
-/

namespace DuplicateScan

/-- Erase binder names, so that two statements differing only in how their variables are
spelled compare equal. Metadata is dropped for the same reason. -/
partial def eraseBinderNames (e : Expr) : Expr :=
  match e with
  | .forallE _ d b bi => .forallE `_ (eraseBinderNames d) (eraseBinderNames b) bi
  | .lam _ d b bi => .lam `_ (eraseBinderNames d) (eraseBinderNames b) bi
  | .letE _ t v b nd => .letE `_ (eraseBinderNames t) (eraseBinderNames v) (eraseBinderNames b) nd
  | .app f a => .app (eraseBinderNames f) (eraseBinderNames a)
  | .mdata _ b => eraseBinderNames b
  | .proj s i b => .proj s i (eraseBinderNames b)
  | e => e

/-- Auto-generated companions of a declaration, which are duplicated by construction. -/
def generated : List String :=
  ["_proof_", "eq_def", "eq_1", "eq_2", "eq_3", "injEq", "noConfusion", "sizeOf",
   "casesOn", "recOn", "below", "brecOn", "match_", "_sunfold", "_unfold", "toCtorIdx",
   "_cstage", "ofNat", "_simp", "_aux"]

/-- A declaration this scan is about: declared in this repository, written by hand, and a
statement rather than data. -/
def isTarget (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  (`CSD).isPrefixOf n
    && !n.isInternal
    && !(generated.any fun s => (n.toString.splitOn s).length > 1)
    && (match ci with | .thmInfo _ => true | _ => false)
    && !(env.isProjectionFn n)
    && !(env.isConstructor n)

def run : CoreM Unit := do
  let env ← getEnv
  -- group by statement, and by final name component
  let mut byType : Std.HashMap Expr (Array Name) := {}
  let mut byLast : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if isTarget env n ci then
      let key := eraseBinderNames ci.type
      byType := byType.insert key ((byType.getD key #[]).push n)
      let last := n.components.getLastD `_
      byLast := byLast.insert last ((byLast.getD last #[]).push n)
  let sameType := byType.toList.filterMap fun (_, ns) =>
    if ns.size ≥ 2 then some ns else none
  -- a group straddling the CSDBridge boundary is an Empirical TWIN, which is the point of
  -- those files; a group inside one namespace is an alias; the rest wants a human
  let isTwin (ns : Array Name) : Bool :=
    (ns.any fun n => (n.toString.splitOn "CSDBridge").length > 1)
      && (ns.any fun n => (n.toString.splitOn "CSDBridge").length == 1)
  let prefixOf (n : Name) : Name := n.getPrefix
  let isAlias (ns : Array Name) : Bool :=
    ns.all fun n => prefixOf n == prefixOf ns[0]!
  -- An ALIAS CITES ITS ORIGINAL: if one member of the group appears in another member's proof
  -- term, there is only one proof in the group and the other names are derived from it. That is
  -- the structural difference between a second name and a second proof, and it is the test that
  -- matters — `b92_nonorthogonal := bb84_states_nonorthogonal` is a name, not a duplication.
  let usesSibling (ns : Array Name) : Bool :=
    ns.any fun n =>
      match env.find? n with
      | some (.thmInfo v) =>
        let used := v.value.getUsedConstants
        ns.any fun m => m != n && used.contains m
      | _ => false
  let twins := sameType.filter isTwin
  let derived := sameType.filter fun ns => !isTwin ns && !isAlias ns && usesSibling ns
  let aliases := sameType.filter fun ns => !isTwin ns && isAlias ns
  let review := sameType.filter fun ns =>
    !isTwin ns && !isAlias ns && !usesSibling ns
  let sameLast := byLast.toList.filterMap fun (c, ns) =>
    if ns.size ≥ 2 then some (c, ns) else none
  IO.println s!"check-duplicates: {byType.size} distinct statements over \
{byType.toList.foldl (fun a (_, ns) => a + ns.size) 0} hand-written CSD theorems"
  IO.println ""
  IO.println s!"(1) SAME STATEMENT, DIFFERENT NAMES: {sameType.length} group(s) = {twins.length} Empirical twin(s) + {aliases.length} in-namespace alias(es) + {derived.length} derived (one cites the other) + {review.length} TO REVIEW"
  IO.println ""
  IO.println s!"  TO REVIEW ({review.length}) — two namespaces, no twin, no alias:"
  for ns in review do
    IO.println s!"    {String.intercalate ", " (ns.toList.map toString)}"
  IO.println ""
  IO.println s!"  derived — one member's proof CITES another, so one proof, several names ({derived.length}):"
  for ns in derived do
    IO.println s!"    {String.intercalate ", " (ns.toList.map toString)}"
  IO.println ""
  IO.println s!"  twins by design ({twins.length}), not findings:"
  for ns in twins do
    IO.println s!"    {String.intercalate ", " (ns.toList.map toString)}"
  IO.println ""
  IO.println s!"  in-namespace aliases ({aliases.length}):"
  for ns in aliases do
    IO.println s!"    {String.intercalate ", " (ns.toList.map toString)}"
  IO.println ""
  IO.println s!"(2) SAME FINAL NAME COMPONENT: {sameLast.length} group(s)"
  for (c, ns) in sameLast do
    IO.println s!"    {c}: {String.intercalate ", " (ns.toList.map toString)}"
  IO.println ""
  IO.println "A group in (1) is one statement proved more than once; generalise one and delete"
  IO.println "the other, or say in the docstring why both are wanted. (2) is a weaker signal."

end DuplicateScan

run_cmd Elab.Command.liftCoreM DuplicateScan.run

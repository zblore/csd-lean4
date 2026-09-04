/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4
open Lean

/-!
# check-axiom-sweep: no `sorry`, no stray axiom, ANYWHERE in the corpus

**Run by `scripts/check-axiom-sweep.sh`. Not part of any lake target.**

## The gap this closes

`lake build` **exits 0 on a `sorry`** — it is a warning, not an error. Verified
2026-08-11 by planting one. So neither build target, nor `lean-action` in CI, fails on a
placeholder proof.

The `#guard_msgs` axiom pins in `CsdLean4/Tests/AxiomAudit/` do catch it, because a
`sorry` shows up as `sorryAx` and breaks the pinned message — but **only for pinned
constants**. There are 1843 pins against roughly 494 modules' worth of declarations, so
the pins are a curated subset, not a cover. A `sorry` in an unpinned lemma passed
everything.

This sweep closes that: it walks **every** `CSD.*` declaration and fails if any of them
transitively depends on an axiom outside the foundational triple
`[propext, Classical.choice, Quot.sound]`. `sorryAx` is called out by name because it is
the one that means "this proof is not a proof".

Complementary to the pins rather than a replacement: the pins record *which* axioms a
named theorem uses, and break loudly on drift. This records that *nothing anywhere* uses
anything else.

## Note

Traversal uses the `.thmInfo` constructor directly — `ConstantInfo.value?` is `none` for
theorems under the module system, so the obvious implementation reports a clean corpus
no matter what is in it. See `scripts/citation-use.lean`.

## The module-system precondition (2026-09-04)

This runs on the environment of `import CsdLean4`, so it sees exactly what that import
EXPORTS. Under the module system a theorem's proof term is exported only from an
`@[expose] public section`. Planted and verified: a module-private `theorem … := by sorry`
consumed by a `public theorem` in a module WITHOUT that section passes this sweep clean.
Every declaring module in the corpus has the section, and `check-axiom-sweep.sh` now
FAILS if one does not — the sweep is a cover only while that holds. The residue this
leaves is dead module-private code (a private `sorry` nothing public consumes) in a module
that does have the section: it is exported there, so in practice it is caught too.
-/

namespace AxiomSweep

/-- The foundational triple. Anything else is a finding. -/
def allowed : Std.HashSet Name :=
  ({} : Std.HashSet Name) |>.insert `propext |>.insert `Classical.choice |>.insert `Quot.sound

/-- Constants referenced by a declaration, through its type and its proof term. -/
def refs (ci : ConstantInfo) : Array Name :=
  let val : Option Expr := match ci with
    | .thmInfo v => some v.value
    | _ => ci.value?
  ci.type.getUsedConstants ++ (match val with | some v => v.getUsedConstants | none => #[])

/-- Walk CSD declarations only. Recursion stops at non-`CSD` constants: a `sorry`
introduced in THIS repository is in a CSD proof term, and axioms referenced by CSD code
are recorded whether or not they are CSD-local. Mathlib's own interior is not re-walked —
traversing it costs minutes and is what the AxiomAudit pins cross-check on the headline
set. Scope stated plainly in `scripts/check-axiom-sweep.sh`. -/
partial def sweep (env : Environment) (stack : List Name)
    (seen : Std.HashSet Name) (found : Std.HashSet Name) : Std.HashSet Name :=
  match stack with
  | [] => found
  | n :: rest =>
    if seen.contains n then sweep env rest seen found
    else
      let seen := seen.insert n
      match env.find? n with
      | none => sweep env rest seen found
      | some ci =>
        match ci with
        | .axiomInfo _ =>
          sweep env rest seen (if allowed.contains n then found else found.insert n)
        | _ =>
          -- Recurse only into CSD constants; still INSPECT every direct reference, so a
          -- disallowed axiom referenced straight from CSD code is caught.
          let direct := refs ci
          let found := direct.foldl (fun acc m =>
            match env.find? m with
            | some (.axiomInfo _) => if allowed.contains m then acc else acc.insert m
            | _ => acc) found
          let next := (direct.filter (fun m => (`CSD).isPrefixOf m)).toList
          sweep env (next ++ rest) seen found

/-- Targeted re-run to attribute a finding to a specific declaration. Same CSD-only
recursion policy as `sweep`, so attribution matches detection. -/
partial def hits (env : Environment) (bad : Std.HashSet Name) (stack : List Name)
    (seen : Std.HashSet Name) : Bool :=
  match stack with
  | [] => false
  | n :: rest =>
    if bad.contains n then true
    else if seen.contains n then hits env bad rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => hits env bad rest seen
      | some ci =>
        let direct := refs ci
        if direct.any (fun m => bad.contains m) then true
        else hits env bad ((direct.filter (fun m => (`CSD).isPrefixOf m)).toList ++ rest) seen

end AxiomSweep

open AxiomSweep in
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  let roots := env.constants.fold (fun (acc : Array Name) n _ =>
    if (`CSD).isPrefixOf n && !n.isInternal then acc.push n else acc) #[]
  let bad := sweep env roots.toList {} {}
  if bad.isEmpty then
    IO.println s!"check-axiom-sweep: OK ({roots.size} CSD declarations, foundational triple only)"
  else
    let hasSorry := bad.contains `sorryAx
    IO.println "FAIL the corpus depends on an axiom outside [propext, Classical.choice, Quot.sound]."
    if hasSorry then
      IO.println "     `sorryAx` is present: a proof somewhere is a placeholder, not a proof."
    IO.println s!"     axioms found: {bad.toList}"
    -- Attribute: report the first few declarations that reach a bad axiom.
    let mut shown := 0
    for r in roots do
      if shown < 10 && hits env bad [r] {} then
        IO.println s!"  {r}"
        shown := shown + 1
    throwError "check-axiom-sweep: {bad.size} disallowed axiom(s) reachable from the corpus"

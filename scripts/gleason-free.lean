/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4
open Lean

/-!
# check-gleason-free: "this module's proofs do not reach Busch", as a checked fact

**Run by `scripts/check-gleason-free.sh`. Not part of any lake target.**

## The gap this closes

56 module headers in this corpus assert Gleason-freeness. For 44 of them the claim is
**structural** — `LF2/EffectGleason.lean` is absent from the transitive import closure, so no
proof of theirs *can* reach Busch — and `check-import-negative.sh` checks exactly that.

The remaining modules import `EffectGleason` transitively (they sit downstream of LF2 or LF3)
and claim something weaker: that their **proof terms route around it**. `SingletKahler.lean`
says it precisely — "the LF3 chain's `weight_eq_P_st` routes through the Busch-free
`OP_p_at_jointEig_eq_P_st_direct` … not through the Busch-mediated twin". An import-closure
guard cannot see that claim, and one re-route through the Busch-mediated twin would make every
one of those headers false, silently. This walks the constant graph instead: for each declared
module, no public declaration it contains may transitively reference a forbidden reconstruction
constant, including the density or matrix constructor rather than just the headline theorem.

Proof-term extraction follows `scripts/axiom-sweep.lean`: `.thmInfo` is
read directly because `ConstantInfo.value?` is `none` for theorems under the module system, so
the obvious implementation reports a clean corpus no matter what is in it. Recursion follows
locally defined constants and declarations from CsdLean4 modules, regardless of their namespace.
External dependencies cannot import this corpus; the repository import-hygiene guard enforces
the corresponding boundary for staged Mathlib modules.

## Scope

`Tests/Witnesses/SingletBell.lean` carries the same claim and is NOT covered here: it lives in
the `CsdLeanTests` target, outside `import CsdLean4`. Its content is the instantiation of
`LF4.ofKählerPreparation`, whose own module IS covered.
-/

namespace GleasonFree

/-- The headline representation theorem. The reconstruction roots below also cover direct
use of its density and matrix constructors. -/
def forbidden : Name := `CSD.LF2.OperationalPackage.effect_gleason_representation

/-- Representation entry points: calling the constructors directly still uses the Busch
reconstruction, even when the headline existence theorem is absent from the proof term. -/
def forbiddenRoots : Array Name := #[
  forbidden,
  `CSD.LF2.OperationalPackage.qdensity,
  `CSD.LF2.OperationalPackage.qmatrix ]

/-- Modules whose proof terms are required to avoid the reconstruction. -/
def declared : Array Name := #[
  `CsdLean4.Empirical.CSD.Contextuality.KCBSVolume,
  `CsdLean4.Empirical.CSD.Contextuality.KS18Volume,
  `CsdLean4.Empirical.CSD.Contextuality.MerminPeresVolume,
  `CsdLean4.Empirical.CSD.ElitzurVaidmanVolume,
  `CsdLean4.Empirical.CSD.MachZehnderVolume,
  `CsdLean4.Empirical.CSD.MalusVolume,
  `CsdLean4.Empirical.CSD.SternGerlachVolume,
  `CsdLean4.Empirical.CSD.VolumeCanonical,
  `CsdLean4.Empirical.Metrology.Ramsey,
  `CsdLean4.LF4.SingletKahler,
  `CsdLean4.LF4.SingletKahlerFlow ]

/-- Constants referenced by a declaration, through its type and its proof term. -/
def refs (ci : ConstantInfo) : Array Name :=
  let val : Option Expr := match ci with
    | .thmInfo v => some v.value
    | _ => ci.value?
  ci.type.getUsedConstants ++ (match val with | some v => v.getUsedConstants | none => #[])

/-- Traverse local declarations and corpus modules irrespective of the declaration namespace.
A helper in a different namespace must not hide a dependency on the reconstruction. -/
def isLocalDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => m == env.mainModule || (`CsdLean4).isPrefixOf m
  | none => true

/-- Does the stack reach any forbidden reconstruction root through local/corpus declarations? -/
partial def reaches (env : Environment) (stack : List Name) (seen : Std.HashSet Name) : Bool :=
  match stack with
  | [] => false
  | n :: rest =>
    if forbiddenRoots.contains n then true
    else if seen.contains n then reaches env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => reaches env rest seen
      | some ci =>
        let direct := refs ci
        if direct.any forbiddenRoots.contains then true
        else reaches env ((direct.filter (isLocalDecl env)).toList ++ rest) seen

/-- Negative fixture outside the CSD namespace: direct use of the density reconstruction. -/
private noncomputable def densityProbe (OP : CSD.LF2.OperationalPackage 2) := OP.qdensity

/-- A second alias tests traversal through a non-CSD local helper. -/
private noncomputable def aliasProbe (OP : CSD.LF2.OperationalPackage 2) := densityProbe OP

/-- A scalar-algebra helper is allowed: importing EffectGleason is not itself forbidden. -/
private theorem benignProbe (OP : CSD.LF2.OperationalPackage 2) :
    OP.p CSD.LF2.Effect.zero = 0 := OP.p_zero

/-- Exercise the rejected routes and an allowed route before scanning the corpus. -/
def checkTraversal (env : Environment) : Bool :=
  forbiddenRoots.all (fun n => env.contains n && reaches env [n] {}) &&
  reaches env [``densityProbe] {} && reaches env [``aliasProbe] {} &&
  !(reaches env [``benignProbe] {})

end GleasonFree

open GleasonFree in
run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  unless checkTraversal env do
    throwError "Gleason-free traversal regression failed (missing root, missed alias, or false positive)"
  -- A declared module that is not in the environment would be checked vacuously: a rename
  -- must fail here, not pass quietly.
  let known := env.header.moduleNames
  let missing := declared.filter (fun m => !known.contains m)
  if !missing.isEmpty then
    IO.println "FAIL declared module(s) not in the environment — a rename left the claim unchecked:"
    for m in missing do IO.println s!"       {m}"
    IO.Process.exit 1
  let mut bad : Array (Name × Name) := #[]
  let mut checked := 0
  for (n, _) in env.constants.toList do
    if !n.isInternal then
      match env.getModuleFor? n with
      | some m =>
        if declared.contains m then
          checked := checked + 1
          if reaches env [n] {} then bad := bad.push (m, n)
      | none => pure ()
  if bad.isEmpty then
    IO.println s!"check-gleason-free: OK ({checked} declaration(s) in {declared.size} module(s), \
none reaching the {forbiddenRoots.size} reconstruction roots; traversal regressions passed)"
  else
    IO.println "FAIL a module whose header says its proofs avoid Busch now reaches it."
    IO.println s!"     forbidden: {forbiddenRoots}"
    for (m, n) in bad[0:20] do
      IO.println s!"       {m}  ::  {n}"
    IO.println "     Fix the route, or correct every header asserting Gleason-freeness."
    IO.Process.exit 1

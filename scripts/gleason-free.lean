/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4
import CsdLean4.Tests.Witnesses.SingletBell
open Lean Matrix
open scoped ComplexOrder

/-!
# Proof dependencies of modules declaring Gleason independence

Run with `lake env lean scripts/gleason-free.lean` after building the library and
`CsdLeanTests`. The modules in `declared` must avoid the complex Busch reconstruction,
the complex/real projection representation theorems, the real frame representation,
and the proved three-dimensional core. Shared linear algebra and polarization remain allowed.

This checks declaration types and proof terms, including `.thmInfo.value`, through all
local and `CsdLean4` declarations regardless of namespace. External dependencies cannot
import this corpus. This is a declared-module guard, not a claim about every corpus module.
Direct, cross-namespace and transitive aliases are exercised before the production scan;
missing roots or missing declared modules fail rather than silently checking an empty scope.
-/

namespace GleasonFree

/-- The headline representation theorem. The reconstruction roots below also cover direct
use of its density and matrix constructors. -/
def forbidden : Name := `CSD.LF2.OperationalPackage.effect_gleason_representation

/-- Representation entry points and the core theorem. Direct reconstruction is forbidden
even when an exported headline theorem is absent from the proof term. -/
def forbiddenRoots : Array Name := #[
  forbidden,
  `CSD.LF2.OperationalPackage.qdensity,
  `CSD.LF2.OperationalPackage.qmatrix,
  `Gleason.coreLemma,
  `Gleason.frameFunction_regular_sphere,
  `Gleason.ProjectionPackage.gleason_representation,
  `Gleason.RealProjectionPackage.real_gleason_representation,
  `Gleason.existsUnique_density_of_frameFunction ]

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
  `CsdLean4.LF4.SingletKahlerFlow,
  `CsdLean4.Tests.Witnesses.SingletBell ]

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

private theorem projectionAlias {N : ℕ} (OP : Gleason.ProjectionPackage N) (hN : 3 ≤ N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re :=
  OP.gleason_representation hN
private theorem realAlias {N : ℕ} (OP : Gleason.RealProjectionPackage N) (hN : 3 ≤ N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℝ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = (ρ * P).trace :=
  OP.real_gleason_representation hN
private theorem frameAlias {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} {W : ℝ}
    (hf : Gleason.IsFrameFunction ℝ f W) (hN : 3 ≤ N) (h0 : ∀ v, ‖v‖ = 1 → 0 ≤ f v) :
    ∃! A : Matrix (Fin N) (Fin N) ℝ, A.PosSemidef ∧ A.trace = W ∧
      ∀ v, ‖v‖ = 1 → f v = dotProduct (⇑v) (A *ᵥ ⇑v) :=
  Gleason.existsUnique_density_of_frameFunction hf hN h0

/-- Repackaging the underlying three-dimensional result must not bypass coreLemma. -/
private theorem coreAlias : Gleason.CoreLemma := fun f _ hf h0 =>
  Gleason.frameFunction_regular_sphere f hf h0

/-- A scalar-algebra helper is allowed: importing EffectGleason is not itself forbidden. -/
private theorem benignProbe (OP : CSD.LF2.OperationalPackage 2) :
    OP.p CSD.LF2.Effect.zero = 0 := OP.p_zero

/-- Exercise the rejected routes and an allowed route before scanning the corpus. -/
def checkTraversal (env : Environment) : Bool :=
  forbiddenRoots.all (fun n => env.contains n && reaches env [n] {}) &&
  reaches env [``densityProbe] {} && reaches env [``aliasProbe] {} &&
  reaches env [``projectionAlias] {} && reaches env [``realAlias] {} &&
  reaches env [``frameAlias] {} && reaches env [``coreAlias] {} &&
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
    IO.println "FAIL a module declaring Gleason independence reaches a forbidden reconstruction root."
    IO.println s!"     forbidden: {forbiddenRoots}"
    for (m, n) in bad[0:20] do
      IO.println s!"       {m}  ::  {n}"
    IO.println "     Fix the route, or correct every header asserting Gleason-freeness."
    IO.Process.exit 1

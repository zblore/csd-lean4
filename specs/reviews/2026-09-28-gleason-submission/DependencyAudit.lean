import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.RealFrame
import CsdLean4.LF2.EffectGleason
open Lean Matrix
open scoped ComplexOrder
namespace LegacyGuard

/-- The forbidden constant, and the modules whose headers claim their proofs avoid it.
The single source of truth, in the house style of `check-import-negative.sh`. -/
def forbidden : Name := `CSD.LF2.OperationalPackage.effect_gleason_representation

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

/-- Does `n` reach `forbidden`, recursing through `CSD.*` constants only? -/
partial def reaches (env : Environment) (stack : List Name) (seen : Std.HashSet Name) : Bool :=
  match stack with
  | [] => false
  | n :: rest =>
    if n == forbidden then true
    else if seen.contains n then reaches env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => reaches env rest seen
      | some ci =>
        let direct := refs ci
        if direct.any (fun m => m == forbidden) then true
        else reaches env ((direct.filter (fun m => (`CSD).isPrefixOf m)).toList ++ rest) seen

end LegacyGuard

namespace SubmissionDependencies

def refs (ci : ConstantInfo) : Array Name :=
  let value := match ci with
    | .thmInfo t => some t.value
    | _ => ci.value?
  ci.type.getUsedConstants ++ (match value with
    | some e => e.getUsedConstants
    | none => #[])

def localDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => m == env.mainModule || (`CsdLean4).isPrefixOf m
  | none => true

partial def reaches (env : Environment) (roots : Array Name)
    (stack : List Name) (seen : Std.HashSet Name) : Bool :=
  match stack with
  | [] => false
  | n :: rest =>
    if roots.contains n then true
    else if seen.contains n then reaches env roots rest seen
    else
      match env.find? n with
      | none => reaches env roots rest (seen.insert n)
      | some ci =>
        let direct := refs ci
        if direct.any roots.contains then true
        else reaches env roots ((direct.filter (localDecl env)).toList ++ rest) (seen.insert n)

theorem projectionAlias {N : ℕ} (OP : Gleason.ProjectionPackage N) (hN : 3 ≤ N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re :=
  OP.gleason_representation hN
theorem realAlias {N : ℕ} (OP : Gleason.RealProjectionPackage N) (hN : 3 ≤ N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℝ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = (ρ * P).trace :=
  OP.real_gleason_representation hN
theorem frameAlias {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} {W : ℝ}
    (hf : Gleason.IsFrameFunction ℝ f W) (hN : 3 ≤ N) (h0 : ∀ v, ‖v‖ = 1 → 0 ≤ f v) :
    ∃! A : Matrix (Fin N) (Fin N) ℝ, A.PosSemidef ∧ A.trace = W ∧
      ∀ v, ‖v‖ = 1 → f v = dotProduct (⇑v) (A *ᵥ ⇑v) :=
  Gleason.existsUnique_density_of_frameFunction hf hN h0
noncomputable def densityAlias (OP : CSD.LF2.OperationalPackage 2) := OP.qdensity
noncomputable def secondAlias (OP : CSD.LF2.OperationalPackage 2) := densityAlias OP

def reconstructionRoots : Array Name := #[
  `CSD.LF2.OperationalPackage.effect_gleason_representation,
  `CSD.LF2.OperationalPackage.qdensity,
  `CSD.LF2.OperationalPackage.qmatrix,
  `Gleason.coreLemma,
  `Gleason.ProjectionPackage.gleason_representation,
  `Gleason.RealProjectionPackage.real_gleason_representation,
  `Gleason.existsUnique_density_of_frameFunction ]

open Elab Command in
run_cmd do
  let env ← getEnv
  for n in reconstructionRoots do
    unless env.contains n do throwError m!"missing reconstruction root {n}"
  for n in [``projectionAlias, ``realAlias, ``frameAlias, ``densityAlias, ``secondAlias] do
    unless reaches env reconstructionRoots [n] {} do throwError m!"missed alias {n}"
    -- Reproduce the gap in the exact current-main traversal.
    if LegacyGuard.reaches env [n] {} then throwError m!"legacy behavior changed for {n}"
    logInfo m!"PASS mutation {n}: legacy misses, expanded traversal detects"
  let pairs : List (Name × Array Name) := [
    (``Gleason.ProjectionPackage.gleason_representation,
      #[`CSD.LF2.OperationalPackage.effect_gleason_representation,
        `CSD.LF2.OperationalPackage.qdensity, `CSD.LF2.OperationalPackage.qmatrix]),
    (``CSD.LF2.OperationalPackage.effect_gleason_representation,
      #[`Gleason.coreLemma, `Gleason.ProjectionPackage.gleason_representation,
        `Gleason.RealProjectionPackage.real_gleason_representation,
        `Gleason.existsUnique_density_of_frameFunction]),
    (``Gleason.RealProjectionPackage.real_gleason_representation,
      #[`Gleason.ProjectionPackage.gleason_representation,
        `CSD.LF2.OperationalPackage.effect_gleason_representation]),
    (``Gleason.existsUnique_density_of_frameFunction,
      #[`Gleason.RealProjectionPackage.real_gleason_representation,
        `Gleason.ProjectionPackage.gleason_representation,
        `CSD.LF2.OperationalPackage.effect_gleason_representation]) ]
  for (n, forbidden) in pairs do
    if reaches env forbidden [n] {} then throwError m!"unexpected representation dependency: {n}"
    logInfo m!"PASS independence {n} avoids {forbidden}"
  unless reaches env #[`Gleason.coreLemma]
      [``Gleason.RealProjectionPackage.real_gleason_representation] {} do
    throwError "positive control failed: real projection must reach coreLemma"
  unless reaches env #[`Gleason.coreLemma] [``Gleason.existsUnique_density_of_frameFunction] {} do
    throwError "positive control failed: real frame must reach coreLemma"
  logInfo "PASS positive controls: both real routes reach the proved core lemma"

end SubmissionDependencies

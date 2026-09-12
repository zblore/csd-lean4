/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.PreparationBarycenter
public import CsdLean4.Mathlib.QuantumInfo.Stinespring
public import CsdLean4.Mathlib.QuantumInfo.CanonicalChannels
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitSection
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Channels from `Σ`-flows: the density operator of a flowed preparation

**Category:** 3-Local (W6 of `specs/qit-chain-scoping.md`; the CSD origin of the channels the
QIT layer reasons about).

W3 (`LF2/PreparationBarycenter.lean`) made the density operator of a preparation the barycentre
`∫ |rep ψ⟩⟨rep ψ| d(π_* μprep)` of rank-one projectors along its projective law. This module
follows that object along an ontic flow. If the flow `Φ : Σ → Σ` **lifts a unitary `U`** through
the projection and the representative — `|rep (π (Φ x))⟩⟨…| = U |rep (π x)⟩⟨…| Uᴴ` — then:

* ★★ `barycenter_flow` — **closed system**: the density operator of the flowed preparation
  `Φ_* μprep` is `U ρ Uᴴ` (`unitaryChannel_apply_barycenter`: the unitary channel of `U` maps
  the density operator of the preparation to that of the flowed preparation);
* ★★ `traceRight_barycenter_flow` — **open system**: for a joint sector `system ⊗ environment`,
  a preparation that is a product with the environment in a ready vector `e₀`, and a flow lifting
  the joint unitary `U`, the *reduced* density operator of the flowed preparation is the
  **Stinespring channel** `ρ ↦ Tr_env (U (ρ ⊗ |e₀⟩⟨e₀|) Uᴴ)` applied to the system's density
  operator. The channel (`stinespringChannel`, a `QuantumInfo.Channel` with Kraus operators the
  environment blocks of the isometry `U · embedEnv e₀`) is *produced by the `Σ`-flow*.

The matrix-level inputs: `barycenterMatrix_map` (barycentre along a pushforward),
`barycenterMatrix_conj` (covariance under a projector-level conjugation),
`barycenterMatrix_kronecker_of_ae` (product preparations have Kronecker barycentres),
`embedEnv` with `embedEnv_conjTranspose_mul` (isometry) and `embedEnv_mul_mul_conjTranspose`
(`E ρ Eᴴ = ρ ⊗ |e₀⟩⟨e₀|`), `outerProduct_toEuclideanLin` (`|U v⟩⟨U v| = U |v⟩⟨v| Uᴴ`).

## The lift hypothesis, and why it is not vacuous

`IsUnitaryLift D Φ rep U` is stated at the **projector** level, so it is phase-free: `rep` is a
choice of unit representative and two representatives of one ray differ by a phase the projector
does not see. It follows from the vector-level lift (`isUnitaryLift_of_vector`) and — the
corpus's actual shape — from `π (Φ x) = U • π x` for the projective action of a unitary, for
**any** unit section `rep` (`isUnitaryLift_of_smul`). That is the `projectable` field of every
`KahlerOnticSetup` (`LF4/NonTrivialSetup.lean`, `unitaryFlowSetup`) and the form of LF5's
`measurementFlow`.

## Honest scope

⚠️ **The survey row misdescribed the corpus.** `specs/qit-chain-scoping.md` W6 called
`RecordLayer.IsJointLift` "the lift of a unitary `U_t` on `ℂᴺ ⊗ ℂᴱ`". It is not: it is the
pointer-arena stroke predicate (pointer agreement plus conserved rates and register). The corpus's
flows-lifting-unitaries are the projective actions above; this module builds W6 on those and on
the abstract `SectorData` interface, at the QM theorem's level of generality.

**Mixed environments.** `traceRight_barycenter_flow` takes the environment in a fixed unit
vector `e₀` (the LF5 apparatus ground state `a₀`). For a mixed environment state `σ`,
`stinespringChannelMixed` is the finite Kraus family `√λₖ · (env-blocks of U · embedEnv vₖ)` over a
spectral decomposition `σ = ∑ₖ λₖ |vₖ⟩⟨vₖ|` (`isHermitian_eq_sum_eigenvalues_smul_outerProduct`),
with action `ρ ↦ Tr_env (U (ρ ⊗ σ) Uᴴ)` (`stinespringChannelMixed_apply`); and ★★
`traceRight_barycenter_flow_prod` is the CSD theorem for a **product preparation** `μS ⊗ μE` on a
product sector: the environment state is then *the barycentre of the environment preparation*
(`barycenterMatrix_prod`, Fubini), and the reduced flowed system state is that channel applied to
the system's density operator.

**The lift hypothesis, discharged for projective actions.** `IsUnitaryLift` says the ontic flow
projects to a unitary action through `rep`; for the corpus's `KahlerOnticSetup` flows it is a
theorem for any unit section (`isUnitaryLift_of_smul`) and unconditional with the canonical
measurable unit section `Projectivization.unitSection` (`isUnitaryLift_unitSection`,
`Mathlib/LinearAlgebra/Projectivization/UnitSection.lean`); for an abstract `SectorData` it is
what "the flow is the lift of `U`" means. Which unitary a given de-isolation flow lifts is the physics (LF5's `vnUnitary` for the
von Neumann coupling; `LF6/DecoherenceChannel.lean` instantiates it).

**Index generality.** The theorems are over any finite index; the projective-action instance
`isUnitaryLift_of_smul` is at `Fin N` because the corpus's projective unitary action
(`Mathlib/LinearAlgebra/Projectivization/Unitary.lean`) is. A joint `Fin N × Fin E` sector is fed
through it by reindexing (`Fin N × Fin E ≃ Fin m`, LF5's device): `isUnitaryLift_of_reindex`
transports the lift along `piLpCongrLeft`, and `LF6/MeasurementFlowChannel.lean` applies it to
LF5's `measurementFlow` (W6′).

References: `specs/qit-chain-scoping.md` (W6, W5); `LF2/PreparationBarycenter.lean` (W3);
`Mathlib/QuantumInfo/Stinespring.lean` (`Channel.ofIsometry`, `ofIsometry_apply`);
`Mathlib/QuantumInfo/CanonicalChannels.lean` (`unitaryChannel`);
`LF5/DilationFromFlow.lean` (`embedGround`, `vnDilationV`); `LF6/Decoherence.lean`
(`decohereReduced`, the instance in `LF6/DecoherenceChannel.lean`).
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace LF2

variable {ι : Type*} [Fintype ι] {Q : Type*} [MeasurableSpace Q]

omit [Fintype ι] [MeasurableSpace Q] in
/-- The entry function is the entry of the projector `|rep p⟩⟨rep p|`. -/
theorem entryFn_eq_outerProduct (rep : Q → EuclideanSpace ℂ ι) (j k : ι) (p : Q) :
    entryFn rep j k p = outerProduct (rep p) j k := rfl

/-- `|U v⟩⟨U v| = U |v⟩⟨v| Uᴴ`. -/
theorem outerProduct_toEuclideanLin [DecidableEq ι] {κ : Type*} (U : Matrix κ ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    outerProduct (Matrix.toEuclideanLin U v) = U * outerProduct v * Uᴴ := by
  ext j k
  simp only [outerProduct, vecMulVec_apply, Matrix.toLpLin_apply, mul_apply,
    conjTranspose_apply, mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, star_sum, star_mul,
    PiLp.toLp_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ### The barycentre under pushforward and under a lifted unitary -/

omit [Fintype ι] in
/-- The barycentre along a pushforward is the barycentre of the composed representative. -/
theorem barycenterMatrix_map {Q' : Type*} [MeasurableSpace Q'] (rep : Q' → EuclideanSpace ℂ ι)
    (hrep_meas : Measurable rep) (f : Q → Q') (hf : Measurable f) (μ : Measure Q) :
    barycenterMatrix rep (Measure.map f μ) = barycenterMatrix (rep ∘ f) μ := by
  ext j k
  simp only [barycenterMatrix, Matrix.of_apply]
  exact integral_map hf.aemeasurable (measurable_entryFn rep hrep_meas j k).aestronglyMeasurable

/-- **Covariance of the barycentre.** If `rep'` is `rep` conjugated by `U` at the projector level
(`|rep' p⟩⟨rep' p| = U |rep p⟩⟨rep p| Uᴴ` for every `p`), the barycentres are conjugate too. -/
theorem barycenterMatrix_conj (rep rep' : Q → EuclideanSpace ℂ ι) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (μ : Measure Q) [IsFiniteMeasure μ] (U : Matrix ι ι ℂ)
    (hlift : ∀ p, outerProduct (rep' p) = U * outerProduct (rep p) * Uᴴ) :
    barycenterMatrix rep' μ = U * barycenterMatrix rep μ * Uᴴ := by
  ext j k
  simp only [barycenterMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hpt : ∀ p, entryFn rep' j k p = ∑ b, (∑ a, U j a * entryFn rep a b p) * star (U k b) := by
    intro p
    rw [entryFn_eq_outerProduct, hlift p]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, entryFn_eq_outerProduct]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun b _ => (integrable_finsetSum _ (fun a _ =>
    (entryFn_integrable rep hrep_unit hrep_meas μ a b).const_mul _)).mul_const _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const, integral_finsetSum _ (fun a _ =>
    (entryFn_integrable rep hrep_unit hrep_meas μ a b).const_mul _)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul]

/-- **Product form.** If the projector of `rep` is a.e. the Kronecker product of the projector
of `repS` with a fixed projector `σ`, the barycentre is the Kronecker product `B_S ⊗ σ`. -/
theorem barycenterMatrix_kronecker_of_ae {n e : Type*}
    (rep : Q → EuclideanSpace ℂ (n × e)) (repS : Q → EuclideanSpace ℂ n)
    (σ : Matrix e e ℂ) (μ : Measure Q)
    (hprod : ∀ᵐ p ∂μ, outerProduct (rep p) = outerProduct (repS p) ⊗ₖ σ) :
    barycenterMatrix rep μ = barycenterMatrix repS μ ⊗ₖ σ := by
  ext ⟨a, i⟩ ⟨b, l⟩
  simp only [barycenterMatrix, Matrix.of_apply, Matrix.kronecker_apply]
  rw [← integral_mul_const]
  refine integral_congr_ae (hprod.mono fun p hp => ?_)
  show entryFn rep (a, i) (b, l) p = entryFn repS a b p * σ i l
  rw [entryFn_eq_outerProduct, entryFn_eq_outerProduct, hp, Matrix.kronecker_apply]

omit [Fintype ι] in
/-- The barycentre only sees the representative almost everywhere. -/
theorem barycenterMatrix_congr_ae (rep rep' : Q → EuclideanSpace ℂ ι) (μ : Measure Q)
    (h : ∀ᵐ p ∂μ, rep p = rep' p) :
    barycenterMatrix rep μ = barycenterMatrix rep' μ := by
  ext j k
  simp only [barycenterMatrix, Matrix.of_apply]
  exact integral_congr_ae (h.mono fun p hp => by simp only [entryFn, hp])

/-- **A preparation living in a subspace has its barycentre there.** If the representative is a.e.
fixed by a Hermitian projector-like matrix `P` (`P (rep p) = rep p`), the barycentre satisfies
`P B Pᴴ = B`. -/
theorem barycenterMatrix_conj_self_of_ae [DecidableEq ι] (rep : Q → EuclideanSpace ℂ ι)
    (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep) (μ : Measure Q)
    [IsFiniteMeasure μ] (P : Matrix ι ι ℂ)
    (h : ∀ᵐ p ∂μ, Matrix.toEuclideanLin P (rep p) = rep p) :
    P * barycenterMatrix rep μ * Pᴴ = barycenterMatrix rep μ := by
  rw [← barycenterMatrix_conj rep (fun p => Matrix.toEuclideanLin P (rep p)) hrep_unit hrep_meas μ P
    (fun p => outerProduct_toEuclideanLin P (rep p))]
  exact barycenterMatrix_congr_ae _ _ μ h

/-! ### The ready-environment embedding and the Stinespring channel of a unitary -/

section Stinespring

variable {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]

variable (n) in
/-- The embedding `ψ ↦ ψ ⊗ e₀` of the system into `system ⊗ environment` with the environment
in the ready vector `e₀`, as a matrix: `(embedEnv n e₀) (a, i) j = δ_{a j} · e₀ i`. -/
def embedEnv (e₀ : EuclideanSpace ℂ e) : Matrix (n × e) n ℂ :=
  Matrix.of fun p j => if p.1 = j then e₀ p.2 else 0

omit [Fintype n] [Fintype e] [DecidableEq e] in
theorem embedEnv_apply (e₀ : EuclideanSpace ℂ e) (p : n × e) (j : n) :
    embedEnv n e₀ p j = if p.1 = j then e₀ p.2 else 0 := rfl

omit [DecidableEq e] in
/-- The embedding is an isometry when `e₀` is a unit vector. -/
theorem embedEnv_conjTranspose_mul (e₀ : EuclideanSpace ℂ e) (he₀ : ‖e₀‖ = 1) :
    (embedEnv n e₀)ᴴ * embedEnv n e₀ = 1 := by
  ext j j'
  simp only [mul_apply, conjTranspose_apply, embedEnv_apply, Fintype.sum_prod_type, one_apply]
  by_cases h : j = j'
  · subst h
    rw [Finset.sum_eq_single j]
    · simp only [if_true]
      have := dotProduct_self_star_of_unit_norm e₀ he₀
      simp only [dotProduct] at this
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · intro a _ ha
      simp [ha]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun i _ => ?_
    by_cases ha : a = j'
    · rw [if_neg (fun h' => h (h'.symm.trans ha))]; simp
    · rw [if_neg ha]; simp

omit [Fintype e] [DecidableEq e] in
/-- Conjugating by the embedding tensors on the ready projector: `E ρ Eᴴ = ρ ⊗ |e₀⟩⟨e₀|`. -/
theorem embedEnv_mul_mul_conjTranspose (e₀ : EuclideanSpace ℂ e) (ρ : Matrix n n ℂ) :
    embedEnv n e₀ * ρ * (embedEnv n e₀)ᴴ = ρ ⊗ₖ outerProduct e₀ := by
  ext ⟨a, i⟩ ⟨b, l⟩
  simp only [mul_apply, conjTranspose_apply, embedEnv_apply, kronecker_apply, outerProduct,
    vecMulVec_apply]
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl, Finset.sum_eq_single a]
    · rw [if_pos rfl]; ring
    · intro c _ hc; rw [if_neg (Ne.symm hc)]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  · intro c _ hc; rw [if_neg (Ne.symm hc)]; simp
  · intro h; exact absurd (Finset.mem_univ b) h

/-- **The Stinespring channel of a unitary with a ready environment**: couple the system to the
environment in `e₀`, evolve the joint by `U`, trace the environment out. Its Kraus operators are
the environment blocks of the isometry `U · embedEnv e₀` (`Channel.ofIsometry`). -/
noncomputable def stinespringChannel (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1)
    (e₀ : EuclideanSpace ℂ e) (he₀ : ‖e₀‖ = 1) : Channel n n e :=
  Channel.ofIsometry (U * embedEnv n e₀) (by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul,
      embedEnv_conjTranspose_mul e₀ he₀])

/-- The channel's action is `ρ ↦ Tr_env (U (ρ ⊗ |e₀⟩⟨e₀|) Uᴴ)`. -/
theorem stinespringChannel_apply (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1)
    (e₀ : EuclideanSpace ℂ e) (he₀ : ‖e₀‖ = 1) (ρ : Matrix n n ℂ) :
    (stinespringChannel U hU e₀ he₀).apply ρ
      = Matrix.traceRight (U * (ρ ⊗ₖ outerProduct e₀) * Uᴴ) := by
  rw [stinespringChannel, Channel.ofIsometry_apply, conjTranspose_mul,
    ← embedEnv_mul_mul_conjTranspose]
  simp only [Matrix.mul_assoc]

omit [Fintype e] [DecidableEq e] in
/-- Embedding the system vector with the ready environment tensors the projectors:
`|ψ ⊗ e₀⟩⟨ψ ⊗ e₀| = |ψ⟩⟨ψ| ⊗ |e₀⟩⟨e₀|`. -/
theorem outerProduct_embedEnv (e₀ : EuclideanSpace ℂ e) (ψ : EuclideanSpace ℂ n) :
    outerProduct (Matrix.toEuclideanLin (embedEnv n e₀) ψ) = outerProduct ψ ⊗ₖ outerProduct e₀ := by
  rw [outerProduct_toEuclideanLin, embedEnv_mul_mul_conjTranspose]

end Stinespring

/-! ### Channels from `Σ`-flows -/

section SigmaFlow

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

variable (D : SectorData SigmaSpace P G)

/-- **A `Σ`-flow lifts a unitary through the representative**, at the projector level: along the
ontic flow `Φ`, the projector `|rep (π x)⟩⟨rep (π x)|` of the projected point is conjugated by
`U`. Phase-free by construction (projectors do not see the phase of `rep`), and implied by the
vector-level lift `rep (π (Φ x)) = U (rep (π x))` (`isUnitaryLift_of_vector`) and by the
projective form `π (Φ x) = U • π x` for a section `rep` (`isUnitaryLift_of_smul`). -/
def IsUnitaryLift (Φ : SigmaSpace → SigmaSpace) (rep : P → EuclideanSpace ℂ ι)
    (U : Matrix ι ι ℂ) : Prop :=
  ∀ x, outerProduct (rep (D.π (Φ x))) = U * outerProduct (rep (D.π x)) * Uᴴ

/-- The vector-level lift implies the projector-level lift. -/
theorem isUnitaryLift_of_vector [DecidableEq ι] (Φ : SigmaSpace → SigmaSpace)
    (rep : P → EuclideanSpace ℂ ι) (U : Matrix ι ι ℂ)
    (h : ∀ x, rep (D.π (Φ x)) = Matrix.toEuclideanLin U (rep (D.π x))) :
    IsUnitaryLift D Φ rep U := fun x => by
  rw [h x, outerProduct_toEuclideanLin]

variable (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]

/-- ★★ **Closed system: the density operator of the flowed preparation is `U ρ Uᴴ`.** If the
ontic flow `Φ` lifts `U`, the barycentre of the flowed preparation `Φ_* μprep` is the barycentre
of `μprep` conjugated by `U` — the Schrödinger-picture evolution of the density operator, derived
from the ontic flow. -/
theorem barycenter_flow (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (rep : P → EuclideanSpace ℂ ι) (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)
    (U : Matrix ι ι ℂ) (hlift : IsUnitaryLift D Φ rep U) :
    barycenterMatrix rep (Measure.map D.π (Measure.map Φ μprep))
      = U * barycenterMatrix rep (Measure.map D.π μprep) * Uᴴ := by
  rw [Measure.map_map D.measurable_π hΦ,
    barycenterMatrix_map rep hrep_meas _ (D.measurable_π.comp hΦ),
    barycenterMatrix_map rep hrep_meas D.π D.measurable_π]
  exact barycenterMatrix_conj (rep ∘ D.π) (rep ∘ D.π ∘ Φ) (fun x => hrep_unit _)
    (hrep_meas.comp D.measurable_π) μprep U hlift

/-- The closed-system statement as a channel: the unitary channel of `U` maps the density
operator of the preparation to the density operator of the flowed preparation. -/
theorem unitaryChannel_apply_barycenter [DecidableEq ι] (Φ : SigmaSpace → SigmaSpace)
    (hΦ : Measurable Φ) (rep : P → EuclideanSpace ℂ ι) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1)
    (hlift : IsUnitaryLift D Φ rep U) :
    (Channel.unitaryChannel U hU).apply (barycenterMatrix rep (Measure.map D.π μprep))
      = barycenterMatrix rep (Measure.map D.π (Measure.map Φ μprep)) := by
  rw [Channel.unitaryChannel_apply, barycenter_flow D μprep Φ hΦ rep hrep_unit hrep_meas U hlift]

/-- ★★ **The channel of a `Σ`-flow (open system).** Let the joint sector carry a representative
`rep : P → ℂⁿ ⊗ ℂᵉ`, let the preparation be a product with the environment in the ready vector
`e₀` (a.e., at the projector level, with system representative `repS`), and let the ontic flow `Φ`
lift the unitary `U`. Then the **reduced** density operator of the flowed preparation is the
Stinespring channel of `U` with ready environment `e₀` applied to the density operator of the
system preparation: `Tr_env ρ(Φ_* μprep) = Φ_U(ρ_S(μprep))`. The channel is produced by the
`Σ`-flow; nothing about it is posited. -/
theorem traceRight_barycenter_flow {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n]
    [DecidableEq e] (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (rep : P → EuclideanSpace ℂ (n × e)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (repS : P → EuclideanSpace ℂ n) (hrepS_meas : Measurable repS)
    (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1) (e₀ : EuclideanSpace ℂ e) (he₀ : ‖e₀‖ = 1)
    (hlift : IsUnitaryLift D Φ rep U)
    (hprod : ∀ᵐ x ∂μprep,
      outerProduct (rep (D.π x)) = outerProduct (repS (D.π x)) ⊗ₖ outerProduct e₀) :
    Matrix.traceRight (barycenterMatrix rep (Measure.map D.π (Measure.map Φ μprep)))
      = (stinespringChannel U hU e₀ he₀).apply (barycenterMatrix repS (Measure.map D.π μprep)) := by
  rw [barycenter_flow D μprep Φ hΦ rep hrep_unit hrep_meas U hlift, stinespringChannel_apply,
    barycenterMatrix_map rep hrep_meas D.π D.measurable_π,
    barycenterMatrix_map repS hrepS_meas D.π D.measurable_π,
    barycenterMatrix_kronecker_of_ae (rep ∘ D.π) (repS ∘ D.π) (outerProduct e₀) μprep hprod]

omit [IsProbabilityMeasure μprep] in
/-- The product hypothesis in vector form: the joint representative is the system representative
embedded with the ready environment, `rep (π x) = repS (π x) ⊗ e₀`, a.e. along the preparation. -/
theorem ae_outerProduct_kronecker_of_embed {n e : Type*} [Fintype n] [DecidableEq n]
    (rep : P → EuclideanSpace ℂ (n × e)) (repS : P → EuclideanSpace ℂ n)
    (e₀ : EuclideanSpace ℂ e)
    (h : ∀ᵐ x ∂μprep, rep (D.π x) = Matrix.toEuclideanLin (embedEnv n e₀) (repS (D.π x))) :
    ∀ᵐ x ∂μprep, outerProduct (rep (D.π x)) = outerProduct (repS (D.π x)) ⊗ₖ outerProduct e₀ :=
  h.mono fun x hx => by rw [hx, outerProduct_embedEnv]

end SigmaFlow

/-! ### The projective unitary action lifts, for any unit section -/

section Projective

variable {N : ℕ} [NeZero N] {SigmaSpace G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace (ℙ ℂ (EuclideanSpace ℂ (Fin N)))]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G (ℙ ℂ (EuclideanSpace ℂ (Fin N)))]
  [MulAction.IsPretransitive G (ℙ ℂ (EuclideanSpace ℂ (Fin N)))]

/-- **Non-vacuity of the lift hypothesis.** If the flow projects to the projective action of a
unitary `U` (`π (Φ x) = U • π x`, the `projectable` shape of every `KahlerOnticSetup`) and `rep`
is a unit section of the projectivisation (`mk (rep p) = p`), then `Φ` lifts `U` at the projector
level: two unit representatives of one ray differ by a phase, which the projector does not see. -/
theorem isUnitaryLift_of_smul (D : SectorData SigmaSpace (ℙ ℂ (EuclideanSpace ℂ (Fin N))) G)
    (Φ : SigmaSpace → SigmaSpace) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (hproj : ∀ x, D.π (Φ x) = U • D.π x)
    (rep : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → EuclideanSpace ℂ (Fin N))
    (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_ne : ∀ p, rep p ≠ 0)
    (hsec : ∀ p, Projectivization.mk ℂ (rep p) (hrep_ne p) = p) :
    IsUnitaryLift D Φ rep U.val := fun x => by
  rw [hproj x]
  set p := D.π x
  have hmk : Projectivization.mk ℂ (rep (U • p)) (hrep_ne _)
      = Projectivization.mk ℂ (Matrix.toEuclideanLin U.val (rep p))
          (Matrix.UnitaryGroup.toEuclideanLin_unitary_ne_zero U (hrep_ne p)) := by
    rw [hsec, ← Matrix.UnitaryGroup.smul_mk_eq_mk U (rep p) (hrep_ne p), hsec]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hmk
  have hconj : outerProduct (rep (U • p))
      = ((c : ℂ) * star (c : ℂ)) • (U.val * outerProduct (rep p) * U.valᴴ) := by
    rw [← hc, Units.smul_def, outerProduct_smul, outerProduct_toEuclideanLin]
  have htr : (U.val * outerProduct (rep p) * U.valᴴ).trace = 1 := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose,
      Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]
    exact outerProduct_trace_of_unit_norm _ (hrep_unit p)
  have hone : (c : ℂ) * star (c : ℂ) = 1 := by
    have h1 := outerProduct_trace_of_unit_norm _ (hrep_unit (U • p))
    rw [hconj, Matrix.trace_smul, htr, smul_eq_mul, mul_one] at h1
    exact h1
  rw [hconj, hone, one_smul]

/-- ★ **The lift hypothesis is unconditional for the projective action.** With the canonical
measurable unit section `Projectivization.unitSection` as representative, every ontic flow that
projects to the action of a unitary lifts it. -/
theorem isUnitaryLift_unitSection (D : SectorData SigmaSpace (ℙ ℂ (EuclideanSpace ℂ (Fin N))) G)
    (Φ : SigmaSpace → SigmaSpace) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (hproj : ∀ x, D.π (Φ x) = U • D.π x) :
    IsUnitaryLift D Φ Projectivization.unitSection U.val :=
  isUnitaryLift_of_smul D Φ U hproj Projectivization.unitSection Projectivization.norm_unitSection
    Projectivization.unitSection_ne_zero Projectivization.mk_unitSection

end Projective

/-! ### A mixed environment: the Stinespring channel over a spectral decomposition -/

section Mixed

variable {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]

/-- A Hermitian matrix is the sum of its eigenvalues times the projectors onto an orthonormal
eigenbasis (the spectral theorem in projector form). -/
theorem isHermitian_eq_sum_eigenvalues_smul_outerProduct {σ : Matrix e e ℂ}
    (hσ : σ.IsHermitian) :
    σ = ∑ k, (RCLike.ofReal (hσ.eigenvalues k) : ℂ) • outerProduct (hσ.eigenvectorBasis k) := by
  conv_lhs => rw [hσ.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, outerProduct,
    vecMulVec_apply, smul_eq_mul, Matrix.star_apply, Function.comp_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

omit [Fintype n] [DecidableEq n] [DecidableEq e] in
theorem traceRight_sum {κ : Type*} (s : Finset κ) (f : κ → Matrix (n × e) (n × e) ℂ) :
    Matrix.traceRight (∑ k ∈ s, f k) = ∑ k ∈ s, Matrix.traceRight (f k) := by
  ext a b
  simp only [Matrix.traceRight_apply, Matrix.sum_apply]
  exact Finset.sum_comm

omit [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e] in
theorem kronecker_sum_right {κ : Type*} (A : Matrix n n ℂ) (s : Finset κ)
    (f : κ → Matrix e e ℂ) : A ⊗ₖ (∑ k ∈ s, f k) = ∑ k ∈ s, A ⊗ₖ f k := by
  ext ⟨a, i⟩ ⟨b, l⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

/-- The square root of a non-negative real, as a complex number, squares to it under `star`. -/
theorem ofReal_sqrt_mul_star {x : ℝ} (hx : 0 ≤ x) :
    ((Real.sqrt x : ℝ) : ℂ) * star ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) := by
  rw [← starRingEnd_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

/-- **The Stinespring channel of a unitary with a mixed environment state `σ`.** Couple the system
to the environment in `σ`, evolve the joint by `U`, trace out the environment:
`ρ ↦ Tr_env (U (ρ ⊗ σ) Uᴴ)`. Its Kraus operators are `√λₖ · (env-block i of U · embedEnv vₖ)` over
a spectral decomposition `σ = ∑ₖ λₖ |vₖ⟩⟨vₖ|`; the trace-preserving constraint is `∑ₖ λₖ = Tr σ = 1`. -/
noncomputable def stinespringChannelMixed (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1)
    {σ : Matrix e e ℂ} (hσ : σ.PosSemidef) (hσ₁ : σ.trace = 1) : Channel n n (e × e) where
  kraus p := ((Real.sqrt (hσ.1.eigenvalues p.2) : ℝ) : ℂ)
    • krausBlock (U * embedEnv n (hσ.1.eigenvectorBasis p.2)) p.1
  tp := by
    rw [Fintype.sum_prod_type_right]
    have hV : ∀ k, (U * embedEnv n (hσ.1.eigenvectorBasis k))ᴴ
        * (U * embedEnv n (hσ.1.eigenvectorBasis k)) = 1 := fun k => by
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul,
        embedEnv_conjTranspose_mul _ (hσ.1.eigenvectorBasis.orthonormal.1 k)]
    have hk : ∀ k, ∑ i, (((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ)
          • krausBlock (U * embedEnv n (hσ.1.eigenvectorBasis k)) i)ᴴ
        * (((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ)
          • krausBlock (U * embedEnv n (hσ.1.eigenvectorBasis k)) i)
        = (RCLike.ofReal (hσ.1.eigenvalues k) : ℂ) • (1 : Matrix n n ℂ) := by
      intro k
      simp_rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Finset.smul_sum,
        sum_krausBlock_conjTranspose_mul, hV k, mul_comm, ofReal_sqrt_mul_star (hσ.eigenvalues_nonneg k)]
      rfl
    simp_rw [hk]
    rw [← Finset.sum_smul, ← hσ.1.trace_eq_sum_eigenvalues, hσ₁, one_smul]

/-- The mixed-environment channel's action is `ρ ↦ Tr_env (U (ρ ⊗ σ) Uᴴ)`. -/
theorem stinespringChannelMixed_apply (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1)
    {σ : Matrix e e ℂ} (hσ : σ.PosSemidef) (hσ₁ : σ.trace = 1) (ρ : Matrix n n ℂ) :
    (stinespringChannelMixed U hU hσ hσ₁).apply ρ = Matrix.traceRight (U * (ρ ⊗ₖ σ) * Uᴴ) := by
  rw [Channel.apply_def]
  simp only [stinespringChannelMixed]
  rw [Fintype.sum_prod_type_right]
  have hk : ∀ k, ∑ i, ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ)
          • krausBlock (U * embedEnv n (hσ.1.eigenvectorBasis k)) i * ρ
        * (((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ)
          • krausBlock (U * embedEnv n (hσ.1.eigenvectorBasis k)) i)ᴴ
        = (RCLike.ofReal (hσ.1.eigenvalues k) : ℂ)
          • Matrix.traceRight (U * (ρ ⊗ₖ outerProduct (hσ.1.eigenvectorBasis k)) * Uᴴ) := by
    intro k
    simp_rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Finset.smul_sum,
      ← traceRight_conj_eq_sum_krausBlock, conjTranspose_mul, ← Matrix.mul_assoc,
      ofReal_sqrt_mul_star (hσ.eigenvalues_nonneg k)]
    rw [Matrix.mul_assoc _ (embedEnv n _) ρ, Matrix.mul_assoc _ (embedEnv n _ * ρ),
      embedEnv_mul_mul_conjTranspose]
    rfl
  simp_rw [hk, ← traceRight_smul]
  rw [← traceRight_sum]
  congr 1
  conv_rhs => rw [isHermitian_eq_sum_eigenvalues_smul_outerProduct hσ.1, kronecker_sum_right, Matrix.mul_sum,
    Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kronecker_smul, Matrix.mul_smul, Matrix.smul_mul]

end Mixed

/-! ### Product preparations: the environment state is the barycentre of the environment -/

section Product

variable {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]

omit [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e] in
/-- **Fubini for barycentres.** If the joint projector is pointwise the Kronecker product of the
system and environment projectors, the barycentre along a product measure is the Kronecker product
of the two barycentres. -/
theorem barycenterMatrix_prod {QS QE : Type*} [MeasurableSpace QS] [MeasurableSpace QE]
    (rep : QS × QE → EuclideanSpace ℂ (n × e)) (repS : QS → EuclideanSpace ℂ n)
    (repE : QE → EuclideanSpace ℂ e)
    (hprod : ∀ p q, outerProduct (rep (p, q)) = outerProduct (repS p) ⊗ₖ outerProduct (repE q))
    (μ : Measure QS) [SFinite μ] (ν : Measure QE) [SFinite ν] :
    barycenterMatrix rep (μ.prod ν) = barycenterMatrix repS μ ⊗ₖ barycenterMatrix repE ν := by
  ext ⟨a, i⟩ ⟨b, l⟩
  simp only [barycenterMatrix, Matrix.of_apply, Matrix.kronecker_apply]
  rw [← integral_prod_mul]
  congr 1
  funext ⟨p, q⟩
  show entryFn rep (a, i) (b, l) (p, q) = entryFn repS a b p * entryFn repE i l q
  rw [entryFn_eq_outerProduct, entryFn_eq_outerProduct, entryFn_eq_outerProduct, hprod p q,
    Matrix.kronecker_apply]

variable {SigmaS SigmaE PS PE G : Type*}
  [MeasurableSpace SigmaS] [MeasurableSpace SigmaE] [Nonempty SigmaS] [Nonempty SigmaE]
  [MeasurableSpace PS] [MeasurableSpace PE]
  [Group G] [MulAction G (SigmaS × SigmaE)] [MulAction G (PS × PE)]
  [MulAction.IsPretransitive G (PS × PE)]

/-- ★★ **The channel of a `Σ`-flow with a mixed environment.** The joint sector is a product
`Σ_sys × Σ_env → P_sys × P_env`; the preparation is the product `μS ⊗ μE` of a system preparation
and an environment preparation; the joint representative is the tensor of the two (projector
level); the ontic flow `Φ` lifts the joint unitary `U`. Then the reduced density operator of the
flowed preparation is the mixed-environment Stinespring channel — with **environment state the
barycentre of the environment preparation** — applied to the density operator of the system
preparation. -/
theorem traceRight_barycenter_flow_prod (D : SectorData (SigmaS × SigmaE) (PS × PE) G)
    (πS : SigmaS → PS) (πE : SigmaE → PE) (hπS : Measurable πS) (hπE : Measurable πE)
    (hπ : D.π = Prod.map πS πE)
    (μS : Measure SigmaS) [IsProbabilityMeasure μS] (μE : Measure SigmaE) [IsProbabilityMeasure μE]
    (Φ : SigmaS × SigmaE → SigmaS × SigmaE) (hΦ : Measurable Φ)
    (rep : PS × PE → EuclideanSpace ℂ (n × e)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep)
    (repS : PS → EuclideanSpace ℂ n)
    (repE : PE → EuclideanSpace ℂ e) (hrepE_unit : ∀ q, ‖repE q‖ = 1)
    (hrepE_meas : Measurable repE)
    (hprod : ∀ p q, outerProduct (rep (p, q)) = outerProduct (repS p) ⊗ₖ outerProduct (repE q))
    (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1)
    (hlift : IsUnitaryLift D Φ rep U) :
    haveI : IsProbabilityMeasure (Measure.map πE μE) :=
      Measure.isProbabilityMeasure_map' hπE.aemeasurable
    Matrix.traceRight (barycenterMatrix rep (Measure.map D.π (Measure.map Φ (μS.prod μE))))
      = (stinespringChannelMixed U hU
          (barycenterMatrix_posSemidef repE hrepE_unit hrepE_meas (Measure.map πE μE))
          (barycenterMatrix_trace repE hrepE_unit hrepE_meas (Measure.map πE μE))).apply
        (barycenterMatrix repS (Measure.map πS μS)) := by
  have : IsProbabilityMeasure (Measure.map πE μE) :=
    Measure.isProbabilityMeasure_map' hπE.aemeasurable
  rw [barycenter_flow D (μS.prod μE) Φ hΦ rep hrep_unit hrep_meas U hlift,
    stinespringChannelMixed_apply, hπ, ← Measure.map_prod_map μS μE hπS hπE,
    barycenterMatrix_prod rep repS repE hprod]

end Product

/-! ### Reindexing the lift -/

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Transporting a vector along `piLpCongrLeft e` transports its projector along `reindex e e`. -/
theorem outerProduct_piLpCongrLeft (e : ι ≃ κ) (v : EuclideanSpace ℂ ι) :
    outerProduct (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e v)
      = Matrix.reindex e e (outerProduct v) := by
  ext a b
  rfl

/-- `reindex e e` is multiplicative and commutes with `ᴴ`, so it respects conjugation. -/
theorem reindex_mul_mul_conjTranspose (e : ι ≃ κ) (U A : Matrix ι ι ℂ) :
    Matrix.reindex e e (U * A * Uᴴ)
      = Matrix.reindex e e U * Matrix.reindex e e A * (Matrix.reindex e e U)ᴴ := by
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **The lift transports along a reindexing.** If the representative on the reindexed space is
the transport of `rep`, a lift of the reindexed unitary is a lift of the unitary. -/
theorem isUnitaryLift_of_reindex (D : SectorData SigmaSpace P G) (Φ : SigmaSpace → SigmaSpace)
    (e : ι ≃ κ) (rep : P → EuclideanSpace ℂ ι) (U : Matrix ι ι ℂ)
    (h : IsUnitaryLift D Φ (fun p => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (rep p))
      (Matrix.reindex e e U)) :
    IsUnitaryLift D Φ rep U := fun x => by
  have hx := h x
  simp only [outerProduct_piLpCongrLeft, ← reindex_mul_mul_conjTranspose] at hx
  exact (Matrix.reindex e e).injective hx

end Reindex

end LF2
end CSD

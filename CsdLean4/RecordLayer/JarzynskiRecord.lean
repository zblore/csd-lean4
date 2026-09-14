/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DrivenTwoTime
public import CsdLean4.Thermo.Jarzynski
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerFlow

/-!
# TH5d: the Jarzynski equality at the `Σ` level — the record-layer work statistics are TH5a's

**Category:** 7-SigmaLayer (the record layer — thermodynamics stated on `Σ`, not on bare
matrices; `specs/thermo-plan.md` TH5, `specs/BACKLOG.md` ▶ OPEN QUEUE #4; the first
thermodynamic consumer of Q29(e)).

**Glossary:** https://glossary.constraintsurfacedynamics.com/jarzynski-equality/

## What "at the `Σ` level" means here

TH5a (`Thermo/Jarzynski.lean`) is a theorem about matrices: a joint law `tpmLaw` DEFINED as
Gibbs weight × transition probability, and the identity `∑ tpmLaw · e^{−βW} = Z₁/Z₀`. This
module runs the same protocol as **records on the sector** and proves that the record
statistics ARE `tpmLaw`:

* the preparation is the Gibbs state as a mixed preparation on the swap arena
  (`gibbsDensity`, `mixedReadyPrep` — the spectral two-stage sampling of `MixedSwap.lean`),
  with the first bank calibrated to the energy eigenrays of `H₀` (`rotatedBank`);
* the first readout is the energy context of `H₀` — the apparatus reading the eigenbasis
  `hH₀.eigenvectorBasis` (`basisContext`, `RotatedContext.lean`);
* between the readouts the system is DRIVEN: its ontic base point moves by the unitary `U`
  acting on `ℂℙ^{N−1}`, the pointer fibre untouched (`baseLift (U • ·)` = the corpus's `U(N)`
  action on `Σ`, `baseLift_unitary_smul`), as the `driveStage` of `DrivenTwoTime.lean`;
* the second readout is the energy context of `H₁`.

★★ `sigma_tpm_law`: the driven two-stage preparation gives the joint record sector
`(energy record i at t₁, energy record j at t₂)` exactly the mass `tpmLaw hH₀ hH₁ U β i j`. Not
a definition — the Gibbs weight is the mixed dynamical Born weight of the first readout
(`traceForm_gibbsDensity_energy` through `driven_mixed_two_time_born`), and the transition
probability is the second context's rate at the DRIVEN collapsed state
(`basisContext_rate_smul`). No positivity hypothesis: Gibbs weights are strictly positive
(`gibbsWeight_pos`), so the conditioning is always licensed.

★★ `sigma_jarzynski`: hence `∑ᵢⱼ P_Σ(i, j) · e^{−βW(i,j)} = Z₁/Z₀` for the record probabilities
`P_Σ`, with ★★ `sigma_jarzynski_freeEnergy` (`= e^{−βΔF}` in TH3's free energies) and
★ `sigma_mean_work_ge_freeEnergy_sub` (the second law of the driven process, on `Σ`);
`sum_tpmSigmaSector` (the record law is a probability law), `sigma_first_energy_record` (the
first readout's records carry the Gibbs weights; no retro-action from the drive).

## Q29(e) consumed

★★ `sigma_tpm_law_hamiltonianFlow`, ★★ `sigma_jarzynski_hamiltonianFlow`: the drive written as
the MANIFOLD Hamiltonian flow `IsSymplectic.hamiltonianFlow` of the Schrödinger Hamiltonian
`−2⟨H_d⟩` for the Fubini–Study form (`HamiltonianFlowVolume.lean`), for a driving Hamiltonian
`H_d` over a time `τ`. Q29(e)'s identification `hamiltonianFlow_schrodingerHamiltonian` turns it
into `exp(−iτH_d) • ·`, and the theorem above applies. This is the first thermodynamic statement
in the corpus whose driving is the sector's own Hamiltonian flow rather than a matrix.

## CSD reading

Work is what the two energy records disagree by; the exponential average over the driven
record chain is a state function of the two equilibrium endpoints. Nothing in the protocol is
a matrix identity: the Gibbs weights are the Born weights the first record dynamics assigns to
the mixed preparation, the transition weights are the Born weights the second record dynamics
assigns to the relocated-and-driven state, and the equality is bookkeeping on the doubly
stochastic transition matrix that unitarity forces (TH5a). The thermodynamics of a driven
process lives on the record layer.

## ⚠️ Honest scope

* **Liouville is not consumed by the theorem, and the row's phrasing is corrected.** The row
  (BACKLOG #4) reads "an absolutely continuous preparation density is transported". The Gibbs
  preparation here is the spectral mixture of Diracs on the base (`mixedReadyPrep`, Haar on
  the fibre), and the collapsed states are Diracs; the drive transports them pointwise. The
  manifold-level Liouville theorem (`fsVolume_map_hamiltonianFlow`) is what Q29(e) is FOR, but
  the two-point-measurement law needs only the flow's identification, not its
  measure-preservation. An absolutely-continuous-density formulation of the Gibbs preparation
  (`ρ_ep dμ_FS`, W3's form) would consume Liouville; it is not the corpus's canonical mixed
  preparation and is not built here.
* The drive is a single unitary `U` (or `exp(−iτH_d)` for a constant driving Hamiltonian);
  a time-dependent protocol is the ordered product of such steps and is not composed here.
* Closed driven system, finite dimension, projective energy readouts in the spectral eigenbases,
  the same `β` at both ends — TH5a's scope; the `[NeZero N]` of the record layer stands in for
  TH3's `[Nonempty n]`.
* **Gleason-free, structurally.** `LF2/EffectGleason.lean` is absent from this module's
  transitive import closure (declared in `scripts/check-import-negative.sh`), so no proof here
  can reach the effect-Gleason representation: the Born weights are the record dynamics'.
  `trace_mul_outerProduct'` restates that module's `trace_mul_outerProduct` on a general index
  for exactly this reason (rule-of-two note: rehome to `LF2/BornWrapper.lean` when next
  touched).

## References

`specs/thermo-plan.md` TH5; `specs/BACKLOG.md` (▶ OPEN QUEUE #4 = TH5d; Q29(e));
`specs/generator-layer-scoping.md` §11 (Q29); `Thermo/Jarzynski.lean` (TH5a: `tpmLaw`,
`tpmTransition_eq`, `gibbsWeight_eq_re_born`, `jarzynski`, `jarzynski_freeEnergy`,
`mean_work_ge_freeEnergy_sub`); `Thermo/FreeEnergy.lean` (TH3: `gibbsState`, `gibbsWeight_pos`,
`gibbsState_posDef`, `gibbsState_trace`); `RecordLayer/DrivenTwoTime.lean`
(`driven_mixed_two_time_born`, `baseLift`); `RecordLayer/RotatedContext.lean`
(`basisContext_rate_mk`); `RecordLayer/RotatedSwap.lean` (`basisPoint`);
`Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceSchrodingerFlow.lean`
(`hamiltonianFlow_schrodingerHamiltonian`, Q29(e)); `LF4/ProjectedDynamics.lean`
(`schrodingerUnitary`); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped ComplexOrder

namespace CSD.RecordLayer

open CSD.Thermo CSD.LF2 CSD.SigmaLayer

/-- `tr(R · ∣v⟩⟨v∣) = ⟨v, R v⟩` on a general finite index (`trace_mul_outerProduct` of
`LF2/EffectGleason.lean`, restated to keep that module out of this closure). -/
lemma trace_mul_outerProduct' {ι : Type*} [Fintype ι] (R : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    (R * outerProduct v).trace = star (⇑v) ⬝ᵥ (R *ᵥ (⇑v)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outerProduct,
    Matrix.vecMulVec_apply, dotProduct, Pi.star_apply, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

variable {N : ℕ} [NeZero N] {H₀ H₁ : Matrix (Fin N) (Fin N) ℂ}

/-! ### The Gibbs preparation and the energy contexts -/

/-- **The Gibbs state as a density operator** (TH3's `gibbsState`, packaged for the record
tier). -/
noncomputable def gibbsDensity (hH₀ : H₀.IsHermitian) (β : ℝ) : DensityOperator N where
  M           := gibbsState H₀ hH₀ β
  isHermitian := gibbsState_isHermitian H₀ hH₀ β
  nonneg      := (gibbsState_posDef H₀ hH₀ β).posSemidef
  trace_one   := gibbsState_trace H₀ hH₀ β

@[simp] theorem gibbsDensity_M (hH₀ : H₀.IsHermitian) (β : ℝ) :
    (gibbsDensity hH₀ β).M = gibbsState H₀ hH₀ β := rfl

/-- **The Gibbs weight is the record tier's Born pairing at the energy outcome**:
`Tr(ρ_β ∣e₀ᵢ⟩⟨e₀ᵢ∣) = e^{−βE₀ᵢ}/Z₀`. -/
theorem traceForm_gibbsDensity_energy (hH₀ : H₀.IsHermitian) (β : ℝ) (i : Fin N) :
    traceForm (gibbsDensity hH₀ β)
        (rankOneEffect (hH₀.eigenvectorBasis i) (hH₀.eigenvectorBasis.orthonormal.1 i))
      = gibbsWeight H₀ hH₀ β (hH₀.eigenvalues i) := by
  rw [traceForm, gibbsWeight_eq_re_born]
  congr 1
  exact trace_mul_outerProduct' (gibbsState H₀ hH₀ β) (hH₀.eigenvectorBasis i)

omit [NeZero N] in
/-- **The second energy readout's rate at the driven collapsed state is the transition
probability**: the context reading the eigenbasis of `H₁`, evaluated at `U • [e₀ᵢ]`, assigns
outcome `j` the weight `‖⟨e₁ⱼ, U e₀ᵢ⟩‖² = tpmTransition i j`. -/
theorem basisContext_rate_smul (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (i j : Fin N) :
    (basisContext hH₁.eigenvectorBasis).rate (U • basisPoint hH₀.eigenvectorBasis i) j
      = tpmTransition hH₀ hH₁ U i j := by
  have hnorm : ‖Matrix.toEuclideanLin U.val (hH₀.eigenvectorBasis i)‖ = 1 := by
    rw [Projectivization.norm_toEuclideanLin_unitary, hH₀.eigenvectorBasis.orthonormal.1 i]
  rw [basisPoint, Matrix.UnitaryGroup.smul_mk_eq_mk, basisContext_rate_mk _ _ _ hnorm j,
    tpmTransition_eq]
  congr 2
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-! ### The `Σ`-level two-point-measurement protocol -/

/-- **The `Σ`-level two-point-measurement preparation**: the Gibbs state of `H₀` as the mixed
preparation on the two-stage arena, the first bank calibrated to the energy eigenrays of `H₀`. -/
noncomputable def tpmSigmaPrep (hH₀ : H₀.IsHermitian) (β : ℝ) :
    Measure (TwoStageArena (LF4.KSigma N) N) :=
  rotatedMixedTwoPrep hH₀.eigenvectorBasis (gibbsDensity hH₀ β)

instance (hH₀ : H₀.IsHermitian) (β : ℝ) : IsProbabilityMeasure (tpmSigmaPrep hH₀ β) := by
  unfold tpmSigmaPrep
  infer_instance

/-- **The `Σ`-level joint record sector**: the initial states destined to display energy record
`i` (in the eigenbasis of `H₀`) at `t₁` and, after the drive `U` on the sector, energy record `j`
(in the eigenbasis of `H₁`) at `t₂`. -/
noncomputable def tpmSigmaSector (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (i j : Fin N) : Set (TwoStageArena (LF4.KSigma N) N) :=
  drivenJointRecordSector (basinIndex (basisContext hH₀.eigenvectorBasis))
    (baseLift (fun p : LF4.CPN N => U • p)) (basinIndex (basisContext hH₁.eigenvectorBasis)) i j

/-- ★★ **TH5d, the law: the record statistics of the `Σ`-level protocol ARE `tpmLaw`.** The
driven two-stage preparation gives the joint sector (energy record `i` at `t₁`, energy record
`j` at `t₂`) exactly the mass `gibbsWeight (E₀ i) · ‖⟨e₁ j, U e₀ i⟩‖²`. No positivity
hypothesis: Gibbs weights are strictly positive. -/
theorem sigma_tpm_law (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (β : ℝ) (i j : Fin N) :
    tpmSigmaPrep hH₀ β (tpmSigmaSector hH₀ hH₁ U i j)
      = ENNReal.ofReal (tpmLaw hH₀ hH₁ U β i j) := by
  rw [tpmSigmaPrep, tpmSigmaSector,
    driven_mixed_two_time_born hH₀.eigenvectorBasis (gibbsDensity hH₀ β)
      (continuous_const_smul U).measurable (basisContext hH₁.eigenvectorBasis) i j
      (by rw [traceForm_gibbsDensity_energy]; exact (gibbsWeight_pos H₀ hH₀ β _).ne'),
    traceForm_gibbsDensity_energy, basisContext_rate_smul, tpmLaw,
    ENNReal.ofReal_mul (gibbsWeight_pos H₀ hH₀ β _).le]

/-- The `Σ`-level record law is a probability law on the outcome pairs. -/
theorem sum_tpmSigmaSector (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (β : ℝ) :
    ∑ i, ∑ j, tpmSigmaPrep hH₀ β (tpmSigmaSector hH₀ hH₁ U i j) = 1 := by
  simp_rw [sigma_tpm_law]
  rw [Finset.sum_congr rfl fun i _ =>
      (ENNReal.ofReal_sum_of_nonneg fun j _ => tpmLaw_nonneg hH₀ hH₁ U β i j).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => tpmLaw_nonneg hH₀ hH₁ U β i j,
    sum_tpmLaw, ENNReal.ofReal_one]

/-- **The first energy readout's records carry the Gibbs weights**, and neither the drive nor
the second apparatus retro-acts on them. -/
theorem sigma_first_energy_record (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (β : ℝ) (i : Fin N) :
    tpmSigmaPrep hH₀ β
        (drivenTwoStage (basinIndex (basisContext hH₀.eigenvectorBasis))
          (baseLift (fun p : LF4.CPN N => U • p)) (basinIndex (basisContext hH₁.eigenvectorBasis))
          ⁻¹' recordOneEvent i)
      = ENNReal.ofReal (gibbsWeight H₀ hH₀ β (hH₀.eigenvalues i)) := by
  rw [tpmSigmaPrep, driven_mixed_two_time_first_record, traceForm_gibbsDensity_energy]

/-! ### ★★ Jarzynski on `Σ` -/

/-- ★★ **TH5d — the Jarzynski equality on `Σ`.** The exponential average of the two-point-
measurement work over the RECORD probabilities of the driven protocol on the sector is the
ratio of the partition functions, `∑ᵢⱼ P_Σ(i, j) · e^{−βW(i,j)} = Z₁/Z₀`. -/
theorem sigma_jarzynski (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (β : ℝ) :
    ∑ i, ∑ j, (tpmSigmaPrep hH₀ β (tpmSigmaSector hH₀ hH₁ U i j)).toReal
        * Real.exp (-β * tpmWork hH₀ hH₁ i j)
      = partitionFn H₁ hH₁ β / partitionFn H₀ hH₀ β := by
  simp_rw [sigma_tpm_law, ENNReal.toReal_ofReal (tpmLaw_nonneg hH₀ hH₁ U β _ _)]
  exact jarzynski hH₀ hH₁ U β

/-- ★★ **Jarzynski on `Σ`, free-energy form**: `⟨e^{−βW}⟩_Σ = e^{−β(F₁ − F₀)}` in TH3's
equilibrium free energies. -/
theorem sigma_jarzynski_freeEnergy (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) ℂ) {β : ℝ} (hβ : 0 < β) :
    ∑ i, ∑ j, (tpmSigmaPrep hH₀ β (tpmSigmaSector hH₀ hH₁ U i j)).toReal
        * Real.exp (-β * tpmWork hH₀ hH₁ i j)
      = Real.exp (-β * (freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
          - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β))) := by
  simp_rw [sigma_tpm_law, ENNReal.toReal_ofReal (tpmLaw_nonneg hH₀ hH₁ U β _ _)]
  exact jarzynski_freeEnergy hH₀ hH₁ U hβ

/-- ★ **The second law of the driven process, on `Σ`**: the mean work over the record
probabilities is at least the free-energy difference, `ΔF ≤ ⟨W⟩_Σ`. -/
theorem sigma_mean_work_ge_freeEnergy_sub (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) ℂ) {β : ℝ} (hβ : 0 < β) :
    freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
        - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β)
      ≤ ∑ i, ∑ j, (tpmSigmaPrep hH₀ β (tpmSigmaSector hH₀ hH₁ U i j)).toReal
          * tpmWork hH₀ hH₁ i j := by
  simp_rw [sigma_tpm_law, ENNReal.toReal_ofReal (tpmLaw_nonneg hH₀ hH₁ U β _ _)]
  exact mean_work_ge_freeEnergy_sub hH₀ hH₁ U hβ

end CSD.RecordLayer

/-! ### Q29(e) consumed: the drive as the manifold Hamiltonian flow -/

namespace CSD.RecordLayer

open CSD.Thermo CSD.LF2 CSD.SigmaLayer

variable {n : ℕ} {H₀ H₁ Hd : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}

/-- **The drive as the Hamiltonian flow of the Schrödinger Hamiltonian.** The manifold flow
`IsSymplectic.hamiltonianFlow` of `−2⟨H_d⟩` for the Fubini–Study form, run for time `τ`, is
the unitary flow `exp(−iτH_d) • ·` (Q29(e), `hamiltonianFlow_schrodingerHamiltonian`), as a
function. -/
theorem hamiltonianFlow_schrodinger_eq (hHd : Hd.IsHermitian) (τ : ℝ) :
    (Projectivization.fsForm_isSymplectic n).hamiltonianFlow
        (Projectivization.contMDiff_schrodingerHamiltonian Hd) τ
      = fun p : LF4.CPN (n + 1) => LF4.schrodingerUnitary hHd τ • p :=
  funext fun p => Projectivization.hamiltonianFlow_schrodingerHamiltonian hHd τ p

/-- ★★ **TH5d with the drive as the sector's Hamiltonian flow** (Q29(e) consumed): with the
system driven for a time `τ` by the MANIFOLD Hamiltonian flow of the Schrödinger Hamiltonian
of `H_d` on `ℂℙⁿ`, the joint record law is `tpmLaw` at the unitary `exp(−iτH_d)`. -/
theorem sigma_tpm_law_hamiltonianFlow (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (hHd : Hd.IsHermitian) (τ β : ℝ) (i j : Fin (n + 1)) :
    tpmSigmaPrep hH₀ β
        (drivenJointRecordSector (basinIndex (basisContext hH₀.eigenvectorBasis))
          (baseLift ((Projectivization.fsForm_isSymplectic n).hamiltonianFlow
            (Projectivization.contMDiff_schrodingerHamiltonian Hd) τ))
          (basinIndex (basisContext hH₁.eigenvectorBasis)) i j)
      = ENNReal.ofReal (tpmLaw hH₀ hH₁ (LF4.schrodingerUnitary hHd τ) β i j) := by
  rw [hamiltonianFlow_schrodinger_eq hHd τ]
  exact sigma_tpm_law hH₀ hH₁ (LF4.schrodingerUnitary hHd τ) β i j

/-- ★★ **Jarzynski on `Σ` with the drive as the sector's Hamiltonian flow** (Q29(e) consumed):
the exponential average of the work over the record probabilities of the protocol driven by the
Hamiltonian flow of `−2⟨H_d⟩` for time `τ` is `Z₁/Z₀`. -/
theorem sigma_jarzynski_hamiltonianFlow (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (hHd : Hd.IsHermitian) (τ β : ℝ) :
    ∑ i, ∑ j, (tpmSigmaPrep hH₀ β
        (drivenJointRecordSector (basinIndex (basisContext hH₀.eigenvectorBasis))
          (baseLift ((Projectivization.fsForm_isSymplectic n).hamiltonianFlow
            (Projectivization.contMDiff_schrodingerHamiltonian Hd) τ))
          (basinIndex (basisContext hH₁.eigenvectorBasis)) i j)).toReal
        * Real.exp (-β * tpmWork hH₀ hH₁ i j)
      = partitionFn H₁ hH₁ β / partitionFn H₀ hH₀ β := by
  rw [hamiltonianFlow_schrodinger_eq hHd τ]
  exact sigma_jarzynski hH₀ hH₁ (LF4.schrodingerUnitary hHd τ) β

end CSD.RecordLayer

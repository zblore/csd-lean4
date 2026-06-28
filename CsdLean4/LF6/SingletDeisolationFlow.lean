import CsdLean4.LF5.FlowBornFrequency
import CsdLean4.LF6.ForcedContextuality
import CsdLean4.LF3.Singlet.JointEig

/-!
# LF6-A.2: the full singlet de-isolation flow

**Category:** 6-Local (the dynamical realisation of the entangled de-isolation
tier; the D1 entangled frontier).

This is **LF6-A.2** of `specs/lf6-plan.md`: an actual deterministic,
Fubini–Study-measure-preserving de-isolation flow whose contextual carve
reproduces the LF3 singlet kernel `P_st`, with a.s. pointer-block frequencies
converging to `P_st`. It is the dynamical counterpart of the forced-contextuality
no-go LF6-A.1 (`ForcedContextuality.lean`), which it **reuses** for the
contextuality anchor.

## The construction (clean path, reusing LF5 @ N = 4 + LF3 + A.1)

The system is the joint two-qubit register `ℂ⁴ ≅ ℂ² ⊗ ℂ²`, measured by the LF5
von Neumann de-isolation flow `measurementFlow 4 e` on the dilated projective
ontic space `Σ' = ℂℙ¹⁵ = ℙ(EuclideanSpace ℂ (Fin 16))` (`e = finProdFinEquiv`,
`16 = 4·4 = 15 + 1`). The flow is **local** as an apparatus dynamics (it is the
single-system LF5 de-isolation at `N = 4`); the non-locality is **not** in the
flow but in the *outcome carve*, which is the joint `BornRegion`
moment-subdivision of `LF4/BornRegionUncond`, and is jointly contextual by A.1.

The prepared state is the singlet expressed in the rotated (axis-context)
measurement basis,
`φ = nudgedSinglet a b`, whose computational coordinate at the pointer cell
`(s, t)` is the singlet's joint-spin-eigenstate amplitude:
`φ_{stIdx (s,t)} = ⟨ψ⁻, singletJointEig s t a b⟩`. This is `φ = (U_A^x ⊗ U_B^y)† ψ⁻`
in coordinates — the pre-measurement *nudge* `U_A^x ⊗ U_B^y` (a reversible
context-setting symmetry, not the carve) rotates the computational basis onto the
joint spin eigenbasis `a_s ⊗ b_t = singletJointEig s t a b`. Then the headline:

```
pointer-block (s,t) FS volume  =  ‖⟨e_{stIdx (s,t)}, φ⟩‖²        -- LF5 vnDilation_pointer_volume @ N=4
                               =  ‖⟨ψ⁻, singletJointEig s t a b⟩‖² -- nudge coordinate identity
                               =  P_st a b s t                     -- LF3 singletJointEig_born
```

So the reproduction is LF5@N=4 + a coordinate (unitary-invariance) step + LF3's
Born identity. The basis-change vectors are the genuine joint spin eigenstates of
`LF3/Singlet/JointEig.lean`; the Born identity `singletJointEig_born` is the proof
behind `MeasurementJointEig.born_eq_P_st`.

## Honest scope (the A.2 ledger)

- **Exhibited.** A genuine deterministic FS-measure-preserving de-isolation flow
  `Φ ≠ id` (`singletDeisolation_*`, inherited from LF5-B), whose joint
  `BornRegion` pointer-block volumes equal `P_st`
  (`singletDeisolation_pointer_volume`) and whose a.s. block frequencies converge
  to `P_st` (`singletDeisolation_frequency`).
- **Imported, not re-derived.** Born = FS-volume is derived one layer down (the
  moment-map / Duistermaat–Heckman cluster, `fs_born_volume_ratio_N`,
  Gleason-free, no Born put in) and imported through
  `vnDilation_pointer_volume`. The singlet kernel `P_st` and its joint
  eigenstates / Born identity are LF3. The contextuality no-go is LF6-A.1.
- **Contextual carve, routed through A.1.** The outcome is the joint `BornRegion`
  cell, **not** a setting-local `{pointer_A = i} ∩ {pointer_B = j}` product
  region. `singletDeisolation_carve_contextual` proves, *through*
  `no_product_partition_realises_singlet`, that no setting-local ±1 product
  partition reproduces the carve's correlations; the carve's block-volume
  correlation is `−a·b` (`singletDeisolation_blockVolume_correlation`), the
  singlet's, which A.1 forbids any product partition to produce. The flow may be
  local; the carve is contextual. Measurement is contextual.
- **Deferred (A.3).** The flow factorisation `Φ = Φ_A ⊗ Φ_B` (the tensor
  reindexing `(sys_A ⊗ ptr_A) ⊗ (sys_B ⊗ ptr_B)`). The de-isolation here is the
  `N = 4` joint coupling; its decomposition into two wing couplings is the heavy
  tensor-reindex piece, deferred (`specs/lf6-plan.md` LF6-A.3). This does **not**
  weaken A.2: A.1 already establishes that the locality of the flow is consistent
  with the contextuality of the carve, and the safety anchor
  (`singletDeisolation_carve_contextual`) does not assume the product structure.
- **Residue: A5.** The entangled sector / the singlet's preparation region `Ω₀`
  is posited, not derived (A5 reduces to D1). `nudgedSinglet`'s amplitudes are the
  singlet's; the *typicality law* on `Σ'` is the Fubini–Study measure (A5).
- **Generic context.** The four-sector construction needs `P_st a b s t > 0` for
  all `(s, t)` (`hgen`), i.e. `|a·b| < 1` — every Bell-test setting. Collinear
  axes have a vanishing sector and carry no Born information.

All exports are foundational-triple-only (Gleason-free; the LF5 pointer engine is
off Busch, A.1 is measure-theoretic Bell content).

Reference: `specs/lf6-plan.md` (LF6-A.2).
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF3 CSD.LF5 CSD.LF2 CSD.LF4 CSD.Empirical.QM.E91

/-! ### Index identification `Sign × Sign ≃ Fin 4` -/

/-- `Sign ≃ Fin 2`: `plus ↦ 0`, `minus ↦ 1`. -/
def signEquiv : Sign ≃ Fin 2 where
  toFun s := match s with | .plus => 0 | .minus => 1
  invFun i := if i = 0 then .plus else .minus
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The pointer-index identification `(s, t) ↦ Fin 4` tying the LF5 pointer
outcome at `N = 4` to the LF3 sign pair. -/
def stIdx : Sign × Sign ≃ Fin 4 :=
  (signEquiv.prodCongr signEquiv).trans finProdFinEquiv

/-! ### The nudged singlet (the prepared state `φ = (U_A^x ⊗ U_B^y)† ψ⁻`) -/

/-- **The prepared state.** The singlet expressed in the rotated (axis-context)
measurement basis: the computational coordinate at the pointer cell `(s, t)` is
the singlet's amplitude on the joint spin eigenstate `singletJointEig s t a b`
(`= ⟨ψ⁻, a_s ⊗ b_t⟩`). This is `(U_A^x ⊗ U_B^y)† ψ⁻` in coordinates, the nudge
of `specs/lf6-plan.md` (reversible, pre-measurement, context-setting). Only
`‖·‖²` of these coordinates is consumed downstream. -/
noncomputable def nudgedSinglet (a b : DetectorSetting) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun k : Fin 4 =>
    inner ℂ singlet (singletJointEig (stIdx.symm k).1 (stIdx.symm k).2 a b))

/-- The pointer-cell coordinate of the nudged singlet is the joint
eigenstate amplitude. -/
lemma nudgedSinglet_coord (a b : DetectorSetting) (s t : Sign) :
    (nudgedSinglet a b) (stIdx (s, t)) = inner ℂ singlet (singletJointEig s t a b) := by
  have h : stIdx.symm (stIdx (s, t)) = (s, t) := Equiv.symm_apply_apply stIdx (s, t)
  show inner ℂ singlet (singletJointEig (stIdx.symm (stIdx (s, t))).1
        (stIdx.symm (stIdx (s, t))).2 a b)
      = inner ℂ singlet (singletJointEig s t a b)
  rw [h]

/-- **The nudge coordinate-Born identity.** The squared computational amplitude
of the nudged singlet at the pointer cell `(s, t)` equals the singlet kernel
`P_st a b s t` — composing the coordinate identity with the genuine LF3 Born
identity `singletJointEig_born`. Generic context (`hgen`). -/
lemma nudgedSinglet_born (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t)
    (s t : Sign) :
    ‖inner ℂ (EuclideanSpace.single (stIdx (s, t)) (1 : ℂ)) (nudgedSinglet a b)‖ ^ 2
      = P_st a b s t := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, nudgedSinglet_coord]
  exact singletJointEig_born s t a b (hgen s t)

/-- The pointer-cell squared coordinate as a function of `Sign × Sign`. -/
lemma nudgedSinglet_coord_normSq (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t)
    (st : Sign × Sign) :
    ‖(nudgedSinglet a b) (stIdx st)‖ ^ 2 = P_st a b st.1 st.2 := by
  obtain ⟨s, t⟩ := st
  rw [nudgedSinglet_coord]
  exact singletJointEig_born s t a b (hgen s t)

/-- The sum of the singlet kernel over the four sectors is `1` (the prepared state
is normalised; the cross term `∑ s·t` vanishes). -/
lemma sum_P_st_eq_one (a b : DetectorSetting) :
    ∑ st : Sign × Sign, P_st a b st.1 st.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Sign.sum_univ, Sign.val_plus, Sign.val_minus, P_st]
  ring

/-- **The nudged singlet is a unit preparation.** `‖φ‖² = ∑_{s,t} P_st = 1`.
Discharges the `hψ` hypothesis of the LF5 pointer-volume / frequency theorems. -/
theorem nudgedSinglet_norm (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t) :
    ‖nudgedSinglet a b‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ k : Fin 4, ‖(nudgedSinglet a b) k‖ ^ 2 = 1 := by
    calc ∑ k : Fin 4, ‖(nudgedSinglet a b) k‖ ^ 2
        = ∑ st : Sign × Sign, ‖(nudgedSinglet a b) (stIdx st)‖ ^ 2 :=
          (Equiv.sum_comp stIdx (fun k => ‖(nudgedSinglet a b) k‖ ^ 2)).symm
      _ = ∑ st : Sign × Sign, P_st a b st.1 st.2 :=
          Finset.sum_congr rfl (fun st _ => nudgedSinglet_coord_normSq a b hgen st)
      _ = 1 := sum_P_st_eq_one a b
  rw [hsum, Real.sqrt_one]

/-- The nudged singlet is nonzero. -/
theorem nudgedSinglet_ne_zero (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t) :
    nudgedSinglet a b ≠ 0 := by
  intro h
  have := nudgedSinglet_norm a b hgen
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-! ### Deliverable 1: the flow -/

/-- **The singlet de-isolation flow** `Φ = measurementFlow 4 finProdFinEquiv` on
the dilated projective ontic space `Σ' = ℂℙ¹⁵ = ℙ(EuclideanSpace ℂ (Fin 16))`
(`16 = 4·4`). This is the LF5-B von Neumann de-isolation flow instantiated at the
joint two-qubit system `N = 4`; it is **local** as an apparatus dynamics. -/
noncomputable def singletDeisolationFlow :
    ℙ ℂ (EuclideanSpace ℂ (Fin (4 * 4))) → ℙ ℂ (EuclideanSpace ℂ (Fin (4 * 4))) :=
  measurementFlow 4 finProdFinEquiv

/-- The singlet de-isolation flow is Fubini–Study measure-preserving (the
Liouville / `hΦ_pres` content), inherited from `measurementFlow_measurePreserving`. -/
theorem singletDeisolation_measurePreserving (p₀ : CPN (4 * 4)) :
    MeasurePreserving singletDeisolationFlow (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  measurementFlow_measurePreserving finProdFinEquiv p₀

/-- The singlet de-isolation flow is genuinely not the identity (`N = 4 > 1`),
inherited from `measurementFlow_ne_id`. -/
theorem singletDeisolation_ne_id : singletDeisolationFlow ≠ id :=
  measurementFlow_ne_id (by norm_num) finProdFinEquiv

/-! ### Deliverable 2: pointer-block FS volume = `P_st` (the headline) -/

/-- **The reproduction (the A.2 headline).** The joint `BornRegion` pointer-block
`(s, t)` Fubini–Study volume of the singlet de-isolation flow equals the LF3
singlet kernel `P_st a b s t`, for the prepared state `φ = nudgedSinglet a b`.

A deterministic FS-measure-preserving de-isolation flow's *contextual* carve (the
joint moment-subdivision `BornRegion`, never a setting-local product region) has
block volumes = the singlet kernel. The proof **composes** LF5
`vnDilation_pointer_volume` at `N = 4` (pointer-block volume = `‖⟨e_i, φ⟩‖²`,
Gleason-free, imported from the DH/FS-volume engine) with the nudge
coordinate-Born identity `nudgedSinglet_born` (which composes the unitary
invariance step with LF3 `singletJointEig_born`). Generic context (`hgen`). -/
theorem singletDeisolation_pointer_volume {M : ℕ}
    (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 4) (nudgedSinglet a b)))
    (hψ'0 : ψ' ≠ 0) (s t : Sign) :
    ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
      = P_st a b s t := by
  rw [← vnDilation_pointer_volume (nudgedSinglet a b) (nudgedSinglet_norm a b hgen)
        e p₀ ψ' hψ'eq hψ'0 (stIdx (s, t))]
  exact nudgedSinglet_born a b hgen s t

/-! ### Deliverable 3: a.s. pointer-block frequencies → `P_st` -/

/-- **The empirical capstone.** For i.i.d. Fubini–Study-typical trials on the
dilated `Σ' = ℂℙ¹⁵` (the A5 typicality posit on the enlarged entangled sector),
almost surely every pointer-block `(s, t)` empirical frequency converges to the
singlet kernel `P_st a b s t`. Instantiates LF5 `vnDilation_pointer_frequency` at
`N = 4`, `φ = nudgedSinglet a b`, and lands the limit on `P_st` via
`nudgedSinglet_born`. -/
theorem singletDeisolation_frequency {M : ℕ}
    (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 4) (nudgedSinglet a b)))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ s t : Sign,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 4,
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (P_st a b s t)) := by
  filter_upwards [vnDilation_pointer_frequency (nudgedSinglet a b)
      (nudgedSinglet_norm a b hgen) e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep] with ω hω s t
  have h := hω (stIdx (s, t))
  rwa [nudgedSinglet_born a b hgen s t] at h

/-! ### Deliverable 4: the carve is contextual (the safety anchor, via A.1) -/

/-- **The carve's block-volume correlation is the singlet's (`−a·b`).** Composes
`singletDeisolation_pointer_volume` (block volume = `P_st`) with the LF3
correlation identity `correlation_eq_neg_dot` (`∑ s·t·P_st = −a·b`). This is the
input fed to the A.1 no-go: the exhibited contextual carve reproduces the singlet
correlation function. -/
theorem singletDeisolation_blockVolume_correlation {M : ℕ}
    (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 4) (nudgedSinglet a b)))
    (hψ'0 : ψ' ≠ 0) :
    ∑ st : Sign × Sign, st.1.val * st.2.val *
        (∑ n : Fin 4,
          (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (st.1, st.2))))).toReal)
      = - dotR a b := by
  have hcongr : ∀ st : Sign × Sign,
      st.1.val * st.2.val *
          (∑ n : Fin 4,
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (st.1, st.2))))).toReal)
        = st.1.val * st.2.val * P_st a b st.1 st.2 := fun st => by
    rw [singletDeisolation_pointer_volume a b hgen e p₀ ψ' hψ'eq hψ'0 st.1 st.2]
  rw [Finset.sum_congr rfl (fun st _ => hcongr st), correlation_eq_neg_dot]

/-- **The carve is contextual (the safety anchor, routed through A.1).** No
setting-local ±1 product partition of any shared probability space `(Λ, μ)`
reproduces the carve's correlation function. The hypothesis `hcarve` is exactly
what `singletDeisolation_blockVolume_correlation` establishes for the exhibited
carve (its block-volume correlation is the singlet's `−a·b`); the conclusion
routes through `no_product_partition_realises_singlet` (LF6-A.1) — the carve
cannot be a product (non-contextual) partition. Measurement is contextual. -/
theorem singletDeisolation_carve_contextual {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (RA RB : DetectorSetting → Λ → ℝ)
    (hPP : IsProductPartition RA RB)
    (hcarve : ∀ a b : DetectorSetting, lhvCorrelation μ RA RB a b = - dotR a b) :
    False := by
  refine no_product_partition_realises_singlet μ RA RB hPP ?_
  intro a b
  rw [hcarve a b, singletCorrelation_eq_neg_dot]

/-! ### Deliverable 6: the capstone -/

/-- **The LF6-A.2 capstone: the singlet de-isolation flow.** A deterministic,
Fubini–Study-measure-preserving de-isolation flow `Φ ≠ id` on the dilated
`Σ' = ℂℙ¹⁵` whose contextual joint-`BornRegion` carve reproduces the LF3 singlet
kernel `P_st`, with a.s. block frequencies → `P_st` and a contextuality anchor
routed through A.1. Conjuncts:

1. genuine dynamics, `Φ ≠ id` (`singletDeisolation_ne_id`);
2. physically admissible: FS measure-preserving (`singletDeisolation_measurePreserving`);
3. pointer-block FS volume = the singlet kernel, every sector
   (`singletDeisolation_pointer_volume`);
4. the carve's block-volume correlation is the singlet's `−a·b`
   (`singletDeisolation_blockVolume_correlation`);
5. a.s. block frequencies → `P_st` (`singletDeisolation_frequency`);
6. the carve is contextual: no setting-local ±1 product partition reproduces the
   `−a·b` correlation of the carve (`singletDeisolation_carve_contextual`, routed
   through A.1 `no_product_partition_realises_singlet`).

The flow is local (LF5 @ N=4); the carve is contextual (the joint moment
subdivision, A.1). Born = FS-volume is imported from the DH/FS-volume engine, not
re-derived. The flow factorisation `Φ = Φ_A ⊗ Φ_B` is deferred to LF6-A.3.
Residue: A5 (the entangled sector posited). Honest ledger: module docstring. -/
theorem singletDeisolation_flow_capstone {M : ℕ}
    (a b : DetectorSetting) (hgen : ∀ s t, 0 < P_st a b s t)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 4) (nudgedSinglet a b)))
    (hψ'0 : ψ' ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    -- (1) genuine dynamics
    measurementFlow 4 e ≠ id
    -- (2) FS measure-preserving
    ∧ MeasurePreserving (measurementFlow 4 e)
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀)
    -- (3) pointer-block FS volume = the singlet kernel
    ∧ (∀ s t : Sign,
        ∑ n : Fin 4,
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
          = P_st a b s t)
    -- (4) the carve's block-volume correlation is the singlet's −a·b
    ∧ (∑ st : Sign × Sign, st.1.val * st.2.val *
          (∑ n : Fin 4,
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (st.1, st.2))))).toReal)
        = - dotR a b)
    -- (5) a.s. block frequencies → P_st
    ∧ (∀ᵐ ω ∂ Pr, ∀ s t : Sign,
        Tendsto
          (fun m : ℕ =>
            ∑ n : Fin 4,
              (∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))
                    (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
          atTop
          (nhds (P_st a b s t)))
    -- (6) the carve is contextual (routed through A.1)
    ∧ (∀ (Λ : Type) [MeasurableSpace Λ] (μ : Measure Λ) [IsProbabilityMeasure μ]
        (RA RB : DetectorSetting → Λ → ℝ), IsProductPartition RA RB →
        (∀ a' b' : DetectorSetting, lhvCorrelation μ RA RB a' b' = - dotR a' b') → False) :=
  ⟨measurementFlow_ne_id (by norm_num) e,
   measurementFlow_measurePreserving e p₀,
   fun s t => singletDeisolation_pointer_volume a b hgen e p₀ ψ' hψ'eq hψ'0 s t,
   singletDeisolation_blockVolume_correlation a b hgen e p₀ ψ' hψ'eq hψ'0,
   singletDeisolation_frequency a b hgen e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep,
   fun Λ _ μ _ RA RB hPP hcarve => singletDeisolation_carve_contextual μ RA RB hPP hcarve⟩

end LF6
end CSD

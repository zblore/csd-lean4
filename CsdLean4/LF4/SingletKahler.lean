import CsdLean4.LF4.KahlerInstance
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF3.Interface
import CsdLean4.LF3.Singlet.JointEig
import CsdLean4.LF2.Preparation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# LF4 §8: the `ofKählerPreparation` constructor for the singlet

Assembles a concrete `LF3.PureSingletPreparation kSectorData ctx 4` on the
non-trivial-fibre compact-Kähler instance `Σ = ℂℙ³ × T²` (the `N = 4` case for
the two-qubit singlet), discharging the bundle's load-bearing fields as
**theorems** for a fixed measurement context:

- the reindex `singletPsi := kReindex singlet : EuclideanSpace ℂ (Fin 4)`;
- the posited fibre law `μψ := (Measure.dirac ⟦singletPsi⟧).prod vol_{T²}`, which
  pushes through `π = pr₁` to the Dirac on the ray (`Measure.fst_prod`);
- the constant projective representative `rep := fun _ => singletPsi` (only its
  value at `ray_point` matters under Dirac integration, so this is sufficient
  for `OperationalPackage.fromPreparation`);
- the genuine joint spin eigenstate `eig s t := kReindex (singletJointEig …)`,
  with `MeasurementJointEig.born_eq_P_st` discharged via
  `singletJointEig_born` (the §3 theorem) transported through the isometry;
- the outcome regions `O_kReg s t` with second factor a measure-`P_st` arc on
  the first `AddCircle 1` of `T²` — `bridge_op_p` then holds because the fibre
  region has volume exactly `P_st` and the Dirac-integrated OP probability is
  the same `P_st` (proved Busch-free via `born_rank_one_direct` and
  `singletJointEig_born`).

**Generic-context hypothesis.** Restricted to `∀ s t, 0 < P_st ctx.a ctx.b s t`,
i.e. `|a·b| < 1`. All Bell-test settings qualify; collinear settings (`a = ±b`)
are excluded as they carry no Born-content.

**Axiom posture.** `ofKählerPreparation` is foundational-triple only (the
constant `rep` + the `_direct` Born theorem keep Busch out of the construction).
The concrete frequency capstone is **also foundational-triple-only / Gleason-free**:
the LF3 chain's `weight_eq_P_st` routes through the Busch-free
`OP_p_at_jointEig_eq_P_st_direct` (the 2026-06-02 re-route; AXIOMS.md §2.4), not
through the Busch-mediated twin.

**Honesty note (Tier-2 framing).** `bridge_op_p` holds because the outcome
regions are *carved* to fibre-volume `P_st`. This realises eq-12 (the
volume-ratio thesis) concretely on a compact-Kähler `Σ`, but it does not
*derive* `P_st` from independent geometry. The capstone-of-the-instance is
non-vacuous; the further reduction "why do volumes select Born?" remains
the constraint-surface-dynamics open problem (LF4-todo §8 outro).
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open CSD.LF3

namespace CSD
namespace LF4

/-! ### Reindex isometry `Fin 2 × Fin 2 → Fin 4` -/

/-- The reindexing isometry, lifting `finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4`
to a `LinearIsometryEquiv` of `EuclideanSpace ℂ`s. -/
noncomputable def kReindex :
    EuclideanSpace ℂ (Fin 2 × Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 4) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finProdFinEquiv

/-- A handy upper bound: `P_st ≤ 1` (it is in fact `≤ 1/2`, but `≤ 1` suffices). -/
private lemma P_st_le_one (a b : DetectorSetting) (s t : Sign) :
    P_st a b s t ≤ 1 := by
  unfold P_st
  have h := abs_dotR_le_one a b
  have ⟨h1, h2⟩ := abs_le.mp h
  have hst : (-1 : ℝ) ≤ s.val * t.val ∧ s.val * t.val ≤ 1 := by
    cases s <;> cases t <;> simp [Sign.val]
  nlinarith [hst.1, hst.2, h1, h2]

/-! ### Singlet vector in `Fin 4` and its projective ray -/

variable {N : ℕ} (ctx : CSD.LF3.MeasurementContext)

/-- The Bell singlet, re-indexed into `EuclideanSpace ℂ (Fin 4)`. -/
noncomputable def singletPsi : EuclideanSpace ℂ (Fin 4) := kReindex singlet

lemma singletPsi_norm : ‖singletPsi‖ = 1 := by
  unfold singletPsi
  rw [LinearIsometryEquiv.norm_map, singlet_norm]

lemma singletPsi_ne_zero : (singletPsi : EuclideanSpace ℂ (Fin 4)) ≠ 0 := by
  intro h
  have : ‖singletPsi‖ = 0 := by rw [h, norm_zero]
  rw [singletPsi_norm] at this
  exact one_ne_zero this

/-- The projective ray `[singletPsi] ∈ ℂℙ³`. -/
noncomputable def singletRay : CPN 4 :=
  Projectivization.mk ℂ singletPsi singletPsi_ne_zero

/-! ### Carving: an arc of `AddCircle 1` with measure `ℓ` -/

/-- For `ℓ ∈ [0, 1]`, the measurable subset of `AddCircle 1` whose pre-image
under the `Ioc 0 1` chart is the sub-interval `Ioc 0 ℓ`; has Haar volume
exactly `ENNReal.ofReal ℓ`. Uses `equivIoc` (the underlying `Equiv`) so
`measurePreserving_equivIoc` applies directly. -/
noncomputable def fibreArc (ℓ : ℝ) : Set (AddCircle (1 : ℝ)) :=
  (AddCircle.equivIoc (1 : ℝ) 0) ⁻¹' (Subtype.val ⁻¹' Set.Ioc 0 ℓ)

lemma fibreArc_measurable (ℓ : ℝ) : MeasurableSet (fibreArc ℓ) := by
  -- `(measurableEquivIoc 1 0)` as a function equals `equivIoc 1 0`, so preimage measurability
  -- transfers directly.
  exact (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable
    (measurable_subtype_coe measurableSet_Ioc)

lemma fibreArc_volume {ℓ : ℝ} (hℓ : ℓ ∈ Set.Icc (0 : ℝ) 1) :
    (volume : Measure (AddCircle (1 : ℝ))) (fibreArc ℓ) = ENNReal.ofReal ℓ := by
  unfold fibreArc
  rw [(AddCircle.measurePreserving_equivIoc (T := 1)).measure_preimage
        (measurable_subtype_coe measurableSet_Ioc).nullMeasurableSet,
      Measure.comap_apply _ Subtype.val_injective
        (fun _ ↦ measurableSet_Ioc.subtype_image)
        _ (measurable_subtype_coe measurableSet_Ioc),
      Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, zero_add]
  -- Goal: vol (Ioc 0 ℓ ∩ {x | x ∈ Ioc 0 1}) = ENNReal.ofReal ℓ
  -- `{x | x ∈ S} = S` is definitional for `Set α = α → Prop`.
  show (volume : Measure ℝ) (Set.Ioc 0 ℓ ∩ Set.Ioc 0 1) = ENNReal.ofReal ℓ
  rw [Set.Ioc_inter_Ioc, max_self,
      min_eq_left (by linarith [hℓ.2] : ℓ ≤ 1),
      Real.volume_Ioc, sub_zero]

/-! ### Outcome regions on `Σ = ℂℙ³ × T²` -/

/-- The outcome region at sector `(s, t)`: all of `ℂℙ³`, times an arc of the
first `AddCircle` of measure `P_st`, times the whole second `AddCircle`.
The base-side factor `univ_{ℂℙ³}` will be inflated to a Dirac at the singlet
ray by the fibre measure `μψ`. -/
noncomputable def kRegion (s t : Sign) : Set (KSigma 4) :=
  Set.univ ×ˢ (fibreArc (P_st ctx.a ctx.b s t) ×ˢ Set.univ)

lemma kRegion_measurable (s t : Sign) : MeasurableSet (kRegion ctx s t) := by
  unfold kRegion
  exact MeasurableSet.univ.prod ((fibreArc_measurable _).prod MeasurableSet.univ)

/-- Packaged as an LF1 `OutcomeRegion` over `kOnticSetup`. -/
noncomputable def kOutcomeRegion (p₀ : CPN 4) (s t : Sign) :
    (kOnticSetup p₀).OutcomeRegion where
  Ω := kRegion ctx s t
  hΩ_meas := kRegion_measurable ctx s t

/-! ### Fibre measure `μψ` -/

/-- The posited fibre trial law over `[singletPsi]`: `δ_{[ψ]} ⊗ vol_{T²}`.
Pushes through `π = pr₁` to the Dirac on the ray. -/
noncomputable def kMuPsi : Measure (KSigma 4) :=
  (Measure.dirac singletRay).prod (volume : Measure KTorus)

instance instProbKMuPsi : IsProbabilityMeasure kMuPsi := by
  unfold kMuPsi
  infer_instance

/-- `μψ`'s pushforward through `π = pr₁` is the Dirac on the singlet ray. -/
lemma kMuPsi_push : Measure.map (Prod.fst : KSigma 4 → CPN 4) kMuPsi
    = Measure.dirac singletRay := by
  unfold kMuPsi
  rw [← Measure.fst, Measure.fst_prod]

/-- The fibre-measure of an outcome region equals the fibre-arc volume,
`ENNReal.ofReal (P_st ctx.a ctx.b s t)` (the carving identity). -/
lemma kMuPsi_kRegion (s t : Sign) :
    kMuPsi (kRegion ctx s t) = ENNReal.ofReal (P_st ctx.a ctx.b s t) := by
  unfold kMuPsi kRegion
  rw [Measure.prod_prod, measure_univ, one_mul]
  -- Goal: vol_{KTorus}(fibreArc P_st ×ˢ univ) = ENNReal.ofReal P_st
  show (volume : Measure KTorus)
      (fibreArc (P_st ctx.a ctx.b s t) ×ˢ Set.univ) = _
  rw [show (volume : Measure KTorus)
        = (volume : Measure (AddCircle (1:ℝ))).prod
            (volume : Measure (AddCircle (1:ℝ))) from rfl]
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact fibreArc_volume ⟨P_st_nonneg _ _ _ _, P_st_le_one ctx.a ctx.b s t⟩

/-! ### `PurePreparation` over `kSectorData` and `μψ`

Constant `rep := fun _ => singletPsi`. Only its value at the ray matters under
Dirac integration; `rep_at_ray` is `rfl`, `push_dirac` is `kMuPsi_push`. -/

/-- The constant projective representative. -/
noncomputable def kRep : CPN 4 → EuclideanSpace ℂ (Fin 4) := fun _ => singletPsi

lemma kRep_unit (p : CPN 4) : ‖kRep p‖ = 1 := singletPsi_norm

lemma kRep_meas : Measurable kRep := measurable_const

variable (p₀ : CPN 4)

/-- The `LF2.PurePreparation` over `kSectorData p₀` and the posited fibre law. -/
noncomputable def kPurePrep :
    LF2.PurePreparation (kSectorData (N := 4) p₀) kMuPsi 4 where
  ψ := singletPsi
  unit_ψ := singletPsi_norm
  rep := kRep
  hrep_unit := kRep_unit
  hrep_meas := kRep_meas
  ray_point := singletRay
  rep_at_ray := rfl
  push_dirac := by
    show Measure.map (kSectorData (N := 4) p₀).π kMuPsi = Measure.dirac singletRay
    exact kMuPsi_push

/-! ### `MeasurementJointEig` for the singlet

The `hgen : ∀ s t, 0 < P_st ctx.a ctx.b s t` (generic-context) hypothesis is
threaded explicitly through the lemmas. -/

/-- The genuine joint spin eigenstates, transported to `Fin 4`. -/
noncomputable def kEig (s t : Sign) : EuclideanSpace ℂ (Fin 4) :=
  kReindex (singletJointEig s t ctx.a ctx.b)

lemma kEig_unit (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t) (s t : Sign) :
    ‖kEig ctx s t‖ = 1 := by
  unfold kEig
  rw [LinearIsometryEquiv.norm_map]
  exact singletJointEig_norm s t ctx.a ctx.b (hgen s t)

lemma kEig_distinct (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t)
    {s t s' t' : Sign} (h : (s, t) ≠ (s', t')) :
    kEig ctx s t ≠ kEig ctx s' t' := by
  intro heq
  have h1 : kReindex (singletJointEig s t ctx.a ctx.b)
        = kReindex (singletJointEig s' t' ctx.a ctx.b) := heq
  have h2 : singletJointEig s t ctx.a ctx.b = singletJointEig s' t' ctx.a ctx.b :=
    kReindex.injective h1
  have h_orth :=
    singletJointEig_orthogonal (s := s) (t := t) (s' := s') (t' := t') ctx.a ctx.b h
  rw [h2] at h_orth
  -- h_orth : ⟪v, v⟫ = 0, but ‖v‖ = 1 so ⟪v,v⟫ = 1
  have hself : (inner ℂ (singletJointEig s' t' ctx.a ctx.b)
                       (singletJointEig s' t' ctx.a ctx.b) : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K,
        singletJointEig_norm s' t' ctx.a ctx.b (hgen s' t')]
    push_cast
    norm_num
  rw [hself] at h_orth
  exact one_ne_zero h_orth

lemma kEig_born (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t) (s t : Sign) :
    ‖inner ℂ singletPsi (kEig ctx s t)‖ ^ 2 = P_st ctx.a ctx.b s t := by
  unfold singletPsi kEig
  rw [LinearIsometryEquiv.inner_map_map]
  exact singletJointEig_born s t ctx.a ctx.b (hgen s t)

/-- The `MeasurementJointEig` bundle for the singlet, with `born_eq_P_st`
discharged as a theorem. -/
noncomputable def kJED (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t) :
    MeasurementJointEig ctx singletPsi where
  eig := kEig ctx
  eig_unit := kEig_unit ctx hgen
  eig_distinct := fun _ _ _ _ h => kEig_distinct ctx hgen h
  born_eq_P_st := kEig_born ctx hgen

/-! ### `MeasureBridgeData` for the Kähler instance (axiom-free, `c = 1`) -/

/-- The (axiom-free) `MeasureBridgeData` for `kSectorData p₀`: `π∗μL = 1 · μFS`
via `Measure.fst_prod`. Builds the bridge fields directly, so it stays
foundational-triple-only (this is now the only route — the abstract
`measure_bridge` / `invariant_measure_uniqueness` axiom were removed 2026-06-04). -/
noncomputable def kBridge (p₀ : CPN 4) :
    LF2.MeasureBridgeData (kSectorData p₀) (fubiniStudyMeasure p₀) where
  is_inv := fun U =>
    ⟨(continuous_const_smul U).measurable, fubiniStudyMeasure_smul_invariant U p₀⟩
  c := 1
  bridge_eq := by
    show Measure.map (kSectorData p₀).π ((kSectorData p₀).μL : Measure (KSigma 4))
        = 1 • fubiniStudyMeasure p₀
    rw [one_smul]
    show Measure.map Prod.fst (kMuL p₀) = fubiniStudyMeasure p₀
    rw [kMuL, ← Measure.fst, Measure.fst_prod]

/-! ### The `ofKählerPreparation` constructor -/

/-- **The constructor**: a concrete `LF3.PureSingletPreparation` for the
singlet on the non-trivial-fibre compact-Kähler `kSectorData p₀`,
with `bridge_op_p` discharged as a theorem (via the carving identity
`kMuPsi_kRegion` and the Busch-free `LF2.PurePreparation.born_rank_one_direct`).

The bundle composes:
- `μψ = kMuPsi = (Measure.dirac singletRay).prod vol_{T²}` (posited fibre law);
- `μFS = fubiniStudyMeasure p₀`, with axiom-free `kBridge` (`c = 1` marginal);
- `PP = kPurePrep p₀` (constant `rep := singletPsi`, ray = `singletRay`);
- `jed = kJED ctx hgen` (genuine joint spin eigenstates, `born_eq_P_st` proved);
- `O_region = kOutcomeRegion ctx p₀` (outcome = `univ_{ℂℙ³} × arc(P_st) × univ`).

`bridge_op_p`: LHS = `μψ(preEvent) = vol_{T²}(arc(P_st) × univ) = P_st`
(carving); RHS = `OP.p(rankOneEffect(eig)) = ‖⟨singletPsi, eig⟩‖² = P_st`
(`born_rank_one_direct` + `kEig_born`). Both sides `ENNReal.ofReal P_st`. -/
noncomputable def ofKählerPreparation
    (p₀ : CPN 4) (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t) :
    LF3.PureSingletPreparation (kSectorData p₀) ctx 4 :=
  LF3.PureSingletPreparation.ofHypothesis
    kMuPsi inferInstance
    (fubiniStudyMeasure p₀) inferInstance
    (kBridge p₀)
    (kPurePrep p₀)
    (by decide)
    (kJED ctx hgen)
    (kOutcomeRegion ctx p₀)
    (by
      intro s t
      change kMuPsi (kRegion ctx s t) = _
      rw [kMuPsi_kRegion]
      congr 1
      symm
      rw [LF2.PurePreparation.born_rank_one_direct
            (kSectorData p₀) (fubiniStudyMeasure p₀) (kBridge p₀) kMuPsi
            (kPurePrep p₀) ((kJED ctx hgen).eig s t) ((kJED ctx hgen).eig_unit s t)]
      exact kEig_born ctx hgen s t)

/-! ### Concrete capstone: non-vacuous instance of the LF1↔LF2↔LF3 chain

Applying `LF3_singlet_frequency_convergence` to the concrete `ofKählerPreparation`
yields a fully non-parametric empirical statement: for i.i.d. trials with law
`(ofKählerPreparation …).μψ`, the per-sector empirical frequencies converge
almost surely to `P_st`. This is the witness that the LF3 chain capstones are
**non-vacuous**: there exists a `PureSingletPreparation` they can be applied to.
-/

open Filter Topology in
/-- **The chain is non-vacuous on this instance.** For i.i.d. trials with the
posited fibre law, the per-sector empirical frequencies converge a.s. to
`P_st ctx.a ctx.b s t`. Foundational-triple-only / Gleason-free (the LF3 chain
routes through the Busch-free `weight_eq_P_st` / `OP_p_at_jointEig_eq_P_st_direct`,
2026-06-02 re-route). -/
theorem ofKählerPreparation_singlet_frequency_convergence
    (p₀ : CPN 4) (hgen : ∀ s t : Sign, 0 < P_st ctx.a ctx.b s t)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → KSigma 4} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = (ofKählerPreparation ctx p₀ hgen).μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator
              (X n ⁻¹' ((ofKählerPreparation ctx p₀ hgen).O_region s t).preEvent)
              (fun _ => (1 : ℝ))))) :
    ∀ s t, ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                (X i ⁻¹' ((ofKählerPreparation ctx p₀ hgen).O_region s t).preEvent)
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (P_st ctx.a ctx.b s t)) :=
  LF3.LF3_singlet_frequency_convergence
    (kSectorData p₀) ctx (ofKählerPreparation ctx p₀ hgen) hX hlaw hindep

end LF4
end CSD

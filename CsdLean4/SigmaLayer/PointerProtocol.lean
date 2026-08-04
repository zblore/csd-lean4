/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerLanding
public import CsdLean4.SigmaLayer.MeasurementProtocol
public import CsdLean4.SigmaLayer.RecordPersistence

/-!
# SigmaLayer/PointerProtocol: the smooth witness as a measurement protocol (brick 4a)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 4, protocol half).

The pointer witness enters the corpus's standard record architecture: a
`MeasurementProtocol` on `PointerArena N N` whose two-time propagator is the **ramped
exponential of the selector-modulated coupling**,

  `Φ_{s→t}(x, q) = (x, exp((κ(t) − κ(s)) • (−i • couplingH (w x))) • q)`,

with `κ` the `C⁰` ramp `t ↦ (π/2)·clamp₀¹(t)` frozen after the readout time. Everything the
piecewise witnesses had to fight for arrives structurally:

* **the two-time law is the group property** of the exponential (`couplingUAt_mul`, from
  `Matrix.exp_add_of_commute` — the same generator always commutes with itself), against the
  swap's eight-case crossing analysis;
* **persistence is freezing**: after the readout time the ramp is constant, the angle
  increment is `0`, the propagator is the identity — `PointerInvariantOn` is discharged
  outright (`pointerProtocol_pointerInvariantOn`), so `record_persists_on_interval` and
  `readout_persists_on_interval` apply verbatim;
* **the correlation obligation is the landing theorem**: `CorrelatesOn (pointerSector …)`
  (`pointerProtocol_correlatesOn`) with sectors = shrunk cell × ready region, via
  `pointer_landing` at the stroke `evolve 0 1 = pointerEvolve`
  (`pointerProtocol_evolve_stroke`);
* ★ **the propagator is jointly continuous in time and state**
  (`continuous_pointerRampedEvolve`, at every start time `s`; identified with the protocol's
  `evolve` by `pointerRampedEvolve_eq_protocol`) — *Corrected 2026-08-04 (codebase audit).*: this cited
  `continuous_pointerProtocolEvolve`, a name that exists nowhere in the corpus — against not
  only `shearEvolve_not_continuous`
  (state discontinuity) but also the swap witnesses' record-triggered firing, which is
  discontinuous **in time**. Route: the entrywise time-Lipschitz estimate
  (`norm_couplingUAt_sub_time`, Duhamel with the roles of time and generator swapped) plus
  the weight estimate, squeezed through `tendsto_iff_dist_tendsto_zero`; the projective
  action by the generic open-quotient descent `continuous_unitaryFamily_smul`.

⚠️ **Honest scope.** The correlation and invariance are established for **this** protocol's
sectors, which cover `1 − 2Nε` of the selector mass, not all of it — the corridor is the
`no_everywhere_correlation` price, as everywhere on this route. The ramp is `C⁰`
(piecewise-linear in time); upgrading to a `C^∞` ramp changes nothing structural and is
recorded in the plan as part of brick 5's presentation. The `ε`-Born sector sandwich is
brick 4b, not this module.

## References

`specs/pointer-witness-plan.md` (brick 4); `specs/BACKLOG.md` (the ★ L row);
`specs/future-work.md`. Reused corpus API: `MeasurementProtocol` +
`CorrelatesOn`/`PointerInvariantOn` (`SigmaLayer/MeasurementProtocol.lean`,
`RecordPersistence.lean`), `pointer_landing`/`shrunkCell` (`SigmaLayer/PointerLanding.lean`),
`couplingH`/`couplingU` estimates (`SigmaLayer/PointerCoupling.lean`),
`Matrix.norm_exp_smul_sub_exp_smul_le` + `Matrix.conjTranspose_real_smul_skew`
(`DuhamelBound.lean` staging), `Matrix.exp_add_of_commute` (Mathlib).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup NormedSpace
open scoped Matrix.Norms.L2Operator

variable {K : ℕ}

/-! ### The propagator at an arbitrary angle -/

/-- The coupling propagator at angle `a`: `exp(a • (−i • couplingH w))`. Brick 2a's
`couplingU` is the stroke value `a = π/2`. -/
noncomputable def couplingUAt (a : ℝ) (w : Fin K → ℝ) :
    Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  NormedSpace.exp (a • ((-Complex.I) • couplingH w))

theorem couplingUAt_pi_div_two (w : Fin K → ℝ) :
    couplingUAt (Real.pi / 2) w = couplingU w := rfl

theorem couplingUAt_zero (w : Fin K → ℝ) : couplingUAt 0 w = 1 := by
  rw [couplingUAt, zero_smul, NormedSpace.exp_zero]

/-- **The angle-additive law** — the two-time composition of the smooth witness is the
group property of the exponential, not a case analysis. -/
theorem couplingUAt_mul (a b : ℝ) (w : Fin K → ℝ) :
    couplingUAt a w * couplingUAt b w = couplingUAt (a + b) w := by
  unfold couplingUAt
  rw [add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl ((-Complex.I) • couplingH w)).smul_left a).smul_right b)]

theorem couplingUAt_mem_unitaryGroup (a : ℝ) (w : Fin K → ℝ) :
    couplingUAt a w ∈ Matrix.unitaryGroup (Fin (K + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  show (couplingUAt a w)ᴴ * couplingUAt a w = 1
  exact CSD.StoneC1.exp_smul_unitary ((-Complex.I) • couplingH w) (couplingH_skew w) a

/-- The angle-`a` propagator as a unitary-group element. -/
noncomputable def couplingUUAt (a : ℝ) (w : Fin K → ℝ) :
    Matrix.unitaryGroup (Fin (K + 1)) ℂ :=
  ⟨couplingUAt a w, couplingUAt_mem_unitaryGroup a w⟩

theorem couplingUUAt_zero (w : Fin K → ℝ) : couplingUUAt 0 w = 1 :=
  Subtype.ext (couplingUAt_zero w)

theorem couplingUUAt_mul (a b : ℝ) (w : Fin K → ℝ) :
    couplingUUAt a w * couplingUUAt b w = couplingUUAt (a + b) w :=
  Subtype.ext (couplingUAt_mul a b w)

theorem couplingUUAt_pi_div_two (w : Fin K → ℝ) :
    couplingUUAt (Real.pi / 2) w = couplingUU w := rfl

/-! ### The two Lipschitz estimates and joint entry continuity -/

/-- The Duhamel estimate in the **weights**, at an arbitrary angle. -/
theorem norm_couplingUAt_sub_le (a : ℝ) (w w' : Fin K → ℝ) :
    ‖couplingUAt a w - couplingUAt a w'‖
      ≤ |a| * (∑ j : Fin K, ‖pointerH j‖) * dist w w' := by
  have hd : ‖couplingUAt a w - couplingUAt a w'‖
      ≤ |a| * ‖couplingH w - couplingH w'‖ := by
    unfold couplingUAt
    exact Matrix.norm_exp_smul_neg_I_sub_le _ _ (couplingH_isHermitian w)
      (couplingH_isHermitian w') a
  calc ‖couplingUAt a w - couplingUAt a w'‖
      ≤ |a| * ‖couplingH w - couplingH w'‖ := hd
    _ ≤ |a| * ((∑ j : Fin K, ‖pointerH j‖) * dist w w') :=
        mul_le_mul_of_nonneg_left (norm_couplingH_sub_le w w') (abs_nonneg a)
    _ = |a| * (∑ j : Fin K, ‖pointerH j‖) * dist w w' := by ring

/-- The Duhamel estimate in the **angle** — time and generator with roles swapped:
`exp(1 • (a•A)) − exp(1 • (b•A))` for the skew generators `a•A`, `b•A`. -/
theorem norm_couplingUAt_sub_time (a b : ℝ) (w : Fin K → ℝ) :
    ‖couplingUAt a w - couplingUAt b w‖ ≤ |a - b| * ‖couplingH w‖ := by
  have hskew0 : ((-Complex.I) • couplingH w)ᴴ = -((-Complex.I) • couplingH w) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact couplingH_skew w
  have h := Matrix.norm_exp_smul_sub_exp_smul_le
    (a • ((-Complex.I) • couplingH w)) (b • ((-Complex.I) • couplingH w))
    (Matrix.conjTranspose_real_smul_skew hskew0 a)
    (Matrix.conjTranspose_real_smul_skew hskew0 b) 1
  rw [one_smul, one_smul, abs_one, one_mul] at h
  calc ‖couplingUAt a w - couplingUAt b w‖
      = ‖exp (a • ((-Complex.I) • couplingH w)) - exp (b • ((-Complex.I) • couplingH w))‖ :=
        rfl
    _ ≤ ‖a • ((-Complex.I) • couplingH w) - b • ((-Complex.I) • couplingH w)‖ := h
    _ = ‖(a - b) • ((-Complex.I) • couplingH w)‖ := by rw [sub_smul]
    _ = |a - b| * ‖(-Complex.I) • couplingH w‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ = |a - b| * ‖couplingH w‖ := by
        rw [norm_smul, norm_neg, Complex.norm_I, one_mul]

/-- **Joint continuity of each propagator entry in (angle, weights)** — squeezed between
the two Lipschitz estimates; no scoped-instance topology appears in the statement. -/
theorem continuous_couplingUAt_entry_joint (b d : Fin (K + 1)) :
    Continuous fun z : ℝ × (Fin K → ℝ) => couplingUAt z.1 z.2 b d := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ z : ℝ × (Fin K → ℝ),
      dist (couplingUAt z.1 z.2 b d) (couplingUAt z₀.1 z₀.2 b d)
        ≤ |z.1| * (∑ j : Fin K, ‖pointerH j‖) * dist z.2 z₀.2
          + |z.1 - z₀.1| * ‖couplingH z₀.2‖ := by
    intro z
    calc dist (couplingUAt z.1 z.2 b d) (couplingUAt z₀.1 z₀.2 b d)
        = ‖couplingUAt z.1 z.2 b d - couplingUAt z₀.1 z₀.2 b d‖ := dist_eq_norm _ _
      _ = ‖(couplingUAt z.1 z.2 - couplingUAt z₀.1 z₀.2) b d‖ := by rw [Matrix.sub_apply]
      _ ≤ ‖couplingUAt z.1 z.2 - couplingUAt z₀.1 z₀.2‖ :=
          Matrix.norm_entry_le_l2_opNorm _ b d
      _ ≤ ‖couplingUAt z.1 z.2 - couplingUAt z.1 z₀.2‖
            + ‖couplingUAt z.1 z₀.2 - couplingUAt z₀.1 z₀.2‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub
            (couplingUAt z.1 z.2) (couplingUAt z.1 z₀.2) (couplingUAt z₀.1 z₀.2)
          exact this
      _ ≤ |z.1| * (∑ j : Fin K, ‖pointerH j‖) * dist z.2 z₀.2
            + |z.1 - z₀.1| * ‖couplingH z₀.2‖ :=
          add_le_add (norm_couplingUAt_sub_le z.1 z.2 z₀.2)
            (norm_couplingUAt_sub_time z.1 z₀.1 z₀.2)
  have hg : Continuous fun z : ℝ × (Fin K → ℝ) =>
      |z.1| * (∑ j : Fin K, ‖pointerH j‖) * dist z.2 z₀.2
        + |z.1 - z₀.1| * ‖couplingH z₀.2‖ := by
    refine Continuous.add ?_ ?_
    · exact ((continuous_fst.abs.mul continuous_const).mul
        (continuous_snd.dist continuous_const))
    · exact ((continuous_fst.sub continuous_const).abs.mul continuous_const)
  refine squeeze_zero (fun z => dist_nonneg) hbound ?_
  have htend := hg.tendsto z₀
  simp only [dist_self, mul_zero, sub_self, abs_zero, zero_mul, add_zero] at htend
  exact htend

/-! ### The generic continuous unitary action -/

/-- **A continuous family of unitaries acts continuously on the pointer** — the open-quotient
descent of brick 2b, factored out for reuse: any topological parameter space, any continuous
family into the unitary group (Pi topology). -/
theorem continuous_unitaryFamily_smul {X : Type*} [TopologicalSpace X]
    {U : X → Matrix.unitaryGroup (Fin (K + 1)) ℂ} (hU : Continuous U) :
    Continuous fun z : X × Pointer K => U z.1 • z.2 := by
  have hQ : IsOpenQuotientMap
      (Prod.map (id : X → X)
        (Projectivization.mk' ℂ :
          {v : EuclideanSpace ℂ (Fin (K + 1)) // v ≠ 0} → Pointer K)) :=
    IsOpenQuotientMap.id.prodMap Projectivization.isOpenQuotientMap_mk'
  rw [hQ.isQuotientMap.continuous_iff]
  have hvec : Continuous fun z : X × {v : EuclideanSpace ℂ (Fin (K + 1)) // v ≠ 0} =>
      (Matrix.toEuclideanLin (U z.1).val z.2.val : EuclideanSpace ℂ (Fin (K + 1))) := by
    show Continuous fun z : X × {v : EuclideanSpace ℂ (Fin (K + 1)) // v ≠ 0} =>
      (WithLp.toLp 2 ((U z.1).val *ᵥ (WithLp.ofLp z.2.val))
        : EuclideanSpace ℂ (Fin (K + 1)))
    refine (PiLp.continuous_toLp _ _).comp ?_
    refine Continuous.matrix_mulVec ?_ ?_
    · exact continuous_subtype_val.comp (hU.comp continuous_fst)
    · exact (PiLp.continuous_ofLp _ _).comp (continuous_subtype_val.comp continuous_snd)
  have hkey : ((fun z : X × Pointer K => U z.1 • z.2)
      ∘ (Prod.map id (Projectivization.mk' ℂ)))
      = fun z : X × {v : EuclideanSpace ℂ (Fin (K + 1)) // v ≠ 0} =>
          Projectivization.mk' ℂ
            ⟨Matrix.toEuclideanLin (U z.1).val z.2.val,
              toEuclideanLin_unitary_apply_ne_zero (U z.1) z.2.2⟩ := by
    funext z
    show U z.1 • (Projectivization.mk' ℂ z.2) = _
    rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk]
    exact Projectivization.smul_mk_eq_mk_toEuclideanLin _ z.2.2
  rw [hkey]
  exact Projectivization.continuous_mk'.comp (hvec.subtype_mk _)

/-! ### The ramp and the protocol -/

/-- The measurement ramp: zero before the interaction, frozen at the quarter-turn stroke
after readout.

★ *Substituted onto the `C^∞` profile 2026-08-04 (`BACKLOG.md` B1b).* This was
`(π/2)·clamp₀¹(t)`, piecewise-linear with corners at `t ∈ {0,1}` — which is why
`rampedU_schrodinger` could only hold on the **open** window `(0,1)`. It is now
`(π/2)·smoothTransition t`, `C^∞` everywhere. The plateau interface is unchanged
(`pointerRamp_zero`, `pointerRamp_of_one_le`), so the protocol's two-time law, freezing and
persistence are untouched; what changes is the generation statement, which now holds at
**every** time and carries the rate factor `smoothTransition′(t)` — a window-free ODE in
place of a constant-generator one on a punctured interval. -/
noncomputable def pointerRamp (t : ℝ) : ℝ := smoothPointerRamp t

theorem pointerRamp_zero : pointerRamp 0 = 0 :=
  smoothPointerRamp_of_nonpos le_rfl

theorem pointerRamp_of_one_le {t : ℝ} (ht : 1 ≤ t) : pointerRamp t = Real.pi / 2 :=
  smoothPointerRamp_of_one_le ht

theorem pointerRamp_one : pointerRamp 1 = Real.pi / 2 :=
  pointerRamp_of_one_le le_rfl

theorem continuous_pointerRamp : Continuous pointerRamp :=
  (contDiff_smoothPointerRamp (n := 0)).continuous

/-- **The ramp is `C^∞`** — new with the B1b substitution; the trapezoid was only
Lipschitz. -/
theorem contDiff_pointerRamp {n : ℕ∞} : ContDiff ℝ n pointerRamp :=
  contDiff_smoothPointerRamp

variable {N : ℕ} [NeZero N]

/-- ★ **The smooth witness as a measurement protocol.** Two-time propagator = ramped
exponential of the selector-modulated coupling; ready/pointer regions = the brick-0
cylinders. The two-time law is the exponential group property; freezing after readout makes
persistence structural. -/
noncomputable def pointerProtocol (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) {δ : ℝ} (hδ : δ ≤ 1 / 2) :
    MeasurementProtocol (PointerArena N N) N where
  evolve s t := fun y =>
    (y.1, couplingUUAt (pointerRamp t - pointerRamp s) (pointerWeights c ε y.1) • y.2)
  evolve_self t := by
    funext y
    show (y.1, couplingUUAt (pointerRamp t - pointerRamp t) (pointerWeights c ε y.1) • y.2)
      = y
    rw [sub_self, couplingUUAt_zero, one_smul]
  evolve_comp s t u := by
    funext y
    show (y.1, couplingUUAt (pointerRamp u - pointerRamp t) (pointerWeights c ε y.1)
        • (couplingUUAt (pointerRamp t - pointerRamp s) (pointerWeights c ε y.1) • y.2))
      = (y.1, couplingUUAt (pointerRamp u - pointerRamp s) (pointerWeights c ε y.1) • y.2)
    rw [← mul_smul, couplingUUAt_mul,
      show (pointerRamp u - pointerRamp t) + (pointerRamp t - pointerRamp s)
        = pointerRamp u - pointerRamp s from by ring]
  measurable_evolve s t := by
    have hU : Continuous fun x : LF4.KSigma N =>
        couplingUUAt (pointerRamp t - pointerRamp s) (pointerWeights c ε x) := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_matrix fun b d => ?_
      exact (continuous_couplingUAt_entry_joint b d).comp
        (continuous_const.prodMk (continuous_pointerWeights c hc ε))
    exact measurable_fst.prodMk (continuous_unitaryFamily_smul hU).measurable
  startTime := 0
  readoutTime := 1
  recordDuration := 1
  readyRegion := arenaReady N δ
  pointerRegion := arenaRecord N
  measurableSet_ready := measurableSet_arenaReady _
  measurableSet_pointer := measurableSet_arenaRecord
  pointer_pairwiseDisjoint := by
    intro i j hij
    refine Set.disjoint_left.mpr fun y hyi hyj => ?_
    exact Set.disjoint_left.mp (recordRegion_pairwiseDisjoint hij) hyi.2 hyj.2
  ready_disjoint_pointer := by
    intro i
    refine Set.disjoint_left.mpr fun y hyr hyi => ?_
    exact Set.disjoint_left.mp (readyRegion_disjoint_recordRegion hδ i) hyr.2 hyi.2

omit [NeZero N] in
/-- The full-stroke identification: `Φ_{0→1}` **is** the brick-2b propagator. -/
theorem pointerProtocol_evolve_stroke (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) {δ : ℝ} (hδ : δ ≤ 1 / 2) :
    (pointerProtocol c hc ε hδ).evolve 0 1 = pointerEvolve c ε := by
  funext y
  show (y.1, couplingUUAt (pointerRamp 1 - pointerRamp 0) (pointerWeights c ε y.1) • y.2)
    = (y.1, couplingUU (pointerWeights c ε y.1) • y.2)
  rw [pointerRamp_one, pointerRamp_zero, sub_zero, couplingUUAt_pi_div_two]

omit [NeZero N] in
/-- The propagator, unfolded — the definitional bridge used by every statement below. -/
theorem pointerProtocol_evolve_apply (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (s t : ℝ) (y : PointerArena N N) :
    (pointerProtocol c hc ε hδ).evolve s t y
      = (y.1, couplingUUAt (pointerRamp t - pointerRamp s)
          (pointerWeights c ε y.1) • y.2) := rfl

/-- The ramped unitary family, named so continuity statements carry concrete types. -/
noncomputable def rampedUU (c : ContextField N) (ε s : ℝ) (v : ℝ × LF4.KSigma N) :
    Matrix.unitaryGroup (Fin (N + 1)) ℂ :=
  couplingUUAt (pointerRamp v.1 - pointerRamp s) (pointerWeights c ε v.2)

omit [NeZero N] in
theorem continuous_rampedUU (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε s : ℝ) :
    Continuous (rampedUU c ε s) := by
  unfold rampedUU couplingUUAt
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun b d => ?_
  exact (continuous_couplingUAt_entry_joint b d).comp
    (((continuous_pointerRamp.comp continuous_fst).sub continuous_const).prodMk
      ((continuous_pointerWeights c hc ε).comp continuous_snd))

/-- The ramped arena propagator as a time–state map: definitionally
`(pointerProtocol c hc ε hδ).evolve s z.1 z.2` (see `pointerRampedEvolve_eq_protocol`). -/
noncomputable def pointerRampedEvolve (c : ContextField N) (ε s : ℝ) :
    ℝ × PointerArena N N → PointerArena N N :=
  fun z => (z.2.1, rampedUU c ε s (z.1, z.2.1) • z.2.2)

omit [NeZero N] in
/-- The named map is the protocol propagator, definitionally. -/
theorem pointerRampedEvolve_eq_protocol (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (s : ℝ) (z : ℝ × PointerArena N N) :
    pointerRampedEvolve c ε s z = (pointerProtocol c hc ε hδ).evolve s z.1 z.2 := rfl

omit [NeZero N] in
/-- ★ **Joint continuity in time and state** — the property neither piecewise witness has:
the shear/swap witnesses jump in the state (`shearEvolve_not_continuous`) and fire
discontinuously in time at the crossing; the smooth witness does neither
(`pointerRampedEvolve_eq_protocol` identifies this map with the protocol's propagator). -/
theorem continuous_pointerRampedEvolve (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε s : ℝ) :
    Continuous (pointerRampedEvolve c ε s) := by
  unfold pointerRampedEvolve
  refine Continuous.prodMk (continuous_fst.comp continuous_snd) ?_
  have hmain := continuous_unitaryFamily_smul (continuous_rampedUU c hc ε s)
  have hcomp : (fun z : ℝ × PointerArena N N => rampedUU c ε s (z.1, z.2.1) • z.2.2)
      = (fun w : (ℝ × LF4.KSigma N) × Pointer N => rampedUU c ε s w.1 • w.2)
        ∘ (fun z : ℝ × PointerArena N N => ((z.1, z.2.1), z.2.2)) := rfl
  rw [hcomp]
  exact Continuous.comp hmain ((continuous_fst.prodMk
    (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd))

/-! ### Correlation and persistence -/

/-- The selector sectors of the smooth witness: shrunk cell × ready region. -/
def pointerSector (c : ContextField N) (ε δ : ℝ) (j : Fin N) :
    Set (PointerArena N N) :=
  shrunkCell c ε j ×ˢ readyRegion δ

omit [NeZero N] in
theorem measurableSet_pointerSector (c : ContextField N) (ε δ : ℝ) (j : Fin N) :
    MeasurableSet (pointerSector c ε δ j) :=
  (measurableSet_shrunkCell c ε j).prod (measurableSet_readyRegion δ)

omit [NeZero N] in
/-- **The correlation obligation, discharged**: every pointer sector is carried into its
outcome's record cylinder — the landing theorem in protocol form. -/
theorem pointerProtocol_correlatesOn (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ≤ 1 / 2) :
    (pointerProtocol c hc ε hδ).CorrelatesOn (pointerSector c ε δ) := by
  intro j y hy
  show (pointerProtocol c hc ε hδ).evolve 0 1 y ∈ arenaRecord N j
  rw [pointerProtocol_evolve_stroke]
  exact pointer_landing c hε hδ hy.1 hy.2

omit [NeZero N] in
/-- **Persistence is structural**: after readout the ramp is frozen, the propagator is the
identity on the record window, so the pointer regions are invariant. -/
theorem pointerProtocol_pointerInvariantOn (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) {δ : ℝ} (hδ : δ ≤ 1 / 2) :
    (pointerProtocol c hc ε hδ).PointerInvariantOn := by
  intro i s t hs hst _ x hx
  show (x.1, couplingUUAt (pointerRamp t - pointerRamp s) (pointerWeights c ε x.1) • x.2)
    ∈ arenaRecord N i
  rw [pointerRamp_of_one_le hs, pointerRamp_of_one_le (hs.trans hst), sub_self,
    couplingUUAt_zero, one_smul]
  exact hx

end CSD.RecordLayer

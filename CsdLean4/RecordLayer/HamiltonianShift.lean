/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.JointLift
public import CsdLean4.RecordLayer.PointerGeneration
public import CsdLean4.RecordLayer.PointerHamiltonianField
public import CsdLean4.SigmaLayer.ChartIntegralCurve

/-!
# RecordLayer/HamiltonianShift: the shift the stroke Hamiltonian generates

**Category:** dynamical measurement — `specs/BACKLOG.md` §A; brick 3 of
`specs/frozen-base-obstruction-scoping.md`, third step (chart-level generation of each
component of the joint lift).

## What this is

`JointLift.lean` took the torus shift `Δ` as a **parameter** and proved that every
conserved-data shift is harmless to records, Born and Liouville measure. This module builds
the shift the interaction Hamiltonian actually produces, and proves — at the chart level, on
regular data — that it is what the stroke Hamiltonian generates in the conjugate directions.

The setting. Conserved data `d = (m, θ₁, q)` (`ConservedData`): context rates, register,
pointer. The chart positions are `x = (m, rep θ₁) ∈ ℝ^{N+1}` (`chartPos`) and the momenta
are their conjugates — the `N` moment-fibre phases and `θ₂`. The weights the stroke reads are
`W(x) = arcWeights ε x`, and `arcWeights_chartPos` says they are exactly the arena's
`pointerWeights`. The stroke Hamiltonian, for a fixed pointer `q`, is

  `𝓗_t(x, y) = ṫ(t) · (π/2) · E(W(x), q)`,   `E(w, q) = ⟨q, H(w) q⟩ / ‖q‖²`

(`strokeH`, `pointerEnergy`): the ramped coupling energy whose Schrödinger flow drives the
pointer (`rampedU_schrodinger`, `coupling_hamiltonian_duality`), now read as a function on the
base chart through the weights. Hamilton's equations in the chart are

  `ẋ = ∂ᵧ𝓗 = 0`,   `ẏᵢ = −∂ₓᵢ𝓗_t = −ṫ(t) (π/2) Σₖ Eₖ(q) ∂ᵢWₖ(x)`

(`dMom_strokeH`, `dPos_strokeH`, `hamiltonianField_strokeH`): the positions — rates and
register, everything the record reads — are **frozen**, and the back-reaction goes entirely
into the momenta. This is the frozen-base obstruction dissolved rather than denied: the base
moves, but along the moment fibre, where the record cannot see it.

Evaluating along the actual pointer trajectory `q(s) = strokeTraj ε d s` and integrating over
the stroke gives the momentum shift

  `shiftReal ε d i = −Σₖ (∫₀¹ ṫ (π/2) Eₖ(q(s)) ds) · ∂ᵢWₖ(x₀)`

and `hamiltonianShift ε d` is that shift read on the arena torus — the `Δ` fed to
`jointLift`.

## Results

* `pointerEnergy`, `pointerEnergy_eq_sum`, `hasFDerivAt_pointerEnergy`,
  `continuous_pointerEnergy` — the projective coupling energy: well defined on `ℙ`, linear
  in the weights with gradient `energyGradient`, continuous in the pointer.
* `arcWeights`, `arcWeights_chartPos`, `contDiffAt_arcWeights` — the chart weights agree
  with the arena weights and are `C^∞` at every **regular** position (`RegularPos`: every
  rate in `(2ε, 1)`, so both non-smooth points of the circle distance — the cell midpoint
  and its antipode — fall inside a plateau of the profile).
* `OffCorridor`, `fderiv_arcWeights_eq_zero_of_offCorridor` — where the register sits
  strictly inside a plateau of every cell, the weights are locally constant.
* `strokeTraj`, `strokeTraj_one_eq_pointerEvolve`, `strokeEnergy`, `avgEnergy`,
  `shiftReal`, `hamiltonianShift`, `measurable_hamiltonianShift` — the trajectory, the
  stroke energies along it, and the integrated shift; measurable in the conserved data.
* `strokeCurve`, `strokeCurve_zero`, `strokeCurve_one_snd`,
  `hamiltonianShift_eq_strokeCurve_one` — the chart curve with frozen positions and
  accumulating momenta; its endpoint **is** the shift.
* ★★ `strokeCurve_hasDerivAt_hamiltonianField` — on regular data the curve is an integral
  curve of the time-dependent stroke Hamiltonian evaluated on the pointer trajectory:
  `γ̇(t) = X_{𝓗_t(q(t))}(γ(t))` for every `t`.
* ★★ `isJointLift_hamiltonianShift`, `jointLift_hamiltonianShift_measurePreserving` — the
  joint lift with the generated shift is a joint lift (so landing, the `ε`-Born sandwich, the
  outcome-sector identity and the moment-marginal law all hold for it) and preserves the
  arena Liouville measure.
* `jointLift_eq_pointerEvolve_off_corridor` — off the corridor the generated shift vanishes
  and the joint lift is the fibrewise witness, as `SigmaLayer/UntriggeredFlow.lean` predicts
  for the untriggered region.

## What this does and does not settle

*Chart level, regular data.* Generation is proved in the Darboux chart of
`SigmaLayer/ChartBracket.lean`, for a time-dependent Hamiltonian (so stated directly as
`HasDerivAt … (hamiltonianField (strokeH ε t …) …)` rather than through the autonomous
`IsHamiltonianCurve`), and only on regular data. The construction itself is total: at a
non-regular position the weights need not be differentiable and `fderiv` is `0` there by
Mathlib's convention, so `hamiltonianShift` is defined everywhere and measurable everywhere;
the generation statement is claimed only where the weights are smooth.

*Nonvanishing.* That `hamiltonianShift` is actually non-zero — that the integrated energies
against the weight derivatives produce phases differing on two coordinates supporting the
state, which is what `jointLift_base_moves_of_ne` needs — is not claimed here. The
computation is one about the coupling generators along the trajectory: in a collar where only
one weight `Wₖ` varies the stroke Hamiltonian is `ṫ(π/2) Wₖ hₖ`, so `Eₖ` is conserved along
the trajectory and vanishes on the ready pointer (`hₖ` is off-diagonal against `e₀`), while at
a shared cell edge two weights vary at once and the energies are not conserved. This
heuristic is paper-side and not formalised.

*Arena level.* Nothing here identifies `jointLift c ε (hamiltonianShift ε)` with the time-`1`
map of a Hamiltonian flow on the arena Kähler manifold — the chart→arena transport of the
generation statement is what is missing (⚠️ RESIDUE(R-016)), now with the chart-level
generation of the shift components in hand.

## References

`specs/frozen-base-obstruction-scoping.md` (brick 3); `specs/future-work.md`;
`RecordLayer/JointLift.lean` (`jointLift`, `isJointLift_jointLift`,
`jointLift_measurePreserving`, `jointLift_base_moves_of_ne`);
`RecordLayer/JointFlowTransfer.lean` (`IsJointLift`); `RecordLayer/PointerGeneration.lean`
(`rampedU_schrodinger`, `couplingUAt`); `RecordLayer/PointerHamiltonianField.lean`
(`coupling_hamiltonian_duality`, `couplingEnergy`); `RecordLayer/SmoothProfile.lean`
(`contDiff_smoothArcWeight_lift`, of which `contDiffAt_smoothArcWeight_lift₃` is the joint
three-variable version); `SigmaLayer/ChartBracket.lean` (`hamiltonianField`, `dPos`, `dMom`);
`SigmaLayer/ChartIntegralCurve.lean` (`IsHamiltonianCurve`,
`translationCurve_isHamiltonianCurve`); `SigmaLayer/UntriggeredFlow.lean`.
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Kahler CSD.SigmaLayer
open scoped Topology

variable {N K : ℕ}

/-! ### The projective coupling energy -/

/-- The coupling energy scales quadratically under complex rescaling of the state. -/
lemma couplingEnergy_smul (w : Fin K → ℝ) (a : ℂ) (v : EuclideanSpace ℂ (Fin (K + 1))) :
    couplingEnergy w (a • v) = ‖a‖ ^ 2 * couplingEnergy w v := by
  unfold couplingEnergy quadraticEnergy metric
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul',
    ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

/-- **The projective coupling energy** `E_w([v]) = couplingEnergy w v / ‖v‖²`: the A4 energy
observable of the fixed-weight coupling, read on the pointer's projective space (the
normalised expectation `½⟨ψ, H(w)ψ⟩/‖ψ‖²`). Well defined on the projective point by
`couplingEnergy_smul`; see `pointerEnergy_mk`. -/
noncomputable def pointerEnergy (w : Fin K → ℝ) (q : Pointer K) : ℝ :=
  couplingEnergy w q.rep / ‖q.rep‖ ^ 2

/-- The projective energy at a representative. -/
lemma pointerEnergy_mk (w : Fin K → ℝ) (v : EuclideanSpace ℂ (Fin (K + 1))) (hv : v ≠ 0) :
    pointerEnergy w (Projectivization.mk ℂ v hv) = couplingEnergy w v / ‖v‖ ^ 2 := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ v hv).rep v
        (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  unfold pointerEnergy
  rw [← ha, Units.smul_def, couplingEnergy_smul, norm_smul, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr a.ne_zero))]

/-- The coupling operator is linear in the weights: `H(w) = Σₖ wₖ H(eₖ)` on every vector. -/
lemma couplingCLM_apply_eq_sum (w : Fin K → ℝ) (v : EuclideanSpace ℂ (Fin (K + 1))) :
    couplingCLM w v = ∑ k, (w k : ℂ) • couplingCLM (Pi.single k 1) v := by
  show Matrix.toEuclideanLin (couplingH w) v
    = ∑ k, (w k : ℂ) • Matrix.toEuclideanLin (couplingH (Pi.single k 1)) v
  simp_rw [couplingH_single]
  unfold couplingH
  rw [map_sum, LinearMap.sum_apply]
  simp_rw [map_smul, LinearMap.smul_apply]

/-- The coupling energy is linear in the weights. -/
lemma couplingEnergy_eq_sum (w : Fin K → ℝ) (v : EuclideanSpace ℂ (Fin (K + 1))) :
    couplingEnergy w v = ∑ k, w k * couplingEnergy (Pi.single k 1) v := by
  unfold couplingEnergy quadraticEnergy metric
  rw [couplingCLM_apply_eq_sum, inner_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, Complex.re_ofReal_mul]
  ring

/-- **The outcome energy** `Eₖ(q)`: the projective energy of the pure plane swap `hₖ`, the
`k`-th coefficient of the projective coupling energy in the weights. -/
noncomputable abbrev outcomeEnergy (k : Fin K) (q : Pointer K) : ℝ :=
  pointerEnergy (Pi.single k 1) q

/-- The projective coupling energy is linear in the weights: `E_w(q) = Σₖ wₖ Eₖ(q)`. -/
theorem pointerEnergy_eq_sum (w : Fin K → ℝ) (q : Pointer K) :
    pointerEnergy w q = ∑ k, w k * outcomeEnergy k q := by
  unfold outcomeEnergy pointerEnergy
  rw [couplingEnergy_eq_sum, Finset.sum_div]
  simp_rw [mul_div_assoc]

/-- The weight-gradient of the projective coupling energy at a fixed pointer state. -/
noncomputable def energyGradient (q : Pointer K) : (Fin K → ℝ) →L[ℝ] ℝ :=
  ∑ k, outcomeEnergy k q • ContinuousLinearMap.proj k

@[simp] lemma energyGradient_apply (q : Pointer K) (u : Fin K → ℝ) :
    energyGradient q u = ∑ k, outcomeEnergy k q * u k := by
  unfold energyGradient
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The projective coupling energy is differentiable in the weights, with derivative
`energyGradient q`. -/
theorem hasFDerivAt_pointerEnergy (q : Pointer K) (w : Fin K → ℝ) :
    HasFDerivAt (fun w : Fin K → ℝ => pointerEnergy w q) (energyGradient q) w := by
  have h : (fun w : Fin K → ℝ => pointerEnergy w q) = ∑ k, fun w : Fin K → ℝ => w k * outcomeEnergy k q := by
    funext w
    rw [pointerEnergy_eq_sum, Finset.sum_apply]
  rw [h]
  exact HasFDerivAt.sum fun k _ => (hasFDerivAt_apply k w).mul_const (outcomeEnergy k q)

/-- The projective coupling energy is continuous on the pointer (descent through `mk'`). -/
theorem continuous_pointerEnergy (w : Fin K → ℝ) : Continuous (pointerEnergy w) := by
  rw [Projectivization.continuous_iff_continuous_comp_mk']
  have hcomp : (pointerEnergy w ∘ Projectivization.mk' ℂ)
      = fun v : { v : EuclideanSpace ℂ (Fin (K + 1)) // v ≠ 0 } =>
          couplingEnergy w (v : EuclideanSpace ℂ (Fin (K + 1)))
            / ‖(v : EuclideanSpace ℂ (Fin (K + 1)))‖ ^ 2 := by
    funext v
    exact pointerEnergy_mk w (v : EuclideanSpace ℂ (Fin (K + 1))) v.2
  rw [hcomp]
  have hE : Continuous (couplingEnergy w) := by
    unfold couplingEnergy quadraticEnergy metric
    exact continuous_const.mul
      (Complex.continuous_re.comp (continuous_id.inner (couplingCLM w).continuous))
  exact (hE.comp continuous_subtype_val).div ((continuous_subtype_val.norm).pow 2)
    fun v => pow_ne_zero _ (norm_ne_zero_iff.mpr v.2)


/-! ### The weights on the joint chart -/

/-- The real lift of the cell midpoint `loSum r k + r k / 2` (so `cellMid r k = ↑(cellMidLift r k)`). -/
noncomputable def cellMidLift (r : Fin N → ℝ) (k : Fin N) : ℝ := loSum r k + r k / 2

lemma cellMid_eq_coe (r : Fin N → ℝ) (k : Fin N) :
    cellMid r k = ((cellMidLift r k : ℝ) : CircleFibre) := rfl

/-- **The weight field on the joint chart.** Positions `x : Fin (N+1) → ℝ` carry the `N`
context rates `x (castSucc k) = mₖ` and the register lift `x (last N) = θ₁`; the weights are
the smooth arc profiles read in these coordinates. On the arena this is `pointerWeights`
(`arcWeights_chartPos`). -/
noncomputable def arcWeights (ε : ℝ) (x : Fin (N + 1) → ℝ) : Fin N → ℝ :=
  fun k => smoothArcWeight ε (x (Fin.castSucc k)) (cellMid (Fin.init x) k)
    ((x (Fin.last N) : ℝ) : CircleFibre)

/-- The chart position of conserved data `(m, θ₁, q)`: the rates, then the canonical lift
of the register. -/
noncomputable def chartPos (d : ConservedData N) : Fin (N + 1) → ℝ :=
  Fin.snoc d.1 (rep d.2.1)

@[simp] lemma chartPos_castSucc (d : ConservedData N) (k : Fin N) :
    chartPos d (Fin.castSucc k) = d.1 k := Fin.snoc_castSucc _ _ k

@[simp] lemma chartPos_last (d : ConservedData N) : chartPos d (Fin.last N) = rep d.2.1 :=
  Fin.snoc_last _ _

lemma init_chartPos (d : ConservedData N) : Fin.init (chartPos d) = d.1 := Fin.init_snoc _ _

theorem measurable_chartPos : Measurable (chartPos (N := N)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [chartPos_last]
    exact measurable_rep.comp (measurable_fst.comp measurable_snd)
  · simp only [chartPos_castSucc]
    exact (measurable_pi_apply k).comp measurable_fst

/-- The arena weights of conserved data, in arena form (continuous in the data). -/
noncomputable def dataWeights (ε : ℝ) (d : ConservedData N) : Fin N → ℝ :=
  fun k => smoothArcWeight ε (d.1 k) (cellMid d.1 k) d.2.1

lemma dataWeights_conservedData (c : ContextField N) (ε : ℝ) (y : PointerArena N N) :
    dataWeights ε (conservedData c y) = pointerWeights c ε y.1 := rfl

/-- The chart weights at the chart position of conserved data are the arena weights. -/
theorem arcWeights_chartPos (ε : ℝ) (d : ConservedData N) :
    arcWeights ε (chartPos d) = dataWeights ε d := by
  funext k
  unfold arcWeights dataWeights
  rw [chartPos_castSucc, chartPos_last, init_chartPos, coe_rep]

theorem continuous_dataWeights (ε : ℝ) : Continuous (dataWeights (N := N) ε) := by
  refine continuous_pi fun k => ?_
  have hr : Continuous fun d : ConservedData N => d.1 k := (continuous_apply k).comp continuous_fst
  have hmid : Continuous fun d : ConservedData N => cellMid d.1 k := by
    rw [show (fun d : ConservedData N => cellMid d.1 k)
      = fun d => ((cellMidLift d.1 k : ℝ) : CircleFibre) from rfl]
    refine (AddCircle.continuous_mk' (p := (1 : ℝ))).comp ?_
    unfold cellMidLift loSum
    exact (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_fst).add
      (hr.div_const 2)
  have hθ : Continuous fun d : ConservedData N => d.2.1 := continuous_fst.comp continuous_snd
  show Continuous fun d : ConservedData N =>
    smoothClampDiv ε (d.1 k / 2 - dist d.2.1 (cellMid d.1 k))
  exact (contDiff_smoothClampDiv (n := 0) ε).continuous.comp ((hr.div_const 2).sub (hθ.dist hmid))

/-! ### Joint smoothness of the arc weight in (rate, midpoint, register) -/

/-- ★ **The smooth arc weight is `C^∞` jointly in the rate, the midpoint lift and the register
lift**, at every point with `2ε < r < 1`. The three-variable form of
`contDiff_smoothArcWeight_lift`: the circle distance is kinked only at the centre and the cut
locus, and both kinks fall inside plateaus of the profile (`ε < r/2`, `r < 1`); in the
transition zone the distance lift is locally the absolute value of an affine function that
does not vanish. -/
theorem contDiffAt_smoothArcWeight_lift₃ {ε : ℝ} (hε : 0 < ε) {z₀ : ℝ × ℝ × ℝ}
    (h2ε : 2 * ε < z₀.1) (hr : z₀.1 < 1) {n : ℕ∞} :
    ContDiffAt ℝ n (fun z : ℝ × ℝ × ℝ =>
      smoothArcWeight ε z.1 ((z.2.1 : ℝ) : CircleFibre) ((z.2.2 : ℝ) : CircleFibre)) z₀ := by
  have hcoe : Continuous fun s : ℝ => ((s : ℝ) : CircleFibre) :=
    AddCircle.continuous_mk' (p := (1 : ℝ))
  have hdc : Continuous fun z : ℝ × ℝ × ℝ =>
      dist ((z.2.2 : ℝ) : CircleFibre) ((z.2.1 : ℝ) : CircleFibre) :=
    (hcoe.comp (continuous_snd.comp continuous_snd)).dist
      (hcoe.comp (continuous_fst.comp continuous_snd))
  have hgap : Continuous fun z : ℝ × ℝ × ℝ =>
      z.1 / 2 - dist ((z.2.2 : ℝ) : CircleFibre) ((z.2.1 : ℝ) : CircleFibre) :=
    (continuous_fst.div_const 2).sub hdc
  set d₀ : ℝ := dist ((z₀.2.2 : ℝ) : CircleFibre) ((z₀.2.1 : ℝ) : CircleFibre) with hd₀
  by_cases hA : d₀ < z₀.1 / 2 - ε
  · -- centre plateau: locally ≡ 1
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hgap.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (show ε < z₀.1 / 2 - d₀ by linarith))] with z hz
    exact smoothArcWeight_eq_one hε (by simp only [Set.mem_preimage, Set.mem_Ioi] at hz; linarith)
  by_cases hB : z₀.1 / 2 < d₀
  · -- cut-locus plateau: locally ≡ 0
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hgap.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (show z₀.1 / 2 - d₀ < 0 by linarith))] with z hz
    exact smoothArcWeight_eq_zero hε (by simp only [Set.mem_preimage, Set.mem_Iio] at hz; linarith)
  -- transition zone: the distance lift is locally the absolute value of an affine function
  have hd₀lo : z₀.1 / 2 - ε ≤ d₀ := not_lt.mp hA
  have hd₀hi : d₀ ≤ z₀.1 / 2 := not_lt.mp hB
  have hd₀pos : 0 < d₀ := lt_of_lt_of_le (by linarith) hd₀lo
  have hd₀half : d₀ < 1 / 2 := lt_of_le_of_lt hd₀hi (by linarith)
  have hdist₀ : d₀ = |z₀.2.2 - z₀.2.1 - round (z₀.2.2 - z₀.2.1)| := by
    rw [hd₀, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  set R : ℤ := round (z₀.2.2 - z₀.2.1) with hR
  have htIoo : z₀.2.2 - z₀.2.1 - R ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2) := by
    have := abs_lt.mp (hdist₀ ▸ hd₀half)
    exact ⟨by linarith [this.1], this.2⟩
  have hround : ∀ y : ℝ, y ∈ Set.Ioo ((R : ℝ) - 1 / 2) ((R : ℝ) + 1 / 2) → round y = R := by
    intro y hy
    rw [round_eq]
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · linarith [hy.1]
    · linarith [hy.2]
  have hsub : Continuous fun z : ℝ × ℝ × ℝ => z.2.2 - z.2.1 :=
    (continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd)
  have hev1 : ∀ᶠ z : ℝ × ℝ × ℝ in 𝓝 z₀,
      z.2.2 - z.2.1 ∈ Set.Ioo ((R : ℝ) - 1 / 2) ((R : ℝ) + 1 / 2) :=
    hsub.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (by linarith [htIoo.1]) (by linarith [htIoo.2]))
  have ht₀ne : z₀.2.2 - z₀.2.1 - (R : ℝ) ≠ 0 := fun h =>
    hd₀pos.ne' (by rw [hdist₀, h, abs_zero])
  have haff : ContDiff ℝ n fun z : ℝ × ℝ × ℝ => z.2.2 - z.2.1 - (R : ℝ) :=
    ((contDiff_snd.comp contDiff_snd).sub (contDiff_fst.comp contDiff_snd)).sub contDiff_const
  rcases lt_or_gt_of_ne ht₀ne with hneg | hpos
  · -- distance = −(affine) locally
    have hev2 : ∀ᶠ z : ℝ × ℝ × ℝ in 𝓝 z₀, z.2.2 - z.2.1 - R < 0 :=
      (hsub.sub continuous_const).continuousAt.preimage_mem_nhds (Iio_mem_nhds hneg)
    have hsm : ContDiff ℝ n fun z : ℝ × ℝ × ℝ =>
        smoothClampDiv ε (z.1 / 2 - -(z.2.2 - z.2.1 - (R : ℝ))) :=
      (contDiff_smoothClampDiv ε).comp ((contDiff_fst.div_const 2).sub haff.neg)
    refine hsm.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hev1, hev2] with z hz1 hz2
    show smoothArcWeight ε z.1 ((z.2.1 : ℝ) : CircleFibre) ((z.2.2 : ℝ) : CircleFibre)
      = smoothClampDiv ε (z.1 / 2 - -(z.2.2 - z.2.1 - (R : ℝ)))
    rw [smoothArcWeight, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq,
      hround _ hz1, abs_of_neg hz2]
  · -- distance = affine locally
    have hev2 : ∀ᶠ z : ℝ × ℝ × ℝ in 𝓝 z₀, 0 < z.2.2 - z.2.1 - R :=
      (hsub.sub continuous_const).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hpos)
    have hsm : ContDiff ℝ n fun z : ℝ × ℝ × ℝ =>
        smoothClampDiv ε (z.1 / 2 - (z.2.2 - z.2.1 - (R : ℝ))) :=
      (contDiff_smoothClampDiv ε).comp ((contDiff_fst.div_const 2).sub haff)
    refine hsm.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hev1, hev2] with z hz1 hz2
    show smoothArcWeight ε z.1 ((z.2.1 : ℝ) : CircleFibre) ((z.2.2 : ℝ) : CircleFibre)
      = smoothClampDiv ε (z.1 / 2 - (z.2.2 - z.2.1 - (R : ℝ)))
    rw [smoothArcWeight, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq,
      hround _ hz1, abs_of_pos hz2]

/-- **Regular chart positions**: every rate strictly inside `(2ε, 1)`. -/
def RegularPos (ε : ℝ) (x : Fin (N + 1) → ℝ) : Prop :=
  ∀ k, 2 * ε < x (Fin.castSucc k) ∧ x (Fin.castSucc k) < 1

/-- ★ **The chart weight field is `C^∞` at every regular position** — jointly in all the
rates and the register. This is what makes the base derivative `∂_m 𝓗` of the stroke
Hamiltonian meaningful on the joint chart, not only its register derivative. -/
theorem contDiffAt_arcWeights {ε : ℝ} (hε : 0 < ε) {x₀ : Fin (N + 1) → ℝ}
    (hreg : RegularPos ε x₀) {n : ℕ∞} : ContDiffAt ℝ n (arcWeights ε) x₀ := by
  rw [contDiffAt_pi]
  intro k
  have hlin : ContDiff ℝ n fun x : Fin (N + 1) → ℝ =>
      (x (Fin.castSucc k), (cellMidLift (Fin.init x) k, x (Fin.last N))) := by
    refine (contDiff_apply ℝ ℝ _).prodMk (ContDiff.prodMk ?_ (contDiff_apply ℝ ℝ _))
    unfold cellMidLift loSum
    exact (ContDiff.sum fun j _ => contDiff_apply ℝ ℝ (Fin.castSucc j)).add
      ((contDiff_apply ℝ ℝ (Fin.castSucc k)).div_const 2)
  exact (contDiffAt_smoothArcWeight_lift₃ hε (hreg k).1 (hreg k).2).comp x₀ hlin.contDiffAt

/-- **Off-corridor data**: the register sits strictly inside a plateau of every weight — in the
centre plateau (`dist < m/2 − ε`) or the outer plateau (`m/2 < dist`) of each cell. -/
def OffCorridor (ε : ℝ) (d : ConservedData N) : Prop :=
  ∀ k, dist d.2.1 (cellMid d.1 k) < d.1 k / 2 - ε ∨ d.1 k / 2 < dist d.2.1 (cellMid d.1 k)

/-- Off the corridor the chart weight field is locally constant around the chart position. -/
theorem arcWeights_eventuallyEq_const_of_offCorridor {ε : ℝ} (hε : 0 < ε) {d : ConservedData N}
    (hd : OffCorridor ε d) :
    arcWeights ε =ᶠ[𝓝 (chartPos d)] fun _ => arcWeights ε (chartPos d) := by
  have hcoe : Continuous fun s : ℝ => ((s : ℝ) : CircleFibre) :=
    AddCircle.continuous_mk' (p := (1 : ℝ))
  have hgap : ∀ k, Continuous fun x : Fin (N + 1) → ℝ =>
      x (Fin.castSucc k) / 2 - dist ((x (Fin.last N) : ℝ) : CircleFibre) (cellMid (Fin.init x) k) := by
    intro k
    refine ((continuous_apply _).div_const 2).sub ((hcoe.comp (continuous_apply _)).dist ?_)
    rw [show (fun x : Fin (N + 1) → ℝ => cellMid (Fin.init x) k)
      = fun x => ((cellMidLift (Fin.init x) k : ℝ) : CircleFibre) from rfl]
    refine hcoe.comp ?_
    unfold cellMidLift loSum
    exact (continuous_finsetSum _ fun j _ => continuous_apply (Fin.castSucc j)).add
      ((continuous_apply (Fin.castSucc k)).div_const 2)
  have hval : ∀ k, chartPos d (Fin.castSucc k) / 2
      - dist ((chartPos d (Fin.last N) : ℝ) : CircleFibre) (cellMid (Fin.init (chartPos d)) k)
      = d.1 k / 2 - dist d.2.1 (cellMid d.1 k) := by
    intro k
    rw [chartPos_castSucc, chartPos_last, init_chartPos, coe_rep]
  have hk : ∀ k, ∀ᶠ x in 𝓝 (chartPos d), arcWeights ε x k = arcWeights ε (chartPos d) k := by
    intro k
    rcases hd k with h | h
    · filter_upwards [(hgap k).continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds (show ε < chartPos d (Fin.castSucc k) / 2
          - dist ((chartPos d (Fin.last N) : ℝ) : CircleFibre) (cellMid (Fin.init (chartPos d)) k)
          by rw [hval k]; linarith))] with x hx
      simp only [Set.mem_preimage, Set.mem_Ioi] at hx
      unfold arcWeights
      rw [smoothArcWeight_eq_one hε (by linarith), smoothArcWeight_eq_one hε
        (by rw [chartPos_castSucc, chartPos_last, init_chartPos, coe_rep]; linarith)]
    · filter_upwards [(hgap k).continuousAt.preimage_mem_nhds
        (Iio_mem_nhds (show chartPos d (Fin.castSucc k) / 2
          - dist ((chartPos d (Fin.last N) : ℝ) : CircleFibre) (cellMid (Fin.init (chartPos d)) k)
          < 0 by rw [hval k]; linarith))] with x hx
      simp only [Set.mem_preimage, Set.mem_Iio] at hx
      unfold arcWeights
      rw [smoothArcWeight_eq_zero hε (by linarith), smoothArcWeight_eq_zero hε
        (by rw [chartPos_castSucc, chartPos_last, init_chartPos, coe_rep]; linarith)]
  have hall : ∀ᶠ x in 𝓝 (chartPos d), ∀ k, arcWeights ε x k = arcWeights ε (chartPos d) k :=
    Filter.eventually_all.mpr hk
  filter_upwards [hall] with x hx
  exact funext hx

/-- Off the corridor the weight field has zero derivative at the chart position. -/
theorem fderiv_arcWeights_eq_zero_of_offCorridor {ε : ℝ} (hε : 0 < ε) {d : ConservedData N}
    (hd : OffCorridor ε d) : fderiv ℝ (arcWeights ε) (chartPos d) = 0 := by
  rw [(arcWeights_eventuallyEq_const_of_offCorridor hε hd).fderiv_eq]
  exact fderiv_const_apply _

/-! ### The pointer trajectory and the energies along it -/

variable (ε : ℝ)

/-- **The pointer trajectory of conserved data** under the ramped stroke: `q(s) = U(r(s), w) • q`
with `w` the arena weights of the data. -/
noncomputable def strokeTraj (d : ConservedData N) (s : ℝ) : Pointer N :=
  couplingUUAt (pointerRamp s) (dataWeights ε d) • d.2.2

theorem strokeTraj_zero (d : ConservedData N) : strokeTraj ε d 0 = d.2.2 := by
  unfold strokeTraj
  rw [pointerRamp_zero, couplingUUAt_zero, one_smul]

theorem strokeTraj_one (d : ConservedData N) :
    strokeTraj ε d 1 = couplingUU (dataWeights ε d) • d.2.2 := by
  unfold strokeTraj
  rw [pointerRamp_one, couplingUUAt_pi_div_two]

/-- At the end of the stroke the trajectory is the pointer of the fibrewise witness — and
hence of every joint lift (`IsJointLift.pointer_eq`). -/
theorem strokeTraj_one_eq_pointerEvolve (c : ContextField N) (y : PointerArena N N) :
    strokeTraj ε (conservedData c y) 1 = (pointerEvolve c ε y).2 := by
  rw [strokeTraj_one, dataWeights_conservedData]
  rfl

theorem continuous_strokeTraj :
    Continuous fun p : ℝ × ConservedData N => strokeTraj ε p.2 p.1 := by
  have hU : Continuous fun p : ℝ × ConservedData N =>
      couplingUUAt (pointerRamp p.1) (dataWeights ε p.2) := by
    unfold couplingUUAt
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun b d => ?_
    exact (continuous_couplingUAt_entry_joint b d).comp
      ((continuous_pointerRamp.comp continuous_fst).prodMk
        ((continuous_dataWeights ε).comp continuous_snd))
  have hq : Continuous fun p : ℝ × ConservedData N => p.2.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have h := (continuous_unitaryFamily_smul hU).comp (continuous_id.prodMk hq)
  exact h

/-- The stroke energy of outcome `k` along the trajectory, `ṫ(s) · (π/2) · Eₖ(q(s))`: the
`k`-th weight-coefficient of the time-dependent stroke Hamiltonian, evaluated on the moving
pointer. -/
noncomputable def strokeEnergy (d : ConservedData N) (k : Fin N) (s : ℝ) : ℝ :=
  deriv Real.smoothTransition s * (Real.pi / 2 * outcomeEnergy k (strokeTraj ε d s))

theorem continuous_strokeEnergy (k : Fin N) :
    Continuous fun p : ℝ × ConservedData N => strokeEnergy ε p.2 k p.1 :=
  (((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp continuous_fst).mul
    (continuous_const.mul ((continuous_pointerEnergy _).comp (continuous_strokeTraj ε)))

/-- **The stroke-averaged outcome energy** `∫₀¹ ṫ(s) (π/2) Eₖ(q(s)) ds`. -/
noncomputable def avgEnergy (d : ConservedData N) (k : Fin N) : ℝ :=
  ∫ s in (0 : ℝ)..1, strokeEnergy ε d k s

theorem continuous_avgEnergy (k : Fin N) : Continuous fun d : ConservedData N => avgEnergy ε d k :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun d s => strokeEnergy ε d k s)
    ((continuous_strokeEnergy ε k).comp continuous_swap) continuous_const

/-! ### The Hamiltonian shift -/

/-- **The real shift** in chart direction `i`: `−Σₖ (∫₀¹ ṫ (π/2) Eₖ(q(s)) ds) · ∂ᵢWₖ(x₀)` — the
total impulse `−∫₀¹ ∂ₓᵢ𝓗_s ds` the stroke Hamiltonian delivers to the conjugate momentum
`yᵢ`, computed along the pointer trajectory at the frozen chart position `x₀ = chartPos d`. -/
noncomputable def shiftReal (d : ConservedData N) (i : Fin (N + 1)) : ℝ :=
  -(∑ k, avgEnergy ε d k * fderiv ℝ (arcWeights ε) (chartPos d) (Pi.single i 1) k)

/-- **The Hamiltonian shift**: the real shifts of the `N` rate-conjugate angles and of the
register-conjugate `θ₂`, read on the arena torus. This is the `Δ` fed to `jointLift`. -/
noncomputable def hamiltonianShift (d : ConservedData N) : ArenaTorus N :=
  (fun j => ((shiftReal ε d (Fin.castSucc j) : ℝ) : AddCircle (1 : ℝ)),
    ((shiftReal ε d (Fin.last N) : ℝ) : AddCircle (1 : ℝ)))

theorem measurable_shiftReal (i : Fin (N + 1)) :
    Measurable fun d : ConservedData N => shiftReal ε d i := by
  refine (Finset.measurable_sum _ fun k _ => ?_).neg
  exact (continuous_avgEnergy ε k).measurable.mul
    (((measurable_fderiv_apply_const ℝ (arcWeights ε) (Pi.single i 1)).comp
      measurable_chartPos).eval)

/-- **The Hamiltonian shift is measurable** — the hypothesis `jointLift_measurePreserving`
needs. The averaged energies are continuous in the data; the weight derivative is measurable
(`measurable_fderiv_apply_const`) though not continuous. -/
theorem measurable_hamiltonianShift : Measurable (hamiltonianShift (N := N) ε) := by
  have hcoe : Continuous fun s : ℝ => ((s : ℝ) : AddCircle (1 : ℝ)) :=
    AddCircle.continuous_mk' (p := (1 : ℝ))
  exact (measurable_pi_iff.mpr fun j => hcoe.measurable.comp (measurable_shiftReal ε _)).prodMk
    (hcoe.measurable.comp (measurable_shiftReal ε _))

/-- Off the corridor the shift vanishes: the weights are locally constant there. -/
theorem shiftReal_eq_zero_of_offCorridor (hε : 0 < ε) {d : ConservedData N}
    (hd : OffCorridor ε d) (i : Fin (N + 1)) : shiftReal ε d i = 0 := by
  unfold shiftReal
  rw [fderiv_arcWeights_eq_zero_of_offCorridor hε hd]
  simp

theorem hamiltonianShift_eq_zero_of_offCorridor (hε : 0 < ε) {d : ConservedData N}
    (hd : OffCorridor ε d) : hamiltonianShift ε d = 0 := by
  unfold hamiltonianShift
  simp only [shiftReal_eq_zero_of_offCorridor ε hε hd]
  rfl

/-! ### The stroke Hamiltonian on the chart -/

/-- **The time-dependent stroke Hamiltonian on the chart**, for a fixed pointer `q`:
`𝓗_t(x, y) = ṫ(t) · (π/2) · E(W(x), q)` — the ramped coupling energy of the pointer, with the
weights read off the chart positions `x` (the `N` rates and the register; the momenta `y` are
their conjugates). It depends on the positions only, so the positions are frozen along its
flow and the momenta absorb `−∫ ∂ₓ𝓗`. -/
noncomputable def strokeH (t : ℝ) (q : Pointer N) (z : Chart (N + 1)) : ℝ :=
  deriv Real.smoothTransition t * (Real.pi / 2 * pointerEnergy (arcWeights ε z.1) q)

/-- Chain rule: wherever the chart weights are differentiable, so is the stroke Hamiltonian,
with derivative the weight-gradient of the energy pulled back through `W'`. -/
theorem hasFDerivAt_strokeH (t : ℝ) (q : Pointer N) {z : Chart (N + 1)}
    {W' : (Fin (N + 1) → ℝ) →L[ℝ] (Fin N → ℝ)} (hW' : HasFDerivAt (arcWeights ε) W' z.1) :
    HasFDerivAt (strokeH ε t q)
      ((deriv Real.smoothTransition t * (Real.pi / 2)) •
        ((energyGradient q).comp (W'.comp (ContinuousLinearMap.fst ℝ _ _)))) z := by
  have h1 : HasFDerivAt (fun z : Chart (N + 1) => pointerEnergy (arcWeights ε z.1) q)
      ((energyGradient q).comp (W'.comp (ContinuousLinearMap.fst ℝ _ _))) z :=
    (hasFDerivAt_pointerEnergy q _).comp z (hW'.comp z hasFDerivAt_fst)
  have hfun : strokeH ε t q = fun z : Chart (N + 1) =>
      (deriv Real.smoothTransition t * (Real.pi / 2)) * pointerEnergy (arcWeights ε z.1) q := by
    funext w
    unfold strokeH
    ring
  rw [hfun]
  exact h1.const_mul _

/-- `∂ₓᵢ𝓗_t = ṫ (π/2) Σₖ Eₖ(q) ∂ᵢWₖ`. -/
theorem dPos_strokeH (t : ℝ) (q : Pointer N) {z : Chart (N + 1)}
    {W' : (Fin (N + 1) → ℝ) →L[ℝ] (Fin N → ℝ)} (hW' : HasFDerivAt (arcWeights ε) W' z.1)
    (i : Fin (N + 1)) :
    dPos (strokeH ε t q) z i
      = deriv Real.smoothTransition t * (Real.pi / 2)
          * ∑ k, outcomeEnergy k q * W' (Pi.single i 1) k := by
  rw [dPos, (hasFDerivAt_strokeH ε t q hW').fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, posDir,
    ContinuousLinearMap.coe_fst', energyGradient_apply, smul_eq_mul]

/-- `∂ᵧᵢ𝓗_t = 0`: the stroke Hamiltonian is momentum-independent. -/
theorem dMom_strokeH (t : ℝ) (q : Pointer N) {z : Chart (N + 1)}
    {W' : (Fin (N + 1) → ℝ) →L[ℝ] (Fin N → ℝ)} (hW' : HasFDerivAt (arcWeights ε) W' z.1)
    (i : Fin (N + 1)) : dMom (strokeH ε t q) z i = 0 := by
  rw [dMom, (hasFDerivAt_strokeH ε t q hW').fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, momDir,
    ContinuousLinearMap.coe_fst', map_zero, smul_zero]

/-- The Hamiltonian field of the stroke Hamiltonian: positions frozen, momenta driven by
`−∂ₓ𝓗`. -/
theorem hamiltonianField_strokeH (t : ℝ) (q : Pointer N) {z : Chart (N + 1)}
    {W' : (Fin (N + 1) → ℝ) →L[ℝ] (Fin N → ℝ)} (hW' : HasFDerivAt (arcWeights ε) W' z.1) :
    hamiltonianField (strokeH ε t q) z
      = (0, fun i => -(deriv Real.smoothTransition t * (Real.pi / 2)
          * ∑ k, outcomeEnergy k q * W' (Pi.single i 1) k)) := by
  unfold hamiltonianField
  refine Prod.ext (funext fun i => dMom_strokeH ε t q hW' i) (funext fun i => ?_)
  show -(dPos (strokeH ε t q) z i) = _
  rw [dPos_strokeH ε t q hW' i]

/-! ### The generated chart curve -/

/-- **The chart curve the stroke generates** from the frozen data `d`: the positions stay at
the frozen chart position (the Hamiltonian is momentum-independent), and each conjugate
momentum accumulates `−∫₀ᵗ ∂ₓᵢ𝓗_s ds`, with `𝓗_s` evaluated on the actual pointer
trajectory `strokeTraj ε d s`. -/
noncomputable def strokeCurve (d : ConservedData N) (t : ℝ) : Chart (N + 1) :=
  (chartPos d, fun i => -(∑ k, (∫ s in (0 : ℝ)..t, strokeEnergy ε d k s)
    * fderiv ℝ (arcWeights ε) (chartPos d) (Pi.single i 1) k))

theorem strokeCurve_fst (d : ConservedData N) (t : ℝ) : (strokeCurve ε d t).1 = chartPos d := rfl

theorem strokeCurve_zero (d : ConservedData N) : strokeCurve ε d 0 = (chartPos d, 0) := by
  unfold strokeCurve
  refine Prod.ext rfl (funext fun i => ?_)
  simp [intervalIntegral.integral_same]

/-- At the end of the stroke the momenta have moved by exactly the real shift. -/
theorem strokeCurve_one_snd (d : ConservedData N) : (strokeCurve ε d 1).2 = shiftReal ε d := rfl

/-- The Hamiltonian shift **is** the endpoint of the generated curve, read on the torus. -/
theorem hamiltonianShift_eq_strokeCurve_one (d : ConservedData N) :
    hamiltonianShift ε d
      = (fun j => (((strokeCurve ε d 1).2 (Fin.castSucc j) : ℝ) : AddCircle (1 : ℝ)),
          (((strokeCurve ε d 1).2 (Fin.last N) : ℝ) : AddCircle (1 : ℝ))) := rfl

/-- ★★ **Chart-level generation of the Hamiltonian shift.** On regular data — every context
rate strictly inside `(2ε, 1)`, so the chart weights are smooth at the frozen position — the
stroke curve is an integral curve of the time-dependent stroke Hamiltonian, evaluated on the
actual pointer trajectory: `γ̇(t) = X_{𝓗_t(q(t))}(γ(t))` for every `t`. The positions stay
frozen (`∂ᵧ𝓗 = 0`) and the momenta are driven by `−∂ₓ𝓗_t` — the fundamental theorem of
calculus applied to the continuous stroke energies. Together with
`hamiltonianShift_eq_strokeCurve_one`, this is the statement "the shift `jointLift` is fed
is what the stroke Hamiltonian generates in the conjugate directions". -/
theorem strokeCurve_hasDerivAt_hamiltonianField (hε : 0 < ε) {d : ConservedData N}
    (hreg : RegularPos ε (chartPos d)) (t : ℝ) :
    HasDerivAt (strokeCurve ε d)
      (hamiltonianField (strokeH ε t (strokeTraj ε d t)) (strokeCurve ε d t)) t := by
  have hW' : HasFDerivAt (arcWeights ε) (fderiv ℝ (arcWeights ε) (chartPos d)) (chartPos d) :=
    ((contDiffAt_arcWeights hε hreg (n := 1)).differentiableAt (by norm_num)).hasFDerivAt
  rw [hamiltonianField_strokeH ε t _ (z := strokeCurve ε d t) hW']
  unfold strokeCurve
  refine HasDerivAt.prodMk (hasDerivAt_const t _) ?_
  refine hasDerivAt_pi.mpr fun i => ?_
  have hk : ∀ k : Fin N, HasDerivAt
      (fun τ => (∫ s in (0 : ℝ)..τ, strokeEnergy ε d k s)
        * fderiv ℝ (arcWeights ε) (chartPos d) (Pi.single i 1) k)
      (strokeEnergy ε d k t * fderiv ℝ (arcWeights ε) (chartPos d) (Pi.single i 1) k) t := by
    intro k
    have hc : Continuous (strokeEnergy ε d k) :=
      (continuous_strokeEnergy ε k).comp (continuous_id.prodMk continuous_const)
    exact ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt).mul_const _
  have hsum := (HasDerivAt.sum fun k (_ : k ∈ Finset.univ) => hk k).neg
  refine (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)).congr_deriv ?_
  · simp only [Pi.neg_apply, Finset.sum_apply]
  · rw [Finset.mul_sum]
    exact neg_inj.mpr (Finset.sum_congr rfl fun k _ => by unfold strokeEnergy; ring)

/-! ### Headline corollaries: the Hamiltonian shift fed to the joint lift -/

/-- **Off the corridor, the Hamiltonian-shift joint lift is the fibrewise witness.** Where the
register sits strictly inside a plateau of every cell the weights are locally constant, the
generated shift vanishes and the base does not move — exactly as `SigmaLayer/UntriggeredFlow`
predicts for the untriggered region. -/
theorem jointLift_eq_pointerEvolve_off_corridor (c : ContextField N) (hε : 0 < ε)
    {y : PointerArena N N} (hy : OffCorridor ε (conservedData c y)) :
    jointLift c ε (hamiltonianShift ε) y = pointerEvolve c ε y :=
  jointLift_eq_pointerEvolve_of_shift_eq_zero c ε _
    (hamiltonianShift_eq_zero_of_offCorridor ε hε hy)

/-- ★★ **The Hamiltonian-shift joint lift is a joint lift.** For every torus-invariant
context, landing, the `ε`-Born sandwich, the outcome-sector identity and the moment-marginal
law (`JointFlowTransfer.lean`) hold for the map whose base is shifted by what the stroke
Hamiltonian generates. -/
theorem isJointLift_hamiltonianShift {c : ContextField N} (hct : c.TorusInvariant) :
    IsJointLift c ε (jointLift c ε (hamiltonianShift ε)) :=
  isJointLift_jointLift ε (hamiltonianShift ε) hct

/-- ★★ **Liouville's theorem for the Hamiltonian-shift joint lift.** The generated shift is
measurable (`measurable_hamiltonianShift`), so `jointLift_measurePreserving` applies: the
back-reacting map preserves the arena Liouville measure. -/
theorem jointLift_hamiltonianShift_measurePreserving {c : ContextField N}
    (hc : ∀ j, Continuous fun p => c.rate p j) (hct : c.TorusInvariant)
    (p₀ : LF4.CPN N) (q₀ : Pointer N) :
    MeasurePreserving (jointLift c ε (hamiltonianShift ε))
      (pointerLiouville p₀ q₀) (pointerLiouville p₀ q₀) :=
  jointLift_measurePreserving ε hc hct (measurable_hamiltonianShift ε) p₀ q₀

end CSD.RecordLayer

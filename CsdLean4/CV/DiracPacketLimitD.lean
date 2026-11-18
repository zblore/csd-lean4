/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracSpinorD
public import CsdLean4.CV.DiracPacketArcD

/-!
# A normalised packet in its moving box: the bound as a number

**Category:** 3-Local (CV). BACKLOG #296, fifth part (Task 8 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; milestone
M7, obligation UO-17; remainder (b) of the row).

`CV/DiracPacketArcD.lean` bounds a packet's weight outside the box that moves with it by a
starting term and a drift error. `CV/DiracSpinorD.lean` computes the norm and the real part
of the overlap of the mode spinors. Here they are put together: for a normalised packet the
bound is a number, and for a flat packet on a box of momenta it is

  `Σ_i (1/N_i + (2π |J| / (L μ))² + |t| (2π/L) Sm_i) / (1 − γ_i)`.

## Cauchy–Schwarz, norms and overlaps

* `star_dotProduct_self_eq`, `norm_star_dotProduct_le`, `ofReal_mul_inv_sqrt_mul_inv_sqrt`;
* `modeNormSqD`, `alignDefect`, `alignDefect_scaled` (under `J = c L / (2 ℓ)` the defect is
  `(π c / (ℓ μ))²`), `modeNormSqD_ge`, `modeNormSqD_pos`, `two_mul_le_sqrt_modeNormSqD`;
* `spinOverlapD_eq`, `spinOverlapD_self`, ★★ `norm_spinOverlapD_le`,
  ★★★ `re_spinOverlapD_succ_ge` (**neighbouring modes along an axis are aligned up to the
  defect**).

## Normalised amplitudes

* `unitAmpD`, `pairSumD`, `pow_card_pos`, ★★ `chainInnerD_packetD_unitAmpD` (the norm is
  `Σ_m b_m²`), `transWeightD_unitAmpD`, `norm_transWeightD_unitAmpD_le`,
  `re_transWeightD_unitAmpD_ge`;
* `transPhaseD_packetD_zero`, ★★ `re_transPhaseD_unitAmpD_ge`, ★★ `driftErrorD_unitAmpD_le`;
* ★★★ `regionWeightD_unitPacket_compl_movedBoxD_le` (**the bound as a number** for
  amplitudes `b ≥ 0`, `Σ b² = 1`).

## A flat window on a box

* `boxWindowD`, `card_boxWindowD`, `filter_succ_boxWindowD`, `card_filter_succ_boxWindowD`,
  `flatAmpD`, `flatAmpD_nonneg`, `card_boxWindowD_pos`, `sum_flatAmpD_sq`,
  ★★ `pairSumD_flatAmpD` (`= 1 − 1/N_i`);
* ★★★ `regionWeightD_flatPacket_compl_movedBoxD_le` (**a flat packet on a box of momenta stays
  in the box that moves with it**, within the three terms above).

## Honest scope

⚠️ **The energy-step errors `Sm i` are a hypothesis.** `hS` asks that `stepErrD` on the window
is at most `Sm i`. It is not evaluated here in terms of the window's width, so the drift term
is a number only once `Sm` is supplied. Under `J = c L / (2 ℓ)` and a window of fixed width
in physical momentum, `(2π/L) Sm_i` stays bounded; that substitution is not made here.

⚠️ **Small when `N_i` is large, `ℓ μ ≫ π c` and `|t|` is short.** `1/N_i` is the price of a flat
window; the alignment defect `(2π |J| / (L μ))²` does not shrink with `L` under the physical
scaling, only with the size of the torus in Compton wavelengths; the drift term grows with
`|t|`.

⚠️ **The box is centred at the direction `1`**, and the real part of the overlap is used. For
two or more axes the overlap's imaginary part displaces the packet's phase at first order in
the step; a box centred there would hold more. This bound is valid and not sharp.

⚠️ **`μ > 0`, `β e₀ = e₀`, `e₀† e₀ = 1`.** Nothing for a massless carrier. No record is read,
and nothing is on the arena of UA-18.

References: `specs/BACKLOG.md` #296; `specs/unified-record-spacetime-plan.md` (UO-17, UD-209,
UD-210, UD-217, UD-220, UD-221); `CV/DiracSpinorD.lean`
(`re_star_cliffordSpinor_dotProduct_ge`, `star_cliffordSpinor_dotProduct_self`);
`CV/DiracPacketArcD.lean` (`regionWeightD_packetD_compl_movedBoxD_le`, `movedBoxD`);
`CV/DiracPacketD.lean` (`transPhaseD_packetD`, `driftErrorD`, `stepErrD`,
`noWrapD_distinctD_of_box`); `CV/DiracPacketLimit.lean` (`dirac_packet_limit`,
`flat_packet_localised`, `flat_sums`); `specs/future-work.md`.
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
  {L : ℕ} [NeZero L]

/-! ### Cauchy–Schwarz for spinors -/

omit [DecidableEq S] in
theorem star_dotProduct_self_eq (u : S → ℂ) :
    star u ⬝ᵥ u = ((∑ b, ‖u b‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']

omit [DecidableEq S] in
theorem norm_star_dotProduct_le (u v : S → ℂ) :
    ‖star u ⬝ᵥ v‖ ≤ Real.sqrt (∑ b, ‖u b‖ ^ 2) * Real.sqrt (∑ b, ‖v b‖ ^ 2) := by
  have h1 : ‖star u ⬝ᵥ v‖ ≤ ∑ b, ‖u b‖ * ‖v b‖ := by
    rw [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => ‖u b‖) (fun b => ‖v b‖)
  have h0 : 0 ≤ ∑ b, ‖u b‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← Real.sqrt_mul h0]
  exact h1.trans (Real.le_sqrt_of_sq_le h2)

/-- For `x > 0`, `x / √x / √x = 1`, in `ℂ`. -/
theorem ofReal_mul_inv_sqrt_mul_inv_sqrt {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * ((Real.sqrt x : ℝ) : ℂ)⁻¹ * ((Real.sqrt x : ℝ) : ℂ)⁻¹ = 1 := by
  have hs : ((Real.sqrt x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hx).ne'
  have hc : (x : ℂ) = ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx.le]
  rw [hc]
  field_simp

/-! ### The norm and the overlap of the modes of a packet -/

/-- **The squared norm of the spinor of the mode `m`**: `2 E (E + μ)` at its lattice energy. -/
def modeNormSqD (L : ℕ) (J μ : ℝ) (m : ι → ℤ) : ℝ :=
  2 * latticeED J μ (angleZD L m) * (latticeED J μ (angleZD L m) + μ)

/-- **The alignment defect of neighbouring modes**: `(2π |J| / (L μ))²`. Under the scaling
`J = c L / (2 ℓ)` it is `(π c / (ℓ μ))²`, with no `L` in it. -/
def alignDefect (L : ℕ) (J μ : ℝ) : ℝ := (2 * Real.pi * |J| / (L * μ)) ^ 2

omit [NeZero L] in
/-- **Under the scaling `J = c L / (2 ℓ)` the alignment defect is `(π c / (ℓ μ))²`**: it has
no `L` in it. -/
theorem alignDefect_scaled {c ℓ μ : ℝ} (hc : 0 ≤ c) (hℓ : 0 < ℓ) (hL : 0 < L) :
    alignDefect L (c * L / (2 * ℓ)) μ = (Real.pi * c / (ℓ * μ)) ^ 2 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  unfold alignDefect
  rw [abs_of_nonneg (by positivity)]
  congr 1
  field_simp

omit [DecidableEq ι] [NeZero L] in
theorem modeNormSqD_ge {J μ : ℝ} (hμ : 0 < μ) (m : ι → ℤ) :
    4 * μ ^ 2 ≤ modeNormSqD L J μ m := by
  have h : μ ≤ latticeED J μ (angleZD L m) := le_dispE μ _
  unfold modeNormSqD
  nlinarith only [h, hμ]

omit [DecidableEq ι] [NeZero L] in
theorem modeNormSqD_pos {J μ : ℝ} (hμ : 0 < μ) (m : ι → ℤ) : 0 < modeNormSqD L J μ m :=
  lt_of_lt_of_le (by positivity) (modeNormSqD_ge hμ m)

omit [DecidableEq ι] [NeZero L] in
theorem two_mul_le_sqrt_modeNormSqD {J μ : ℝ} (hμ : 0 < μ) (m : ι → ℤ) :
    2 * μ ≤ Real.sqrt (modeNormSqD L J μ m) :=
  Real.le_sqrt_of_sq_le (by nlinarith only [modeNormSqD_ge (L := L) (J := J) hμ m])

variable (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ)

omit [DecidableEq ι] [NeZero L] in
theorem spinOverlapD_eq (J μ : ℝ) (e₀ : S → ℂ) (m' m : ι → ℤ) :
    spinOverlapD (L := L) α β J μ e₀ m' m
      = star (cliffordSpinor α β (modeSD J (castZ L m')) μ e₀)
        ⬝ᵥ cliffordSpinor α β (modeSD J (castZ L m)) μ e₀ := rfl

variable {α β}

theorem spinOverlapD_self (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀)
    (hn : star e₀ ⬝ᵥ e₀ = 1) (J μ : ℝ) (m : ι → ℤ) :
    spinOverlapD (L := L) α β J μ e₀ m m = ((modeNormSqD L J μ m : ℝ) : ℂ) := by
  rw [spinOverlapD_eq, star_cliffordSpinor_dotProduct_self h he hn, dispE_modeSD_castZ,
    modeNormSqD]

/-- ★★ **The modulus of the overlap is at most the product of the norms.** -/
theorem norm_spinOverlapD_le (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀)
    (hn : star e₀ ⬝ᵥ e₀ = 1) (J μ : ℝ) (m' m : ι → ℤ) :
    ‖spinOverlapD (L := L) α β J μ e₀ m' m‖
      ≤ Real.sqrt (modeNormSqD L J μ m') * Real.sqrt (modeNormSqD L J μ m) := by
  have key : ∀ m : ι → ℤ, ∑ b, ‖cliffordSpinor α β (modeSD J (castZ L m)) μ e₀ b‖ ^ 2
      = modeNormSqD L J μ m := fun m => by
    have h1 := star_cliffordSpinor_dotProduct_self h he hn (modeSD J (castZ L m)) μ
    rw [star_dotProduct_self_eq, dispE_modeSD_castZ] at h1
    rw [modeNormSqD]
    exact_mod_cast h1
  rw [spinOverlapD_eq, ← key m', ← key m]
  exact norm_star_dotProduct_le _ _

/-- ★★★ **Neighbouring modes along an axis are aligned up to the defect**: for `μ > 0`,
`Re ⟨u_{m + e_i}, u_m⟩ ≥ ‖u_{m + e_i}‖ ‖u_m‖ (1 − (2π |J| / (L μ))²)`. -/
theorem re_spinOverlapD_succ_ge (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀)
    (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ) (m : ι → ℤ) (i : ι) :
    Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1)) * Real.sqrt (modeNormSqD L J μ m)
        * (1 - alignDefect L J μ)
      ≤ (spinOverlapD (L := L) α β J μ e₀ (m + Pi.single i 1) m).re := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hge := re_star_cliffordSpinor_dotProduct_ge h he hn
    (modeSD J (castZ L (m + Pi.single i 1))) (modeSD J (castZ L m)) (e₀ := e₀) hμ
  rw [dispE_modeSD_castZ, dispE_modeSD_castZ, ← modeNormSqD, ← modeNormSqD,
    ← spinOverlapD_eq] at hge
  -- the momentum terms differ on the axis `i` only, by at most `2 |J| · 2π / L`
  have hdiff : ∀ j, modeSD J (castZ L (m + Pi.single i 1)) j - modeSD J (castZ L m) j
      = if j = i then 2 * J * (Real.sin (angleZD L m i + 2 * Real.pi / L)
          - Real.sin (angleZD L m i)) else 0 := by
    intro j
    rw [modeSD_castZ, modeSD_castZ, angleZD_add_single]
    by_cases hj : j = i
    · subst hj
      simp only [sinS, Function.update_self, ↓reduceIte]
      ring
    · simp only [sinS, Function.update_of_ne hj, sub_self, hj, ↓reduceIte]
  have hsin : |Real.sin (angleZD L m i + 2 * Real.pi / L) - Real.sin (angleZD L m i)|
      ≤ 2 * Real.pi / L := by
    have h1 := Real.lipschitzWith_sin.dist_le_mul (angleZD L m i + 2 * Real.pi / L)
      (angleZD L m i)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, add_sub_cancel_left,
      abs_of_pos (div_pos (mul_pos two_pos Real.pi_pos) hL)] at h1
    exact h1
  have hd : |2 * J * (Real.sin (angleZD L m i + 2 * Real.pi / L) - Real.sin (angleZD L m i))|
      ≤ 2 * |J| * (2 * Real.pi / L) := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hsin (by positivity)
  have hsq : ∑ j, (modeSD J (castZ L (m + Pi.single i 1)) j - modeSD J (castZ L m) j) ^ 2
      = (2 * J * (Real.sin (angleZD L m i + 2 * Real.pi / L)
          - Real.sin (angleZD L m i))) ^ 2 := by
    simp only [hdiff]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  have hE := abs_dispE_sNorm_sub_le hμ (modeSD J (castZ L (m + Pi.single i 1)))
    (modeSD J (castZ L m))
  have habs : ∑ j, |modeSD J (castZ L (m + Pi.single i 1)) j - modeSD J (castZ L m) j|
      = |2 * J * (Real.sin (angleZD L m i + 2 * Real.pi / L)
          - Real.sin (angleZD L m i))| := by
    simp only [hdiff]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  rw [habs, dispE_modeSD_castZ, dispE_modeSD_castZ] at hE
  rw [hsq] at hge
  -- collect
  have hX : 4 * μ ^ 2 ≤ Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1))
      * Real.sqrt (modeNormSqD L J μ m) := by
    have a := two_mul_le_sqrt_modeNormSqD (L := L) (J := J) hμ (m + Pi.single i 1)
    have b := two_mul_le_sqrt_modeNormSqD (L := L) (J := J) hμ m
    nlinarith only [a, b, hμ]
  have hη : alignDefect L J μ = (2 * |J| * (2 * Real.pi / L)) ^ 2 / (4 * μ ^ 2) := by
    unfold alignDefect
    field_simp
    ring
  have hδ0 : 0 ≤ (2 * |J| * (2 * Real.pi / L)) ^ 2 / (4 * μ ^ 2) := by positivity
  have hXη : (2 * |J| * (2 * Real.pi / L)) ^ 2
      ≤ Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1))
        * Real.sqrt (modeNormSqD L J μ m) * alignDefect L J μ := by
    rw [hη]
    have e : (2 * |J| * (2 * Real.pi / L)) ^ 2
        = 4 * μ ^ 2 * ((2 * |J| * (2 * Real.pi / L)) ^ 2 / (4 * μ ^ 2)) := by
      field_simp
    calc (2 * |J| * (2 * Real.pi / L)) ^ 2
        = 4 * μ ^ 2 * ((2 * |J| * (2 * Real.pi / L)) ^ 2 / (4 * μ ^ 2)) := e
      _ ≤ _ := mul_le_mul_of_nonneg_right hX hδ0
  have hd2 : (2 * J * (Real.sin (angleZD L m i + 2 * Real.pi / L)
      - Real.sin (angleZD L m i))) ^ 2 ≤ (2 * |J| * (2 * Real.pi / L)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hE2 : (latticeED J μ (angleZD L (m + Pi.single i 1)) - latticeED J μ (angleZD L m)) ^ 2
      ≤ (2 * |J| * (2 * Real.pi / L)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hE.trans hd) 2
  linarith only [hge, hXη, hd2, hE2]

/-! ### Normalised amplitudes -/

/-- **Normalised real amplitudes**: `b m` divided by the norm `√(L^d) ‖u_m‖` of the mode. -/
def unitAmpD (L : ℕ) (J μ : ℝ) (b : (ι → ℤ) → ℝ) (m : ι → ℤ) : ℂ :=
  ((b m * (Real.sqrt ((L : ℝ) ^ Fintype.card ι))⁻¹
    * (Real.sqrt (modeNormSqD L J μ m))⁻¹ : ℝ) : ℂ)

/-- **The sum of the products of neighbouring amplitudes along the axis `i`.** -/
def pairSumD (W : Finset (ι → ℤ)) (b : (ι → ℤ) → ℝ) (i : ι) : ℝ :=
  ∑ m ∈ W.filter (fun m => m + Pi.single i 1 ∈ W), b (m + Pi.single i 1) * b m

omit [DecidableEq ι] in
theorem pow_card_pos : (0 : ℝ) < (L : ℝ) ^ Fintype.card ι :=
  pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _

/-- ★★ **The norm of a packet with normalised amplitudes is `Σ_m b_m²`.** -/
theorem chainInnerD_packetD_unitAmpD (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ)
    {W : Finset (ι → ℤ)} (hD : DistinctD L W) (b : (ι → ℤ) → ℝ) (t : ℝ) :
    chainInnerD (packetD (L := L) α β J μ e₀ W (unitAmpD L J μ b) t)
        (packetD (L := L) α β J μ e₀ W (unitAmpD L J μ b) t)
      = ((∑ m ∈ W, b m ^ 2 : ℝ) : ℂ) := by
  have hP := ofReal_mul_inv_sqrt_mul_inv_sqrt (pow_card_pos (ι := ι) (L := L))
  push_cast at hP
  rw [chainInnerD_packetD_self α β J μ e₀ hD, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  have hN := ofReal_mul_inv_sqrt_mul_inv_sqrt (modeNormSqD_pos (L := L) (J := J) hμ m)
  rw [spinOverlapD_self h he hn, unitAmpD, Complex.star_def, Complex.conj_ofReal]
  push_cast
  linear_combination ((b m : ℂ) ^ 2 * ((modeNormSqD L J μ m : ℝ) : ℂ)
      * ((Real.sqrt (modeNormSqD L J μ m) : ℝ) : ℂ)⁻¹
      * ((Real.sqrt (modeNormSqD L J μ m) : ℝ) : ℂ)⁻¹) * hP + (b m : ℂ) ^ 2 * hN

/-- The weight of a neighbouring pair for normalised amplitudes. -/
theorem transWeightD_unitAmpD (J μ : ℝ) (e₀ : S → ℂ) (b : (ι → ℤ) → ℝ) (i : ι) (m : ι → ℤ) :
    transWeightD (L := L) α β J μ e₀ (unitAmpD L J μ b) i m
      = ((b (m + Pi.single i 1) * b m
          * ((Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1)))⁻¹
            * (Real.sqrt (modeNormSqD L J μ m))⁻¹) : ℝ) : ℂ)
        * spinOverlapD (L := L) α β J μ e₀ (m + Pi.single i 1) m := by
  have hP := ofReal_mul_inv_sqrt_mul_inv_sqrt (pow_card_pos (ι := ι) (L := L))
  push_cast at hP
  rw [transWeightD, unitAmpD, unitAmpD, Complex.star_def, Complex.conj_ofReal]
  push_cast
  linear_combination ((b (m + Pi.single i 1) : ℂ) * (b m : ℂ)
      * ((Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1)) : ℝ) : ℂ)⁻¹
      * ((Real.sqrt (modeNormSqD L J μ m) : ℝ) : ℂ)⁻¹
      * spinOverlapD (L := L) α β J μ e₀ (m + Pi.single i 1) m) * hP

theorem norm_transWeightD_unitAmpD_le (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ)
    (b : (ι → ℤ) → ℝ) (i : ι) (m : ι → ℤ) :
    ‖transWeightD (L := L) α β J μ e₀ (unitAmpD L J μ b) i m‖
      ≤ |b (m + Pi.single i 1) * b m| := by
  have h1 := Real.sqrt_pos.2 (modeNormSqD_pos (L := L) (J := J) hμ (m + Pi.single i 1))
  have h2 := Real.sqrt_pos.2 (modeNormSqD_pos (L := L) (J := J) hμ m)
  have hO := norm_spinOverlapD_le (L := L) h he hn J μ (m + Pi.single i 1) m
  rw [transWeightD_unitAmpD, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (mul_pos (inv_pos.2 h1) (inv_pos.2 h2))]
  calc |b (m + Pi.single i 1) * b m|
        * ((Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1)))⁻¹
          * (Real.sqrt (modeNormSqD L J μ m))⁻¹)
        * ‖spinOverlapD (L := L) α β J μ e₀ (m + Pi.single i 1) m‖
      ≤ |b (m + Pi.single i 1) * b m|
        * ((Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1)))⁻¹
          * (Real.sqrt (modeNormSqD L J μ m))⁻¹)
        * (Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1))
          * Real.sqrt (modeNormSqD L J μ m)) :=
        mul_le_mul_of_nonneg_left hO (by positivity)
    _ = |b (m + Pi.single i 1) * b m| := by
        field_simp

theorem re_transWeightD_unitAmpD_ge (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ)
    (b : (ι → ℤ) → ℝ) (i : ι) (m : ι → ℤ) (hb : 0 ≤ b (m + Pi.single i 1) * b m) :
    b (m + Pi.single i 1) * b m * (1 - alignDefect L J μ)
      ≤ (transWeightD (L := L) α β J μ e₀ (unitAmpD L J μ b) i m).re := by
  have h1 := Real.sqrt_pos.2 (modeNormSqD_pos (L := L) (J := J) hμ (m + Pi.single i 1))
  have h2 := Real.sqrt_pos.2 (modeNormSqD_pos (L := L) (J := J) hμ m)
  have hO := re_spinOverlapD_succ_ge (L := L) (J := J) h he hn hμ m i (e₀ := e₀)
  rw [transWeightD_unitAmpD, Complex.re_ofReal_mul]
  calc b (m + Pi.single i 1) * b m * (1 - alignDefect L J μ)
      = b (m + Pi.single i 1) * b m
        * ((Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1)))⁻¹
          * (Real.sqrt (modeNormSqD L J μ m))⁻¹)
        * (Real.sqrt (modeNormSqD L J μ (m + Pi.single i 1))
          * Real.sqrt (modeNormSqD L J μ m) * (1 - alignDefect L J μ)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hO (mul_nonneg hb (by positivity))

/-! ### The packet's phase and drift, as numbers -/

variable (α β)

theorem transPhaseD_packetD_zero (J μ : ℝ) (e₀ : S → ℂ) {W : Finset (ι → ℤ)} {i : ι}
    (hW : NoWrapD L W i) (c : (ι → ℤ) → ℂ) :
    transPhaseD i (packetD (L := L) α β J μ e₀ W c 0)
      = ∑ m ∈ W.filter (fun m => m + Pi.single i 1 ∈ W),
          transWeightD (L := L) α β J μ e₀ c i m := by
  rw [transPhaseD_packetD α β J μ e₀ hW c 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

variable {α β}

/-- ★★ **The starting phase of a normalised packet with amplitudes of one sign.** -/
theorem re_transPhaseD_unitAmpD_ge (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ)
    {W : Finset (ι → ℤ)} {i : ι} (hW : NoWrapD L W i) {b : (ι → ℤ) → ℝ}
    (hb : ∀ m, 0 ≤ b m) :
    pairSumD W b i * (1 - alignDefect L J μ)
      ≤ (transPhaseD i (packetD (L := L) α β J μ e₀ W (unitAmpD L J μ b) 0)).re := by
  rw [transPhaseD_packetD_zero α β J μ e₀ hW, Complex.re_sum, pairSumD, Finset.sum_mul]
  exact Finset.sum_le_sum fun m _ =>
    re_transWeightD_unitAmpD_ge h he hn hμ b i m (mul_nonneg (hb _) (hb _))

/-- ★★ **The drift error of a normalised packet**, for a window whose energy steps along `i`
have error at most `Sm`. -/
theorem driftErrorD_unitAmpD_le (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ)
    {W : Finset (ι → ℤ)} {i : ι} {b : (ι → ℤ) → ℝ} (hb : ∀ m, 0 ≤ b m) (k₀ : ι → ℝ)
    {Sm : ℝ} (hS : ∀ m ∈ W, stepErrD J μ (angleZD L m) k₀ i (2 * Real.pi / L) ≤ Sm) :
    driftErrorD (L := L) α β J μ e₀ W (unitAmpD L J μ b) i k₀
      ≤ pairSumD W b i * (2 * Real.pi / L * Sm) := by
  rw [driftErrorD, pairSumD, Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  have hmW : m ∈ W := (Finset.mem_filter.1 hm).1
  have h1 := norm_transWeightD_unitAmpD_le (L := L) (J := J) h he hn hμ b i m (e₀ := e₀)
  rw [abs_of_nonneg (mul_nonneg (hb _) (hb _))] at h1
  have h0 : 0 ≤ stepErrD J μ (angleZD L m) k₀ i (2 * Real.pi / L) := by
    unfold stepErrD
    positivity
  exact mul_le_mul h1 (mul_le_mul_of_nonneg_left (hS m hmW) (by positivity))
    (by positivity) (mul_nonneg (hb _) (hb _))

/-- ★★★ **A normalised packet in the box that moves with it: the bound as a number.** For a
Clifford family, `β e₀ = e₀`, `e₀† e₀ = 1`, `μ > 0`, a window without wrap-around and with
distinct momenta, amplitudes `b ≥ 0` with `Σ b² = 1`, energy-step errors at most `Sm i` on the
window, and `γ i < 1`: at the time `t` the weight outside the box of arcs about the directions
`1` turned at the group velocity is at most the sum over the axes of

  `(1 − P_i (1 − η) + |t| P_i (2π/L) Sm_i) / (1 − γ_i)`,

`P_i` the sum of the products of neighbouring amplitudes along `i` and
`η = (2π |J| / (L μ))²`. -/
theorem regionWeightD_unitPacket_compl_movedBoxD_le (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ)
    {W : Finset (ι → ℤ)} (hW : ∀ i, NoWrapD L W i) (hD : DistinctD L W)
    {b : (ι → ℤ) → ℝ} (hb : ∀ m, 0 ≤ b m) (hb1 : ∑ m ∈ W, b m ^ 2 = 1) (k₀ : ι → ℝ)
    {Sm : ι → ℝ}
    (hS : ∀ i, ∀ m ∈ W, stepErrD J μ (angleZD L m) k₀ i (2 * Real.pi / L) ≤ Sm i) (t : ℝ)
    {γ : ι → ℝ} (hγ : ∀ i, γ i < 1) :
    regionWeightD (packetD (L := L) α β J μ e₀ W (unitAmpD L J μ b) t)
        (movedBoxD L J μ k₀ (fun _ => 1) γ t)ᶜ
      ≤ ∑ i, (1 - pairSumD W b i * (1 - alignDefect L J μ)
              + |t| * (pairSumD W b i * (2 * Real.pi / L * Sm i))) / (1 - γ i) := by
  refine (regionWeightD_packetD_compl_movedBoxD_le (L := L) (J := J) α β hμ e₀ hW hD
    (unitAmpD L J μ b) k₀ t (u := fun _ => 1) (fun _ => norm_one) hγ).trans
    (Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right ?_ (sub_pos.2 (hγ i)).le)
  have h1 := re_transPhaseD_unitAmpD_ge (L := L) (J := J) h he hn hμ (hW i) hb (e₀ := e₀)
  have h2 := mul_le_mul_of_nonneg_left
    (driftErrorD_unitAmpD_le (L := L) (J := J) h he hn hμ hb k₀ (hS i) (e₀ := e₀) (W := W))
    (abs_nonneg t)
  rw [chainInnerD_packetD_unitAmpD h he hn hμ hD, Complex.ofReal_re, hb1, star_one, one_mul]
  linarith only [h1, h2]

/-! ### A flat window on a box -/

/-- **A box of integer momenta**: `N j` consecutive momenta from `lo j` on each axis. -/
def boxWindowD (lo : ι → ℤ) (N : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun j => Finset.Ico (lo j) (lo j + N j)

theorem card_boxWindowD (lo : ι → ℤ) (N : ι → ℕ) : (boxWindowD lo N).card = ∏ j, N j := by
  rw [boxWindowD, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]

/-- The momenta of the box whose neighbour along `i` is in the box are a box one shorter
along `i`. -/
theorem filter_succ_boxWindowD (lo : ι → ℤ) (N : ι → ℕ) (i : ι) :
    (boxWindowD lo N).filter (fun m => m + Pi.single i 1 ∈ boxWindowD lo N)
      = Fintype.piFinset (Function.update (fun j => Finset.Ico (lo j) (lo j + N j)) i
          (Finset.Ico (lo i) (lo i + N i - 1))) := by
  ext m
  simp only [boxWindowD, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = i
    · subst hj
      have a := h1 j
      have c := h2 j
      rw [Function.update_self]
      simp only [Pi.add_apply, Pi.single_eq_same, Finset.mem_Ico] at a c ⊢
      omega
    · rw [Function.update_of_ne hj]
      exact h1 j
  · intro hall
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = i
      · subst hj
        have a := hall j
        rw [Function.update_self] at a
        simp only [Finset.mem_Ico] at a ⊢
        omega
      · have a := hall j
        rwa [Function.update_of_ne hj] at a
    · by_cases hj : j = i
      · subst hj
        have a := hall j
        rw [Function.update_self] at a
        simp only [Pi.add_apply, Pi.single_eq_same, Finset.mem_Ico] at a ⊢
        omega
      · have a := hall j
        rw [Function.update_of_ne hj] at a
        simpa only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero] using a

theorem card_filter_succ_boxWindowD (lo : ι → ℤ) (N : ι → ℕ) (i : ι) :
    ((boxWindowD lo N).filter (fun m => m + Pi.single i 1 ∈ boxWindowD lo N)).card * N i
      = (N i - 1) * (boxWindowD lo N).card := by
  have h1 : (Function.update (fun j => Finset.Ico (lo j) (lo j + N j)) i
      (Finset.Ico (lo i) (lo i + N i - 1)) i).card = N i - 1 := by
    rw [Function.update_self, Int.card_Ico]
    omega
  have h2 : ∏ j ∈ Finset.univ.erase i, (Function.update
      (fun j => Finset.Ico (lo j) (lo j + N j)) i (Finset.Ico (lo i) (lo i + N i - 1)) j).card
      = ∏ j ∈ Finset.univ.erase i, N j :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), Int.card_Ico, add_sub_cancel_left,
        Int.toNat_natCast]
  rw [filter_succ_boxWindowD, Fintype.card_piFinset, card_boxWindowD,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ N (Finset.mem_univ i), h1, h2]
  ring

/-- **Flat amplitudes on a box**: `1/√|W|` everywhere. -/
def flatAmpD (lo : ι → ℤ) (N : ι → ℕ) : (ι → ℤ) → ℝ :=
  fun _ => (Real.sqrt ((boxWindowD lo N).card : ℝ))⁻¹

theorem flatAmpD_nonneg (lo : ι → ℤ) (N : ι → ℕ) (m : ι → ℤ) : 0 ≤ flatAmpD lo N m :=
  inv_nonneg.2 (Real.sqrt_nonneg _)

theorem card_boxWindowD_pos (lo : ι → ℤ) {N : ι → ℕ} (hN : ∀ j, 0 < N j) :
    (0 : ℝ) < (boxWindowD lo N).card := by
  rw [card_boxWindowD]
  exact_mod_cast Finset.prod_pos fun j _ => hN j

theorem sum_flatAmpD_sq (lo : ι → ℤ) {N : ι → ℕ} (hN : ∀ j, 0 < N j) :
    ∑ m ∈ boxWindowD lo N, flatAmpD lo N m ^ 2 = 1 := by
  have hc := card_boxWindowD_pos lo hN
  simp only [flatAmpD, Finset.sum_const, nsmul_eq_mul, inv_pow, Real.sq_sqrt hc.le]
  field_simp

/-- ★★ **On a flat box the neighbouring products along `i` sum to `1 − 1/N_i`.** -/
theorem pairSumD_flatAmpD (lo : ι → ℤ) {N : ι → ℕ} (hN : ∀ j, 0 < N j) (i : ι) :
    pairSumD (boxWindowD lo N) (flatAmpD lo N) i = 1 - 1 / N i := by
  have hc := card_boxWindowD_pos lo hN
  have hNi : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hcard := congrArg (Nat.cast : ℕ → ℝ) (card_filter_succ_boxWindowD lo N i)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (hN i), Nat.cast_one] at hcard
  have hf : (((boxWindowD lo N).filter
      (fun m => m + Pi.single i 1 ∈ boxWindowD lo N)).card : ℝ)
      = ((N i : ℝ) - 1) * (boxWindowD lo N).card / N i := by
    rw [eq_div_iff hNi.ne']
    exact hcard
  simp only [pairSumD, flatAmpD, Finset.sum_const, nsmul_eq_mul]
  rw [hf, ← sq, inv_pow, Real.sq_sqrt hc.le]
  field_simp

/-- ★★★ **A flat packet on a box of momenta stays in the box that moves with it.** For a
Clifford family, `β e₀ = e₀`, `e₀† e₀ = 1`, `μ > 0`, the flat normalised packet on `N j`
consecutive momenta per axis, `0 < N j < L`, energy-step errors at most `Sm i ≥ 0` on the
window, and `γ i < 1`: at the time `t` the weight outside the box of arcs about the
directions `1` turned at the group velocity is at most

  `Σ_i (1/N_i + (2π |J| / (L μ))² + |t| (2π/L) Sm_i) / (1 − γ_i)`. -/
theorem regionWeightD_flatPacket_compl_movedBoxD_le (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ) (lo : ι → ℤ)
    {N : ι → ℕ} (hN : ∀ j, 0 < N j) (hNL : ∀ j, N j < L) (k₀ : ι → ℝ) {Sm : ι → ℝ}
    (hSm : ∀ i, 0 ≤ Sm i)
    (hS : ∀ i, ∀ m ∈ boxWindowD lo N,
      stepErrD J μ (angleZD L m) k₀ i (2 * Real.pi / L) ≤ Sm i) (t : ℝ)
    {γ : ι → ℝ} (hγ : ∀ i, γ i < 1) :
    regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo N)
        (unitAmpD L J μ (flatAmpD lo N)) t) (movedBoxD L J μ k₀ (fun _ => 1) γ t)ᶜ
      ≤ ∑ i, (1 / N i + alignDefect L J μ + |t| * (2 * Real.pi / L * Sm i)) / (1 - γ i) := by
  obtain ⟨hW, hD⟩ := noWrapD_distinctD_of_box (L := L) (W := boxWindowD lo N) (lo := lo)
    (fun m hm j => by
      have a := (Fintype.mem_piFinset.1 hm) j
      have b := hNL j
      simp only [Finset.mem_Ico] at a
      omega)
  refine (regionWeightD_unitPacket_compl_movedBoxD_le (L := L) (J := J) h he hn hμ hW hD
    (flatAmpD_nonneg lo N) (sum_flatAmpD_sq lo hN) k₀ hS t hγ).trans
    (Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right ?_ (sub_pos.2 (hγ i)).le)
  have hNi : (0 : ℝ) < N i := by exact_mod_cast hN i
  have hx0 : 0 ≤ 1 / (N i : ℝ) := by positivity
  have hx1 : 1 / (N i : ℝ) ≤ 1 := by
    rw [div_le_one hNi]
    exact_mod_cast hN i
  have hη : 0 ≤ alignDefect L J μ := sq_nonneg _
  have hd : 0 ≤ |t| * (2 * Real.pi / L * Sm i) := by
    have := hSm i
    positivity
  rw [pairSumD_flatAmpD lo hN]
  nlinarith only [hx0, hx1, hη, hd, mul_nonneg hx0 hη, mul_nonneg hx0 hd]

end CSD.CV

end

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracPacketD

/-!
# The mode spinors of a Clifford family: norm and overlap

**Category:** 3-Local (CV). BACKLOG #296, fourth part (Task 8 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; milestone
M7, obligation UO-17; towards remainder (b), the limit for a window).

`CV/DiracPacketBoxD.lean` bounds a packet's weight outside a box by a starting term and a
drift error, both sums over the window with the spinor overlaps of neighbouring modes as
weights. Nothing was shown small because those overlaps were not known. On the ring
(`CV/DiracPacketLimit.lean`) they are computed for the Pauli matrices. Here they are
computed for any Clifford family, from the relations alone.

* `spinExp` (the expectation `e₀† M e₀` as a linear map), `spinExp_apply`, `spinExp_one`,
  `spinExp_mul_right_fix`, `spinExp_mul_left_fix`, `spinExp_conjTranspose`;
* `cliffordSymbol_add_add`, `cliffordSymbol_isHermitian`,
  ★★ `cliffordSymbol_mul_add_mul` (**`H(s') H(s) + H(s) H(s') = 2 (μ² + s' · s)`**),
  ★ `spinExp_cliffordSymbol` (the symbol's expectation is `μ`);
* `cliffordSpinor`, `star_cliffordSpinor_dotProduct`,
  ★★ `star_cliffordSpinor_dotProduct_self` (**the norm**: `u(s)† u(s) = 2 E (E + μ)`),
  ★★★ `re_star_cliffordSpinor_dotProduct` (**the real part of the overlap**:
  `Re u(s')† u(s) = s' · s + (E' + μ)(E + μ)`),
  ★★★ `re_star_cliffordSpinor_dotProduct_ge` (**neighbouring spinors are nearly aligned**: the
  real part is at least the product of the norms less `((E' − E)² + Σ_i (s'_i − s_i)²) / 2`).

## Honest scope

⚠️ **`β e₀ = e₀` and `e₀† e₀ = 1` are hypotheses.** The spinor `e₀` is a unit vector of positive
rest energy. For other `e₀` the norm can vanish and nothing is claimed.

⚠️ **The real part only.** For two or more axes the overlap of two mode spinors has an
imaginary part of first order in the momentum step (it comes from `α_i α_j`, `i ≠ j`). It is
not computed. It turns the translation phase of a packet, so the box that holds the packet
best is displaced from the one centred where the real part alone would put it. The bounds
that use the real part stay valid; they are not sharp.

⚠️ **Not yet a packet.** The modulus of the overlap (needed for the drift error), the
normalised amplitudes, the sums over a flat window and the bound of
`regionWeightD_packetD_compl_movedBoxD_le` as a number are not here. Nothing is shown small
for a packet by this module.

References: `specs/BACKLOG.md` #296; `specs/unified-record-spacetime-plan.md` (UO-17, UD-206,
UD-209, UD-210, UD-217, UD-220); `CV/DiracLatticeD.lean` (`IsCliffordFamily`,
`cliffordSymbol`, `cliffordSymbol_mul_self`, `mul_cliffordSymbol_add`);
`CV/DiracPacketD.lean` (`modeSpinD`, `spinOverlapD`); `CV/DiracPacketLimit.lean`
(`spinNorm`, `spin_align`, `one_sub_le_spinCos`); `specs/future-work.md`.
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
  {α : ι → Matrix S S ℂ} {β : Matrix S S ℂ}

/-! ### The expectation in a spinor -/

/-- **The expectation of a matrix in the spinor `e₀`**, `e₀† M e₀`, as a linear map. -/
def spinExp (e₀ : S → ℂ) : Matrix S S ℂ →ₗ[ℂ] ℂ where
  toFun M := star e₀ ⬝ᵥ M *ᵥ e₀
  map_add' M N := by rw [Matrix.add_mulVec, dotProduct_add]
  map_smul' c M := by rw [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply]

omit [DecidableEq S] in
theorem spinExp_apply (e₀ : S → ℂ) (M : Matrix S S ℂ) :
    spinExp e₀ M = star e₀ ⬝ᵥ M *ᵥ e₀ := rfl

theorem spinExp_one (e₀ : S → ℂ) : spinExp e₀ 1 = star e₀ ⬝ᵥ e₀ := by
  rw [spinExp_apply, Matrix.one_mulVec]

omit [DecidableEq S] in
theorem spinExp_mul_right_fix {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (M : Matrix S S ℂ) :
    spinExp e₀ (M * β) = spinExp e₀ M := by
  rw [spinExp_apply, spinExp_apply, ← Matrix.mulVec_mulVec, he]

omit [DecidableEq S] in
theorem spinExp_mul_left_fix (hβ : β.IsHermitian) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀)
    (M : Matrix S S ℂ) : spinExp e₀ (β * M) = spinExp e₀ M := by
  have h1 : star e₀ ᵥ* β = star e₀ := by
    have := congrArg star he
    rwa [Matrix.star_mulVec, hβ.eq] at this
  rw [spinExp_apply, spinExp_apply, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1]

omit [DecidableEq S] in
theorem spinExp_conjTranspose (e₀ : S → ℂ) (M : Matrix S S ℂ) :
    spinExp e₀ Mᴴ = star (spinExp e₀ M) := by
  rw [spinExp_apply, spinExp_apply, ← star_dotProduct, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec]

/-! ### The symbol -/

omit [DecidableEq ι] [Fintype S] [DecidableEq S] in
theorem cliffordSymbol_add_add (s s' : ι → ℝ) (μ μ' : ℝ) :
    cliffordSymbol α β (s + s') (μ + μ')
      = cliffordSymbol α β s μ + cliffordSymbol α β s' μ' := by
  unfold cliffordSymbol
  simp only [Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  abel

omit [DecidableEq ι] in
theorem cliffordSymbol_isHermitian (h : IsCliffordFamily α β) (s : ι → ℝ) (μ : ℝ) :
    (cliffordSymbol α β s μ).IsHermitian := by
  unfold cliffordSymbol
  rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    (h.isHermitian_α _).eq, h.isHermitian_β.eq]

/-- ★★ **The symmetrised product of two symbols is a scalar**:
`H(s') H(s) + H(s) H(s') = 2 (μ² + s' · s)`. -/
theorem cliffordSymbol_mul_add_mul (h : IsCliffordFamily α β) (s s' : ι → ℝ) (μ : ℝ) :
    cliffordSymbol α β s' μ * cliffordSymbol α β s μ
        + cliffordSymbol α β s μ * cliffordSymbol α β s' μ
      = ((2 * (μ ^ 2 + ∑ i, s' i * s i) : ℝ) : ℂ) • (1 : Matrix S S ℂ) := by
  have hsum : ∑ i, (s + s') i ^ 2
      = ∑ i, s i ^ 2 + 2 * ∑ i, s' i * s i + ∑ i, s' i ^ 2 := by
    simp only [Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hr : ((μ + μ) ^ 2 + ∑ i, (s + s') i ^ 2) - (μ ^ 2 + ∑ i, s i ^ 2)
      - (μ ^ 2 + ∑ i, s' i ^ 2) = 2 * (μ ^ 2 + ∑ i, s' i * s i) := by
    rw [hsum]
    ring
  have h1 := cliffordSymbol_mul_self h (s + s') (μ + μ)
  rw [cliffordSymbol_add_add, add_mul, mul_add, mul_add, cliffordSymbol_mul_self h s μ,
    cliffordSymbol_mul_self h s' μ] at h1
  have h2 : cliffordSymbol α β s' μ * cliffordSymbol α β s μ
        + cliffordSymbol α β s μ * cliffordSymbol α β s' μ
      = (((μ + μ) ^ 2 + ∑ i, (s + s') i ^ 2 : ℝ) : ℂ) • (1 : Matrix S S ℂ)
        - ((μ ^ 2 + ∑ i, s i ^ 2 : ℝ) : ℂ) • (1 : Matrix S S ℂ)
        - ((μ ^ 2 + ∑ i, s' i ^ 2 : ℝ) : ℂ) • (1 : Matrix S S ℂ) := by
    rw [← h1]
    abel
  rw [h2, ← sub_smul, ← sub_smul, ← Complex.ofReal_sub, ← Complex.ofReal_sub, hr]

omit [DecidableEq ι] in
/-- ★ **The expectation of the symbol in a spinor of positive rest energy is `μ`**, for
`β e₀ = e₀` and `e₀† e₀ = 1`. -/
theorem spinExp_cliffordSymbol (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀)
    (hn : star e₀ ⬝ᵥ e₀ = 1) (s : ι → ℝ) (μ : ℝ) :
    spinExp e₀ (cliffordSymbol α β s μ) = (μ : ℂ) := by
  have h1 := congrArg (spinExp e₀) (mul_cliffordSymbol_add h s μ)
  rw [map_add, spinExp_mul_left_fix h.isHermitian_β he, spinExp_mul_right_fix he, map_smul,
    spinExp_one, hn, smul_eq_mul, mul_one] at h1
  push_cast at h1
  linear_combination h1 / 2

/-! ### The mode's spinor -/

variable (α β)

/-- **The spinor of the upper band at the momentum terms `s`**: `(H(s) + E) e₀`. -/
def cliffordSpinor (s : ι → ℝ) (μ : ℝ) (e₀ : S → ℂ) : S → ℂ :=
  (cliffordSymbol α β s μ + (dispE μ (sNorm s) : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀

variable {α β}

omit [DecidableEq ι] in
/-- The overlap of two mode spinors through the expectation of the product of their symbols. -/
theorem star_cliffordSpinor_dotProduct (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) (s' s : ι → ℝ) (μ : ℝ) :
    star (cliffordSpinor α β s' μ e₀) ⬝ᵥ cliffordSpinor α β s μ e₀
      = spinExp e₀ (cliffordSymbol α β s' μ * cliffordSymbol α β s μ)
        + (μ : ℂ) * ((dispE μ (sNorm s) : ℂ) + (dispE μ (sNorm s') : ℂ))
        + (dispE μ (sNorm s') : ℂ) * (dispE μ (sNorm s) : ℂ) := by
  have hH' : (cliffordSymbol α β s' μ + (dispE μ (sNorm s') : ℂ) • (1 : Matrix S S ℂ))ᴴ
      = cliffordSymbol α β s' μ + (dispE μ (sNorm s') : ℂ) • (1 : Matrix S S ℂ) := by
    rw [Matrix.conjTranspose_add, (cliffordSymbol_isHermitian h s' μ).eq,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hexp : (cliffordSymbol α β s' μ + (dispE μ (sNorm s') : ℂ) • (1 : Matrix S S ℂ))
        * (cliffordSymbol α β s μ + (dispE μ (sNorm s) : ℂ) • (1 : Matrix S S ℂ))
      = cliffordSymbol α β s' μ * cliffordSymbol α β s μ
        + (dispE μ (sNorm s) : ℂ) • cliffordSymbol α β s' μ
        + ((dispE μ (sNorm s') : ℂ) • cliffordSymbol α β s μ
          + ((dispE μ (sNorm s) : ℂ) * (dispE μ (sNorm s') : ℂ)) • (1 : Matrix S S ℂ)) := by
    rw [add_mul, mul_add, mul_add]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, smul_smul]
  unfold cliffordSpinor
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH', hexp,
    ← spinExp_apply]
  simp only [map_add, map_smul, smul_eq_mul, spinExp_cliffordSymbol h he hn, spinExp_one, hn]
  ring

/-- ★★ **The norm of a mode's spinor**: `u(s)† u(s) = 2 E (E + μ)`, `E = √(μ² + |s|²)`. -/
theorem star_cliffordSpinor_dotProduct_self (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) (s : ι → ℝ) (μ : ℝ) :
    star (cliffordSpinor α β s μ e₀) ⬝ᵥ cliffordSpinor α β s μ e₀
      = ((2 * dispE μ (sNorm s) * (dispE μ (sNorm s) + μ) : ℝ) : ℂ) := by
  have hE : ((μ ^ 2 + ∑ i, s i ^ 2 : ℝ) : ℂ)
      = (dispE μ (sNorm s) : ℂ) * (dispE μ (sNorm s) : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, dispE_sNorm_sq]
  rw [star_cliffordSpinor_dotProduct h he hn, cliffordSymbol_mul_self h, map_smul, spinExp_one,
    hn, smul_eq_mul, mul_one, hE]
  push_cast
  ring

/-- ★★★ **The real part of the overlap of two mode spinors**:
`Re u(s')† u(s) = s' · s + (E' + μ)(E + μ)`. It is the dot product of the real vectors
`(E' + μ, s')` and `(E + μ, s)`, whose squared lengths are the two norms. -/
theorem re_star_cliffordSpinor_dotProduct (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) (s' s : ι → ℝ) (μ : ℝ) :
    (star (cliffordSpinor α β s' μ e₀) ⬝ᵥ cliffordSpinor α β s μ e₀).re
      = ∑ i, s' i * s i + (dispE μ (sNorm s') + μ) * (dispE μ (sNorm s) + μ) := by
  have hc : spinExp e₀ (cliffordSymbol α β s μ * cliffordSymbol α β s' μ)
      = (starRingEnd ℂ) (spinExp e₀ (cliffordSymbol α β s' μ * cliffordSymbol α β s μ)) := by
    rw [← Complex.star_def, ← spinExp_conjTranspose, Matrix.conjTranspose_mul,
      (cliffordSymbol_isHermitian h s μ).eq, (cliffordSymbol_isHermitian h s' μ).eq]
  have h1 := congrArg (spinExp e₀) (cliffordSymbol_mul_add_mul h s s' μ)
  rw [map_add, hc, map_smul, spinExp_one, hn, smul_eq_mul, mul_one] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.add_re, Complex.conj_re, Complex.ofReal_re] at h2
  rw [star_cliffordSpinor_dotProduct h he hn]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.add_im, add_zero]
  linarith only [h2]

/-- ★★★ **Neighbouring mode spinors are nearly aligned.** For `μ > 0` the real part of the
overlap is at least the product of the two norms less half of
`(E' − E)² + Σ_i (s'_i − s_i)²`. -/
theorem re_star_cliffordSpinor_dotProduct_ge (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) (s' s : ι → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    Real.sqrt (2 * dispE μ (sNorm s') * (dispE μ (sNorm s') + μ))
          * Real.sqrt (2 * dispE μ (sNorm s) * (dispE μ (sNorm s) + μ))
        - ((dispE μ (sNorm s') - dispE μ (sNorm s)) ^ 2 + ∑ i, (s' i - s i) ^ 2) / 2
      ≤ (star (cliffordSpinor α β s' μ e₀) ⬝ᵥ cliffordSpinor α β s μ e₀).re := by
  have hE := dispE_pos hμ (sNorm s)
  have hE' := dispE_pos hμ (sNorm s')
  have e1 := dispE_sNorm_sq μ s
  have e2 := dispE_sNorm_sq μ s'
  have hN : 0 ≤ 2 * dispE μ (sNorm s) * (dispE μ (sNorm s) + μ) := by positivity
  have hN' : 0 ≤ 2 * dispE μ (sNorm s') * (dispE μ (sNorm s') + μ) := by positivity
  have hsum : ∑ i, (s' i - s i) ^ 2 = ∑ i, s' i ^ 2 - 2 * ∑ i, s' i * s i + ∑ i, s i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [re_star_cliffordSpinor_dotProduct h he hn, hsum]
  nlinarith only [sq_nonneg (Real.sqrt (2 * dispE μ (sNorm s') * (dispE μ (sNorm s') + μ))
      - Real.sqrt (2 * dispE μ (sNorm s) * (dispE μ (sNorm s) + μ))),
    Real.sq_sqrt hN, Real.sq_sqrt hN', e1, e2]

end CSD.CV

end

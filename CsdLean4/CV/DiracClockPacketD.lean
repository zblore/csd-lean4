/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracPacketLimitD
public import CsdLean4.CV.DiracDevice

/-!
# The two-level clock on a packet, on the lattice in `d` dimensions

**Category:** 3-Local (CV). BACKLOG #296, seventh part (Task 8 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; milestone
M7, obligation UO-17; plan `specs/unified-records-spacetime-task-plans.md` §6).

`CV/DiracDevice.lean` carries a clock on a packet of the ring: two internal levels of
different rest energy, whose coherence turns at the difference of the two bands' energies.
This module does the same on the torus of any number of axes, for any Clifford family.

## The coherence

* `levelSpinOverlapD`, `levelCoherenceD`, `levelWeightD`;
* ★★ `levelCoherenceD_eq` — the coherence between two levels of one window is a sum over the
  window of phases turning at `E⁰(m) − E¹(m)`;
* `levelErrorD`, ★★★ `levelCoherenceD_rate` — **the coherence turns at the level splitting
  at the centre `k₀` of the window**, within `|t|` times the window's spread of splittings.

## The spinors of the two levels

* `star_symbol_add_mulVec_dotProduct`;
* ★★ `star_cliffordSpinor_dotProduct_levels` — at one momentum the spinors of the two levels
  overlap by `(E⁰ + μ₀)(E⁰ + E¹ + μ₁ − μ₀)`, a real number;
* ★ `levelSpinOverlapD_eq`, `levelSpinOverlapD_pos` — it is positive for positive rest
  energies, so no momentum of the window drops out of the clock.

## The device

* `deviceHamD`, `devicePacketD`, `deviceHamD_mulVec_apply`;
* ★★ `hasDerivAt_devicePacketD` — the two-level packet solves `i Ψ' = H_dev Ψ`;
* `deviceCoherenceD`, ★ `deviceCoherenceD_devicePacketD` — its coherence is `levelCoherenceD`.

## Honest scope

⚠️ **The error is the window's spread of splittings, as it stands.** `levelErrorD` is
`Σ_m |w_m| · |(E⁰(m) − E¹(m)) − (E⁰(k₀) − E¹(k₀))|`. It is not bounded here by the window's
width, and no limit of lattices is taken.

⚠️ **The rate is in flow time.** That the splitting at `k₀` is the rest splitting divided by
the Lorentz factor of the packet's group velocity (the time dilation of
`CV/DiracDevice.lean` on the ring) is not shown for `d` dimensions.

⚠️ **`μ₀, μ₁ > 0`** for the positivity of the overlap. `μ = 0` is not treated.

⚠️ **No pointer reads this clock.** The device is a vector solving Schrödinger's equation.

References: `specs/BACKLOG.md` #296; `specs/unified-record-spacetime-plan.md` (UO-17, UD-207,
UD-220, UD-221, UD-235); `specs/unified-records-spacetime-task-plans.md` (§6);
`CV/DiracDevice.lean` (`levelCoherence_eq`, `levelCoherence_rate`, `levelMass`, `deviceHam`);
`CV/DiracPacketD.lean` (`packetD`, `chainInnerD_packetD_self`, `hasDerivAt_packetD`);
`CV/DiracSpinorD.lean` (`cliffordSpinor`, `spinExp_cliffordSymbol`); `CV/DiracPacket.lean`
(`norm_sum_phase_sub_le`); `specs/future-work.md`.
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
  {L : ℕ} [NeZero L]

/-! ### The coherence between two levels -/

variable (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ)

/-- **The overlap of the two levels' spinors at the momentum `m`.** -/
def levelSpinOverlapD (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ) (m : ι → ℤ) : ℂ :=
  ∑ b, star (modeSpinD α β J μ₀ (castZ L m) e₀ b) * modeSpinD α β J μ₁ (castZ L m) e₀ b

/-- **The coherence between two levels**: level `0` at rest energy `μ₀` with amplitudes `a₀`,
level `1` at `μ₁` with `a₁`, on one window of momenta. -/
def levelCoherenceD (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ) (W : Finset (ι → ℤ)) (a₀ a₁ : (ι → ℤ) → ℂ)
    (t : ℝ) : ℂ :=
  chainInnerD (packetD (L := L) α β J μ₀ e₀ W a₀ t) (packetD (L := L) α β J μ₁ e₀ W a₁ t)

/-- The weight of the momentum `m` in the coherence. -/
def levelWeightD (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ) (a₀ a₁ : (ι → ℤ) → ℂ) (m : ι → ℤ) : ℂ :=
  (L : ℂ) ^ Fintype.card ι * star (a₀ m) * a₁ m * levelSpinOverlapD (L := L) α β J μ₀ μ₁ e₀ m

/-- ★★ **The coherence, exactly**: each momentum's phase turns at `E⁰(m) − E¹(m)`. -/
theorem levelCoherenceD_eq (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ) {W : Finset (ι → ℤ)}
    (hD : DistinctD L W) (a₀ a₁ : (ι → ℤ) → ℂ) (t : ℝ) :
    levelCoherenceD (L := L) α β J μ₀ μ₁ e₀ W a₀ a₁ t
      = ∑ m ∈ W, levelWeightD (L := L) α β J μ₀ μ₁ e₀ a₀ a₁ m
          * exp (I * (((latticeED J μ₀ (angleZD L m) - latticeED J μ₁ (angleZD L m) : ℝ) : ℂ)
            * t)) := by
  unfold levelCoherenceD packetD
  rw [chainInnerD_sum_left]
  simp only [chainInnerD_sum_right, diracModeD_eq, chainInnerD_spinorWave]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  have hin : ∑ m ∈ W, (a₁ m * exp (-(I * latticeED J μ₁ (angleZD L m)) * t))
        * ((if castZ L m' = castZ L m then (L : ℂ) ^ Fintype.card ι else 0)
          * ∑ b, star (modeSpinD α β J μ₀ (castZ L m') e₀ b)
              * modeSpinD α β J μ₁ (castZ L m) e₀ b)
      = (a₁ m' * exp (-(I * latticeED J μ₁ (angleZD L m')) * t))
        * ((L : ℂ) ^ Fintype.card ι * levelSpinOverlapD (L := L) α β J μ₀ μ₁ e₀ m') := by
    rw [Finset.sum_eq_single m']
    · simp only [↓reduceIte, levelSpinOverlapD]
    · intro m hm hne
      rw [ite_eq_right (fun h => hne ((hD m' hm' m hm).1 h.symm)), zero_mul, mul_zero]
    · intro h
      exact absurd hm' h
  have hexp : exp (I * (latticeED J μ₀ (angleZD L m') * t))
      * exp (-(I * latticeED J μ₁ (angleZD L m')) * t)
      = exp (I * (((latticeED J μ₀ (angleZD L m') - latticeED J μ₁ (angleZD L m') : ℝ) : ℂ)
        * t)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hin, star_mul', star_exp_neg_I_mul, levelWeightD, ← hexp]
  ring

/-- The coherence error: the window's spread of level splittings about the centre `k₀`. -/
def levelErrorD (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ) (W : Finset (ι → ℤ)) (a₀ a₁ : (ι → ℤ) → ℂ)
    (k₀ : ι → ℝ) : ℝ :=
  ∑ m ∈ W, ‖levelWeightD (L := L) α β J μ₀ μ₁ e₀ a₀ a₁ m‖
    * |latticeED J μ₀ (angleZD L m) - latticeED J μ₁ (angleZD L m)
        - (latticeED J μ₀ k₀ - latticeED J μ₁ k₀)|

/-- ★★★ **The coherence turns at the level splitting at the centre of the window**, within
`|t|` times the window's spread of splittings. -/
theorem levelCoherenceD_rate (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ) {W : Finset (ι → ℤ)}
    (hD : DistinctD L W) (a₀ a₁ : (ι → ℤ) → ℂ) (k₀ : ι → ℝ) (t : ℝ) :
    ‖levelCoherenceD (L := L) α β J μ₀ μ₁ e₀ W a₀ a₁ t
        - exp (I * (((latticeED J μ₀ k₀ - latticeED J μ₁ k₀ : ℝ) : ℂ) * t))
          * levelCoherenceD (L := L) α β J μ₀ μ₁ e₀ W a₀ a₁ 0‖
      ≤ |t| * levelErrorD (L := L) α β J μ₀ μ₁ e₀ W a₀ a₁ k₀ := by
  rw [levelCoherenceD_eq α β J μ₀ μ₁ e₀ hD a₀ a₁ t, levelCoherenceD_eq α β J μ₀ μ₁ e₀ hD a₀ a₁ 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  exact norm_sum_phase_sub_le _ _ _ _ t

variable {α β}

/-! ### The spinors of the two levels -/

/-- The overlap of two vectors `(H(s) + a) e₀` and `(H(s) + b) e₀` of one symbol. -/
theorem star_symbol_add_mulVec_dotProduct (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) (s : ι → ℝ) (μ a b : ℝ) :
    star ((cliffordSymbol α β s μ + (a : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀)
        ⬝ᵥ ((cliffordSymbol α β s μ + (b : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀)
      = ((μ ^ 2 + ∑ i, s i ^ 2 + (a + b) * μ + a * b : ℝ) : ℂ) := by
  have hH' : (cliffordSymbol α β s μ + (a : ℂ) • (1 : Matrix S S ℂ))ᴴ
      = cliffordSymbol α β s μ + (a : ℂ) • (1 : Matrix S S ℂ) := by
    rw [Matrix.conjTranspose_add, (cliffordSymbol_isHermitian h s μ).eq,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hexp : (cliffordSymbol α β s μ + (a : ℂ) • (1 : Matrix S S ℂ))
        * (cliffordSymbol α β s μ + (b : ℂ) • (1 : Matrix S S ℂ))
      = cliffordSymbol α β s μ * cliffordSymbol α β s μ
        + (b : ℂ) • cliffordSymbol α β s μ
        + ((a : ℂ) • cliffordSymbol α β s μ + ((b : ℂ) * (a : ℂ)) • (1 : Matrix S S ℂ)) := by
    rw [add_mul, mul_add, mul_add]
    simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, smul_smul]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH', hexp,
    ← spinExp_apply, cliffordSymbol_mul_self h]
  simp only [map_add, map_smul, smul_eq_mul, spinExp_cliffordSymbol h he hn, spinExp_one, hn]
  push_cast
  ring

/-- ★★ **The spinors of two levels at one momentum**:
`u(s, μ₀)† u(s, μ₁) = (E⁰ + μ₀)(E⁰ + E¹ + μ₁ − μ₀)`, a real number. -/
theorem star_cliffordSpinor_dotProduct_levels (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) (s : ι → ℝ) (μ₀ μ₁ : ℝ) :
    star (cliffordSpinor α β s μ₀ e₀) ⬝ᵥ cliffordSpinor α β s μ₁ e₀
      = (((dispE μ₀ (sNorm s) + μ₀)
          * (dispE μ₀ (sNorm s) + dispE μ₁ (sNorm s) + μ₁ - μ₀) : ℝ) : ℂ) := by
  have h1 : cliffordSpinor α β s μ₁ e₀
      = (cliffordSymbol α β s μ₀
          + ((dispE μ₁ (sNorm s) + μ₁ - μ₀ : ℝ) : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀ := by
    unfold cliffordSpinor cliffordSymbol
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, he, Matrix.one_mulVec]
    push_cast
    module
  rw [h1]
  unfold cliffordSpinor
  rw [star_symbol_add_mulVec_dotProduct h he hn, ← dispE_sNorm_sq μ₀ s]
  congr 1
  ring

omit [NeZero L] in
/-- ★ **The overlap of the two levels' spinors at a momentum of the window.** -/
theorem levelSpinOverlapD_eq (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀)
    (hn : star e₀ ⬝ᵥ e₀ = 1) (J μ₀ μ₁ : ℝ) (m : ι → ℤ) :
    levelSpinOverlapD (L := L) α β J μ₀ μ₁ e₀ m
      = (((dispE μ₀ (sNorm (modeSD J (castZ L m))) + μ₀)
          * (dispE μ₀ (sNorm (modeSD J (castZ L m)))
            + dispE μ₁ (sNorm (modeSD J (castZ L m))) + μ₁ - μ₀) : ℝ) : ℂ) :=
  star_cliffordSpinor_dotProduct_levels h he hn (modeSD J (castZ L m)) μ₀ μ₁

omit [NeZero L] in
/-- For positive rest energies the two levels' spinors overlap by a positive number. -/
theorem levelSpinOverlapD_pos (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀)
    (hn : star e₀ ⬝ᵥ e₀ = 1) (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) (m : ι → ℤ) :
    0 < (levelSpinOverlapD (L := L) α β J μ₀ μ₁ e₀ m).re := by
  rw [levelSpinOverlapD_eq h he hn, Complex.ofReal_re]
  have a0 := le_dispE μ₀ (sNorm (modeSD J (castZ L m)))
  have a1 := dispE_pos h1 (sNorm (modeSD J (castZ L m)))
  have a2 := dispE_pos h0 (sNorm (modeSD J (castZ L m)))
  exact mul_pos (by linarith) (by linarith)

/-! ### The device -/

variable (α β)

/-- ★ **The device's Hamiltonian on the torus**: the lattice Dirac Hamiltonian at rest energy
`μ₀` on internal level `0` and at `μ₁` on level `1`, one block per level. -/
def deviceHamD (J μ₀ μ₁ : ℝ) :
    Matrix (((ι → ZMod L) × S) × Fin 2) (((ι → ZMod L) × S) × Fin 2) ℂ :=
  Matrix.blockDiagonal fun i => latticeDiracHam α β J (levelMass μ₀ μ₁ i)

/-- ★★ **The device on the torus**: one window of momenta carrying both internal levels,
level `i` with the amplitudes `a i`. -/
def devicePacketD (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ) (W : Finset (ι → ℤ))
    (a : Fin 2 → (ι → ℤ) → ℂ) (t : ℝ) : ((ι → ZMod L) × S) × Fin 2 → ℂ := fun x =>
  packetD (L := L) α β J (levelMass μ₀ μ₁ x.2) e₀ W (a x.2) t x.1

omit [DecidableEq S] in
theorem deviceHamD_mulVec_apply (J μ₀ μ₁ : ℝ) (Ψ : ((ι → ZMod L) × S) × Fin 2 → ℂ)
    (p : (ι → ZMod L) × S) (i : Fin 2) :
    (deviceHamD α β J μ₀ μ₁ *ᵥ Ψ) (p, i)
      = (latticeDiracHam α β J (levelMass μ₀ μ₁ i) *ᵥ fun q => Ψ (q, i)) p := by
  simp only [Matrix.mulVec, dotProduct, deviceHamD, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

variable {α β}

/-- ★★ **The device is one quantum system**: it solves `i Ψ' = H_dev Ψ`. -/
theorem hasDerivAt_devicePacketD (h : IsCliffordFamily α β) (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ)
    (W : Finset (ι → ℤ)) (a : Fin 2 → (ι → ℤ) → ℂ) (t : ℝ) :
    HasDerivAt (devicePacketD (L := L) α β J μ₀ μ₁ e₀ W a)
      ((-I) • (deviceHamD α β J μ₀ μ₁ *ᵥ devicePacketD (L := L) α β J μ₀ μ₁ e₀ W a t)) t := by
  rw [hasDerivAt_pi]
  rintro ⟨p, i⟩
  have hp := hasDerivAt_pi.1
    (hasDerivAt_packetD (L := L) h J (levelMass μ₀ μ₁ i) e₀ W (a i) t) p
  refine HasDerivAt.congr_deriv
    (f := fun x => devicePacketD (L := L) α β J μ₀ μ₁ e₀ W a x (p, i)) hp ?_
  change _ = -I • (deviceHamD α β J μ₀ μ₁ *ᵥ devicePacketD (L := L) α β J μ₀ μ₁ e₀ W a t) (p, i)
  rw [deviceHamD_mulVec_apply]
  rfl

/-- **The device's clock on the torus**: the coherence between its two levels. -/
def deviceCoherenceD (Ψ : ((ι → ZMod L) × S) × Fin 2 → ℂ) : ℂ :=
  ∑ p, star (Ψ (p, 0)) * Ψ (p, 1)

/-- ★ **The device's clock is the coherence between its levels.** -/
theorem deviceCoherenceD_devicePacketD (J μ₀ μ₁ : ℝ) (e₀ : S → ℂ) (W : Finset (ι → ℤ))
    (a : Fin 2 → (ι → ℤ) → ℂ) (t : ℝ) :
    deviceCoherenceD (devicePacketD (L := L) α β J μ₀ μ₁ e₀ W a t)
      = levelCoherenceD (L := L) α β J μ₀ μ₁ e₀ W (a 0) (a 1) t := by
  have hm0 : levelMass μ₀ μ₁ 0 = μ₀ := by simp [levelMass]
  have hm1 : levelMass μ₀ μ₁ 1 = μ₁ := by simp [levelMass]
  simp only [deviceCoherenceD, levelCoherenceD, chainInnerD, devicePacketD, hm0, hm1]

end CSD.CV

end

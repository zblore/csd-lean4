/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Singlet.Expectations
public import CsdLean4.LF3.Projectors.SectorVolume

/-!
# LF3 Singlet / Kernel: pointer-sector kernel, correlation, marginals

**Category:** 3-Local (LF3 algebraic core: `P_st`, `cAmp`, `cst_squared_eq`, correlation, marginals, no-signalling).

Paper §6 / §7.

The algebraic core: `‖c_{st}(a,b)‖² = (1 − st · a·b) / 4` (spec §9.8 calls
this "the algebraic core of LF3"). Together with the strong-readout pointer
probability `P_{st}`, the singlet correlation `−a·b`, the marginal identities
`= 1/2`, and the operational no-signalling consequences, these supply the
content of `LF3_main_theorem`.

`cAmp` is defined in **closed form** via `Real.sqrt ((1 − st a·b)/4)`. This
sidesteps the explicit construction of joint spin eigenstates `|s_a, t_b⟩`
(which require either a parametric spectral decomposition or a unit
eigenvector of `jointSpinProj`); the squared-amplitude content `‖cAmp‖² =
(1 − st a·b)/4` is preserved exactly. A future v2 may swap the closed-form
definition for `cAmp := inner ℂ jointSpinEig singlet` once the eigenstate
construction is added; downstream theorems consume only `‖cAmp‖²`, so the
swap is transparent.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Matrix

namespace CSD
namespace LF3

/-- Three-vector dot product `a · b` for two `DetectorSetting`s, expanded as
    `∑_{i = 0, 1, 2} a_i b_i`. -/
noncomputable def dotR (a b : DetectorSetting) : ℝ :=
  a.vec 0 * b.vec 0 + a.vec 1 * b.vec 1 + a.vec 2 * b.vec 2

/-- The pointer-sector probability `P_{st}(a, b) = (1 − st · a·b) / 4`
    (paper §6.9, spec §9.8). -/
noncomputable def P_st (a b : DetectorSetting) (s t : Sign) : ℝ :=
  (1 - s.val * t.val * dotR a b) / 4

/-! ### Non-negativity of `P_st` (needed for `cAmp` definition) -/

/-- For unit vectors, `|a · b| ≤ 1`. Cauchy–Schwarz: identify `dotR` with the
    real inner product on `EuclideanSpace ℝ (Fin 3)` (the equality is `rfl`
    up to the `ofLp` and `star_trivial` reductions), then apply
    `abs_real_inner_le_norm` with the unit-norm hypotheses. -/
lemma abs_dotR_le_one (a b : DetectorSetting) : |dotR a b| ≤ 1 := by
  have h_inner : dotR a b = inner ℝ a.vec b.vec := by
    show dotR a b = b.vec.ofLp ⬝ᵥ star (a.vec.ofLp)
    rw [dotProduct, Fin.sum_univ_three]
    simp only [Pi.star_apply, star_trivial]
    unfold dotR
    ring
  rw [h_inner]
  have hbound := abs_real_inner_le_norm a.vec b.vec
  rw [a.unit, b.unit] at hbound
  linarith

/-- The pointer-sector probability is non-negative (needed to take `Real.sqrt`). -/
lemma P_st_nonneg (a b : DetectorSetting) (s t : Sign) : 0 ≤ P_st a b s t := by
  unfold P_st
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 4)
  -- 1 - st · a·b ≥ 0 since |st · a·b| ≤ 1
  have hst : s.val * t.val ∈ ({-1, 1} : Set ℝ) := by
    cases s <;> cases t <;> simp [Sign.val]
  rcases hst with h1 | h1
  · rw [h1]; linarith [abs_dotR_le_one a b, abs_le.mp (abs_dotR_le_one a b)]
  · rw [h1]; linarith [abs_dotR_le_one a b, abs_le.mp (abs_dotR_le_one a b)]

/-! ### Singlet amplitude (closed form) -/

/-- The singlet amplitude `c_{st}(a, b)`, defined in closed form as the real
    square root of `P_{st}(a, b)`. This is one canonical representative of
    the bra-ket form `⟨s_a, t_b | ψ⁻⟩`; only `‖cAmp‖²` is consumed downstream
    (in `sectorVolume_strong_readout` and the LF1↔LF2↔LF3 chain). -/
noncomputable def cAmp (a b : DetectorSetting) (s t : Sign) : ℂ :=
  ((Real.sqrt (P_st a b s t) : ℝ) : ℂ)

/-- **The algebraic core of LF3** (paper §6.9, spec §9.8):
    `‖c_{st}(a,b)‖² = (1 − st · a·b) / 4`. -/
theorem cst_squared_eq (a b : DetectorSetting) (s t : Sign) :
    ‖cAmp a b s t‖ ^ 2 = P_st a b s t := by
  unfold cAmp
  rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (P_st_nonneg a b s t)

/-! ### Born-form equivalence (paper §6.11)

The closed-form `cAmp = √P_st` is a real-valued representative of the
physical complex amplitude `⟨s_a, t_b | ψ⁻⟩`. The Born-form fidelity claim is
that this representative agrees with the genuine bra-ket inner product
`⟨v, ψ⁻⟩` on its squared norm, whenever `v : EuclideanSpace ℂ (Fin 2 × Fin
2)` is an actual joint spin eigenstate `|s_a, t_b⟩`. The equivalence is
expressed as a hypothesis on `‖inner ℂ v singlet‖² = P_st a b s t`; in a v2
with a constructed `jointSpinEig`, this hypothesis discharges from the
rank-1 projector identity `jointSpinProj = |v⟩⟨v|`. -/

/-- **Closed-form / bra-ket equivalence.** If `v : EuclideanSpace ℂ (Fin 2 ×
    Fin 2)` is a vector whose bra-ket inner product with the singlet has
    squared norm equal to `P_{st}(a, b)`, then `‖cAmp s t (a, b)‖² = ‖⟨v,
    ψ⁻⟩‖²`. The hypothesis `h_inner` is the inner-product-norm equality that
    a rank-1 projector identity `jointSpinProj = |v⟩⟨v|` would entail (via a
    spectral argument); the theorem here consumes that conclusion directly.
    A v2 construction of `jointSpinEig` from the spectral decomposition of
    `jointSpinProj` would discharge `h_inner` automatically. -/
theorem cAmp_norm_sq_eq_inner_norm_sq (a b : DetectorSetting) (s t : Sign)
    (v : EuclideanSpace ℂ (Fin 2 × Fin 2))
    (h_inner : ‖inner ℂ v singlet‖ ^ 2 = P_st a b s t) :
    ‖cAmp a b s t‖ ^ 2 = ‖inner ℂ v singlet‖ ^ 2 := by
  rw [cst_squared_eq, h_inner]

/-! ### Correlation and marginals (paper §6.10 / §7.3) -/

/-- **Singlet correlation** at the strong-readout limit: `∑_{s,t} st·P_{st}
    = −a·b`. Direct finite-`Sign × Sign`-sum calculation. -/
theorem correlation_eq_neg_dot (a b : DetectorSetting) :
    ∑ st : Sign × Sign, st.1.val * st.2.val * P_st a b st.1 st.2
      = -(dotR a b) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Sign.sum_univ]
  unfold P_st
  simp [Sign.val_plus, Sign.val_minus]
  ring

/-- **Singlet A-side marginal** at the strong-readout limit: `∑_t P_{st} =
    1/2`. Two-term sum, `1/2` for each sign. -/
theorem marginal_a_eq_half (a b : DetectorSetting) (s : Sign) :
    ∑ t : Sign, P_st a b s t = 1 / 2 := by
  unfold P_st
  rw [Sign.sum_univ]
  simp [Sign.val_plus, Sign.val_minus]
  ring

/-- **Singlet B-side marginal** at the strong-readout limit. -/
theorem marginal_b_eq_half (a b : DetectorSetting) (t : Sign) :
    ∑ s : Sign, P_st a b s t = 1 / 2 := by
  unfold P_st
  rw [Sign.sum_univ]
  simp [Sign.val_plus, Sign.val_minus]
  ring

/-! ### No-signalling corollaries (paper §7.10) -/

/-- **No-signalling, strong-readout, A side.** Alice's marginal is
    independent of Bob's setting. -/
theorem no_signalling_strong_readout_a
    (a b b' : DetectorSetting) (s : Sign) :
    (∑ t : Sign, P_st a b s t) = (∑ t : Sign, P_st a b' s t) := by
  rw [marginal_a_eq_half a b s, marginal_a_eq_half a b' s]

/-- **No-signalling, strong-readout, B side.** Bob's marginal is independent
    of Alice's setting. -/
theorem no_signalling_strong_readout_b
    (a a' b : DetectorSetting) (t : Sign) :
    (∑ s : Sign, P_st a b s t) = (∑ s : Sign, P_st a' b s t) := by
  rw [marginal_b_eq_half a b t, marginal_b_eq_half a' b t]

/-! ### Bridge to the abstract layer (paper §6.11) -/

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
  {S : SystemApparatusSetup K_A K_B H_SA}

/-- The strong-readout sector volume at the singlet equals the singlet kernel
    `P_{st}(a, b)`. Composes `sectorVolume_strong_readout` (operator-level
    sector volume on a `StrongReadoutCompat`-equipped projector algebra and
    measurement unitary) with `cst_squared_eq` (the closed-form algebraic
    core for the singlet amplitude). -/
theorem abstract_sectorVolume_eq_P_st_at_singlet
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (a b : DetectorSetting)
    (compat : StrongReadoutCompat P M φA0 φB0) (s t : Sign) :
    sectorVolume P (finalState M (cAmp a b) φA0 φB0) s t = P_st a b s t := by
  rw [sectorVolume_strong_readout P M φA0 φB0 (cAmp a b) compat s t]
  exact cst_squared_eq a b s t

end LF3
end CSD

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderBandFlat

/-!
# The transponder with a band, in contact with a messenger: what the contact launches

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2) for the transponder of
UA-21; fifth brick on it. Link L2 of the skeleton,
`specs/unified-record-spacetime-plan.md` §9.4).

The three earlier bricks are joined. For a messenger `ψ` and the transponder of UA-21
prepared in its first level with the wave function `χ`, both of norm `1`:

1. the contact term of UA-19 (b) does what the swap acting everywhere does, within `|g|`
   times the amplitude apart along the ungated orbit (`RecordLayer/TransponderBandGate.lean`);
2. with the swap acting everywhere, the banded transponder is the two-level transponder with
   the energies `E 0`, `E 1`, within `κ s`, `κ = (|g|/Ω) ‖(H₁ − E 1) χ‖`
   (`RecordLayer/TransponderBandFlat.lean`);
3. the two-level transponder is solved, stays on the sites of `χ`, and has the amplitude
   `(|g|/Ω) |sin Ωt|` in its second level (`RecordLayer/TransponderBandRabi.lean`).

* `sum_norm_sq_exp_skew_mulVec` — a unitary orbit of a unit vector has norm `1`;
* `one_kronecker_mulVec_prod` — an operator of the second carrier on a product;
* `norm_mul_mul_le_add_of_norm_le_one`, `abs_norm_mul_mul_sub_le_of_norm_le_one`;
* `norm_exp_band_sub_levels_mul_prod_le`, `norm_coincProj_levels_orbit_mul_prod_le`,
  ★ `norm_levelProj_one_levels_orbit_mul_prod`;
* ★★★ `transponder_band_contact_second_level` — **while the messenger's weight off sets
  `A s` that are wholly in contact with the transponder's sites is at most `ε`, the part of
  the state with the transponder in its second level has norm within
  `|g| (√ε + κ t) t + κ t` of `(|g|/Ω) |sin (Ω t)|`**.

## Honest scope

⚠️ **The messenger is any unit vector with a hypothesis on where its orbit is.** The sets
`A s` and the bound `ε` are hypotheses. The lattice Dirac packet and its moving box are not
substituted, and neither is `‖(H₁ − E 1) χ‖` for the Dirac band.

⚠️ **Contact from the flow time `0`.** The run does not start apart, so this does not show
that the launch follows the meeting; `transponder_band_launch_le` is the bound before it,
and the two are not yet in one run.

⚠️ **A short contact.** The error `κ t` is small only while the launched part has moved less
than the width of `χ`. The amplitude `(|g|/Ω) |sin Ωt|` is then at most `|g| t`, so a
launched amplitude that exceeds the error needs `|g| t` well above `κ t (1 + |g| t)`: a
spread of energies `‖(H₁ − E 1) χ‖` small against `Ω`. No instance is given.

⚠️ **The amplitude in the second level, not a return.** Where the launched part goes after
the contact, and that a receiver records it (R1 to R7 of §9.4), is not here.

⚠️ **Flow times.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UA-21,
UO-26, UD-262, UD-266, UD-267, UD-268, UD-269; §9.4); `RecordLayer/TransponderBandGate.lean`
(`transponder_band_gated_second_level`); `RecordLayer/TransponderBandFlat.lean`
(`sqrt_sum_norm_sq_exp_band_sub_levels_le`, `sum_norm_sq_exp_compositeH_sub_prod`);
`RecordLayer/TransponderBandRabi.lean` (`exp_levels_swap_mulVec_inLevel_zero`);
`RecordLayer/CoincidenceOrbit.lean` (`sum_norm_sq_coincProj_freeOrbit_prod_le`);
`RecordLayer/TransponderDetunedMeeting.lean` (`norm_exp_skew_mul`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### Tools -/

section Tools

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A unitary orbit of a unit vector has norm `1`. -/
theorem sum_norm_sq_exp_skew_mulVec [Nonempty m] {A : Matrix m m ℂ} (hA : Aᴴ = -A) (t : ℝ)
    {v : m → ℂ} (hv : ∑ x, ‖v x‖ ^ 2 = 1) : ∑ x, ‖(exp (t • A) *ᵥ v) x‖ ^ 2 = 1 := by
  have h := norm_exp_skew_mul hA t (Matrix.vecMulVec v (star v))
  rw [norm_mul_vecMulVec, (norm_vecMulVec_star_of_sum_eq_one hv).1, mul_one,
    (norm_vecMulVec_star_of_sum_eq_one hv).2] at h
  exact Real.sqrt_eq_one.1 h

/-- A part of an orbit against the same part of a reference orbit. -/
theorem norm_mul_mul_le_add_of_norm_le_one {P : Matrix m m ℂ} (hP : ‖P‖ ≤ 1)
    (U F X : Matrix m m ℂ) : ‖P * U * X‖ ≤ ‖P * F * X‖ + ‖(U - F) * X‖ := by
  have e : P * U * X = P * F * X + P * ((U - F) * X) := by
    simp only [mul_assoc, sub_mul, mul_sub]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hP)))

/-- The norms of a part of two orbits differ by at most the orbits' difference. -/
theorem abs_norm_mul_mul_sub_le_of_norm_le_one {Q : Matrix m m ℂ} (hQ : ‖Q‖ ≤ 1)
    (U F X : Matrix m m ℂ) : |‖Q * U * X‖ - ‖Q * F * X‖| ≤ ‖(U - F) * X‖ := by
  have e : Q * U * X - Q * F * X = Q * ((U - F) * X) := by
    simp only [mul_assoc, mul_sub, sub_mul]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [e]
  exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hQ)

end Tools

section Prod

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- An operator of the second carrier acts on a product through the second factor. -/
theorem one_kronecker_mulVec_prod (P : Matrix κ κ ℂ) (a : ι → ℂ) (b : κ → ℂ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ P) *ᵥ (fun y : ι × κ => a y.1 * b y.2)
      = fun y : ι × κ => a y.1 * (P *ᵥ b) y.2 := by
  funext y
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply]
  rw [Finset.sum_eq_single y.1]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [↓reduceIte]
      ring
  · intro i _ hi
    exact Finset.sum_eq_zero fun j _ => by
      simp only [Ne.symm hi, ↓reduceIte]
      ring
  · intro h
    exact absurd (Finset.mem_univ _) h

end Prod

/-! ### The three pieces for a product with a messenger -/

section Contact

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Nonempty ι] [Nonempty n]

omit [DecidableEq ι] [DecidableEq n] [Nonempty ι] [Nonempty n] in
/-- The product of a unit messenger and a unit first-level state has norm `1`. -/
theorem sum_norm_sq_prod_inLevel_zero {ψ : ι → ℂ} (hψ : ∑ p, ‖ψ p‖ ^ 2 = 1) {χ : n → ℂ}
    (hχ : ∑ p, ‖χ p‖ ^ 2 = 1) :
    ∑ x : ι × (n × Fin 2), ‖ψ x.1 * inLevel 0 χ x.2‖ ^ 2 = 1 := by
  rw [sum_norm_sq_prod, hψ, sum_norm_sq_inLevel, hχ, one_mul]

omit [Fintype n] [Nonempty ι] [Nonempty n] in
/-- Level energies with no hopping, plus the swap term, are Hermitian. -/
theorem levels_add_swap_isHermitian (E : Fin 2 → ℝ) (g : ℝ) :
    (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      + (g : ℂ) • levelSwap n).IsHermitian := by
  have hgS : ((g : ℂ) • levelSwap n).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, (levelSwap_isHermitian n).eq,
      Complex.star_def, Complex.conj_ofReal]
  have hEh : ∀ l : Fin 2, (((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun l =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  exact (blockDiagonal_isHermitian hEh).add hgS

/-- **The band against one energy, for a product with a messenger.** -/
theorem norm_exp_band_sub_levels_mul_prod_le {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    (E : Fin 2 → ℝ) {H₁ : Matrix n n ℂ} (hH₁ : H₁.IsHermitian) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2) {ψ : ι → ℂ} (hψ : ∑ p, ‖ψ p‖ ^ 2 = 1)
    {χ : n → ℂ} (hχ : ∑ p, ‖χ p‖ ^ 2 = 1) {s : ℝ} (hs : 0 ≤ s) :
    ‖(exp (s • ((-Complex.I) • compositeH M₀
            (Matrix.blockDiagonal (bandBlocks (E 0) H₁) + (g : ℂ) • levelSwap n)))
        - exp (s • ((-Complex.I) • compositeH M₀
            (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • levelSwap n))))
        * Matrix.vecMulVec (fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)
          (star fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)‖
      ≤ |g| / Ω * Real.sqrt (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2)
        * s := by
  rw [norm_mul_vecMulVec,
    (norm_vecMulVec_star_of_sum_eq_one (sum_norm_sq_prod_inLevel_zero hψ hχ)).1, mul_one,
    Matrix.sub_mulVec, sum_norm_sq_exp_compositeH_sub_prod,
    sum_norm_sq_exp_skew_mulVec (Matrix.conjTranspose_neg_I_smul hM) s hψ, one_mul]
  exact sqrt_sum_norm_sq_exp_band_sub_levels_le E hH₁ g hΩ hΩ2 hχ hs

omit [Nonempty ι] in
/-- **The reference orbit's amplitude on related configurations.** For the two-level
transponder with the swap acting everywhere, a first-level state `χ` on the sites `B` and
sets `A`, `B` with no pair in the relation `ρ`: the amplitude on the `ρ`-related
configurations is at most the square root of the messenger's weight off `A`. -/
theorem norm_coincProj_levels_orbit_mul_prod_le [DecidableEq S] (σ : ι → S)
    (τ : n × Fin 2 → S) (ρ : S → S → Prop) [DecidableRel ρ] (M₀ : Matrix ι ι ℂ)
    (E : Fin 2 → ℝ) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2) {ψ : ι → ℂ} (hψ : ∑ p, ‖ψ p‖ ^ 2 = 1)
    {χ : n → ℂ} (hχ : ∑ p, ‖χ p‖ ^ 2 = 1) {A B : Finset S}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ ρ a b) (hχB : ∀ q : n × Fin 2, τ q ∉ B → χ q.1 = 0)
    (s : ℝ) :
    ‖coincProj σ τ ρ
        * exp (s • ((-Complex.I) • compositeH M₀
            (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • levelSwap n)))
        * Matrix.vecMulVec (fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)
          (star fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)‖
      ≤ Real.sqrt (∑ p, if σ p ∈ A then 0
          else ‖(exp (s • ((-Complex.I) • M₀)) *ᵥ ψ) p‖ ^ 2) := by
  have hv1 : ∑ q, ‖inLevel 0 χ q‖ ^ 2 = 1 := by rw [sum_norm_sq_inLevel, hχ]
  rw [norm_mul_vecMulVec,
    (norm_vecMulVec_star_of_sum_eq_one (sum_norm_sq_prod_inLevel_zero hψ hχ)).1, mul_one,
    ← Matrix.mulVec_mulVec]
  refine Real.sqrt_le_sqrt ?_
  have h1 := sum_norm_sq_coincProj_freeOrbit_prod_le σ τ ρ M₀
    (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      + (g : ℂ) • levelSwap n) s ψ (inLevel 0 χ) hAB
  have hw1 := sum_norm_sq_exp_skew_mulVec
    (Matrix.conjTranspose_neg_I_smul (levels_add_swap_isHermitian (n := n) E g)) s hv1
  have hB0 : (∑ q, if τ q ∈ B then (0 : ℝ) else
      ‖(exp (s • ((-Complex.I) • (Matrix.blockDiagonal
          (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • levelSwap n))) *ᵥ inLevel 0 χ) q‖ ^ 2) = 0 :=
    Finset.sum_eq_zero fun q _ => by
      split_ifs with hq
      · rfl
      · rw [exp_levels_swap_mulVec_inLevel_zero E g hΩ hΩ2 χ s]
        simp [inLevel, hχB q hq]
  rw [hw1, hB0, mul_one, mul_zero, add_zero] at h1
  exact h1

omit [Nonempty n] in
/-- ★ **The reference orbit's second level.** For the two-level transponder with the swap
acting everywhere and a unit product with the transponder in its first level, the part in
the second level has norm exactly `(|g|/Ω) |sin (Ω t)|`. -/
theorem norm_levelProj_one_levels_orbit_mul_prod {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    (E : Fin 2 → ℝ) (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2) {ψ : ι → ℂ} (hψ : ∑ p, ‖ψ p‖ ^ 2 = 1)
    {χ : n → ℂ} (hχ : ∑ p, ‖χ p‖ ^ 2 = 1) (t : ℝ) :
    ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • compositeH M₀
            (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • levelSwap n)))
        * Matrix.vecMulVec (fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)
          (star fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)‖
      = |g| / Ω * |Real.sin (Ω * t)| := by
  rw [norm_mul_vecMulVec,
    (norm_vecMulVec_star_of_sum_eq_one (sum_norm_sq_prod_inLevel_zero hψ hχ)).1, mul_one,
    ← Matrix.mulVec_mulVec, exp_compositeH_mulVec_prod, one_kronecker_mulVec_prod,
    sum_norm_sq_prod, sum_norm_sq_exp_skew_mulVec (Matrix.conjTranspose_neg_I_smul hM) t hψ,
    one_mul, exp_levels_swap_mulVec_inLevel_zero E g hΩ hΩ2 χ t, Matrix.mulVec_smul,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
    levelProj_mulVec_inLevel_of_ne (l := 1) (k := 0) (by decide) χ,
    levelProj_mulVec_inLevel_same, smul_zero, zero_sub, smul_neg, smul_smul, ← neg_smul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [← Finset.mul_sum, sum_norm_sq_inLevel, hχ, mul_one, Real.sqrt_sq (norm_nonneg _),
    norm_neg_exp_mul_I_sin_mul, abs_div, abs_of_pos hΩ, mul_comm]

/-- ★★★ **What the contact launches from the transponder of UA-21.** The messenger `ψ` has
norm `1`; the transponder has the first-level energy `E 0` and a Hermitian second-level
Hamiltonian `H₁`, and starts in its first level with a wave function `χ` of norm `1` on the
sites `B`. `Ω > 0` with `Ω² = g² + ((E 1 − E 0)/2)²`, and
`κ = (|g|/Ω) ‖(H₁ − E 1) χ‖`. If at every flow time `s` of `[0, t]` every site of `A s` is in
the relation `r` with every site of `B`, and the messenger's orbit has weight at most `ε`
off `A s`, then the part of the state at `t` with the transponder in its second level has
norm within `|g| (√ε + κ t) t + κ t` of `(|g|/Ω) |sin (Ω t)|`. -/
theorem transponder_band_contact_second_level [DecidableEq S] (σ : ι → S)
    (τ : n × Fin 2 → S) (r : S → S → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0) {M₀ : Matrix ι ι ℂ}
    (hM : M₀.IsHermitian) (E : Fin 2 → ℝ) {H₁ : Matrix n n ℂ} (hH₁ : H₁.IsHermitian)
    (g : ℝ) {Ω : ℝ} (hΩ : 0 < Ω) (hΩ2 : Ω ^ 2 = g ^ 2 + ((E 1 - E 0) / 2) ^ 2)
    {ψ : ι → ℂ} (hψ : ∑ p, ‖ψ p‖ ^ 2 = 1) {χ : n → ℂ} (hχ : ∑ p, ‖χ p‖ ^ 2 = 1)
    (B : Finset S) (hχB : ∀ q : n × Fin 2, τ q ∉ B → χ q.1 = 0) (A : ℝ → Finset S)
    {ε t : ℝ} (ht : 0 ≤ t)
    (hcont : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ A s, ∀ b ∈ B, r a b)
    (hA : ∀ s, 0 ≤ s → s ≤ t → (∑ p, if σ p ∈ A s then 0
      else ‖(exp (s • ((-Complex.I) • M₀)) *ᵥ ψ) p‖ ^ 2) ≤ ε) :
    |Real.sqrt (∑ x, ‖((((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
          * exp (t • ((-Complex.I) • (compositeH M₀
              (Matrix.blockDiagonal (bandBlocks (E 0) H₁))
            + (g : ℂ) • gateOp σ τ r (levelSwap n)))))
          *ᵥ fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2) x‖ ^ 2)
        - (|g| / Ω * |Real.sin (Ω * t)|)|
      ≤ |g| * ((Real.sqrt ε
            + |g| / Ω * Real.sqrt
                (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2) * t) * t)
        + |g| / Ω * Real.sqrt
            (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2) * t := by
  have hκ0 : 0 ≤ |g| / Ω * Real.sqrt
      (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2) :=
    mul_nonneg (div_nonneg (abs_nonneg g) hΩ.le) (Real.sqrt_nonneg _)
  have hP1 : ‖coincProj σ τ (fun a b => ¬ r a b)‖ ≤ 1 :=
    norm_le_one_of_isHermitian_idem (coincProj_isHermitian σ τ _) (coincProj_mul_self σ τ _)
  have hQ1 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1‖ ≤ 1 :=
    norm_le_one_of_isHermitian_idem (one_kronecker_levelProj_isHermitian 1)
      (one_kronecker_levelProj_mul_self 1)
  have hd := fun (s : ℝ) (hs : 0 ≤ s) =>
    norm_exp_band_sub_levels_mul_prod_le hM E hH₁ g hΩ hΩ2 hψ hχ hs
  -- the amplitude apart along the ungated orbit
  have hint : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀
              (Matrix.blockDiagonal (bandBlocks (E 0) H₁) + (g : ℂ) • levelSwap n)))
          * Matrix.vecMulVec (fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)
            (star fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)‖
        ≤ Real.sqrt ε + |g| / Ω * Real.sqrt
            (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2) * t := by
    intro s hs
    refine (norm_mul_mul_le_add_of_norm_le_one hP1 _
      (exp (s • ((-Complex.I) • compositeH M₀
        (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
          + (g : ℂ) • levelSwap n)))) _).trans (add_le_add ?_ ?_)
    · exact (norm_coincProj_levels_orbit_mul_prod_le σ τ (fun a b => ¬ r a b) M₀ E g hΩ hΩ2
        hψ hχ (A := A s) (B := B)
        (fun a ha b hb h => h (hcont s hs.1 hs.2 a ha b hb)) hχB s).trans
        (Real.sqrt_le_sqrt (hA s hs.1 hs.2))
    · exact (hd s hs.1).trans (mul_le_mul_of_nonneg_left hs.2 hκ0)
  have hI : (∫ s in (0 : ℝ)..t, ‖coincProj σ τ (fun a b => ¬ r a b)
          * exp (s • ((-Complex.I) • compositeH M₀
              (Matrix.blockDiagonal (bandBlocks (E 0) H₁) + (g : ℂ) • levelSwap n)))
          * Matrix.vecMulVec (fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)
            (star fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)‖)
      ≤ (Real.sqrt ε + |g| / Ω * Real.sqrt
          (∑ p, ‖((H₁ - ((E 1 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) p‖ ^ 2) * t) * t := by
    refine (intervalIntegral.integral_mono_on ht
      ((Matrix.continuous_norm_mul_exp_smul_mul _ _ _).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) hint).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
  have h1 := (transponder_band_gated_second_level σ τ r hτ hM (E 0) hH₁ g
    (Matrix.vecMulVec (fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)
      (star fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)) ht).trans
    (mul_le_mul_of_nonneg_left hI (abs_nonneg g))
  have h2 := (abs_norm_mul_mul_sub_le_of_norm_le_one hQ1
    (exp (t • ((-Complex.I) • compositeH M₀
      (Matrix.blockDiagonal (bandBlocks (E 0) H₁) + (g : ℂ) • levelSwap n))))
    (exp (t • ((-Complex.I) • compositeH M₀
      (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        + (g : ℂ) • levelSwap n))))
    (Matrix.vecMulVec (fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2)
      (star fun y : ι × (n × Fin 2) => ψ y.1 * inLevel 0 χ y.2))).trans (hd t ht)
  rw [norm_levelProj_one_levels_orbit_mul_prod hM E g hΩ hΩ2 hψ hχ t] at h2
  have hfin := (abs_sub_le _ _ _).trans (add_le_add h1 h2)
  rwa [norm_mul_vecMulVec,
    (norm_vecMulVec_star_of_sum_eq_one (sum_norm_sq_prod_inLevel_zero hψ hχ)).1, mul_one]
    at hfin

end Contact

end CSD.RecordLayer

end

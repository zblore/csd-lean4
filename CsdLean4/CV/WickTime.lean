/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.FeynmanVertex
public import CsdLean4.Mathlib.Combinatorics.PairingSum

/-!
# CV-28: Wick's theorem at the cutoff — every word, every time

**Category:** 3-Local (CV; continuous variables — the multi-mode field).

CV-23 proved Wick's theorem at the cutoff for four quadratures at distinct stroboscopic periods
(`timeFourPoint_wick`) and, in CV-23d, for an arbitrary equal-time word
(`wordOp_vac_eq_prod_wickMoment`). This module states it once, for every word and every real
time: the vacuum expectation of `Q_{k₁}(t₁) ⋯ Q_{kₘ}(tₘ)`, each quadrature at its own Heisenberg
time under the free field, is the **sum over perfect matchings** of the insertions of the product
of the propagator lines, a line joining two insertions of the same mode with the kernel
`½ e^{−i tᵢ} e^{+i tⱼ}`. The pairing sum is written in its first-contraction recursive form
(`wickSum`): the leftmost insertion is contracted with each later insertion of its mode in turn,
and the rest is the pairing sum of the word with the two removed.

* `quadratureAt t` — the single-mode quadrature at time `t`, `e^{−it}/√2 · a + e^{it}/√2 · a†`
  (`quadratureAt_apply`: the free phases dress the two hops); `timeQ t k` — the quadrature of mode
  `k` at real time `t`, `U(t)† Q_k U(t)`, and ★ `timeQ_eq_modeOp` — it is `modeOp k` of
  `quadratureAt t`;
* `timeWord l` — the product of the insertions `(k, t)` of a word, in the written order;
  `contraction x y` — the propagator line, `δ_{kl} · ½ e^{−it} e^{+is}`; `wickSum l` — the pairing
  sum, `wickSum [] = 1`, `wickSum (x :: l) = ∑ⱼ contraction x lⱼ · wickSum (l without j)`;
* ★★ `timeWord_vac_eq_wickSum` — **Wick's theorem at the cutoff, every word, every time**: below
  the threshold `count k / 2 < N` for every mode,
  `⟨vac∣ Q_{k₁}(t₁) ⋯ Q_{kₘ}(tₘ) ∣vac⟩ = wickSum [(k₁, t₁), …, (kₘ, tₘ)]`.
  The proof is the first-contraction recursion ★ `timeWord_cons_vac`: the vacuum row of the
  leftmost quadrature is its annihilator row; commuting the annihilator through the rest of the
  word (`mul_map_prod_sub_map_prod_mul`, the commutator of a product one factor at a time) meets
  the truncated CCR at each later insertion of the same mode
  (`annihilation_quadratureAt_commutator`); the CCR's rank-one defect at the top level dies
  because the word cannot lift the vacuum that high on both sides of the defect at once
  (`timeWord_apply_eq_zero_of_lt`, the walk band, and `timeWord_mul_topProj_mul_timeWord_vac`);
* corollaries — `wickSum_eq_zero_of_odd` (odd words vanish), `wickSum_pair`, `wickSum_four` (the
  three pairings), ★ `timeFourPoint_eq_wickSum` (CV-23b's four-point function is the pairing sum
  at stroboscopic times: `contraction_natMul` is `twoPointKernel`), ★ `wickSum_map_zero` (at equal
  time the pairing sum is CV-23d's `∏_k wickMoment (count k)`), and
  ★★ `dysonTerm_two_vac_wordOp` — **the second-order vacuum diagrams of every monomial vertex**:
  for `V = Q_{k₁} ⋯ Q_{kₘ}` the two-vertex amplitude of CV-27 is the ordered double integral of the
  pairing sum of the word with itself at the time difference — the `Q⁴` sunset and its
  disconnected partners, at the cutoff, as a theorem;
* ★★ `wickSum_eq_pairingSum` / ★★ `timeWord_vac_eq_pairingSum` — **the matching-indexed form**:
  `wickSum l` is `Fin.pairingSum` of the contraction on the positions of `l`, the sum over
  perfect matchings `σ` of `Fin m` of `∏_{i < σ i} contraction lᵢ l_{σ i}`; so the vacuum
  expectation of a word is the sum over the perfect matchings of its insertions of the product of
  the propagator lines, Wick's theorem as the textbook states it.

**Why the threshold.** Contracting the leftmost insertion of mode `k` with a later one leaves the
CCR defect `N · |N−1⟩⟨N−1|` sandwiched between the two halves of the word; a half with fewer than
`N − 1` insertions of mode `k` cannot connect the vacuum to the top level, and with `count k < 2N`
one half always has fewer. Exactly CV-23c's `n < N`, one insertion at a time.

## Honest scope

⚠️ **Two forms of the pairing sum.** `wickSum` is the pairing sum computed by first contraction;
★★ `wickSum_eq_pairingSum` identifies it with the matching-indexed form of
`Mathlib/Combinatorics/PairingSum.lean` — the sum over fixed-point-free involutions `σ` of the
positions of the product over the pairs `i < σ i` of `contraction lᵢ l_{σ i}` — and
★★ `timeWord_vac_eq_pairingSum` states Wick's theorem in that textbook form.

⚠️ **Finite cutoff, free dynamics.** The thresholds are where Wick survives truncation; the
times are Heisenberg times under the free field only. Nothing continuum is claimed.

References: `CV/Wick.lean` (CV-23b/c: `timeFourPoint_wick`, `twoPointKernel`, the walk band and
the moment recursion this module generalises); `CV/WickGeneral.lean` (CV-23d);
`CV/FeynmanVertex.lean` (CV-27, `dysonTerm_two_vac`); `CV/Oscillator.lean` (`truncated_ccr`,
`topProj`); `CV/ModeLocality.lean` (`modeOp`, `commute_modeOp`);
`Mathlib/Combinatorics/PairingSum.lean` (`Fin.pairingSum`, `Fin.pairingSum_succ_succ`);
`specs/BACKLOG.md` #36(b)(iv), (iv′); `specs/future-work.md` (row CV-28).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix NormedSpace

namespace CSD.CV

variable {K N : ℕ}

/-! ### A commutator through a product -/

/-- The commutator with a product, one factor at a time:
`[A, ∏ f l] = ∑ⱼ (∏ f (l.take j)) · [A, f lⱼ] · (∏ f (l.drop (j + 1)))`. -/
theorem mul_map_prod_sub_map_prod_mul {R α : Type*} [Ring R] (A : R) (f : α → R) :
    ∀ l : List α, A * (l.map f).prod - (l.map f).prod * A
      = ∑ j : Fin l.length, ((l.take j).map f).prod * (A * f l[j] - f l[j] * A)
          * ((l.drop (j + 1)).map f).prod
  | [] => by simp
  | x :: l => by
    have ih := mul_map_prod_sub_map_prod_mul A f l
    show _ = ∑ j : Fin (l.length + 1), _
    rw [Fin.sum_univ_succ]
    simp only [List.map_cons, List.prod_cons, Fin.getElem_fin, Fin.val_zero, List.take_zero,
      List.map_nil, List.prod_nil, one_mul, zero_add, List.getElem_cons_zero, Fin.val_succ,
      List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, List.drop_zero]
    simp only [Fin.getElem_fin, mul_assoc] at ih ⊢
    rw [← Finset.mul_sum, ← ih]
    noncomm_ring

/-! ### The single-mode quadrature at time `t` -/

/-- The coefficient `e^{−it}/√2` of the annihilator in the evolved quadrature. -/
noncomputable def ladderPhase (t : ℝ) : ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * Complex.exp (-(Complex.I * t))

theorem ladderPhase_mul_ladderPhase_neg (t s : ℝ) :
    ladderPhase t * ladderPhase (-s)
      = 2⁻¹ * Complex.exp (-(Complex.I * t)) * Complex.exp (Complex.I * s) := by
  rw [ladderPhase, ladderPhase, Complex.ofReal_neg, mul_neg, neg_neg, ← inv_sqrt_two_mul_self]
  ring

/-- **The single-mode quadrature at time `t`**: `Q(t) = e^{−it}/√2 · a + e^{it}/√2 · a†`. -/
noncomputable def quadratureAt (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  ladderPhase t • annihilation N + ladderPhase (-t) • creation N

/-- The free phases dress the two hops: `Q(t) i j = e^{it (i − j)} · Q i j`. -/
theorem quadratureAt_apply (t : ℝ) (i j : Fin N) :
    quadratureAt (N := N) t i j
      = Complex.exp (Complex.I * t * (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ))) * Q N i j := by
  rw [quadratureAt, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul, Q, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, annihilation_apply,
    creation_apply, ladderPhase, ladderPhase]
  by_cases h1 : (i : ℕ) + 1 = (j : ℕ)
  · have h2 : ¬ (j : ℕ) + 1 = (i : ℕ) := by omega
    have hij : ((i : ℕ) : ℂ) - ((j : ℕ) : ℂ) = -1 := by
      rw [← h1]; push_cast; ring
    rw [if_pos h1, if_neg h2, hij, Complex.ofReal_neg, mul_neg, neg_neg]
    simp only [mul_zero, add_zero, mul_neg, mul_one]
    ring
  · by_cases h2 : (j : ℕ) + 1 = (i : ℕ)
    · have hij : ((i : ℕ) : ℂ) - ((j : ℕ) : ℂ) = 1 := by
        rw [← h2]; push_cast; ring
      rw [if_neg h1, if_pos h2, hij, Complex.ofReal_neg, mul_neg, neg_neg]
      simp only [mul_zero, zero_add, mul_one]
      ring
    · rw [if_neg h1, if_neg h2]
      simp

/-- The evolved quadrature is strictly tridiagonal, like the bare one. -/
theorem quadratureAt_apply_eq_zero_of_far [NeZero N] (t : ℝ) {i j : Fin N}
    (h1 : (i : ℕ) + 1 ≠ (j : ℕ)) (h2 : (j : ℕ) + 1 ≠ (i : ℕ)) :
    quadratureAt (N := N) t i j = 0 := by
  rw [quadratureAt_apply, Q_apply_eq_zero_of_far h1 h2, mul_zero]

/-- The truncated CCR against the evolved quadrature:
`[a, Q(t)] = e^{it}/√2 · (1 − N · topProj)`. -/
theorem annihilation_quadratureAt_commutator (t : ℝ) :
    annihilation N * quadratureAt t - quadratureAt t * annihilation N
      = ladderPhase (-t) • ((1 : Matrix (Fin N) (Fin N) ℂ) - (N : ℂ) • topProj N) := by
  rw [← truncated_ccr, quadratureAt, mul_add, add_mul, mul_smul_comm, mul_smul_comm,
    smul_mul_assoc, smul_mul_assoc, smul_sub]
  abel

/-! ### `modeOp` algebra -/

theorem modeOp_apply_of_not_agree (k : Fin K) (a : Matrix (Fin N) (Fin N) ℂ)
    {c d : FieldConfig K N} (h : ¬ ∀ j, j ≠ k → c j = d j) : modeOp k a c d = 0 := by
  rw [modeOp, if_neg h]

theorem modeOp_add (k : Fin K) (a b : Matrix (Fin N) (Fin N) ℂ) :
    modeOp k (a + b) = modeOp k a + modeOp k b := by
  ext c d
  by_cases h : ∀ j, j ≠ k → c j = d j
  · rw [Matrix.add_apply, modeOp_apply_of_agree k _ h, modeOp_apply_of_agree k _ h,
      modeOp_apply_of_agree k _ h, Matrix.add_apply]
  · rw [Matrix.add_apply, modeOp_apply_of_not_agree k _ h, modeOp_apply_of_not_agree k _ h,
      modeOp_apply_of_not_agree k _ h, add_zero]

theorem modeOp_smul (k : Fin K) (r : ℂ) (a : Matrix (Fin N) (Fin N) ℂ) :
    modeOp k (r • a) = r • modeOp k a := by
  ext c d
  by_cases h : ∀ j, j ≠ k → c j = d j
  · rw [Matrix.smul_apply, modeOp_apply_of_agree k _ h, modeOp_apply_of_agree k _ h,
      Matrix.smul_apply]
  · rw [Matrix.smul_apply, modeOp_apply_of_not_agree k _ h, modeOp_apply_of_not_agree k _ h,
      smul_zero]

theorem modeOp_sub (k : Fin K) (a b : Matrix (Fin N) (Fin N) ℂ) :
    modeOp k (a - b) = modeOp k a - modeOp k b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, modeOp_add, ← neg_one_smul ℂ b, modeOp_smul,
    neg_one_smul]

/-- `modeOp` of a diagonal matrix is diagonal in the configuration basis. -/
theorem modeOp_diagonal (k : Fin K) (f : Fin N → ℂ) :
    modeOp k (Matrix.diagonal f) = Matrix.diagonal fun c : FieldConfig K N => f (c k) := by
  ext c d
  by_cases hcd : c = d
  · subst hcd
    rw [modeOp_apply_of_agree k _ (fun _ _ => rfl), Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hcd]
    by_cases h : ∀ j, j ≠ k → c j = d j
    · rw [modeOp_apply_of_agree k _ h, Matrix.diagonal_apply_ne]
      intro hk
      exact hcd (funext fun j => by
        by_cases hj : j = k
        · subst hj; exact hk
        · exact h j hj)
    · exact modeOp_apply_of_not_agree k _ h

/-- The creation operator has no vacuum row. -/
theorem modeOp_creation_vac_apply [NeZero N] (k : Fin K) (e : FieldConfig K N) :
    modeOp k (creation N) (vacCfg K N) e = 0 := by
  by_cases h : ∀ j, j ≠ k → vacCfg K N j = e j
  · rw [modeOp_apply_of_agree k _ h, creation_apply, vacCfg_apply, if_neg (by simp)]
  · exact modeOp_apply_of_not_agree k _ h

/-- The annihilation operator has no vacuum column. -/
theorem modeOp_annihilation_apply_vac [NeZero N] (k : Fin K) (e : FieldConfig K N) :
    modeOp k (annihilation N) e (vacCfg K N) = 0 := by
  by_cases h : ∀ j, j ≠ k → e j = vacCfg K N j
  · rw [modeOp_apply_of_agree k _ h, annihilation_apply, vacCfg_apply, if_neg (by simp)]
  · exact modeOp_apply_of_not_agree k _ h

/-! ### The quadrature of a mode at a real time -/

/-- The Heisenberg entry formula for the free evolution at a real time. -/
theorem heisenberg_freeFieldU_apply (τ : ℝ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (c d : FieldConfig K N) :
    heisenberg (freeFieldU K N τ) A c d
      = Complex.exp (Complex.I * τ * (((fieldEnergy c : ℝ) : ℂ) - ((fieldEnergy d : ℝ) : ℂ)))
          * A c d := by
  rw [← pow_one (freeFieldU K N τ), heisenberg_freeFieldU_pow_apply, Nat.cast_one, one_mul]

/-- Configurations agreeing off one mode differ in energy by that mode's occupation. -/
theorem fieldEnergy_sub_of_agree {c d : FieldConfig K N} (k : Fin K)
    (h : ∀ j, j ≠ k → c j = d j) :
    fieldEnergy c - fieldEnergy d = ((c k : ℕ) : ℝ) - ((d k : ℕ) : ℝ) := by
  rw [fieldEnergy, fieldEnergy, ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
  · rw [oscEnergy, oscEnergy]
    ring
  · intro j _ hj
    rw [h j hj, sub_self]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- **The quadrature of mode `k` at real time `t`**: `Q_k(t) = U(t)† Q_k U(t)`. -/
noncomputable def timeQ (t : ℝ) (k : Fin K) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  heisenberg (freeFieldU K N t) (modeOp k (Q N))

/-- ★ The evolved mode quadrature is the single-mode evolved quadrature on its mode. -/
theorem timeQ_eq_modeOp (t : ℝ) (k : Fin K) :
    timeQ (N := N) t k = modeOp k (quadratureAt t) := by
  ext c d
  rw [timeQ, heisenberg_freeFieldU_apply]
  by_cases h : ∀ j, j ≠ k → c j = d j
  · rw [modeOp_apply_of_agree k _ h, modeOp_apply_of_agree k _ h, quadratureAt_apply,
      ← Complex.ofReal_sub, fieldEnergy_sub_of_agree k h]
    push_cast
    rfl
  · rw [modeOp_apply_of_not_agree k _ h, modeOp_apply_of_not_agree k _ h, mul_zero]

/-- Where an evolved quadrature has an entry: the configurations agree off its mode and differ
by one quantum on it. -/
theorem timeQ_support [NeZero N] (t : ℝ) (k : Fin K) {c d : FieldConfig K N}
    (h : timeQ (N := N) t k c d ≠ 0) :
    (∀ j, j ≠ k → c j = d j) ∧ ((c k : ℕ) + 1 = (d k : ℕ) ∨ (d k : ℕ) + 1 = (c k : ℕ)) := by
  rw [timeQ_eq_modeOp] at h
  by_cases hagree : ∀ j, j ≠ k → c j = d j
  · refine ⟨hagree, ?_⟩
    rw [modeOp_apply_of_agree k _ hagree] at h
    by_contra hstep
    push Not at hstep
    exact h (quadratureAt_apply_eq_zero_of_far t hstep.1 hstep.2)
  · exact absurd (modeOp_apply_of_not_agree k _ hagree) h

/-- The commutator of a mode's annihilator with an evolved quadrature: zero at another mode,
the truncated CCR at its own. -/
theorem modeOp_annihilation_timeQ_commutator (t : ℝ) (k k' : Fin K) :
    modeOp k (annihilation N) * timeQ (N := N) t k' - timeQ t k' * modeOp k (annihilation N)
      = if k' = k then
          ladderPhase (-t) • ((1 : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
            - (N : ℂ) • modeOp k (topProj N))
        else 0 := by
  rw [timeQ_eq_modeOp]
  split_ifs with hk
  · subst hk
    rw [modeOp_mul, modeOp_mul, ← modeOp_sub, annihilation_quadratureAt_commutator, modeOp_smul,
      modeOp_sub, modeOp_one, modeOp_smul]
  · rw [commute_modeOp (fun h => hk h.symm), sub_self]

/-! ### Words at their times, the contraction and the pairing sum -/

/-- **The word** `Q_{k₁}(t₁) ⋯ Q_{kₘ}(tₘ)` of the insertions `(kᵢ, tᵢ)`, in the written order. -/
noncomputable def timeWord (l : List (Fin K × ℝ)) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  (l.map fun x => timeQ (N := N) x.2 x.1).prod

@[simp] theorem timeWord_nil : timeWord (N := N) ([] : List (Fin K × ℝ)) = 1 := rfl

theorem timeWord_cons (x : Fin K × ℝ) (l : List (Fin K × ℝ)) :
    timeWord (N := N) (x :: l) = timeQ x.2 x.1 * timeWord l := rfl

theorem timeWord_append (l₁ l₂ : List (Fin K × ℝ)) :
    timeWord (N := N) (l₁ ++ l₂) = timeWord l₁ * timeWord l₂ := by
  rw [timeWord, timeWord, timeWord, List.map_append, List.prod_append]

theorem timeWord_eraseIdx (l : List (Fin K × ℝ)) (j : ℕ) :
    timeWord (N := N) (l.eraseIdx j) = timeWord (l.take j) * timeWord (l.drop (j + 1)) := by
  rw [List.eraseIdx_eq_take_drop_succ, timeWord_append]

/-- **The contraction** (propagator line) of two insertions: `δ_{kl} · ½ e^{−it} e^{+is}`. -/
noncomputable def contraction (x y : Fin K × ℝ) : ℂ :=
  if x.1 = y.1 then
    2⁻¹ * Complex.exp (-(Complex.I * (x.2 : ℂ))) * Complex.exp (Complex.I * (y.2 : ℂ))
  else 0

/-- **The pairing sum**, in first-contraction form: the leftmost insertion is contracted with
each later one in turn, and the rest is the pairing sum of the word with the two removed. -/
noncomputable def wickSum : List (Fin K × ℝ) → ℂ
  | [] => 1
  | x :: l => ∑ j : Fin l.length, contraction x l[j] * wickSum (l.eraseIdx j)
termination_by l => l.length
decreasing_by
  simp only [List.length_eraseIdx, List.length_cons]
  split <;> omega

@[simp] theorem wickSum_nil : wickSum (K := K) [] = 1 := by
  rw [wickSum]

theorem wickSum_cons (x : Fin K × ℝ) (l : List (Fin K × ℝ)) :
    wickSum (x :: l) = ∑ j : Fin l.length, contraction x l[j] * wickSum (l.eraseIdx j) := by
  rw [wickSum]

/-! ### The walk band -/

/-- **The walk band, row form**: a word cannot raise a mode by more than its number of
insertions of that mode. -/
theorem timeWord_apply_eq_zero_of_lt [NeZero N] :
    ∀ (l : List (Fin K × ℝ)) (c d : FieldConfig K N) (k : Fin K),
      (c k : ℕ) + (l.map Prod.fst).count k < (d k : ℕ) → timeWord (N := N) l c d = 0
  | [], c, d, k, h => by
    rw [List.map_nil, List.count_nil, add_zero] at h
    rw [timeWord_nil, Matrix.one_apply_ne]
    intro hcd
    rw [hcd] at h
    exact lt_irrefl _ h
  | x :: l, c, d, k, h => by
    rw [timeWord_cons, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases hQ : timeQ (N := N) x.2 x.1 c e = 0
    · rw [hQ, zero_mul]
    · obtain ⟨hagree, hstep⟩ := timeQ_support x.2 x.1 hQ
      rw [List.map_cons, List.count_cons] at h
      have hlt : (e k : ℕ) + (l.map Prod.fst).count k < (d k : ℕ) := by
        by_cases hk : x.1 = k
        · subst hk
          simp only [beq_self_eq_true, if_true] at h
          omega
        · rw [hagree k (Ne.symm hk)] at h
          simp only [beq_iff_eq, hk, if_false, add_zero] at h
          exact h
      rw [timeWord_apply_eq_zero_of_lt l e d k hlt, mul_zero]

/-- **The walk band, column form**: a word cannot lower a mode by more than its number of
insertions of that mode. -/
theorem timeWord_apply_eq_zero_of_lt' [NeZero N] :
    ∀ (l : List (Fin K × ℝ)) (c d : FieldConfig K N) (k : Fin K),
      (d k : ℕ) + (l.map Prod.fst).count k < (c k : ℕ) → timeWord (N := N) l c d = 0
  | [], c, d, k, h => by
    rw [List.map_nil, List.count_nil, add_zero] at h
    rw [timeWord_nil, Matrix.one_apply_ne]
    intro hcd
    rw [hcd] at h
    exact lt_irrefl _ h
  | x :: l, c, d, k, h => by
    rw [timeWord_cons, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases hQ : timeQ (N := N) x.2 x.1 c e = 0
    · rw [hQ, zero_mul]
    · obtain ⟨hagree, hstep⟩ := timeQ_support x.2 x.1 hQ
      rw [List.map_cons, List.count_cons] at h
      have hlt : (d k : ℕ) + (l.map Prod.fst).count k < (e k : ℕ) := by
        by_cases hk : x.1 = k
        · subst hk
          simp only [beq_self_eq_true, if_true] at h
          omega
        · rw [hagree k (Ne.symm hk)] at h
          simp only [beq_iff_eq, hk, if_false, add_zero] at h
          exact h
      rw [timeWord_apply_eq_zero_of_lt' l e d k hlt, mul_zero]

/-- **The defect dies below threshold**: with fewer than `2N − 2` insertions of mode `k` in the
two halves together, the top-level projector of mode `k` sandwiched between them has no vacuum
expectation — one half cannot reach the top level. -/
theorem timeWord_mul_topProj_mul_timeWord_vac [NeZero N] (l₁ l₂ : List (Fin K × ℝ)) (k : Fin K)
    (h : (l₁.map Prod.fst).count k + (l₂.map Prod.fst).count k + 2 < 2 * N) :
    (timeWord (N := N) l₁ * modeOp k (topProj N) * timeWord (N := N) l₂) (vacCfg K N)
      (vacCfg K N)
      = 0 := by
  rw [topProj, modeOp_diagonal, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [Matrix.mul_diagonal]
  by_cases he : (e k : ℕ) = N - 1
  · rcases lt_or_ge ((l₁.map Prod.fst).count k) (N - 1) with h₁ | h₁
    · rw [timeWord_apply_eq_zero_of_lt l₁ _ e k (by rw [vacCfg_apply, Fin.val_zero]; omega),
        zero_mul, zero_mul]
    · rw [timeWord_apply_eq_zero_of_lt' l₂ e _ k (by rw [vacCfg_apply, Fin.val_zero]; omega),
        mul_zero]
  · rw [if_neg he, mul_zero, zero_mul]

/-! ### The first-contraction recursion -/

/-- The count of a mode in a word, split at an insertion. -/
theorem count_map_fst_eq (l : List (Fin K × ℝ)) (j : Fin l.length) (k : Fin K) :
    (l.map Prod.fst).count k
      = ((l.take j).map Prod.fst).count k + (if l[j].1 = k then 1 else 0)
          + ((l.drop (j + 1)).map Prod.fst).count k := by
  conv_lhs => rw [← List.take_append_drop (j : ℕ) l, List.drop_eq_getElem_cons j.isLt]
  rw [List.map_append, List.map_cons, List.count_append, List.count_cons]
  simp only [beq_iff_eq, Fin.getElem_fin]
  omega

/-- ★ **The first-contraction recursion**: below threshold, the vacuum expectation of a word is
the sum over the later insertions of the contraction of the leftmost with it, times the vacuum
expectation of the word with the two removed. -/
theorem timeWord_cons_vac [NeZero N] (x : Fin K × ℝ) (l : List (Fin K × ℝ))
    (hN : ∀ k, ((x :: l).map Prod.fst).count k < 2 * N) :
    timeWord (N := N) (x :: l) (vacCfg K N) (vacCfg K N)
      = ∑ j : Fin l.length,
          contraction x l[j] * timeWord (N := N) (l.eraseIdx j) (vacCfg K N) (vacCfg K N) := by
  obtain ⟨k, t⟩ := x
  -- the vacuum row of the leftmost quadrature is its annihilator row
  have h1 : timeWord (N := N) ((k, t) :: l) (vacCfg K N) (vacCfg K N)
      = ladderPhase t * (modeOp k (annihilation N) * timeWord (N := N) l) (vacCfg K N)
          (vacCfg K N) := by
    have hcre : (modeOp k (creation N) * timeWord (N := N) l) (vacCfg K N) (vacCfg K N) = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun e _ => by rw [modeOp_creation_vac_apply, zero_mul]
    rw [timeWord_cons, timeQ_eq_modeOp, quadratureAt, modeOp_add, modeOp_smul, modeOp_smul,
      add_mul, smul_mul_assoc, smul_mul_assoc, Matrix.add_apply, Matrix.smul_apply,
      Matrix.smul_apply, smul_eq_mul, smul_eq_mul, hcre, mul_zero, add_zero]
  -- the annihilator through the word: only the commutators survive at the vacuum
  have h2 : (modeOp k (annihilation N) * timeWord (N := N) l) (vacCfg K N) (vacCfg K N)
      = ∑ j : Fin l.length,
          (timeWord (N := N) (l.take j)
            * (modeOp k (annihilation N) * timeQ (N := N) (l[j]).2 (l[j]).1
                - timeQ (N := N) (l[j]).2 (l[j]).1 * modeOp k (annihilation N))
            * timeWord (N := N) (l.drop (j + 1))) (vacCfg K N) (vacCfg K N) := by
    have hann : (timeWord (N := N) l * modeOp k (annihilation N)) (vacCfg K N) (vacCfg K N)
        = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun e _ => by rw [modeOp_annihilation_apply_vac, mul_zero]
    have hcomm := mul_map_prod_sub_map_prod_mul (modeOp k (annihilation N))
      (fun x : Fin K × ℝ => timeQ (N := N) x.2 x.1) l
    have h0 := congrArg (fun M : Matrix (FieldConfig K N) (FieldConfig K N) ℂ =>
      M (vacCfg K N) (vacCfg K N)) hcomm
    simp only [Matrix.sub_apply, Matrix.sum_apply] at h0
    rw [show (l.map fun x : Fin K × ℝ => timeQ (N := N) x.2 x.1).prod = timeWord l from rfl,
      hann, sub_zero] at h0
    exact h0
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [modeOp_annihilation_timeQ_commutator]
  by_cases hk : (l[j]).1 = k
  · rw [if_pos hk, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      timeWord_mul_topProj_mul_timeWord_vac (l.take j) (l.drop (j + 1)) k (by
        have := hN k
        rw [List.map_cons, List.count_cons, count_map_fst_eq l j k, if_pos hk] at this
        simp only [beq_self_eq_true, if_true] at this
        omega),
      mul_zero, sub_zero, ← timeWord_eraseIdx, ← mul_assoc, contraction, if_pos hk.symm,
      ladderPhase_mul_ladderPhase_neg]
  · rw [if_neg hk, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, mul_zero, contraction,
      if_neg (fun h => hk h.symm), zero_mul]

/-! ### Wick's theorem, every word, every time -/

/-- ★★ **Wick's theorem at the cutoff, for every word at every time.** Below the threshold
`count k < 2N` for every mode, the vacuum expectation of `Q_{k₁}(t₁) ⋯ Q_{kₘ}(tₘ)` is the pairing
sum `wickSum [(k₁, t₁), …, (kₘ, tₘ)]`. -/
theorem timeWord_vac_eq_wickSum [NeZero N] :
    ∀ l : List (Fin K × ℝ), (∀ k, (l.map Prod.fst).count k < 2 * N) →
      timeWord (N := N) l (vacCfg K N) (vacCfg K N) = wickSum l
  | [], _ => by rw [timeWord_nil, wickSum_nil, Matrix.one_apply_eq]
  | x :: l, hN => by
    rw [timeWord_cons_vac x l hN, wickSum_cons]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [timeWord_vac_eq_wickSum (l.eraseIdx j) fun k =>
      lt_of_le_of_lt (List.Sublist.count_le k
        (((List.eraseIdx_sublist l j).trans (List.sublist_cons_self x l)).map Prod.fst)) (hN k)]
termination_by l => l.length
decreasing_by
  simp only [List.length_eraseIdx, List.length_cons]
  split <;> omega

/-- ★★ The same, with the threshold in CV-23d's form `count k / 2 < N`. -/
theorem timeWord_vac_eq_wickSum' [NeZero N] (l : List (Fin K × ℝ))
    (hN : ∀ k, (l.map Prod.fst).count k / 2 < N) :
    timeWord (N := N) l (vacCfg K N) (vacCfg K N) = wickSum l :=
  timeWord_vac_eq_wickSum l fun k => by have := hN k; omega

/-! ### Consequences -/

/-- The pairing sum of an odd word vanishes. -/
theorem wickSum_eq_zero_of_odd :
    ∀ l : List (Fin K × ℝ), Odd l.length → wickSum l = 0
  | [], h => by simp at h
  | x :: l, h => by
    rw [wickSum_cons]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [wickSum_eq_zero_of_odd (l.eraseIdx j) (by
      have hj := j.isLt
      rw [List.length_eraseIdx, if_pos hj]
      rw [List.length_cons] at h
      rcases h with ⟨m, hm⟩
      exact ⟨m - 1, by omega⟩), mul_zero]
termination_by l => l.length
decreasing_by
  simp only [List.length_eraseIdx, List.length_cons]
  split <;> omega

/-- Below threshold, an odd word has no vacuum expectation. -/
theorem timeWord_vac_eq_zero_of_odd [NeZero N] (l : List (Fin K × ℝ))
    (hN : ∀ k, (l.map Prod.fst).count k < 2 * N) (hl : Odd l.length) :
    timeWord (N := N) l (vacCfg K N) (vacCfg K N) = 0 := by
  rw [timeWord_vac_eq_wickSum l hN, wickSum_eq_zero_of_odd l hl]

/-- Two insertions: the pairing sum is the one contraction. -/
theorem wickSum_pair (x y : Fin K × ℝ) : wickSum [x, y] = contraction x y := by
  simp [wickSum_cons]

/-- Four insertions: the three pairings. -/
theorem wickSum_four (a b c d : Fin K × ℝ) :
    wickSum [a, b, c, d]
      = contraction a b * contraction c d + contraction a c * contraction b d
        + contraction a d * contraction b c := by
  rw [wickSum_cons]
  show ∑ j : Fin 3, _ = _
  simp [Fin.sum_univ_three, wickSum_pair]

/-- At stroboscopic times the contraction is CV-23b's kernel. -/
theorem contraction_natMul (τ : ℝ) (n m : ℕ) (k l : Fin K) :
    contraction (k, (n : ℝ) * τ) (l, (m : ℝ) * τ) = if k = l then twoPointKernel τ n m else 0 :=
  rfl

/-- The stroboscopic power of the free step is the free step at the multiplied time. -/
theorem freeFieldU_pow_eq (τ : ℝ) (n : ℕ) :
    freeFieldU K N τ ^ n = freeFieldU K N ((n : ℝ) * τ) := by
  rw [freeFieldU_pow, freeFieldU]
  congr 1
  funext c
  ring

/-- ★ CV-23b's time-separated four-point function is the pairing sum at stroboscopic times. -/
theorem timeFourPoint_eq_wickSum [NeZero N] (hN2 : 2 < N) (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    (k₁ k₂ k₃ k₄ : Fin K) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k₁ k₂ k₃ k₄
      = wickSum [(k₁, (n₁ : ℝ) * τ), (k₂, (n₂ : ℝ) * τ), (k₃, (n₃ : ℝ) * τ),
          (k₄, (n₄ : ℝ) * τ)] := by
  have key := timeWord_vac_eq_wickSum (N := N)
    [(k₁, (n₁ : ℝ) * τ), (k₂, (n₂ : ℝ) * τ), (k₃, (n₃ : ℝ) * τ), (k₄, (n₄ : ℝ) * τ)]
    (fun k => lt_of_le_of_lt List.count_le_length (by simp; omega))
  rw [← key, timeFourPoint, timeWord, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil,
    mul_one, timeQ, timeQ, timeQ, timeQ, ← freeFieldU_pow_eq, ← freeFieldU_pow_eq,
    ← freeFieldU_pow_eq, ← freeFieldU_pow_eq, Matrix.mul_assoc, Matrix.mul_assoc]

/-- The free step at time `0` is the identity. -/
theorem freeFieldU_zero : freeFieldU K N 0 = 1 := by
  apply Subtype.ext
  rw [freeFieldU, phaseDiagU_val]
  show Matrix.diagonal _ = (1 : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
  rw [← Matrix.diagonal_one]
  congr 1
  funext c
  simp

/-- At time `0` the word is CV-23d's equal-time word. -/
theorem timeWord_map_zero (l : List (Fin K)) :
    timeWord (N := N) (l.map fun k => (k, (0 : ℝ))) = wordOp l := by
  rw [timeWord, wordOp, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  show timeQ (N := N) 0 k = modeOp k (Q N)
  rw [timeQ, freeFieldU_zero, heisenberg_one]

/-- ★ At equal time the pairing sum is CV-23d's Gaussian moment product: each mode contributes
`(count − 1)‼ / 2^{count/2}`, the number of its pairings times the kernel `½` per pair. -/
theorem wickSum_map_zero [NeZero N] (l : List (Fin K)) (hN : ∀ k, l.count k / 2 < N) :
    wickSum (l.map fun k => (k, (0 : ℝ))) = ∏ k : Fin K, wickMoment (l.count k) := by
  rw [← timeWord_vac_eq_wickSum' _ (fun k => by
      rw [List.map_map, show Prod.fst ∘ (fun k : Fin K => (k, (0 : ℝ))) = id from rfl,
        List.map_id]
      exact hN k),
    timeWord_map_zero, wordOp_vac_eq_prod_wickMoment l hN]

/-! ### The second-order vacuum diagrams of every monomial vertex -/

/-- Heisenberg conjugation fixes the identity. -/
theorem heisenberg_one_op (U : Matrix.unitaryGroup (FieldConfig K N) ℂ) :
    heisenberg U (1 : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) = 1 := by
  rw [heisenberg, Matrix.mul_one]
  exact Matrix.mem_unitaryGroup_iff'.mp U.property

/-- Heisenberg conjugation distributes over a product of operators. -/
theorem heisenberg_list_prod (U : Matrix.unitaryGroup (FieldConfig K N) ℂ) :
    ∀ l : List (Matrix (FieldConfig K N) (FieldConfig K N) ℂ),
      heisenberg U l.prod = (l.map (heisenberg U)).prod
  | [] => by rw [List.prod_nil, List.map_nil, List.prod_nil, heisenberg_one_op]
  | A :: l => by
    rw [List.prod_cons, List.map_cons, List.prod_cons, heisenberg_mul_op,
      heisenberg_list_prod U l]

/-- The free Heisenberg picture of an equal-time word is the word at that time. -/
theorem heisenberg_wordOp (τ : ℝ) (w : List (Fin K)) :
    heisenberg (freeFieldU K N τ) (wordOp (N := N) w) = timeWord (w.map fun k => (k, τ)) := by
  rw [wordOp, heisenberg_list_prod, timeWord, List.map_map, List.map_map]
  rfl

/-- ★★ **The second-order vacuum diagrams of every monomial vertex.** For `V = Q_{k₁} ⋯ Q_{kₘ}`
with fewer than `N` insertions of every mode, the two-vertex vacuum amplitude of CV-27 is the
ordered double integral of the pairing sum of the word with its copy at the time difference
`s₁ − s₂` — every pairing of the `2m` legs of the two vertices, each a product of `m` propagator
lines. -/
theorem dysonTerm_two_vac_wordOp [NeZero N] (lam : ℝ) (w : List (Fin K))
    (hw : ∀ k, w.count k < N) (t : ℝ) :
    dysonTerm ((-Complex.I) • fieldHamiltonian K N) ((-Complex.I) • (lam • wordOp (N := N) w))
        2 t (vacCfg K N) (vacCfg K N)
      = Complex.exp (t * (-Complex.I * ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)))
          * ((-Complex.I * lam) ^ 2 * ∫ s₂ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s₂,
              wickSum ((w.map fun k => (k, (0 : ℝ))) ++ w.map fun k => (k, s₁ - s₂))) := by
  rw [dysonTerm_two_vac]
  congr 2
  refine intervalIntegral.integral_congr fun s₂ _ => ?_
  refine intervalIntegral.integral_congr fun s₁ _ => ?_
  rw [heisenberg_wordOp, ← timeWord_map_zero, ← timeWord_append, timeWord_vac_eq_wickSum]
  intro k
  rw [List.map_append, List.count_append, List.map_map, List.map_map,
    show Prod.fst ∘ (fun k : Fin K => (k, (0 : ℝ))) = id from rfl,
    show Prod.fst ∘ (fun k : Fin K => (k, s₁ - s₂)) = id from rfl, List.map_id]
  have := hw k
  omega

/-! ### The matching-indexed form -/

/-- ★★ **The pairing sum is the sum over perfect matchings.** `wickSum l` is `Fin.pairingSum`
of the contraction on the positions of `l`: the sum over fixed-point-free involutions `σ` of
`Fin l.length` of the product over the pairs `i < σ i` of `contraction lᵢ l_{σ i}`. -/
theorem wickSum_eq_pairingSum :
    ∀ l : List (Fin K × ℝ),
      wickSum l = Fin.pairingSum fun i i' : Fin l.length => contraction l[i] l[i']
  | [] => by rw [wickSum_nil, Fin.pairingSum_zero]
  | [x] => by
    rw [wickSum_cons]
    show ∑ j : Fin 0, _ = _
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact (Fin.pairingSum_one _).symm
  | x :: y :: l => by
    rw [wickSum_cons]
    show _ = Fin.pairingSum (m := l.length + 2) _
    rw [Fin.pairingSum_succ_succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlen : ((y :: l).eraseIdx j).length = l.length := by
      rw [List.length_eraseIdx, if_pos j.isLt]
      rfl
    have hget : ∀ i : Fin ((y :: l).eraseIdx j).length,
        ((y :: l).eraseIdx j)[(i : ℕ)] = (x :: y :: l)[(Fin.emb j (Fin.cast hlen i) : ℕ)] := by
      intro i
      rw [List.getElem_eraseIdx]
      split_ifs with hij
      · have h := Fin.succAbove_of_castSucc_lt j (Fin.cast hlen i)
          (by rw [Fin.lt_def]; simpa using hij)
        simp [Fin.emb, h]
      · have h := Fin.succAbove_of_le_castSucc j (Fin.cast hlen i)
          (by rw [Fin.le_def]; simpa using hij)
        simp [Fin.emb, h]
    rw [wickSum_eq_pairingSum ((y :: l).eraseIdx j),
      ← Fin.pairingSum_cast hlen fun a b =>
        contraction (x :: y :: l)[Fin.emb j a] (x :: y :: l)[Fin.emb j b]]
    simp only [Fin.getElem_fin, hget, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ]
termination_by l => l.length
decreasing_by
  simp only [List.length_eraseIdx, List.length_cons]
  split <;> omega

/-- ★★ **Wick's theorem at the cutoff, matching-indexed.** Below threshold, the vacuum expectation
of `Q_{k₁}(t₁) ⋯ Q_{kₘ}(tₘ)` is the sum over the perfect matchings `σ` of its `m` insertions of
the product over the pairs `i < σ i` of the propagator lines `contraction (kᵢ, tᵢ) (k_{σ i}, t_{σ i})`. -/
theorem timeWord_vac_eq_pairingSum [NeZero N] (l : List (Fin K × ℝ))
    (hN : ∀ k, (l.map Prod.fst).count k / 2 < N) :
    timeWord (N := N) l (vacCfg K N) (vacCfg K N)
      = Fin.pairingSum fun i i' : Fin l.length => contraction l[i] l[i'] := by
  rw [timeWord_vac_eq_wickSum' l hN, wickSum_eq_pairingSum]

end CSD.CV

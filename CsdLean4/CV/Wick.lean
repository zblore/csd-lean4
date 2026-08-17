/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ThermalPropagator

/-!
# CV-23b: the time-separated four-point function — Wick's theorem with the phases on

**Category:** CV (continuous variables — the multi-mode field).

CV-22/CV-23a proved Wick's four-point theorem at equal times (`eqFourPoint_wick`);
CV-13 computed the two-point function with one factor evolved (`freeTwoPoint_eq`).
This module joins them: each quadrature at its **own** Heisenberg period, and the
four-point function equal to the pairing sum over stroboscopic kernels.

* `twoPointKernel τ n m` — the stroboscopic kernel `K(n,m) = ½·e^{-inτ}·e^{+imτ}`,
  kept in two-factor form so ℕ-subtraction never appears. `twoPointKernel_self`
  (`= ½`, the equal-time vacuum fluctuation) and `twoPointKernel_zero_right`
  (the CV-13 propagator value at right period `0`).
* `timeTwoPoint τ n m k l` — `⟨vac∣Q_k(n)·Q_l(m)∣vac⟩`, both factors evolved.
  ★ `timeTwoPoint_eq` — the **two-time propagator**: `= δ_{kl}·K(n,m)`, diagonal in
  the mode index; `timeTwoPoint_zero_right` recovers `freeTwoPoint` at the
  definition level.
* `timeFourPoint τ n₁ n₂ n₃ n₄ k₁ k₂ k₃ k₄` —
  `⟨vac∣Q_{k₁}(n₁)·Q_{k₂}(n₂)·Q_{k₃}(n₃)·Q_{k₄}(n₄)∣vac⟩`, resolved by coincidence
  pattern exactly as the equal-time table: a singleton mode kills it
  (`timeFourPoint_single₁`–`₄`), the two-pair patterns give the kernel product of
  the paired **times** (`_pair`/`_alt`/`_outer` — the arrangement now carries
  content the equal-time table could not see: which times meet in a kernel is
  decided by the pairing), and the all-equal pattern is the three-pairing sum
  (★ `timeFourPoint_same`, `2 < N`).
* ★★ `timeFourPoint_wick` — **Wick's four-point theorem at distinct times**: above
  the truncation threshold `2 < N`,

    `⟨Q_{k₁}(n₁)Q_{k₂}(n₂)Q_{k₃}(n₃)Q_{k₄}(n₄)⟩
       = δ_{k₁k₂}δ_{k₃k₄}·K₁₂K₃₄ + δ_{k₁k₃}δ_{k₂k₄}·K₁₃K₂₄ + δ_{k₁k₄}δ_{k₂k₃}·K₁₄K₂₃`,

  one formula over every mode pattern, with `K_{ij} = twoPointKernel τ n_i n_j`.
  All periods `0` (or the formula at equal periods, via `twoPointKernel_self`)
  recover CV-23a: `timeFourPoint_zero`.
* **The CV-23c gate — the six-point pass** (equal time): ★ `modeOpQ_six_vac` — the
  sixth moment `⟨vac∣Q_k⁶∣vac⟩ = 15/8 = 5!!·(½)³` for `3 < N`, via the `Q³` column
  at the vacuum (`modeOpQ_cube_apply_vac` — the plan's `‖Q³e₀‖²` anchor, computed
  in walk-collapse form); `modeOpQ_four_two_vac` — the mixed pattern
  `⟨Q_k⁴·Q_l²⟩ = 3/8` by clustering into `eqFourPoint_same`. At `N = 3` the
  level-3 walk dies and the all-equal value is `9/8`, not `15/8` — the threshold
  honesty one rung up, guarded by `3 < N`. The idiom scaled by exactly one rung
  (one configuration, one entry-ladder level, one reachability lemma,
  `fin_cases`-free): **the gate passes**.

**Why Wick survives truncation exactly** (the load-bearing identity): the all-equal
pattern is one level-2 walk `0→1→2→1→0` with amplitude `½·e^{-i(t₁+t₂−t₃−t₄)}`, and
the two cross-pairings `K₁₃K₂₄` and `K₁₄K₂₃` are **each** `¼·e^{-i(t₁+t₂−t₃−t₄)}` —
their sum IS the walk term. At `N = 2` the walk dies and only `K₁₂K₃₄` survives:
the `2 < N` hypothesis is load-bearing exactly where `eqFourPoint_same` says.

⚠️ Honest scope: the free (mode-diagonal) drive only, matching `freeTwoPoint`'s
scope; interacting corrections are priced by the CV-9/CV-12 ladder
(`twoPoint_interacting_dist_le`) and not restated. No continuum limit
(`ApproxCCR.no_exact_finite_ccr` stands). The general `2n`-point Wick theorem is
**not claimed**: the CV-23c gate below lands the six-point pass (which un-gates that
work), not the theorem itself. The relativistic reading is the CV-13 substitution
(`relFieldHamiltonian`, spacing `ω(m, p)`), recorded not restated.

## References

`specs/eft-stage7-plan.md` (row CV-23b — the construction notes this module
executes: the two-factor kernel, the cross-pairing exponent identity, the brick
list); `specs/BACKLOG.md` (Q21); `specs/future-work.md` (row CV-23);
`CV/Propagator.lean` (`eqFourPoint` and its coincidence table, `eqFourPoint_wick`,
`freeTwoPoint_eq`, `diag_entry_mul_of_disjointSupport`, the `Q` entry ladder);
`CV/ThermalPropagator.lean` (`heisenberg_freeFieldU_pow_apply`);
`CV/ModeLocality.lean` (`commute_of_disjointSupport`, `modeOp_supportedOn`);
`CV/DynamicalLocality.lean` (`heisenberg_freeFieldU_pow_supportedOn`);
`CONVENTIONS.md` §8.3b (the pattern lemmas feed the one packaged capstone).
-/

@[expose] public section

open Matrix

namespace CSD.CV

variable {K N : ℕ}

/-! ### The stroboscopic kernel -/

/-- **The stroboscopic two-point kernel** `K(n,m) = ½·e^{-inτ}·e^{+imτ}`, the value of
the two-time propagator on the mode diagonal. Kept in two-factor form (never
`e^{-i(n-m)τ}`) so ℕ-subtraction does not appear. -/
noncomputable def twoPointKernel (τ : ℝ) (n m : ℕ) : ℂ :=
  2⁻¹ * Complex.exp (-(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)))
    * Complex.exp (Complex.I * (((m : ℝ) * τ : ℝ) : ℂ))

/-- Equal periods: the kernel is the equal-time vacuum fluctuation `½`. -/
lemma twoPointKernel_self (τ : ℝ) (n : ℕ) : twoPointKernel τ n n = (2 : ℂ)⁻¹ := by
  rw [twoPointKernel, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    mul_one]

/-- Right period `0`: the kernel is CV-13's propagator value `½·e^{-inτ}`
(`freeTwoPoint_eq`'s diagonal entry). -/
lemma twoPointKernel_zero_right (τ : ℝ) (n : ℕ) :
    twoPointKernel τ n 0
      = (2 : ℂ)⁻¹ * Complex.exp (-(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ))) := by
  rw [twoPointKernel]
  norm_num

/-- `(√2)⁻¹·(√2)⁻¹ = 2⁻¹` in `ℂ` — the squared hop amplitude. -/
lemma inv_sqrt_two_mul_self :
    (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-! ### The energy step to the two-quantum level -/

/-- The second quantum also costs one unit of free energy:
`E(exc2 l) − E(exc l) = 1`. -/
lemma fieldEnergy_exc2Cfg_sub [NeZero N] (hN2 : 2 < N) (hN : 1 < N) (l : Fin K) :
    fieldEnergy (exc2Cfg (K := K) hN2 l) - fieldEnergy (excCfg (K := K) hN l) = 1 := by
  classical
  rw [show fieldEnergy (exc2Cfg (K := K) hN2 l)
      = ∑ k, oscEnergy ((exc2Cfg (K := K) hN2 l) k : ℕ) from rfl,
    show fieldEnergy (excCfg (K := K) hN l)
      = ∑ k, oscEnergy ((excCfg (K := K) hN l) k : ℕ) from rfl,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single l]
  · rw [exc2Cfg_self, excCfg_self]
    show oscEnergy 2 - oscEnergy 1 = 1
    rw [oscEnergy, oscEnergy]
    norm_num
  · intro j _ hj
    rw [exc2Cfg_of_ne hN2 hj, excCfg_of_ne hN hj, sub_self]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-! ### The evolved quadrature's hop entries

The free evolution decorates each `modeOp k (Q N)` entry with the phase
`e^{inτ(E_c − E_d)}` (`heisenberg_freeFieldU_pow_apply`); on the four hops the walk
uses, the energy difference is `±1` and the phase is `e^{∓inτ}`. -/

/-- The evolved quadrature reaches the vacuum only from the one-quantum
configuration: the phase decoration does not move the support (column form). -/
lemma evolvedQ_apply_vac [NeZero N] (hN : 1 < N) (τ : ℝ) (n : ℕ) (k : Fin K)
    {e : FieldConfig K N} (he : e ≠ excCfg hN k) :
    heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) e (vacCfg K N) = 0 := by
  rw [heisenberg_freeFieldU_pow_apply, modeOp_Q_apply_vac hN k e he, mul_zero]

/-- Row form: from the vacuum, the evolved quadrature reaches only the one-quantum
configuration. -/
lemma evolvedQ_vac_apply [NeZero N] (hN : 1 < N) (τ : ℝ) (n : ℕ) (k : Fin K)
    {e : FieldConfig K N} (he : e ≠ excCfg hN k) :
    heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) (vacCfg K N) e = 0 := by
  rw [heisenberg_freeFieldU_pow_apply, modeOpQ_symm, modeOp_Q_apply_vac hN k e he,
    mul_zero]

/-- The up-hop from the vacuum: `Q_k(n)(vac, exc) = e^{-inτ}·(√2)⁻¹`. -/
lemma evolvedQ_vac_exc [NeZero N] (hN : 1 < N) (τ : ℝ) (n : ℕ) (k : Fin K) :
    heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) (vacCfg K N) (excCfg hN k)
      = Complex.exp (-(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)))
        * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  rw [heisenberg_freeFieldU_pow_apply,
    modeOp_apply_of_agree k (Q N) (fun j hj => (excCfg_agree hN k hj).symm),
    vacCfg_apply, excCfg_self, Q_zero_one hN]
  have hE : ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)
      - ((fieldEnergy (excCfg (K := K) hN k) : ℝ) : ℂ) = -1 := by
    rw [← Complex.ofReal_sub,
      show fieldEnergy (vacCfg K N) - fieldEnergy (excCfg (K := K) hN k) = -1 from by
        have h := fieldEnergy_excCfg_sub (K := K) hN k
        linarith]
    norm_num
  rw [hE, show Complex.I * (((n : ℝ) * τ : ℝ) : ℂ) * (-1)
      = -(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)) from by ring]

/-- The down-hop to the vacuum: `Q_k(n)(exc, vac) = e^{+inτ}·(√2)⁻¹`. -/
lemma evolvedQ_exc_vac [NeZero N] (hN : 1 < N) (τ : ℝ) (n : ℕ) (k : Fin K) :
    heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) (excCfg hN k) (vacCfg K N)
      = Complex.exp (Complex.I * (((n : ℝ) * τ : ℝ) : ℂ))
        * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  rw [heisenberg_freeFieldU_pow_apply,
    modeOp_apply_of_agree k (Q N) (fun j hj => excCfg_agree hN k hj),
    excCfg_self, vacCfg_apply, Q_one_zero hN]
  have hE : ((fieldEnergy (excCfg (K := K) hN k) : ℝ) : ℂ)
      - ((fieldEnergy (vacCfg K N) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sub, fieldEnergy_excCfg_sub (K := K) hN k]
    norm_num
  rw [hE, mul_one]

/-- The up-hop into the two-quantum level: `Q_k(n)(exc, exc2) = e^{-inτ}` (the ladder
amplitude `√2/√2 = 1`). -/
lemma evolvedQ_exc_exc2 [NeZero N] (hN2 : 2 < N) (hN : 1 < N) (τ : ℝ) (n : ℕ)
    (k : Fin K) :
    heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) (excCfg hN k) (exc2Cfg hN2 k)
      = Complex.exp (-(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ))) := by
  rw [heisenberg_freeFieldU_pow_apply,
    modeOp_apply_of_agree k (Q N) (fun j hj => by
      rw [excCfg_of_ne hN hj, exc2Cfg_of_ne hN2 hj]),
    excCfg_self, exc2Cfg_self, Q_one_two hN2]
  have hE : ((fieldEnergy (excCfg (K := K) hN k) : ℝ) : ℂ)
      - ((fieldEnergy (exc2Cfg (K := K) hN2 k) : ℝ) : ℂ) = -1 := by
    rw [← Complex.ofReal_sub,
      show fieldEnergy (excCfg (K := K) hN k)
          - fieldEnergy (exc2Cfg (K := K) hN2 k) = -1 from by
        have h := fieldEnergy_exc2Cfg_sub (K := K) hN2 hN k
        linarith]
    norm_num
  rw [hE, show Complex.I * (((n : ℝ) * τ : ℝ) : ℂ) * (-1)
      = -(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)) from by ring, mul_one]

/-- The down-hop from the two-quantum level: `Q_k(n)(exc2, exc) = e^{+inτ}`. -/
lemma evolvedQ_exc2_exc [NeZero N] (hN2 : 2 < N) (hN : 1 < N) (τ : ℝ) (n : ℕ)
    (k : Fin K) :
    heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) (exc2Cfg hN2 k) (excCfg hN k)
      = Complex.exp (Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)) := by
  rw [heisenberg_freeFieldU_pow_apply,
    modeOp_apply_of_agree k (Q N) (fun j hj => by
      rw [exc2Cfg_of_ne hN2 hj, excCfg_of_ne hN hj]),
    exc2Cfg_self, excCfg_self, Q_two_one hN2]
  have hE : ((fieldEnergy (exc2Cfg (K := K) hN2 k) : ℝ) : ℂ)
      - ((fieldEnergy (excCfg (K := K) hN k) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sub, fieldEnergy_exc2Cfg_sub (K := K) hN2 hN k]
    norm_num
  rw [hE, mul_one, mul_one]

/-! ### The evolved pair: entries of `Q_k(n)·Q_k(m)` at the vacuum -/

/-- The evolved pair's vacuum diagonal IS the kernel:
`(Q_k(n)·Q_k(m))(vac, vac) = K(n,m)` — one up-hop, one down-hop. -/
lemma evolvedPair_vac_vac [NeZero N] (hN : 1 < N) (τ : ℝ) (n m : ℕ) (k : Fin K) :
    (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N))
        * heisenberg (freeFieldU K N τ ^ m) (modeOp k (Q N)))
      (vacCfg K N) (vacCfg K N) = twoPointKernel τ n m := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (excCfg hN k)]
  · rw [evolvedQ_vac_exc hN τ n k, evolvedQ_exc_vac hN τ m k, twoPointKernel]
    linear_combination (Complex.exp (-(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)))
      * Complex.exp (Complex.I * (((m : ℝ) * τ : ℝ) : ℂ))) * inv_sqrt_two_mul_self
  · intro c _ hc
    rw [evolvedQ_vac_apply hN τ n k hc, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Distinct modes have no vacuum two-point correlation, whatever the periods:
clustering plus the quadrature's missing vacuum diagonal. -/
lemma evolvedPair_vac_vac_offdiag [NeZero N] (τ : ℝ) (n m : ℕ) {k l : Fin K}
    (hkl : k ≠ l) :
    (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N))
        * heisenberg (freeFieldU K N τ ^ m) (modeOp l (Q N)))
      (vacCfg K N) (vacCfg K N) = 0 := by
  classical
  rw [diag_entry_mul_of_disjointSupport (by simpa using hkl)
      (heisenberg_freeFieldU_pow_supportedOn τ n (modeOp_supportedOn k (Q N)))
      (heisenberg_freeFieldU_pow_supportedOn τ m (modeOp_supportedOn l (Q N))),
    heisenberg_freeFieldU_pow_apply,
    modeOp_apply_of_agree k (Q N) (fun j _ => rfl), vacCfg_apply, Q_zero_zero,
    mul_zero, zero_mul]

/-- The evolved pair's column at the vacuum is supported on the vacuum and the
two-quantum configuration — the only three-hop walks from level 1 end at levels
0 and 2. -/
lemma evolvedPair_apply_vac_of_ne [NeZero N] (hN2 : 2 < N) (hN : 1 < N) (τ : ℝ)
    (n m : ℕ) (k : Fin K) {e : FieldConfig K N} (h0 : e ≠ vacCfg K N)
    (h2 : e ≠ exc2Cfg hN2 k) :
    (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N))
        * heisenberg (freeFieldU K N τ ^ m) (modeOp k (Q N)))
      e (vacCfg K N) = 0 := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (excCfg hN k)]
  · rw [heisenberg_freeFieldU_pow_apply, modeOp_Q_apply_exc hN2 k h0 h2, mul_zero,
      zero_mul]
  · intro c _ hc
    rw [evolvedQ_apply_vac hN τ m k hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The evolved pair's entry into the two-quantum configuration:
`(Q_k(n)·Q_k(m))(vac, exc2) = (√2)⁻¹·e^{-inτ}·e^{-imτ}` — two up-hops. -/
lemma evolvedPair_vac_exc2 [NeZero N] (hN2 : 2 < N) (hN : 1 < N) (τ : ℝ) (n m : ℕ)
    (k : Fin K) :
    (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N))
        * heisenberg (freeFieldU K N τ ^ m) (modeOp k (Q N)))
      (vacCfg K N) (exc2Cfg hN2 k)
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (Complex.exp (-(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)))
          * Complex.exp (-(Complex.I * (((m : ℝ) * τ : ℝ) : ℂ)))) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (excCfg hN k)]
  · rw [evolvedQ_vac_exc hN τ n k, evolvedQ_exc_exc2 hN2 hN τ m k]
    ring
  · intro c _ hc
    rw [evolvedQ_vac_apply hN τ n k hc, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The evolved pair's return from the two-quantum configuration:
`(Q_k(n)·Q_k(m))(exc2, vac) = (√2)⁻¹·e^{+inτ}·e^{+imτ}` — two down-hops. -/
lemma evolvedPair_exc2_vac [NeZero N] (hN2 : 2 < N) (hN : 1 < N) (τ : ℝ) (n m : ℕ)
    (k : Fin K) :
    (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N))
        * heisenberg (freeFieldU K N τ ^ m) (modeOp k (Q N)))
      (exc2Cfg hN2 k) (vacCfg K N)
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        * (Complex.exp (Complex.I * (((n : ℝ) * τ : ℝ) : ℂ))
          * Complex.exp (Complex.I * (((m : ℝ) * τ : ℝ) : ℂ))) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (excCfg hN k)]
  · rw [evolvedQ_exc2_exc hN2 hN τ n k, evolvedQ_exc_vac hN τ m k]
    ring
  · intro c _ hc
    rw [evolvedQ_apply_vac hN τ m k hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The two-time propagator -/

/-- **The time-separated two-point function** `⟨vac∣Q_k(n)·Q_l(m)∣vac⟩`: both
quadratures in the Heisenberg picture, each at its own period. -/
noncomputable def timeTwoPoint [NeZero N] (τ : ℝ) (n m : ℕ) (k l : Fin K) : ℂ :=
  (heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N))
      * heisenberg (freeFieldU K N τ ^ m) (modeOp l (Q N)))
    (vacCfg K N) (vacCfg K N)

/-- ★ **The two-time propagator**: `⟨vac∣Q_k(n)·Q_l(m)∣vac⟩ = δ_{kl}·K(n,m)` —
diagonal in the mode index, the kernel at the two periods on the diagonal. -/
theorem timeTwoPoint_eq [NeZero N] (hN : 1 < N) (τ : ℝ) (n m : ℕ) (k l : Fin K) :
    timeTwoPoint (K := K) (N := N) τ n m k l
      = if k = l then twoPointKernel τ n m else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, timeTwoPoint]
    exact evolvedPair_vac_vac hN τ n m k
  · rw [if_neg hkl, timeTwoPoint]
    exact evolvedPair_vac_vac_offdiag τ n m hkl

/-- Right period `0` recovers CV-13's `freeTwoPoint` at the definition level. -/
theorem timeTwoPoint_zero_right [NeZero N] (τ : ℝ) (n : ℕ) (k l : Fin K) :
    timeTwoPoint (K := K) (N := N) τ n 0 k l = freeTwoPoint (K := K) (N := N) τ n k l := by
  rw [timeTwoPoint, freeTwoPoint, pow_zero, heisenberg_one]

/-! ### The time-separated four-point function -/

/-- **The time-separated four-point function**
`⟨vac∣Q_{k₁}(n₁)·Q_{k₂}(n₂)·Q_{k₃}(n₃)·Q_{k₄}(n₄)∣vac⟩` — every quadrature at its
own Heisenberg period under the free stroboscopic dynamics. -/
noncomputable def timeFourPoint [NeZero N] (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    (k₁ k₂ k₃ k₄ : Fin K) : ℂ :=
  (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k₁ (Q N))
      * heisenberg (freeFieldU K N τ ^ n₂) (modeOp k₂ (Q N))
      * heisenberg (freeFieldU K N τ ^ n₃) (modeOp k₃ (Q N))
      * heisenberg (freeFieldU K N τ ^ n₄) (modeOp k₄ (Q N)))
    (vacCfg K N) (vacCfg K N)

/-- All periods `0` recover the equal-time four-point function (CV-22/CV-23a). -/
theorem timeFourPoint_zero [NeZero N] (τ : ℝ) (k₁ k₂ k₃ k₄ : Fin K) :
    timeFourPoint (N := N) τ 0 0 0 0 k₁ k₂ k₃ k₄ = eqFourPoint (N := N) k₁ k₂ k₃ k₄ := by
  rw [timeFourPoint, eqFourPoint, pow_zero, heisenberg_one, heisenberg_one,
    heisenberg_one, heisenberg_one]

/-- Evolved quadratures at distinct modes commute, whatever their periods — the
Haag–Kastler locality of `commute_modeOp`, transported through the free evolution
(`heisenberg_freeFieldU_pow_supportedOn`). -/
lemma commute_evolvedQ [NeZero N] (τ : ℝ) (n m : ℕ) {k l : Fin K} (hkl : k ≠ l) :
    heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N))
        * heisenberg (freeFieldU K N τ ^ m) (modeOp l (Q N))
      = heisenberg (freeFieldU K N τ ^ m) (modeOp l (Q N))
        * heisenberg (freeFieldU K N τ ^ n) (modeOp k (Q N)) := by
  classical
  exact commute_of_disjointSupport (by simpa using hkl)
    (heisenberg_freeFieldU_pow_supportedOn τ n (modeOp_supportedOn k (Q N)))
    (heisenberg_freeFieldU_pow_supportedOn τ m (modeOp_supportedOn l (Q N)))

/-- A mode appearing **once** (first position) kills the time-separated expectation:
the evolved quadrature has no vacuum diagonal, and clustering isolates it. -/
theorem timeFourPoint_single₁ [NeZero N] (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    {k₁ k₂ k₃ k₄ : Fin K} (h1 : k₁ ≠ k₂) (h2 : k₁ ≠ k₃) (h3 : k₁ ≠ k₄) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k₁ k₂ k₃ k₄ = 0 := by
  classical
  have hsupp : SupportedOn ({k₂} ∪ {k₃} ∪ {k₄} : Finset (Fin K))
      (heisenberg (freeFieldU K N τ ^ n₂) (modeOp k₂ (Q N))
        * heisenberg (freeFieldU K N τ ^ n₃) (modeOp k₃ (Q N))
        * heisenberg (freeFieldU K N τ ^ n₄) (modeOp k₄ (Q N))) := by
    refine SupportedOn.mul (SupportedOn.mul ?_ ?_) ?_
    · exact SupportedOn.mono
        (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
        (heisenberg_freeFieldU_pow_supportedOn τ n₂ (modeOp_supportedOn k₂ (Q N)))
    · exact SupportedOn.mono
        (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)
        (heisenberg_freeFieldU_pow_supportedOn τ n₃ (modeOp_supportedOn k₃ (Q N)))
    · exact SupportedOn.mono Finset.subset_union_right
        (heisenberg_freeFieldU_pow_supportedOn τ n₄ (modeOp_supportedOn k₄ (Q N)))
  have hdisj : Disjoint ({k₁} : Finset (Fin K)) ({k₂} ∪ {k₃} ∪ {k₄}) := by
    simp only [Finset.disjoint_left, Finset.mem_singleton, Finset.mem_union]
    rintro x rfl
    simp [h1, h2, h3]
  rw [timeFourPoint,
    mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k₁ (Q N))
      * heisenberg (freeFieldU K N τ ^ n₂) (modeOp k₂ (Q N))),
    mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k₁ (Q N))),
    diag_entry_mul_of_disjointSupport hdisj
      (heisenberg_freeFieldU_pow_supportedOn τ n₁ (modeOp_supportedOn k₁ (Q N)))
      (by rw [← mul_assoc]; exact hsupp),
    heisenberg_freeFieldU_pow_apply,
    modeOp_apply_of_agree k₁ (Q N) (fun j _ => rfl), vacCfg_apply, Q_zero_zero,
    mul_zero, zero_mul]

/-- A mode appearing once (second position) kills the expectation. -/
theorem timeFourPoint_single₂ [NeZero N] (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    {k₁ k₂ k₃ k₄ : Fin K} (h1 : k₂ ≠ k₁) (h2 : k₂ ≠ k₃) (h3 : k₂ ≠ k₄) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k₁ k₂ k₃ k₄ = 0 := by
  have h := timeFourPoint_single₁ (N := N) τ n₂ n₁ n₃ n₄ h1 h2 h3
  rw [timeFourPoint] at h ⊢
  rw [commute_evolvedQ τ n₂ n₁ h1] at h
  exact h

/-- A mode appearing once (third position) kills the expectation. -/
theorem timeFourPoint_single₃ [NeZero N] (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    {k₁ k₂ k₃ k₄ : Fin K} (h1 : k₃ ≠ k₁) (h2 : k₃ ≠ k₂) (h3 : k₃ ≠ k₄) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k₁ k₂ k₃ k₄ = 0 := by
  have h := timeFourPoint_single₁ (N := N) τ n₃ n₁ n₂ n₄ h1 h2 h3
  rw [timeFourPoint] at h ⊢
  rw [commute_evolvedQ τ n₃ n₁ h1,
    mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k₁ (Q N))),
    commute_evolvedQ τ n₃ n₂ h2, ← mul_assoc] at h
  exact h

/-- A mode appearing once (fourth position) kills the expectation. -/
theorem timeFourPoint_single₄ [NeZero N] (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    {k₁ k₂ k₃ k₄ : Fin K} (h1 : k₄ ≠ k₁) (h2 : k₄ ≠ k₂) (h3 : k₄ ≠ k₃) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k₁ k₂ k₃ k₄ = 0 := by
  have h := timeFourPoint_single₁ (N := N) τ n₄ n₁ n₂ n₃ h1 h2 h3
  rw [timeFourPoint] at h ⊢
  rw [commute_evolvedQ τ n₄ n₁ h1,
    mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k₁ (Q N))),
    commute_evolvedQ τ n₄ n₂ h2, ← mul_assoc,
    mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k₁ (Q N))
      * heisenberg (freeFieldU K N τ ^ n₂) (modeOp k₂ (Q N))),
    commute_evolvedQ τ n₄ n₃ h3, ← mul_assoc] at h
  exact h

/-- ★ **Two pairs, grouped**: `⟨Q_k(n₁)Q_k(n₂)Q_l(n₃)Q_l(n₄)⟩ = K(n₁,n₂)·K(n₃,n₄)`
for `k ≠ l` — the one surviving Wick pairing, via clustering
(`diag_entry_mul_of_disjointSupport`). -/
theorem timeFourPoint_pair [NeZero N] (hN : 1 < N) (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    {k l : Fin K} (hkl : k ≠ l) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k k l l
      = twoPointKernel τ n₁ n₂ * twoPointKernel τ n₃ n₄ := by
  classical
  rw [timeFourPoint,
    mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k (Q N))
      * heisenberg (freeFieldU K N τ ^ n₂) (modeOp k (Q N))),
    diag_entry_mul_of_disjointSupport (by simpa using hkl)
      ((heisenberg_freeFieldU_pow_supportedOn τ n₁ (modeOp_supportedOn k (Q N))).mul
        (heisenberg_freeFieldU_pow_supportedOn τ n₂ (modeOp_supportedOn k (Q N))))
      ((heisenberg_freeFieldU_pow_supportedOn τ n₃ (modeOp_supportedOn l (Q N))).mul
        (heisenberg_freeFieldU_pow_supportedOn τ n₄ (modeOp_supportedOn l (Q N)))),
    evolvedPair_vac_vac hN τ n₁ n₂ k, evolvedPair_vac_vac hN τ n₃ n₄ l]

/-- **Two pairs, alternating**: `⟨Q_k(n₁)Q_l(n₂)Q_k(n₃)Q_l(n₄)⟩ = K(n₁,n₃)·K(n₂,n₄)`
— commuting the disjoint modes pairs the times `(n₁,n₃)` and `(n₂,n₄)`: the
arrangement decides which times meet in a kernel. -/
theorem timeFourPoint_alt [NeZero N] (hN : 1 < N) (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    {k l : Fin K} (hkl : k ≠ l) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k l k l
      = twoPointKernel τ n₁ n₃ * twoPointKernel τ n₂ n₄ := by
  have h := timeFourPoint_pair (N := N) hN τ n₁ n₃ n₂ n₄ hkl
  rw [timeFourPoint] at h ⊢
  rw [mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k (Q N))),
    commute_evolvedQ τ n₃ n₂ hkl, ← mul_assoc] at h
  exact h

/-- **Two pairs, nested**: `⟨Q_k(n₁)Q_l(n₂)Q_l(n₃)Q_k(n₄)⟩ = K(n₁,n₄)·K(n₂,n₃)`. -/
theorem timeFourPoint_outer [NeZero N] (hN : 1 < N) (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    {k l : Fin K} (hkl : k ≠ l) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k l l k
      = twoPointKernel τ n₁ n₄ * twoPointKernel τ n₂ n₃ := by
  have h := timeFourPoint_alt (N := N) hN τ n₁ n₂ n₄ n₃ hkl
  rw [timeFourPoint] at h ⊢
  rw [mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k (Q N))
      * heisenberg (freeFieldU K N τ ^ n₂) (modeOp l (Q N))),
    commute_evolvedQ τ n₄ n₃ hkl, ← mul_assoc] at h
  exact h

/-- ★ **All four equal**: the three-pairing sum
`⟨Q_k(n₁)Q_k(n₂)Q_k(n₃)Q_k(n₄)⟩ = K₁₂K₃₄ + K₁₃K₂₄ + K₁₄K₂₃` for `2 < N`. The walk
through the vacuum gives `K₁₂K₃₄`; the level-2 walk `0→1→2→1→0` gives
`½e^{-i(t₁+t₂−t₃−t₄)}`, which is **exactly** `K₁₃K₂₄ + K₁₄K₂₃` — the cross-pairings
share one exponent, and that identity is why Wick survives truncation. At `N = 2`
the level-2 walk is cut off, exactly as in `eqFourPoint_same`. -/
theorem timeFourPoint_same [NeZero N] (hN2 : 2 < N) (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    (k : Fin K) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k k k k
      = twoPointKernel τ n₁ n₂ * twoPointKernel τ n₃ n₄
        + twoPointKernel τ n₁ n₃ * twoPointKernel τ n₂ n₄
        + twoPointKernel τ n₁ n₄ * twoPointKernel τ n₂ n₃ := by
  classical
  have hN : 1 < N := by omega
  rw [timeFourPoint,
    mul_assoc (heisenberg (freeFieldU K N τ ^ n₁) (modeOp k (Q N))
      * heisenberg (freeFieldU K N τ ^ n₂) (modeOp k (Q N))),
    Matrix.mul_apply]
  rw [← Finset.sum_subset
      (Finset.subset_univ ({vacCfg K N, exc2Cfg hN2 k} : Finset _))
      (fun e _ he => by
        rw [evolvedPair_apply_vac_of_ne hN2 hN τ n₃ n₄ k
            (fun h => he (by simp [h])) (fun h => he (by simp [h])),
          mul_zero])]
  rw [Finset.sum_pair (vacCfg_ne_exc2Cfg hN2 k),
    evolvedPair_vac_vac hN τ n₁ n₂ k, evolvedPair_vac_vac hN τ n₃ n₄ k,
    evolvedPair_vac_exc2 hN2 hN τ n₁ n₂ k, evolvedPair_exc2_vac hN2 hN τ n₃ n₄ k]
  simp only [twoPointKernel]
  linear_combination (Complex.exp (-(Complex.I * (((n₁ : ℝ) * τ : ℝ) : ℂ)))
    * Complex.exp (-(Complex.I * (((n₂ : ℝ) * τ : ℝ) : ℂ)))
    * Complex.exp (Complex.I * (((n₃ : ℝ) * τ : ℝ) : ℂ))
    * Complex.exp (Complex.I * (((n₄ : ℝ) * τ : ℝ) : ℂ))) * inv_sqrt_two_mul_self

/-- ★★ **Wick's four-point theorem at distinct times** (CV-23b): above the
truncation threshold `2 < N`, the time-separated four-point function IS the pairing
sum over stroboscopic kernels,

  `⟨Q_{k₁}(n₁)Q_{k₂}(n₂)Q_{k₃}(n₃)Q_{k₄}(n₄)⟩
     = δ_{k₁k₂}δ_{k₃k₄}·K₁₂K₃₄ + δ_{k₁k₃}δ_{k₂k₄}·K₁₃K₂₄ + δ_{k₁k₄}δ_{k₂k₃}·K₁₄K₂₃`,

one formula over every mode pattern, with `K_{ij} = twoPointKernel τ n_i n_j` the
two-time propagator value (`timeTwoPoint_eq`). Equal periods collapse every kernel
to `½` (`twoPointKernel_self`) and recover `eqFourPoint_wick`; all periods `0`
recover it at the definition level (`timeFourPoint_zero`). The `2 < N` hypothesis
is load-bearing exactly where the equal-time table says: only the all-equal
pattern's level-2 walk needs it. -/
theorem timeFourPoint_wick [NeZero N] (hN2 : 2 < N) (τ : ℝ) (n₁ n₂ n₃ n₄ : ℕ)
    (k₁ k₂ k₃ k₄ : Fin K) :
    timeFourPoint (N := N) τ n₁ n₂ n₃ n₄ k₁ k₂ k₃ k₄
      = (if k₁ = k₂ then twoPointKernel τ n₁ n₂ else 0)
          * (if k₃ = k₄ then twoPointKernel τ n₃ n₄ else 0)
        + (if k₁ = k₃ then twoPointKernel τ n₁ n₃ else 0)
          * (if k₂ = k₄ then twoPointKernel τ n₂ n₄ else 0)
        + (if k₁ = k₄ then twoPointKernel τ n₁ n₄ else 0)
          * (if k₂ = k₃ then twoPointKernel τ n₂ n₃ else 0) := by
  have hN : 1 < N := by omega
  by_cases h12 : k₁ = k₂
  · subst h12
    by_cases h13 : k₁ = k₃
    · subst h13
      by_cases h14 : k₁ = k₄
      · subst h14
        rw [timeFourPoint_same hN2]
        simp
      · rw [timeFourPoint_single₄ τ n₁ n₂ n₃ n₄ (fun h => h14 h.symm)
          (fun h => h14 h.symm) (fun h => h14 h.symm)]
        simp [h14]
    · by_cases h34 : k₃ = k₄
      · subst h34
        rw [timeFourPoint_pair hN τ n₁ n₂ n₃ n₄ h13]
        simp [h13]
      · rw [timeFourPoint_single₃ τ n₁ n₂ n₃ n₄ (fun h => h13 h.symm)
          (fun h => h13 h.symm) h34]
        simp [h13, h34]
  · by_cases h13 : k₁ = k₃
    · subst h13
      by_cases h24 : k₂ = k₄
      · subst h24
        rw [timeFourPoint_alt hN τ n₁ n₂ n₃ n₄ h12]
        simp [h12]
      · rw [timeFourPoint_single₂ τ n₁ n₂ n₃ n₄ (fun h => h12 h.symm)
          (fun h => h12 h.symm) h24]
        simp [h12, Ne.symm h12, h24]
    · by_cases h14 : k₁ = k₄
      · subst h14
        by_cases h23 : k₂ = k₃
        · subst h23
          rw [timeFourPoint_outer hN τ n₁ n₂ n₃ n₄ h12]
          simp [h12]
        · rw [timeFourPoint_single₂ τ n₁ n₂ n₃ n₄ (fun h => h12 h.symm) h23
            (fun h => h12 h.symm)]
          simp [h12, Ne.symm h12, h23]
      · rw [timeFourPoint_single₁ τ n₁ n₂ n₃ n₄ h12 h13 h14]
        simp [h12, h13, h14]

/-! ### The CV-23c gate: the six-point pass

The go/no-go probe for the `2n`-point Wick theorem, agreed in advance
(`eft-stage7-plan.md`): the six-point all-equal pattern and one mixed pattern must
land with the walk-collapse idiom, `fin_cases`-free, thresholds explicit. The idiom
scales by exactly one rung: one new configuration (`exc3Cfg`), one new level of the
`Q` entry ladder (`Q_two_three`/`Q_three_two`), one new reachability lemma
(`modeOp_Q_apply_exc2`), and the `Q³` column at the vacuum. The general `2n`-point
theorem is NOT claimed here — the gate un-gates it. -/

/-- `Q` connects the second to the third level with amplitude `√3/√2`. -/
lemma Q_two_three [NeZero N] (hN3 : 3 < N) :
    Q N ⟨2, by omega⟩ ⟨3, hN3⟩
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ) := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply, creation_apply]
  norm_num

/-- `Q` connects the third level back to the second with the same amplitude. -/
lemma Q_three_two [NeZero N] (hN3 : 3 < N) :
    Q N ⟨3, hN3⟩ ⟨2, by omega⟩
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ) := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply, creation_apply]
  norm_num

/-- `Q` reaches the second level only from the first and the third. -/
lemma Q_apply_two_eq_zero [NeZero N] (hN2 : 2 < N) {m : Fin N} (h1 : (m : ℕ) ≠ 1)
    (h3 : (m : ℕ) ≠ 3) : Q N m ⟨2, hN2⟩ = 0 := by
  rw [Q, Matrix.smul_apply, Matrix.add_apply, annihilation_apply, creation_apply,
    if_neg (show ¬((m : ℕ) + 1 = ((2 : ℕ))) from by omega),
    if_neg (show ¬((2 : ℕ) + 1 = ((m : ℕ))) from by omega)]
  simp

/-- The **three-quantum configuration** at mode `l`. -/
def exc3Cfg [NeZero N] (hN3 : 3 < N) (l : Fin K) : FieldConfig K N :=
  Function.update (vacCfg K N) l ⟨3, hN3⟩

@[simp] lemma exc3Cfg_self [NeZero N] (hN3 : 3 < N) (l : Fin K) :
    (exc3Cfg (K := K) hN3 l) l = ⟨3, hN3⟩ := by
  simp [exc3Cfg]

lemma exc3Cfg_of_ne [NeZero N] (hN3 : 3 < N) {l j : Fin K} (h : j ≠ l) :
    (exc3Cfg (K := K) hN3 l) j = 0 := by
  simp [exc3Cfg, h]

lemma excCfg_ne_exc3Cfg [NeZero N] (hN3 : 3 < N) (hN : 1 < N) (k : Fin K) :
    excCfg (K := K) hN k ≠ exc3Cfg hN3 k := by
  intro h
  have hk := congrFun h k
  rw [excCfg_self, exc3Cfg_self] at hk
  exact absurd (congrArg Fin.val hk) (by simp)

/-- From the two-quantum configuration, the mode quadrature reaches only the
one- and three-quantum configurations. -/
lemma modeOp_Q_apply_exc2 [NeZero N] (hN3 : 3 < N) (hN2 : 2 < N) (hN : 1 < N)
    (k : Fin K) {e : FieldConfig K N} (h1 : e ≠ excCfg hN k)
    (h3 : e ≠ exc3Cfg hN3 k) :
    modeOp k (Q N) e (exc2Cfg hN2 k) = 0 := by
  by_cases hoff : ∀ j, j ≠ k → e j = (vacCfg K N) j
  · rw [modeOp_apply_of_agree k _ (fun j hj => by
      rw [hoff j hj, vacCfg_apply, exc2Cfg_of_ne hN2 hj]),
      exc2Cfg_self]
    refine Q_apply_two_eq_zero hN2 ?_ ?_
    · intro hval
      refine h1 (funext fun j => ?_)
      by_cases hj : j = k
      · subst hj
        rw [excCfg_self]
        exact Fin.ext (by simpa using hval)
      · rw [hoff j hj, vacCfg_apply, excCfg_of_ne hN hj]
    · intro hval
      refine h3 (funext fun j => ?_)
      by_cases hj : j = k
      · subst hj
        rw [exc3Cfg_self]
        exact Fin.ext (by simpa using hval)
      · rw [hoff j hj, vacCfg_apply, exc3Cfg_of_ne hN3 hj]
  · rw [modeOp, if_neg (fun h' => hoff (fun j hj => by
      rw [h' j hj, exc2Cfg_of_ne hN2 hj, vacCfg_apply]))]

/-- The mode quadrature is symmetric as a matrix transpose identity. -/
lemma modeOpQ_transpose [NeZero N] (k : Fin K) :
    (modeOp k (Q N))ᵀ = modeOp k (Q N) := by
  ext c d
  rw [Matrix.transpose_apply, modeOpQ_symm]

/-- The cube of the mode quadrature is symmetric — powers of a symmetric matrix
stay symmetric, entrywise form. -/
lemma modeOpQ_cube_symm [NeZero N] (k : Fin K) (c d : FieldConfig K N) :
    (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N)) c d
      = (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N)) d c := by
  have h : (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N))ᵀ
      = modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, modeOpQ_transpose, ← mul_assoc]
  conv_lhs => rw [← h]
  rw [Matrix.transpose_apply]

/-- The column of `Q_k³` at the vacuum — the plan's `Q³e₀ = (3/(2√2))·e₁ + (√3/2)·e₃`
anchor, in walk-collapse form: mass `(3/2)·(√2)⁻¹` on the one-quantum configuration,
`√3/2` on the three-quantum configuration, nothing else. -/
lemma modeOpQ_cube_apply_vac [NeZero N] (hN3 : 3 < N) (hN2 : 2 < N) (hN : 1 < N)
    (k : Fin K) (e : FieldConfig K N) :
    (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N)) e (vacCfg K N)
      = if e = excCfg hN k then (3 / 2 : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
        else if e = exc3Cfg hN3 k then ((Real.sqrt 3 : ℝ) : ℂ) * (2 : ℂ)⁻¹
        else 0 := by
  classical
  rw [mul_assoc, Matrix.mul_apply]
  rw [← Finset.sum_subset
      (Finset.subset_univ ({vacCfg K N, exc2Cfg hN2 k} : Finset _))
      (fun c _ hc => by
        rw [modeOpQ_sq_apply_vac hN2 k c, if_neg (fun h => hc (by simp [h])),
          if_neg (fun h => hc (by simp [h])), mul_zero])]
  rw [Finset.sum_pair (vacCfg_ne_exc2Cfg hN2 k), modeOpQ_sq_vac hN k,
    modeOpQ_sq_exc2_vac hN2 k]
  split_ifs with he1 he3
  · subst he1
    rw [modeOp_apply_of_agree k (Q N) (fun j hj => excCfg_agree hN k hj),
      excCfg_self, vacCfg_apply, Q_one_zero hN,
      modeOp_apply_of_agree k (Q N) (fun j hj => by
        rw [excCfg_of_ne hN hj, exc2Cfg_of_ne hN2 hj]),
      excCfg_self, exc2Cfg_self, Q_one_two hN2]
    ring
  · subst he3
    rw [modeOp_Q_apply_vac hN k _ (excCfg_ne_exc3Cfg hN3 hN k).symm,
      modeOp_apply_of_agree k (Q N) (fun j hj => by
        rw [exc3Cfg_of_ne hN3 hj, exc2Cfg_of_ne hN2 hj]),
      exc3Cfg_self, exc2Cfg_self, Q_three_two hN3]
    linear_combination (((Real.sqrt 3 : ℝ) : ℂ)) * inv_sqrt_two_mul_self
  · rw [modeOp_Q_apply_vac hN k e he1, modeOp_Q_apply_exc2 hN3 hN2 hN k he1 he3]
    norm_num

/-- ★ **The six-point pass, all-equal pattern**: the equal-time sixth moment
`⟨vac∣Q_k⁶∣vac⟩ = 15/8 = 5!!·(½)³` for `3 < N` — Wick's fifteen pairings, all
surviving at `(½)³` each. Via `‖Q³e₀‖² = 9/8 + 3/4`: the walk through
the one-quantum configuration squared plus the walk through the three-quantum
configuration squared. At `N = 3` the level-3 walk dies and the value is `9/8` —
the truncation honesty one rung above `eqFourPoint_same`'s. -/
theorem modeOpQ_six_vac [NeZero N] (hN3 : 3 < N) (k : Fin K) :
    (modeOp k (Q N) ^ 6) (vacCfg K N) (vacCfg K N) = 15 / 8 := by
  classical
  have hN : 1 < N := by omega
  have hN2 : 2 < N := by omega
  have h1 : (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N))
      (excCfg hN k) (vacCfg K N)
      = (3 / 2 : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
    rw [modeOpQ_cube_apply_vac hN3 hN2 hN k, if_pos rfl]
  have h3 : (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N))
      (exc3Cfg hN3 k) (vacCfg K N)
      = ((Real.sqrt 3 : ℝ) : ℂ) * (2 : ℂ)⁻¹ := by
    rw [modeOpQ_cube_apply_vac hN3 hN2 hN k,
      if_neg (excCfg_ne_exc3Cfg hN3 hN k).symm, if_pos rfl]
  have hpow : modeOp k (Q N) ^ 6
      = (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N))
        * (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N)) := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, show (3 : ℕ) = 2 + 1 from rfl,
      pow_succ, pow_two]
  rw [hpow, Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun e _ => by
    rw [modeOpQ_cube_symm k (vacCfg K N) e])]
  rw [← Finset.sum_subset
      (Finset.subset_univ ({excCfg hN k, exc3Cfg hN3 k} : Finset _))
      (fun e _ he => by
        rw [modeOpQ_cube_apply_vac hN3 hN2 hN k e,
          if_neg (fun h => he (by simp [h])), if_neg (fun h => he (by simp [h])),
          zero_mul])]
  rw [Finset.sum_pair (excCfg_ne_exc3Cfg hN3 hN k), h1, h3]
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  linear_combination (9 / 4 : ℂ) * inv_sqrt_two_mul_self + (4 : ℂ)⁻¹ * hs3

/-- **The six-point pass, mixed pattern**: `⟨vac∣Q_k⁴·Q_l²∣vac⟩ = 3/8 = (3/4)·(1/2)`
for `k ≠ l` — clustering splits the modes, and the factors are the four-point
all-equal value and the vacuum fluctuation. Needs only `2 < N` (the thresholds of
its factors). -/
theorem modeOpQ_four_two_vac [NeZero N] (hN2 : 2 < N) {k l : Fin K} (hkl : k ≠ l) :
    (modeOp k (Q N) ^ 4 * modeOp l (Q N) ^ 2) (vacCfg K N) (vacCfg K N) = 3 / 8 := by
  classical
  have hN : 1 < N := by omega
  have hpow : modeOp k (Q N) ^ 4
      = modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N) := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, show (3 : ℕ) = 2 + 1 from rfl,
      pow_succ, pow_two]
  rw [hpow, pow_two,
    diag_entry_mul_of_disjointSupport (by simpa using hkl)
      ((((modeOp_supportedOn k (Q N)).mul (modeOp_supportedOn k (Q N))).mul
        (modeOp_supportedOn k (Q N))).mul (modeOp_supportedOn k (Q N)))
      ((modeOp_supportedOn l (Q N)).mul (modeOp_supportedOn l (Q N))),
    show (modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N) * modeOp k (Q N))
        (vacCfg K N) (vacCfg K N) = eqFourPoint (N := N) k k k k from rfl,
    eqFourPoint_same hN2 k, modeOpQ_sq_vac hN l]
  norm_num

end CSD.CV

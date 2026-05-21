import CsdLean4.LF3.Singlet.Kernel
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Empirical: Bell-family predictions on the bipartite singlet

**Category:** 3-Local (CSD-specific empirical-test re-exports of the LF3
singlet kernel; some items here are QM-generic and may be promoted to
Cat-2 Framework on demand).

This module names the LF3 singlet-kernel content as **empirical
predictions** with explicit experimental provenance, providing a
regression suite that verifies the CSD volume-ratio account reproduces
the well-tested QM predictions about Bell-type experiments.

Phase A items (per `specs/qm-empirical-tests.md`):

- **A1: CHSH at Tsirelson bound.** `∃ a a' b b' : DetectorSetting,
  |S(a, a', b, b')| = 2√2` on the singlet, where
  `S = E(a, b) − E(a, b') + E(a', b) + E(a', b')`.
- **A2: Classical bound violated.** `2√2 > 2`, named as
  `chsh_classical_bound_violated`.
- **A3 / A4: No-signalling.** Alice's marginal is independent of Bob's
  setting; symmetric for Bob.
- **A5: Singlet marginals uniform.** `P(A = +) = P(B = +) = 1/2`.

- **A6: Tsirelson upper bound (inner-product / expectation form).** Two
  forms are exported. The **algebraic Khalfin-Tsirelson** form
  (`chsh_inner_bound`) bounds
  `|Re⟨α, β⟩ − Re⟨α, β'⟩ + Re⟨α', β⟩ + Re⟨α', β'⟩| ≤ 2√2` for any
  four unit vectors `α, α', β, β'` in a complex inner product space,
  proved via the parallelogram law + Cauchy-Schwarz on `ℝ²`. The
  **QM-expectation lift** (`chsh_qm_tsirelson_bound`) lifts this to the
  bipartite-Pauli CHSH expectation
  `|Re⟨ψ, (σ·a ⊗ σ·b)ψ⟩ ± …| ≤ 2√2` for any unit `ψ ∈ ℂ² ⊗ ℂ²`, via the
  standard Tsirelson construction `α(a, ψ) := (σ·a ⊗ I)ψ`,
  `β(b, ψ) := (I ⊗ σ·b)ψ`. (The operator-form Loewner-order statement
  via Mathlib's `tsirelson_inequality` was the original target but is
  currently blocked on a missing `IsOrderedModule ℝ (Matrix n n ℂ)`
  instance upstream; the algebraic + lift route is mathematically
  equivalent and lands the same expectation bound.)

## Experimental provenance

- Bell 1964: *Physics* **1**, 195 (the classical bound).
- Tsirelson 1980: *Lett. Math. Phys.* **4**, 93 (the quantum bound 2√2).
- Aspect, Grangier, Roger 1982: *Phys. Rev. Lett.* **49**, 91
  (laboratory verification of Bell-inequality violation).

The Lean theorems below are derived from LF3 `correlation_eq_neg_dot`,
`marginal_a_eq_half`, `marginal_b_eq_half`, `no_signalling_strong_readout_a/b`,
which themselves consume only LF3's algebraic core `P_st(a, b, s, t)
= (1 − st · a·b)/4` (Kernel.lean). The chain to the empirical-frequency
side (LF1 SLLN) sits in `LF3/Interface.lean`'s
`LF3_singlet_frequency_convergence` capstones.

## Caveat on ontic grounding

These predictions verify CSD-against-QM equivalence on the projective
side. Full *ontic* grounding (Σ as a compact Kähler manifold, μL as the
Kähler volume form) is the LF4 §8 obligation. Until then the empirical
content is conditional on the CSD ontic axioms supplying the bridge
data and the Dirac-concentration preparation. See
`[[project-structural-debts]]` and `[[project-lf4-decisions]]`.
-/

open Real
open scoped BigOperators

namespace CSD
namespace Empirical
namespace Bell

open LF3

/-! ### Singlet correlation function

The CHSH inequality is phrased in terms of the correlation
`E(a, b) := ⟨ψ⁻| σ·a ⊗ σ·b |ψ⁻⟩ = −a·b` for the singlet `|ψ⁻⟩` (proved
inside LF3 as `singlet_pauli_correlation` for the operator form, and
as `correlation_eq_neg_dot` for the operational pointer-sector form).
The latter is the canonical empirical-prediction form: it states the
correlation as a finite sum `∑_{s, t} st·P_st(a, b)` over the
strong-readout pointer-sector probabilities, exactly the quantity an
experimentalist measures.
-/

/-- **Singlet correlation function** in operational form: the signed
sum `∑_{s, t} st·P_st(a, b)` over the joint pointer-sector probabilities
in the strong-readout limit, equal to `−a·b` for the singlet.

This is the experimental quantity directly measured in Bell-type
experiments (after Alice and Bob aggregate joint outcomes per setting
pair). -/
noncomputable def correlation (a b : DetectorSetting) : ℝ :=
  ∑ st : Sign × Sign, st.1.val * st.2.val * P_st a b st.1 st.2

/-- Closed form: `E(a, b) = −a·b` for the singlet.

This re-states `LF3.correlation_eq_neg_dot` as an empirical-prediction
named export. -/
theorem correlation_eq_neg_dot (a b : DetectorSetting) :
    correlation a b = -(dotR a b) :=
  CSD.LF3.correlation_eq_neg_dot a b

/-! ### A3 / A4: no-signalling

Both sides' marginals are independent of the other side's setting.
Experimentally verified to high precision; structurally guaranteed in
QM by the partial-trace marginal identity. In LF3 this comes from the
finite `Sign`-sum identity for `P_st`, with no appeal to entanglement
structure beyond the kernel.

**Experimental verification:** Aspect 1982 (locality-loophole-free
versions: Hensen 2015, Giustina 2015, Shalm 2015). -/

/-- **A3: No-signalling, Alice side.** Alice's marginal probability is
independent of Bob's setting. -/
theorem no_signalling_alice
    (a b b' : DetectorSetting) (s : Sign) :
    (∑ t : Sign, P_st a b s t) = (∑ t : Sign, P_st a b' s t) :=
  CSD.LF3.no_signalling_strong_readout_a a b b' s

/-- **A4: No-signalling, Bob side.** Bob's marginal probability is
independent of Alice's setting. -/
theorem no_signalling_bob
    (a a' b : DetectorSetting) (t : Sign) :
    (∑ s : Sign, P_st a b s t) = (∑ s : Sign, P_st a' b s t) :=
  CSD.LF3.no_signalling_strong_readout_b a a' b t

/-! ### A5: singlet marginals uniform

For the singlet state, each side sees `1/2 / 1/2` outcomes regardless of
setting choice. This is the "maximally mixed marginal" property of the
singlet; together with no-signalling it is the operational signature
of the singlet's symmetry. -/

/-- **A5: Singlet A-side marginal uniform** at `1/2`. -/
theorem singlet_marginal_alice (a b : DetectorSetting) (s : Sign) :
    ∑ t : Sign, P_st a b s t = 1 / 2 :=
  CSD.LF3.marginal_a_eq_half a b s

/-- **A5 (Bob side): Singlet B-side marginal uniform** at `1/2`. -/
theorem singlet_marginal_bob (a b : DetectorSetting) (t : Sign) :
    ∑ s : Sign, P_st a b s t = 1 / 2 :=
  CSD.LF3.marginal_b_eq_half a b t

/-! ### A2: classical Bell bound violation gap

The classical (Bell 1964) bound on the CHSH operator under any local
hidden-variable assignment is `|S| ≤ 2`. The QM prediction `|S| = 2√2`
(Tsirelson 1980, saturated by the singlet at canonical angles) violates
this bound. The named gap is the empirical falsification of local
realism. -/

/-- **The numerical value `2` of the Bell-1964 classical (LHV) CHSH
bound.** This is a named constant carrying the value `2`, not a
theorem that any local-hidden-variable model satisfies `|S| ≤ 2`. The
LHV inequality itself is **not** formalised in this module — doing so
would require modelling a probability space of hidden variables and a
factorisable joint distribution, which is outside the current scope.

The constant is named `bellClassicalBoundValue` (with the trailing
`Value` to make the un-formalised LHV-theorem status visible) and
exists solely so that the gap theorem `chsh_classical_bound_violated`
can state `value < 2√2` rather than open-coding the literal. -/
def bellClassicalBoundValue : ℝ := 2

/-- **A2: The Bell-classical-bound value `2` is strictly less than the
quantum Tsirelson bound `2√2`.** The numerical gap is the empirical
falsification of local realism realised by the singlet at canonical
angles — under the **un-formalised** premise that any LHV model
satisfies `|S| ≤ 2` (Bell 1964). The Lean statement is purely
numerical (`2 < 2√2`).

**Experimental verification:** Aspect, Grangier, Roger 1982,
*Phys. Rev. Lett.* **49**, 91 (and many subsequent loophole-free
experiments). -/
theorem chsh_classical_bound_violated : bellClassicalBoundValue < 2 * Real.sqrt 2 := by
  unfold bellClassicalBoundValue
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at this
  linarith

/-! ### A1: CHSH at Tsirelson bound

The CHSH operator `S(a, a', b, b') := E(a, b) − E(a, b') + E(a', b) +
E(a', b')` evaluated on the singlet achieves `|S| = 2√2` at the
canonical angles `a = ẑ̂_x`, `a' = ẑ̂_y`, `b = (ẑ̂_x + ẑ̂_y)/√2`,
`b' = (−ẑ̂_x + ẑ̂_y)/√2` (where `ẑ̂_x` etc. denote unit vectors along
the indicated axis of ℝ³).

**Tsirelson 1980** proves `|S| ≤ 2√2` for any quantum state (the upper
bound, A6 below). **A1** here establishes saturation: the singlet at
canonical angles realises the Tsirelson bound.

We construct the four detector settings explicitly and compute `S`
algebraically against `correlation_eq_neg_dot`. -/

/-- **CHSH operator** evaluated on the singlet correlation function. -/
noncomputable def chshOperator (a a' b b' : DetectorSetting) : ℝ :=
  correlation a b - correlation a b' + correlation a' b + correlation a' b'

/-- Helper: construct a `DetectorSetting` from three real components
`(x, y, z)` with the unit-norm side condition. Uses `WithLp.toLp 2` to
build the underlying `EuclideanSpace ℝ (Fin 3)` value from a tuple. -/
private noncomputable def detector3 (x y z : ℝ)
    (h_norm : x ^ 2 + y ^ 2 + z ^ 2 = 1) : DetectorSetting where
  vec := WithLp.toLp 2 (![x, y, z] : Fin 3 → ℝ)
  unit := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [h_norm]
    exact Real.sqrt_one

/-- The canonical CHSH detector `a = (1, 0, 0)` along the x-axis. -/
noncomputable def chshA : DetectorSetting :=
  detector3 1 0 0 (by ring)

/-- The canonical CHSH detector `a' = (0, 1, 0)` along the y-axis. -/
noncomputable def chshA' : DetectorSetting :=
  detector3 0 1 0 (by ring)

/-- Auxiliary: `(√2 / 2) ^ 2 = 1 / 2`. -/
private lemma sqrt2_div_two_sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
  norm_num

/-- The canonical CHSH detector `b = (√2/2, √2/2, 0)` at 45° in the
xy-plane. -/
noncomputable def chshB : DetectorSetting :=
  detector3 (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) 0 (by
    rw [sqrt2_div_two_sq]
    ring)

/-- The canonical CHSH detector `b' = (−√2/2, √2/2, 0)` at 135° in the
xy-plane. -/
noncomputable def chshB' : DetectorSetting :=
  detector3 (-(Real.sqrt 2 / 2)) (Real.sqrt 2 / 2) 0 (by
    rw [neg_pow, sqrt2_div_two_sq]
    norm_num)

/-- Component-evaluation lemmas for the canonical detectors. The
`.ofLp` projection exposes the underlying `Fin 3 → ℝ` representation
(which is `WithLp.toLp 2 ![...]` definitionally). -/
@[simp] lemma chshA_vec_ofLp_0 : chshA.vec.ofLp 0 = 1 := rfl
@[simp] lemma chshA_vec_ofLp_1 : chshA.vec.ofLp 1 = 0 := rfl
@[simp] lemma chshA_vec_ofLp_2 : chshA.vec.ofLp 2 = 0 := rfl

@[simp] lemma chshA'_vec_ofLp_0 : chshA'.vec.ofLp 0 = 0 := rfl
@[simp] lemma chshA'_vec_ofLp_1 : chshA'.vec.ofLp 1 = 1 := rfl
@[simp] lemma chshA'_vec_ofLp_2 : chshA'.vec.ofLp 2 = 0 := rfl

@[simp] lemma chshB_vec_ofLp_0 : chshB.vec.ofLp 0 = Real.sqrt 2 / 2 := rfl
@[simp] lemma chshB_vec_ofLp_1 : chshB.vec.ofLp 1 = Real.sqrt 2 / 2 := rfl
@[simp] lemma chshB_vec_ofLp_2 : chshB.vec.ofLp 2 = 0 := rfl

@[simp] lemma chshB'_vec_ofLp_0 : chshB'.vec.ofLp 0 = -(Real.sqrt 2 / 2) := rfl
@[simp] lemma chshB'_vec_ofLp_1 : chshB'.vec.ofLp 1 = Real.sqrt 2 / 2 := rfl
@[simp] lemma chshB'_vec_ofLp_2 : chshB'.vec.ofLp 2 = 0 := rfl

/-- `√2 · √2 = 2`. -/
private lemma sqrt2_mul_sqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

/-- **A1 (named-witness form):** the CHSH operator on the singlet at
the canonical angles equals `−2√2`. -/
theorem chsh_singlet_at_optimal_angles :
    chshOperator chshA chshA' chshB chshB' = -(2 * Real.sqrt 2) := by
  unfold chshOperator
  simp only [correlation_eq_neg_dot]
  unfold dotR
  simp only [chshA_vec_ofLp_0, chshA_vec_ofLp_1, chshA_vec_ofLp_2,
    chshA'_vec_ofLp_0, chshA'_vec_ofLp_1, chshA'_vec_ofLp_2,
    chshB_vec_ofLp_0, chshB_vec_ofLp_1, chshB_vec_ofLp_2,
    chshB'_vec_ofLp_0, chshB'_vec_ofLp_1, chshB'_vec_ofLp_2]
  ring

/-- **A1: CHSH at the Tsirelson bound.** There exist detector settings
`a, a', b, b'` for which the singlet CHSH operator saturates the
Tsirelson bound `|S(a, a', b, b')| = 2√2`.

Combined with A2 (`bellClassicalBound < 2√2`) and A6 (Tsirelson upper
bound), this constitutes the LF3-side formal record of the
Bell-inequality violation that Aspect 1982 first verified
experimentally.

**Experimental verification:** Aspect, Grangier, Roger 1982,
*Phys. Rev. Lett.* **49**, 91; loophole-free verifications including
Hensen et al. 2015, *Nature* **526**, 682; Giustina et al. 2015,
*Phys. Rev. Lett.* **115**, 250401; Shalm et al. 2015,
*Phys. Rev. Lett.* **115**, 250402. -/
theorem chsh_singlet_tsirelson_bound :
    ∃ a a' b b' : DetectorSetting,
      |chshOperator a a' b b'| = 2 * Real.sqrt 2 := by
  refine ⟨chshA, chshA', chshB, chshB', ?_⟩
  rw [chsh_singlet_at_optimal_angles, abs_neg, abs_of_pos]
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-! ### A6: Tsirelson upper bound (Khalfin-Tsirelson algebraic form)

The Tsirelson 1980 inequality says that for any quantum state — pure or
mixed, on any Hilbert space — the CHSH observable on a pair of binary
commuting observable families has expectation bounded by `2√2`.

We deliver the **Khalfin-Tsirelson algebraic form**: a purely
inner-product-space statement that supplies the load-bearing inequality
for any QM realisation. For any (complex) inner product space `E` and
four unit vectors `α, α', β, β' ∈ E`:
```
|Re⟨α, β⟩ − Re⟨α, β'⟩ + Re⟨α', β⟩ + Re⟨α', β'⟩| ≤ 2√2.
```

The QM Tsirelson upper bound follows by the standard Tsirelson
construction: set `α(a) := (σ·a ⊗ I)ψ`, `β(b) := (I ⊗ σ·b)ψ` for unit
`ψ`. Each is a unit vector (uses `(σ·a)² = I`), and
`⟨ψ, (σ·a ⊗ σ·b)ψ⟩ = ⟨α(a), β(b)⟩` (Hermiticity). Applying the
algebraic K-T lemma below yields the QM CHSH bound.

The QM-application lift is deferred: it requires either Mathlib's
`tsirelson_inequality` (currently blocked on the missing
`IsOrderedModule ℝ (Matrix n n ℂ)` instance) or the direct K-T
construction (Hilbert-vector setup + Hermitian-adjoint manipulations).
Neither is in scope for this commit.

**Why the algebraic form is the load-bearing content.** Tsirelson's
original 1980 result is, up to relabeling, exactly the algebraic
inner-product inequality below: he derives it via the parallelogram
law and Cauchy-Schwarz on `ℝ²`. The QM-application step is mechanical
once the algebraic core is in place.

**Experimental verification:** Tsirelson 1980, *Lett. Math. Phys.* **4**,
93 (theoretical); saturated by the singlet at canonical angles
(`chsh_singlet_at_optimal_angles`, A1). -/

/-- Auxiliary: `x + y ≤ √2 · √(x² + y²)` for any non-negative reals
`x, y`. Cauchy-Schwarz on `ℝ²` applied to `(1, 1)` and `(x, y)`. -/
private lemma sum_le_sqrt_two_mul_sqrt_sum_sq {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x + y ≤ Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) := by
  have h_sq : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h_target_sq :
      (Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 = 2 * (x ^ 2 + y ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0),
        Real.sq_sqrt (by positivity : 0 ≤ x ^ 2 + y ^ 2)]
  have h_target_nn : 0 ≤ Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_lhs_nn : 0 ≤ x + y := add_nonneg hx hy
  -- (x+y)² ≤ (target)² with both sides non-negative ⟹ x+y ≤ target
  nlinarith [h_sq, h_target_sq, h_target_nn, h_lhs_nn,
             sq_nonneg (x + y - Real.sqrt 2 * Real.sqrt (x ^ 2 + y ^ 2))]

/-- **A6: Khalfin-Tsirelson algebraic CHSH bound** in a complex inner
product space.

For any four unit vectors `α, α', β, β'` in a complex inner product
space, the CHSH expression in real-inner-product form is bounded by
`2√2`:
```
|Re⟨α, β⟩ − Re⟨α, β'⟩ + Re⟨α', β⟩ + Re⟨α', β'⟩| ≤ 2√2.
```

**Proof.** Let `S := Re⟨α, β − β'⟩ + Re⟨α', β + β'⟩`. By the real-part
Cauchy-Schwarz inequality:
- `Re⟨α, β − β'⟩ ≤ ‖α‖ · ‖β − β'‖ = ‖β − β'‖` (unit α).
- `Re⟨α', β + β'⟩ ≤ ‖α'‖ · ‖β + β'‖ = ‖β + β'‖`.

So `S ≤ ‖β − β'‖ + ‖β + β'‖`. By `sum_le_sqrt_two_mul_sqrt_sum_sq` and
the parallelogram identity `‖β − β'‖² + ‖β + β'‖² = 2(‖β‖² + ‖β'‖²) = 4`:
```
‖β − β'‖ + ‖β + β'‖ ≤ √2 · √(‖β − β'‖² + ‖β + β'‖²) = √2 · √4 = 2√2.
```

The lower bound on `S` follows by symmetry (negate α, α').

**Experimental verification:** Tsirelson 1980 (theoretical); saturated
by the singlet at canonical angles via the standard Tsirelson
construction `α(a) := (σ·a ⊗ I)ψ⁻`, `β(b) := (I ⊗ σ·b)ψ⁻`. -/
theorem chsh_inner_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (α α' β β' : E)
    (hα : ‖α‖ = 1) (hα' : ‖α'‖ = 1)
    (hβ : ‖β‖ = 1) (hβ' : ‖β'‖ = 1) :
    |Complex.re (inner ℂ α β) - Complex.re (inner ℂ α β')
        + Complex.re (inner ℂ α' β) + Complex.re (inner ℂ α' β')|
    ≤ 2 * Real.sqrt 2 := by
  -- Rewrite as `Re⟨α, β-β'⟩ + Re⟨α', β+β'⟩`.
  have rewrite_S :
      Complex.re (inner ℂ α β) - Complex.re (inner ℂ α β')
          + Complex.re (inner ℂ α' β) + Complex.re (inner ℂ α' β')
        = Complex.re (inner ℂ α (β - β')) + Complex.re (inner ℂ α' (β + β')) := by
    simp [inner_sub_right, inner_add_right, Complex.sub_re, Complex.add_re]
    ring
  rw [rewrite_S]
  -- Cauchy-Schwarz for the real part: `|re ⟨x, y⟩| ≤ ‖x‖ * ‖y‖`.
  have re_inner_abs_bound :
      ∀ (x y : E), |Complex.re (inner ℂ x y)| ≤ ‖x‖ * ‖y‖ := by
    intro x y
    have h_pos : Complex.re (inner ℂ x y) ≤ ‖x‖ * ‖y‖ := re_inner_le_norm (𝕜 := ℂ) x y
    have h_neg : -Complex.re (inner ℂ x y) ≤ ‖x‖ * ‖y‖ := by
      have h := re_inner_le_norm (𝕜 := ℂ) (-x) y
      rwa [inner_neg_left, map_neg, norm_neg] at h
    exact abs_le.mpr ⟨by linarith, h_pos⟩
  have cs_α : |Complex.re (inner ℂ α (β - β'))| ≤ ‖β - β'‖ := by
    have h := re_inner_abs_bound α (β - β')
    rw [hα, one_mul] at h; exact h
  have cs_α' : |Complex.re (inner ℂ α' (β + β'))| ≤ ‖β + β'‖ := by
    have h := re_inner_abs_bound α' (β + β')
    rw [hα', one_mul] at h; exact h
  -- Parallelogram identity (Mathlib form: ‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)).
  have parallelogram :
      ‖β - β'‖ ^ 2 + ‖β + β'‖ ^ 2 = 4 := by
    have hp := parallelogram_law_with_norm ℂ β β'
    -- hp : ‖β + β'‖^2 + ‖β - β'‖^2 = 2 * (‖β‖^2 + ‖β'‖^2)
    rw [hβ, hβ'] at hp
    linarith
  -- Apply the auxiliary bound and finish.
  have h_norm_sum :
      ‖β - β'‖ + ‖β + β'‖ ≤ 2 * Real.sqrt 2 := by
    have h_aux := sum_le_sqrt_two_mul_sqrt_sum_sq
      (norm_nonneg (β - β')) (norm_nonneg (β + β'))
    rw [parallelogram] at h_aux
    have h_sqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h_sqrt4] at h_aux
    linarith
  have h_abs :
      |Complex.re (inner ℂ α (β - β')) + Complex.re (inner ℂ α' (β + β'))|
        ≤ ‖β - β'‖ + ‖β + β'‖ := by
    calc |Complex.re (inner ℂ α (β - β')) + Complex.re (inner ℂ α' (β + β'))|
        ≤ |Complex.re (inner ℂ α (β - β'))| + |Complex.re (inner ℂ α' (β + β'))| :=
          abs_add_le _ _
      _ ≤ ‖β - β'‖ + ‖β + β'‖ := by linarith
  linarith

/-! ### A6 QM-application lift: Tsirelson bound on QM expectation

The algebraic `chsh_inner_bound` lifts to the QM CHSH expectation via the
standard Tsirelson construction:

```
α(a, ψ) := (σ·a ⊗ I) ψ,        β(b, ψ) := (I ⊗ σ·b) ψ
```

For unit `ψ`, each of `α(a), α(a'), β(b), β(b')` is a unit vector
(since `(σ·a ⊗ I)² = I` is a Hermitian involution, which preserves
norms). The inner-product identity

```
⟨α(a, ψ), β(b, ψ)⟩  =  ⟨ψ, (σ·a ⊗ σ·b) ψ⟩
```

(from Hermiticity of `σ·a ⊗ I` plus the Kronecker product identity
`(σ·a ⊗ I) · (I ⊗ σ·b) = σ·a ⊗ σ·b`) then turns the QM CHSH expectation
into the inner-product form, and `chsh_inner_bound` gives `≤ 2√2`.
-/

open scoped Kronecker

/-- `(σ·a ⊗ I)² = I` as a matrix identity. The kernel of the involution
property that underlies norm preservation by the Tsirelson Alice-side
operator. -/
private lemma sigmaDotLeft_sq (a : DetectorSetting) :
    sigmaDotLeft a * sigmaDotLeft a = 1 := by
  unfold sigmaDotLeft
  rw [← Matrix.mul_kronecker_mul, pauliDot_sq, one_mul, Matrix.one_kronecker_one]

/-- `(I ⊗ σ·b)² = I`. -/
private lemma sigmaDotRight_sq (b : DetectorSetting) :
    sigmaDotRight b * sigmaDotRight b = 1 := by
  unfold sigmaDotRight
  rw [← Matrix.mul_kronecker_mul, pauliDot_sq, one_mul, Matrix.one_kronecker_one]

/-- `σ·a ⊗ I` is Hermitian. -/
private lemma sigmaDotLeft_isHermitian (a : DetectorSetting) :
    (sigmaDotLeft a).IsHermitian := by
  unfold sigmaDotLeft Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, (pauliDot_isHermitian a).eq,
      Matrix.conjTranspose_one]

/-- `I ⊗ σ·b` is Hermitian. -/
private lemma sigmaDotRight_isHermitian (b : DetectorSetting) :
    (sigmaDotRight b).IsHermitian := by
  unfold sigmaDotRight Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, (pauliDot_isHermitian b).eq,
      Matrix.conjTranspose_one]

/-- Kronecker product identity: `(σ·a ⊗ I) · (I ⊗ σ·b) = σ·a ⊗ σ·b`. -/
private lemma sigmaDotLeft_mul_sigmaDotRight (a b : DetectorSetting) :
    sigmaDotLeft a * sigmaDotRight b = sigmaDotJoint a b := by
  unfold sigmaDotLeft sigmaDotRight sigmaDotJoint
  rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]

/-- The Tsirelson construction vector `α(a, ψ) := (σ·a ⊗ I) ψ`. -/
noncomputable def alphaVec (a : DetectorSetting)
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  Matrix.toEuclideanLin (sigmaDotLeft a) ψ

/-- The Tsirelson construction vector `β(b, ψ) := (I ⊗ σ·b) ψ`. -/
noncomputable def betaVec (b : DetectorSetting)
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  Matrix.toEuclideanLin (sigmaDotRight b) ψ

/-- `‖α(a, ψ)‖ = ‖ψ‖`: the Alice-side Tsirelson vector preserves the
norm of `ψ`, because `σ·a ⊗ I` is a Hermitian involution. -/
lemma norm_alphaVec (a : DetectorSetting)
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) : ‖alphaVec a ψ‖ = ‖ψ‖ := by
  -- ‖T ψ‖² = ⟨T ψ, T ψ⟩ = ⟨ψ, T (T ψ)⟩ = ⟨ψ, ψ⟩ = ‖ψ‖²; norms non-negative.
  have key : ‖alphaVec a ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ _ _ _ _, @norm_sq_eq_re_inner ℂ _ _ _ _]
    congr 1
    show inner ℂ (Matrix.toEuclideanLin (sigmaDotLeft a) ψ)
                 (Matrix.toEuclideanLin (sigmaDotLeft a) ψ)
       = inner ℂ ψ ψ
    rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (sigmaDotLeft a))]
    rw [show (Matrix.toEuclideanLin (sigmaDotLeft a)).adjoint
            = Matrix.toEuclideanLin (sigmaDotLeft a) from by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
              (sigmaDotLeft_isHermitian a).eq]]
    rw [show Matrix.toEuclideanLin (sigmaDotLeft a)
              (Matrix.toEuclideanLin (sigmaDotLeft a) ψ)
          = Matrix.toEuclideanLin (sigmaDotLeft a * sigmaDotLeft a) ψ from by
          rw [Matrix.toLpLin_mul_same]; rfl]
    rw [sigmaDotLeft_sq, Matrix.toLpLin_one]
    rfl
  have h1 : 0 ≤ ‖alphaVec a ψ‖ := norm_nonneg _
  have h2 : 0 ≤ ‖ψ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖alphaVec a ψ‖ - ‖ψ‖), sq_nonneg (‖alphaVec a ψ‖ + ‖ψ‖)]

/-- `‖β(b, ψ)‖ = ‖ψ‖`. -/
lemma norm_betaVec (b : DetectorSetting)
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) : ‖betaVec b ψ‖ = ‖ψ‖ := by
  have key : ‖betaVec b ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ _ _ _ _, @norm_sq_eq_re_inner ℂ _ _ _ _]
    congr 1
    show inner ℂ (Matrix.toEuclideanLin (sigmaDotRight b) ψ)
                 (Matrix.toEuclideanLin (sigmaDotRight b) ψ)
       = inner ℂ ψ ψ
    rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (sigmaDotRight b))]
    rw [show (Matrix.toEuclideanLin (sigmaDotRight b)).adjoint
            = Matrix.toEuclideanLin (sigmaDotRight b) from by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
              (sigmaDotRight_isHermitian b).eq]]
    rw [show Matrix.toEuclideanLin (sigmaDotRight b)
              (Matrix.toEuclideanLin (sigmaDotRight b) ψ)
          = Matrix.toEuclideanLin (sigmaDotRight b * sigmaDotRight b) ψ from by
          rw [Matrix.toLpLin_mul_same]; rfl]
    rw [sigmaDotRight_sq, Matrix.toLpLin_one]
    rfl
  nlinarith [sq_nonneg (‖betaVec b ψ‖ - ‖ψ‖), sq_nonneg (‖betaVec b ψ‖ + ‖ψ‖),
             norm_nonneg (betaVec b ψ), norm_nonneg ψ]

/-- The inner-product identity at the heart of the Tsirelson construction:
`⟨α(a, ψ), β(b, ψ)⟩ = ⟨ψ, (σ·a ⊗ σ·b) ψ⟩`. -/
lemma inner_alphaVec_betaVec
    (a b : DetectorSetting) (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    inner ℂ (alphaVec a ψ) (betaVec b ψ)
      = inner ℂ ψ (Matrix.toEuclideanLin (sigmaDotJoint a b) ψ) := by
  show inner ℂ (Matrix.toEuclideanLin (sigmaDotLeft a) ψ)
               (Matrix.toEuclideanLin (sigmaDotRight b) ψ) = _
  rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (sigmaDotLeft a))]
  rw [show (Matrix.toEuclideanLin (sigmaDotLeft a)).adjoint
          = Matrix.toEuclideanLin (sigmaDotLeft a) from by
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
            (sigmaDotLeft_isHermitian a).eq]]
  rw [show Matrix.toEuclideanLin (sigmaDotLeft a)
            (Matrix.toEuclideanLin (sigmaDotRight b) ψ)
        = Matrix.toEuclideanLin (sigmaDotLeft a * sigmaDotRight b) ψ from by
        rw [Matrix.toLpLin_mul_same]; rfl]
  rw [sigmaDotLeft_mul_sigmaDotRight]

/-- **A6 QM form: Tsirelson upper bound on bipartite Pauli CHSH
expectation.** For any unit `ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)` and
any unit detector settings `a, a', b, b' : DetectorSetting`,
```
|Re⟨ψ, (σ·a ⊗ σ·b)ψ⟩ − Re⟨ψ, (σ·a ⊗ σ·b')ψ⟩ + Re⟨ψ, (σ·a' ⊗ σ·b)ψ⟩
   + Re⟨ψ, (σ·a' ⊗ σ·b')ψ⟩| ≤ 2√2.
```

Proved by the standard Tsirelson construction `α(a, ψ) := (σ·a ⊗ I)ψ`,
`β(b, ψ) := (I ⊗ σ·b)ψ`, followed by the algebraic `chsh_inner_bound`.

**Experimental verification:** Tsirelson 1980, *Lett. Math. Phys.* **4**,
93. Saturation by the singlet (`ψ = singlet`) at canonical angles
(`chsh_singlet_at_optimal_angles`). -/
theorem chsh_qm_tsirelson_bound
    (a a' b b' : DetectorSetting)
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (hψ : ‖ψ‖ = 1) :
    |Complex.re (inner ℂ ψ (Matrix.toEuclideanLin (sigmaDotJoint a b) ψ))
        - Complex.re (inner ℂ ψ (Matrix.toEuclideanLin (sigmaDotJoint a b') ψ))
        + Complex.re (inner ℂ ψ (Matrix.toEuclideanLin (sigmaDotJoint a' b) ψ))
        + Complex.re (inner ℂ ψ (Matrix.toEuclideanLin (sigmaDotJoint a' b') ψ))|
    ≤ 2 * Real.sqrt 2 := by
  rw [← inner_alphaVec_betaVec, ← inner_alphaVec_betaVec,
      ← inner_alphaVec_betaVec, ← inner_alphaVec_betaVec]
  exact chsh_inner_bound (alphaVec a ψ) (alphaVec a' ψ)
    (betaVec b ψ) (betaVec b' ψ)
    (by rw [norm_alphaVec]; exact hψ)
    (by rw [norm_alphaVec]; exact hψ)
    (by rw [norm_betaVec]; exact hψ)
    (by rw [norm_betaVec]; exact hψ)

end Bell
end Empirical
end CSD

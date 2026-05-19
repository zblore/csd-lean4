import CsdLean4.LF3.Singlet.Kernel

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

A6 (Tsirelson upper bound for any pure 2-qubit state) is deferred to
a follow-up commit; this file delivers A1–A5.

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

/-- **Bell classical bound on the CHSH operator** (Bell 1964): under any
local hidden-variable model, `|S| ≤ 2`. -/
def bellClassicalBound : ℝ := 2

/-- **A2: Classical CHSH bound is strictly violated by the quantum
Tsirelson bound.** The numerical gap `2√2 > 2` is the empirical
falsification of local realism realised by the singlet at canonical
angles.

**Experimental verification:** Aspect, Grangier, Roger 1982,
*Phys. Rev. Lett.* **49**, 91 (and many subsequent loophole-free
experiments). -/
theorem chsh_classical_bound_violated : bellClassicalBound < 2 * Real.sqrt 2 := by
  unfold bellClassicalBound
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
bound, future), this constitutes the LF3-side formal record of the
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

end Bell
end Empirical
end CSD

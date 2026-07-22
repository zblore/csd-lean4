/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.Metrology.QuantumFisher

/-!
# Empirical/Metrology A3: the Heisenberg limit (1/N scaling) via the GHZ probe

**Category:** 3-Local (QM-validity metrology layer; reuses the A2 Quantum-Fisher-
Information machinery, no CSD ontology beyond the A1/A2 lineage).

This is **item A3** of `specs/metrology-plan.md`: the Heisenberg-limit comparison.
`N` qubits used as *one entangled GHZ probe* carry `N` times the metrological
information of `N` qubits used as `N` *independent (separable) Ramsey probes*, both
accumulating the same phase `φ`.

## The GHZ probe (this file's Lean content)

The phase-accumulated GHZ state on a genuine `N`-qubit carrier
`EuclideanSpace ℂ (Fin (2^N))` is
`ψ_N(φ) = (1/√2)(|0…0⟩ + e^{iNφ}|1…1⟩)`,
with `|0…0⟩` the all-zeros index `0` and `|1…1⟩` the all-ones index `2^N − 1`. All `N`
qubits flip together, so the collective phase is `Nφ`; only two components are nonzero
(`ghzPhaseVec`). It is genuinely normalized (`ghzPhaseVec_norm`, for `N ≥ 1`; the A2
`fsMetric`/`qfi` definitions are faithful only for unit `ψ`). Its genuine derivative
(only the all-ones component varies) is certified by `ghzPhaseVec_hasDerivAt` via the
chain rule on `φ ↦ exp((N·φ:ℂ)·I)` assembled through the ℝ-linear CLM `ghzSingleRL`
(mirroring A2's `singleRL`/`ramseyVec_hasDerivAt`; it is proved, not asserted). Then:

- `‖dψ_N‖² = N²/2`, `⟪ψ_N, dψ_N⟫ = i·N/2`, so `‖⟪ψ_N,dψ_N⟫‖² = N²/4`;
- `g = N²/2 − N²/4 = N²/4`, hence **`F_Q^GHZ = 4·(N²/4) = N²`** (`ghz_qfi`) — the
  Heisenberg quadratic enhancement. The `N²` comes from the phase being `Nφ`, not from
  the carrier dimension.

## SQL (separable) probe and the Heisenberg advantage

`N` independent Ramsey probes each have `F_Q = 1` (A2's `ramsey_qfi`). The (classical /
quantum) Fisher information is **additive** over independent probes, so
`F_Q^SQL = N·1 = N` (`sqlQFI`; the additivity is the standard fact, with A2's per-probe
`ramsey_qfi = 1` the input — see the `sqlQFI` docstring). Therefore
**`F_Q^GHZ / F_Q^SQL = N²/N = N`** (`heisenberg_advantage`: `N² = N·N`;
`ghz_qfi_div_sql`): the `N`-fold metrological enhancement. Operationally, the quantum
Cramér-Rao bound `Var(φ̂) ≥ 1/(n·F_Q)` over `n` shots gives precision scaling `1/N²`
(Heisenberg, standard deviation `1/N`) for the GHZ probe versus `1/N` (SQL, standard
deviation `1/√N`) for the separable probes.

## What is and is not modelled

`ghzPhaseVec` is the `N`-qubit GHZ-phase *family* and `ghzDeriv` its derivative vector;
`ghz_qfi` is the geometric Quantum Fisher Information of that family (the A2 trajectory
pullback of the Fubini-Study metric). The dynamical `N`-body interaction that *prepares*
the GHZ state, and the physical phase-imprinting Hamiltonian, are **not** modelled (as
in A2: this is the QFI of the state family, single parameter `φ`). `F_Q^GHZ = N²` is the
Heisenberg limit and `F_Q^SQL = N` the standard quantum limit. This reuses A2's
`fsMetric`/`qfi`/`singleRL` idiom verbatim, so the A2 metric infrastructure genuinely
generalizes from the qubit to the `N`-qubit entangled probe. QM-validity layer; the CSD
content is the A1/A2 metrology lineage.
-/

@[expose] public section

open scoped ComplexConjugate

namespace CSD
namespace Empirical
namespace Metrology

/-! ### The GHZ carrier indices: all-zeros `0` and all-ones `2^N − 1` -/

/-- The all-zeros computational-basis index `|0…0⟩` of the `N`-qubit carrier
`EuclideanSpace ℂ (Fin (2^N))`, i.e. `0 : Fin (2^N)`. -/
def ghzZero (N : ℕ) : Fin (2 ^ N) := ⟨0, pow_pos (by norm_num) N⟩

/-- The all-ones computational-basis index `|1…1⟩` of the `N`-qubit carrier, i.e. the top
index `2^N − 1 : Fin (2^N)` (the binary all-ones bitstring). -/
def ghzOne (N : ℕ) : Fin (2 ^ N) := ⟨2 ^ N - 1, Nat.sub_lt (pow_pos (by norm_num) N) one_pos⟩

/-- The all-zeros and all-ones indices are distinct for a genuine `N`-qubit system
(`N ≥ 1`), since then `2^N ≥ 2`. -/
lemma ghzZero_ne_ghzOne {N : ℕ} (hN : 1 ≤ N) : ghzZero N ≠ ghzOne N := by
  apply Fin.ne_of_val_ne
  have h2 : 2 ≤ 2 ^ N := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  simp only [ghzZero, ghzOne]; omega

/-! ### The phase-accumulated GHZ state and its derivative vector -/

/-- The **phase-accumulated GHZ state** `ψ_N(φ) = (1/√2)(|0…0⟩ + e^{iNφ}|1…1⟩)` on the
genuine `N`-qubit carrier `EuclideanSpace ℂ (Fin (2^N))`. Only the all-zeros (`ghzZero`)
and all-ones (`ghzOne`) components are nonzero; the collective phase `Nφ` reflects all `N`
qubits flipping together. -/
noncomputable def ghzPhaseVec (N : ℕ) (φ : ℝ) : EuclideanSpace ℂ (Fin (2 ^ N)) :=
  EuclideanSpace.single (ghzZero N) ((1 / Real.sqrt 2 : ℝ) : ℂ)
    + EuclideanSpace.single (ghzOne N)
        (((1 / Real.sqrt 2 : ℝ) : ℂ) * Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I))

/-- The **GHZ derivative vector** `dψ_N(φ) = (i·N·e^{iNφ}/√2)·|1…1⟩`: only the all-ones
component varies with `φ`. Certified to be the genuine derivative of `ghzPhaseVec` in
`ghzPhaseVec_hasDerivAt`. -/
noncomputable def ghzDeriv (N : ℕ) (φ : ℝ) : EuclideanSpace ℂ (Fin (2 ^ N)) :=
  EuclideanSpace.single (ghzOne N)
    (((1 / Real.sqrt 2 : ℝ) : ℂ)
      * (Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I) * ((N : ℂ) * Complex.I)))

/-! ### Normalisation -/

/-- `‖e^{iNφ}‖ = 1`. -/
lemma norm_exp_phase_N (N : ℕ) (φ : ℝ) :
    ‖Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp, Complex.mul_I_re]
  simp [Complex.mul_im, Complex.natCast_im, Complex.ofReal_im, Complex.natCast_re,
    Complex.ofReal_re]

/-- **`‖ghzPhaseVec N φ‖ = 1`** for `N ≥ 1`: the two nonzero components each have squared
modulus `1/2`. Load-bearing: the A2 `fsMetric`/`qfi` definitions are faithful only for a
normalized state. -/
theorem ghzPhaseVec_norm (N : ℕ) (hN : 1 ≤ N) (φ : ℝ) : ‖ghzPhaseVec N φ‖ = 1 := by
  have hne := ghzZero_ne_ghzOne hN
  have c0val : ghzPhaseVec N φ (ghzZero N) = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
    simp [ghzPhaseVec, Ne.symm hne]
  have c1val : ghzPhaseVec N φ (ghzOne N)
      = ((1 / Real.sqrt 2 : ℝ) : ℂ) * Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I) := by
    simp [ghzPhaseVec, hne]
  have czero : ∀ k, k ≠ ghzZero N → k ≠ ghzOne N → ghzPhaseVec N φ k = 0 := by
    intro k hk0 hk1; simp [ghzPhaseVec, hk0, hk1]
  have e0 : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < 1 / Real.sqrt 2 by positivity),
        div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have e1 : ‖((1 / Real.sqrt 2 : ℝ) : ℂ) * Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I)‖ ^ 2
      = 1 / 2 := by
    rw [norm_mul, norm_exp_phase_N, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < 1 / Real.sqrt 2 by positivity),
        div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [EuclideanSpace.norm_eq,
      Fintype.sum_eq_add (ghzZero N) (ghzOne N) hne
        (fun k h => by simp [czero k h.1 h.2])]
  dsimp only
  rw [c0val, c1val, e0, e1, show (1 : ℝ) / 2 + 1 / 2 = 1 from by norm_num, Real.sqrt_one]

/-! ### The genuine derivative -/

/-- `EuclideanSpace.single i`, packaged as an **ℝ-linear** continuous map. Built ℝ-linear
from the start so composing the ℝ-valued `HasDerivAt` of a scalar trajectory with it needs
no `restrictScalars` (which triggers the ℝ-ℂ-`EuclideanSpace` module diamond). The
`Fin (2^N)`-indexed analogue of A2's `singleRL`. -/
noncomputable def ghzSingleRL {N : ℕ} (i : Fin (2 ^ N)) :
    ℂ →L[ℝ] EuclideanSpace ℂ (Fin (2 ^ N)) :=
  LinearMap.toContinuousLinearMap
    { toFun := EuclideanSpace.single i
      map_add' := fun x y => by
        ext j; simp only [PiLp.single_apply, PiLp.add_apply]; split_ifs <;> simp
      map_smul' := fun (r : ℝ) x => by
        ext j; simp only [PiLp.single_apply, PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }

/-- Componentwise lift: a scalar `HasDerivAt a a' φ` lifts to a vector `HasDerivAt` of the
single-supported vector, via `ghzSingleRL`. The `Fin (2^N)` analogue of A2's
`hasDerivAt_single`. -/
lemma hasDerivAt_ghzSingle {N : ℕ} (i : Fin (2 ^ N)) {a : ℝ → ℂ} {a' : ℂ} {φ : ℝ}
    (h : HasDerivAt a a' φ) :
    HasDerivAt (fun φ => EuclideanSpace.single i (a φ)) (EuclideanSpace.single i a') φ := by
  have := ((ghzSingleRL i).hasFDerivAt (x := a φ)).comp_hasDerivAt φ h
  exact this

/-- **`ghzDeriv` is the genuine derivative of `ghzPhaseVec`.** The all-zeros component is
constant; the all-ones component `φ ↦ e^{iNφ}/√2` has derivative `i·N·e^{iNφ}/√2`, proved
via the chain rule `HasDerivAt.cexp` on `φ ↦ exp((N·φ:ℂ)·I)` and assembled through
`ghzSingleRL`. This earns the "derivative" label; it is not asserted. Mirrors A2's
`ramseyVec_hasDerivAt`. -/
theorem ghzPhaseVec_hasDerivAt (N : ℕ) (φ : ℝ) :
    HasDerivAt (ghzPhaseVec N) (ghzDeriv N φ) φ := by
  have h0 : HasDerivAt (fun φ : ℝ => ((φ : ℂ))) 1 φ :=
    Complex.ofRealCLM.hasDerivAt (x := φ)
  have h1 : HasDerivAt (fun φ : ℝ => (N : ℂ) * (φ : ℂ)) (N : ℂ) φ := by
    simpa using h0.const_mul (N : ℂ)
  have hlin : HasDerivAt (fun φ : ℝ => (N : ℂ) * (φ : ℂ) * Complex.I) ((N : ℂ) * Complex.I) φ := by
    simpa using h1.mul_const Complex.I
  have hexp : HasDerivAt (fun φ : ℝ => Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I))
      (Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I) * ((N : ℂ) * Complex.I)) φ := hlin.cexp
  have ha : HasDerivAt
      (fun φ : ℝ => ((1 / Real.sqrt 2 : ℝ) : ℂ) * Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I))
      (((1 / Real.sqrt 2 : ℝ) : ℂ)
        * (Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I) * ((N : ℂ) * Complex.I))) φ :=
    hexp.const_mul _
  have Dconst : HasDerivAt
      (fun _ : ℝ => EuclideanSpace.single (ghzZero N) ((1 / Real.sqrt 2 : ℝ) : ℂ)) 0 φ :=
    hasDerivAt_const φ _
  have hsum := Dconst.add (hasDerivAt_ghzSingle (ghzOne N) ha)
  rw [zero_add] at hsum
  exact hsum

/-! ### The headline Heisenberg QFI: `F_Q^GHZ = N²` -/

/-- **`‖dψ_N‖² = N²/2`** for the GHZ derivative vector. -/
lemma ghzDeriv_normSq (N : ℕ) (φ : ℝ) : ‖ghzDeriv N φ‖ ^ 2 = (N : ℝ) ^ 2 / 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [ghzDeriv, PiLp.norm_single, norm_mul, norm_mul, norm_mul, norm_exp_phase_N,
      Complex.norm_real, Real.norm_eq_abs, RCLike.norm_natCast, Complex.norm_I,
      abs_of_pos (show (0 : ℝ) < 1 / Real.sqrt 2 by positivity),
      show (1 / Real.sqrt 2) * (1 * ((N : ℝ) * 1)) = (N : ℝ) / Real.sqrt 2 from by ring,
      div_pow, h2]

/-- **`⟪ψ_N, dψ_N⟫ = i·N/2`** for the GHZ state and its derivative. The cross term
collapses via `e^{iNφ}·conj(e^{iNφ}) = 1`. -/
lemma ghz_inner (N : ℕ) (hN : 1 ≤ N) (φ : ℝ) :
    (inner ℂ (ghzPhaseVec N φ) (ghzDeriv N φ) : ℂ) = (N : ℂ) * Complex.I / 2 := by
  rw [ghzDeriv, EuclideanSpace.inner_single_right]
  rw [show (ghzPhaseVec N φ).ofLp (ghzOne N)
        = ((1 / Real.sqrt 2 : ℝ) : ℂ) * Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I)
      from by simp [ghzPhaseVec, ghzZero_ne_ghzOne hN]]
  rw [map_mul, Complex.conj_ofReal]
  have hee : Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I)
      * (starRingEnd ℂ) (Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add,
        show ((N : ℂ) * (φ : ℂ) * Complex.I)
            + (starRingEnd ℂ) ((N : ℂ) * (φ : ℂ) * Complex.I) = 0
          from by rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
            Complex.conj_natCast]; ring,
        Complex.exp_zero]
  have hc0 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    have hr : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
    rw [← Complex.ofReal_mul, hr]; norm_num
  linear_combination ((N : ℂ) * Complex.I * (Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I)
      * (starRingEnd ℂ) (Complex.exp ((N : ℂ) * (φ : ℂ) * Complex.I)))) * hc0
    + ((N : ℂ) * Complex.I / 2) * hee

/-- **The GHZ Quantum Fisher Information `F_Q^GHZ = N²`** (the Heisenberg limit). With
`‖dψ‖² = N²/2` and `‖⟪ψ,dψ⟫‖² = N²/4`: `g = N²/4`, so `F_Q = 4·(N²/4) = N²`. The `N²` is
the quadratic enhancement carried by the collective phase `Nφ`. -/
theorem ghz_qfi (N : ℕ) (hN : 1 ≤ N) (φ : ℝ) :
    qfi (ghzPhaseVec N φ) (ghzDeriv N φ) = (N : ℝ) ^ 2 := by
  have hin2 : ‖(inner ℂ (ghzPhaseVec N φ) (ghzDeriv N φ) : ℂ)‖ ^ 2 = (N : ℝ) ^ 2 / 4 := by
    rw [ghz_inner N hN, norm_div, norm_mul, RCLike.norm_natCast, Complex.norm_I, mul_one,
        RCLike.norm_two, div_pow]
    norm_num
  rw [qfi, fsMetric, ghzDeriv_normSq, hin2]; ring

/-! ### The SQL (separable) probe and the Heisenberg advantage -/

/-- **The standard-quantum-limit QFI `F_Q^SQL = N`.** `N` independent Ramsey probes, each
with per-probe `F_Q = 1` (A2's `ramsey_qfi`); the (classical/quantum) Fisher information is
**additive** over independent probes, so `F_Q^SQL = N·1 = N`. (Additivity is the standard
fact for independent probes; the per-probe input is A2's `ramsey_qfi = 1`. We record the
value `N` rather than re-deriving general tensor-product QFI additivity.) -/
def sqlQFI (N : ℕ) : ℝ := (N : ℝ) * 1

/-- `F_Q^SQL = N`. -/
@[simp] lemma sqlQFI_eq (N : ℕ) : sqlQFI N = (N : ℝ) := by rw [sqlQFI, mul_one]

/-- **The Heisenberg advantage: `F_Q^GHZ = N · F_Q^SQL`** (i.e. `N² = N·N`), the `N`-fold
metrological enhancement. The entangled GHZ probe carries `N` times the per-shot
information of the `N` separable probes. -/
theorem heisenberg_advantage (N : ℕ) (hN : 1 ≤ N) (φ : ℝ) :
    qfi (ghzPhaseVec N φ) (ghzDeriv N φ) = (N : ℝ) * sqlQFI N := by
  rw [ghz_qfi N hN, sqlQFI]; ring

/-- **The Heisenberg enhancement ratio `F_Q^GHZ / F_Q^SQL = N`** (for `N ≥ 1`).
Operationally: precision `Var(φ̂) ≥ 1/(n·F_Q)` scales as `1/N²` (Heisenberg) for the GHZ
probe versus `1/N` (SQL) for the separable probes. -/
theorem ghz_qfi_div_sql (N : ℕ) (hN : 1 ≤ N) (φ : ℝ) :
    qfi (ghzPhaseVec N φ) (ghzDeriv N φ) / sqlQFI N = (N : ℝ) := by
  rw [ghz_qfi N hN, sqlQFI, mul_one]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [pow_two, mul_div_assoc, div_self hN0, mul_one]

end Metrology
end Empirical
end CSD

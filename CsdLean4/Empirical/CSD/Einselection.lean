import CsdLean4.LF6.Decoherence
import CsdLean4.Empirical.QM.Gates.SingleQubit

/-!
# Empirical/CSD: einselection / pointer-basis selection (Build 15a)

**Category:** 6-Local (the open-system / decoherence stratum of D1; the first
einselection result on the LF6-B decoherence machinery).

Decoherence (LF6-B.1, `LF6/Decoherence.lean`) does not merely make the system
state mixed: it **selects a preferred basis**. The reduced state
`decohereReduced ψ = partialTraceRight (V |ψ⟩⟨ψ| Vᴴ)` is *diagonal* in the
measurement (pointer) basis `{eⱼ}` — its off-diagonal coherences vanish there
(`decoherence_offdiagonal_vanish`) — but its coherences **persist** in a rotated
basis. This basis-selectivity is Zurek's einselection: the "why a preferred
basis" content.

## The qubit computation (concrete witness)

For `N = 2`, `decohereReduced ψ = diagonal (p₀, p₁)` with `pⱼ = ‖⟨eⱼ,ψ⟩‖²`
(= `ψⱼ · star ψⱼ`, `decohereReduced_eq_diagonal`). Conjugating by the Hadamard
`qmH` rotates into the `{(e₀±e₁)/√2}` basis:

```
qmH · diag(p₀,p₁) · qmH = (1/2) · !![p₀+p₁, p₀−p₁; p₀−p₁, p₀+p₁],
```

so the rotated-basis off-diagonal entry `(0,1)` equals `(p₀ − p₁)/2`. This is
**nonzero whenever `p₀ ≠ p₁`** (`decohere_hadamard_offDiag` +
`decohere_not_diagonal_in_rotated_basis`). The pointer basis `{e₀,e₁}` is
genuinely einselected: it is the one basis in which the decohered state is
diagonal.

The `p₀ ≠ p₁` hypothesis is **load-bearing and honest**: at `p₀ = p₁` the
reduced state is the fully mixed `(1/2)·I`, which is diagonal in *every* basis,
so there is no preferred basis to select. Einselection is the statement that for
a *generic* superposition (distinct Born weights) the diagonalising basis is
unique.

## Deliverables

- `decohere_hadamard_offDiag` — the rotated off-diagonal value
  `(qmH · ρ_red · qmH) 0 1 = (ψ₀·star ψ₀ − ψ₁·star ψ₁)/2`, every qubit `ψ`
  (computed, not asserted).
- `decohere_diagonal_in_pointer_basis` — `ρ_red` is `Matrix.diagonal` in `{eⱼ}`
  (restates `decohereReduced_eq_diagonal`): the pointer basis is special.
- `decohere_not_diagonal_in_rotated_basis` (THE einselection witness) — for any
  qubit with `p₀ ≠ p₁`, the Hadamard-rotated reduced state has a nonzero `(0,1)`
  off-diagonal: coherence persists in the rotated basis.
- `einselectionWitness` — a concrete superposition `(2,1)` with `p₀ = 4 ≠ 1 = p₁`
  (non-vacuity), and `einselectionWitness_offDiag` — its rotated off-diagonal is
  `3/2 ≠ 0`.
- `einselection` (capstone) — diagonal in the pointer basis (off-diag `0`) AND
  off-diagonal `3/2 ≠ 0` in the Hadamard rotation, for the witness.

## Follow-up (#34): the degeneracy boundary + general `N`

**Part A — the degeneracy boundary (qubit).** Einselection has a sharp boundary at
`p₀ = p₁`. `decohere_hadamard_offDiag_ne_zero_iff` makes it crisp: the rotated-basis
coherence `(p₀ − p₁)/2` is nonzero IFF `p₀ ≠ p₁`. At the degenerate locus
`p₀ = p₁` the reduced state is `(ψ₀·star ψ₀) • I` (`decohere_degenerate_scalar`), and
for unit `ψ` exactly the maximally mixed `(1/2)·I` (`decohere_degenerate_half`,
witness `degenerateWitness_decohere_half`). Being `c • I` it is invariant under ANY
unitary conjugation (`decohere_degenerate_basis_invariant`), so NO basis is selected:
the einselection-FAILS side (`einselection_degenerate_boundary`).

**Part B — general `N`.** The dephasing channel `decohereReducedN ρ := diagonal
(fun i => ρ i i)` zeroes off-diagonal coherences and keeps the diagonal pointer
populations for any `N` (`einselectionN`); it restricts to the qubit `decohereReduced`
on a pure-state density (`decohereReducedN_outerProduct`), and genuinely acts
(off-diagonal nonzero before, `0` after: `decohereReducedN_acts_nontrivial`). The
degeneracy boundary lifts: equal populations `ρ i i = 1/N` give `(1/N)·I`
(`decohereReducedN_degenerate_scalar`, witness `decohereReducedN_maximally_mixed`),
basis-invariant (`einselectionN_degenerate`).

The pointer basis is the COMPUTATIONAL basis by construction of the dephasing
channel; the deeper ontic einselection-from-Σ-dynamics origin stays gated to the
entangled tier / D1.

## Honest scope and the contrast with #29 (`LF4/TypicalityForcing.lean`)

Einselection here is the **basis selection imposed by the de-isolation /
partial-trace in the pointer basis** (LF6-B). It contrasts sharply with the
typicality layer: `fubiniStudy_forced_by_symmetry` (#29) shows the Fubini–Study
typicality measure is the *unique* `U(N)`-invariant probability measure — it is
basis-**covariant** and picks **no** basis. The preferred basis therefore does
**not** come from the symmetric typicality / sector structure; it comes from the
**measurement context** — which basis the de-isolation couples to and traces in.
Einselection is the symmetry-breaking-by-context layered on the symmetric
substrate.

This is the QM-validity / open-system reading; the CSD content is the
de-isolation reading of which basis is selected. **Honest scope:** single-system;
the pointer basis is the de-isolation's computational basis (the context's
choice). Deriving *which* basis a given physical environment selects (Zurek's
predictability-sieve dynamics, a Hamiltonian-level account) is **not** modelled —
here the basis is the de-isolation's by construction, and the theorem is that
decoherence is basis-**selective** (diagonal in exactly one basis up to
degeneracy), not that the basis is derived from an environment Hamiltonian.

All exports are foundational-triple-only (off `busch_effect_gleason`): the result
is concrete `Matrix` arithmetic on `Fin 2` over the LF6-B `decohereReduced`.
-/

open Matrix
open CSD.LF2 CSD.LF6 CSD.Empirical.QM.Gates

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Einselection

/-! ### The rotated-basis off-diagonal (the core computation) -/

/-- `((√2)⁻¹)² = 1/2`, the Hadamard normalisation squared (cf. `qmH_mul_self`). -/
private lemma sqrt_two_inv_sq : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (1 / 2 : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `z · z̄ = (‖z‖ : ℂ)²` (the diagonal density entry as the Born weight). -/
private lemma mul_star_normSq (z : ℂ) : z * star z = ((‖z‖ : ℂ)) ^ 2 := by
  rw [← starRingEnd_apply]
  exact RCLike.mul_conj z

/-- `star (↑r) = ↑r` for a real scalar embedded in `ℂ`. -/
private lemma star_ofReal' (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [← starRingEnd_apply]
  exact Complex.conj_ofReal r

/-- A constant diagonal is a scalar multiple of the identity:
`diagonal (fun _ => c) = c • 1`. The shape of the maximally mixed / degenerate
reduced state. -/
private lemma diagonal_const_eq_smul_one {N : ℕ} (c : ℂ) :
    Matrix.diagonal (fun _ : Fin N => c) = c • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.diagonal_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The Hadamard-rotated off-diagonal of the decohered qubit state.**
`(qmH · decohereReduced ψ · qmH) 0 1 = (ψ₀·star ψ₀ − ψ₁·star ψ₁)/2 = (p₀ − p₁)/2`.
Computed from `decohereReduced_eq_diagonal` + concrete `Fin 2` matrix arithmetic:
`qmH = s·!![1,1;1,-1]` with `s² = 1/2`, and `!![1,1;1,-1]·diag(p₀,p₁)·!![1,1;1,-1]`
has `(0,1)` entry `p₀ − p₁`. -/
theorem decohere_hadamard_offDiag (ψ : EuclideanSpace ℂ (Fin 2)) :
    (qmH * decohereReduced ψ * qmH) 0 1
      = (ψ 0 * star (ψ 0) - ψ 1 * star (ψ 1)) / 2 := by
  rw [decohereReduced_eq_diagonal, qmH, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, sqrt_two_inv_sq, Matrix.smul_apply, smul_eq_mul]
  have hM : (!![(1 : ℂ), 1; 1, -1] * Matrix.diagonal (fun i => ψ i * star (ψ i))
              * !![(1 : ℂ), 1; 1, -1]) 0 1
            = ψ 0 * star (ψ 0) - ψ 1 * star (ψ 1) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Fin.isValue,
      Fin.reduceEq, if_true, if_false, mul_zero, add_zero, zero_add]
    rw [show !![(1 : ℂ), 1; 1, -1] 0 0 = 1 from rfl,
      show !![(1 : ℂ), 1; 1, -1] 0 1 = 1 from rfl,
      show !![(1 : ℂ), 1; 1, -1] 1 1 = -1 from rfl]
    ring
  rw [hM]; ring

/-! ### (1) Diagonal in the pointer basis -/

/-- **The decohered state is diagonal in the pointer basis `{eⱼ}`** (restates
`decohereReduced_eq_diagonal`): `decohereReduced ψ = diagonal (j ↦ ψⱼ·star ψⱼ)`.
The off-diagonal coherences vanish (`decoherence_offdiagonal_vanish`) — the pointer
basis is the special, diagonalising basis. -/
theorem decohere_diagonal_in_pointer_basis {N : ℕ} [NeZero N] (ψ : EuclideanSpace ℂ (Fin N)) :
    decohereReduced ψ = Matrix.diagonal (fun i => ψ i * star (ψ i)) :=
  decohereReduced_eq_diagonal ψ

/-! ### (2) NOT diagonal in the Hadamard-rotated basis (the einselection witness) -/

/-- **THE einselection witness: coherence persists in the rotated basis.**
For any qubit `ψ` whose two Born weights differ (`p₀ ≠ p₁`, i.e.
`ψ₀·star ψ₀ ≠ ψ₁·star ψ₁`), the Hadamard-conjugated reduced state has a **nonzero**
`(0,1)` off-diagonal `(p₀ − p₁)/2`. So the decohered state is diagonal in the
pointer basis but NOT in the Hadamard-rotated basis: the pointer basis is genuinely
selected, not arbitrary. The `p₀ ≠ p₁` hypothesis is load-bearing — at `p₀ = p₁`
the state is fully mixed and diagonal in every basis. -/
theorem decohere_not_diagonal_in_rotated_basis (ψ : EuclideanSpace ℂ (Fin 2))
    (hp : ψ 0 * star (ψ 0) ≠ ψ 1 * star (ψ 1)) :
    (qmH * decohereReduced ψ * qmH) 0 1 ≠ 0 := by
  rw [decohere_hadamard_offDiag, div_ne_zero_iff]
  exact ⟨sub_ne_zero.mpr hp, by norm_num⟩

/-! ### Concrete non-vacuity witness -/

/-- A concrete qubit superposition `(2, 1)` with distinct Born weights
`p₀ = 4 ≠ 1 = p₁` (unnormalised; the einselection off-diagonal is scale-covariant
and its non-vanishing depends only on `p₀ ≠ p₁`). -/
noncomputable def einselectionWitness : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (2 : ℂ) + EuclideanSpace.single 1 (1 : ℂ)

@[simp] lemma einselectionWitness_apply_zero : einselectionWitness 0 = 2 := by
  simp [einselectionWitness]

@[simp] lemma einselectionWitness_apply_one : einselectionWitness 1 = 1 := by
  simp [einselectionWitness]

/-- The witness has distinct Born weights: `p₀ = 4 ≠ 1 = p₁`. Non-vacuity for
`decohere_not_diagonal_in_rotated_basis`. -/
lemma einselectionWitness_weights_ne :
    einselectionWitness 0 * star (einselectionWitness 0)
      ≠ einselectionWitness 1 * star (einselectionWitness 1) := by
  simp only [einselectionWitness_apply_zero, einselectionWitness_apply_one, star_one,
    star_ofNat]
  norm_num

/-- **The witness's rotated off-diagonal is `3/2 ≠ 0`.** Concrete value of the
einselection coherence in the Hadamard-rotated basis: `(p₀ − p₁)/2 = (4 − 1)/2 = 3/2`. -/
theorem einselectionWitness_offDiag :
    (qmH * decohereReduced einselectionWitness * qmH) 0 1 = 3 / 2 := by
  rw [decohere_hadamard_offDiag, einselectionWitness_apply_zero, einselectionWitness_apply_one,
    star_one, star_ofNat]
  norm_num

/-! ### Capstone -/

/-- **The einselection capstone: decoherence selects the pointer basis `{e₀,e₁}`.**
For the witness superposition (distinct Born weights):

1. **diagonal in the pointer basis** — `decohereReduced einselectionWitness 0 1 = 0`
   (`decoherence_offdiagonal_vanish`): the pointer basis is the diagonalising one;
2. **off-diagonal in the Hadamard rotation** —
   `(qmH · ρ_red · qmH) 0 1 = 3/2` (`einselectionWitness_offDiag`);
3. **and it is nonzero** — coherence persists in the rotated basis, so the pointer
   basis is genuinely selected.

This is the "why a preferred basis" result: decoherence is basis-**selective**.
The selected basis is the de-isolation's pointer (computational) basis — the
**measurement context's** choice — NOT the symmetric Fubini–Study typicality
(`LF4.fubiniStudy_forced_by_symmetry`, #29: the unique `U(N)`-invariant law,
basis-COVARIANT, picks no basis). Einselection is symmetry-breaking-by-context on
the symmetric substrate. Honest scope: single-system; the basis is posited as the
de-isolation's context, not derived from an environment Hamiltonian. -/
theorem einselection :
    decohereReduced einselectionWitness 0 1 = 0
    ∧ (qmH * decohereReduced einselectionWitness * qmH) 0 1 = 3 / 2
    ∧ (qmH * decohereReduced einselectionWitness * qmH) 0 1 ≠ 0 := by
  refine ⟨decoherence_offdiagonal_vanish einselectionWitness (by decide), einselectionWitness_offDiag, ?_⟩
  rw [einselectionWitness_offDiag]; norm_num

/-! ### Part A: the degeneracy boundary of einselection (qubit)

`decohere_hadamard_offDiag` shows the rotated-basis off-diagonal is exactly the
populations difference over two, `(p₀ − p₁)/2`. So einselection has a sharp
boundary: it **selects** the pointer basis iff `p₀ ≠ p₁`, and **degenerates**
exactly at `p₀ = p₁`, where the reduced state is the maximally mixed `(1/2)·I` —
a scalar multiple of the identity, invariant under any unitary conjugation, so NO
basis is preferred. -/

/-- **The off-diagonal vanishes in the rotated basis iff the populations are
equal.** Makes the einselection boundary crisp: the rotated-basis coherence
`(qmH · ρ_red · qmH) 0 1 = (p₀ − p₁)/2` is nonzero exactly when `p₀ ≠ p₁`. -/
theorem decohere_hadamard_offDiag_ne_zero_iff (ψ : EuclideanSpace ℂ (Fin 2)) :
    (qmH * decohereReduced ψ * qmH) 0 1 ≠ 0
      ↔ ψ 0 * star (ψ 0) ≠ ψ 1 * star (ψ 1) := by
  rw [decohere_hadamard_offDiag, div_ne_zero_iff]
  constructor
  · rintro ⟨h, _⟩; exact sub_ne_zero.mp h
  · intro h; exact ⟨sub_ne_zero.mpr h, by norm_num⟩

/-- **The degenerate case: at `p₀ = p₁` the rotated off-diagonal is `0`** — the
same as the computational basis. So at equal populations the Hadamard-rotated
state is *also* diagonal: the pointer basis is not distinguished from the rotated
one. The einselection-FAILS side (contrast `decohere_not_diagonal_in_rotated_basis`). -/
theorem decohere_degenerate_hadamard_offDiag_zero (ψ : EuclideanSpace ℂ (Fin 2))
    (hp : ψ 0 * star (ψ 0) = ψ 1 * star (ψ 1)) :
    (qmH * decohereReduced ψ * qmH) 0 1 = 0 := by
  rw [decohere_hadamard_offDiag, hp, sub_self, zero_div]

/-- **The degenerate reduced state is a scalar multiple of the identity.** At
equal populations `p₀ = p₁`, `decohereReduced ψ = (ψ₀·star ψ₀) • 1`. Being
`c • I` it is invariant under any unitary conjugation
(`decohere_degenerate_basis_invariant`), so no basis is einselected. -/
theorem decohere_degenerate_scalar (ψ : EuclideanSpace ℂ (Fin 2))
    (hp : ψ 0 * star (ψ 0) = ψ 1 * star (ψ 1)) :
    decohereReduced ψ = (ψ 0 * star (ψ 0)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [decohereReduced_eq_diagonal]
  have hfun : (fun i : Fin 2 => ψ i * star (ψ i))
      = (fun _ : Fin 2 => ψ 0 * star (ψ 0)) := by
    funext i
    fin_cases i
    · rfl
    · exact hp.symm
  rw [hfun, diagonal_const_eq_smul_one]

/-- **The normalised degenerate state is exactly `(1/2)·I`** (the maximally mixed
qubit). For a unit `ψ` with equal populations `p₀ = p₁`, the dephased reduced
state is `(1/2) • 1`. (`p₀ + p₁ = ‖ψ‖² = 1` and `p₀ = p₁` force `p₀ = 1/2`.) -/
theorem decohere_degenerate_half (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1)
    (hp : ψ 0 * star (ψ 0) = ψ 1 * star (ψ 1)) :
    decohereReduced ψ = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hsum : ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 = 1 := by
    have h := CSD.LF4.euclidean_norm_sq_eq_sum ψ
    rw [Fin.sum_univ_two, hψ, one_pow] at h
    linarith
  have hreal : ‖ψ 0‖ ^ 2 = ‖ψ 1‖ ^ 2 := by
    have h2 : ((‖ψ 0‖ : ℂ)) ^ 2 = ((‖ψ 1‖ : ℂ)) ^ 2 := by
      rw [← mul_star_normSq, ← mul_star_normSq]; exact hp
    exact_mod_cast h2
  have hhalf : ‖ψ 0‖ ^ 2 = 1 / 2 := by linarith
  rw [decohere_degenerate_scalar ψ hp]
  congr 1
  rw [mul_star_normSq, ← Complex.ofReal_pow, hhalf]
  norm_num

/-- **Basis-invariance of a scalar matrix (general `N`).** `U · (c • I) · Uᴴ = c • I`
for any `U` with `U Uᴴ = 1`. This is the einselection-degenerates statement: at the
degenerate locus the reduced state is `c • I` (`decohere_degenerate_scalar`), so
conjugation by ANY unitary leaves it unchanged — no basis is preferred. -/
theorem decohere_degenerate_basis_invariant {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (hU : U * Uᴴ = 1) (c : ℂ) :
    U * (c • (1 : Matrix (Fin N) (Fin N) ℂ)) * Uᴴ
      = c • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hU]

/-! ### Concrete degenerate witness -/

/-- A concrete normalised qubit with EQUAL populations `p₀ = p₁ = 1/2`:
`(1/√2)(e₀ + e₁)`. Non-vacuity for the degeneracy boundary. -/
noncomputable def degenerateWitness : EuclideanSpace ℂ (Fin 2) :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
    • (EuclideanSpace.single 0 (1 : ℂ) + EuclideanSpace.single 1 (1 : ℂ))

@[simp] lemma degenerateWitness_apply_zero :
    degenerateWitness 0 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  simp [degenerateWitness]

@[simp] lemma degenerateWitness_apply_one :
    degenerateWitness 1 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  simp [degenerateWitness]

/-- The witness has equal populations `p₀ = p₁` (the degenerate locus). -/
lemma degenerateWitness_degenerate :
    degenerateWitness 0 * star (degenerateWitness 0)
      = degenerateWitness 1 * star (degenerateWitness 1) := by
  rw [degenerateWitness_apply_zero, degenerateWitness_apply_one]

/-- **The witness decoheres to `(1/2)·I`** (the maximally mixed qubit). Concrete
instance of `decohere_degenerate_half`, computed not asserted. -/
theorem degenerateWitness_decohere_half :
    decohereReduced degenerateWitness = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [decohere_degenerate_scalar _ degenerateWitness_degenerate]
  congr 1
  rw [degenerateWitness_apply_zero, star_ofReal', ← Complex.ofReal_mul,
    show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) from by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num]
  norm_num

/-- **The qubit degeneracy-boundary capstone.** For the equal-population witness:

1. `decohereReduced = (1/2)·I` — the maximally mixed scalar state
   (`degenerateWitness_decohere_half`);
2. the Hadamard-rotated off-diagonal is `0` — SAME as the computational basis, so
   the rotated basis is not distinguished (`decohere_degenerate_hadamard_offDiag_zero`);
3. the computational-basis off-diagonal is `0` (`decoherence_offdiagonal_vanish`);
4. conjugation by ANY unitary leaves the state unchanged
   (`decohere_degenerate_basis_invariant`): no basis is einselected.

This is the einselection-FAILS side, sharply contrasting `einselection` (where
`p₀ ≠ p₁` and the pointer basis IS selected). The boundary is exactly `p₀ = p₁`
(`decohere_hadamard_offDiag_ne_zero_iff`). -/
theorem einselection_degenerate_boundary :
    decohereReduced degenerateWitness = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ∧ (qmH * decohereReduced degenerateWitness * qmH) 0 1 = 0
    ∧ decohereReduced degenerateWitness 0 1 = 0
    ∧ ∀ U : Matrix (Fin 2) (Fin 2) ℂ, U * Uᴴ = 1 →
        U * decohereReduced degenerateWitness * Uᴴ = decohereReduced degenerateWitness := by
  refine ⟨degenerateWitness_decohere_half,
    decohere_degenerate_hadamard_offDiag_zero _ degenerateWitness_degenerate,
    decoherence_offdiagonal_vanish _ (by decide), fun U hU => ?_⟩
  rw [degenerateWitness_decohere_half]
  exact decohere_degenerate_basis_invariant U hU (1 / 2)

/-! ### Part B: general-`N` einselection (lift off the qubit)

The dephasing channel `decohereReducedN ρ := diagonal (fun i => ρ i i)` zeroes the
off-diagonal coherences of any density `ρ` and keeps the diagonal pointer-basis
populations, for any `N`. The computational basis is the pointer basis. The
degeneracy boundary lifts too: if all populations are equal (`ρ i i = 1/N`), the
channel output is `(1/N)·I`, basis-invariant, einselection degenerates. -/

/-- **The general-`N` dephasing channel (pointer-basis selection).** Zeroes the
off-diagonal entries of a density `ρ`, keeping the diagonal (the pointer
populations). The computational basis is the pointer basis by construction. -/
noncomputable def decohereReducedN {N : ℕ} (ρ : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => ρ i i)

/-- **Off-diagonals killed (einselection, general `N`).** `i ≠ j ⇒ (decohereReducedN ρ) i j = 0`. -/
theorem decohereReducedN_offDiag_zero {N : ℕ} (ρ : Matrix (Fin N) (Fin N) ℂ)
    {i j : Fin N} (h : i ≠ j) : decohereReducedN ρ i j = 0 := by
  show Matrix.diagonal (fun i => ρ i i) i j = 0
  rw [Matrix.diagonal_apply, if_neg h]

/-- **Diagonal preserved (the pointer populations).** `(decohereReducedN ρ) i i = ρ i i`. -/
theorem decohereReducedN_diagonal {N : ℕ} (ρ : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    decohereReducedN ρ i i = ρ i i := by
  show Matrix.diagonal (fun i => ρ i i) i i = ρ i i
  rw [Matrix.diagonal_apply, if_pos rfl]

/-- **General-`N` einselection.** The dephasing channel kills off-diagonals and
preserves the diagonal pointer populations: the computational basis is the pointer
basis. Note: stated alone this is definitional (`decohereReducedN ρ := diagonal (ρ i i)`,
so "off-diagonal of a diagonal is zero"); the einselection CONTENT - that the channel
genuinely acts on a coherent state - lives in `decohereReducedN_acts_nontrivial`
(off-diagonal nonzero before, `0` after) and `decohereReducedN_outerProduct` (the
restriction to the derived qubit `decohereReduced`). -/
theorem einselectionN {N : ℕ} (ρ : Matrix (Fin N) (Fin N) ℂ) :
    (∀ i j, i ≠ j → decohereReducedN ρ i j = 0)
    ∧ (∀ i, decohereReducedN ρ i i = ρ i i) :=
  ⟨fun _ _ h => decohereReducedN_offDiag_zero ρ h, fun i => decohereReducedN_diagonal ρ i⟩

/-- **The general-`N` channel restricts to the qubit einselection.**
`decohereReducedN (|ψ⟩⟨ψ|) = decohereReduced ψ`: the abstract dephasing channel on
the pure-state density reproduces the LF6-B reduced state. -/
theorem decohereReducedN_outerProduct {N : ℕ} [NeZero N] (ψ : EuclideanSpace ℂ (Fin N)) :
    decohereReducedN (outerProduct ψ) = decohereReduced ψ := by
  ext i j
  show Matrix.diagonal (fun i => outerProduct ψ i i) i j = decohereReduced ψ i j
  rw [decohereReduced_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; subst h; simp only [outerProduct, Matrix.vecMulVec_apply]
  · rw [if_neg h, if_neg h]

/-- **Non-vacuity: the dephasing genuinely acts.** For a pure-state density with two
nonzero components `ψᵢ, ψⱼ` (`i ≠ j`), the off-diagonal `(|ψ⟩⟨ψ|) i j = ψᵢ·star ψⱼ`
is NONZERO before dephasing and exactly `0` after. The channel is not vacuous. -/
theorem decohereReducedN_acts_nontrivial {N : ℕ} (ψ : EuclideanSpace ℂ (Fin N))
    {i j : Fin N} (hij : i ≠ j) (hi : ψ i ≠ 0) (hj : ψ j ≠ 0) :
    outerProduct ψ i j ≠ 0 ∧ decohereReducedN (outerProduct ψ) i j = 0 := by
  refine ⟨?_, decohereReducedN_offDiag_zero _ hij⟩
  simp only [outerProduct, Matrix.vecMulVec_apply]
  exact mul_ne_zero hi (star_ne_zero.mpr hj)

/-- **General-`N` degeneracy boundary.** If all populations are equal
(`ρ i i = 1/N`), the dephased state is `(1/N)·I` — a scalar multiple of the
identity. Einselection degenerates: basis-invariant (`einselectionN_degenerate`). -/
theorem decohereReducedN_degenerate_scalar {N : ℕ} [NeZero N] (ρ : Matrix (Fin N) (Fin N) ℂ)
    (hdeg : ∀ i, ρ i i = (1 / (N : ℂ))) :
    decohereReducedN ρ = (1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  show Matrix.diagonal (fun i => ρ i i) = (1 / (N : ℂ)) • 1
  rw [show (fun i => ρ i i) = (fun _ : Fin N => (1 / (N : ℂ))) from funext hdeg]
  exact diagonal_const_eq_smul_one _

/-- **Non-vacuity of the degenerate case: the maximally mixed input.** The dephasing
channel fixes `(1/N)·I` (the maximally mixed state): `decohereReducedN ((1/N)·I) = (1/N)·I`.
A genuine equal-populations witness, scalar·I in and out. -/
theorem decohereReducedN_maximally_mixed {N : ℕ} [NeZero N] :
    decohereReducedN ((1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ))
      = (1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  apply decohereReducedN_degenerate_scalar
  intro i
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]

/-- **General-`N` degeneracy capstone.** At equal populations (`ρ i i = 1/N`):

1. the dephased state is `(1/N)·I` (`decohereReducedN_degenerate_scalar`);
2. it is invariant under ANY unitary conjugation `U (·) Uᴴ` (`U Uᴴ = 1`):
   einselection degenerates, no basis preferred
   (`decohere_degenerate_basis_invariant`).

The contrast with `einselectionN` (off this locus a definite diagonal pointer
basis IS singled out) is the general-`N` einselection-selects-vs-degenerates
boundary. -/
theorem einselectionN_degenerate {N : ℕ} [NeZero N] (ρ : Matrix (Fin N) (Fin N) ℂ)
    (hdeg : ∀ i, ρ i i = (1 / (N : ℂ))) :
    decohereReducedN ρ = (1 / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)
    ∧ ∀ U : Matrix (Fin N) (Fin N) ℂ, U * Uᴴ = 1 →
        U * decohereReducedN ρ * Uᴴ = decohereReducedN ρ := by
  refine ⟨decohereReducedN_degenerate_scalar ρ hdeg, fun U hU => ?_⟩
  rw [decohereReducedN_degenerate_scalar ρ hdeg]
  exact decohere_degenerate_basis_invariant U hU (1 / (N : ℂ))

end Einselection
end CSDBridge
end Empirical
end CSD

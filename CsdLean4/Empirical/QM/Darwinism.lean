/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Helstrom

/-!
# Empirical/QM: quantum Darwinism as spectrum broadcast structure

**Category:** 3-Local (promotion-ready). QM-generic: density matrices and a two-outcome
test, no CSD ontology.

Expert-review row **E** of `specs/BACKLOG.md`, QM side. Scoped in
[`specs/quantum-darwinism-scoping.md`](../../../specs/quantum-darwinism-scoping.md); read
its §2 and §4 before extending this file.

The corpus proves that records are *made* (the pointer strokes, the Lüders theorems) and
which basis survives (`Empirical/CSD/Einselection.lean`). It did not say that a record is
**redundantly** copied — the property the decoherence literature uses as its criterion for a
record being objective.

## Which theorem this is, and which it is not

⚠️ **Not the mutual-information plateau.** Zurek's redundancy is usually stated as
`I(S : F) ≥ (1−δ)H(S)` for many disjoint fragments `F`. That form routes through mutual
information and its monotonicity, and in this corpus
`Mathlib/QuantumInfo/StrongSubadditivity.lean` carries SSA with **`hDPI` as an explicit
hypothesis** — the unconditional version sits behind the Effros/Lieb summit, which sits
behind `specs/lieb-dpi-scoping.md` Gate 1, an open author decision. Building the entropic
form here would import that gate. It is deliberately not built.

**What is here** is spectrum broadcast structure (Horodecki–Korbicz–Aharonov 2015): the
*structural* form of the same physics, which implies the plateau and does not need entropies.
Each fragment holds a state `ρᵢ⁽ᶠ⁾` conditioned on the outcome `i`, and the states of any one
fragment are **pairwise orthogonal**, so that fragment alone identifies the outcome.

* `SpectrumBroadcast` — the structure: a probability vector, per-fragment conditional states,
  and orthogonality within each fragment;
* ★ `SpectrumBroadcast.not_of_constant_fragment` — **the vacuity test the scoping note
  demands, as a theorem.** A fragment whose state does not depend on the outcome — the
  fragment that was never coupled — cannot occur in a spectrum broadcast structure at all.
  So the orthogonality field is doing work: it excludes something;
* ★ `successProb_eq_one_of_discriminating` — the general operational lemma: a test that
  passes `ρᵢ` and rejects `ρⱼ` discriminates them with certainty;
* `copyBroadcast` — the `k`-fold classical copy, and ★ `copyBroadcast_perfect` : **every one
  of the `k` fragments, on its own, identifies the outcome with probability one**. That is
  the redundancy statement, non-vacuously realised at arbitrary `k`.

## Honest scope

⚠️ **The general "orthogonal ⇒ perfectly discriminable" theorem is NOT proved here.** From
`ρᵢ ρⱼ = 0` alone, producing the discriminating test needs the **support projection** of a
positive semidefinite matrix and the fact that it annihilates anything orthogonal to it.
`TraceDistance.lean` has the ingredients (`posProj`, `mul_posProj_eq_posPart`) but not that
lemma, and it is a spectral argument, not a computation. What is proved instead is the
conditional lemma plus its instantiation on the copy witness, where the projection is
explicit. **Recorded as the residue of this module**; closing it would upgrade
`copyBroadcast_perfect` from a witness to a theorem about every `SpectrumBroadcast`.

⚠️ **No dynamics.** Nothing here derives that a physical environment couples this way; which
interaction an environment realises is `R-015`, a permanent boundary. `copyBroadcast` is a
modelling choice exhibited as a witness, not a claim about environments.

⚠️ **No CSD content.** The CSD-side twin — records as agreeing coordinates of one `Σ`-point,
and the scope theorem that objectivity is the ontic selection rather than the redundancy —
is `specs/quantum-darwinism-scoping.md` §5 and is **not built**.

References: Horodecki, Korbicz & Aharonov, *Phys. Rev. A* 91, 032122 (2015) (spectrum
broadcast structure); Zurek, *Nature Physics* 5, 181 (2009) (quantum Darwinism);
Blume-Kohout & Zurek, *Phys. Rev. A* 73, 062310 (2006) (the plateau, §2 above — not built);
`CsdLean4/Mathlib/QuantumInfo/Helstrom.lean`; `specs/quantum-darwinism-scoping.md`.
-/

@[expose] public section

open Matrix

namespace CSD
namespace Empirical
namespace Darwinism

open QuantumInfo
open scoped ComplexOrder

variable {N k d : ℕ}

/-! ### The structure -/

/-- **Spectrum broadcast structure.** The joint state of a system with `N` outcomes and `k`
environment fragments has the form `∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ⁽¹⁾ ⊗ ⋯ ⊗ ρᵢ⁽ᵏ⁾` with, for each
fragment, the conditional states pairwise orthogonal.

The joint state is not carried as a matrix: the whole content of the definition is the
per-fragment data plus `orthogonal`, and a `k`-fold Kronecker product would add index
plumbing without adding a hypothesis. -/
structure SpectrumBroadcast (N k d : ℕ) where
  /-- The outcome distribution. -/
  p : Fin N → ℝ
  /-- Probabilities are nonnegative. -/
  p_nonneg : ∀ i, 0 ≤ p i
  /-- Probabilities sum to one. -/
  p_sum : ∑ i, p i = 1
  /-- The state of fragment `f` conditioned on outcome `i`. -/
  ρ : Fin k → Fin N → Matrix (Fin d) (Fin d) ℂ
  /-- Each conditional state is positive semidefinite. -/
  ρ_posSemidef : ∀ f i, (ρ f i).PosSemidef
  /-- Each conditional state is normalised. -/
  ρ_trace : ∀ f i, (ρ f i).trace = 1
  /-- **The broadcast condition.** Within any one fragment, distinct outcomes leave
  orthogonal states — which is what makes that fragment alone a record. -/
  orthogonal : ∀ (f : Fin k) (i j : Fin N), i ≠ j → ρ f i * ρ f j = 0

namespace SpectrumBroadcast

variable (S : SpectrumBroadcast N k d)

/-- Orthogonality in trace form. -/
theorem trace_mul_eq_zero (f : Fin k) {i j : Fin N} (h : i ≠ j) :
    (S.ρ f i * S.ρ f j).trace = 0 := by
  rw [S.orthogonal f i j h, Matrix.trace_zero]

/-- ★ **The vacuity test, as a theorem** (`specs/quantum-darwinism-scoping.md` §4).

A fragment whose conditional state does **not** depend on the outcome — the fragment that
the interaction never touched — cannot appear in a spectrum broadcast structure, as soon as
there are two outcomes to tell apart. So `orthogonal` excludes something, and a redundancy
statement resting on this structure is not true by construction.

The proof is the reason the normalisation field is there: a constant fragment would need
`σ * σ = 0`, and a positive semidefinite matrix with `σ² = 0` is zero, which has trace `0`,
not `1`. -/
theorem not_of_constant_fragment (hN : 1 < N) (f : Fin k)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hconst : ∀ i, S.ρ f i = σ) : False := by
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin N, i ≠ j := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    simp [Fin.ext_iff]
  have hσσ : σ * σ = 0 := by
    have := S.orthogonal f i j hij
    rwa [hconst i, hconst j] at this
  have hpsd : σ.PosSemidef := by
    have := S.ρ_posSemidef f i
    rwa [hconst i] at this
  have hzero : σ = 0 := by
    have hsq : σ.conjTranspose * σ = 0 := by rwa [hpsd.isHermitian.eq]
    exact conjTranspose_mul_self_eq_zero.mp hsq
  have htr : σ.trace = 1 := by
    have := S.ρ_trace f i
    rwa [hconst i] at this
  rw [hzero, Matrix.trace_zero] at htr
  exact zero_ne_one htr

end SpectrumBroadcast

/-! ### Discrimination from an explicit test -/

/-- ★ **A test that passes `ρ₀` and rejects `ρ₁` discriminates them with certainty.**

`E * ρ₀ = ρ₀` says the test accepts the first state outright; `E * ρ₁ = 0` says it never
fires on the second. The Helstrom success probability is then exactly `1`. -/
theorem successProb_eq_one_of_discriminating {n : Type*} [Fintype n] [DecidableEq n]
    {ρ₀ ρ₁ E : Matrix n n ℂ} (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1)
    (hpass : ρ₀ * E = ρ₀) (hreject : ρ₁ * E = 0) :
    successProb ρ₀ ρ₁ E = 1 := by
  have h1 : ρ₁ * ((1 : Matrix n n ℂ) - E) = ρ₁ := by
    rw [Matrix.mul_sub, Matrix.mul_one, hreject, sub_zero]
  rw [successProb, hpass, h1, h₀, h₁]
  norm_num

/-! ### The `k`-fold classical copy, and redundancy at every fragment -/

/-- The rank-one diagonal projection `|i⟩⟨i|`. -/
noncomputable def basisProj (i : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun m => if m = i then 1 else 0

@[simp]
theorem basisProj_mul_self (i : Fin N) : basisProj i * basisProj i = basisProj i := by
  simp only [basisProj, diagonal_mul_diagonal]
  congr 1
  funext m
  by_cases h : m = i <;> simp [h]

@[simp]
theorem basisProj_mul_ne {i j : Fin N} (h : i ≠ j) : basisProj i * basisProj j = 0 := by
  simp only [basisProj, diagonal_mul_diagonal, ← diagonal_zero]
  congr 1
  funext m
  by_cases hm : m = i <;> by_cases hm' : m = j <;> simp_all

@[simp]
theorem trace_basisProj (i : Fin N) : (basisProj i).trace = 1 := by
  simp [basisProj, Matrix.trace_diagonal]

theorem basisProj_posSemidef (i : Fin N) : (basisProj i).PosSemidef := by
  refine Matrix.PosSemidef.diagonal ?_
  intro m
  by_cases h : m = i <;> simp [h]

/-- **The `k`-fold classical copy.** Every fragment ends holding the pointer state `|i⟩⟨i|`:
the interaction copied the outcome into all `k` of them. -/
noncomputable def copyBroadcast (k N : ℕ) (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : SpectrumBroadcast N k N where
  p := p
  p_nonneg := hp
  p_sum := hsum
  ρ := fun _ i => basisProj i
  ρ_posSemidef := fun _ i => basisProj_posSemidef i
  ρ_trace := fun _ i => trace_basisProj i
  orthogonal := fun _ _ _ h => basisProj_mul_ne h

/-- ★★ **Redundancy.** In the `k`-fold copy, **each fragment on its own** identifies the
outcome with probability one: for every fragment `f` and every pair of distinct outcomes,
the test `|i⟩⟨i|` applied to that fragment alone discriminates them perfectly.

This is the redundancy statement the row asked for, and it is non-vacuous in both directions:
it holds for arbitrary `k` here, and by `SpectrumBroadcast.not_of_constant_fragment` it
would fail outright for a fragment the interaction never touched. -/
theorem copyBroadcast_perfect (k N : ℕ) (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (f : Fin k) {i j : Fin N} (hij : i ≠ j) :
    successProb ((copyBroadcast k N p hp hsum).ρ f i)
      ((copyBroadcast k N p hp hsum).ρ f j) (basisProj i) = 1 :=
  successProb_eq_one_of_discriminating (trace_basisProj i) (trace_basisProj j)
    (basisProj_mul_self i) (basisProj_mul_ne hij.symm)

/-- The discriminating test really is a two-outcome test. -/
theorem basisProj_isTest (i : Fin N) : IsTest (basisProj i) := by
  refine ⟨basisProj_posSemidef i, ?_⟩
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) - basisProj i
      = diagonal fun m => if m = i then 0 else 1 := by
    simp only [basisProj, ← diagonal_one, diagonal_sub]
    congr 1
    funext m
    by_cases h : m = i <;> simp [h]
  rw [h1]
  refine Matrix.PosSemidef.diagonal ?_
  intro m
  by_cases h : m = i <;> simp [h]

end Darwinism
end Empirical
end CSD

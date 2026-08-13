/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound
public import CsdLean4.LF4.MomentMap
public import CsdLean4.LF4.KahlerInstance

/-!
# SigmaLayer/ApproxProjectability: A5's approximate `(ε,T)`-projectability

**Category:** 7-SigmaLayer (Paper C A5 — the axiom that *selects the sector*).

## What A5 says, and what was missing

A5's physical content is the **approximate** case: a Hamiltonian is quantum-effective when it is
*almost* fibre-invariant — `H = h∘π + δH` with `sup‖d(δH)|_V‖ ≤ ε` over a time window `T` — and it
is this condition, not the exact one, that selects which Hamiltonians the sector supports. Until
now only the exact case `H = h∘π` was formalised (`kSectorDataFlow_projectable`,
`SigmaLayer/DynamicsBridge.lean`): the axiom that does the selecting had its actual content
unformalised. This module supplies it, in two halves:

* **the ontic predicate** — `EpsProjectable`, in **oscillation form**: the ontic Hamiltonian varies
  by at most `ε` along each fibre. ⚠️ The *derivative* form `sup‖d(δH)|_V‖ ≤ ε` is the scoped
  manifold statement (`reconstruction-status.md` §2a — no exterior-calculus API); the oscillation
  form is its formalisable core, related in the usual way (a derivative bound integrates to an
  oscillation bound on a compact fibre). Stated so the substitution is visible, not silent.
* **the dynamical content** — the **shadowing theorem**: a Hamiltonian `ε`-close in L2 operator
  norm to a sector-projectable one generates Schrödinger dynamics that the sector dynamics tracks
  to within `ε·T` over the window `[−T, T]` (`quantum_effective_shadowing`, from the Duhamel
  bound). That is the operational meaning of "quantum-effective": for times up to `T`, the sector
  cannot tell `H` from its projectable part.

## What is proved

* `EpsProjectable` — the predicate on ontic Hamiltonians `Σ → ℝ`; `epsProjectable_mono`.
* `epsProjectable_zero_iff` — **the exact case is the `ε = 0` instance**: zero fibre-oscillation is
  precisely factoring through `π`. This is the BACKLOG row's required tie-in, and it is an iff.
* `diagOnticEnergy_epsProjectable` — non-vacuity: the moment-map energy of a diagonal observable
  (`∑ₖ λₖ · momentMap`) is an `EpsProjectable _ 0` witness — the corpus's own Born-weight energies
  are exactly projectable.
* `quantum_effective_shadowing` — `‖H − H₀‖ ≤ ε` and `|t| ≤ T` give
  `‖e^{t(−iH)} − e^{t(−iH₀)}‖ ≤ ε·T`.
* `quantum_effective_shadowing_state` — the same at the level of states: evolved vectors stay
  within `ε·T·‖ψ‖`.

## ⚠️ Scope

* The **derivative-form** predicate is not formalised (manifold API; §2a) — the oscillation form
  stands in, and the docstrings say so wherever it appears.
* The shadowing theorems live on the **Hilbert side** (matrix generators), where the corpus's
  dynamics genuinely runs; the ontic predicate lives on `Σ`. The bridge between them — an ontic
  Hamiltonian *generating* a flow whose projection is `e^{−itH}` — is A2's open row, not A5's, and
  is not claimed here.
* `H₀`'s witness flow being projectable is the existing exact-case result
  (`productDynamicsBridge`); this module adds the *approximate* layer on top of it, not a new
  dynamics.

## References

`Mathlib/Analysis/Matrix/DuhamelBound.lean` (the quantitative engine);
`SigmaLayer/DynamicsBridge.lean` (the exact case this extends); `LF4/MomentMap.lean`
(`momentMap` — the non-vacuity witness); `specs/BACKLOG.md` (the ★ A5 row);
`specs/reconstruction-status.md` §2a.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### The ontic predicate, in oscillation form -/

/-- **`(ε)`-projectability of an ontic Hamiltonian** (oscillation form): `Hs` varies by at most `ε`
along each fibre of `π = Prod.fst`. The fibre directions are Paper C's vertical subspace `V`; the
scoped derivative form `sup‖d(δH)|_V‖ ≤ ε` refines this on a smooth structure the corpus does not
carry (`reconstruction-status.md` §2a). -/
def EpsProjectable (Hs : LF4.KSigma N → ℝ) (ε : ℝ) : Prop :=
  ∀ (p : LF4.CPN N) (θ θ' : LF4.KTorus), |Hs (p, θ) - Hs (p, θ')| ≤ ε

theorem epsProjectable_mono {Hs : LF4.KSigma N → ℝ} {ε ε' : ℝ} (h : ε ≤ ε')
    (hHs : EpsProjectable Hs ε) : EpsProjectable Hs ε' :=
  fun p θ θ' => (hHs p θ θ').trans h

/-- **The exact case is the `ε = 0` instance — as an iff.** Zero fibre-oscillation is precisely
factoring through the projection: `Hs = h ∘ π`. This ties the new predicate to the corpus's
existing exact-case formalisation (`kSectorDataFlow_projectable`). -/
theorem epsProjectable_zero_iff (Hs : LF4.KSigma N → ℝ) :
    EpsProjectable Hs 0 ↔ ∃ h : LF4.CPN N → ℝ, Hs = fun x => h x.1 := by
  constructor
  · intro hHs
    refine ⟨fun p => Hs (p, (0, 0)), ?_⟩
    funext x
    have h0 := hHs x.1 x.2 (0, 0)
    have : Hs (x.1, x.2) = Hs (x.1, (0, 0)) := by
      have := abs_nonpos_iff.mp h0
      linarith [sub_eq_zero.mp this]
    simpa using this
  · rintro ⟨h, rfl⟩
    intro p θ θ'
    simp

/-- **Non-vacuity: the corpus's own energies are exactly projectable.** The moment-map energy of a
diagonal observable with eigenvalues `λ` — the ontic form of `⟨ψ, diag(λ) ψ⟩`
(`observable_correspondence_diagonal`) — depends on the base point alone, so it is
`EpsProjectable _ 0`. -/
noncomputable def diagOnticEnergy (lam : Fin N → ℝ) : LF4.KSigma N → ℝ :=
  fun x => ∑ k, lam k * LF4.momentMap x.1 k

theorem diagOnticEnergy_epsProjectable (lam : Fin N → ℝ) :
    EpsProjectable (diagOnticEnergy lam) 0 :=
  (epsProjectable_zero_iff _).mpr ⟨fun p => ∑ k, lam k * LF4.momentMap p k, rfl⟩

/-! ### The dynamical content: shadowing over the window -/

variable [NeZero N]

/-- **★ The shadowing theorem (A5's dynamical content).** If `H` is `ε`-close in L2 operator norm
to a Hamiltonian `H₀` — the projectable part — then over the whole window `[−T, T]` the two
Schrödinger unitaries differ by at most `ε·T`.

Reading: `H₀`'s witness flow is projectable (the exact case, `productDynamicsBridge`), so **the
sector dynamics tracks the true dynamics of `H` to within `ε·T`** — for times up to `T`, the sector
cannot tell a quantum-effective Hamiltonian from its projectable part. That is what "selects the
sector" means operationally, and it is the content the exact case alone could not express. -/
theorem quantum_effective_shadowing
    {H H₀ : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hH₀ : H₀.IsHermitian)
    {ε T t : ℝ} (hclose : ‖H - H₀‖ ≤ ε) (ht : |t| ≤ T) :
    ‖exp (t • ((-Complex.I) • H)) - exp (t • ((-Complex.I) • H₀))‖ ≤ ε * T := by
  calc ‖exp (t • ((-Complex.I) • H)) - exp (t • ((-Complex.I) • H₀))‖
      ≤ |t| * ‖H - H₀‖ := Matrix.norm_exp_smul_neg_I_sub_le H H₀ hH hH₀ t
    _ ≤ T * ε := by
        apply mul_le_mul ht hclose (norm_nonneg _) ((abs_nonneg t).trans ht)
    _ = ε * T := mul_comm T ε

/-- **The shadowing theorem at the level of states**: for any initial vector `ψ`, the two evolved
states stay within `ε·T·‖ψ‖` for the whole window. -/
theorem quantum_effective_shadowing_state
    {H H₀ : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hH₀ : H₀.IsHermitian)
    {ε T t : ℝ} (hclose : ‖H - H₀‖ ≤ ε) (ht : |t| ≤ T) (ψ : EuclideanSpace ℂ (Fin N)) :
    ‖Matrix.toEuclideanLin (exp (t • ((-Complex.I) • H))) ψ
      - Matrix.toEuclideanLin (exp (t • ((-Complex.I) • H₀))) ψ‖ ≤ ε * T * ‖ψ‖ := by
  have hlin : Matrix.toEuclideanLin (exp (t • ((-Complex.I) • H))) ψ
      - Matrix.toEuclideanLin (exp (t • ((-Complex.I) • H₀))) ψ
      = Matrix.toEuclideanLin
          (exp (t • ((-Complex.I) • H)) - exp (t • ((-Complex.I) • H₀))) ψ := by
    simp [map_sub]
  rw [hlin]
  calc ‖Matrix.toEuclideanLin
        (exp (t • ((-Complex.I) • H)) - exp (t • ((-Complex.I) • H₀))) ψ‖
      ≤ ‖exp (t • ((-Complex.I) • H)) - exp (t • ((-Complex.I) • H₀))‖ * ‖ψ‖ := by
        set D := exp (t • ((-Complex.I) • H)) - exp (t • ((-Complex.I) • H₀)) with hD
        rw [Matrix.l2_opNorm_def]
        exact ContinuousLinearMap.le_opNorm
          ((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) D) ψ
    _ ≤ ε * T * ‖ψ‖ := by
        apply mul_le_mul_of_nonneg_right
          (quantum_effective_shadowing hH hH₀ hclose ht) (norm_nonneg ψ)

end CSD.RecordLayer

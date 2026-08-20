/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.LindbladGenerator
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Lindblad semigroup: the exponentiated GKSL tier (§Q Q5, LF6-9)

**Category:** 4-LF (open-system dynamics). The generator tier
(`LF6/LindbladGenerator.lean`) built `ℒ(ρ) = −i[H,ρ] + Σₖ D_{Lₖ}(ρ)` and
proved trace annihilation, Hermiticity preservation, and complete
positivity of the jump part. This module exponentiates: `Φₜ = e^{tℒ}`, for
an **arbitrary** GKSL generator, with the flow-level laws.

* `lindbladSemigroup` — `Φₜ := exp (t • ℒ)` in the Banach algebra of
  continuous endomorphisms of matrix space (the L2-operator scope supplies
  the norm and completeness, as everywhere in the corpus's matrix-exp
  work).
* `lindbladSemigroup_zero` / ★ `lindbladSemigroup_add` — `Φ₀ = 1` and the
  semigroup law `Φ_{s+t} = Φ_s ∘ Φ_t`.
* ★★ `lindbladSemigroup_hasDerivAt` — **the master equation**: for every
  state, `d/dt (Φₜ ρ) = ℒ(Φₜ ρ)`. The dephasing instance solved its master
  equation by hand (`dephasingChannel_master_equation`); this is the
  general-generator statement.
* ★ `lindbladSemigroup_trace` — **trace preservation at the flow level**,
  `tr (Φₜ ρ) = tr ρ`: the exponential series termwise inherits
  `lindbladGenerator_trace` (every power `ℒⁿ, n ≥ 1` is traceless on any
  input), so only the identity term survives.
* ★ `lindbladSemigroup_conjTranspose` — **Hermiticity preservation at the
  flow level**: `(Φₜ ρ)ᴴ = Φₜ (ρᴴ)` for Hermitian `H`, via the generator
  intertwining `lindbladGenerator_conjTranspose` pushed through the series
  (`HasSum.star`). Corollary `lindbladSemigroup_isHermitian`.

## Honest scope

~~Complete positivity of `e^{tℒ}` is NOT claimed — that is the remaining
genuinely-Mathlib-scale half recorded on the LF6-9 row.~~ **Superseded
2026-08-20**: positivity of `e^{tℒ}` for every GKSL generator with Hermitian
`H`, at every `t ≥ 0`, is now proved in `LF6/LindbladPositivity.lean`
(`lindbladSemigroup_posSemidef`, via the de-skewed Banach-algebra Trotter
formula), together with its stability under every ancilla amplification of
the generator (`lindbladSemigroup_amplified_posSemidef`). The "needs a
Lie–Trotter limit theorem Mathlib does not have" wall was stale — the
theorem was buildable in-corpus. What this module still delivers is the
tier below: the semigroup exists, solves the master equation, and preserves
trace and Hermiticity for arbitrary `H, {Lₖ}`.

Proof-engineering note: several scalar-action facts (`0 • ℒ = 0`,
`(s+t) • ℒ`, commutation of the scaled generators, powers of `t • ℒ`) are
proved pointwise or by `module` rather than by the generic `smul` lemmas —
the module system blocks the instance-level defeq those lemmas' typeclass
paths need (`Complex.mulAux` is not exposed). Same family as the
`project_module_system_defeq` trap.

Cross-references: `specs/future-work.md` (LF6-2, LF6-9),
`specs/BACKLOG.md` §Q (Q5) and the GKSL row;
`Mathlib/Analysis/Matrix/DuhamelBound.lean` (the same L2-operator exp
scope), `LF4/ManyToOneSchrodingerDerived.lean` (the closed-system
`exp(t • A)` derivative idiom this reuses).
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace CSD.LF6

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]

/-! ### The generator as a (continuous) linear endomorphism -/

/-- One dissipator term as a linear endomorphism of matrix space. -/
noncomputable def lindbladDissipatorL (L : Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  (LinearMap.mulLeft ℂ L).comp (LinearMap.mulRight ℂ Lᴴ)
    - (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ (Lᴴ * L)
        + LinearMap.mulRight ℂ (Lᴴ * L))

lemma lindbladDissipatorL_apply (L ρ : Matrix n n ℂ) :
    lindbladDissipatorL L ρ = lindbladDissipator L ρ := by
  simp only [lindbladDissipatorL, lindbladDissipator, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]

/-- The GKSL generator as a linear endomorphism of matrix space. -/
noncomputable def lindbladGeneratorL (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  (-Complex.I) • (LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H)
    + ∑ k, lindbladDissipatorL (L k)

lemma lindbladGeneratorL_apply (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) :
    lindbladGeneratorL H L ρ = lindbladGenerator H L ρ := by
  simp only [lindbladGeneratorL, lindbladGenerator, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, LinearMap.sum_apply, lindbladDissipatorL_apply]

/-- The GKSL generator as a **continuous** linear endomorphism of matrix
space, over ℝ (`restrictScalars`) — the element the exponential acts on.
Working in the ℝ-endomorphism algebra keeps every scalar action, the
`Commute` instance, and the exponential's field on a single canonical
instance path (the module system blocks cross-path instance defeq;
see the proof-engineering note above). -/
noncomputable def lindbladGeneratorCLM (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (LinearMap.toContinuousLinearMap (lindbladGeneratorL H L)).restrictScalars ℝ

@[simp] lemma lindbladGeneratorCLM_apply (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    lindbladGeneratorCLM H L ρ = lindbladGenerator H L ρ :=
  lindbladGeneratorL_apply H L ρ

/-! ### The semigroup -/

/-- **The Lindblad semigroup** `Φₜ = exp (t ℒ)`: the flow of the master
equation, as a family of continuous endomorphisms of matrix space. -/
noncomputable def lindbladSemigroup (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  exp (t • lindbladGeneratorCLM H L)

/-- At `t = 0` the flow is the identity. -/
@[simp] theorem lindbladSemigroup_zero (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) :
    lindbladSemigroup H L 0 = 1 := by
  have h0 : (0 : ℝ) • lindbladGeneratorCLM H L = 0 := by module
  rw [lindbladSemigroup, h0, exp_zero]

/-- ★ **The semigroup law**: `Φ_{s+t} = Φ_s ∘ Φ_t`. -/
theorem lindbladSemigroup_add (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ)
    (s t : ℝ) :
    lindbladSemigroup H L (s + t)
      = lindbladSemigroup H L s * lindbladSemigroup H L t := by
  have hadd : (s + t) • lindbladGeneratorCLM H L
      = s • lindbladGeneratorCLM H L + t • lindbladGeneratorCLM H L := by
    module
  rw [lindbladSemigroup, lindbladSemigroup, lindbladSemigroup, hadd]
  refine exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (𝔸 := Matrix n n ℂ →L[ℝ] Matrix n n ℂ) ?_
    ((expSeries_radius_eq_top ℝ
        (Matrix n n ℂ →L[ℝ] Matrix n n ℂ)).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ
        (Matrix n n ℂ →L[ℝ] Matrix n n ℂ)).symm ▸ edist_lt_top _ _)
  refine ContinuousLinearMap.ext fun ρ => ?_
  show s • lindbladGeneratorCLM H L (t • lindbladGeneratorCLM H L ρ)
    = t • lindbladGeneratorCLM H L (s • lindbladGeneratorCLM H L ρ)
  rw [map_smul, map_smul, smul_comm]

/-- ★★ **The master equation, arbitrary GKSL generator**: for every state
`ρ`, the flow satisfies `d/dt (Φₜ ρ) = ℒ(Φₜ ρ)`. The general-generator form
of what the dephasing instance solved by hand. -/
theorem lindbladSemigroup_hasDerivAt (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) (t : ℝ) :
    HasDerivAt (fun u => lindbladSemigroup H L u ρ)
      (lindbladGenerator H L (lindbladSemigroup H L t ρ)) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (lindbladGeneratorCLM H L) t
  have h2 := ((ContinuousLinearMap.apply ℝ (Matrix n n ℂ)
      ρ).hasFDerivAt).comp_hasDerivAt t h
  have h3 : (ContinuousLinearMap.apply ℝ (Matrix n n ℂ) ρ)
        (lindbladGeneratorCLM H L * exp (t • lindbladGeneratorCLM H L))
      = lindbladGenerator H L (lindbladSemigroup H L t ρ) := by
    show lindbladGeneratorCLM H L
        (exp (t • lindbladGeneratorCLM H L) ρ) = _
    rw [lindbladGeneratorCLM_apply]
    rfl
  rw [h3] at h2
  exact h2

/-! ### The series form: what the flow does termwise -/

/-- The flow applied to a state, as the exponential series. -/
lemma lindbladSemigroup_apply_hasSum (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (t : ℝ) (ρ : Matrix n n ℂ) :
    HasSum (fun m : ℕ => (((m.factorial : ℝ))⁻¹
        • (t • lindbladGeneratorCLM H L) ^ m) ρ)
      (lindbladSemigroup H L t ρ) := by
  have hexp : lindbladSemigroup H L t
      = ∑' m : ℕ, ((m.factorial : ℝ))⁻¹
          • (t • lindbladGeneratorCLM H L) ^ m := by
    rw [lindbladSemigroup, exp_eq_tsum (𝕂 := ℝ)]
  have h1 := (expSeries_summable' (𝕂 := ℝ)
      (t • lindbladGeneratorCLM H L)).hasSum
  rw [← hexp] at h1
  exact h1.mapL (ContinuousLinearMap.apply ℝ (Matrix n n ℂ) ρ)

/-- Every positive power of the scaled generator is traceless on any
input. -/
lemma lindbladGeneratorCLM_smul_pow_succ_trace (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (t : ℝ) (m : ℕ) (ρ : Matrix n n ℂ) :
    (((t • lindbladGeneratorCLM H L) ^ (m + 1)) ρ).trace = 0 := by
  induction m generalizing ρ with
  | zero =>
    rw [pow_one]
    show (t • lindbladGeneratorCLM H L ρ).trace = 0
    rw [Matrix.trace_smul, lindbladGeneratorCLM_apply,
      lindbladGenerator_trace, smul_zero]
  | succ m ih =>
    rw [pow_succ]
    exact ih ((t • lindbladGeneratorCLM H L) ρ)

/-- ★ **Trace preservation at the flow level**: `tr (Φₜ ρ) = tr ρ` for
every `t` and every input — the exponential series termwise inherits the
generator's trace annihilation, so only the identity term survives. -/
theorem lindbladSemigroup_trace (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ)
    (t : ℝ) (ρ : Matrix n n ℂ) :
    (lindbladSemigroup H L t ρ).trace = ρ.trace := by
  have h := (lindbladSemigroup_apply_hasSum H L t ρ).mapL
    (LinearMap.toContinuousLinearMap
      (Matrix.traceLinearMap (α := ℝ) (R := ℂ) (n := n)))
  have hterm : ∀ m : ℕ, m ≠ 0 →
      (LinearMap.toContinuousLinearMap
          (Matrix.traceLinearMap (α := ℝ) (R := ℂ) (n := n)))
        ((((m.factorial : ℝ))⁻¹
          • (t • lindbladGeneratorCLM H L) ^ m) ρ) = 0 := by
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp only [LinearMap.coe_toContinuousLinearMap',
      Matrix.traceLinearMap_apply, _root_.smul_apply, Matrix.trace_smul,
      Nat.succ_eq_add_one, lindbladGeneratorCLM_smul_pow_succ_trace,
      smul_zero]
  have htsum := h.tsum_eq
  rw [tsum_eq_single 0 hterm] at htsum
  simpa [Nat.factorial] using htsum.symm

/-! ### Hermiticity at the flow level -/

omit [DecidableEq n] in
/-- **The generator intertwines the adjoint**: `(ℒρ)ᴴ = ℒ(ρᴴ)` for
Hermitian `H` — on arbitrary (not necessarily Hermitian) inputs. The
generator-tier `lindbladGenerator_isHermitian` is the diagonal of this. -/
theorem lindbladGenerator_conjTranspose {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (L : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    (lindbladGenerator H L ρ)ᴴ = lindbladGenerator H L ρᴴ := by
  have hdiss : ∀ M : Matrix n n ℂ,
      (lindbladDissipator M ρ)ᴴ = lindbladDissipator M ρᴴ := by
    intro M
    simp only [lindbladDissipator, conjTranspose_sub, conjTranspose_smul,
      conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      star_div₀, star_one, star_ofNat, mul_assoc]
    rw [add_comm (ρᴴ * (Mᴴ * M)) (Mᴴ * (M * ρᴴ))]
  rw [lindbladGenerator, lindbladGenerator, conjTranspose_add,
    conjTranspose_sum]
  congr 1
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul,
      conjTranspose_mul, hH.eq,
      show star (-Complex.I) = Complex.I from by simp]
    module
  · exact Finset.sum_congr rfl fun k _ => hdiss (L k)

/-- Powers of the scaled generator intertwine the adjoint. -/
lemma lindbladGeneratorCLM_smul_pow_conjTranspose {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (L : ι → Matrix n n ℂ) (t : ℝ) (m : ℕ)
    (ρ : Matrix n n ℂ) :
    (((t • lindbladGeneratorCLM H L) ^ m) ρ)ᴴ
      = ((t • lindbladGeneratorCLM H L) ^ m) ρᴴ := by
  induction m generalizing ρ with
  | zero => simp
  | succ m ih =>
    have hstep : ∀ σ : Matrix n n ℂ,
        ((t • lindbladGeneratorCLM H L) σ)ᴴ
          = (t • lindbladGeneratorCLM H L) σᴴ := by
      intro σ
      show (t • lindbladGeneratorCLM H L σ)ᴴ = _
      rw [conjTranspose_smul, star_trivial, lindbladGeneratorCLM_apply,
        lindbladGenerator_conjTranspose hH, ← lindbladGeneratorCLM_apply]
      rfl
    rw [pow_succ,
      show ((t • lindbladGeneratorCLM H L) ^ m
            * (t • lindbladGeneratorCLM H L)) ρ
          = ((t • lindbladGeneratorCLM H L) ^ m)
              ((t • lindbladGeneratorCLM H L) ρ) from rfl,
      show ((t • lindbladGeneratorCLM H L) ^ m
            * (t • lindbladGeneratorCLM H L)) ρᴴ
          = ((t • lindbladGeneratorCLM H L) ^ m)
              ((t • lindbladGeneratorCLM H L) ρᴴ) from rfl,
      ih, hstep]

/-- ★ **Hermiticity preservation at the flow level**: `(Φₜ ρ)ᴴ = Φₜ (ρᴴ)`
for Hermitian `H` — the generator intertwining pushed through the
exponential series. -/
theorem lindbladSemigroup_conjTranspose {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (L : ι → Matrix n n ℂ) (t : ℝ) (ρ : Matrix n n ℂ) :
    (lindbladSemigroup H L t ρ)ᴴ = lindbladSemigroup H L t ρᴴ := by
  have h2 := lindbladSemigroup_apply_hasSum H L t ρᴴ
  have hstar := (lindbladSemigroup_apply_hasSum H L t ρ).star
  have hterm : (fun m : ℕ =>
      star ((((m.factorial : ℝ))⁻¹
        • (t • lindbladGeneratorCLM H L) ^ m) ρ))
      = fun m : ℕ =>
        (((m.factorial : ℝ))⁻¹
          • (t • lindbladGeneratorCLM H L) ^ m) ρᴴ := by
    funext m
    rw [Matrix.star_eq_conjTranspose]
    simp only [_root_.smul_apply, conjTranspose_smul, star_trivial,
      lindbladGeneratorCLM_smul_pow_conjTranspose hH]
  rw [hterm] at hstar
  rw [← Matrix.star_eq_conjTranspose]
  exact hstar.unique h2

/-- The flow keeps states Hermitian. -/
theorem lindbladSemigroup_isHermitian {H ρ : Matrix n n ℂ}
    (hH : H.IsHermitian) (L : ι → Matrix n n ℂ) (t : ℝ)
    (hρ : ρ.IsHermitian) :
    (lindbladSemigroup H L t ρ).IsHermitian := by
  rw [Matrix.IsHermitian, lindbladSemigroup_conjTranspose hH, hρ.eq]

end CSD.LF6

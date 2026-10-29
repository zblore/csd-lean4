/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.ActivatedHamiltonian
public import CsdLean4.RecordLayer.ApproxProjectability

/-!
# SigmaLayer/ActivatedRegime: A5's approximate regime as a dynamical statement

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian"; `specs/TERMS.md`
records what is backed and what is not.

**Category:** 7-SigmaLayer (the projective-sector layer, Paper C — the A5 approximate regime).
BACKLOG #208.

`EpsProjectable` was populated at `ε > 0` (`SigmaLayer/MovingFibreWitness.lean`) but only as a
predicate: no flow had it as its generator, the derivative form `sup‖d(δH)|_V‖ ≤ ε` was not stated,
and `quantum_effective_shadowing` lived on matrices with no bridge to the arena. This module closes
all three on the corpus's own record-creating Hamiltonian, the activated write of #194/#195,

  `𝓗 = −(2/ħ)(J⟨X⟩ + g f(θ₂) n_B)`   on `Σ = ℂℙ³ × T²`,

whose Hamiltonian flow for the arena symplectic form *is* #194's `activeFlow`
(`hamiltonianFlow_activeFlow`).

## The derivative form, and why it implies the oscillation form

* `verticalDeriv Hs p` — the manifold derivative of `Hs` restricted to the fibre directions
  `V = 0 × (ℝ × ℝ)` of the arena model; `EpsProjectableDeriv Hs ε` — `‖d(Hs)|_V‖ ≤ ε` everywhere.
* ★★ `epsProjectable_of_deriv` — **a vertical derivative bound `ε` gives fibre oscillation at most
  `ε/2`**: any two points of a fibre are joined by a straight fibre path whose step has sup-norm at
  most `1/2` (`exists_coe_add_eq`), and the mean value inequality runs along it. This is the
  "derivative bound integrates to an oscillation bound" that `RecordLayer/ApproxProjectability.lean`
  could only state in prose.

## The coupled energy, in general

For `𝓗 = −2⟨A⟩ − 2⟨B⟩ f(θ₂)` (`LF4/ArenaCoupledFlow.lean`):

* `coupledEnergy_sub`, `epsProjectable_coupledEnergy_iff` — the fibre oscillation exactly;
  `abs_expectation_le`, ★ `epsProjectable_coupledEnergy` — `EpsProjectable` at `2‖B‖·osc f`;
* `exists_hasMFDerivAt_coupledEnergy`, `mdifferentiable_coupledEnergy`,
  ★ `verticalDeriv_coupledEnergy` — **`d𝓗|_V = −2⟨B⟩(x) f'(θ₂) dθ₂`**;
  ★ `epsProjectableDeriv_coupledEnergy` — the derivative form at `2‖B‖·sup|f'|`;
* `schrodingerUnitary_smul_mk`, `norm_coupledMatrix_sub_le`, ★★★ `coupledFlow_shadowing` — **the
  `(ε, T)` shadowing bound on the arena**: from the same point of `Σ`, the coupled flow and the flow of
  the *exactly projectable* sector energy of `A + f(φ₀) B` have rays represented within
  `‖B‖·osc·T·‖v‖` for `|t| ≤ T`; `abs_expectation_mk_sub_le`, `exists_unit_mk`,
  ★★★ `coupledFlow_expectation_shadowing` — **every sector expectation is shadowed** to
  `2‖O‖·‖B‖·osc·T`, on rays, with no representative chosen.

## The activated write

* `abs_schrodingerHamiltonian_hamB_le`, `exists_abs_schrodingerHamiltonian_hamB_eq` — the coupled
  term is bounded by `2|g|/|ħ|`, attained where the receiver is occupied;
* ★★ `epsProjectable_activatedEnergy_iff` — **the sharp `ε`**: the activated energy is
  `EpsProjectable` at `ε` iff `ε ≥ (2|g|/|ħ|)·|f(a) − f(b)|` for all `a, b`;
  ★ `epsProjectable_activatedEnergy` — at `(2|g|/|ħ|)·osc f`;
  ★★ `activatedEnergy_not_projectable` — for `g ≠ 0` and nonconstant `f` it is **not** `EpsProjectable`
  at `0`, so it does not factor through `π`;
* ★ `epsProjectableDeriv_activatedEnergy` — the derivative form at `(2|g|/|ħ|)·sup|f'|`, and
  `epsProjectable_activatedEnergy_of_deriv` — integrated, `(|g|/|ħ|)·sup|f'|`;
* `norm_hamB` (`‖g n_B/ħ‖ = |g|/|ħ|`), ★★★ `activated_shadowing`,
  ★★★ `activated_expectation_shadowing` — **sector predictions shadowed at `‖O‖·ε·T`** with `ε` the
  sharp ontic oscillation; the matrix-level constant is exactly half of it, the factor `2` being the
  corpus's `−2⟨·⟩` normalisation;
* ★★★ `activated_regime` — the package (6 conjuncts).

## Honest scope

* The norm on `V` is Mathlib's product (sup) norm on `ℝ × ℝ`. For these energies `d𝓗|_V` has only a
  `dθ₂` component, so its norm is the same for the flat metric; the integration constant `1/2` is the
  sup-norm reach of the unit torus (the flat one would be `√2/2`).
* The shadowing compares the **projections** to `ℂℙ³`. The fibre is not shadowed and is not meant to
  be: the pointer angle `θ₁` moves under the activated flow and stays put under the sector flow —
  that motion is the record write.
* The comparison flow is the exact sector flow of `A + f(φ₀) B` for a chosen reference angle; the
  constant is uniform in `φ₀`, `θ` and the initial ray.
* Specific to coupled energies `−2⟨A⟩ − 2⟨B⟩ f(θ₂)`; a general ontic Hamiltonian on `Σ` has no
  matrix to shadow against, which is A2's question, not A5's.

## References

`RecordLayer/ApproxProjectability.lean` (`EpsProjectable`, `quantum_effective_shadowing_state`);
`SigmaLayer/MovingFibreWitness.lean` (the first `ε > 0` instance, predicate only);
`RecordLayer/ActivatedHamiltonian.lean` (`activatedEnergy`, `hamiltonianFlow_activeFlow`);
`LF4/ArenaCoupledFlow.lean` (`coupledEnergy`, `hamiltonianFlow_coupledEnergy`);
`LF4/ArenaSymplectic.lean` (`hamiltonianFlow_sectorEnergy_schrodinger`);
`specs/BACKLOG.md` #208; `specs/reconstruction-status.md` §7; `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Projectivization MeasureTheory NormedSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator LinearAlgebra.Projectivization

namespace CSD
namespace SigmaLayer

open LF4 RecordLayer

variable {N : ℕ}

/-! ### The derivative form, and its integration to the oscillation form -/

/-- **The vertical derivative** `d(Hs)|_V` of an ontic Hamiltonian on the arena: the manifold
derivative restricted to the fibre directions `V = 0 × (ℝ × ℝ)`. -/
def verticalDeriv (Hs : KSigma (N + 1) → ℝ) (p : KSigma (N + 1)) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) Hs p).comp (ContinuousLinearMap.inr ℝ (Fin N → ℂ) (ℝ × ℝ))

/-- **`(ε)`-projectability in derivative form**: `sup ‖d(Hs)|_V‖ ≤ ε`. -/
def EpsProjectableDeriv (Hs : KSigma (N + 1) → ℝ) (ε : ℝ) : Prop :=
  ∀ p, ‖verticalDeriv Hs p‖ ≤ ε

/-- Every angle of the unit circle is reached from any other by a real step of size at most `1/2`. -/
theorem exists_coe_add_eq (a : ℝ) (z : AddCircle (1 : ℝ)) :
    ∃ u : ℝ, |u| ≤ 1 / 2 ∧ ((a + u : ℝ) : AddCircle (1 : ℝ)) = z := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective z
  refine ⟨(b - a) - round (b - a), abs_sub_round _, ?_⟩
  show ((a + ((b - a) - round (b - a)) : ℝ) : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ))
  rw [show a + ((b - a) - round (b - a)) = b - (round (b - a) : ℤ) by ring, AddCircle.coe_sub]
  have h0 : (((round (b - a) : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples_iff.2 ⟨round (b - a), by simp⟩)
  rw [h0, sub_zero]

/-- ★★ **The derivative form integrates to the oscillation form.** If the vertical derivative is
bounded by `ε` everywhere, the fibre oscillation is at most `ε/2`: any two points of a fibre are
joined by a straight fibre path whose step has sup-norm at most `1/2`, and the mean value
inequality runs along it. -/
theorem epsProjectable_of_deriv {Hs : KSigma (N + 1) → ℝ} {ε : ℝ}
    (hd : MDifferentiable 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) Hs) (h : EpsProjectableDeriv Hs ε) :
    EpsProjectable Hs (ε / 2) := by
  intro x θ θ'
  have hε : 0 ≤ ε := (norm_nonneg _).trans (h (x, θ))
  obtain ⟨a₁, ha₁⟩ := QuotientAddGroup.mk_surjective θ.1
  obtain ⟨a₂, ha₂⟩ := QuotientAddGroup.mk_surjective θ.2
  obtain ⟨u₁, hu₁, hθ₁⟩ := exists_coe_add_eq a₁ θ'.1
  obtain ⟨u₂, hu₂, hθ₂⟩ := exists_coe_add_eq a₂ θ'.2
  set u : ℝ × ℝ := (u₁, u₂) with hu
  have hun : ‖u‖ ≤ 1 / 2 := norm_prod_le_iff.2 ⟨by simpa [Real.norm_eq_abs] using hu₁,
    by simpa [Real.norm_eq_abs] using hu₂⟩
  set γ : ℝ → KSigma (N + 1) := fun s =>
    (x, (((a₁ + s * u₁ : ℝ) : AddCircle (1 : ℝ)), ((a₂ + s * u₂ : ℝ) : AddCircle (1 : ℝ))))
    with hγdef
  have hγ : ∀ s : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ArenaModel N) γ s
      (ContinuousLinearMap.smulRight (M₂ := TangentSpace 𝓘(ℝ, ArenaModel N) (γ s))
        (1 : ℝ →L[ℝ] ℝ) (((0 : Fin N → ℂ), u) : ArenaModel N)) := by
    intro s
    have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun s : ℝ => (((a₁ + s * u₁ : ℝ) : AddCircle (1 : ℝ)))) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight u₁) :=
      AddCircle.hasMFDerivAt_coe_comp ((((hasDerivAt_id s).mul_const u₁).const_add a₁).congr_deriv
        (by simp))
    have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun s : ℝ => (((a₂ + s * u₂ : ℝ) : AddCircle (1 : ℝ)))) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight u₂) :=
      AddCircle.hasMFDerivAt_coe_comp ((((hasDerivAt_id s).mul_const u₂).const_add a₂).congr_deriv
        (by simp))
    have h0 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin N → ℂ) (fun _ : ℝ => x) s
        (0 : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, Fin N → ℂ) x) :=
      hasMFDerivAt_const x s
    refine (h0.prodMk_self (h1.prodMk_self h2)).congr_deriv ?_
    refine ContinuousLinearMap.ext fun r => Prod.ext ?_ (Prod.ext ?_ ?_)
    · show (0 : Fin N → ℂ) = ((1 : ℝ →L[ℝ] ℝ) r) • (0 : Fin N → ℂ)
      rw [smul_zero]
    · show ((1 : ℝ →L[ℝ] ℝ) r) • u₁ = ((1 : ℝ →L[ℝ] ℝ) r • u).1
      rfl
    · show ((1 : ℝ →L[ℝ] ℝ) r) • u₂ = ((1 : ℝ →L[ℝ] ℝ) r • u).2
      rfl
  have hderiv : ∀ s : ℝ, HasDerivAt (Hs ∘ γ) (verticalDeriv Hs (γ s) u) s := by
    intro s
    have h := (hd (γ s)).hasMFDerivAt.comp s (hγ s)
    have h' : HasFDerivAt (Hs ∘ γ)
        ((mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) Hs (γ s)).comp
          (ContinuousLinearMap.smulRight (M₂ := TangentSpace 𝓘(ℝ, ArenaModel N) (γ s))
            (1 : ℝ →L[ℝ] ℝ) (((0 : Fin N → ℂ), u) : ArenaModel N))) s :=
      hasMFDerivAt_iff_hasFDerivAt.1 h
    rw [hasDerivAt_iff_hasFDerivAt]
    refine h'.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun r => ?_
    set v : TangentSpace 𝓘(ℝ, ArenaModel N) (γ s) := (((0 : Fin N → ℂ), u) : ArenaModel N)
    have hm : mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) Hs (γ s) ((r : ℝ) • v)
        = (r : ℝ) • mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) Hs (γ s) v :=
      (mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) Hs (γ s)).map_smul (r : ℝ) v
    show mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) Hs (γ s) ((r : ℝ) • v)
      = (r : ℝ) • verticalDeriv Hs (γ s) u
    rw [hm]
    rfl
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := Hs ∘ γ)
    (f' := fun s => verticalDeriv Hs (γ s) u) (C := ε / 2)
    (fun s _ => (hderiv s).hasDerivWithinAt)
    (fun s _ => by
      calc ‖verticalDeriv Hs (γ s) u‖ ≤ ‖verticalDeriv Hs (γ s)‖ * ‖u‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε * (1 / 2) := mul_le_mul (h _) hun (norm_nonneg _) hε
        _ = ε / 2 := by ring)
  have hγ0 : γ 0 = (x, θ) := by
    simp only [hγdef, zero_mul, add_zero, ha₁, ha₂]
  have hγ1 : γ 1 = (x, θ') := by
    simp only [hγdef, one_mul, hθ₁, hθ₂]
  rw [Function.comp_apply, Function.comp_apply, hγ0, hγ1, Real.norm_eq_abs] at hmv
  rwa [abs_sub_comm]

/-! ### The coupled energy: oscillation and vertical derivative -/

variable {f : ℝ → ℝ} (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- Along a fibre only the coupled term moves: `𝓗(x, θ) − 𝓗(x, θ') = −2⟨B⟩(x) (f(θ₂) − f(θ₂'))`. -/
theorem coupledEnergy_sub (hf : Function.Periodic f 1) (x : CPN (N + 1)) (θ θ' : KTorus) :
    coupledEnergy A B hf (x, θ) - coupledEnergy A B hf (x, θ')
      = schrodingerHamiltonian B x * (hf.lift θ.2 - hf.lift θ'.2) := by
  simp only [coupledEnergy, torusPotential]
  ring

/-- **The fibre oscillation of the coupled energy, exactly.** -/
theorem epsProjectable_coupledEnergy_iff (hf : Function.Periodic f 1) {ε : ℝ} :
    EpsProjectable (coupledEnergy A B hf) ε
      ↔ ∀ (x : CPN (N + 1)) (a b : ℝ), |schrodingerHamiltonian B x| * |f a - f b| ≤ ε := by
  constructor
  · intro h x a b
    have := h x (0, (a : AddCircle (1 : ℝ))) (0, (b : AddCircle (1 : ℝ)))
    rwa [coupledEnergy_sub, abs_mul, hf.lift_coe, hf.lift_coe] at this
  · intro h x θ θ'
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective θ.2
    obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective θ'.2
    rw [coupledEnergy_sub, abs_mul, ← ha, ← hb]
    simpa only [hf.lift_coe] using h x a b

/-- A matrix moves a vector by at most its L2 operator norm. -/
theorem norm_toEuclideanLin_le (v : EuclideanSpace ℂ (Fin (N + 1))) :
    ‖Matrix.toEuclideanLin B v‖ ≤ ‖B‖ * ‖v‖ := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) B) v

/-- The expectation of a matrix at a ray is bounded by its operator norm. -/
theorem abs_expectation_le (x : CPN (N + 1)) : |expectation B x| ≤ ‖B‖ := by
  have hv : x.rep ≠ 0 := x.rep_nonzero
  have hpos : 0 < ‖x.rep‖ ^ 2 := by positivity
  have hB := norm_toEuclideanLin_le B x.rep
  rw [expectation, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |(inner ℂ x.rep (Matrix.toEuclideanLin B x.rep)).re|
      ≤ ‖inner ℂ x.rep (Matrix.toEuclideanLin B x.rep)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x.rep‖ * ‖Matrix.toEuclideanLin B x.rep‖ := norm_inner_le_norm _ _
    _ ≤ ‖x.rep‖ * (‖B‖ * ‖x.rep‖) := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = ‖B‖ * ‖x.rep‖ ^ 2 := by ring

/-- Expectations at two unit representatives differ by at most `2‖B‖` times their distance. -/
theorem abs_expectation_mk_sub_le {w w₀ : EuclideanSpace ℂ (Fin (N + 1))} (hw : w ≠ 0)
    (hw₀ : w₀ ≠ 0) (h1 : ‖w‖ = 1) (h2 : ‖w₀‖ = 1) :
    |expectation B (mk ℂ w hw) - expectation B (mk ℂ w₀ hw₀)| ≤ 2 * ‖B‖ * ‖w - w₀‖ := by
  rw [expectation_mk, expectation_mk, h1, h2, one_pow, div_one, div_one, ← Complex.sub_re]
  have hsplit : inner ℂ w (Matrix.toEuclideanLin B w) - inner ℂ w₀ (Matrix.toEuclideanLin B w₀)
      = inner ℂ (w - w₀) (Matrix.toEuclideanLin B w)
        + inner ℂ w₀ (Matrix.toEuclideanLin B (w - w₀)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  calc |(inner ℂ w (Matrix.toEuclideanLin B w)
          - inner ℂ w₀ (Matrix.toEuclideanLin B w₀)).re|
      ≤ ‖inner ℂ w (Matrix.toEuclideanLin B w) - inner ℂ w₀ (Matrix.toEuclideanLin B w₀)‖ :=
        Complex.abs_re_le_norm _
    _ = ‖inner ℂ (w - w₀) (Matrix.toEuclideanLin B w)
          + inner ℂ w₀ (Matrix.toEuclideanLin B (w - w₀))‖ := by rw [hsplit]
    _ ≤ ‖w - w₀‖ * ‖Matrix.toEuclideanLin B w‖ + ‖w₀‖ * ‖Matrix.toEuclideanLin B (w - w₀)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ ‖w - w₀‖ * (‖B‖ * ‖w‖) + ‖w₀‖ * (‖B‖ * ‖w - w₀‖) := by
        gcongr
        · exact norm_toEuclideanLin_le B w
        · exact norm_toEuclideanLin_le B (w - w₀)
    _ = 2 * ‖B‖ * ‖w - w₀‖ := by rw [h1, h2]; ring

/-- Every ray has a unit representative. -/
theorem exists_unit_mk (x : CPN (N + 1)) :
    ∃ (v : EuclideanSpace ℂ (Fin (N + 1))) (hv : v ≠ 0), ‖v‖ = 1 ∧ x = mk ℂ v hv := by
  have h0 : x.rep ≠ 0 := x.rep_nonzero
  have hn : ((‖x.rep‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have hv : ((‖x.rep‖ : ℂ))⁻¹ • x.rep ≠ 0 := smul_ne_zero (inv_ne_zero hn) h0
  refine ⟨_, hv, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  · have h : mk ℂ _ hv = mk ℂ x.rep h0 :=
      (mk_eq_mk_iff ℂ _ x.rep hv h0).2 ⟨Units.mk0 _ (inv_ne_zero hn), rfl⟩
    rw [h, mk_rep]

theorem abs_schrodingerHamiltonian_le (x : CPN (N + 1)) :
    |schrodingerHamiltonian B x| ≤ 2 * ‖B‖ := by
  rw [schrodingerHamiltonian, abs_mul, abs_neg, abs_two]
  exact mul_le_mul_of_nonneg_left (abs_expectation_le B x) zero_le_two

/-- ★ **A coupled energy is `EpsProjectable` at `2‖B‖osc`**, where `osc` bounds the oscillation of `f`. -/
theorem epsProjectable_coupledEnergy (hf : Function.Periodic f 1) {osc : ℝ}
    (hosc : ∀ a b, |f a - f b| ≤ osc) :
    EpsProjectable (coupledEnergy A B hf) (2 * ‖B‖ * osc) := by
  rw [epsProjectable_coupledEnergy_iff]
  intro x a b
  exact mul_le_mul (abs_schrodingerHamiltonian_le B x) (hosc a b) (abs_nonneg _) (by positivity)

/-- The coupled energy is differentiable, with fibre part `v ↦ −2⟨B⟩(x) f'(θ₂) v₂`. -/
theorem exists_hasMFDerivAt_coupledEnergy (hf : Function.Periodic f 1) (hd : Differentiable ℝ f)
    (p : KSigma (N + 1)) :
    ∃ L : ArenaModel N →L[ℝ] ℝ, HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) (coupledEnergy A B hf) p L
      ∧ ∀ v : ℝ × ℝ, L (0, v) = schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2 * v.2 := by
  have hA : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => schrodingerHamiltonian A q.1) p
      ((mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian A) p.1).comp
        (ContinuousLinearMap.fst ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
    (mdifferentiableAt_schrodingerHamiltonian A p.1).hasMFDerivAt.comp p
      (Prod.hasMFDerivAt_fst_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
  have ha : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => schrodingerHamiltonian B q.1) p
      ((mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian B) p.1).comp
        (ContinuousLinearMap.fst ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
    (mdifferentiableAt_schrodingerHamiltonian B p.1).hasMFDerivAt.comp p
      (Prod.hasMFDerivAt_fst_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
  have hb : HasMFDerivAt 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ)
      (fun q : KSigma (N + 1) => torusPotential hf q.2) p
      ((((1 : ℝ →L[ℝ] ℝ).smulRight (hf.deriv_periodic.lift p.2.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp (ContinuousLinearMap.snd ℝ (Fin N → ℂ) (ℝ × ℝ))) :=
    (hasMFDerivAt_torusPotential hf hd p.2).comp p
      (Prod.hasMFDerivAt_snd_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)
  refine ⟨_, hA.add (ha.mul hb), fun v => ?_⟩
  have h0A : (show ℝ from (mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian A) p.1) 0) = 0 :=
    map_zero _
  have h0B : (show ℝ from (mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian B) p.1) 0) = 0 :=
    map_zero _
  show (show ℝ from (mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian A) p.1) 0)
      + (schrodingerHamiltonian B p.1 * (v.2 * hf.deriv_periodic.lift p.2.2)
        + torusPotential hf p.2
          * (show ℝ from (mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) (schrodingerHamiltonian B) p.1) 0))
    = schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2 * v.2
  rw [h0A, h0B]
  ring

theorem mdifferentiable_coupledEnergy (hf : Function.Periodic f 1) (hd : Differentiable ℝ f) :
    MDifferentiable 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) (coupledEnergy A B hf) := fun p =>
  (exists_hasMFDerivAt_coupledEnergy A B hf hd p).choose_spec.1.mdifferentiableAt

/-- ★ **The vertical derivative of the coupled energy**: `d𝓗|_V = −2⟨B⟩(x) f'(θ₂) dθ₂`. -/
theorem verticalDeriv_coupledEnergy (hf : Function.Periodic f 1) (hd : Differentiable ℝ f)
    (p : KSigma (N + 1)) :
    verticalDeriv (coupledEnergy A B hf) p
      = (schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2)
          • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  obtain ⟨L, hL, hv⟩ := exists_hasMFDerivAt_coupledEnergy A B hf hd p
  rw [verticalDeriv, hL.mfderiv]
  refine ContinuousLinearMap.ext fun v => ?_
  exact hv v

theorem norm_verticalDeriv_coupledEnergy_le (hf : Function.Periodic f 1) (hd : Differentiable ℝ f)
    (p : KSigma (N + 1)) :
    ‖verticalDeriv (coupledEnergy A B hf) p‖
      ≤ |schrodingerHamiltonian B p.1| * |hf.deriv_periodic.lift p.2.2| := by
  rw [verticalDeriv_coupledEnergy A B hf hd]
  calc ‖(schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2)
          • ContinuousLinearMap.snd ℝ ℝ ℝ‖
      ≤ ‖schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2‖
          * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖schrodingerHamiltonian B p.1 * hf.deriv_periodic.lift p.2.2‖ * 1 :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) (norm_nonneg _)
    _ = |schrodingerHamiltonian B p.1| * |hf.deriv_periodic.lift p.2.2| := by
        rw [mul_one, Real.norm_eq_abs, abs_mul]

/-- ★ **The coupled energy is `EpsProjectable` in derivative form at `2‖B‖D`**, where `D` bounds
`|f'|`. -/
theorem epsProjectableDeriv_coupledEnergy (hf : Function.Periodic f 1) (hd : Differentiable ℝ f)
    {D : ℝ} (hD : ∀ a, |deriv f a| ≤ D) :
    EpsProjectableDeriv (coupledEnergy A B hf) (2 * ‖B‖ * D) := by
  intro p
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective p.2.2
  refine (norm_verticalDeriv_coupledEnergy_le A B hf hd p).trans ?_
  have : hf.deriv_periodic.lift p.2.2 = deriv f a := by
    rw [← ha]; exact hf.deriv_periodic.lift_coe a
  rw [this]
  exact mul_le_mul (abs_schrodingerHamiltonian_le B p.1) (hD a) (abs_nonneg _) (by positivity)

/-! ### The shadowing bound on the arena -/

variable {A B}

/-- The Schrödinger unitary moves a ray through any of its representatives. -/
theorem schrodingerUnitary_smul_mk {H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hH : H.IsHermitian)
    (t : ℝ) (v : EuclideanSpace ℂ (Fin (N + 1))) (hv : v ≠ 0) :
    ∃ hw : Matrix.toEuclideanLin (exp (t • ((-Complex.I) • H))) v ≠ 0,
      ‖Matrix.toEuclideanLin (exp (t • ((-Complex.I) • H))) v‖ = ‖v‖
        ∧ Matrix.schrodingerUnitary hH t • mk ℂ v hv
          = mk ℂ (Matrix.toEuclideanLin (exp (t • ((-Complex.I) • H))) v) hw := by
  have hval : ((Matrix.schrodingerUnitary hH t : Matrix.unitaryGroup (Fin (N + 1)) ℂ) :
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) = exp (t • ((-Complex.I) • H)) := by
    show exp (Matrix.schrodingerGen H t) = _
    congr 1
    ext i j
    simp only [Matrix.schrodingerGen, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    ring
  have hw' : Matrix.toEuclideanLin ((Matrix.schrodingerUnitary hH t :
      Matrix.unitaryGroup (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) v ≠ 0 :=
    (Matrix.UnitaryGroup.toEuclideanLinearEquiv (Matrix.schrodingerUnitary hH t)).map_ne_zero_iff.2 hv
  refine ⟨hval ▸ hw', ?_, ?_⟩
  · rw [← hval]
    exact norm_toEuclideanLin_unitary _ v
  have h : Matrix.schrodingerUnitary hH t • mk ℂ v hv
      = mk ℂ (Matrix.toEuclideanLin ((Matrix.schrodingerUnitary hH t :
          Matrix.unitaryGroup (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) v) hw' :=
    rfl
  rw [h]
  congr 2
  exact congrArg _ hval

/-- The state-dependent matrices at two angles differ by the coupled term alone. -/
theorem norm_coupledMatrix_sub_le (hf : Function.Periodic f 1) {osc : ℝ}
    (hosc : ∀ a b, |f a - f b| ≤ osc) (φ φ₀ : AddCircle (1 : ℝ)) :
    ‖coupledMatrix A B hf φ - coupledMatrix A B hf φ₀‖ ≤ ‖B‖ * osc := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective φ
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective φ₀
  have h : coupledMatrix A B hf (a : AddCircle (1 : ℝ)) - coupledMatrix A B hf (b : AddCircle (1 : ℝ))
      = ((f a - f b : ℝ) : ℂ) • B := by
    unfold coupledMatrix
    rw [hf.lift_coe, hf.lift_coe, add_sub_add_left_eq_sub, ← sub_smul]
    push_cast
    rfl
  rw [h, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (hosc a b) (norm_nonneg _)

/-- ★★★ **The `(ε, T)` shadowing bound on the arena.** Start the Hamiltonian flow of a coupled
energy at `([v], θ)`, and start the flow of the **exactly projectable** sector energy of
`A + f(φ₀) B` (any reference angle `φ₀`) at the same point. For `|t| ≤ T` the two rays are
represented by vectors within `‖B‖·osc·T·‖v‖` of each other, where `osc` bounds the oscillation
of `f`. This is `quantum_effective_shadowing_state` carried from matrices to the arena: the ray
of the coupled flow is the Schrödinger orbit of `A + f(θ₂) B` (`hamiltonianFlow_coupledEnergy`),
the ray of the sector flow is that of `A + f(φ₀) B` (`hamiltonianFlow_sectorEnergy_schrodinger`),
and the two matrices are `‖B‖·osc`-close. -/
theorem coupledFlow_shadowing (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (φ₀ : AddCircle (1 : ℝ)) {osc T t : ℝ}
    (hosc : ∀ a b, |f a - f b| ≤ osc) (ht : |t| ≤ T) (v : EuclideanSpace ℂ (Fin (N + 1)))
    (hv : v ≠ 0) (θ : KTorus) :
    ∃ (w w₀ : EuclideanSpace ℂ (Fin (N + 1))) (hw : w ≠ 0) (hw₀ : w₀ ≠ 0),
      ((arenaForm_isSymplectic N).hamiltonianFlow (contMDiff_coupledEnergy A B hf hc) t
          (mk ℂ v hv, θ)).1 = mk ℂ w hw
      ∧ ((arenaForm_isSymplectic N).hamiltonianFlow
          (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (coupledMatrix A B hf φ₀))) t
          (mk ℂ v hv, θ)).1 = mk ℂ w₀ hw₀
      ∧ ‖w‖ = ‖v‖ ∧ ‖w₀‖ = ‖v‖
      ∧ ‖w - w₀‖ ≤ ‖B‖ * osc * T * ‖v‖ := by
  obtain ⟨hw, hn, hU⟩ := schrodingerUnitary_smul_mk (coupledMatrix_isHermitian hA hB hf θ.2) t v hv
  obtain ⟨hw₀, hn₀, hU₀⟩ :=
    schrodingerUnitary_smul_mk (coupledMatrix_isHermitian hA hB hf φ₀) t v hv
  refine ⟨_, _, hw, hw₀, ?_, ?_, hn, hn₀, ?_⟩
  · rw [hamiltonianFlow_coupledEnergy hA hB hf hc]
    exact hU
  · rw [hamiltonianFlow_sectorEnergy_schrodinger (coupledMatrix_isHermitian hA hB hf φ₀)]
    exact hU₀
  · exact quantum_effective_shadowing_state (coupledMatrix_isHermitian hA hB hf θ.2)
      (coupledMatrix_isHermitian hA hB hf φ₀) (norm_coupledMatrix_sub_le hf hosc θ.2 φ₀) ht v

/-- ★★★ **Every sector prediction is shadowed.** For every matrix `O`, every ray `x` and every
fibre point `θ`, the expectation of `O` on the ray of the coupled flow and on the ray of the
exactly projectable sector flow of `A + f(φ₀) B` differ by at most `2‖O‖·‖B‖·osc·T` over
`|t| ≤ T`. Stated on rays, so no representative is chosen. -/
theorem coupledFlow_expectation_shadowing (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (φ₀ : AddCircle (1 : ℝ)) {osc T t : ℝ}
    (hosc : ∀ a b, |f a - f b| ≤ osc) (ht : |t| ≤ T) (O : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (x : CPN (N + 1)) (θ : KTorus) :
    |expectation O ((arenaForm_isSymplectic N).hamiltonianFlow (contMDiff_coupledEnergy A B hf hc) t
          (x, θ)).1
      - expectation O ((arenaForm_isSymplectic N).hamiltonianFlow
          (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian (coupledMatrix A B hf φ₀))) t
          (x, θ)).1|
      ≤ 2 * ‖O‖ * (‖B‖ * osc * T) := by
  obtain ⟨v, hv, hv1, rfl⟩ := exists_unit_mk x
  obtain ⟨w, w₀, hw, hw₀, h1, h2, hn, hn₀, hd⟩ :=
    coupledFlow_shadowing hA hB hf hc φ₀ hosc ht v hv θ
  rw [h1, h2]
  refine (abs_expectation_mk_sub_le O hw hw₀ (hn.trans hv1) (hn₀.trans hv1)).trans ?_
  rw [hv1, mul_one] at hd
  exact mul_le_mul_of_nonneg_left hd (by positivity)

/-! ### The activated write -/

section Activated

variable (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- The coupled term of the activated write is bounded by `2|g|/|ħ|` on all of `Σ`. -/
theorem abs_schrodingerHamiltonian_hamB_le (q : CPN 4) :
    |schrodingerHamiltonian (hamB g ħ) q| ≤ 2 * |g| / |ħ| := by
  obtain ⟨p, rfl⟩ := (CV.arenaEquiv 2 2).surjective q
  rw [schrodingerHamiltonian_hamB, abs_mul, abs_neg, abs_div, abs_mul, abs_two,
    abs_of_nonneg (momentMap_nonneg p CV.excB)]
  have h1 := momentMap_le_one p CV.excB
  have h2 : 0 ≤ 2 * |g| / |ħ| := by positivity
  nlinarith

/-- … and the bound is attained, at the ray where the receiver is occupied. -/
theorem exists_abs_schrodingerHamiltonian_hamB_eq :
    ∃ q : CPN 4, |schrodingerHamiltonian (hamB g ħ) q| = 2 * |g| / |ħ| := by
  have hv : (EuclideanSpace.single CV.excB (1 : ℂ)) ≠ 0 := by
    intro h
    have := congrArg (fun w : EuclideanSpace ℂ CV.HopConfig => w CV.excB) h
    simp at this
  refine ⟨CV.arenaEquiv 2 2 (mk ℂ _ hv), ?_⟩
  rw [schrodingerHamiltonian_hamB, momentMap_mk]
  simp [abs_div, abs_mul]

/-- ★★ **The activated energy's fibre oscillation, exactly**: it is `EpsProjectable` at `ε`
precisely when `ε ≥ (2|g|/|ħ|)·|f(a) − f(b)|` for all `a, b`. The `ε` of the row is therefore
`(2|g|/|ħ|)·osc f`, and no smaller one works. -/
theorem epsProjectable_activatedEnergy_iff {ε : ℝ} :
    EpsProjectable (activatedEnergy J ħ g hf) ε ↔ ∀ a b : ℝ, 2 * |g| / |ħ| * |f a - f b| ≤ ε := by
  show EpsProjectable (coupledEnergy (hamA J ħ) (hamB g ħ) hf) ε ↔ _
  rw [epsProjectable_coupledEnergy_iff]
  constructor
  · intro h a b
    obtain ⟨q, hq⟩ := exists_abs_schrodingerHamiltonian_hamB_eq ħ g
    have := h q a b
    rwa [hq] at this
  · intro h q a b
    exact (mul_le_mul_of_nonneg_right (abs_schrodingerHamiltonian_hamB_le ħ g q)
      (abs_nonneg _)).trans (h a b)

/-- ★ **The activated energy is `EpsProjectable` at `(2|g|/|ħ|)·osc`.** -/
theorem epsProjectable_activatedEnergy {osc : ℝ} (hosc : ∀ a b, |f a - f b| ≤ osc) :
    EpsProjectable (activatedEnergy J ħ g hf) (2 * |g| / |ħ| * osc) :=
  (epsProjectable_activatedEnergy_iff J ħ g hf).2 fun a b =>
    mul_le_mul_of_nonneg_left (hosc a b) (by positivity)

/-- ★★ **And it does not factor through `π`**: a nonzero coupling to a nonconstant potential is
not `EpsProjectable` at `0`. -/
theorem activatedEnergy_not_projectable (hg : g ≠ 0) (hħ : ħ ≠ 0) {a b : ℝ} (hab : f a ≠ f b) :
    ¬ EpsProjectable (activatedEnergy J ħ g hf) 0 := by
  rw [epsProjectable_activatedEnergy_iff]
  intro h
  have hpos : 0 < 2 * |g| / |ħ| * |f a - f b| :=
    mul_pos (div_pos (mul_pos two_pos (abs_pos.2 hg)) (abs_pos.2 hħ))
      (abs_pos.2 (sub_ne_zero.2 hab))
  linarith [h a b]

/-- ★ **The activated energy in derivative form**: `sup ‖d𝓗|_V‖ ≤ (2|g|/|ħ|)·D`, where `D` bounds
the derivative of `f`. -/
theorem epsProjectableDeriv_activatedEnergy (hd : Differentiable ℝ f) {D : ℝ}
    (hD : ∀ a, |deriv f a| ≤ D) :
    EpsProjectableDeriv (activatedEnergy J ħ g hf) (2 * |g| / |ħ| * D) := by
  intro p
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective p.2.2
  refine (norm_verticalDeriv_coupledEnergy_le (hamA J ħ) (hamB g ħ) hf hd p).trans ?_
  have : hf.deriv_periodic.lift p.2.2 = deriv f a := by
    rw [← ha]; exact hf.deriv_periodic.lift_coe a
  rw [this]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  exact mul_le_mul (abs_schrodingerHamiltonian_hamB_le ħ g p.1) (hD a) (abs_nonneg _)
    (by positivity)

/-- The derivative form, integrated: the activated energy is `EpsProjectable` at `(|g|/|ħ|)·D`. -/
theorem epsProjectable_activatedEnergy_of_deriv (hd : Differentiable ℝ f) {D : ℝ}
    (hD : ∀ a, |deriv f a| ≤ D) :
    EpsProjectable (activatedEnergy J ħ g hf) (|g| / |ħ| * D) := by
  have h := epsProjectable_of_deriv (mdifferentiable_coupledEnergy (hamA J ħ) (hamB g ħ) hf hd)
    (epsProjectableDeriv_activatedEnergy J ħ g hf hd hD)
  rwa [show 2 * |g| / |ħ| * D / 2 = |g| / |ħ| * D by ring] at h

/-- The receiver occupancy has operator norm one, so the coupling matrix has norm `|g|/|ħ|`. -/
theorem norm_hamB : ‖hamB g ħ‖ = |g| / |ħ| := by
  have h : Matrix.reindex hopIdx hopIdx CV.occB
      = Matrix.diagonal (Pi.single (hopIdx CV.excB) (1 : ℂ)) := by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, CV.occB, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = hopIdx CV.excB
      · subst hi
        simp
      · have : hopIdx.symm i ≠ CV.excB := fun h => hi (by rw [← h, Equiv.apply_symm_apply])
        simp [hi, Ne.symm this]
    · have : hopIdx.symm i ≠ hopIdx.symm j := fun h => hij (hopIdx.symm.injective h)
      simp only [Matrix.single_apply, hij, ite_false]
      split_ifs with h1
      · exact absurd (h1.1.symm.trans h1.2) this
      · rfl
  rw [hamB, reindex_smul_hop, h, norm_smul, Matrix.l2_opNorm_diagonal, Pi.norm_single, norm_one,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div]

/-- ★★★ **The `(ε, T)` shadowing bound for the activated write.** Over `|t| ≤ T` the ray of the
activated flow and the ray of the exactly projectable sector flow of `A + f(φ₀) B` stay represented
within `(|g|/|ħ|)·osc·T·‖v‖`: the matrix-level constant is **half** the sharp ontic `ε`
(`epsProjectable_activatedEnergy_iff`), the factor `2` being the corpus's `−2⟨·⟩` normalisation. -/
theorem activated_shadowing (hc : ContDiff ℝ ∞ f) (φ₀ : AddCircle (1 : ℝ)) {osc T t : ℝ}
    (hosc : ∀ a b, |f a - f b| ≤ osc) (ht : |t| ≤ T) (v : EuclideanSpace ℂ (Fin 4)) (hv : v ≠ 0)
    (θ : KTorus) :
    ∃ (w w₀ : EuclideanSpace ℂ (Fin 4)) (hw : w ≠ 0) (hw₀ : w₀ ≠ 0),
      ((arenaForm_isSymplectic 3).hamiltonianFlow (contMDiff_activatedEnergy J ħ g hf hc) t
          (mk ℂ v hv, θ)).1 = mk ℂ w hw
      ∧ ((arenaForm_isSymplectic 3).hamiltonianFlow
          (contMDiff_sectorEnergy
            (contMDiff_schrodingerHamiltonian (coupledMatrix (hamA J ħ) (hamB g ħ) hf φ₀))) t
          (mk ℂ v hv, θ)).1 = mk ℂ w₀ hw₀
      ∧ ‖w‖ = ‖v‖ ∧ ‖w₀‖ = ‖v‖
      ∧ ‖w - w₀‖ ≤ |g| / |ħ| * osc * T * ‖v‖ := by
  have h := coupledFlow_shadowing (hamA_isHermitian J ħ) (hamB_isHermitian g ħ) hf hc φ₀ hosc ht
    v hv θ
  rwa [norm_hamB] at h

/-- ★★★ **The activated write's sector predictions are shadowed at the ontic `ε`.** For every
matrix `O` the expectation on the ray of the activated flow and on the ray of the exactly
projectable sector flow differ by at most `‖O‖·ε·T` over `|t| ≤ T`, where `ε = (2|g|/|ħ|)·osc`
is the sharp fibre oscillation of the activated energy (`epsProjectable_activatedEnergy_iff`). -/
theorem activated_expectation_shadowing (hc : ContDiff ℝ ∞ f) (φ₀ : AddCircle (1 : ℝ))
    {osc T t : ℝ} (hosc : ∀ a b, |f a - f b| ≤ osc) (ht : |t| ≤ T)
    (O : Matrix (Fin 4) (Fin 4) ℂ) (x : CPN 4) (θ : KTorus) :
    |expectation O ((arenaForm_isSymplectic 3).hamiltonianFlow
          (contMDiff_activatedEnergy J ħ g hf hc) t (x, θ)).1
      - expectation O ((arenaForm_isSymplectic 3).hamiltonianFlow
          (contMDiff_sectorEnergy
            (contMDiff_schrodingerHamiltonian (coupledMatrix (hamA J ħ) (hamB g ħ) hf φ₀))) t
          (x, θ)).1|
      ≤ ‖O‖ * (2 * |g| / |ħ| * osc) * T := by
  have h := coupledFlow_expectation_shadowing (hamA_isHermitian J ħ) (hamB_isHermitian g ħ) hf hc
    φ₀ hosc ht O x θ
  rw [norm_hamB] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- ★★★ **A5's approximate regime, as a dynamical statement, on the activated write.** On
`Σ = ℂℙ³ × T²` with the arena symplectic form, for `f` smooth of period one with oscillation at
most `osc` and slope at most `D`:

* the activated energy is `EpsProjectable` at `ε` exactly when `ε ≥ (2|g|/|ħ|)·|f(a) − f(b)|`, so
  in particular at `(2|g|/|ħ|)·osc`;
* with `g ≠ 0`, `ħ ≠ 0` and `f` nonconstant it is not `EpsProjectable` at `0`;
* in derivative form `sup‖d𝓗|_V‖ ≤ (2|g|/|ħ|)·D`;
* its Hamiltonian flow is #194's `activeFlow`, read through the index bridge;
* every sector expectation of its flow is shadowed by the exactly projectable sector flow to within
  `‖O‖·(2|g|/|ħ|)·osc·T` over `|t| ≤ T`. -/
theorem activated_regime (hc : ContDiff ℝ ∞ f) {osc D : ℝ} (hosc : ∀ a b, |f a - f b| ≤ osc)
    (hD : ∀ a, |deriv f a| ≤ D) :
    (∀ ε : ℝ, EpsProjectable (activatedEnergy J ħ g hf) ε
        ↔ ∀ a b : ℝ, 2 * |g| / |ħ| * |f a - f b| ≤ ε)
      ∧ EpsProjectable (activatedEnergy J ħ g hf) (2 * |g| / |ħ| * osc)
      ∧ (g ≠ 0 → ħ ≠ 0 → ∀ a b : ℝ, f a ≠ f b → ¬ EpsProjectable (activatedEnergy J ħ g hf) 0)
      ∧ EpsProjectableDeriv (activatedEnergy J ħ g hf) (2 * |g| / |ħ| * D)
      ∧ (∀ (t : ℝ) (x : ActiveArena),
          (arenaForm_isSymplectic 3).hamiltonianFlow (contMDiff_activatedEnergy J ħ g hf hc) t
              (CV.fibredArenaEquiv 2 2 x)
            = CV.fibredArenaEquiv 2 2 (activeFlow J ħ g hf t x))
      ∧ (∀ (φ₀ : AddCircle (1 : ℝ)) (T t : ℝ), |t| ≤ T →
          ∀ (O : Matrix (Fin 4) (Fin 4) ℂ) (x : CPN 4) (θ : KTorus),
            |expectation O ((arenaForm_isSymplectic 3).hamiltonianFlow
                  (contMDiff_activatedEnergy J ħ g hf hc) t (x, θ)).1
              - expectation O ((arenaForm_isSymplectic 3).hamiltonianFlow
                  (contMDiff_sectorEnergy
                    (contMDiff_schrodingerHamiltonian (coupledMatrix (hamA J ħ) (hamB g ħ) hf φ₀)))
                  t (x, θ)).1|
              ≤ ‖O‖ * (2 * |g| / |ħ| * osc) * T) :=
  ⟨fun _ => epsProjectable_activatedEnergy_iff J ħ g hf,
    epsProjectable_activatedEnergy J ħ g hf hosc,
    fun hg hħ _ _ hab => activatedEnergy_not_projectable J ħ g hf hg hħ hab,
    epsProjectableDeriv_activatedEnergy J ħ g hf (hc.differentiable (by simp)) hD,
    hamiltonianFlow_activeFlow J ħ g hf hc,
    fun φ₀ _ _ ht O x θ => activated_expectation_shadowing J ħ g hf hc φ₀ hosc ht O x θ⟩

end Activated

end SigmaLayer
end CSD

end

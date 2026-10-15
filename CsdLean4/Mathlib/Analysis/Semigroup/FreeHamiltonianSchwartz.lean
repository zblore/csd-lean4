/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.FreeHamiltonian
public import CsdLean4.Mathlib.Analysis.Semigroup.SchrodingerSchwartz
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# The free Hamiltonian in position space is `−½ d²/dx²`, on Schwartz functions

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #128 (out of ~~#64(i)~~).

`FreeHamiltonian.lean` built the free Hamiltonian in the position representation,
`freePositionOp`, as the Fourier conjugate of multiplication by the symbol `2π²ξ²`, and proved it
self-adjoint with spectrum `[0, ∞)`. The name says `−½Δ`; the construction says "conjugate of a
multiplier". This file makes the name honest on the **Schwartz core**: for every Schwartz function
`φ`, its `L²` class lies in the domain of `freePositionOp`, and the operator sends it to the `L²`
class of `−½ φ''`.

* `fourier_kineticOp`: the transform of the Schwartz kinetic operator `kineticOp φ`
  (`SchrodingerSchwartz.lean`, already identified with `−½Δφ` there) is the symbol times the
  transform of `φ`, pointwise `𝓕(H₀φ)(ξ) = 2π²ξ² · 𝓕φ(ξ)` (`fourier_kineticOp_apply`);
* `toLp_fourier_mem_freeSymbolOp_domain`, ★ `freeSymbolOp_toLp_fourier`: in the momentum
  representation the multiplier acts on `(𝓕φ).toLp` exactly as the transform of `H₀φ`;
* `toLp_mem_freePositionOp_domain`: **Schwartz functions lie in the position-space domain**;
* ★★ `freePositionOp_toLp`: `freePositionOp (φ.toLp) = (kineticOp φ).toLp`, hence
  ★★★ `freePositionOp_toLp_eq_laplacian`: `= ((−½) • Δφ).toLp`, and pointwise almost everywhere
  ★★★ `freePositionOp_toLp_ae`: `= −½ · φ''` (`iteratedDeriv 2 φ`, i.e. `deriv (deriv φ)`,
  `freePositionOp_toLp_ae_deriv`).
* `freeSymbol_eq_neg_half_mul_sq` records the convention the row flagged: with Mathlib's
  `𝓕 f (ξ) = ∫ e^{−2πixξ} f(x) dx`, the symbol `2π²ξ²` *is* `−½ (2πiξ)²`, which is why
  `−½ d²/dx²` has this symbol and not `½ξ²`.

Every step moves across the transform by Mathlib's own bridges — `SchwartzMap.toLp_fourier_eq`,
`toLp_fourierInv_eq` (the `L²` Fourier transform agrees with the Schwartz one on Schwartz
classes) and the Schwartz Fourier inversion — so nothing about `L²` limits is re-proved here.

## Honest scope

* **The Schwartz core only.** The row asked for two things: (a) the Fourier–derivative identity on
  the whole domain `𝓕⁻¹{(1 + ξ²) f ∈ L²}`, and (b) the identification of that domain with the Sobolev
  space `H²(ℝ)`. This file proves (a) on Schwartz functions and does **not** prove that Schwartz
  functions are a core for `freePositionOp` (that its closure from the Schwartz restriction is the
  whole operator), nor (b): Mathlib has no `H^s` scale on `Lp` at this pin, and `H²` is a definition
  before it is a theorem. What is proved is that the self-adjoint operator of #64(i) **restricts to
  `−½ d²/dx²` on every Schwartz function**, which is the sense in which an analyst reads the name.
* **One dimension**, as in `FreeHamiltonian.lean`; the Laplacian form `freePositionOp_toLp_eq_laplacian`
  is the one that would survive to `ℝⁿ`, and the second-derivative form is its reading on `ℝ`
  (`laplacian_eq_iteratedDeriv_real`).
* Nothing here is a dynamics statement: `PhaseGenerator.lean` already has the Schrödinger equation
  with `freePositionOp` as generator; this file says what that generator *is* on smooth data.

References: Reed–Simon I §IX.7 (the free Hamiltonian on `H²`); `FreeHamiltonian.lean`
(`freeSymbolOp`, `freePositionOp`, `freePositionOp_apply`), `SchrodingerSchwartz.lean`
(`kineticOp`, `kineticOp_eq_laplacian`), `PhaseGenerator.lean`
(`hasDerivAt_fourierGroup_freePositionOp`); Mathlib `SchwartzMap.toLp_fourier_eq`,
`SchwartzMap.laplacian_apply`, `InnerProductSpace.laplacian_eq_iteratedDeriv_real`;
`specs/BACKLOG.md` #128, ~~#64~~.
-/

@[expose] public section

open scoped ENNReal SchwartzMap FourierTransform Laplacian
open MeasureTheory SchwartzMap FourierTransform

noncomputable section

namespace SchrodingerGroup

/-! ### The convention -/

/-- **The convention, as an identity.** With `𝓕` carrying `e^{−2πixξ}`, the free symbol `2π²ξ²` is
`−½ (2πiξ)²`: the symbol of `−½ d²/dx²`. -/
theorem freeSymbol_eq_neg_half_mul_sq (ξ : ℝ) :
    (freeSymbol ξ : ℂ) = -(1 / 2 : ℂ) * (2 * Real.pi * Complex.I * ξ) ^ 2 := by
  rw [freeSymbol_real]
  push_cast
  linear_combination (2 * (Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2) * Complex.I_sq

/-! ### The transform of the kinetic operator -/

/-- The transform of the Schwartz kinetic operator is the symbol times the transform. -/
theorem fourier_kineticOp (φ : 𝓢(ℝ, ℂ)) :
    𝓕 (kineticOp (E := ℝ) φ) = smulLeftCLM (𝕜 := ℝ) ℂ (freeSymbol (E := ℝ)) (𝓕 φ) := by
  rw [kineticOp, fourierMultiplierCLM_apply, fourier_fourierInv_eq]

/-- Pointwise: `𝓕(H₀φ)(ξ) = 2π²ξ² · 𝓕φ(ξ)`. -/
theorem fourier_kineticOp_apply (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (kineticOp (E := ℝ) φ) ξ = (freeSymbol ξ : ℂ) * 𝓕 φ ξ := by
  rw [fourier_kineticOp, smulLeftCLM_apply_apply hasTemperateGrowth_freeSymbol, Complex.real_smul]

/-! ### The momentum representation on Schwartz classes -/

/-- The transform of a Schwartz function lies in the domain of the momentum-space operator. -/
theorem toLp_fourier_mem_freeSymbolOp_domain (φ : 𝓢(ℝ, ℂ)) :
    (𝓕 φ).toLp 2 ∈ freeSymbolOp.domain := by
  rw [freeSymbolOp, L2.mulOp_domain, L2.mem_mulDomain_iff]
  refine ((𝓕 (kineticOp (E := ℝ) φ)).memLp 2).ae_eq ?_
  filter_upwards [(𝓕 φ).coeFn_toLp 2] with ξ hξ
  rw [hξ, fourier_kineticOp_apply]

/-- The momentum-space operator, pointwise almost everywhere: multiplication by the symbol. Stated
for a variable of the domain so that its instances at concrete elements need no unfolding. -/
theorem coeFn_freeSymbolOp (f : freeSymbolOp.domain) :
    (freeSymbolOp f : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
      fun ξ => (freeSymbol ξ : ℂ) * (f : Lp ℂ 2 (volume : Measure ℝ)) ξ :=
  L2.coeFn_mulOp f

/-- ★ **The multiplier acts on a Schwartz transform as the transform of the kinetic operator**,
stated for any element of the domain whose coordinate is the transform's class. -/
theorem freeSymbolOp_eq_of_coe_eq (φ : 𝓢(ℝ, ℂ)) (f : freeSymbolOp.domain)
    (hf : (f : Lp ℂ 2 (volume : Measure ℝ)) = (𝓕 φ).toLp 2) :
    freeSymbolOp f = (𝓕 (kineticOp (E := ℝ) φ)).toLp 2 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_freeSymbolOp f, (𝓕 φ).coeFn_toLp 2,
    (𝓕 (kineticOp (E := ℝ) φ)).coeFn_toLp 2] with ξ h1 h2 h3
  rw [h1, h3, fourier_kineticOp_apply, hf, h2]

/-- ★ The same at the canonical element. -/
theorem freeSymbolOp_toLp_fourier (φ : 𝓢(ℝ, ℂ)) :
    freeSymbolOp ⟨(𝓕 φ).toLp 2, toLp_fourier_mem_freeSymbolOp_domain φ⟩
      = (𝓕 (kineticOp (E := ℝ) φ)).toLp 2 :=
  freeSymbolOp_eq_of_coe_eq φ _ rfl

/-! ### The position representation on Schwartz classes -/

/-- The `L²` inverse transform of a Schwartz transform is the Schwartz class itself. -/
theorem fourierL2_symm_toLp_fourier (ψ : 𝓢(ℝ, ℂ)) :
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm ((𝓕 ψ).toLp 2 volume) = ψ.toLp 2 volume := by
  have h : 𝓕⁻ ((𝓕 ψ).toLp 2 (volume : Measure ℝ)) = (𝓕⁻ (𝓕 ψ)).toLp 2 volume :=
    SchwartzMap.toLp_fourierInv_eq (𝓕 ψ)
  rw [fourierInv_fourier_eq] at h
  exact h

/-- **Schwartz functions lie in the position-space domain** of the free Hamiltonian. -/
theorem toLp_mem_freePositionOp_domain (φ : 𝓢(ℝ, ℂ)) :
    φ.toLp 2 volume ∈ freePositionOp.domain := by
  have h := LinearPMap.mem_conjIsometry_domain (Lp.fourierTransformₗᵢ ℝ ℂ).symm freeSymbolOp
    (toLp_fourier_mem_freeSymbolOp_domain φ)
  rwa [fourierL2_symm_toLp_fourier] at h

/-- ★★ **On a Schwartz class the position-space free Hamiltonian is the kinetic operator.** -/
theorem freePositionOp_toLp (φ : 𝓢(ℝ, ℂ)) :
    freePositionOp ⟨φ.toLp 2, toLp_mem_freePositionOp_domain φ⟩
      = (kineticOp (E := ℝ) φ).toLp 2 := by
  have h := LinearPMap.conjIsometry_apply_of_eq (Lp.fourierTransformₗᵢ ℝ ℂ).symm freeSymbolOp
    ⟨(𝓕 φ).toLp 2, toLp_fourier_mem_freeSymbolOp_domain φ⟩
    ⟨φ.toLp 2, toLp_mem_freePositionOp_domain φ⟩ (fourierL2_symm_toLp_fourier φ).symm
  rw [freeSymbolOp_toLp_fourier, fourierL2_symm_toLp_fourier] at h
  exact h

/-- ★★★ **The free Hamiltonian in position space is `−½Δ` on Schwartz functions.** -/
theorem freePositionOp_toLp_eq_laplacian (φ : 𝓢(ℝ, ℂ)) :
    freePositionOp ⟨φ.toLp 2, toLp_mem_freePositionOp_domain φ⟩
      = ((-(1 / 2 : ℝ)) • Δ φ).toLp 2 := by
  rw [freePositionOp_toLp, kineticOp_eq_laplacian]

/-- ★★★ **Pointwise, almost everywhere: `(H₀ φ)(x) = −½ φ''(x)`.** -/
theorem freePositionOp_toLp_ae (φ : 𝓢(ℝ, ℂ)) :
    (freePositionOp ⟨φ.toLp 2, toLp_mem_freePositionOp_domain φ⟩ : Lp ℂ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun x => -(1 / 2 : ℂ) * iteratedDeriv 2 (φ : ℝ → ℂ) x := by
  rw [freePositionOp_toLp_eq_laplacian]
  filter_upwards [((-(1 / 2 : ℝ)) • Δ φ).coeFn_toLp 2] with x hx
  rw [hx, smul_apply, SchwartzMap.laplacian_apply,
    InnerProductSpace.laplacian_eq_iteratedDeriv_real, Complex.real_smul]
  congr 1
  norm_num

/-- The same, written with two derivatives: `(H₀ φ)(x) = −½ (φ')'(x)`. -/
theorem freePositionOp_toLp_ae_deriv (φ : 𝓢(ℝ, ℂ)) :
    (freePositionOp ⟨φ.toLp 2, toLp_mem_freePositionOp_domain φ⟩ : Lp ℂ 2 (volume : Measure ℝ))
      =ᵐ[volume] fun x => -(1 / 2 : ℂ) * deriv (deriv (φ : ℝ → ℂ)) x := by
  have h := freePositionOp_toLp_ae φ
  rwa [iteratedDeriv_succ, iteratedDeriv_one] at h

end SchrodingerGroup

end

end

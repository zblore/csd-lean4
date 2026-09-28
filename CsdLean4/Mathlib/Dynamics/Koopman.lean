/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The Koopman operator: classical mechanics in Hilbert space

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #47.

Koopman (1931) and von Neumann (1932): a measure-preserving flow on phase space acts on `L²(μ)` by
composition, `U_t f = f ∘ φ_t`, and that action is a **unitary group**. So Hilbert space, unitarity,
superposition and spectral theory are all available in *classical* mechanics. What is not available is
a noncommutative algebra of observables: classical observables multiply pointwise, and the Koopman
operator is an algebra homomorphism for that product (`koopmanFun_mul`). The commutator `[x, p] = iℏ`
is the one thing quantum mechanics adds — which is the sharpest statement of where the two theories
part.

* ★ `koopmanL2` — the Koopman operator of a measure-preserving map as a **linear isometry** of
  `L²(μ)`. Mathlib has the composition as an `AddMonoidHom` (`Lp.compMeasurePreserving`) and its
  isometry, but not the linear packaging, and no Koopman operator;
* ★★ `koopmanUnitary` — for an invertible measure-preserving map, the **unitary**: a
  `LinearIsometryEquiv` whose inverse is the Koopman operator of the inverse map;
* ★★ `koopmanL2_flow` — **the group law**: for a measure-preserving flow, `U_{s+t} = U_t ∘ U_s`, so
  `t ↦ U_t` is a one-parameter unitary group;
* `koopmanFun`, `koopmanFun_mul` — on observables the Koopman map is an algebra homomorphism for the
  pointwise product: the classical side of the contrast;
* ★ `hasDerivAt_koopmanFun` — **the generator on differentiable observables**: along a flow line,
  `d/dt (f ∘ φ_t)(x) = Df(φ_t x)[X(φ_t x)]`. For a Hamiltonian field that derivative is the Poisson
  bracket `{f, H}` — the Liouvillian — which is the corpus's `SigmaLayer/ChartBracket.lean`
  (`poissonBracket`, `BracketIsDerivative`).

## Honest scope

⚠️ **The generator is pointwise, on differentiable observables along a given flow line.** No
statement is made about the generator as an operator on `L²` — its domain, its self-adjointness, or
Stone's theorem for `t ↦ U_t`. That is the analytic half of Koopman–von Neumann and is not here.

⚠️ **The flow is a hypothesis.** `koopmanL2_flow` takes a family `φ` with the flow property and each
`φ t` measure preserving; that a Hamiltonian flow has those properties is Liouville's theorem, which
the corpus proves elsewhere (`LF4/ArenaSymplectic.lean`, `Q29`) and this module does not reprove.

⚠️ **The contrast is prose, deliberately.** `koopmanFun_mul` records that the classical observable
algebra is a commutative algebra carried by composition; no theorem here states a quantum commutator,
and none could witness the sentence "the commutator is what quantum mechanics adds". That sentence is
positioning, and it is the row's point.

References: B. O. Koopman, *Hamiltonian systems and transformations in Hilbert space*, PNAS 17 (1931)
315; J. von Neumann, *Zur Operatorenmethode in der klassischen Mechanik*, Ann. Math. 33 (1932) 587;
`specs/BACKLOG.md` #47; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace Koopman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### The Koopman operator on `L²` -/

/-- ★ **The Koopman operator** of a measure-preserving map: `f ↦ f ∘ T`, a linear isometry of
`L²(μ)`. -/
noncomputable def koopmanL2 (T : α → α) (hT : MeasurePreserving T μ μ) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := Lp.compMeasurePreserving T hT
  map_add' := (Lp.compMeasurePreserving T hT).map_add
  map_smul' c g := by
    refine Lp.ext_iff.mpr ?_
    calc ((Lp.compMeasurePreserving T hT (c • g) : Lp ℂ 2 μ) : α → ℂ)
        =ᵐ[μ] ((c • g : Lp ℂ 2 μ) : α → ℂ) ∘ T :=
          Lp.coeFn_compMeasurePreserving (c • g) hT
      _ =ᵐ[μ] (c • ((g : Lp ℂ 2 μ) : α → ℂ)) ∘ T :=
          hT.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c g)
      _ =ᵐ[μ] c • ((Lp.compMeasurePreserving T hT g : Lp ℂ 2 μ) : α → ℂ) :=
          ((Lp.coeFn_compMeasurePreserving g hT).const_smul c).symm
      _ =ᵐ[μ] ((c • Lp.compMeasurePreserving T hT g : Lp ℂ 2 μ) : α → ℂ) :=
          (Lp.coeFn_smul c _).symm
  norm_map' g := Lp.norm_compMeasurePreserving g hT

theorem coeFn_koopmanL2 (T : α → α) (hT : MeasurePreserving T μ μ) (g : Lp ℂ 2 μ) :
    (koopmanL2 T hT g : α → ℂ) =ᵐ[μ] (g : α → ℂ) ∘ T :=
  Lp.coeFn_compMeasurePreserving g hT

/-- ★★ **The Koopman operator of an invertible measure-preserving map is unitary**: composition with
the inverse map inverts it, and it is an isometry, so it is a `LinearIsometryEquiv` of `L²(μ)`. -/
noncomputable def koopmanUnitary (T T' : α → α) (hT : MeasurePreserving T μ μ)
    (hT' : MeasurePreserving T' μ μ) (hleft : ∀ y, T' (T y) = y) (hright : ∀ y, T (T' y) = y) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := koopmanL2 T hT
  map_add' := (koopmanL2 T hT).map_add
  map_smul' := (koopmanL2 T hT).map_smul
  invFun := koopmanL2 T' hT'
  left_inv g := by
    refine Lp.ext_iff.mpr ?_
    calc ((koopmanL2 T' hT' (koopmanL2 T hT g) : Lp ℂ 2 μ) : α → ℂ)
        =ᵐ[μ] ((koopmanL2 T hT g : Lp ℂ 2 μ) : α → ℂ) ∘ T' :=
          coeFn_koopmanL2 T' hT' _
      _ =ᵐ[μ] ((g : Lp ℂ 2 μ) : α → ℂ) ∘ T ∘ T' :=
          hT'.quasiMeasurePreserving.ae_eq_comp (coeFn_koopmanL2 T hT g)
      _ = ((g : Lp ℂ 2 μ) : α → ℂ) := by
          funext y
          show (g : α → ℂ) (T (T' y)) = (g : α → ℂ) y
          rw [hright y]
  right_inv g := by
    refine Lp.ext_iff.mpr ?_
    calc ((koopmanL2 T hT (koopmanL2 T' hT' g) : Lp ℂ 2 μ) : α → ℂ)
        =ᵐ[μ] ((koopmanL2 T' hT' g : Lp ℂ 2 μ) : α → ℂ) ∘ T :=
          coeFn_koopmanL2 T hT _
      _ =ᵐ[μ] ((g : Lp ℂ 2 μ) : α → ℂ) ∘ T' ∘ T :=
          hT.quasiMeasurePreserving.ae_eq_comp (coeFn_koopmanL2 T' hT' g)
      _ = ((g : Lp ℂ 2 μ) : α → ℂ) := by
          funext y
          show (g : α → ℂ) (T' (T y)) = (g : α → ℂ) y
          rw [hleft y]
  norm_map' g := (koopmanL2 T hT).norm_map g

/-- ★★ **The group law**: a measure-preserving flow gives a one-parameter group of Koopman
unitaries, `U_{s+t} = U_t ∘ U_s` (composition of observables with the flow reverses the order). -/
theorem koopmanL2_flow {φ : ℝ → α → α} (hφ : ∀ t, MeasurePreserving (φ t) μ μ)
    (hadd : ∀ s t y, φ (s + t) y = φ s (φ t y)) (s t : ℝ) (g : Lp ℂ 2 μ) :
    koopmanL2 (φ (s + t)) (hφ (s + t)) g = koopmanL2 (φ t) (hφ t) (koopmanL2 (φ s) (hφ s) g) := by
  refine Lp.ext_iff.mpr ?_
  calc ((koopmanL2 (φ (s + t)) (hφ (s + t)) g : Lp ℂ 2 μ) : α → ℂ)
      =ᵐ[μ] ((g : Lp ℂ 2 μ) : α → ℂ) ∘ φ (s + t) := coeFn_koopmanL2 _ _ g
    _ = (((g : Lp ℂ 2 μ) : α → ℂ) ∘ φ s) ∘ φ t := by
        funext y
        show (g : α → ℂ) (φ (s + t) y) = (g : α → ℂ) (φ s (φ t y))
        rw [hadd s t y]
    _ =ᵐ[μ] ((koopmanL2 (φ s) (hφ s) g : Lp ℂ 2 μ) : α → ℂ) ∘ φ t :=
        ((hφ t).quasiMeasurePreserving.ae_eq_comp (coeFn_koopmanL2 (φ s) (hφ s) g)).symm
    _ =ᵐ[μ] ((koopmanL2 (φ t) (hφ t) (koopmanL2 (φ s) (hφ s) g) : Lp ℂ 2 μ) : α → ℂ) :=
        (coeFn_koopmanL2 (φ t) (hφ t) _).symm

/-! ### Observables, and the generator -/

/-- The Koopman map on observables: `f ↦ f ∘ T`, for observables valued anywhere. -/
def koopmanFun {F : Type*} (T : α → α) (f : α → F) : α → F := f ∘ T

omit [MeasurableSpace α] in
/-- The Koopman map is an algebra homomorphism for the pointwise product — the classical observable
algebra is commutative and the evolution respects it. -/
theorem koopmanFun_mul {F : Type*} [Mul F] (T : α → α) (f g : α → F) :
    koopmanFun T (f * g) = koopmanFun T f * koopmanFun T g := rfl

/-- ★ **The Koopman generator on differentiable observables** (the Liouvillian): along a flow line,
`d/dt (f ∘ φ_t)(x) = Df(φ_t x)[X(φ_t x)]`, where `X` is the flow's velocity field. For a Hamiltonian
field that derivative is the Poisson bracket `{f, H}`. -/
theorem hasDerivAt_koopmanFun {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : ℝ → E → E} {f : E → F} {x v : E} {t : ℝ}
    (hφ : HasDerivAt (fun s => φ s x) v t) (hf : DifferentiableAt ℝ f (φ t x)) :
    HasDerivAt (fun s => koopmanFun (φ s) f x) (fderiv ℝ f (φ t x) v) t :=
  HasFDerivAt.comp_hasDerivAt t hf.hasFDerivAt hφ

end Koopman

end

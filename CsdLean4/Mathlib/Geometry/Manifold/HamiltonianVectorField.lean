/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.SymplecticForm
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Hamiltonian vector fields on a manifold

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold`, where at
the pin the words "Hamiltonian", "moment map" and "Poisson" do not occur).

Brick **G1** of `specs/generator-layer-scoping.md`: the defining equation of a Hamiltonian vector
field, `ι_X ω = dH`, at manifold level, together with the pointwise facts that follow from it by
alternation and linearity alone.

* `DifferentialForm.interiorProduct ω X` — the interior product `ι_X ω`, `x ↦ (ω x).curryLeft (X x)`,
  a 1-form *family* (`interiorProduct_apply`);
* `DifferentialForm.IsHamiltonianVectorField ω X H` — **`ω x (X x, v) = dH_x v` at every point**,
  with `dH_x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H x`; a Prop demanding the equation, nothing else;
* `DifferentialForm.IsLocallyHamiltonian ω X` — `d (ι_X ω) = 0`, the closedness of the 1-form
  family (the notion the flux correction of `RecordLayer/PiecewiseHamiltonian.lean` needs);
* for `h : IsHamiltonianVectorField ω X H`: `h.interiorProduct_eq` (`ι_X ω = dH` as families),
  ★ `h.mfderiv_apply_self` (**`dH (X) = 0`**: the energy is infinitesimally conserved along its own
  field, by alternation), `h.eq_of_nondegenerate` and ★ `h.unique_of_isSymplectic` (**the
  Hamiltonian vector field of `H` is unique** where `ω` is non-degenerate, in particular for a
  symplectic form), `h.add`, `h.smul` (linearity in `H`), `IsHamiltonianVectorField.const`
  (the zero field is Hamiltonian for a constant), and `h.mfderiv_eq` (two Hamiltonians of one field
  have the same derivative — the input to uniqueness up to a constant, brick G8).

## Honest scope

⚠️ **Predicates on families, not on smooth sections.** `X` is any `Π x, TangentSpace 𝓘 x` and
`ω` any family; nothing here asserts or needs smoothness. `IsLocallyHamiltonian` applies `mextDeriv`
to the family `ι_X ω`, which is meaningful when that family is smooth (brick G3) and junk otherwise
— exactly as `fderiv` of a non-differentiable function is junk.

⚠️ **No existence.** That a non-degenerate `ω` and an `H` *produce* a Hamiltonian field is brick
G2 (pointwise, finite-dimensional linear algebra) and G3 (its smoothness); only uniqueness is here.

⚠️ **Not yet: "Hamiltonian implies locally Hamiltonian".** `d(dH) = 0` needs `dH` as the exterior
derivative of the 0-form `H` — the flat half exists upstream (`extDeriv_constOfIsEmpty`), the
manifold half (`mextDeriv` of a 0-form family is `mfderiv`) is the first item of G3.

⚠️ **No inhabitant on `ℂℙⁿ` here.** The moment-map equation for the torus action is brick G6.

References: `specs/generator-layer-scoping.md` (G1); `Geometry/Manifold/SymplecticForm.lean`
(`IsSymplectic`); `Geometry/Manifold/ExteriorDerivative.lean` (`mextDeriv`);
`Analysis/InnerProductSpace/HamiltonianVectorField.lean` (the linear duality this lifts);
`RecordLayer/CellLawForced.lean` (`IsPhaseHamiltonian`, the linear moment-map equation);
`Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`; `specs/TERMS.md` (Hamiltonian);
`specs/future-work.md`.
-/

@[expose] public section

open Bundle Filter Topology Set
open scoped Manifold Bundle Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

namespace DifferentialForm

/-! ### The interior product -/

/-- The interior product `ι_X α` of a 2-form family with a vector field: `(ι_X α) x v = α x (X x, v)`,
a 1-form family. Smoothness is not part of the definition. -/
def interiorProduct
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin 2]→L[ℝ] Bundle.Trivial M ℝ x)
    (X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x) :
    ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin 1]→L[ℝ] Bundle.Trivial M ℝ x :=
  fun x => (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) (X x) : E [⋀^Fin 1]→L[ℝ] ℝ)

theorem interiorProduct_apply
    (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin 2]→L[ℝ] Bundle.Trivial M ℝ x)
    (X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x) (x : M)
    (v : Fin 1 → TangentSpace (modelWithCornersSelf ℝ E) x) :
    interiorProduct α X x v = α x (Matrix.vecCons (X x) v) :=
  ContinuousAlternatingMap.curryLeft_apply_apply (E := E) (F := ℝ) (α x) (X x) v

/-! ### Linearity of a 2-form family in its first slot, through `curryLeft` -/

variable (α : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin 2]→L[ℝ] Bundle.Trivial M ℝ x)

/-- `curryLeft` evaluated on a single vector is the 2-form on the pair. -/
theorem curryLeft_apply_vecCons (x : M) (u v : TangentSpace (modelWithCornersSelf ℝ E) x) :
    (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) u) ![v] = α x ![u, v] :=
  ContinuousAlternatingMap.curryLeft_apply_apply (E := E) (F := ℝ) (α x) u ![v]

theorem apply_sub_left (x : M) (a b v : TangentSpace (modelWithCornersSelf ℝ E) x) :
    α x ![a - b, v] = α x ![a, v] - α x ![b, v] :=
  calc α x ![a - b, v]
      = (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) (a - b)) ![v] :=
        (curryLeft_apply_vecCons α x (a - b) v).symm
    _ = (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) a
          - ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) b) ![v] :=
        congrArg (fun L : E [⋀^Fin 1]→L[ℝ] ℝ => L ![v])
          ((ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x)).map_sub a b)
    _ = (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) a) ![v]
          - (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) b) ![v] :=
        ContinuousAlternatingMap.sub_apply _ _ _
    _ = α x ![a, v] - α x ![b, v] :=
        congrArg₂ (· - ·) (curryLeft_apply_vecCons α x a v) (curryLeft_apply_vecCons α x b v)

theorem apply_add_left (x : M) (a b v : TangentSpace (modelWithCornersSelf ℝ E) x) :
    α x ![a + b, v] = α x ![a, v] + α x ![b, v] :=
  calc α x ![a + b, v]
      = (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) (a + b)) ![v] :=
        (curryLeft_apply_vecCons α x (a + b) v).symm
    _ = (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) a
          + ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) b) ![v] :=
        congrArg (fun L : E [⋀^Fin 1]→L[ℝ] ℝ => L ![v])
          ((ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x)).map_add a b)
    _ = (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) a) ![v]
          + (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) b) ![v] :=
        ContinuousAlternatingMap.add_apply _ _ _
    _ = α x ![a, v] + α x ![b, v] :=
        congrArg₂ (· + ·) (curryLeft_apply_vecCons α x a v) (curryLeft_apply_vecCons α x b v)

theorem apply_smul_left (x : M) (c : ℝ) (a v : TangentSpace (modelWithCornersSelf ℝ E) x) :
    α x ![c • a, v] = c • α x ![a, v] :=
  calc α x ![c • a, v]
      = (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) (c • a)) ![v] :=
        (curryLeft_apply_vecCons α x (c • a) v).symm
    _ = (c • ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) a) ![v] :=
        congrArg (fun L : E [⋀^Fin 1]→L[ℝ] ℝ => L ![v])
          ((ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x)).map_smul c a)
    _ = c • (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) a) ![v] :=
        ContinuousAlternatingMap.smul_apply _ _ _
    _ = c • α x ![a, v] := congrArg (c • ·) (curryLeft_apply_vecCons α x a v)

theorem apply_zero_left (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x) :
    α x ![0, v] = 0 :=
  calc α x ![0, v]
      = (ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x) 0) ![v] :=
        (curryLeft_apply_vecCons α x 0 v).symm
    _ = (0 : E [⋀^Fin 1]→L[ℝ] ℝ) ![v] :=
        congrArg (fun L : E [⋀^Fin 1]→L[ℝ] ℝ => L ![v])
          ((ContinuousAlternatingMap.curryLeft (E := E) (F := ℝ) (α x)).map_zero)
    _ = 0 := rfl

/-! ### The defining equation -/

/-- **`X` is the Hamiltonian vector field of `H` for `α`**: `α x (X x, v) = dH_x v` at every point
and for every tangent vector `v`, with `dH_x = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) H x`. A Prop demanding the
equation; nothing about smoothness or existence is asserted by the name. -/
def IsHamiltonianVectorField
    (X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x) (H : M → ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x),
    (α x ![X x, v] : ℝ) = mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x v

namespace IsHamiltonianVectorField

variable {α} {X Y : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x} {H K : M → ℝ}

/-- `ι_X α = dH` as 1-form families. -/
theorem interiorProduct_eq (h : IsHamiltonianVectorField α X H) (x : M)
    (v : Fin 1 → TangentSpace (modelWithCornersSelf ℝ E) x) :
    (interiorProduct α X x v : ℝ)
      = mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x (v 0) := by
  rw [interiorProduct_apply, ← h x (v 0)]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- ★ **Infinitesimal energy conservation**: `dH (X) = α (X, X) = 0`. -/
theorem mfderiv_apply_self (h : IsHamiltonianVectorField α X H) (x : M) :
    mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x (X x) = 0 := by
  rw [← h x (X x)]
  exact (α x).map_eq_zero_of_eq ![X x, X x] (i := 0) (j := 1) rfl (by decide)

/-- **Uniqueness at a point where `α` is non-degenerate**: two Hamiltonian vector fields of the
same `H` agree there. -/
theorem eq_of_nondegenerate (h : IsHamiltonianVectorField α X H)
    (h' : IsHamiltonianVectorField α Y H) (x : M)
    (hnd : ∀ v : TangentSpace (modelWithCornersSelf ℝ E) x, v ≠ 0 → ∃ w, α x ![v, w] ≠ 0) :
    X x = Y x := by
  by_contra hne
  obtain ⟨w, hw⟩ := hnd (X x - Y x) (sub_ne_zero.2 hne)
  apply hw
  rw [apply_sub_left]
  rw [h x w, h' x w]
  exact sub_self _

/-- Linearity in `H`: the sum of the fields is Hamiltonian for the sum of the energies. -/
theorem add (hX : IsHamiltonianVectorField α X H) (hY : IsHamiltonianVectorField α Y K)
    (hH : ∀ x, MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x)
    (hK : ∀ x, MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) K x) :
    IsHamiltonianVectorField α (fun x => X x + Y x) (H + K) := by
  intro x v
  rw [mfderiv_add (hH x) (hK x), apply_add_left]
  exact congrArg₂ (· + ·) (hX x v) (hY x v)

/-- Linearity in `H`: scaling. -/
theorem smul (hX : IsHamiltonianVectorField α X H) (c : ℝ)
    (hH : ∀ x, MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x) :
    IsHamiltonianVectorField α (fun x => c • X x) (c • H) := by
  intro x v
  rw [const_smul_mfderiv (hH x) c, apply_smul_left]
  exact congrArg (c • ·) (hX x v)

/-- The zero field is Hamiltonian for a constant energy. -/
theorem const (c : ℝ) : IsHamiltonianVectorField α (fun _ => 0) (fun _ => c) := by
  intro x v
  rw [mfderiv_const, apply_zero_left]
  rfl

/-- Two Hamiltonians of the same field for the same form have the same derivative everywhere. -/
theorem mfderiv_eq (h : IsHamiltonianVectorField α X H) (h' : IsHamiltonianVectorField α X K)
    (x : M) :
    mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x
      = mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) K x :=
  ContinuousLinearMap.ext fun v => (h x v).symm.trans (h' x v)

end IsHamiltonianVectorField

/-! ### Locally Hamiltonian fields, and uniqueness for a symplectic form -/

variable [IsManifold (modelWithCornersSelf ℝ E) ∞ M]

/-- **`X` is locally Hamiltonian for `α`**: the 1-form family `ι_X α` is closed. Meaningful when
the family is smooth (brick G3); the distinction from `IsHamiltonianVectorField` is exactly the
flux obstruction of `RecordLayer/PiecewiseHamiltonian.lean`. -/
def IsLocallyHamiltonian (X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x) : Prop :=
  ∀ x : M, _root_.mextDeriv (interiorProduct α X) x = 0

/-- ★ **The Hamiltonian vector field of `H` for a symplectic form is unique.** -/
theorem IsHamiltonianVectorField.unique_of_isSymplectic
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    {X Y : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x} {H : M → ℝ}
    (h : IsHamiltonianVectorField (fun x => β x) X H)
    (h' : IsHamiltonianVectorField (fun x => β x) Y H) : X = Y :=
  funext fun x => h.eq_of_nondegenerate h' x (hβ.nondegenerate x)

end DifferentialForm

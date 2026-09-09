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

Bricks **G1**, **G2**, **G8** (in part) and **G11** of `specs/generator-layer-scoping.md`: the
defining equation of a Hamiltonian vector field, `ι_X ω = dH`, at manifold level, the pointwise facts
that follow from it by alternation and linearity alone, its existence and uniqueness from
non-degeneracy, and the passage to the closed 1-form `d(ι_X ω) = 0`.

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
  have the same derivative — the input to uniqueness up to a constant, brick G8);
* `h.interiorProduct_eq_mextDeriv_zeroFormFamily` (`ι_X ω = dH` with `dH` the exterior derivative
  of the `0`-form `H`, `ExteriorDerivative.lean`) and ★ `h.isLocallyHamiltonian` — **Hamiltonian
  implies locally Hamiltonian** (G11): `d(ι_X ω) = d(dH) = 0` for a `C^∞` energy, by `d ∘ d = 0`;
* **G2, existence.** `flatAt α x : E →ₗ[ℝ] Module.Dual ℝ E` (the flat map `v ↦ α x (v, ·)`),
  `flatAt_injective` (non-degeneracy at `x` is its injectivity), `flatEquiv` (hence bijective, `E`
  finite-dimensional: `Subspace.dual_finrank_eq`), `hamiltonianVectorAt α x hnd L` (the unique `v`
  with `α x (v, ·) = L`, ★ `apply_hamiltonianVectorAt`, `eq_hamiltonianVectorAt`), and ★★
  `hamiltonianVectorField α hnd H = fun x => (ω♭ₓ)⁻¹ (dH_x)` with ★★
  `hamiltonianVectorField_isHamiltonianVectorField` (**existence**) and
  `h.eq_hamiltonianVectorField` (**uniqueness**: every Hamiltonian vector field of `H` is it);
  `IsSymplectic.hamiltonianVectorField` and its two theorems specialise to a symplectic form.

## Honest scope

⚠️ **Predicates on families, not on smooth sections.** `X` is any `Π x, TangentSpace 𝓘 x` and
`ω` any family; nothing here asserts or needs smoothness. `IsLocallyHamiltonian` applies `mextDeriv`
to the family `ι_X ω`, which is meaningful when that family is smooth (brick G3) and junk otherwise
— exactly as `fderiv` of a non-differentiable function is junk.

⚠️ **Existence is pointwise.** `hamiltonianVectorField` is a family `Π x, TangentSpace 𝓘 x` built
by finite-dimensional linear algebra at each point; that it is a *smooth section* when `α` and `H`
are smooth is brick G3, not here.

⚠️ **The converse of G11 is false and not stated.** A locally Hamiltonian field need not be
Hamiltonian: `ι_X ω` closed but not exact is exactly the flux obstruction of
`RecordLayer/PiecewiseHamiltonian.lean`, and `H¹` decides it. Nothing here touches that.

⚠️ **No inhabitant on `ℂℙⁿ` here.** The moment-map equation for the torus action is brick G6.

References: `specs/generator-layer-scoping.md` (G1, G2, G8, G11); `Geometry/Manifold/SymplecticForm.lean`
(`IsSymplectic`); `Geometry/Manifold/ExteriorDerivative.lean` (`mextDeriv`, `zeroFormFamily`,
`toFlat_mextDeriv_zeroFormFamily`, `mextDeriv_mextDeriv`);
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

/-! ### Existence: the Hamiltonian vector field of `H` from non-degeneracy (G2) -/

/-- `![v, w]` updated in its second slot. -/
theorem update_vecCons_one {β : Type*} (v w z : β) :
    Function.update ![v, w] 1 z = ![v, z] := by
  funext i
  fin_cases i <;> simp

theorem apply_add_right (x : M) (v a b : TangentSpace (modelWithCornersSelf ℝ E) x) :
    α x ![v, a + b] = α x ![v, a] + α x ![v, b] := by
  have h := (α x).map_update_add ![v, a] 1 a b
  simpa only [update_vecCons_one] using h

theorem apply_smul_right (x : M) (c : ℝ) (v a : TangentSpace (modelWithCornersSelf ℝ E) x) :
    α x ![v, c • a] = c • α x ![v, a] := by
  have h := (α x).map_update_smul ![v, a] 1 c a
  simpa only [update_vecCons_one] using h

/-- The flat map of a 2-form family at `x`, `v ↦ α x (v, ·)`, as a linear map into the dual of
the model space. -/
def flatAt (x : M) : E →ₗ[ℝ] Module.Dual ℝ E :=
  LinearMap.mk₂ ℝ (fun v w => (α x ![v, w] : ℝ))
    (fun a b w => apply_add_left α x a b w)
    (fun c a w => apply_smul_left α x c a w)
    (fun v a b => apply_add_right α x v a b)
    (fun c v a => apply_smul_right α x c v a)

theorem flatAt_apply (x : M) (v w : TangentSpace (modelWithCornersSelf ℝ E) x) :
    flatAt α x v w = α x ![v, w] := rfl

/-- Non-degeneracy at `x` is injectivity of the flat map. -/
theorem flatAt_injective (x : M)
    (hnd : ∀ v : TangentSpace (modelWithCornersSelf ℝ E) x, v ≠ 0 → ∃ w, α x ![v, w] ≠ 0) :
    Function.Injective (flatAt α x) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  by_contra hne
  obtain ⟨w, hw⟩ := hnd v hne
  exact hw (LinearMap.congr_fun hv w)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The flat map as a linear equivalence, where `α` is non-degenerate at `x`: injective
(`flatAt_injective`), hence bijective since `E` and its dual have the same finite dimension
(`Subspace.dual_finrank_eq`, `LinearMap.linearEquivOfInjective`). -/
def flatEquiv (x : M)
    (hnd : ∀ v : TangentSpace (modelWithCornersSelf ℝ E) x, v ≠ 0 → ∃ w, α x ![v, w] ≠ 0) :
    E ≃ₗ[ℝ] Module.Dual ℝ E :=
  LinearMap.linearEquivOfInjective (flatAt α x) (flatAt_injective α x hnd)
    Subspace.dual_finrank_eq.symm

theorem flatEquiv_apply (x : M)
    (hnd : ∀ v : TangentSpace (modelWithCornersSelf ℝ E) x, v ≠ 0 → ∃ w, α x ![v, w] ≠ 0)
    (v : E) : flatEquiv α x hnd v = flatAt α x v :=
  LinearMap.linearEquivOfInjective_apply _ _ _

/-- **The Hamiltonian vector of a covector**: the unique tangent vector `v` at `x` with
`α x (v, ·) = L`, where `α` is non-degenerate at `x`. -/
def hamiltonianVectorAt (x : M)
    (hnd : ∀ v : TangentSpace (modelWithCornersSelf ℝ E) x, v ≠ 0 → ∃ w, α x ![v, w] ≠ 0)
    (L : E →L[ℝ] ℝ) : TangentSpace (modelWithCornersSelf ℝ E) x :=
  (flatEquiv α x hnd).symm (L : E →ₗ[ℝ] ℝ)

/-- ★ The defining property: `α x (X_L, w) = L w`. -/
theorem apply_hamiltonianVectorAt (x : M)
    (hnd : ∀ v : TangentSpace (modelWithCornersSelf ℝ E) x, v ≠ 0 → ∃ w, α x ![v, w] ≠ 0)
    (L : E →L[ℝ] ℝ) (w : TangentSpace (modelWithCornersSelf ℝ E) x) :
    (α x ![hamiltonianVectorAt α x hnd L, w] : ℝ) = L w := by
  have h := LinearMap.congr_fun ((flatEquiv α x hnd).apply_symm_apply (L : E →ₗ[ℝ] ℝ)) w
  rw [flatEquiv_apply] at h
  exact h

/-- Uniqueness: any tangent vector with `α x (v, ·) = L` is the Hamiltonian vector of `L`. -/
theorem eq_hamiltonianVectorAt (x : M)
    (hnd : ∀ v : TangentSpace (modelWithCornersSelf ℝ E) x, v ≠ 0 → ∃ w, α x ![v, w] ≠ 0)
    (L : E →L[ℝ] ℝ) {v : TangentSpace (modelWithCornersSelf ℝ E) x}
    (hv : ∀ w, (α x ![v, w] : ℝ) = L w) : v = hamiltonianVectorAt α x hnd L := by
  apply (flatEquiv α x hnd).injective
  rw [hamiltonianVectorAt, LinearEquiv.apply_symm_apply]
  exact (flatEquiv_apply α x hnd v).trans (LinearMap.ext fun w => hv w)

/-- ★★ **The Hamiltonian vector field of `H`**, for a 2-form family non-degenerate at every point:
`x ↦ (ω♭ₓ)⁻¹ (dH_x)`. -/
def hamiltonianVectorField
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (H : M → ℝ) (x : M) : TangentSpace (modelWithCornersSelf ℝ E) x :=
  hamiltonianVectorAt α x (hnd x)
    (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x)

/-- ★★ **Existence**: the constructed field is a Hamiltonian vector field of `H`. -/
theorem hamiltonianVectorField_isHamiltonianVectorField
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (H : M → ℝ) : IsHamiltonianVectorField α (hamiltonianVectorField α hnd H) H :=
  fun x v => apply_hamiltonianVectorAt α x (hnd x) _ v

variable {α} in
/-- **Uniqueness**: every Hamiltonian vector field of `H` is the constructed one. -/
theorem IsHamiltonianVectorField.eq_hamiltonianVectorField
    {X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x} {H : M → ℝ}
    (h : IsHamiltonianVectorField α X H)
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0) :
    X = hamiltonianVectorField α hnd H :=
  funext fun x => eq_hamiltonianVectorAt α x (hnd x) _ (h x)

end FiniteDimensional


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

/-! ### Hamiltonian implies locally Hamiltonian (G11) -/

namespace IsHamiltonianVectorField

variable {α} {X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x} {H : M → ℝ}

/-- `ι_X α = dH` as `1`-form families, with `dH` the exterior derivative of the `0`-form `H`. -/
theorem interiorProduct_eq_mextDeriv_zeroFormFamily (h : IsHamiltonianVectorField α X H)
    (hH : ∀ x, MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x) :
    interiorProduct α X = _root_.mextDeriv (zeroFormFamily (E := E) H) := by
  funext x
  refine ContinuousAlternatingMap.ext fun v => ?_
  have h1 : (interiorProduct α X x v : ℝ)
      = mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x (v 0) :=
    h.interiorProduct_eq x v
  have h2 : toFlat (_root_.mextDeriv (zeroFormFamily (E := E) H) x) v
      = mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H x (v 0) := by
    rw [toFlat_mextDeriv_zeroFormFamily (E := E) (hH x)]
    exact ContinuousAlternatingMap.ofSubsingleton_apply_apply ℝ E ℝ (0 : Fin 1) _ v
  exact h1.trans h2.symm

/-- ★ **Hamiltonian implies locally Hamiltonian**: `d(ι_X α) = d(dH) = 0` for a `C^∞` energy. -/
theorem isLocallyHamiltonian (h : IsHamiltonianVectorField α X H)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) :
    IsLocallyHamiltonian α X := by
  intro x
  rw [h.interiorProduct_eq_mextDeriv_zeroFormFamily fun x => (hH x).mdifferentiableAt (by simp)]
  exact _root_.mextDeriv_mextDeriv _ (contMDiff_zeroFormFamily hH) x

end IsHamiltonianVectorField

/-! ### The Hamiltonian vector field of a symplectic form (G2) -/

section Symplectic

variable [FiniteDimensional ℝ E]

/-- The Hamiltonian vector field of `H` for a symplectic form. -/
def IsSymplectic.hamiltonianVectorField
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    (H : M → ℝ) : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x :=
  DifferentialForm.hamiltonianVectorField (fun x => β x) hβ.nondegenerate H

/-- ★★ For a symplectic form, `H` has a Hamiltonian vector field. -/
theorem IsSymplectic.hamiltonianVectorField_isHamiltonianVectorField
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    (H : M → ℝ) :
    IsHamiltonianVectorField (fun x => β x) (hβ.hamiltonianVectorField H) H :=
  DifferentialForm.hamiltonianVectorField_isHamiltonianVectorField (fun x => β x) hβ.nondegenerate H

/-- For a symplectic form, every Hamiltonian vector field of `H` is `hβ.hamiltonianVectorField H`. -/
theorem IsHamiltonianVectorField.eq_isSymplectic_hamiltonianVectorField
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    {X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x} {H : M → ℝ}
    (h : IsHamiltonianVectorField (fun x => β x) X H) : X = hβ.hamiltonianVectorField H :=
  h.eq_hamiltonianVectorField hβ.nondegenerate

end Symplectic


end DifferentialForm

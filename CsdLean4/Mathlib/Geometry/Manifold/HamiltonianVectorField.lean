/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.SymplecticForm
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hamiltonian vector fields on a manifold

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold`, where at
the pin the words "Hamiltonian", "moment map" and "Poisson" do not occur).

Bricks **G1**, **G2**, **G3**, **G4**, **G8** (in part) and **G11** of
`specs/generator-layer-scoping.md`: the defining equation of a Hamiltonian vector field,
`ι_X ω = dH`, at manifold level, the pointwise facts that follow from it by alternation and
linearity alone, its existence and uniqueness from non-degeneracy, its smoothness, its integral
curves, and the passage to the closed 1-form `d(ι_X ω) = 0`.

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
  `IsSymplectic.hamiltonianVectorField` and its two theorems specialise to a symplectic form;
* **G3, smoothness.** `flatVec` (G2's construction on the model), `flatCLE` / `coe_flatCLE` /
  `inverse_curryLeft_apply` (where `ξ` is non-degenerate `curryLeft ξ` is a continuous linear
  equivalence and the flat-level Hamiltonian vector is `ContinuousLinearMap.inverse` of it),
  `localHamiltonianVector` (the field read in a chart), `localRep_nondegenerate`, ★★
  `trivializationAt_hamiltonianVectorField_snd` (the tangent trivialisation of `X_H` is the local
  Hamiltonian vector — uniqueness at the flat level), ★★ `contDiffAt_localHamiltonianVector`
  (smooth, by `contDiffAt_map_inverse`), and ★★★ `contMDiff_hamiltonianVectorField` — **the
  Hamiltonian vector field of a `C^∞` energy for a `C^∞` non-degenerate 2-form is a `C^∞` section
  of the tangent bundle**; bundled as `hamiltonianVectorFieldSection`, and
  `IsSymplectic.contMDiff_hamiltonianVectorField`;
* **G4, integral curves.** ★ `h.hasDerivAt_comp_of_isMIntegralCurve` and ★★
  `h.comp_eq_of_isMIntegralCurve` — **energy conservation**: `H` is constant along every integral
  curve of a Hamiltonian vector field of `H`, by `dH (X) = 0` and the mean value theorem; ★★
  `exists_isMIntegralCurveAt_hamiltonianVectorField` (**local existence**, Picard–Lindelöf on the
  `C^1` section of G3) and ★★ `isMIntegralCurve_hamiltonianVectorField_eq` (**uniqueness** of
  global integral curves on a Hausdorff manifold); the three `IsSymplectic.` forms specialise.

## Honest scope

⚠️ **Predicates on families, not on smooth sections.** `X` is any `Π x, TangentSpace 𝓘 x` and
`ω` any family; the predicates neither assert nor need smoothness. Smoothness is a separate
theorem (G3) about the constructed field, under `C^∞` hypotheses on `ω` and `H`.

⚠️ **`IsLocallyHamiltonian` is stated on families.** It applies `mextDeriv` to `ι_X α`, which is
meaningful when that family is smooth — and for `hamiltonianVectorField` of a `C^∞` energy it now
is (G3) — and junk otherwise, exactly as `fderiv` of a non-differentiable function is junk.

⚠️ **No global flow.** G4 gives local existence, uniqueness and conservation for integral
curves; that a global flow `ℝ × M → M` exists (completeness of the field, e.g. on a compact
manifold) is not stated — Mathlib has no flows of vector fields on manifolds, which is why G5
(Liouville at manifold level) is unscheduled.

⚠️ **The converse of G11 is false and not stated.** A locally Hamiltonian field need not be
Hamiltonian: `ι_X ω` closed but not exact is exactly the flux obstruction of
`RecordLayer/PiecewiseHamiltonian.lean`, and `H¹` decides it. Nothing here touches that.

⚠️ **No inhabitant on `ℂℙⁿ` here.** The moment-map equation for the torus action is brick G6.

References: `specs/generator-layer-scoping.md` (G1, G2, G3, G4, G8, G11); `Geometry/Manifold/SymplecticForm.lean`
(`IsSymplectic`); `Geometry/Manifold/ExteriorDerivative.lean` (`mextDeriv`, `zeroFormFamily`,
`toFlat_mextDeriv_zeroFormFamily`, `mextDeriv_mextDeriv`);
`Analysis/InnerProductSpace/HamiltonianVectorField.lean` (the linear duality this lifts);
`RecordLayer/CellLawForced.lean` (`IsPhaseHamiltonian`, the linear moment-map equation);
`Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`;
`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean` (`exists_isMIntegralCurveAt_of_contMDiffAt`,
`isMIntegralCurve_eq_of_contMDiff`); `specs/TERMS.md` (Hamiltonian);
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

/-! ### Smoothness: the Hamiltonian vector field is a `C^∞` section (G3) -/

section Smooth

variable [FiniteDimensional ℝ E]

/-- A 2-form on the model, as a constant 2-form family on the manifold `E` — the shape G2's
constructions take, so that the model-level statements below are their instances. -/
def flatFamily (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (x : E) :
    TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin 2]→L[ℝ] Bundle.Trivial E ℝ x := ξ

omit [FiniteDimensional ℝ E] in
theorem flatFamily_nondegenerate (ξ : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hξ : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0) (x : E) :
    ∀ v : TangentSpace (modelWithCornersSelf ℝ E) x, v ≠ 0 → ∃ w, flatFamily ξ x ![v, w] ≠ 0 :=
  fun v hv => hξ v hv

/-- The Hamiltonian vector of a covector `L` for a non-degenerate 2-form `ξ` on the model: G2's
`hamiltonianVectorAt`, with model-typed data. -/
def flatVec (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (hξ : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0)
    (L : E →L[ℝ] ℝ) : E :=
  hamiltonianVectorAt (flatFamily ξ) 0 (flatFamily_nondegenerate ξ hξ 0) L

theorem apply_flatVec (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (hξ : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0)
    (L : E →L[ℝ] ℝ) (u : E) : ξ ![flatVec ξ hξ L, u] = L u :=
  apply_hamiltonianVectorAt (flatFamily ξ) 0 (flatFamily_nondegenerate ξ hξ 0) L u

theorem eq_flatVec (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (hξ : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0)
    (L : E →L[ℝ] ℝ) {v : E} (hv : ∀ u, ξ ![v, u] = L u) : v = flatVec ξ hξ L :=
  eq_hamiltonianVectorAt (flatFamily ξ) 0 (flatFamily_nondegenerate ξ hξ 0) L hv

/-- Where `ξ` is non-degenerate, `curryLeft ξ : E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)` is a continuous
linear equivalence: G2's `flatEquiv` on the model, followed by `ofSubsingletonLIE`, made continuous
by finite dimension (`LinearEquiv.toContinuousLinearEquiv`). -/
def flatCLE (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (hξ : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0) :
    E ≃L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ) :=
  (((flatEquiv (flatFamily ξ) 0 (flatFamily_nondegenerate ξ hξ 0)).trans
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ))).trans
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
        (0 : Fin 1)).toLinearEquiv).toContinuousLinearEquiv

theorem flatCLE_apply (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (hξ : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0)
    (v : E) (m : Fin 1 → E) : flatCLE ξ hξ v m = ξ ![v, m 0] :=
  rfl

theorem coe_flatCLE (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) (hξ : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0) :
    (flatCLE ξ hξ : E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)) = ContinuousAlternatingMap.curryLeft ξ := by
  ext v m
  rw [ContinuousLinearEquiv.coe_coe, flatCLE_apply, ContinuousAlternatingMap.curryLeft_apply_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The flat-level Hamiltonian vector is `ContinuousLinearMap.inverse` of `curryLeft ξ` — the
form in which its smoothness in `ξ` and `L` is visible. -/
theorem inverse_curryLeft_apply (ξ : E [⋀^Fin 2]→L[ℝ] ℝ)
    (hξ : ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0) (L : E →L[ℝ] ℝ) :
    ContinuousLinearMap.inverse (ContinuousAlternatingMap.curryLeft ξ)
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1) L)
      = flatVec ξ hξ L := by
  rw [← coe_flatCLE ξ hξ, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_eq]
  ext m
  rw [flatCLE_apply, apply_flatVec]
  rfl

variable (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ) (H : M → ℝ)

/-- The Hamiltonian vector field read in the chart at `x₀`: the flat-level Hamiltonian vector of
the local representative of `α` for the chart derivative of `H`. -/
def localHamiltonianVector (x₀ : M) (w : E) : E :=
  ContinuousLinearMap.inverse (ContinuousAlternatingMap.curryLeft (localRep (fun x => α x) x₀ w))
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
      (fderiv ℝ (H ∘ (chartAt E x₀).symm) w))

omit [FiniteDimensional ℝ E] in
/-- The local representative of a non-degenerate 2-form is non-degenerate on the chart target: the
tangent trivialisation carries non-degeneracy across (`trivializationAt_snd`,
`tangent_symmL_eq_fderiv`, `Trivialization.symmL_continuousLinearMapAt`). -/
theorem localRep_nondegenerate
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (x₀ : M) {w : E} (hw : w ∈ (chartAt E x₀).target) :
    ∀ v : E, v ≠ 0 → ∃ u, localRep (fun x => α x) x₀ w ![v, u] ≠ 0 := by
  intro v hv
  have hys : (chartAt E x₀).symm w ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hw
  have hwy : chartAt E x₀ ((chartAt E x₀).symm w) = w := (chartAt E x₀).right_inv hw
  have hloc : localRep (fun x => α x) x₀ w
      = (toFlat (α ((chartAt E x₀).symm w))).compContinuousLinearMap
          (fderiv ℝ (chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w) := by
    have h := trivializationAt_snd (fun x => α x) x₀ ((chartAt E x₀).symm w) hys
    rw [hwy] at h
    exact h
  have hDsymm : (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).symmL ℝ
      ((chartAt E x₀).symm w)
      = fderiv ℝ (chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w := by
    rw [tangent_symmL_eq_fderiv x₀ _ hys, hwy]
  have hyb : (chartAt E x₀).symm w
      ∈ (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).baseSet := hys
  have hDv : fderiv ℝ (chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w v ≠ 0 := by
    intro h0
    have h := Trivialization.continuousLinearMapAt_symmL (R := ℝ)
      (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀) hyb v
    rw [hDsymm] at h
    have h2 : (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).continuousLinearMapAt
        ℝ ((chartAt E x₀).symm w)
        (fderiv ℝ (chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w v) = 0 := by
      rw [h0]
      exact map_zero _
    exact hv (h.symm.trans h2)
  obtain ⟨u, hu⟩ := hnd _ _ hDv
  refine ⟨(trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).continuousLinearMapAt
    ℝ ((chartAt E x₀).symm w) u, ?_⟩
  have hDu : fderiv ℝ (chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w
      ((trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).continuousLinearMapAt
        ℝ ((chartAt E x₀).symm w) u) = u := by
    rw [← hDsymm]
    exact Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀) hyb u
  rw [hloc, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hcomp : (⇑(fderiv ℝ (chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w)
      ∘ ![v, (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).continuousLinearMapAt
        ℝ ((chartAt E x₀).symm w) u])
      = ![fderiv ℝ (chartAt E ((chartAt E x₀).symm w) ∘ (chartAt E x₀).symm) w v, u] := by
    funext i
    fin_cases i
    · rfl
    · exact hDu
  rw [hcomp]
  exact hu

/-- ★★ **The trivialised Hamiltonian vector field is the local Hamiltonian vector**: on the chart
source of `x₀`, the tangent trivialisation of `X_H y` is `localHamiltonianVector α H x₀` at the
chart coordinate of `y`. Proved by uniqueness at the flat level (`eq_flatVec`): the trivialised
vector satisfies the local equation, because the trivialisation intertwines `α` with its local
representative (`trivializationAt_snd`) and `dH` with the chart derivative (`mfderiv_comp`). -/
theorem trivializationAt_hamiltonianVectorField_snd
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H)
    (x₀ : M) {y : M} (hy : y ∈ (chartAt E x₀).source) :
    (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀
        ⟨y, hamiltonianVectorField (fun x => α x) hnd H y⟩).2
      = localHamiltonianVector α H x₀ (chartAt E x₀ y) := by
  have hwt : chartAt E x₀ y ∈ (chartAt E x₀).target := (chartAt E x₀).map_source hy
  have hyw : (chartAt E x₀).symm (chartAt E x₀ y) = y := (chartAt E x₀).left_inv hy
  have hω := localRep_nondegenerate α hnd x₀ hwt
  rw [localHamiltonianVector, inverse_curryLeft_apply _ hω]
  refine eq_flatVec _ hω _ fun u => ?_
  -- the local representative at `chartAt E x₀ y`, through the trivialisation
  have hloc : localRep (fun x => α x) x₀ (chartAt E x₀ y)
      = (toFlat (α y)).compContinuousLinearMap
          (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y)) := by
    have h := trivializationAt_snd (fun x => α x) x₀ y hy
    show (trivializationAt (E [⋀^Fin 2]→L[ℝ] ℝ)
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ E) x [⋀^Fin 2]→L[ℝ] Bundle.Trivial M ℝ x)
      x₀ ⟨(chartAt E x₀).symm (chartAt E x₀ y), α ((chartAt E x₀).symm (chartAt E x₀ y))⟩).2 = _
    rw [hyw]
    exact h
  have hyb : y ∈ (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).baseSet := hy
  have hDsymm : (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).symmL ℝ y
      = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) :=
    tangent_symmL_eq_fderiv x₀ y hy
  -- the trivialised vector, and its image under the transition derivative
  have hv : (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀
        ⟨y, hamiltonianVectorField (fun x => α x) hnd H y⟩).2
      = (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).continuousLinearMapAt ℝ y
          (hamiltonianVectorField (fun x => α x) hnd H y) :=
    (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀) hyb _).symm
  have hDv : fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y)
      ((trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀).continuousLinearMapAt ℝ y
        (hamiltonianVectorField (fun x => α x) hnd H y))
      = hamiltonianVectorField (fun x => α x) hnd H y := by
    rw [← hDsymm]
    exact Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀) hyb _
  -- the chart derivative of `H` is `dH_y` composed with the transition derivative
  have hsymm : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
      (chartAt E x₀).symm (chartAt E x₀ y) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas E x₀) hwt
  have hchain : fderiv ℝ (H ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u
      = mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H y
          (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u) := by
    have hHy : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H
        ((chartAt E x₀).symm (chartAt E x₀ y)) := (hH _).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp (chartAt E x₀ y) hHy hsymm
    have hsd : mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) (chartAt E x₀).symm
        (chartAt E x₀ y)
        = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) := by
      rw [hsymm.mfderiv]
      simp only [writtenInExtChartAt, Function.comp_def, extChartAt_model_space_eq_id,
        PartialEquiv.refl_symm, PartialEquiv.refl_coe, id, extChartAt_coe, modelWithCornersSelf_coe,
        Set.range_id, fderivWithin_univ, hyw]
      rfl
    have hpt : (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H
        ((chartAt E x₀).symm (chartAt E x₀ y)) : E →L[ℝ] ℝ)
        = mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H y := by
      rw [hyw]
    have e2 : (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) (chartAt E x₀).symm
        (chartAt E x₀ y) u : E)
        = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u :=
      congrArg (fun L : E →L[ℝ] E => L u) hsd
    rw [← mfderiv_eq_fderiv, hcomp]
    exact (congrArg (fun v : E => mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H
      ((chartAt E x₀).symm (chartAt E x₀ y)) v) e2).trans
      (congrArg (fun L : E →L[ℝ] ℝ =>
        L (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u)) hpt)
  rw [hloc, ContinuousAlternatingMap.compContinuousLinearMap_apply, hchain]
  have hcomp : (⇑(fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y))
      ∘ ![(trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) x₀
            ⟨y, hamiltonianVectorField (fun x => α x) hnd H y⟩).2, u])
      = ![hamiltonianVectorField (fun x => α x) hnd H y,
          fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u] := by
    funext i
    fin_cases i
    · show fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) _ = _
      rw [hv]
      exact hDv
    · rfl
  rw [hcomp]
  exact hamiltonianVectorField_isHamiltonianVectorField (fun x => α x) hnd H y _

/-- ★★ The local Hamiltonian vector is `C^∞` at the chart image of `x₀`: inversion of `curryLeft`
is smooth at an invertible point (`contDiffAt_map_inverse`), the local representative is smooth
(`contDiffAt_localRep`), and the chart derivative of a `C^∞` energy is `C^∞`. -/
theorem contDiffAt_localHamiltonianVector
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) (x₀ : M) :
    ContDiffAt ℝ ∞ (localHamiltonianVector α H x₀) (chartAt E x₀ x₀) := by
  have hw₀ : chartAt E x₀ x₀ ∈ (chartAt E x₀).target := mem_chart_target E x₀
  have hω := localRep_nondegenerate α hnd x₀ hw₀
  -- `curryLeft` is a bounded linear map (`curryLeft_add`, `curryLeft_smul`, `norm_curryLeft`);
  -- the boundedness witness is elaborated against the shape `IsBoundedLinearMap.contDiff` expects
  have hΦ : ContDiffAt ℝ ∞
      (fun w => ContinuousAlternatingMap.curryLeft (localRep (fun x => α x) x₀ w))
      (chartAt E x₀ x₀) :=
    (IsBoundedLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (f := fun ξ : E [⋀^Fin 2]→L[ℝ] ℝ => ContinuousAlternatingMap.curryLeft ξ)
      ⟨⟨fun ξ ξ' => ContinuousAlternatingMap.curryLeft_add ξ ξ',
        fun c ξ => ContinuousAlternatingMap.curryLeft_smul c ξ⟩,
        1, one_pos, fun ξ => le_of_eq
          ((ContinuousAlternatingMap.norm_curryLeft ξ).trans (one_mul _).symm)⟩).contDiffAt.comp _
      (contDiffAt_localRep (fun x => α x) α.contMDiff_toFun x₀ hw₀)
  have hinv : ContDiffAt ℝ ∞
      (fun w => ContinuousLinearMap.inverse
        (ContinuousAlternatingMap.curryLeft (localRep (fun x => α x) x₀ w)))
      (chartAt E x₀ x₀) := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞) (flatCLE _ hω)
    rw [coe_flatCLE] at h
    exact h.comp (chartAt E x₀ x₀) hΦ
  have hHloc : ContDiffAt ℝ ∞ (H ∘ (chartAt E x₀).symm) (chartAt E x₀ x₀) := by
    rw [← contMDiffAt_iff_contDiffAt]
    have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (chartAt E x₀).symm (chartAt E x₀ x₀) :=
      (contMDiffOn_chart_symm (n := ∞) (x := x₀)).contMDiffAt
        ((chartAt E x₀).open_target.mem_nhds hw₀)
    exact (hH _).comp _ h1
  have hL : ContDiffAt ℝ ∞
      (fun w => ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)
        (fderiv ℝ (H ∘ (chartAt E x₀).symm) w)) (chartAt E x₀ x₀) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
      (0 : Fin 1)).contDiff.contDiffAt.comp _ (hHloc.fderiv_right (by simp))
  exact hinv.clm_apply hL

/-- ★★★ **The Hamiltonian vector field is a `C^∞` section of the tangent bundle**, for a `C^∞`
2-form family non-degenerate at every point and a `C^∞` energy. -/
theorem contMDiff_hamiltonianVectorField
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) :
    ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E)) ∞
      (fun x : M => TotalSpace.mk' E x (hamiltonianVectorField (fun x => α x) hnd H x)) := by
  intro x₀
  rw [contMDiffAt_section]
  have h1 : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
      (fun y => localHamiltonianVector α H x₀ (chartAt E x₀ y)) x₀ :=
    (contDiffAt_localHamiltonianVector α H hnd hH x₀).contMDiffAt.comp x₀
      (contMDiffAt_extChartAt (n := ∞) (I := modelWithCornersSelf ℝ E) (x := x₀))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with y hy
  exact trivializationAt_hamiltonianVectorField_snd α H hnd hH x₀ hy

/-- The Hamiltonian vector field of `H`, as a `C^∞` vector field (a `C^∞` section of the tangent
bundle). -/
def hamiltonianVectorFieldSection
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) :
    ContMDiffSection (modelWithCornersSelf ℝ E) E ∞
      (TangentSpace (modelWithCornersSelf ℝ E) : M → Type _) :=
  ⟨hamiltonianVectorField (fun x => α x) hnd H, contMDiff_hamiltonianVectorField α H hnd hH⟩

/-- ★★★ For a symplectic form, the Hamiltonian vector field of a `C^∞` energy is a `C^∞` vector
field. -/
theorem IsSymplectic.contMDiff_hamiltonianVectorField
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    (H : M → ℝ) (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) :
    ContMDiff (modelWithCornersSelf ℝ E)
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E)) ∞
      (fun x : M => TotalSpace.mk' E x (hβ.hamiltonianVectorField H x)) :=
  DifferentialForm.contMDiff_hamiltonianVectorField β H hβ.nondegenerate hH

end Smooth

/-! ### Integral curves: existence, uniqueness, and energy conservation (G4) -/

section IntegralCurve

omit [IsManifold (modelWithCornersSelf ℝ E) ∞ M] in
variable {α} in
/-- ★ **Infinitesimal energy conservation along an integral curve**: if `X` is a Hamiltonian
vector field of `H` and `γ` is an integral curve of `X`, then `H ∘ γ` has zero derivative
(`mfderiv_apply_self`: `dH (X) = α (X, X) = 0`). -/
theorem IsHamiltonianVectorField.hasDerivAt_comp_of_isMIntegralCurve
    {X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x} {H : M → ℝ}
    (h : IsHamiltonianVectorField α X H) {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) {t : ℝ}
    (hH : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H (γ t)) :
    HasDerivAt (H ∘ γ) 0 t := by
  have h1 : HasMFDerivAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) (H ∘ γ) t
      ((mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) :=
    hH.hasMFDerivAt.comp t (hγ t)
  have h2 : HasFDerivAt (H ∘ γ)
      (((mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t))) : ℝ →L[ℝ] ℝ)) t :=
    hasMFDerivAt_iff_hasFDerivAt.mp h1
  show HasFDerivAt (H ∘ γ) ((1 : ℝ →L[ℝ] ℝ).smulRight (0 : ℝ)) t
  refine h2.congr_fderiv (ContinuousLinearMap.ext_ring ?_)
  simp [h.mfderiv_apply_self (γ t)]
  rfl

omit [IsManifold (modelWithCornersSelf ℝ E) ∞ M] in
variable {α} in
/-- ★★ **Energy conservation**: `H` is constant along every integral curve of a Hamiltonian
vector field of `H` (a differentiable energy). -/
theorem IsHamiltonianVectorField.comp_eq_of_isMIntegralCurve
    {X : ∀ x : M, TangentSpace (modelWithCornersSelf ℝ E) x} {H : M → ℝ}
    (h : IsHamiltonianVectorField α X H) {γ : ℝ → M} (hγ : IsMIntegralCurve γ X)
    (hH : MDifferentiable (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H) (t s : ℝ) :
    H (γ t) = H (γ s) :=
  is_const_of_deriv_eq_zero
    (fun u => (h.hasDerivAt_comp_of_isMIntegralCurve hγ (hH (γ u))).differentiableAt)
    (fun u => (h.hasDerivAt_comp_of_isMIntegralCurve hγ (hH (γ u))).deriv) t s

end IntegralCurve

section IntegralCurveSmooth

variable [FiniteDimensional ℝ E]
variable (α : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ) (H : M → ℝ)

/-- ★★ **Local existence**: through every point, at every time, passes an integral curve of the
Hamiltonian vector field of a `C^∞` energy (Picard–Lindelöf in the chart,
`exists_isMIntegralCurveAt_of_contMDiffAt`, on the `C^1` section G3 provides). -/
theorem exists_isMIntegralCurveAt_hamiltonianVectorField
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) (x₀ : M) (t₀ : ℝ) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧
      IsMIntegralCurveAt γ (hamiltonianVectorField (fun x => α x) hnd H) t₀ := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact exists_isMIntegralCurveAt_of_contMDiffAt (t₀ := t₀)
    ((contMDiff_hamiltonianVectorField α H hnd hH).of_le (m := 1)
      (mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)) x₀)
    BoundarylessManifold.isInteriorPoint

/-- ★★ **Uniqueness**: two global integral curves of the Hamiltonian vector field of a `C^∞`
energy that agree at one time agree everywhere (`isMIntegralCurve_eq_of_contMDiff`, on a Hausdorff
manifold). -/
theorem isMIntegralCurve_hamiltonianVectorField_eq [T2Space M]
    (hnd : ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ E) x), v ≠ 0 →
      ∃ w, α x ![v, w] ≠ 0)
    (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H) {γ γ' : ℝ → M}
    (hγ : IsMIntegralCurve γ (hamiltonianVectorField (fun x => α x) hnd H))
    (hγ' : IsMIntegralCurve γ' (hamiltonianVectorField (fun x => α x) hnd H)) {t₀ : ℝ}
    (h : γ t₀ = γ' t₀) : γ = γ' :=
  isMIntegralCurve_eq_of_contMDiff (fun _ => BoundarylessManifold.isInteriorPoint)
    ((contMDiff_hamiltonianVectorField α H hnd hH).of_le (m := 1)
      (mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))
    hγ hγ' h

/-- ★★ For a symplectic form: local existence of integral curves of the Hamiltonian vector field
of a `C^∞` energy. -/
theorem IsSymplectic.exists_isMIntegralCurveAt_hamiltonianVectorField
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    (H : M → ℝ) (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H)
    (x₀ : M) (t₀ : ℝ) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ (hβ.hamiltonianVectorField H) t₀ :=
  DifferentialForm.exists_isMIntegralCurveAt_hamiltonianVectorField β H hβ.nondegenerate hH x₀ t₀

/-- ★★ For a symplectic form: uniqueness of global integral curves of the Hamiltonian vector
field of a `C^∞` energy. -/
theorem IsSymplectic.isMIntegralCurve_hamiltonianVectorField_eq [T2Space M]
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    (H : M → ℝ) (hH : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ H)
    {γ γ' : ℝ → M} (hγ : IsMIntegralCurve γ (hβ.hamiltonianVectorField H))
    (hγ' : IsMIntegralCurve γ' (hβ.hamiltonianVectorField H)) {t₀ : ℝ} (h : γ t₀ = γ' t₀) :
    γ = γ' :=
  DifferentialForm.isMIntegralCurve_hamiltonianVectorField_eq β H hβ.nondegenerate hH hγ hγ' h

/-- ★★ For a symplectic form: the energy is conserved along every integral curve of its
Hamiltonian vector field. -/
theorem IsSymplectic.comp_eq_of_isMIntegralCurve_hamiltonianVectorField
    {β : DifferentialForm (modelWithCornersSelf ℝ E) M ∞ (Fin 2) ℝ} (hβ : β.IsSymplectic)
    (H : M → ℝ) (hH : MDifferentiable (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) H)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (hβ.hamiltonianVectorField H)) (t s : ℝ) :
    H (γ t) = H (γ s) :=
  (hβ.hamiltonianVectorField_isHamiltonianVectorField H).comp_eq_of_isMIntegralCurve hγ hH t s

end IntegralCurveSmooth


end DifferentialForm

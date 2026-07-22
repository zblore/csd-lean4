/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Mathlib upstream candidate: `Measure.pi` is preserved by currying a product index

`MeasurableEquiv.piCurry` regroups a product over a sigma index `Σ i, κ i` into an
iterated product (`(i : ι) → (j : κ i) → X i j`). Mathlib proves it measurable
(`measurable_piCurry`) but provides **no measure-preserving statement**: currying a
`Measure.pi` over `Σ i, κ i` yields the iterated `Measure.pi`-of-`Measure.pi`,

```
map (piCurry X) (Measure.pi μ) = Measure.pi (fun i => Measure.pi (fun j => μ ⟨i, j⟩)).
```

The proof is the sigma-index analogue of `measurePreserving_arrowProdEquivProdArrow`:
verify on the box-of-boxes π-system (`pi_eq_generateFrom`), where `piCurry⁻¹` of a box
of boxes is a genuine sigma-box, so `Measure.pi_pi` factors both sides and
`Finset.prod_sigma'` collapses the double product to the sigma product.

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib upstream candidate).

## Provenance

Needed for the general-N Duistermaat–Heckman / Dirichlet computation
(`CsdLean4/LF4/MomentRatioUniformN.lean` + the Slice E assembly): the standard
Gaussian on `ℝ^{N×2}` (indexed by the product `Fin N × Fin 2`) must be regrouped
into a product over `Fin N` of `ℝ²`-Gaussians before Slices C/D apply. See
`specs/general-n-dh-plan.md` Slice E.

## Tags

measure preserving, pi, curry, sigma, product measure
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]
  (μ : (p : (i : ι) × κ i) → Measure (X p.1 p.2)) [∀ p, SigmaFinite (μ p)]

/-- **Currying a product index preserves `Measure.pi`.** The measurable equivalence
`MeasurableEquiv.piCurry` (regrouping `Σ i, κ i` into an iterated index) pushes the
product measure forward to the iterated product measure. -/
theorem measurePreserving_piCurry :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi μ)
      (Measure.pi (fun i => Measure.pi (fun j => μ ⟨i, j⟩))) := by
  refine ⟨(MeasurableEquiv.piCurry X).measurable, ?_⟩
  refine (Measure.pi_eq_generateFrom
      (μ := fun i => Measure.pi (fun j => μ ⟨i, j⟩))
      (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
      (fun i => Measure.FiniteSpanningSetsIn.pi (fun j => (μ ⟨i, j⟩).toFiniteSpanningSetsIn))
      ?_).symm
  intro s hs
  -- Each `s i` is a box `pi univ (t i)` of measurable sets.
  have hbox : ∀ i, ∃ t : (j : κ i) → Set (X i j),
      (∀ j, MeasurableSet (t j)) ∧ Set.pi univ t = s i := by
    intro i
    obtain ⟨a, ha, hae⟩ := hs i
    exact ⟨a, fun j => ha j (mem_univ j), hae⟩
  choose t ht hts using hbox
  -- The `piCurry`-preimage of a box of boxes is a genuine sigma-box.
  have hpre : (MeasurableEquiv.piCurry X) ⁻¹' (Set.pi univ s)
      = Set.pi univ (fun p : (i : ι) × κ i => t p.1 p.2) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, mem_univ, forall_true_left,
      MeasurableEquiv.coe_piCurry]
    constructor
    · intro h p
      have h1 := h p.1
      rw [← hts p.1, Set.mem_pi] at h1
      exact h1 p.2 (mem_univ _)
    · intro h i
      rw [← hts i, Set.mem_pi]
      exact fun j _ => h ⟨i, j⟩
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  -- Right side: factor each `pi`-box, then collapse the double product.
  have hrhs : ∏ i, (Measure.pi (fun j => μ ⟨i, j⟩)) (s i)
      = ∏ i, ∏ j, μ ⟨i, j⟩ (t i j) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← hts i, Measure.pi_pi]
  rw [hrhs, Finset.prod_sigma' (s := (Finset.univ : Finset ι))
    (t := fun _ => (Finset.univ : Finset (κ _)))
    (f := fun i j => μ ⟨i, j⟩ (t i j)), Finset.univ_sigma_univ]

/-! ### Product-index variant

The concrete form consumed by the general-N Duistermaat–Heckman assembly: the
standard Gaussian on `ℝ^{N×2}` is indexed by the **product** `Fin N × Fin 2`, so the
regrouping needed there is currying a product index, not a sigma index. The proof is
identical to `measurePreserving_piCurry` with `Fintype.prod_prod_type` (product big
operator) in place of `Finset.prod_sigma'`. -/

variable {ιp κp : Type*} [Fintype ιp] [Fintype κp] {α : ιp × κp → Type*}
  [∀ p, MeasurableSpace (α p)] (ν : (p : ιp × κp) → Measure (α p)) [∀ p, SigmaFinite (ν p)]

/-- **Currying a product index preserves `Measure.pi`.** The plain currying map
`y ↦ fun i j => y (i, j)` pushes the product measure over `ιp × κp` forward to the
iterated product measure. -/
theorem map_curryProd_pi :
    Measure.map (fun y : (p : ιp × κp) → α p => fun i j => y (i, j)) (Measure.pi ν)
      = Measure.pi (fun i => Measure.pi (fun j => ν (i, j))) := by
  have hmeas : Measurable (fun y : (p : ιp × κp) → α p => fun i j => y (i, j)) := by
    apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j
    exact measurable_pi_apply (i, j)
  refine (Measure.pi_eq_generateFrom
      (μ := fun i => Measure.pi (fun j => ν (i, j)))
      (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
      (fun i => Measure.FiniteSpanningSetsIn.pi (fun j => (ν (i, j)).toFiniteSpanningSetsIn))
      ?_).symm
  intro s hs
  have hbox : ∀ i, ∃ t : (j : κp) → Set (α (i, j)),
      (∀ j, MeasurableSet (t j)) ∧ Set.pi univ t = s i := by
    intro i
    obtain ⟨a, ha, hae⟩ := hs i
    exact ⟨a, fun j => ha j (mem_univ j), hae⟩
  choose t ht hts using hbox
  have hsmeas : ∀ i, MeasurableSet (s i) := by
    intro i; rw [← hts i]; exact MeasurableSet.univ_pi (ht i)
  have hpre : (fun y : (p : ιp × κp) → α p => fun i j => y (i, j)) ⁻¹' (Set.pi univ s)
      = Set.pi univ (fun p : ιp × κp => t p.1 p.2) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, mem_univ, forall_true_left]
    constructor
    · intro h p
      have h1 := h p.1
      rw [← hts p.1, Set.mem_pi] at h1
      exact h1 p.2 (mem_univ _)
    · intro h i
      rw [← hts i, Set.mem_pi]
      exact fun j _ => h (i, j)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hsmeas), hpre, Measure.pi_pi]
  have hrhs : ∏ i, (Measure.pi (fun j => ν (i, j))) (s i)
      = ∏ i, ∏ j, ν (i, j) (t i j) := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← hts i, Measure.pi_pi]
  rw [hrhs, Fintype.prod_prod_type (f := fun p : ιp × κp => ν p (t p.1 p.2))]

end MeasureTheory

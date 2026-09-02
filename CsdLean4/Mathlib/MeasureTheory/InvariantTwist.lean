/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Invariant twists of an invariant measure are measure-preserving

**Category:** 1-Mathlib (CSD-free upstream candidate).

Let a group `G` with a left-invariant probability measure `λ` act measurably on `X`, let `μ`
be a measure on `X` preserved by every `act g`, and let `φ : X → G` be a measurable
**invariant** parameter: `φ (act g y) = φ y`. Then the *twist*

  `y ↦ act (φ y) y`

— "rotate each point by a group element that depends only on its orbit" — preserves `μ`.

This is the measure-theoretic content of "a fibrewise rotation by a fibre-constant angle
preserves a fibrewise-invariant measure" without ever disintegrating `μ` along the orbits.
The proof is four lines of Tonelli: insert `∫ dλ(g)` (a probability), use `μ`-invariance to
replace `y` by `act g y` inside, use the invariance of `φ` and the action law to turn the
integrand into `f (act (φ y * g) y)`, absorb `φ y` by the left-invariance of `λ`, swap the
integrals back and use `μ`-invariance once more.

Typical instance (the reason the lemma exists here): a torus acting on a Kähler manifold by
its Hamiltonian `T`-action, `μ` the Liouville measure, `φ` any measurable function of the
moment map. The time-`1` map of a Hamiltonian whose flow moves each point only along its
torus orbit — by an angle depending on the conserved quantities — is such a twist.

## Provenance

Staged as upstream Mathlib material; no `CsdLean4`-namespace content. Not found in Mathlib
(2026-09-01): `MeasurePreserving.skew_product` covers product spaces with a fibre map that
depends on the base point, which is the special case `X = B × F`, `act` trivial on `B`.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {G X : Type*} [MeasurableSpace G] [MeasurableSpace X]

/-- **Invariant twists preserve an invariant measure.** If every `act g` preserves `μ`, `λ`
is a left-invariant probability measure on `G`, and `φ : X → G` is measurable and constant
on orbits, then `y ↦ act (φ y) y` preserves `μ`. The action is only asked to be a
measurable map `G × X → X` satisfying the composition law `act a (act b y) = act (a * b) y`;
no `MulAction` instance is needed. -/
@[to_additive MeasurePreserving.vadd_twist_of_invariant
      /-- **Invariant twists preserve an invariant measure** (additive group). If every `act g`
      preserves `μ`, `λ` is a left-invariant probability measure on `G`, and `φ : X → G` is
      measurable and constant on orbits, then `y ↦ act (φ y) y` preserves `μ`. -/]
theorem MeasurePreserving.twist_of_invariant [Group G] [MeasurableMul₂ G]
    (haar : Measure G) [IsProbabilityMeasure haar] [haar.IsMulLeftInvariant]
    {μ : Measure X} [SFinite μ]
    {act : G → X → X} (hact : Measurable (Function.uncurry act))
    (hcomp : ∀ a b y, act a (act b y) = act (a * b) y)
    (hinv : ∀ g, MeasurePreserving (act g) μ μ)
    {φ : X → G} (hφ : Measurable φ) (hφinv : ∀ g y, φ (act g y) = φ y) :
    MeasurePreserving (fun y => act (φ y) y) μ μ := by
  have hT : Measurable fun y => act (φ y) y := hact.comp (hφ.prodMk measurable_id)
  refine ⟨hT, Measure.ext_of_lintegral _ fun f hf => ?_⟩
  rw [lintegral_map hf hT]
  -- Step 1: the integrand may be twisted by any further `g`, by `μ`-invariance and the
  -- invariance of `φ`.
  have h1 : ∀ g : G, ∫⁻ y, f (act (φ y) y) ∂μ = ∫⁻ y, f (act (φ y * g) y) ∂μ := by
    intro g
    calc ∫⁻ y, f (act (φ y) y) ∂μ
        = ∫⁻ y, f (act (φ (act g y)) (act g y)) ∂μ :=
          ((hinv g).lintegral_comp (hf.comp hT)).symm
      _ = ∫⁻ y, f (act (φ y * g) y) ∂μ := by
          congr 1; funext y; rw [hφinv, hcomp]
  -- Measurability of the two joint integrands for Tonelli.
  have hm1 : Measurable (Function.uncurry fun g y => f (act (φ y * g) y)) :=
    hf.comp (hact.comp (((hφ.comp measurable_snd).mul measurable_fst).prodMk measurable_snd))
  have hm2 : Measurable (Function.uncurry fun g y => f (act g y)) := hf.comp hact
  -- Step 2: average step 1 over `haar`, swap, absorb `φ y` by left-invariance, swap back.
  calc ∫⁻ y, f (act (φ y) y) ∂μ
      = ∫⁻ g, ∫⁻ y, f (act (φ y) y) ∂μ ∂haar := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ g, ∫⁻ y, f (act (φ y * g) y) ∂μ ∂haar := by
        congr 1; funext g; exact h1 g
    _ = ∫⁻ y, ∫⁻ g, f (act (φ y * g) y) ∂haar ∂μ :=
        lintegral_lintegral_swap hm1.aemeasurable
    _ = ∫⁻ y, ∫⁻ g, f (act g y) ∂haar ∂μ := by
        congr 1; funext y
        exact lintegral_mul_left_eq_self (fun g => f (act g y)) (φ y)
    _ = ∫⁻ g, ∫⁻ y, f (act g y) ∂μ ∂haar :=
        (lintegral_lintegral_swap hm2.aemeasurable).symm
    _ = ∫⁻ g, ∫⁻ y, f y ∂μ ∂haar := by
        congr 1; funext g; exact (hinv g).lintegral_comp hf
    _ = ∫⁻ y, f y ∂μ := by
        rw [lintegral_const, measure_univ, mul_one]

end MeasureTheory

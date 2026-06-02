import CsdLean4.LF4.MomentMarginalUniform
import CsdLean4.Mathlib.MeasureTheory.PiCurry

/-!
# LF4 general-N Slice E (bridge): `ℝ^{N×2}` Gaussian → `Exp(1/2)^{⊗N}`

The bridge connecting the standard Gaussian on `ℝ^{N×2}` (indexed by the product
`Fin N × Fin 2`, the real coordinate space behind `gaussianHN`) to the `N`-fold
product `Exp(1/2)^{⊗N}` that Slice D (`ratioSqNorm_map_expHalf_pi`) consumes.

The per-block squared-norm map `y ↦ (i ↦ y(i,0)² + y(i,1)²)` pushes
`gaussianReal^{⊗(N×2)}` to `expHalf^{⊗N}`. The proof regroups the product index
via `map_curryProd_pi` (the Cat-1 product-index curry, `PiCurry.lean`), then applies
the per-factor map lemma `Measure.pi_map_pi` with the single-block fact

```
(fun w : Fin 2 → ℝ => (w 0)² + (w 1)²)∗ gaussianReal^{⊗2} = expHalf   (E1).
```

This **bypasses Slice C** (`blockSqNorm_map_gaussianN_pi`, which routed through
`pi (Fin N) gaussian2`): currying lands directly on `pi (Fin N) (pi (Fin 2) gaussianReal)`,
so the single-block computation is the Fin-2 form of Slice 1, not the `gaussian2`
explicit-density form. See `specs/general-n-dh-plan.md` Slice E.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CSD
namespace LF4

/-- The single-block squared-norm map on `Fin 2 → ℝ`. -/
noncomputable def gBlock : (Fin 2 → ℝ) → ℝ := fun w => (w 0) ^ 2 + (w 1) ^ 2

lemma measurable_gBlock : Measurable gBlock := by unfold gBlock; fun_prop

/-- **E1.** The single-block squared norm pushes the 2-fold standard Gaussian to
`Exp(1/2)`: `(fun w => w₀² + w₁²)∗ gaussianReal^{⊗2} = expHalf`. The `Fin 2 → ℝ`
form of `sqNorm_map_gaussian2` (Slice 1), routed through
`measurePreserving_piFinTwo` and `gaussian2_eq_prod`. -/
theorem gBlock_map_pi :
    Measure.map gBlock (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = expHalf := by
  have hpiftwo : gBlock
      = (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ∘ (MeasurableEquiv.piFinTwo (fun _ => ℝ)) := by
    funext w
    simp only [gBlock, Function.comp_apply, MeasurableEquiv.piFinTwo_apply]
  rw [hpiftwo, ← Measure.map_map (by fun_prop) (MeasurableEquiv.piFinTwo (fun _ => ℝ)).measurable,
    (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).map_eq,
    ← gaussian2_eq_prod, sqNorm_map_gaussian2]

/-- **E2 (the bridge).** The per-block squared-norm map `y ↦ (i ↦ y(i,0)² + y(i,1)²)`
pushes the standard Gaussian on `ℝ^{N×2}` (`gaussianReal^{⊗(N×2)}`) to the `N`-fold
product `Exp(1/2)^{⊗N}`. -/
theorem blockSqNormCurry_map_pi {N : ℕ} :
    Measure.map (fun y : (Fin N × Fin 2) → ℝ => fun i => (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2)
      (Measure.pi (fun _ : Fin N × Fin 2 => gaussianReal 0 1))
      = Measure.pi (fun _ : Fin N => expHalf) := by
  have hcurry : Measurable (fun y : (Fin N × Fin 2) → ℝ => fun i j => y (i, j)) := by
    apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j
    exact measurable_pi_apply (i, j)
  have hblock : Measurable
      (fun w : Fin N → Fin 2 → ℝ => fun i => gBlock (w i)) := by
    apply measurable_pi_lambda; intro i
    exact measurable_gBlock.comp (measurable_pi_apply i)
  have hcomp : (fun y : (Fin N × Fin 2) → ℝ => fun i => (y (i, 0)) ^ 2 + (y (i, 1)) ^ 2)
      = (fun w : Fin N → Fin 2 → ℝ => fun i => gBlock (w i))
          ∘ (fun y : (Fin N × Fin 2) → ℝ => fun i j => y (i, j)) := by
    funext y; rfl
  rw [hcomp, ← Measure.map_map hblock hcurry,
    map_curryProd_pi (ν := fun _ : Fin N × Fin 2 => gaussianReal 0 1)]
  -- per-factor map: `map (fun w i => gBlock (w i)) (pi μ) = pi (fun i => map gBlock (μ i))`.
  haveI hsf : ∀ _i : Fin N,
      SigmaFinite (Measure.map gBlock (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))) := by
    intro _i; rw [gBlock_map_pi]; infer_instance
  rw [Measure.pi_map_pi (f := fun _ : Fin N => gBlock)
    (fun _ => measurable_gBlock.aemeasurable)]
  simp only [gBlock_map_pi]

end LF4
end CSD

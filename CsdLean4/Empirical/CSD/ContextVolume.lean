import CsdLean4.LF4.BornFrequencyN

/-!
# Empirical/CSD: arbitrary projective measurement contexts as derived Kähler volumes

**Category:** 3-Local (CSD-ontic layer; genuine volume derivation, not a
transport tag, and **not** conditional on any preparation bundle).

The context-generic surfacing of `LF4.born_frequency_convergence_N`: measuring a
pure state `ψ` on `ℂℙ^M` in **any** orthonormal-basis (rank-1 projective)
context `B`, the outcome Born weights `‖⟨B i, ψ⟩‖²` are genuine Fubini–Study
typicality volumes on the ontic `Σ = ℂℙ^M`. Carving-free, Gleason-free,
unconditional modulo the genericity hypothesis `hpos`. In the spirit of
`Empirical/CSD/BellVolume.lean`, `Empirical/CSD/GHZVolume.lean`, and
`Empirical/CSD/HardyVolume.lean`, but parameterised over the *context* rather
than a fixed state.

## The key reduction (no new geometry)

Measuring `ψ` in the orthonormal context `B` is, coordinate-for-coordinate,
measuring the rotated coordinate vector `B.repr ψ` in the computational basis:

```
⟨B i, ψ⟩ = (B.repr ψ) i = ⟨eᵢ, B.repr ψ⟩         (OrthonormalBasis.repr_apply_apply
                                                  + EuclideanSpace.inner_single_left)
```

so `‖⟨B i, ψ⟩‖² = ‖⟨eᵢ, B.repr ψ⟩‖²`. Since `B.repr` is a `LinearIsometryEquiv`,
`‖B.repr ψ‖ = ‖ψ‖`, so the rotated state inherits norm-one and (under `hpos`)
the same interior-point genericity. Instantiating `born_frequency_convergence_N`
at `B.repr ψ` therefore lands exactly on the context Born weights `‖⟨B i, ψ⟩‖²`,
with the Born = ontic-volume content (`fs_born_volume_ratio_N` / `_apex`)
already discharged for the rotated state. No Busch, no carving.

## Why this is the grounding for contextuality

The Kochen–Specker / Mermin–Peres no-go statements (`Empirical/QM/`) turn on
the fact that the outcome weights a measurement assigns are **context-dependent**:
no single non-contextual hidden-variable assignment of `0/1` values to all rays
reproduces the quantum statistics across overlapping contexts. This file realises
each such context's rank-1 outcome weight as a genuine Fubini–Study typicality
volume on the *same* ontic `Σ = ℂℙ^M` — the context enters only through which
orthonormal frame `B` carves the moment regions, not through any extra ontic
structure. The context-dependence the KS/MP theorems exploit is, on the CSD
ontology, the dependence of the carved volume regions on the measurement frame.

## Honest scope

Rank-1 (non-degenerate) projective contexts only. Degenerate-eigenspace
measurements (e.g. the two-qubit Mermin–Peres observables, whose eigenprojectors
have rank > 1) are **not** covered by this lemma: `born_frequency_convergence_N`
is stated for the `N`-element computational outcome partition, one ray per
outcome. The genericity hypothesis `hpos` (every context Born weight strictly
positive) makes the rotated state an interior simplex point; boundary contexts
need a separate carve-out, exactly as for the per-state files. The LHV / KS / MP
impossibility itself lives in `Empirical/QM/` (`KochenSpecker`, `MerminPeres`).
-/

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace ContextVolume

variable {M : ℕ}

/-! ### The context-rotation identity (step 1) -/

/-- **Context ↔ rotated-state Born identity.** The Born weight of outcome `i` when
measuring `ψ` in the orthonormal context `B` equals the `i`-th computational Born
weight of the rotated coordinate vector `B.repr ψ`. Pure inner-product geometry:
`⟨B i, ψ⟩ = (B.repr ψ) i = ⟨eᵢ, B.repr ψ⟩` (`OrthonormalBasis.repr_apply_apply`
+ `EuclideanSpace.inner_single_left`). -/
lemma context_born_eq_rotated
    (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (i : Fin (M + 1)) :
    ‖inner ℂ (B i) ψ‖ ^ 2
      = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) (B.repr ψ)‖ ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, B.repr_apply_apply]

/-! ### Rotated-state norm and genericity transport -/

/-- `B.repr` is a `LinearIsometryEquiv`, so the rotated state preserves the norm. -/
lemma repr_norm (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) : ‖B.repr ψ‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, hψ]

/-- The rotated state is nonzero (it has norm one). -/
lemma repr_ne_zero (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) : B.repr ψ ≠ 0 := by
  intro h
  have : ‖B.repr ψ‖ = 0 := by rw [h, norm_zero]
  rw [repr_norm B ψ hψ] at this
  exact one_ne_zero this

/-- Genericity transports along the rotation: if every context Born weight is
strictly positive, so is every computational Born weight of `B.repr ψ`. -/
lemma repr_hpos (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1)))
    (hpos : ∀ i, 0 < ‖inner ℂ (B i) ψ‖ ^ 2) :
    ∀ i, 0 < ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) (B.repr ψ)‖ ^ 2 := by
  intro i
  rw [← context_born_eq_rotated B ψ i]
  exact hpos i

/-! ### The context volume-frequency capstone -/

/-- **Any projective measurement context's outcome Born weights as derived Kähler
volumes.** For i.i.d. trials drawing microstates from the Fubini–Study typicality
measure on the ontic `Σ = ℂℙ^M`, the empirical frequencies of the `N = M+1`
barycentric Born outcome regions (carved in the rotated frame `B.repr ψ`)
converge, on a single almost-sure event, to the context Born weights
`‖⟨B i, ψ⟩‖²` of measuring the norm-one preparation `ψ` in the orthonormal
context `B`.

Carving-free, Gleason-free, unconditional — no `busch_effect_gleason`, no carved
regions, no preparation bundle. The proof is the rotation reduction: instantiate
`born_frequency_convergence_N` at `B.repr ψ` (norm one and generic by
`repr_norm` / `repr_hpos`), then rewrite the computational Born weights back to
the context weights via `context_born_eq_rotated`.

This grounds **every** rank-1 projective measurement context — the reusable
contextuality primitive (Kochen–Specker, the rank-1 Mermin–Peres parts): each
context-dependent outcome weight that a non-contextual hidden-variable assignment
cannot jointly reproduce is here a genuine Fubini–Study typicality volume on the
fixed ontic `Σ`. Honest scope: rank-1 (non-degenerate) contexts; degenerate
eigenspaces are out (see the module docstring). -/
theorem context_born_frequency_volume
    (p₀ : CPN (M + 1))
    (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ i, 0 < ‖inner ℂ (B i) ψ‖ ^ 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((X k) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (B i) ψ‖ ^ 2)) := by
  have key := born_frequency_convergence_N (M := M) p₀ (B.repr ψ)
    (repr_ne_zero B ψ hψ) (repr_norm B ψ hψ) (repr_hpos B ψ hpos) X hX hlaw hindep
  filter_upwards [key] with ω hω i
  rw [context_born_eq_rotated B ψ i]
  exact hω i

end ContextVolume
end CSDBridge
end Empirical
end CSD

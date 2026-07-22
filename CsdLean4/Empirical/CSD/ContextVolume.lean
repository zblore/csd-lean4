/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.BornRegionUncond
public import CsdLean4.LF4.BornRegionDisjoint

/-!
# Empirical/CSD: arbitrary projective measurement contexts as derived Kähler volumes

**Category:** 3-Local (CSD-ontic layer; genuine volume derivation, not a
transport tag, and **not** conditional on any preparation bundle).

The context-generic surfacing of `LF4.born_frequency_convergence_N_uncond`:
measuring a pure state `ψ` on `ℂℙ^M` in **any** orthonormal-basis (rank-1
projective) context `B`, the outcome Born weights `‖⟨B i, ψ⟩‖²` are genuine
Fubini–Study typicality volumes on the ontic `Σ = ℂℙ^M`. Carving-free,
Gleason-free, unconditional — **every** unit preparation, eigenstates of the
context included (no genericity hypothesis; hpos-free since the 2026-06-11
call-site migration onto `LF4/BornRegionUncond.lean`). In the spirit of
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
`‖B.repr ψ‖ = ‖ψ‖`, so the rotated state inherits norm-one. Instantiating
`born_frequency_convergence_N_uncond` at `B.repr ψ` therefore lands exactly on
the context Born weights `‖⟨B i, ψ⟩‖²`, with the Born = ontic-volume content
(`fs_born_volume_ratio_N_uncond` / `_apex_uncond`) already discharged for the
rotated state — vanishing rotated amplitudes give FS-null cells, which **is**
the Born weight `0`. No Busch, no carving.

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

No genericity hypothesis: the capstones cover **every** unit preparation `ψ`,
including eigenstates of the context (`ψ = B i`, the Kochen–Specker-interesting
boundary preparations) — resolving the earlier limitation, recorded at the
a9c3a50 landing, that `ψ = B 0` failed the engine-inherited `hpos`. Zero-weight
outcome cells genuinely collapse to FS-null sets (BornRegionUncond per-cell
dichotomy); they are not redefined to hit Born values. The LHV / KS / MP
impossibility itself lives in `Empirical/QM/` (`KochenSpecker`, `MerminPeres`).

## Degenerate-eigenspace extension (rank-1 scope note closed)

A **degenerate** projective measurement has outcome projectors `Pₐ` of rank ≥ 1.
Picking an orthonormal eigenbasis `B` adapted to the spectral decomposition and a
block labelling `blk : Fin (M+1) → ι` (the `ι`-many outcome labels), the outcome-`a`
projector is `Pₐ = ∑_{blk i = a} |B i⟩⟨B i|`, so the outcome Born weight is the
**block sum** of per-ray Born weights:

```
⟨ψ, Pₐ ψ⟩ = ∑_{blk i = a} ‖⟨B i, ψ⟩‖²        (block_born_eq_blockSum)
```

a finite **sum of Fubini–Study typicality volumes** on the same ontic `Σ = ℂℙ^M`.
The block (degenerate-outcome) empirical frequency is the finite sum of the per-ray
frequencies (the per-ray barycentric regions are disjoint, so summing the
frequencies is the frequency of their union, the block outcome region), and it
converges to the block Born weight: `block_born_frequency_volume`. This closes the
rank-1 scope note above: degenerate contexts — including the two-qubit Mermin–Peres
rank-2 eigenspace observables and any other rank ≥ 1 projective context — are now
grounded as block sums of FS volumes. `block_born_eq_blockSum` writes the block
Born weight via the explicit rank-1-sum projector image `Pₐ ψ = ∑_{blk i = a}
⟨B i, ψ⟩ • B i`; the equivalent reading is `∑_{blk i = a} ‖⟨B i, ψ⟩‖² =
‖orthogonalProjection (span {B i : blk i = a}) ψ‖²` (Parseval over the orthonormal
sub-family), which is the standard "projection onto the eigenspace" statement.

Honest scope unchanged from the rank-1 case: this is a faithful **realisation**,
not a derivation (`Φ = id`, the FS regions carved in the rotated frame); the
contextuality / KS / MP no-go stays at the QM-validity layer (`Empirical/QM/`).
-/

@[expose] public section

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
strictly positive, so is every computational Born weight of `B.repr ψ`.
No longer consumed by the capstones below (they route through the hpos-free
`born_frequency_convergence_N_uncond`); retained for callers of the conditional
engine `born_frequency_convergence_N`. -/
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
regions, no preparation bundle, **no genericity hypothesis**. The proof is the
rotation reduction: instantiate `born_frequency_convergence_N_uncond` at
`B.repr ψ` (norm one by `repr_norm`), then rewrite the computational Born
weights back to the context weights via `context_born_eq_rotated`.

This grounds **every** rank-1 projective measurement context at **every** unit
preparation — eigenstates of the context included (`ψ = B i`: the other rays'
cells are FS-null and their frequencies converge to `0`) — the reusable
contextuality primitive (Kochen–Specker, the rank-1 Mermin–Peres parts): each
context-dependent outcome weight that a non-contextual hidden-variable assignment
cannot jointly reproduce is here a genuine Fubini–Study typicality volume on the
fixed ontic `Σ`. Honest scope: rank-1 (non-degenerate) contexts; degenerate
eigenspaces via `block_born_frequency_volume` (see the module docstring). -/
theorem context_born_frequency_volume
    (p₀ : CPN (M + 1))
    (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1)
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
  have key := born_frequency_convergence_N_uncond (M := M) p₀ (B.repr ψ)
    (repr_ne_zero B ψ hψ) (repr_norm B ψ hψ) X hX hlaw hindep
  filter_upwards [key] with ω hω i
  rw [context_born_eq_rotated B ψ i]
  exact hω i

/-! ### Degenerate-eigenspace blocks (step 1: the block Born weight) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Degenerate-outcome Born weight = block sum of per-ray Born weights.** For an
orthonormal eigenbasis `B` adapted to a block labelling `blk`, the rank-≥1
eigenspace projector for outcome `a` is `Pₐ = ∑_{blk i = a} |B i⟩⟨B i|`, so
`Pₐ ψ = ∑_{blk i = a} ⟨B i, ψ⟩ • B i`. Sandwiching against `ψ` (real part) gives the
block sum of per-ray Born weights `∑_{blk i = a} ‖⟨B i, ψ⟩‖²`, the outcome-`a` Born
weight `⟨ψ, Pₐ ψ⟩`.

Delivered in the **block-sum-direct** form (the projector applied to `ψ` written as
its explicit rank-1 sum), not the `orthogonalProjection`-over-subfamily-span form:
the latter requires constructing an orthonormal basis of the span submodule from the
sub-family of `B`, which is span-of-subfamily friction in Mathlib with no payoff here.
The equivalent projector reading is
`∑_{blk i = a} ‖⟨B i, ψ⟩‖² = ‖orthogonalProjection (span ℂ {B i : blk i = a}) ψ‖²`
(Parseval over the orthonormal sub-family). Proof: `inner_sum` + `inner_smul_right` +
`inner_conj_symm` + `RCLike.mul_conj`, termwise. -/
lemma block_born_eq_blockSum
    (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (blk : Fin (M + 1) → ι) (a : ι) :
    RCLike.re (inner ℂ ψ
        (∑ i ∈ Finset.univ.filter (fun i => blk i = a), (inner ℂ (B i) ψ) • B i))
      = ∑ i ∈ Finset.univ.filter (fun i => blk i = a), ‖inner ℂ (B i) ψ‖ ^ 2 := by
  rw [inner_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_smul_right, ← inner_conj_symm ψ (B i), RCLike.mul_conj, ← RCLike.ofReal_pow]
  exact RCLike.ofReal_re _

/-! ### The degenerate-context block volume-frequency capstone (step 2) -/

omit [Fintype ι] in
/-- **Degenerate projective measurement context's block (eigenspace) Born weight as a
derived sum of Kähler volumes.** For i.i.d. trials drawing microstates from the
Fubini–Study typicality measure on the ontic `Σ = ℂℙ^M`, the empirical frequency of
the degenerate outcome `a` — the finite **sum** of the per-ray empirical frequencies
over the block `{i : blk i = a}` — converges, on a single almost-sure event, to the block
Born weight `∑_{blk i = a} ‖⟨B i, ψ⟩‖² = ⟨ψ, Pₐ ψ⟩` (see `block_born_eq_blockSum`).
(This sum-of-per-ray-frequencies equals the frequency of the *union* of the block's
barycentric per-ray regions, because those regions are pairwise disjoint — the
barycentric subdivision is a genuine partition, now formalised as
`CSD.LF4.bornRegion_pairwiseDisjoint` (LF5-F engine half). The union-event
restatement is `block_born_frequency_volume_event` below; the sum form proved here
needs only additivity of limits.)

Carving-free, Gleason-free, unconditional — no genericity hypothesis (every unit
preparation, eigenvectors of any block included).
Proof: take the single a.s. event from `context_born_frequency_volume` (which gives
**every** ray `i`'s convergence simultaneously) and sum the block's per-ray
convergences via `tendsto_finsetSum`. The per-ray frequency summand is verbatim the
conclusion of `context_born_frequency_volume`, so the per-ray limits feed in directly.

This closes the rank-1 scope note of `context_born_frequency_volume`: degenerate-
eigenspace contexts (the two-qubit Mermin–Peres rank-2 observables and any rank ≥ 1
projective context) are grounded as block sums of FS typicality volumes on the fixed
ontic `Σ`. Honest scope unchanged: realisation not derivation (`Φ = id`, FS regions
carved in the rotated frame); the KS / MP no-go stays at the QM-validity layer. -/
theorem block_born_frequency_volume
    (p₀ : CPN (M + 1))
    (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1)
    (blk : Fin (M + 1) → ι) (a : ι)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => blk i = a),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (∑ i ∈ Finset.univ.filter (fun i => blk i = a),
          ‖inner ℂ (B i) ψ‖ ^ 2)) := by
  have h := context_born_frequency_volume p₀ B ψ hψ X hX hlaw hindep
  filter_upwards [h] with ω hω
  exact tendsto_finsetSum _ (fun i _ => hω i)

/-! ### The union-event restatement (the owed `aeece86` form) -/

omit [Fintype ι] in
/-- **Degenerate-outcome block frequency, as the frequency of a single union
event.** The `aeece86`-owed restatement of `block_born_frequency_volume`: the
empirical frequency of the degenerate outcome `a` stated as the frequency of the
**single** union event `⋃_{blk i = a} bornRegion …` (the eigenspace outcome
region), converging to the block Born weight `∑_{blk i = a} ‖⟨B i, ψ⟩‖²`. The
union form is now available because the per-ray barycentric cells are pairwise
disjoint (`CSD.LF4.bornRegion_pairwiseDisjoint`, LF5-F engine half), so the
indicator of the union equals the sum of the per-ray indicators
(`CSD.LF4.indicator_iUnion_disjoint`). The sum form (`block_born_frequency_volume`)
is untouched. -/
theorem block_born_frequency_volume_event
    (p₀ : CPN (M + 1))
    (B : OrthonormalBasis (Fin (M + 1)) ℂ (EuclideanSpace ℂ (Fin (M + 1))))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1)
    (blk : Fin (M + 1) → ι) (a : ι)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((X k) ⁻¹' (⋃ i ∈ Finset.univ.filter (fun i => blk i = a),
                    bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (∑ i ∈ Finset.univ.filter (fun i => blk i = a),
          ‖inner ℂ (B i) ψ‖ ^ 2)) := by
  have hbase := block_born_frequency_volume p₀ B ψ hψ blk a X hX hlaw hindep
  filter_upwards [hbase] with ω hω
  -- the union-event indicator equals the block sum of per-ray indicators
  have hdisj : ∀ k,
      ((Finset.univ.filter (fun i => blk i = a)) : Set (Fin (M + 1))).PairwiseDisjoint
        (fun i => (X k) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i) := by
    intro k i _ j _ hij
    exact (bornRegion_pairwiseDisjoint (B.repr ψ) (repr_ne_zero B ψ hψ) hij).preimage _
  have hind : ∀ k ω0,
      Set.indicator ((X k) ⁻¹' (⋃ i ∈ Finset.univ.filter (fun i => blk i = a),
          bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)) (fun _ => (1 : ℝ)) ω0
      = ∑ i ∈ Finset.univ.filter (fun i => blk i = a),
          Set.indicator ((X k) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)
            (fun _ => (1 : ℝ)) ω0 := by
    intro k ω0
    rw [Set.preimage_iUnion₂]
    exact CSD.LF4.indicator_iUnion_disjoint _ _ (hdisj k) _ ω0
  have hfreq_eq : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
          Set.indicator ((X k) ⁻¹' (⋃ i ∈ Finset.univ.filter (fun i => blk i = a),
              bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)) (fun _ => (1 : ℝ)) ω) / (m : ℝ)
      = ∑ i ∈ Finset.univ.filter (fun i => blk i = a),
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' bornRegion (B.repr ψ) (repr_ne_zero B ψ hψ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ) := by
    intro m
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hind k ω)
  simp_rw [hfreq_eq]
  exact hω

/-! ### Concrete degenerate (rank-2) witness: the two-qubit parity `Z⊗Z` -/

/-- **Concrete degenerate (rank-2) witness: the two-qubit parity observable `Z⊗Z`.**
The parity / `Z⊗Z` outcome Born weight realised as a block sum of Fubini–Study
typicality volumes — the Mermin–Peres rank-2 observable case made explicit.

`Z⊗Z` on `EuclideanSpace ℂ (Fin 4)` has eigenvalues `±1`, each eigenspace of
rank 2; its eigenbasis **is** the computational basis (no rotation needed), so we
take `B := EuclideanSpace.basisFun (Fin 4) ℂ` (whose `i`-th vector is
`EuclideanSpace.single i 1`, `EuclideanSpace.basisFun_apply`). The block labelling
`blk = ![0,1,1,0] : Fin 4 → Fin 2` is the parity grouping of the two-qubit strings:
indices `{0,3}` (`|00⟩, |11⟩`, even parity, eigenvalue `+1`) ↦ outcome `0`; indices
`{1,2}` (`|01⟩, |10⟩`, odd parity, eigenvalue `−1`) ↦ outcome `1`.

Instantiating `block_born_frequency_volume` at `B`, `blk`, `a = 0` and collapsing the
even-parity block `{0,3}` (`Finset.sum_pair`, `decide` on the filter), the empirical
frequency of the even-parity (`Z⊗Z = +1`) outcome converges almost surely to the
`Z⊗Z = +1` Born weight `‖⟨e₀, ψ⟩‖² + ‖⟨e₃, ψ⟩‖² = ⟨ψ, P₊ ψ⟩`, a block sum of two
FS typicality volumes on the fixed ontic `Σ = ℂℙ³`. Carving-free, Gleason-free,
foundational-triple-only.

Honest scope unchanged from the generic degenerate case (`block_born_frequency_volume`):
this is a faithful **realisation** of the rank-2 outcome weight as a sum of ontic
volumes, not a derivation (`Φ = id`, FS regions carved in the computational frame);
the Mermin–Peres / Kochen–Specker no-go itself stays at the QM-validity layer
(`Empirical/QM/`). No genericity hypothesis: every unit two-qubit preparation is
covered, the computational eigenstates `|00⟩, |01⟩, |10⟩, |11⟩` (and the Bell
states with vanishing components) included. -/
theorem zz_parity_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
              (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 1, 0] : Fin 4 → Fin 2) i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
                    (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (3 : Fin 4) (1 : ℂ)) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ
    (![0, 1, 1, 0] : Fin 4 → Fin 2) 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 1, 0] : Fin 4 → Fin 2) i = 0),
          ‖inner ℂ ((EuclideanSpace.basisFun (Fin 4) ℂ) i) ψ‖ ^ 2)
        = ‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (3 : Fin 4) (1 : ℂ)) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => (![0, 1, 1, 0] : Fin 4 → Fin 2) i = 0))
          = {0, 3} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 3),
      EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
  rw [← hsum]
  exact h

end ContextVolume
end CSDBridge
end Empirical
end CSD

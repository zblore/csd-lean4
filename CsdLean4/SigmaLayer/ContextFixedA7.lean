/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.MomentMap

/-!
# Context-fixed A7 at general `N`: the support reduction

**Category:** SigmaLayer (the Paper C A7 architecture).

Paper C **A7** asks for outcome regions `Ωᵢ(M) ⊂ ℂℙⁿ⁻¹` fixed by the **apparatus context `M`
alone**, together with a preparation law `ρ_ψ^ep`, such that

  `P(i ∣ M, ψ) = ∫_{Ωᵢ(M)} ρ_ψ^ep dμ_FS = |⟨eᵢ|ψ⟩|²`.

Under `U(N)`-covariance the preparation density collapses to `ρ_ψ^ep(φ) = g(|⟨ψ|φ⟩|²)` for a
**single** function `g : [0,1] → ℝ≥0`, the same for every state and every context. So the whole
question is whether such a `g` exists. At `N = 2` it does — `g(s) = 4(2s−1)₊`, the CSD spread
density, with `{Ωᵢ}` the hemispheres (`LF4/QubitBorn.lean` `qubitBorn`). At `N ≥ 3` the question
is **open in both directions** (`specs/BACKLOG.md`; the earlier "provably dead" verdict rested on
numerics plus an informal argument and was retracted 2026-07-28).

## What this file contributes

The **support reduction**: a hard, elementary constraint on any such `g`, obtained by evaluating
the A7 requirement at the `n` basis-vector preparations `ψ = eⱼ`, where the Born weights are
`|⟨eᵢ|eⱼ⟩|² = δᵢⱼ`. For `i ≠ j` the requirement says a **non-negative** integrand integrates to
**zero** over `Ωᵢ`, which forces it to vanish a.e. there. Consequently

* `overlapSupport_ae_subset` — the support of `g ∘ sⱼ` lies inside `Ωⱼ` (a.e.);
* `overlapSupports_ae_disjoint` — the `n` supports are pairwise a.e. disjoint;
* `sum_measure_overlapSupport_le_one` — their measures sum to at most `1`, so by symmetry each is
  at most `1/n`.

Read physically: **a base-only preparation density must be concentrated, with the region it
occupies shrinking as `1/n`, while still integrating to `1`.** It has to spike. That is a genuine
structural obstruction — it is what the `N = 2` solution `4(2s−1)₊`, supported exactly on
`(½, 1]`, is doing — and it sharply narrows the space any `N ≥ 3` construction must live in.

## Deliberately stated over an abstract measure space

Nothing here needs projective geometry: it is the measure-theoretic core, so it is proved once,
for a probability space with `n` overlap functions and `n` disjoint regions. The intended
instantiation is `X := CPN n`, `μ := fubiniStudyMeasure p₀` (a probability measure), `s j :=`
`momentMap · j` (`momentMap_mk_eq_inner_sq` identifies it with `|⟨eⱼ|φ⟩|²`, and
`momentMap_sum_eq_one` gives `∑ⱼ sⱼ = 1`), `Ω j := Ωⱼ(M)`. Keeping it abstract also means the
result survives a move to a fibred `Σ`, where the same reduction applies verbatim.

## What this does NOT do

**It is not the no-go.** It constrains `g`; it does not refute it. Two things stand between this
and a genuine `N ≥ 3` impossibility theorem:

1. **The generic-`ψ` requirement is untouched.** Everything here comes from the `n` basis-vector
   preparations. The suspected obstruction lives at generic `ψ`, where the Born value
   `|⟨eᵢ|ψ⟩|²` varies continuously and the cap around `ψ` straddles several regions.
2. **The harmonic argument is out of reach.** The informal reason for pessimism is that
   `g(|⟨ψ|φ⟩|²)` integrated over a fixed region produces, as a function of `ψ`, components of
   every degree `(k,k)`, while the target `|⟨eᵢ|ψ⟩|²` is pure degree `(1,1)`; killing the higher
   harmonics for all regions and all contexts is what should fail at `N ≥ 3`. Formalising that
   needs representation theory / harmonic analysis on `ℂℙⁿ⁻¹` for which Mathlib has no API.

So: this is step one of the no-go, and it is honest about being step one.

## References

`LF4/QubitBorn.lean` (`qubitBorn`, the `N = 2` case that *does* work); `LF4/MomentMap.lean`
(`momentMap_mk_eq_inner_sq`, `momentMap_sum_eq_one`); `specs/BACKLOG.md` (the re-opened
general-`N` A7 row, and the `hpos` boundary row — note the DH region machinery cannot express a
vanishing amplitude, a second structural limit at this same spot);
`specs/record-layer-plan.md` §3; `specs/sigma-fibre-contextuality.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.SigmaLayer

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {n : ℕ}

/-- The set where the preparation density is non-zero at overlap function `s`: the ontic states
that a preparation with overlap profile `s` can actually occupy. -/
def overlapSupport (g : ℝ → ℝ) (s : X → ℝ) : Set X := {x | g (s x) ≠ 0}

theorem measurableSet_overlapSupport {g : ℝ → ℝ} {s : X → ℝ}
    (h : Measurable fun x => g (s x)) : MeasurableSet (overlapSupport g s) :=
  h (measurableSet_singleton (0 : ℝ)).compl

/-! ### The reduction -/

/-- **A non-negative density with a vanishing Born weight vanishes on that region.**

This is the whole mechanism, isolated. The A7 requirement at preparation `eⱼ` and outcome `i ≠ j`
reads `∫_{Ωᵢ} g(sⱼ) dμ = |⟨eᵢ|eⱼ⟩|² = 0`; since `g ≥ 0`, a zero integral forces the integrand to
vanish almost everywhere on `Ωᵢ`. Non-negativity of the preparation density is doing all the work
— exactly the hypothesis a signed density would escape. -/
theorem ae_eq_zero_of_setIntegral_eq_zero {g : ℝ → ℝ} {s : X → ℝ} {Ω : Set X}
    (hg : ∀ t, 0 ≤ g t)
    (hint : IntegrableOn (fun x => g (s x)) Ω μ)
    (hzero : ∫ x in Ω, g (s x) ∂μ = 0) :
    ∀ᵐ x ∂(μ.restrict Ω), g (s x) = 0 := by
  have hnn : 0 ≤ᵐ[μ.restrict Ω] fun x => g (s x) := Filter.Eventually.of_forall fun x => hg (s x)
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hzero
  filter_upwards [this] with x hx using hx

/-- **The support of the density for outcome `j` lies inside region `j`** (up to a null set).

Given the off-diagonal A7 conditions — the Born weight of outcome `i` at preparation `eⱼ` is zero
for `i ≠ j` — and a covering family of regions, the states where `g(sⱼ) ≠ 0` cannot lie in any
region other than `Ωⱼ`. -/
theorem overlapSupport_ae_subset {g : ℝ → ℝ} {s : Fin n → X → ℝ} {Ω : Fin n → Set X}
    (hg : ∀ t, 0 ≤ g t)
    (hint : ∀ i j, IntegrableOn (fun x => g (s j x)) (Ω i) μ)
    (hoff : ∀ i j, i ≠ j → ∫ x in Ω i, g (s j x) ∂μ = 0)
    (hcover : ∀ x, ∃ i, x ∈ Ω i)
    (hmeas : ∀ i, MeasurableSet (Ω i)) (j : Fin n) :
    μ (overlapSupport g (s j) \ Ω j) = 0 := by
  classical
  -- Off `Ω j`, every state lies in some `Ω i` with `i ≠ j`, where the density vanishes a.e.
  have hsub : overlapSupport g (s j) \ Ω j ⊆ ⋃ i ∈ ({j}ᶜ : Set (Fin n)),
      (overlapSupport g (s j) ∩ Ω i) := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x
    have hij : i ≠ j := by rintro rfl; exact hx.2 hi
    exact mem_biUnion (by simpa using hij) ⟨hx.1, hi⟩
  refine measure_mono_null hsub ?_
  refine measure_biUnion_null_iff (Set.to_countable _) |>.mpr fun i hi => ?_
  have hij : i ≠ j := by simpa using hi
  -- On `Ω i` the density is a.e. zero, so its support meets `Ω i` in a null set.
  have hae := ae_eq_zero_of_setIntegral_eq_zero hg (hint i j) (hoff i j hij)
  rw [ae_restrict_iff' (hmeas i)] at hae
  have : {x | x ∈ overlapSupport g (s j) ∩ Ω i} ⊆ {x | ¬ (x ∈ Ω i → g (s j x) = 0)} := by
    rintro x ⟨hxs, hxi⟩ hcon
    exact hxs (hcon hxi)
  exact measure_mono_null this hae

/-- **The supports are pairwise almost disjoint.** Distinct outcomes' preparation supports cannot
overlap on a set of positive measure: each is confined to its own region, and the regions are
disjoint. -/
theorem overlapSupports_ae_disjoint {g : ℝ → ℝ} {s : Fin n → X → ℝ} {Ω : Fin n → Set X}
    (hg : ∀ t, 0 ≤ g t)
    (hint : ∀ i j, IntegrableOn (fun x => g (s j x)) (Ω i) μ)
    (hoff : ∀ i j, i ≠ j → ∫ x in Ω i, g (s j x) ∂μ = 0)
    (hcover : ∀ x, ∃ i, x ∈ Ω i)
    (hmeas : ∀ i, MeasurableSet (Ω i))
    (hdisj : Pairwise (Function.onFun Disjoint Ω)) {j k : Fin n} (hjk : j ≠ k) :
    μ (overlapSupport g (s j) ∩ overlapSupport g (s k)) = 0 := by
  have hj := overlapSupport_ae_subset hg hint hoff hcover hmeas j
  have hk := overlapSupport_ae_subset hg hint hoff hcover hmeas k
  -- Anything in both supports is either outside `Ω j`, or outside `Ω k`, or in both regions.
  have hsub : overlapSupport g (s j) ∩ overlapSupport g (s k)
      ⊆ (overlapSupport g (s j) \ Ω j) ∪ (overlapSupport g (s k) \ Ω k) := by
    rintro x ⟨hxj, hxk⟩
    by_cases hj' : x ∈ Ω j
    · right
      refine ⟨hxk, fun hk' => ?_⟩
      exact absurd (hdisj hjk) (by
        intro hd
        exact Set.not_disjoint_iff.mpr ⟨x, hj', hk'⟩ hd)
    · exact Or.inl ⟨hxj, hj'⟩
  exact measure_mono_null hsub (by
    simpa using measure_union_null hj hk)

/-- **The supports occupy at most the whole space, hence at most `1/n` each by symmetry.**

The quantitative form of the reduction: a base-only preparation density is confined to `n`
pairwise-disjoint sets whose measures sum to at most `1`. Each must still carry total integral
`1`, so as `n` grows the density has to spike on an ever-smaller set. -/
theorem sum_measure_overlapSupport_le_one [IsProbabilityMeasure μ]
    {g : ℝ → ℝ} {s : Fin n → X → ℝ} {Ω : Fin n → Set X}
    (hg : ∀ t, 0 ≤ g t)
    (hint : ∀ i j, IntegrableOn (fun x => g (s j x)) (Ω i) μ)
    (hoff : ∀ i j, i ≠ j → ∫ x in Ω i, g (s j x) ∂μ = 0)
    (hcover : ∀ x, ∃ i, x ∈ Ω i)
    (hmeas : ∀ i, MeasurableSet (Ω i))
    (hdisj : Pairwise (Function.onFun Disjoint Ω)) :
    ∑ j, μ (overlapSupport g (s j)) ≤ 1 := by
  classical
  -- Each support is contained in its region up to a null set, so is no bigger.
  have hle : ∀ j, μ (overlapSupport g (s j)) ≤ μ (Ω j) := by
    intro j
    have h0 := overlapSupport_ae_subset hg hint hoff hcover hmeas j
    have : overlapSupport g (s j) ⊆ (overlapSupport g (s j) \ Ω j) ∪ Ω j := by
      intro x hx; by_cases h : x ∈ Ω j
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    calc μ (overlapSupport g (s j))
        ≤ μ ((overlapSupport g (s j) \ Ω j) ∪ Ω j) := measure_mono this
      _ ≤ μ (overlapSupport g (s j) \ Ω j) + μ (Ω j) := measure_union_le _ _
      _ = μ (Ω j) := by rw [h0, zero_add]
  calc ∑ j, μ (overlapSupport g (s j))
      ≤ ∑ j, μ (Ω j) := Finset.sum_le_sum fun j _ => hle j
    _ = μ (⋃ j, Ω j) := by
        rw [measure_iUnion hdisj hmeas, tsum_fintype]
    _ ≤ 1 := prob_le_one

/-! ### Step two: the cap — the density is confined above `½`

The supports are `Aᵢ = {φ : sᵢ(φ) ∈ S_g}` for `S_g = {t | g t ≠ 0}`, and step one showed them
pairwise a.e. disjoint. Now push on that.

Suppose `S_g` contained a positive-measure set `T` of overlap values **below `½`**. Two
coordinates taking values in `T` sum to less than `1`, so such states are not excluded by
`∑ᵢ sᵢ = 1` — and at `N ≥ 3` there is a third coordinate free to absorb the remainder, so they
occur with positive measure. Any such state lies in `Aⱼ ∩ Aₖ`, contradicting disjointness.

Conclusion: `g` vanishes a.e. below `½`. The `N = 2` solution `4(2s−1)₊` is supported exactly on
`(½, 1]`, so the bound is sharp and attained.

The state-abundance input is taken as an explicit hypothesis (`hjoint`) rather than derived,
because deriving it is the Dirichlet pushforward of `μ_FS` — real work, and orthogonal to the
argument. What makes this worth stating that way is `joint_degenerate_of_sum_eq_one` below:
**the hypothesis fails at `N = 2`, and that failure is exactly the qubit's escape route.** -/

/-- **The cap bound.** If two overlap coordinates can jointly take values in any positive-measure
set below `½`, then the preparation density vanishes almost everywhere below `½`. -/
theorem cap_of_joint_nondegenerate {g : ℝ → ℝ} {s : Fin n → X → ℝ} {j k : Fin n}
    (hgm : Measurable g)
    (hdisj : μ (overlapSupport g (s j) ∩ overlapSupport g (s k)) = 0)
    (hjoint : ∀ T : Set ℝ, MeasurableSet T → T ⊆ Set.Ioo 0 (1 / 2 : ℝ) → 0 < volume T →
      0 < μ {x | s j x ∈ T ∧ s k x ∈ T}) :
    volume ({t | g t ≠ 0} ∩ Set.Ioo 0 (1 / 2 : ℝ)) = 0 := by
  by_contra hne
  have hpos : 0 < volume ({t | g t ≠ 0} ∩ Set.Ioo 0 (1 / 2 : ℝ)) := pos_iff_ne_zero.mpr hne
  have hTm : MeasurableSet ({t | g t ≠ 0} ∩ Set.Ioo 0 (1 / 2 : ℝ)) :=
    (hgm (measurableSet_singleton (0 : ℝ)).compl).inter measurableSet_Ioo
  have hjk := hjoint _ hTm Set.inter_subset_right hpos
  -- A state whose `j`- and `k`-coordinates both land in the set lies in both supports.
  have hcontain :
      {x | s j x ∈ ({t | g t ≠ 0} ∩ Set.Ioo 0 (1 / 2 : ℝ)) ∧
           s k x ∈ ({t | g t ≠ 0} ∩ Set.Ioo 0 (1 / 2 : ℝ))}
        ⊆ overlapSupport g (s j) ∩ overlapSupport g (s k) := by
    rintro x ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact ⟨h1, h2⟩
  have hlt := lt_of_lt_of_le hjk (measure_mono hcontain)
  rw [hdisj] at hlt
  exact lt_irrefl 0 hlt

omit [MeasurableSpace X] in
/-- **Why the qubit escapes.** When two overlap coordinates are complementary — `sⱼ + sₖ = 1`,
which is forced at `N = 2` because the two Born weights exhaust the state — they can *never* both
lie below `½`. So the abundance hypothesis of `cap_of_joint_nondegenerate` fails identically, and
no cap bound follows.

This is not a technicality: it is the structural reason `N = 2` admits a base-only density at all.
At `N ≥ 3` the coordinates stop being functionally dependent, a third one is free to absorb the
remainder, and the escape closes. -/
theorem joint_degenerate_of_sum_eq_one {s : Fin n → X → ℝ} {j k : Fin n}
    (hsum : ∀ x, s j x + s k x = 1) {T : Set ℝ} (hT : T ⊆ Set.Iio (1 / 2 : ℝ)) :
    {x | s j x ∈ T ∧ s k x ∈ T} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hj hk
  have h1 : s j x < 1 / 2 := hT hj
  have h2 : s k x < 1 / 2 := hT hk
  have := hsum x
  linarith

/-- **The reduction, assembled.** Under the hypotheses of step one plus joint non-degeneracy of two
overlap coordinates, a base-only `U(N)`-covariant non-negative preparation density is confined to
overlap values `≥ ½` — up to a null set — while still having to integrate to `1`.

Together with `sum_measure_overlapSupport_le_one` this is a genuine squeeze on any `N ≥ 3`
construction: the density lives on a set of measure `≤ 1/n` **and** only where the overlap exceeds
`½`. It is not yet a contradiction; see the module header for the two steps that remain. -/
theorem base_only_density_confined [IsProbabilityMeasure μ]
    {g : ℝ → ℝ} {s : Fin n → X → ℝ} {Ω : Fin n → Set X}
    (hg : ∀ t, 0 ≤ g t)
    (hint : ∀ i j, IntegrableOn (fun x => g (s j x)) (Ω i) μ)
    (hoff : ∀ i j, i ≠ j → ∫ x in Ω i, g (s j x) ∂μ = 0)
    (hcover : ∀ x, ∃ i, x ∈ Ω i)
    (hmeas : ∀ i, MeasurableSet (Ω i))
    (hdisj : Pairwise (Function.onFun Disjoint Ω))
    {j k : Fin n} (hjk : j ≠ k) (hgm : Measurable g)
    (hjoint : ∀ T : Set ℝ, MeasurableSet T → T ⊆ Set.Ioo 0 (1 / 2 : ℝ) → 0 < volume T →
      0 < μ {x | s j x ∈ T ∧ s k x ∈ T}) :
    volume ({t | g t ≠ 0} ∩ Set.Ioo 0 (1 / 2 : ℝ)) = 0 ∧
    ∑ i, μ (overlapSupport g (s i)) ≤ 1 :=
  ⟨cap_of_joint_nondegenerate hgm
      (overlapSupports_ae_disjoint hg hint hoff hcover hmeas hdisj hjk) hjoint,
   sum_measure_overlapSupport_le_one hg hint hoff hcover hmeas hdisj⟩

/-! ### Step four: orthogonal preparations, and the `(n−1)/n` support bound

Steps one to three used only the `n` basis-vector preparations. The first genuinely
**generic-`ψ`** input is the *orthogonal* one: whenever `ψ ⊥ eᵢ` the Born weight `|⟨eᵢ|ψ⟩|²`
is zero, so the same non-negativity argument applies — `g ∘ sψ` must vanish a.e. on `Ωᵢ`.

What makes this stronger than the basis-vector case is that there are *many* such `ψ`, and the
overlap values they realise at a given `φ` sweep an entire interval. For unit `ψ ⊥ eᵢ`, the
overlap `|⟨ψ|φ⟩|²` is maximised at the normalised projection of `φ` into `eᵢ^⊥`, with value
`1 − sᵢ(φ)`; tilting `ψ` within `eᵢ^⊥` scales it continuously down to `0`. **That tilt needs
`dim eᵢ^⊥ ≥ 2`, i.e. `n ≥ 3`** — at `n = 2` the orthocomplement is a line, `ψ` is unique up to
phase, and only the single value `1 − sᵢ(φ)` is realised. The same threshold, for the third
independent reason.

So for `n ≥ 3`: a.e. `φ ∈ Ωᵢ` forces `g ≡ 0` on the whole interval `[0, 1 − sᵢ(φ)]`. Since the
regions cover, a.e. `φ` has some `i` with `g ≡ 0` on `[0, 1 − sᵢ(φ)]`, and `maxᵢ sᵢ(φ)` can be
made arbitrarily close to `1/n` on a positive-measure set — so `g` vanishes below `(n−1)/n`.

At `n = 2` that reads `g = 0` below `½`, which is exactly where `4(2s−1)₊` is supported. The
bound is sharp at the one dimension where a solution is known. -/

/-- **Orthogonal-preparation confinement.** If a family of preparations all give outcome `i`
zero Born weight, then on `Ωᵢ` the density vanishes at every overlap value any of them realises.

Only the non-negativity of `g` and the vanishing of the Born weight are used, so this is the
basis-vector argument of step one applied to a much larger family — the first step that uses
preparations other than the `eⱼ`. -/
theorem orthogonal_preparation_vanishes {g : ℝ → ℝ} {Ω : Set X} {u : ℕ → X → ℝ}
    (hg : ∀ t, 0 ≤ g t)
    (hint : ∀ m, IntegrableOn (fun x => g (u m x)) Ω μ)
    (hzero : ∀ m, ∫ x in Ω, g (u m x) ∂μ = 0)
    (hmeas : MeasurableSet Ω) :
    ∀ᵐ x ∂μ, x ∈ Ω → ∀ m, g (u m x) = 0 := by
  have hall : ∀ m, ∀ᵐ x ∂μ, x ∈ Ω → g (u m x) = 0 := by
    intro m
    have := ae_eq_zero_of_setIntegral_eq_zero hg (hint m) (hzero m)
    rwa [ae_restrict_iff' hmeas] at this
  rw [← ae_all_iff] at hall
  filter_upwards [hall] with x hx hxΩ m using hx m hxΩ

/-- **The interval form.** If, at almost every `x ∈ Ω`, the realised overlap values are dense in
`[0, r x]` and `g` is continuous, the vanishing extends from those values to the whole interval.

The density hypothesis is the geometric input: for `ψ` ranging over the unit sphere of `eᵢ^⊥`,
the overlaps `|⟨ψ|φ⟩|²` sweep `[0, 1 − sᵢ(φ)]` — available exactly when `dim eᵢ^⊥ ≥ 2`, i.e.
`n ≥ 3`. -/
theorem vanishes_on_interval_of_dense {g : ℝ → ℝ} {Ω : Set X} {u : ℕ → X → ℝ} {r : X → ℝ}
    (hgc : Continuous g)
    (hvan : ∀ᵐ x ∂μ, x ∈ Ω → ∀ m, g (u m x) = 0)
    (hdense : ∀ x ∈ Ω, ∀ t ∈ Set.Icc (0 : ℝ) (r x),
      ∀ ε > 0, ∃ m, |u m x - t| < ε) :
    ∀ᵐ x ∂μ, x ∈ Ω → ∀ t ∈ Set.Icc (0 : ℝ) (r x), g t = 0 := by
  filter_upwards [hvan] with x hx hxΩ t ht
  -- `g` is continuous and vanishes on a dense subset of `[0, r x]`, hence at `t`.
  by_contra hne
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_ne.preimage hgc) t hne
  obtain ⟨m, hm⟩ := hdense x hxΩ t ht δ hδ
  exact absurd (hx hxΩ m) (hball (by simpa [Real.dist_eq] using hm))

/-! ### Step five: the `(n−1)/n` support bound

Step four gives, for a.e. `φ`, an outcome `i` with `g ≡ 0` on `[0, 1 − sᵢ(φ)]`. To make that a
statement about `g` alone, take `φ` as *balanced* as possible: the smaller `maxᵢ sᵢ(φ)`, the
longer the interval. Since `∑ᵢ sᵢ = 1` forces `maxᵢ sᵢ ≥ 1/n`, the best available interval is
`[0, 1 − 1/n]`, and states arbitrarily close to the barycentre occur with positive measure.

The step is short because step four's conclusion is **pointwise in `g`** — `g` vanishes on a whole
interval, for a.e. `φ`. `g` is a fixed function, so **one** suitable `φ` suffices; no almost-
everywhere bookkeeping survives into the conclusion. -/

/-- A positive-measure set meets any almost-everywhere property. -/
theorem exists_mem_of_measure_pos_of_ae {A : Set X} {P : X → Prop}
    (hA : 0 < μ A) (hP : ∀ᵐ x ∂μ, P x) : ∃ x ∈ A, P x := by
  by_contra hcon
  push Not at hcon
  exact absurd (measure_mono_null (fun x hx => hcon x hx) (ae_iff.mp hP)) (ne_of_gt hA)

/-- **★ The `(n−1)/n` support bound.** A base-only preparation density vanishes on every overlap
value below `(n−1)/n`.

`hvan` is what step four delivers (each state lies in *some* outcome region, and there `g` dies on
`[0, 1 − sᵢ]`); `hbalanced` says states with all overlaps below `c` are not negligible, for any
`c` above the forced minimum `1/n`.

At `n = 2` the bound reads "`g` vanishes below `½`", which is exactly the support of the known
solution `4(2s−1)₊` — sharp at the one dimension where a solution exists. -/
theorem vanishes_below_of_balanced {g : ℝ → ℝ} {s : Fin n → X → ℝ} (_hn : 0 < n)
    (hvan : ∀ᵐ x ∂μ, ∃ i, ∀ t ∈ Set.Icc (0 : ℝ) (1 - s i x), g t = 0)
    (hbalanced : ∀ c : ℝ, 1 / (n : ℝ) < c → 0 < μ {x | ∀ i, s i x ≤ c}) :
    ∀ t ∈ Set.Ico (0 : ℝ) (1 - 1 / (n : ℝ)), g t = 0 := by
  rintro t ⟨ht0, ht1⟩
  -- Aim at states whose overlaps are all at most `1 - t`; that threshold exceeds `1/n`.
  have hc : 1 / (n : ℝ) < 1 - t := by linarith
  obtain ⟨x, hxA, i, hxi⟩ := exists_mem_of_measure_pos_of_ae (hbalanced (1 - t) hc) hvan
  -- `s i x ≤ 1 - t` means the interval `g` dies on reaches at least as far as `t`.
  exact hxi t ⟨ht0, by have := hxA i; linarith⟩

end CSD.SigmaLayer

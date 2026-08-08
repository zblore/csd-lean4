/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.DynamicBorn

/-!
# SigmaLayer/OutcomeField: outcome count decoupled from dimension (item 7)

**Category:** 7-SigmaLayer (the record layer — generalisation).

`ContextField N` ties the number of outcomes to the Hilbert-space dimension: `rate : CPN N → Fin N`.
That is right for a **nondegenerate** measurement and wrong for everything else — a degenerate
projective measurement has fewer outcomes than dimensions.

`OutcomeField N K` decouples them.

## ★ The design constraint this file respects

The plan is explicit on two points, and both are followed:

1. **Introduce `OutcomeField` alongside `ContextField`, do not replace every use of it.** `globalBasin`
   and everything downstream still take a `ContextField`; nothing was refactored. The conversion
   `ContextField.toOutcomeField` shows the generalisation is *conservative*.
2. **Do not treat an arbitrary simplex-valued rate field as automatically physical.** An
   `OutcomeField` is a measurable simplex-valued field and no more — inhabiting it proves nothing
   about an apparatus. The physical content is in `blockField`, which *derives* the field from a
   measurement's degeneracy structure rather than positing it.

## What is proved

* `OutcomeField N K` — a measurable simplex-valued rate field with `K` outcomes on `ℂℙ^{N-1}`.
* `ContextField.toOutcomeField` — every context field is one, with `K = N`. Conservativity.
* `blockField` — ★ **degenerate projective measurements.** Given a degeneracy map `b : Fin N → Fin K`
  grouping basis directions into outcomes, the rate of outcome `i` is `∑_{b j = i} momentMap p j`.
  Non-negativity, normalisation and measurability all come free from the moment map's, because the
  field is a *finite sum of moment coordinates* — the same object, coarse-grained.
* `blockField_id` — with `b = id` this is exactly `momentContext`, so the nondegenerate case is
  recovered rather than replaced.

## The remaining extensions, in the plan's order

`blockField` covers **degenerate projective measurements** (step 2). *Corrected 2026-08-04 (codebase audit).* — **steps 1, 3, 4
and 5 have all since landed** (`measurement_covariance`, `SigmaLayer/RotatedSwap.lean`;
`mixed_swap_sector_born`, `MixedSwap.lean`, with the conditioned update in `MixedLuders.lean`;
`povm_selector_born`/`povm_instrument`, `PovmDynamics.lean`). What this module does not do is
*drive* them. Formerly: still open, and *not* attempted
here: arbitrary orthonormal bases by unitary covariance (step 1 — the `U(N)` action on `CPN` exists,
so this should be cheap); mixed preparations by trace linearity (step 3); POVMs through the existing
Naimark machinery (step 4); instrument-level updates (step 5).

⚠️ And note what is **not** connected: `globalBasin` still consumes a `ContextField`, so an
`OutcomeField` cannot yet drive the dynamical layer. Generalising `globalBasin` is the bridge, and it
is deliberately not done here — see design constraint 1.

## References

`SigmaLayer/GlobalBasin.lean` (`ContextField`, `momentContext`); `LF4/MomentMap.lean`
(`momentMap_nonneg`, `momentMap_sum_eq_one`, `measurable_momentMap`); `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N K : ℕ}

/-- **A measurement's outcome field**: a measurable, simplex-valued rate field with `K` outcomes on
the `N`-dimensional projective base. Unlike `ContextField`, the outcome count is **independent of the
dimension**, which is what a degenerate measurement needs.

⚠️ Inhabiting this proves nothing about a physical apparatus — it is a measurability-and-simplex
condition. See `blockField` for a field that is *derived* from a measurement rather than posited. -/
structure OutcomeField (N K : ℕ) where
  /-- The rate assigned to each ontic base point. -/
  rate : LF4.CPN N → Fin K → ℝ
  /-- Each coordinate is measurable. -/
  measurable_rate : ∀ i, Measurable fun p => rate p i
  /-- The rates are non-negative. -/
  nonneg : ∀ p i, 0 ≤ rate p i
  /-- The rates are normalised. -/
  sum_one : ∀ p, ∑ i, rate p i = 1

/-- **Conservativity**: every `ContextField` is an `OutcomeField` with `K = N`. The generalisation
adds cases, it does not change the existing ones. -/
def ContextField.toOutcomeField (c : ContextField N) : OutcomeField N N where
  rate := c.rate
  measurable_rate := c.measurable_rate
  nonneg := c.nonneg
  sum_one := c.sum_one

/-! ### Degenerate projective measurements -/

variable [NeZero N]

/-- **★ The outcome field of a degenerate projective measurement.**

`b : Fin N → Fin K` is the *degeneracy map*: it says which outcome each basis direction belongs to.
The rate of outcome `i` is the total moment-map weight of its block,

  `rate p i = ∑_{j : b j = i} momentMap p j`

which is the ontic form of `⟨ψ, Π_i ψ⟩` for the projector `Π_i` onto that block's eigenspace.

★ Every field condition comes free from the moment map's, because this is a **finite sum of moment
coordinates** — the same object, coarse-grained. Nothing new is posited: the degeneracy structure is
the only input, and it is combinatorial. -/
noncomputable def blockField (b : Fin N → Fin K) : OutcomeField N K where
  rate p i := ∑ j ∈ Finset.univ.filter (fun j => b j = i), LF4.momentMap p j
  measurable_rate i := by
    classical
    exact Finset.measurable_sum _ fun j _ => LF4.measurable_momentMap j
  nonneg p i := Finset.sum_nonneg fun j _ => LF4.momentMap_nonneg p j
  sum_one p := by
    classical
    rw [← LF4.momentMap_sum_eq_one p]
    exact Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ (b j)) _

omit [NeZero N] in
/-- **The nondegenerate case is recovered, not replaced.** With the identity degeneracy map every
block is a single direction, so `blockField id` is `momentContext` viewed as an `OutcomeField`. -/
theorem blockField_id (p : LF4.CPN N) (i : Fin N) :
    (blockField (id : Fin N → Fin N)).rate p i = (momentContext N).rate p i := by
  classical
  simp only [blockField, momentContext, id_eq]
  rw [Finset.filter_eq' Finset.univ i, if_pos (Finset.mem_univ i), Finset.sum_singleton]

end CSD.RecordLayer

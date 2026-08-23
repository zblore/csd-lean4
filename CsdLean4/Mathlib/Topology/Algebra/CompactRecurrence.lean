/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Recurrence of powers in a compact group

**Category:** 1-Mathlib. A single elementary fact with no CSD content: in a compact topological
group, the powers of any element return to every neighbourhood of the identity, at arbitrarily
large exponents.

This is the classical pigeonhole behind *almost periodicity*, and it is what the equilibration
arc (`specs/equilibration-arc-plan.md` E5) needs in order to say that finite-dimensional unitary
dynamics cannot have decaying correlations: a system whose evolution keeps returning near its
starting configuration cannot forget it.

## The argument

The sequence `n ↦ U ^ n` lives in a compact space, so it has a cluster point `g`. Every
neighbourhood of `g` therefore contains `U ^ n` for infinitely many `n`; pick two such exponents
`i < j` as far apart as desired. Continuity of `(x, y) ↦ y * x⁻¹` at `(g, g)` lets us choose that
neighbourhood small enough that `U ^ j * (U ^ i)⁻¹` lands in the target neighbourhood of `1`, and
powers of a single element commute, so that product *is* `U ^ (j - i)`.

No metric and no second countability are used, only `CompactSpace` and `IsTopologicalGroup`.

Reference: `specs/equilibration-arc-plan.md` (E5); `specs/future-work.md`.
-/

@[expose] public section

open Filter Topology

/-- **Powers recur in a compact group.** For every neighbourhood `V` of `1` and every bound `M`
there is an exponent `n ≥ M` with `U ^ n ∈ V`.

The `M` is the whole point: without it the statement is trivially witnessed by `n = 0`. With it,
the conclusion is that the orbit returns near the identity *forever*, which is what forbids any
quantity built from `U ^ n` from settling to a different value. -/
theorem exists_le_pow_mem_of_compactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (U : G) {V : Set G} (hV : V ∈ 𝓝 (1 : G)) (M : ℕ) :
    ∃ n, M ≤ n ∧ U ^ n ∈ V := by
  -- a cluster point of the power sequence
  obtain ⟨g, hg⟩ : ∃ g : G, MapClusterPt g atTop (fun n : ℕ => U ^ n) :=
    exists_clusterPt_of_compactSpace _
  -- a neighbourhood `A` of `g` on which `y * x⁻¹` stays inside `V`
  have hcont : ContinuousAt (fun p : G × G => p.2 * p.1⁻¹) (g, g) :=
    continuousAt_snd.mul continuousAt_fst.inv
  have hpre : (fun p : G × G => p.2 * p.1⁻¹) ⁻¹' V ∈ 𝓝 ((g, g) : G × G) := by
    refine hcont.preimage_mem_nhds ?_
    simpa using hV
  rw [nhds_prod_eq, mem_prod_self_iff] at hpre
  obtain ⟨A, hA, hsub⟩ := hpre
  -- infinitely many exponents land in `A`; take two of them far apart
  have hfreq : ∃ᶠ n in atTop, U ^ n ∈ A := hg.frequently hA
  obtain ⟨i, -, hi⟩ := frequently_atTop.mp hfreq 0
  obtain ⟨j, hj, hjA⟩ := frequently_atTop.mp hfreq (i + M)
  refine ⟨j - i, by omega, ?_⟩
  have hmem : U ^ j * (U ^ i)⁻¹ ∈ V := hsub (Set.mk_mem_prod hi hjA)
  have hsplit : U ^ j * (U ^ i)⁻¹ = U ^ (j - i) := by
    have hj' : U ^ j = U ^ (j - i) * U ^ i := by
      rw [← pow_add]
      congr 1
      omega
    rw [hj', mul_assoc, mul_inv_cancel, mul_one]
  rwa [hsplit] at hmem

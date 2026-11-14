/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCompositeCarrier

/-!
# Coincidence gates between two carriers

**Category:** 7-SigmaLayer (the record layer). BACKLOG #390 — the author's programme "From `Σ`
to physical spacetime", milestone M6, obligation UO-16; step (4) of the plan of 2026-11-14,
second brick: the couplings of UA-18 (c). No new assumption beyond UA-18.

UA-18 admits one kind of coupling on the radar arena: a coincidence projector of two carriers
times a clock's level swap. This module defines both operators and proves their algebra. No
flow, pointer or record is defined here.

Each carrier's index `i` sits at a site `σ i`. For a relation `r` between sites,
`coincProj σ τ r` is diagonal in the product basis of two carriers and is `1` exactly where
the two sites are related. `gateOp σ τ r Y` is that projector times `1 ⊗ Y`.

* `arenaObs_zero'`, `arenaObs_finset_sum`;
* `siteSel`, `siteSel_isHermitian`;
* `coincProj`, `coincProj_isHermitian`, `coincProj_mul_self`, `one_sub_coincProj` (the
  complement is the coincidence projector of the negated relation);
* ★ `coincProj_eq_sum` — a sum over related pairs of sites of products of site projectors;
* ★★ `arenaObs_coincProj_prodRay` — on a product ray it reads the sum over related pairs of
  the product of the two carriers' site occupancies;
* `gateOp`, ★ `coincProj_mul_one_kronecker` (the projector commutes with every operator of the
  second carrier that does not move it between sites), `gateOp_isHermitian`,
  ★ `gateOp_eq_sum`, ★★ `arenaObs_gateOp_prodRay`.

## Exact scope

* **Operators only.** Nothing here is a flow, a pointer, a reading or a record.
* **Any decidable relation.** UA-18 admits only coincidence within a fixed width. The
  definitions take an arbitrary relation, an order relation included; the restriction is the
  contract's, not this module's.
* **Two carriers.** UA-18 has three. A gate between two of them on the composite of three is
  to be obtained by taking one factor here to be a product; that is not done here.
* **The product-ray formulas are about product rays.** A gated term in the energy joins the
  two carriers. No such flow is defined here. Under one a product ray is not expected to
  stay a product ray, except on a fibre where the pointer's profile vanishes (as in #376)
  when the uncoupled energy does not join the carriers; neither is shown. The formulas say
  nothing about an entangled ray.
* **Earlier.** #376 has the product coupling `P ⊗ X` for one region projector `P`
  (`gateFlow`, UA-17 (c)); `arenaObs_kronecker` (`CV/ProductRay.lean`) is the factorisation
  used here term by term.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-9,
UA-17, UA-18, UO-16, UD-140); `RecordLayer/UnifiedCompositeCarrier.lean` (#376: `gateFlow`,
`prodIdx`); `CV/ProductRay.lean` (`prodRay`, `arenaObs_kronecker`);
`CV/DetunedExchange.lean` (`arenaObs_add`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

section Coincidence

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S]

omit [Fintype ι] [DecidableEq ι] in
theorem arenaObs_zero' [Fintype ι] [DecidableEq ι] (p : GenArena ι) :
    arenaObs (0 : Matrix ι ι ℂ) p = 0 := by
  simp [arenaObs]

/-- The expectation is additive over finite sums of operators. -/
theorem arenaObs_finset_sum {T : Type*} (s : Finset T) (A : T → Matrix ι ι ℂ)
    (p : GenArena ι) : arenaObs (∑ t ∈ s, A t) p = ∑ t ∈ s, arenaObs (A t) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [arenaObs_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, arenaObs_add, ih]

/-- **The projector of a carrier onto one site**, for a carrier whose index `i` sits at the
site `σ i`. -/
def siteSel (σ : ι → S) (s : S) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if σ i = s then 1 else 0

omit [Fintype ι] [Fintype S] in
theorem siteSel_isHermitian (σ : ι → S) (s : S) : (siteSel σ s).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [siteSel, Matrix.diagonal_apply]
  split_ifs <;> simp_all

/-- **The coincidence projector of two carriers** for a relation `r` between sites: diagonal in
the product basis, `1` exactly where the two carriers' sites are related. -/
def coincProj (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r] :
    Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.diagonal fun p => if r (σ p.1) (τ p.2) then 1 else 0

variable (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]

omit [Fintype ι] [Fintype κ] [Fintype S] [DecidableEq S] in
theorem coincProj_isHermitian : (coincProj σ τ r).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [coincProj, Matrix.diagonal_apply]
  split_ifs <;> simp_all

omit [Fintype S] [DecidableEq S] in
/-- The coincidence projector is idempotent. -/
theorem coincProj_mul_self : coincProj σ τ r * coincProj σ τ r = coincProj σ τ r := by
  rw [coincProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

omit [Fintype ι] [Fintype κ] [Fintype S] [DecidableEq S] in
/-- **The complement of a coincidence projector is the coincidence projector of the negated
relation.** -/
theorem one_sub_coincProj :
    1 - coincProj σ τ r = coincProj σ τ (fun a b => ¬ r a b) := by
  ext p q
  simp only [coincProj, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all

omit [Fintype ι] [Fintype κ] in
/-- ★ **A coincidence projector is a sum of products of site projectors.** -/
theorem coincProj_eq_sum :
    coincProj σ τ r
      = ∑ s, ∑ s', if r s s' then siteSel σ s ⊗ₖ siteSel τ s' else 0 := by
  ext p q
  simp only [coincProj, Matrix.diagonal_apply, Matrix.sum_apply]
  by_cases hpq : p = q
  · subst hpq
    rw [Finset.sum_eq_single (σ p.1), Finset.sum_eq_single (τ p.2)]
    · simp only [↓reduceIte]
      split_ifs <;> simp [siteSel]
    · intro b _ hb
      split_ifs <;> simp [siteSel, Ne.symm hb]
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs <;> simp [siteSel, Ne.symm ha]
    · simp
  · simp only [hpq, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs
    · simp only [Matrix.kroneckerMap_apply, siteSel, Matrix.diagonal_apply]
      by_cases h1 : p.1 = q.1
      · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
        simp [h2]
      · simp [h1]
    · simp

/-- ★★ **On a product ray the coincidence projector reads the joint site occupancies**: the
sum over related pairs of sites of the product of the two carriers' occupancies. -/
theorem arenaObs_coincProj_prodRay (p : GenArena ι) (q : GenArena κ) :
    arenaObs (coincProj σ τ r) (prodRay p q)
      = ∑ s, ∑ s', if r s s' then arenaObs (siteSel σ s) p * arenaObs (siteSel τ s') q
          else 0 := by
  rw [coincProj_eq_sum, arenaObs_finset_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [arenaObs_finset_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs
  · exact arenaObs_kronecker (siteSel_isHermitian σ s) _ p q
  · exact arenaObs_zero' _

/-! ### The gated operator: a coincidence projector times an operator of the second carrier -/

/-- **A gated operator**: the coincidence projector times `1 ⊗ Y`, for an operator `Y` of the
second carrier. In UA-18 `Y` is a clock's level swap. -/
def gateOp (Y : Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  coincProj σ τ r * ((1 : Matrix ι ι ℂ) ⊗ₖ Y)

omit [Fintype S] [DecidableEq S] in
/-- ★ **The coincidence projector commutes with every operator of the second carrier that does
not move it between sites.** -/
theorem coincProj_mul_one_kronecker {Y : Matrix κ κ ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) :
    coincProj σ τ r * ((1 : Matrix ι ι ℂ) ⊗ₖ Y)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ Y) * coincProj σ τ r := by
  ext p q
  rw [coincProj, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases h1 : p.1 = q.1
  · by_cases h2 : τ p.2 = τ q.2
    · rw [h1, h2]
      ring
    · rw [hY _ _ h2]
      simp
  · simp [h1]

omit [Fintype S] [DecidableEq S] in
/-- The gated operator is Hermitian when `Y` is Hermitian and does not move the carrier
between sites. -/
theorem gateOp_isHermitian {Y : Matrix κ κ ℂ} (hYh : Y.IsHermitian)
    (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) : (gateOp σ τ r Y).IsHermitian := by
  have h1 : ((1 : Matrix ι ι ℂ) ⊗ₖ Y).IsHermitian :=
    kronecker_isHermitian Matrix.isHermitian_one hYh
  rw [gateOp, Matrix.IsHermitian, Matrix.conjTranspose_mul, h1.eq,
    (coincProj_isHermitian σ τ r).eq]
  exact (coincProj_mul_one_kronecker σ τ r hY).symm

/-- ★ **A gated operator is a sum of products**: a site projector of the first carrier times
the second carrier's operator restricted to a related site. -/
theorem gateOp_eq_sum (Y : Matrix κ κ ℂ) :
    gateOp σ τ r Y
      = ∑ s, ∑ s', if r s s' then siteSel σ s ⊗ₖ (siteSel τ s' * Y) else 0 := by
  rw [gateOp, coincProj_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs
  · rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  · rw [zero_mul]

/-- ★★ **On a product ray the gated operator reads, for each related pair of sites, the first
carrier's occupancy of its site times `arenaObs (siteSel τ s' * Y)` of the second carrier.**
That factor is the real part of the expectation of `P_{s'} Y`; it is the reading of an
observable when `Y` does not move the carrier between sites
(`coincProj_mul_one_kronecker`). -/
theorem arenaObs_gateOp_prodRay (Y : Matrix κ κ ℂ) (p : GenArena ι) (q : GenArena κ) :
    arenaObs (gateOp σ τ r Y) (prodRay p q)
      = ∑ s, ∑ s', if r s s'
          then arenaObs (siteSel σ s) p * arenaObs (siteSel τ s' * Y) q else 0 := by
  rw [gateOp_eq_sum, arenaObs_finset_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [arenaObs_finset_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs
  · exact arenaObs_kronecker (siteSel_isHermitian σ s) _ p q
  · exact arenaObs_zero' _

end Coincidence

end CSD.RecordLayer

end

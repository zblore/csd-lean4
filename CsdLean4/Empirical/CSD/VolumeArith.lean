/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Arithmetic the volume twins share

**Category:** 3-Local (programme-specific content; the `Empirical/CSD/` volume twins).
BACKLOG #146 cluster (A).

Each `Empirical/CSD/*Volume.lean` computes a typicality volume, and each had opened by re-proving
the same handful of one-line facts: that `√2² = 2`, that `‖z‖²` is `z.re² + z.im²`, that the inner
product against a basis vector picks out a coordinate. `check-duplicates` counted eight such groups
across six files. This module holds one copy of each.

The names and statements are unchanged, and they live in `CSD.Empirical.CSDBridge` — the namespace
each volume file's own namespace sits inside — so **no call site moved**: the lemmas resolve exactly
where they resolved before.

* `r2`, `r3`, `r6`, `r3_4` — squares and fourth powers of small square roots;
* `normSq_coord`, `realNormSq` — the two bridges from `‖·‖²` to real coordinates;
* `normSq_inner_single` — the coordinate read-off, **now at every dimension**;
* `inner_three` — the three-term inner product.

## One of them got better rather than just moved

`normSq_inner_single` existed three times: at `Fin 4` in `BellVolume`, proved by expanding the sum
with `Fin.sum_univ_four` and a `fin_cases` over the index, and at `Fin 4` in `HardyVolume` and
`Fin 8` in `GHZVolume`, both proved in two lines from `EuclideanSpace.inner_single_left`. That
second proof never used the dimension, so the version here is **generic in the index type**, which
is both shorter than Bell's and covers all three sites — including the `Fin 8` one the duplicate
scan could not group, since it compares statements and a `Fin 4` statement is not a `Fin 8` one.

⚠️ **There is a fourth copy, in `LF4/POVMVolume.lean`**, at the dilated index `Fin N × ι` and with
the same two-line proof. The scan's weaker signal (2) — same final name component, different
namespace — is what found it, and it is why the version here is index-generic rather than `Fin n`:
`LF4.normSq_inner_single` is now a one-line citation away from being deleted. Doing that deletion
is **not** part of this cluster, because `LF4` cannot import an `Empirical/` module and the lemma
would have to move to a Category-1 home first — which is exactly the shape of #146's cluster (D),
where it is recorded.

## Honest scope

⚠️ **Convenience specialisations, not library additions.** `r2` is `Real.sq_sqrt` at `2` and
`normSq_coord` is `Complex.sq_norm` composed with `Complex.normSq_apply`. They are here to be
written once, not because Mathlib lacks them, which is why this is Category 3 and not a staging
file.

⚠️ **`r2_4` and `imagNormSq` stayed where they were** (`SIC3Volume` and `GHZVolume`): each has one
home already, so moving them would be churn without removing a duplicate. They still resolve
against the `r2` and `realNormSq` here, through the enclosing namespace.

References: the six consumers `Empirical/CSD/{Bell,GHZ,Hardy,MUB3,SIC,SIC3}Volume.lean`;
`scripts/check-duplicates.sh`; `specs/BACKLOG.md` #146, ~~#145~~.
-/

@[expose] public section

namespace CSD
namespace Empirical
namespace CSDBridge

/-! ### Small square roots -/

lemma r2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma r3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
lemma r6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

lemma r3_4 : Real.sqrt 3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, r3]; norm_num

/-! ### From the norm to real coordinates -/

/-- `‖z‖² = z.re·z.re + z.im·z.im`, the bridge to real coordinates. -/
lemma normSq_coord (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]

/-- `‖↑r‖² = r²`. -/
lemma realNormSq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### Reading a coordinate off an inner product -/

/-- **The inner product against a basis vector is that coordinate**, over any index type. -/
lemma normSq_inner_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (i : ι) :
    ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 = ‖ψ.ofLp i‖ ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- The three-term inner product, written out. -/
lemma inner_three (x y : EuclideanSpace ℂ (Fin 3)) :
    inner ℂ x y = star (x.ofLp 0) * y.ofLp 0 + star (x.ofLp 1) * y.ofLp 1
      + star (x.ofLp 2) * y.ofLp 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  simp only [Pi.star_apply]; ring

end CSDBridge
end Empirical
end CSD

end

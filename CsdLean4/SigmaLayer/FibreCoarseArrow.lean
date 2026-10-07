/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.InformationTheory.CoarseGrainArrow
public import CsdLean4.SigmaLayer.MovingFibreWitness
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The coarse-grained arrow on the fibre

**Category:** 7-SigmaLayer.
BACKLOG #18 / `R-019`, brick (b) — the fibre instance of `CoarseGrainArrow.lean`.

`R-019` asks for a relaxation H-theorem on the fibre: *for a partition into cells of size `δ`, the
coarse-grained relative entropy with respect to Haar decreases, and the distribution approaches
Haar.* It has stood open as research-grade, blocked on first-passage asymptotics for small sets.

This file settles the **first clause** and, in doing so, says exactly where the difficulty is not.

* `circCell`/`torusCell`/`fibreCell` — the fibre cut into `(m+1)²` cells, measurable through
  `AddCircle.measurableEquivIoc`;
* ★★★ `antitone_klDiv_fibreCell_stroke` — **the coarse-grained relative entropy from the Haar cell
  law is non-increasing along the hyperbolic stroke**, monotonically in the number of steps;
* ★★★ `antitone_klDiv_fibreCell_kFlow` — **and along the translation too.**

## What the second capstone is for

The pair is the point. `relaxation_requires_hyperbolic_fibre` (this file's import) proves that on one
and the same fibre the translation `kFlow` admits **no** summable decay envelope while the hyperbolic
`catStroke` has a finitely supported one — the corpus's reason for saying relaxation needs a
hyperbolic fibre map. Yet both maps satisfy the H-theorem's monotonicity clause, and by the same
one-line instantiation.

So the monotone decrease is **not** the content of relaxation and cannot distinguish a fibre that
relaxes from one that does not: it holds for any measure-preserving map and any finite measurable
partition, cell geometry included. `R-019`'s difficulty is located entirely in its second clause —
that the divergence tends to `0`, at a rate set by the cell size — and that is where first-passage
asymptotics are needed. The split is now visible rather than inferred.

## Honest scope

⚠️ **No convergence.** Nothing here says the divergence tends to `0`, for either map, and the
relaxation that would need it is open (`RESIDUE(R-019)`). ⚠️ **No rate**,
and nothing about `δ`: the cells are indexed by `m` and `m` appears in no bound. ⚠️ **Not a
relaxation theorem**, and in particular not a Track B prediction — a prediction differing from
quantum mechanics needs a fibre that is demonstrably *out of* equilibrium and returns to it, which is
the open half. ⚠️ **The arrow is for the induced macro chain**, not for coarse-graining the fine
orbit; see `CoarseGrainArrow.lean`'s header for why no theorem could give the latter.

References: [`CoarseGrainArrow.lean`](../Mathlib/InformationTheory/CoarseGrainArrow.lean) (#18 brick
(a)), [`MovingFibreWitness.lean`](MovingFibreWitness.lean)
(`relaxation_requires_hyperbolic_fibre`, `catStroke`), [`LF4/KahlerFlow.lean`](../LF4/KahlerFlow.lean)
(`kFlow`, `kFlow_measurePreserving`), `RecordLayer/MacrostateArrow.lean` (#109);
`specs/BACKLOG.md` #18, #109; `specs/residues.tsv` `R-019`; `specs/cr-queue.md` CR-14.
-/

@[expose] public section

open MeasureTheory InformationTheory Set

namespace CSD.SigmaLayer

open LF4

/-! ### A finite cell decomposition of the fibre -/

/-- The representative of a circle point in `(0, 1]`. -/
noncomputable def circRep (x : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.measurableEquivIoc (1 : ℝ) 0 x : ℝ)

theorem measurable_circRep : Measurable circRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable

/-- The unclamped index of the cell of width `1/(m+1)` containing `x`. -/
noncomputable def circIdx (m : ℕ) (x : AddCircle (1 : ℝ)) : ℕ :=
  ⌊((m : ℝ) + 1) * circRep x⌋₊

theorem measurable_circIdx (m : ℕ) : Measurable (circIdx m) :=
  Measurable.comp (Nat.measurable_floor : Measurable (Nat.floor : ℝ → ℕ))
    (measurable_const.mul measurable_circRep)

/-- The cell of the circle containing `x`, out of `m + 1` cells of equal width. -/
noncomputable def circCell (m : ℕ) (x : AddCircle (1 : ℝ)) : Fin (m + 1) :=
  ⟨min m (circIdx m x), by omega⟩

theorem measurable_circCell (m : ℕ) : Measurable (circCell m) :=
  (Measurable.of_discrete (f := fun k : ℕ => (⟨min m k, by omega⟩ : Fin (m + 1)))).comp
    (measurable_circIdx m)

/-- The cell of the `T²` fibre containing `y`, out of `(m + 1)²`. -/
noncomputable def torusCell (m : ℕ) (y : KTorus) : Fin (m + 1) × Fin (m + 1) :=
  (circCell m y.1, circCell m y.2)

theorem measurable_torusCell (m : ℕ) : Measurable (torusCell m) :=
  ((measurable_circCell m).comp measurable_fst).prodMk
    ((measurable_circCell m).comp measurable_snd)

/-- The fibre cell of a point of `Σ`: the coarse-graining `R-019` is stated for. -/
noncomputable def fibreCell {N : ℕ} (m : ℕ) (p : KSigma N) : Fin (m + 1) × Fin (m + 1) :=
  torusCell m p.2

theorem measurable_fibreCell {N : ℕ} (m : ℕ) : Measurable (fibreCell (N := N) m) :=
  (measurable_torusCell m).comp measurable_snd

/-! ### The hyperbolic stroke as a dynamics on `Σ` -/

/-- The hyperbolic fibre stroke, acting on `Σ` with the base fixed. -/
noncomputable def fibreStroke {N : ℕ} : KSigma N → KSigma N := Prod.map id catStroke

theorem fibreStroke_measurePreserving {N : ℕ} (p₀ : CPN N) :
    MeasurePreserving (fibreStroke (N := N)) (kMuL p₀) (kMuL p₀) := by
  rw [kMuL]
  exact (MeasurePreserving.id _).prod catStroke_measurePreserving

/-! ### The arrow, for both fibre maps -/

/-- ★★★ **The coarse-grained H-theorem on the fibre, for the hyperbolic stroke.** Along the macro
dynamics the stroke induces on the fibre cells, every cell law's relative entropy from the Haar cell
law is non-increasing, monotonically in the number of steps.

This is `R-019`'s first clause. It is *not* its second: see the header. -/
theorem antitone_klDiv_fibreCell_stroke {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (μ : Measure (Fin (m + 1) × Fin (m + 1))) [IsProbabilityMeasure μ] :
    Antitone fun n : ℕ =>
      klDiv (μ.compIterate (coarseKernel (kMuL p₀) (fibreCell m) fibreStroke) n)
        (coarseLaw (kMuL p₀) (fibreCell (N := N) m)) :=
  antitone_klDiv_coarseLaw _ (measurable_fibreCell m) (fibreStroke_measurePreserving p₀) μ

/-- ★★★ **And along the translation, which cannot relax.** `relaxation_requires_hyperbolic_fibre`
proves `kFlow` admits no summable decay envelope on this very fibre, yet its induced macro dynamics
satisfies the same monotonicity by the same instantiation.

So monotone decrease does not distinguish a relaxing fibre from a non-relaxing one, and `R-019`'s
content is entirely in the convergence it does not give. -/
theorem antitone_klDiv_fibreCell_kFlow {N : ℕ} (p₀ : CPN N) (sh : KTorus) (m : ℕ)
    (μ : Measure (Fin (m + 1) × Fin (m + 1))) [IsProbabilityMeasure μ] :
    Antitone fun n : ℕ =>
      klDiv (μ.compIterate (coarseKernel (kMuL p₀) (fibreCell m) (kFlow sh)) n)
        (coarseLaw (kMuL p₀) (fibreCell (N := N) m)) :=
  antitone_klDiv_coarseLaw _ (measurable_fibreCell m) (kFlow_measurePreserving p₀ sh) μ

end CSD.SigmaLayer

end

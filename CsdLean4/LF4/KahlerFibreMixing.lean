/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.KahlerFlowNoMixing
public import CsdLean4.Mathlib.Dynamics.Kac
public import Mathlib.Dynamics.Ergodic.AddCircle

/-!
# The fibre torus does admit a mixing map — the wall is about the map, not about Σ

**Category:** 3-CSD. `Q12-d` brick (i).

⚠️ **The race route this brick served was RETIRED 2026-08-24, and the brick outlived it.** `Q12-d`
— derive the race from a deterministic flow — was withdrawn as **mis-specified**, not as blocked,
for three reasons none of which is effort: *regime mismatch* (Galves–Schmitt/Abadi is about rare
sets, `μA → 0`, while a Born partition's cells sum to 1); *exact vs asymptotic* (Q12-c2 gives exact
Born ⟺ exactly exponential, so a limit theorem yields Born only asymptotically — strictly weaker
than `measure_raceCell`, which already proves it exactly); and *independence* (the race needs `n`
independent clocks, but one deterministic trajectory is one process). See `specs/BACKLOG.md` (Q12)
and `specs/q12-fibre-mechanism-scoping.md`.

**What survives here is the corrective, and it is the whole point of the module:** the wall is about
the *map*, not about Σ. That reading is independent of the race framing and is why this module is
not retired with it. The successor question was executed in honest form 2026-08-27
(`RecordLayer/ShearDeIsolation.lean`); the surviving open item is Posit 1's discharge condition
(`specs/POSITS.md`).

`W1` and its finite-horizon companion say no flow the corpus *defines* can decorrelate. It is easy
to read that as "Σ cannot mix", and that reading is **wrong**. ★★
`torusDouble_hasCorrelationDecay` exhibits a map of the corpus's own fibre `T²` whose correlations
are **exactly zero at every nonzero lag** — the strongest possible decay, with a finitely supported
envelope.

## Why this escapes `W1`, precisely

`not_hasCorrelationDecay_of_compactGroup` rules out flows `Ψ U` whose iterates are the **powers of
an element of a compact group**. `kFlow` is such a flow: it translates the torus, and translations
are the compact group `T²` acting on itself, so Dirichlet-style recurrence applies and the
correlations must come back.

`torusDouble` is the **doubling endomorphism** `y ↦ 2y`, not a translation. Its iterates are
`y ↦ 2ⁿ y`, powers in the multiplicative monoid `ℕ` — *discrete and non-compact*. There is no
compact group for the recurrence lemma to bite on, and in fact the correlations do not merely fail
to recur: they vanish outright.

**So the obstruction `W1` records is a fact about the class of maps the corpus chose, not about the
ontic space.** Σ is unchanged here: `KTorus` is the fibre the Kähler instance already has.

## ⚠️ What this does and does not settle

* It does **not** replace `kFlow`. `kFlow` is the *phase* translation — free evolution — and it is
  correct that a phase translates. `torusDouble` is a candidate for the **de-isolation** map, which
  is what `Q12-d` asks for and which the corpus does not otherwise have.
* ⚠️ `torusDouble` is **not invertible**. That is a real limitation: a symplectic/Hamiltonian
  Σ-flow would be, so this is a witness that the *mixing* half of `Q12-d` is satisfiable on `T²`,
  not yet a physically admissible de-isolation dynamics. The invertible case is a **hyperbolic
  toral automorphism** (`[[2,1],[1,1]]`, the cat map): the character argument is the same shape, and
  the extra cost is Haar-invariance of a toral automorphism, which Mathlib does not provide.
* ⚠️ **Mixing is not the race.** Even with a mixing fibre map, `Q12-d` needs first-passage times to
  be *exponential at moment-map rates*. That link — hitting times of small sets in mixing systems
  are asymptotically exponential — is Galves–Schmitt/Abadi, rated research-grade and not upstream in
  `W2`. **That, not Σ's vocabulary, is what actually blocks `Q12-d`.**

## The proof is free

`torusObs` reads only the first angle and `torusDouble` acts coordinatewise, so every correlation
collapses to the corresponding one-dimensional integral and E5's witness
(`MeasureTheory.circ_hasCorrelationDecay`) supplies the answer. The second factor integrates out
through `Measure.map_fst_prod`. Nothing about the doubling map is re-proved.

Reference: `specs/q12-fibre-mechanism-scoping.md` (`Q12-d`, `W1`, `W2`);
`specs/equilibration-arc-plan.md` (E5, the witness reused here); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD
namespace LF4

/-- **The doubling endomorphism of the fibre torus**, `y ↦ 2y` in both angles.

A toral endomorphism, not a translation — which is exactly why `W1` does not reach it. -/
noncomputable def torusDouble : KTorus → KTorus :=
  Prod.map MeasureTheory.doubling MeasureTheory.doubling

/-- The fibre observable on the torus: `cos 2π` of the first angle. Same function as `fibreObs`,
read on the fibre alone rather than on all of `Σ`. -/
noncomputable def torusObs (y : KTorus) : ℝ := MeasureTheory.circObs y.1

@[simp] lemma torusObs_apply (y : KTorus) : torusObs y = MeasureTheory.circObs y.1 := rfl

lemma torusDouble_iterate (u : ℕ) (y : KTorus) :
    torusDouble^[u] y
      = (MeasureTheory.doubling^[u] y.1, MeasureTheory.doubling^[u] y.2) := by
  induction u generalizing y with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih]; rfl

/-- The observable along the doubling orbit. Not `@[simp]`: `torusObs_apply` rewrites the head
first, so this composite could never fire (`simpNF`); it is a `rw`/`simp only` lemma. -/
lemma torusObs_torusDouble_iterate (u : ℕ) (y : KTorus) :
    torusObs (torusDouble^[u] y) = MeasureTheory.circObs (MeasureTheory.doubling^[u] y.1) := by
  rw [torusObs_apply, torusDouble_iterate]

/-! ### The second angle integrates out -/

lemma map_fst_torus :
    (volume : Measure KTorus).map Prod.fst = (volume : Measure MeasureTheory.Circ) := by
  rw [Measure.volume_eq_prod, Measure.map_fst_prod, measure_univ, one_smul]

/-- Integrals of functions of the first angle collapse to the circle. -/
lemma integral_torus_fst {F : MeasureTheory.Circ → ℝ} (hF : Measurable F)
    (hbd : ∀ z, |F z| ≤ 1) :
    ∫ y, F y.1 ∂(volume : Measure KTorus)
      = ∫ x, F x ∂(volume : Measure MeasureTheory.Circ) := by
  have hint : Integrable F (volume : Measure MeasureTheory.Circ) :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hbd z))
  rw [← map_fst_torus, integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable]

lemma integral_torusObs_pair (s t : ℕ) :
    ∫ y, torusObs (torusDouble^[s] y) * torusObs (torusDouble^[t] y) ∂(volume : Measure KTorus)
      = ∫ x, MeasureTheory.circObs (MeasureTheory.doubling^[s] x)
          * MeasureTheory.circObs (MeasureTheory.doubling^[t] x)
          ∂(volume : Measure MeasureTheory.Circ) := by
  have hm : Measurable (fun x : MeasureTheory.Circ =>
      MeasureTheory.circObs (MeasureTheory.doubling^[s] x)
        * MeasureTheory.circObs (MeasureTheory.doubling^[t] x)) :=
    (MeasureTheory.measurable_circObs.comp (MeasureTheory.measurable_doubling.iterate s)).mul
      (MeasureTheory.measurable_circObs.comp (MeasureTheory.measurable_doubling.iterate t))
  have hbd : ∀ x : MeasureTheory.Circ,
      |MeasureTheory.circObs (MeasureTheory.doubling^[s] x)
        * MeasureTheory.circObs (MeasureTheory.doubling^[t] x)| ≤ 1 := by
    intro x
    rw [abs_mul]
    exact mul_le_one₀ (MeasureTheory.abs_circObs_le_one _) (abs_nonneg _)
      (MeasureTheory.abs_circObs_le_one _)
  simp only [torusObs_torusDouble_iterate]
  exact integral_torus_fst hm hbd

lemma integral_torusObs : ∫ y, torusObs y ∂(volume : Measure KTorus) = 0 := by
  simp only [torusObs_apply]
  rw [integral_torus_fst MeasureTheory.measurable_circObs MeasureTheory.abs_circObs_le_one,
    MeasureTheory.integral_circObs]

/-! ### The witness -/

/-- ★★ **The corpus's fibre torus carries a map whose correlations vanish exactly.**

`torusDouble` has `MeasureTheory.circEnv` as a decay envelope — `1` at lag zero and `0` at every
other lag. That is not merely decay, it is exact decorrelation at every nonzero lag.

Read against `not_hasCorrelationDecay_kFlow`: the *same fibre*, the *same observable*, opposite
verdicts. The difference is entirely that `kFlow` translates and `torusDouble` does not, which is
precisely the hypothesis `not_hasCorrelationDecay_of_compactGroup` needs and `torusDouble` fails to
meet. **`W1` constrains the choice of map, not the ontic space.** -/
theorem torusDouble_hasCorrelationDecay :
    MeasureTheory.HasCorrelationDecay (volume : Measure KTorus) torusDouble torusObs
      MeasureTheory.circEnv := by
  intro s t
  rw [integral_torusObs_pair s t, integral_torusObs]
  have h := MeasureTheory.circ_hasCorrelationDecay s t
  rwa [MeasureTheory.integral_circObs] at h

/-- The envelope is summable, so the witness meets the hypothesis E4's engine actually takes. -/
theorem torusDouble_summable : Summable MeasureTheory.circEnv :=
  MeasureTheory.circ_summable

/-- **Non-trivial**: the observable is not almost everywhere constant, so this is a genuine witness
rather than the degenerate case that `HasCorrelationDecay.integral_mul_self_eq_of_recurrent` forces
on every compact-group flow. -/
theorem torusObs_variance_ne :
    ∫ y, torusObs y * torusObs y ∂(volume : Measure KTorus)
      ≠ (∫ z, torusObs z ∂(volume : Measure KTorus)) ^ 2 := by
  have hm : Measurable (fun x : MeasureTheory.Circ =>
      MeasureTheory.circObs x * MeasureTheory.circObs x) :=
    MeasureTheory.measurable_circObs.mul MeasureTheory.measurable_circObs
  have hbd : ∀ x : MeasureTheory.Circ,
      |MeasureTheory.circObs x * MeasureTheory.circObs x| ≤ 1 := by
    intro x
    rw [abs_mul]
    exact mul_le_one₀ (MeasureTheory.abs_circObs_le_one x) (abs_nonneg _)
      (MeasureTheory.abs_circObs_le_one x)
  have hsq : ∫ y, torusObs y * torusObs y ∂(volume : Measure KTorus) = 1 / 2 := by
    simp only [torusObs_apply]
    rw [integral_torus_fst hm hbd, MeasureTheory.integral_circObs_sq]
  rw [hsq, integral_torusObs]
  norm_num

/-! ### Kac on the same map -/

/-- ★★ **Kac's formula on the mixing fibre map**, which is also the non-vacuity check for
`MeasureTheory.tsum_measure_lt_returnTime`: its hypotheses (ergodic, measure-preserving, positive
measure) are satisfiable, and satisfied by the very map brick (i) exhibits.

The content: a fibre cell of measure `b` is returned to on average every `1/b` steps. **That is the
rate content of the record layer's race, derived from the dynamics rather than posited** — and it is
regime-correct, holding for any cell of positive measure rather than only for rare ones.

⚠️ It gives the **rates**, not the exponential **law**. See the `Q12-d` row. -/
theorem kac_doubling {A : Set MeasureTheory.Circ} (hA : MeasurableSet A)
    (hApos : volume A ≠ 0) :
    ∑' n : ℕ,
        volume (A ∩ {x | (n : ℕ∞) < MeasureTheory.returnTime MeasureTheory.doubling A x}) = 1 := by
  have herg : Ergodic (fun y : MeasureTheory.Circ => (2 : ℕ) • y) :=
    AddCircle.ergodic_nsmul (T := 1) (n := 2) (by norm_num)
  exact MeasureTheory.tsum_measure_lt_returnTime herg.toMeasurePreserving
    herg.toPreErgodic hA hApos MeasureTheory.measurable_doubling

end LF4
end CSD

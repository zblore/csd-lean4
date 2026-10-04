/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerConcentration

/-!
# Dephasing cannot concentrate the Born weights — and what is true instead

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #106, out of #105.

#105(a) proved that nearness to a pointer ray buys an overwhelming *and* robust record macrostate, and
#106 was opened to find the dynamics that **produces** that nearness. Two routes were recorded. Route
(1) was "an explicit dephasing estimate", an inequality

    1 − momentMap (Φ t p) i ≤ e^{−λt} · (1 − momentMap p i).

**That route is closed negatively here.** Dephasing acts on a pure preparation by a phase per branch —
that is what destroys interference — and a phase changes no amplitude's **modulus**. Since a record
weight is a modulus squared and nothing else, every record weight is a **fixed point** of it: there is
no contraction, at any rate, for any time.

So the premise behind "overwhelmingly many microstates share the record" has to be *corrected*, not
supplied. The correct replacement is the second half of this file, and it needs **no concentration
hypothesis at all**.

## What is proved

* ★★★ `momentMap_eq_of_norm_coord_eq` — **a record weight depends only on the coordinate moduli.** Two
  unit preparations with the same `‖ψ i‖` have the same moment coordinates, hence
  ★★ `globalBasin_prob_eq_of_norm_coord_eq`: **no basin's probability changes**, outcome by outcome.
  Dephasing is exactly a modulus-preserving map, so this is stated at the level where it does the work
  and covers every such map at once, not only coordinatewise phases;
* ★★★ `not_concentrates_of_norm_coord_eq` — **route (1) of #106 is impossible**: for a preparation
  whose weight at `i` is not already `1`, no modulus-preserving dynamics satisfies a contraction
  `1 − momentMap(evolved) i ≤ q · (1 − momentMap p i)` with `q < 1`. The defect is a fixed point, so no
  rate and no time can shrink it. The route is not unfinished — it is the wrong mechanism;
* ★★★ `one_sub_le_robust_fraction` — **the correct replacement, with no concentration hypothesis**:
  *within the cell of outcome `i`*, the fraction of microstates robust to a record write of size `δ` is
  at least `1 − δ / rate p i`. So "overwhelmingly many microstates share the record" is true of
  **every** outcome once it is read as a statement about that outcome's own cell, and what it needs is
  `δ` small compared with the weight — not a dominant weight;
* ★★ `robust_fraction_tendsto_one` — and that fraction tends to `1` as the write shrinks, for every
  outcome of positive weight.

## Honest scope

⚠️ **The no-go is about modulus-preserving dynamics.** What is refuted is route (1) for the dynamics
that dephasing *is*. A map that genuinely reweights the amplitudes — amplitude damping, or a
measurement with feedback — is **not** covered and is not refuted. The physical reading is the point:
such a map is a *re-preparation*, not a decoherence, so it cannot be what makes an existing
superposition's record macroscopic.

⚠️ **This does not withdraw #105(a).** That theorem stands exactly as stated: *given* `1 − ε ≤ rate p i`
the cell is overwhelming and robust. What is corrected is the expectation that a decoherence model
would supply its hypothesis.

⚠️ **The replacement is conditional on the outcome, deliberately.** `one_sub_le_robust_fraction`
divides by `rate p i`: the realised cell is mostly robust; **no cell is claimed large**. For a genuine
superposition none is, the Born weights stay spread, and nothing here pretends otherwise — that is
correct physics, not a gap.

⚠️ **Route (2) is untouched.** Connecting the shear de-isolation pointer of
[`ShearDeIsolation.lean`](ShearDeIsolation.lean) to the record layer is not attempted; it is BACKLOG
#107 and still inherits the de-isolation obligation of [`DeIsolationFlow.lean`](DeIsolationFlow.lean).

⚠️ **No dynamics is constructed at all.** The no-go quantifies over preparations with equal moduli; it
exhibits no flow, no generator, no environment and no time parameter. That is what makes it general,
and correspondingly it is not a statement about any particular physical model.

⚠️ **The canonical context only.** As in #105, `momentContext` is the standard-basis context, so
"record weight" means a moment coordinate; no general apparatus is treated.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
[`future-work.md`](../../specs/future-work.md); `PointerConcentration.lean` (#105(a)),
`MacrostateStability.lean` (#103), `GlobalBasin.lean`, `LF4/MomentMap.lean`;
`specs/BACKLOG.md` #106, #107, #105, #103.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### A record weight sees only the moduli -/

/-- ★★★ **A record weight depends only on the coordinate moduli.** Two unit preparations whose
amplitudes have the same moduli have the same moment coordinates. Dephasing is exactly such a map — a
phase per branch — so this is the no-go's engine, stated for every modulus-preserving map at once. -/
theorem momentMap_eq_of_norm_coord_eq {ψ φ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0) (hφ0 : φ ≠ 0)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (h : ∀ i, ‖φ i‖ = ‖ψ i‖) (i : Fin N) :
    LF4.momentMap (Projectivization.mk ℂ φ hφ0) i
      = LF4.momentMap (Projectivization.mk ℂ ψ hψ0) i := by
  rw [momentMap_mk_eq_coord_sq φ hφ0 hφ i, momentMap_mk_eq_coord_sq ψ hψ0 hψ i, h i]

/-- ★★ **So no basin's probability changes.** The canonical context's record weights are untouched,
outcome by outcome. -/
theorem globalBasin_prob_eq_of_norm_coord_eq {ψ φ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0)
    (hφ0 : φ ≠ 0) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (h : ∀ i, ‖φ i‖ = ‖ψ i‖) (i : Fin N) :
    epistemicMeasure (Projectivization.mk ℂ φ hφ0) (globalBasin (momentContext N) i)
      = epistemicMeasure (Projectivization.mk ℂ ψ hψ0) (globalBasin (momentContext N) i) := by
  rw [globalBasin_prob, globalBasin_prob, momentContext_rate, momentContext_rate,
    momentMap_eq_of_norm_coord_eq hψ0 hφ0 hψ hφ h i]

/-- ★★★ **Route (1) of #106 is impossible.** The row asked for a dephasing estimate contracting the
defect `1 − momentMap p i`. That defect is a **fixed point** of every modulus-preserving map, so no
contraction factor `q < 1` is available at any rate or any time, unless the weight was already `1`.

The route is therefore not unfinished but misconceived: dephasing destroys interference, and leaves the
Born weights exactly where they were. -/
theorem not_concentrates_of_norm_coord_eq {ψ φ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0)
    (hφ0 : φ ≠ 0) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (h : ∀ i, ‖φ i‖ = ‖ψ i‖) (i : Fin N)
    (hne : LF4.momentMap (Projectivization.mk ℂ ψ hψ0) i ≠ 1) {q : ℝ} (hq : q < 1) :
    ¬ (1 - LF4.momentMap (Projectivization.mk ℂ φ hφ0) i
        ≤ q * (1 - LF4.momentMap (Projectivization.mk ℂ ψ hψ0) i)) := by
  rw [momentMap_eq_of_norm_coord_eq hψ0 hφ0 hψ hφ h i]
  intro hle
  have hpos : 0 < 1 - LF4.momentMap (Projectivization.mk ℂ ψ hψ0) i := by
    have hle1 := LF4.momentMap_le_one (Projectivization.mk ℂ ψ hψ0) i
    rcases lt_or_eq_of_le hle1 with hlt | heq
    · linarith
    · exact absurd heq hne
  nlinarith

/-! ### What is true instead: the realised cell is mostly robust -/

/-- ★★★ **The correct replacement, with no concentration hypothesis.** Within the cell of outcome `i`,
the fraction of microstates robust to a record write of size `δ` is at least `1 − δ / rate p i`. So
"overwhelmingly many microstates share the record" holds for **every** outcome once it is read as a
statement about that outcome's own cell — and what it needs is `δ` small compared with the weight, not
a dominant weight. -/
theorem one_sub_le_robust_fraction (c : ContextField N) {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin N)
    (p : LF4.CPN N) (hrate : 0 < c.rate p i) :
    1 - δ / c.rate p i
      ≤ (epistemicMeasure p (robustBasin c δ i)).toReal / c.rate p i := by
  have hr0 : c.rate p i ≠ 0 := ne_of_gt hrate
  have htop : epistemicMeasure p (robustBasin c δ i) ≠ ⊤ := measure_ne_top _ _
  have hreal : c.rate p i - δ ≤ (epistemicMeasure p (robustBasin c δ i)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal htop).1 (measure_robustBasin_ge c hδ i p)
  calc 1 - δ / c.rate p i = (c.rate p i - δ) / c.rate p i := by field_simp
    _ ≤ (epistemicMeasure p (robustBasin c δ i)).toReal / c.rate p i := by gcongr

/-- ★★ **And the robust fraction tends to `1` as the write shrinks**, for every outcome of positive
weight — the honest form of "the record macrostate is stable", with no appeal to a dominant Born
weight. -/
theorem robust_fraction_tendsto_one (c : ContextField N) (i : Fin N) (p : LF4.CPN N) :
    Filter.Tendsto (fun δ : ℝ => 1 - δ / c.rate p i) (nhdsWithin 0 (Ici (0 : ℝ))) (nhds 1) := by
  have hid : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Ici (0 : ℝ))) (nhds 0) :=
    nhdsWithin_le_nhds
  have h : Filter.Tendsto (fun δ : ℝ => δ / c.rate p i) (nhdsWithin 0 (Ici (0 : ℝ))) (nhds 0) := by
    simpa using hid.div_const (c.rate p i)
  simpa using h.const_sub (1 : ℝ)

end CSD.RecordLayer

end

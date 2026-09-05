/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SwapLuders
public import CsdLean4.RecordLayer.DegenerateLuders

/-!
# RecordLayer/NStepChain: the measurement chain to arbitrary depth

**Category:** 7-SigmaLayer (the record layer).

The corpus proves one step (`globalBasin_prob`, `csd_sequential_born`) and two steps
(`two_stage_joint`). The programme's account of measurement is the chain to *arbitrary* depth, and
until now that was an argument rather than a theorem. This module makes it a theorem, at the level
where the argument actually lives: the sequence of record-layer states.

## The content, which is self-similarity

After a record `i`, the state is the vertex `vertexPoint i` — that is the collapse, and it is what
makes the chain repeat. So the state entering step `k+1` is a function of the previous record alone,
never of the preparation or of the earlier records:

* `chainState` — `chainState p i 0 = p`, and `chainState p i (k+1) = vertexPoint (i k)`.
* ★ `chainState_succ` — the reset, as a lemma rather than an unfolding.

The chain law is then a product of per-step rates read at those states:

* ★★ `csd_nstep_born` — for every depth `n`, every sequence of context fields and every sequence of
  outcomes, the product of the per-step basin measures equals `ENNReal.ofReal` of the product of the
  per-step rates. Induction on `n`; the step is `globalBasin_prob` at `chainState`.
* ★ `csd_nstep_born_succ` — the recursion in the form the programme states it: depth `n+1` is the
  first rate times the depth-`n` chain *at the collapsed vertex*.
* ★ `csd_twostep_born` — the `n = 2` instance, so the general theorem is visibly the two-step law
  the corpus already had.
* ★ `csd_nstep_repeatable` — non-vacuity with teeth: measuring the same basis repeatedly reproduces
  the first outcome with probability one at every depth, because the vertex rate is an indicator.

## ⚠️ What the bank family is doing, and what this does not claim

**One measurement consumes one bank**, so a depth-`n` chain is an `n`-bank construction and the
posit is renewed at each step (`specs/POSITS.md` Posit 5; the external review's Posit 2). That
renewal is exactly what `chainState` encodes: each step is prepared afresh at
`epistemicMeasure (chainState …)`, with a fresh register and a fresh bank. The theorem is
*conditional on the bank family* in that sense, and the hypothesis is visible in the statement as
the per-step `epistemicMeasure` rather than hidden in a structure field.

⚠️ **This is the chain at the level of record-layer states, not a single-arena factorisation.**
`two_stage_joint` (`RecordLayer/TwoTimeLuders.lean`) does something different and harder for `n = 2`:
it factors the joint probability *inside one two-stage arena*, with the stage-2 apparatus explicitly
adjoined. Generalising that construction to an `n`-stage arena is a separate and larger piece of
work, and it is **not** done here. What is proved here is the law the chain obeys once each step is
granted its own bank; what is not proved is that an `n`-stage arena assembles to give it.

## References

`RecordLayer/GlobalBasin.lean` (`epistemicMeasure`, `globalBasin`, `globalBasin_prob`,
`ContextField`); `RecordLayer/SwapLuders.lean` (`vertexPoint`, `momentMap_vertex`);
`RecordLayer/TwoTimeLuders.lean` (`two_stage_joint`, the single-arena two-stage factorisation);
`Empirical/CSD/SequentialMeasurement.lean` (`csd_sequential_born`, `csd_repeatability`);
`specs/POSITS.md` (Posit 5, the calibrated bank); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD
namespace RecordLayer

open LF4

variable {N : ℕ}

/-- The state entering step `k` of the chain: the preparation at step `0`, and thereafter the
vertex named by the previous record. This is the collapse, written as data. -/
noncomputable def chainState (p : CPN N) (i : ℕ → Fin N) : ℕ → CPN N
  | 0 => p
  | k + 1 => vertexPoint (i k)

@[simp] lemma chainState_zero (p : CPN N) (i : ℕ → Fin N) : chainState p i 0 = p := rfl

/-- ★ **The reset.** The state entering step `k+1` depends on the previous record *alone* — not on
the preparation, and not on the records before it. This is why the chain repeats. -/
@[simp] lemma chainState_succ (p : CPN N) (i : ℕ → Fin N) (k : ℕ) :
    chainState p i (k + 1) = vertexPoint (i k) := rfl

/-- ★ **The tail of a chain is a chain.** Re-rooting at the first record's vertex and shifting the
outcome sequence reproduces the original states from step one on. This is `chainState_succ` in the
form the induction needs, where the equation sits under a binder and `rfl` will not reach it. -/
lemma chainState_shift (p : CPN N) (i : ℕ → Fin N) (k : ℕ) :
    chainState (vertexPoint (i 0)) (fun m => i (m + 1)) k = chainState p i (k + 1) := by
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The chain rate to depth `n`: the product of the per-step rates, each read at the state that
step actually sees. -/
noncomputable def chainRate (p : CPN N) (c : ℕ → ContextField N) (i : ℕ → Fin N) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (c k).rate (chainState p i k) (i k)

@[simp] lemma chainRate_zero (p : CPN N) (c : ℕ → ContextField N) (i : ℕ → Fin N) :
    chainRate p c i 0 = 1 := by
  simp [chainRate]

lemma chainRate_nonneg (p : CPN N) (c : ℕ → ContextField N) (i : ℕ → Fin N) (n : ℕ) :
    0 ≤ chainRate p c i n :=
  Finset.prod_nonneg fun k _ => (c k).nonneg _ _

/-- ★★ **The measurement chain to arbitrary depth.** For every depth, every sequence of context
fields and every sequence of outcomes, the product of the per-step basin measures is the product of
the per-step rates.

Each factor is `globalBasin_prob` at the state that step sees, and the states are given by
`chainState`: the preparation first, the collapsed vertex thereafter. The bank family enters as the
per-step `epistemicMeasure` — one measurement, one bank (`specs/POSITS.md` Posit 5). -/
theorem csd_nstep_born (p : CPN N) (c : ℕ → ContextField N) (i : ℕ → Fin N) (n : ℕ) :
    (∏ k ∈ Finset.range n,
        epistemicMeasure (chainState p i k) (globalBasin (c k) (i k)))
      = ENNReal.ofReal (chainRate p c i n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, globalBasin_prob,
        ← ENNReal.ofReal_mul (chainRate_nonneg p c i n)]
      congr 1
      simp [chainRate, Finset.prod_range_succ]

/-- ★ **The recursion, in the form the programme states it.** A depth-`n+1` chain is the first
step's rate times a depth-`n` chain *at the collapsed vertex*: the tail of a chain is a chain. -/
theorem csd_nstep_born_succ (p : CPN N) (c : ℕ → ContextField N) (i : ℕ → Fin N) (n : ℕ) :
    chainRate p c i (n + 1)
      = (c 0).rate p (i 0)
        * chainRate (vertexPoint (i 0)) (fun k => c (k + 1)) (fun k => i (k + 1)) n := by
  rw [chainRate, Finset.prod_range_succ', mul_comm, chainState_zero]
  congr 1
  rw [chainRate]
  exact (Finset.prod_congr rfl fun k _ => by rw [chainState_shift]).symm

/-- ★ **The two-step instance.** The general theorem specialised to `n = 2`, so it is visible that
the depth-`n` law is the two-step law the corpus already had, extended rather than replaced.
⚠️ This is the state-level statement; `two_stage_joint` proves the harder single-arena
factorisation for two steps. -/
theorem csd_twostep_born (p : CPN N) (c : ℕ → ContextField N) (i : ℕ → Fin N) :
    epistemicMeasure p (globalBasin (c 0) (i 0))
        * epistemicMeasure (vertexPoint (i 0)) (globalBasin (c 1) (i 1))
      = ENNReal.ofReal ((c 0).rate p (i 0) * (c 1).rate (vertexPoint (i 0)) (i 1)) := by
  have h := csd_nstep_born p c i 2
  rw [Finset.prod_range_succ, Finset.prod_range_one] at h
  simpa [chainRate, Finset.prod_range_succ, Finset.prod_range_one] using h

/-- ★ **Repeatability at every depth.** Measure the computational basis, record `i 0`, then measure
it again at every later step: the chain reproduces `i 0` with probability one, to arbitrary depth.

Non-vacuity with teeth — the vertex rate is an indicator (`momentMap_vertex`), so the product of the
tail rates is `1` and the chain does not decay. -/
theorem csd_nstep_repeatable (p : CPN N) (i₀ : Fin N) (n : ℕ) :
    chainRate p (fun _ => momentContext N) (fun _ => i₀) (n + 1)
      = (momentContext N).rate p i₀ := by
  rw [csd_nstep_born_succ]
  have : ∀ m : ℕ, chainRate (vertexPoint i₀) (fun _ => momentContext N) (fun _ => i₀) m = 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
        rw [chainRate, Finset.prod_range_succ, ← chainRate, ihm, one_mul]
        cases m with
        | zero => simpa using momentMap_vertex i₀ i₀
        | succ m' => simpa using momentMap_vertex i₀ i₀
  rw [this, mul_one]

end RecordLayer
end CSD

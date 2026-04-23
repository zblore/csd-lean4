# LF1 implementation plan (retrospective)

Companion to `specs/LF1-v1.01.pdf` (extracted text: `specs/LF1-v1.01.txt`).

LF1 is **already implemented and merged**. This document records the realized design for reference — it is not an aspirational plan. For the canonical source, read `CsdLean4/LF1/`. For session guidance, read `CLAUDE.md`. For a narrative overview, read `README.md`.

## 0. Status

- Modules: 8, under `CsdLean4/LF1/`
- Build: `lake build` — clean, 2649 jobs, no warnings
- `sorry` count: 0
- `axiom` count: 0 (only Mathlib's foundational axioms are assumed)
- CI: green on `main`

## 1. Scope and key design choice

LF1 formalises a **deterministic repeated-trial frequency theorem**: empirical frequencies of outcomes converge almost surely to ontic volume weights. Probability enters only through repeated-preparation sampling; the ontic flow `Φ` is a deterministic measure-preserving map. There is no stochastic ontic dynamics.

The ontic space `Σ` is kept abstract (`MeasurableSpace Σ`). No concrete phase space — no `ℝ^{2n}`, no symplectic manifold, no Kähler structure. Concrete instantiation is deferred to LF2+.

## 2. Realized module layout

```
CsdLean4/LF1/
  Setup.lean         — OnticSetup: Σ, μL (finite), Φ (deterministic flow),
                       Ω0 (preparation region), with hΩ0_meas, hΩ0_nonzero, hΦ_pres
  Preparation.lean   — prepMeasure: conditional measure μprep(A) = μL(A ∩ Ω0) / μL(Ω0)
                       plus prepMeasure_apply (the explicit rewriting lemma)
  Outcomes.lean      — OutcomeRegion: measurable O ⊆ Σ, preEvent pullback, weight,
                       weight_eq_prepEvent_div
  Trials.lean        — TrialModel: i.i.d. preparation sampling over ℕ
  Indicators.lean    — indicatorRV O j ω, empiricalFreq, Bernoulli distribution
                       per trial; indicatorRV_integrable, indicatorRV_identDistrib,
                       trialEvent_eq_comp_preimage
  Expectation.lean   — Bridge: 𝔼[indicatorRV O n] = O.weightReal
  Convergence.lean   — Applies Mathlib's strong law of large numbers
  MainTheorem.lean   — LF1_main_theorem_ae and corollaries
```

Namespaces: `CSD.LF1`, with sub-namespaces `OnticSetup` and `OnticSetup.TrialModel`.

Root imports: `CsdLean4.lean` lists every module explicitly; `CsdLean4/Basic.lean` is a convenience re-export via `MainTheorem`.

## 3. Main theorem (exported)

```lean
theorem LF1_main_theorem_ae
    (T : S.TrialModel Ω)
    (O : S.OutcomeRegion)
    (hindep : Pairwise (IndepFun on (T.indicatorRV O ·))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto (T.empiricalFreq O · ω) atTop (nhds O.weightReal)
```

Caller supplies only pairwise independence of trial indicators. Integrability and identical distribution are proved internally.

The theorem is stated for a **single** `O : OutcomeRegion`. The joint almost-sure statement for a finite measurable partition follows by applying the theorem once per element and intersecting the resulting full-measure sets. This is intentional; a partition type may be introduced at LF2/LF3 for POVM completeness, not here.

## 4. Infrastructure lemmas consumed by LF2+

These are the load-bearing exports:
- `prepMeasure_apply` — the explicit rewriting formula for `μprep`
- `weight_eq_prepEvent_div` — volume interpretation of weights
- `trialEvent_eq_comp_preimage` — makes deterministic structure explicit
- `indicatorRV_integrable`, `indicatorRV_identDistrib` — prerequisites for SLLN

## 5. Conventions worth noting

- `hΩ0_nonzero : (μL : Measure Σ) Ω0 ≠ 0` is threaded through many definitions to prevent division-by-zero in `prepMeasure`.
- `hΦ_pres : MeasurePreserving Φ μL μL` (Liouville's theorem) is structural ontic input; **inside LF1 only its measurability content is used** (extracted via `measurable_Φ`). Full measure preservation is carried for physical admissibility and for LF2+.
- Structure field order in `OnticSetup` and `TrialModel` is load-bearing due to Lean elaboration order.

## 6. What LF1 does not do

- No derivation from symplectic / Hamiltonian first principles.
- No projective / Fubini–Study structure — that is LF2's job.
- No Born-rule claim — LF1 is a frequency theorem, not a probability-rule derivation.
- No mixed states, POVMs, or sequential update — those are later layers.

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Framework
public import CsdLean4.LF3.Interface

/-!
# Empirical/CSD: Bell-family CSD-side reading

**Category:** 3-Local (CSD-side companion to `Empirical/QM/Bell.lean`).

Pairs with `Empirical/QM/Bell.lean` (Phase A1-A6: CHSH, Tsirelson,
no-signalling, marginals, classical-bound-violated). The QM file
states the Bell-family content as pure linear-algebra theorems on
`EuclideanSpace ℂ (Fin 2 × Fin 2)` with Pauli operators. This file
states the **CSD volume-ratio reading**: under CSD's ontic substrate
(Σ, μL, π, prepMeasure, SectorData), the LF1↔LF2↔LF3 chain capstones
predict the same Bell-singlet frequencies that QM does, conditional
on the LF4-discharge hypotheses bundled in `PureSingletPreparation`.

## What this file does

Re-exports the six existing LF1↔LF2↔LF3 chain capstones from
`CsdLean4/LF3/Interface.lean` under empirical-prediction names with
experimental-provenance docstrings. The capstones already exist; this
file adds the empirical framing and the explicit pairing with the
QM-side file. The chain capstones are:

- `LF3_singlet_frequency_convergence` — pre-Born form, lands on
  `P_st ctx.a ctx.b s t`.
- `LF3_singlet_frequency_convergence_born` — closed-form Born,
  lands on `‖cAmp ctx.a ctx.b s t‖²`.
- `LF3_singlet_frequency_convergence_born_inner` — genuine bra-ket
  Born form, lands on `‖⟨prep.PP.ψ, prep.jed.eig s t⟩‖²` where the
  bra-ket is against the bundle's actual joint spin eigenstate.
- Three `_joint` variants with the a.s.-then-∀-s-t quantifier swap.

## LF4 obligations carried (load-bearing, externally supplied, undischarged)

The CSD-side Bell reading inherits the LF4 obligations of the
`PureSingletPreparation D ctx N` bundle:

- `PureSingletPreparation.bridge_op_p` — ontic-weight ↔ OP.p bridge
  on the four `O_region s t` pulled-back outcome events. **Discharge
  target: LF4-todo §2 + §7.**
- `MeasurementJointEig.born_eq_P_st` — Born identity for the joint
  spin eigenstate, `‖⟨PP.ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t`.
  **Discharge target: LF4-todo §2 + §7.**

Both are listed in `BRIDGE-OBLIGATIONS.md` with their LF4-todo
cross-references.

## Experimental provenance

Same as the QM-side `Empirical/QM/Bell.lean`:

- Bell 1964: *Physics* **1**, 195.
- Tsirelson 1980: *Lett. Math. Phys.* **4**, 93.
- Aspect, Grangier, Roger 1982: *Phys. Rev. Lett.* **49**, 91.
- Loophole-free: Hensen 2015, Giustina 2015, Shalm 2015.

## Honest reading

This file does not add new theorem content beyond what LF3 already
delivers. It is the empirical-framing companion: it names the LF3
chain capstones as Bell-family empirical predictions and ties them to
the QM-side counterparts in `Empirical/QM/Bell.lean`.

The CSD-vs-experiment claim for Bell-family content is conditional on
the `PureSingletPreparation` bundle being non-trivially constructible
at LF4 — i.e. conditional on LF4-todo §2 + §7 being discharged. Pre-LF4,
the chain capstones are statements parametric on the bundle; concrete
empirical verification awaits LF4's concrete Kähler instantiation.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Bell

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-! ## CSD-side Bell-family chain capstones (re-exports of LF3)

**STATUS: TRANSPORT-ONLY (all six theorems in this section).** Each
theorem below has a one-line proof body invoking the corresponding LF3
chain capstone. The CSD-side files in this directory add empirical-
prediction framing in their docstrings; they do not add new proof
content. The real content sits in `CsdLean4/LF3/Interface.lean` and
the `PureSingletPreparation` bundle's load-bearing fields.

See `PLACEHOLDERS.md §3` for the canonical transport-only ledger. -/

/-- **Bell singlet frequency convergence (CSD pre-Born form).**

The empirical frequency of the `(s, t)` pointer-sector outcome over
repeated singlet-preparation trials converges almost surely to
`P_{st}(a, b) = (1 − st·a·b)/4`, predicted by CSD's ontic chain
(LF1 trial sampling → LF2 measure bridge → LF3 singlet kernel).

This is the CSD-side companion to `Empirical/QM/Bell.lean`'s
`correlation_eq_neg_dot`: where the QM-side states the singlet
correlation as a closed-form `−a·b`, the CSD-side states the per-sector
frequencies converging to the corresponding `P_st`. Summing
`∑_{s,t} st · P_st(a, b) = −a·b` recovers the QM correlation.

**Experimental verification:** Aspect 1982 (and loophole-free
follow-ups); the pointer-sector frequencies are what the Alice/Bob
joint outcome counts measure. -/
theorem bell_singlet_frequency_convergence
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : CSD.LF3.MeasurementContext) {N : ℕ}
    (prep : CSD.LF3.PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ s t, ∀ᵐ ω ∂ Pr,
       Tendsto
         (fun M : ℕ =>
           (∑ i ∈ Finset.range M,
               Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
             / (M : ℝ))
         atTop
         (nhds (CSD.LF3.P_st ctx.a ctx.b s t)) :=
  CSD.LF3.LF3_singlet_frequency_convergence D ctx prep hX hlaw hindep

/-- **Bell singlet frequency convergence (CSD Born form, closed-form
amplitude).**

Same as `bell_singlet_frequency_convergence` but the per-sector limit
is the squared closed-form singlet amplitude `‖cAmp s t (a, b)‖²`.
Identifies the pre-Born target `P_{st}(a, b)` with the Born form via
`cst_squared_eq`. -/
theorem bell_singlet_frequency_convergence_born
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : CSD.LF3.MeasurementContext) {N : ℕ}
    (prep : CSD.LF3.PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ s t, ∀ᵐ ω ∂ Pr,
       Tendsto
         (fun M : ℕ =>
           (∑ i ∈ Finset.range M,
               Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
             / (M : ℝ))
         atTop
         (nhds (‖CSD.LF3.cAmp ctx.a ctx.b s t‖ ^ 2)) :=
  CSD.LF3.LF3_singlet_frequency_convergence_born D ctx prep hX hlaw hindep

/-- **Bell singlet frequency convergence (CSD Born form, bra-ket
amplitude).**

The physically faithful form: per-sector limit is the genuine
Hilbert-space inner product `‖⟨prep.PP.ψ, prep.jed.eig s t⟩‖²` between
the bundle's pure-preparation vector and the bundle's joint spin
eigenstate. Pairs with `Empirical/QM/Bell.lean`'s `chsh_qm_tsirelson_bound`
(which uses Pauli-tensor expectations on `ψ`); both forms describe the
same physical content via different mathematical phrasings. -/
theorem bell_singlet_frequency_convergence_born_inner
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : CSD.LF3.MeasurementContext) {N : ℕ}
    (prep : CSD.LF3.PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ s t, ∀ᵐ ω ∂ Pr,
       Tendsto
         (fun M : ℕ =>
           (∑ i ∈ Finset.range M,
               Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
             / (M : ℝ))
         atTop
         (nhds (‖inner ℂ prep.PP.ψ (prep.jed.eig s t)‖ ^ 2)) :=
  CSD.LF3.LF3_singlet_frequency_convergence_born_inner D ctx prep hX hlaw hindep

/-! ### Joint partition variants -/

/-- **Joint a.s. version of `bell_singlet_frequency_convergence`.** -/
theorem bell_singlet_frequency_convergence_joint
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : CSD.LF3.MeasurementContext) {N : ℕ}
    (prep : CSD.LF3.PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
       ∀ s t,
         Tendsto
           (fun M : ℕ =>
             (∑ i ∈ Finset.range M,
                 Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
               / (M : ℝ))
           atTop
           (nhds (CSD.LF3.P_st ctx.a ctx.b s t)) :=
  CSD.LF3.LF3_singlet_frequency_convergence_joint D ctx prep hX hlaw hindep

/-- **Joint a.s. version of `bell_singlet_frequency_convergence_born`.** -/
theorem bell_singlet_frequency_convergence_born_joint
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : CSD.LF3.MeasurementContext) {N : ℕ}
    (prep : CSD.LF3.PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
       ∀ s t,
         Tendsto
           (fun M : ℕ =>
             (∑ i ∈ Finset.range M,
                 Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
               / (M : ℝ))
           atTop
           (nhds (‖CSD.LF3.cAmp ctx.a ctx.b s t‖ ^ 2)) :=
  CSD.LF3.LF3_singlet_frequency_convergence_born_joint D ctx prep hX hlaw hindep

/-- **Joint a.s. version of `bell_singlet_frequency_convergence_born_inner`.** -/
theorem bell_singlet_frequency_convergence_born_inner_joint
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (ctx : CSD.LF3.MeasurementContext) {N : ℕ}
    (prep : CSD.LF3.PureSingletPreparation D ctx N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = prep.μψ)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
       ∀ s t,
         Tendsto
           (fun M : ℕ =>
             (∑ i ∈ Finset.range M,
                 Set.indicator (X i ⁻¹' (prep.O_region s t).preEvent) (fun _ => (1 : ℝ)) ω)
               / (M : ℝ))
           atTop
           (nhds (‖inner ℂ prep.PP.ψ (prep.jed.eig s t)‖ ^ 2)) :=
  CSD.LF3.LF3_singlet_frequency_convergence_born_inner_joint D ctx prep hX hlaw hindep

end Bell
end CSDBridge
end Empirical
end CSD

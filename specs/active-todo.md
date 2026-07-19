# Active TODO — CSD session work queue (persistent)

> **⚠️ Open items now live in [`BACKLOG.md`](BACKLOG.md).** This is a historical
> session-queue record (mostly-DONE core rows + the #16/#15/framing notes). The ecdsa.fail
> task rows and score ledger were moved to the separated track: [`ecdsa/todo.md`](ecdsa/todo.md),
> [`ecdsa/score-ledger.md`](ecdsa/score-ledger.md).

**Purpose.** Durable copy of the session task list so it survives session loss. If the
in-memory task list is gone, re-seed from the table below (each row → a task; keep the
Category / Complexity / Blocked-by columns). Last updated 2026-07-16.

**Complexity key:** S = single step · M = one expert tranche · L = multi-tranche · XL =
research-frontier / infrastructure gap.

## Task table

| # | Task | Category | Cx | Status | Blocked by |
|---|---|---|---|---|---|
| 1 | LF6-A.3 local product de-isolation flow | LF6 | M | DONE | |
| 3 | LF6-B.1 decoherence / partial-trace (D1b) | LF6 | M | DONE | |
| 6 | LF6-A.2 contextuality corollary | LF6 | S | DONE | |
| 8 | LF6-A.3 flow-realises-dilation lemma | LF6 | S | DONE | |
| 9 | LF6-B.2 purity-drop witness | LF6 | M | DONE | |
| 16 | Debt D1c-1: structural Φ≠id into kSectorData (kFlow) | Foundations-debt | M | DONE | |
| 28 | D1c-2: physically-meaningful Φ (obsFlow Hamiltonian) into cpSectorData | Foundations-debt | S | DONE | |
| 29 | A5 onramp: typicality forced by symmetry + single-flow obstruction (DONE) | Foundations-debt | L | DONE | |
| 32 | A5 onramp follow-up: conserved-quantity CONTINUUM of invariant measures (DONE) | Foundations-debt | M | DONE | |
| 33 | A5: obsFlow_not_ergodic — momentMap·i is a non-constant conserved observable (closes the obstruction story) | Foundations-debt | S–M | DONE | |
| 17 | A5: derive sector (π,G) + FS typicality from dynamics — BOUNDARY PROVED both sides (2026-07-16, `FND/A5NoGo.lean`): a single projective flow provably CANNOT pin μ_FS (`flow_admits_invariant_ne_fubiniStudy`, exhibited on `diag(1,-1)`/ℂℙ¹ `phaseFlip_admits_invariant_ne_fubiniStudy`); full U(N) symmetry provably DOES (`region_measure_symmetry_forced`). L7 now OPEN (boundary proved). Residual = derive G=U(N) from D1 substrate | Foundations-debt | XL | open | #29 |
| 5 | LF6 general-N entangled tier — C.1 + C.2 + C.3 DONE 2026-06-30. C.1: GHZ forced-contextuality crux (`no_product_partition_realises_ghz`, DETERMINISTIC all-or-nothing; GHZContextuality.lean). C.2: GHZ de-isolation FLOW `Φ≠id` @ N=8, MINIMAL diagonal carve (GHZDeisolationFlow.lean). C.3: the GENUINE dynamical contextual carve (GHZMerminCarve.lean) — new GHZ Pauli-context joint eigenstructure, `ghzDeisolation_blockVolume_correlation` (block-volume sum = Mermin expectation `re⟨ghz|σσσ|ghz⟩`, all four contexts) + `ghzDeisolation_carve_not_product` (four-context tie to C.1 CLOSED, the carve's OWN correlations). First DYNAMICAL realisation of GHZ non-locality. NEXT: 3-party local product flow V₀⊗V₁⊗V₂ + wider general-N (bipartite d×d, GHZ_n) | LF6 | L | C.1–C.3 DONE; local-flow + wider-N open | |
| 15 | Open-system / decoherence empirical (umbrella; 15a einselection DONE) | Empirical | L | 15a–e ALL DONE (series closed) | |
| 27 | 15e channel capacities — DONE: dephasing classical-yes/quantum-no contrast (fixes |i⟩⟨i|, Holevo χ=log 2; |+⟩→½I entropy jump 0→log 2); single-letter Holevo (regularized capacity NOT claimed, concavity gated); 2 new Cat-1 entropy lemmas S(c·I)/S(½I)=log 2 relocated to QuantumInfo/Entropy.lean; ontic capacity D1-gated (ChannelCapacity.lean) | Empirical | M | DONE | |
| 26 | 15d quantum Zeno — DONE: derived quadratic short-time bound P(s)≥1−(ΔH)²s² + zero slope P'(0)=0 (σx/|0⟩ witness, variance (ΔH)²=1 from matrices), Bernoulli lower bound P_n≥1−(ΔH)²t²/n, freezing P_n→1 (squeeze); non-vacuity (ΔH)²>0 + full decay at π/2; exp(-isσx) closed-form asserted, rest derived; CSD re-carving reading, dynamical Σ-flow D1-gated (QuantumZeno.lean) | Empirical | M | DONE | |
| 25 | 15c weak/unsharp measurement — DONE: unsharp POVM weakEffect±(η)=½(I±ησ), no-meas(η=0)↔projective(η=1) interpolation, partial-info witness, FULL FS-volume reading on ℂℙ³ Naimark dilation (Gleason-free uncond engine); continuous-measurement flow D1-gated (WeakMeasurement.lean) | Empirical | M | DONE | |
| 24 | 15b QEC-as-decoherence — DONE: error = K2 bit-flip CHANNEL + Stinespring origin + in-code correction (recoverⱼ∘errorⱼ=id on encoded density, one space); ontic Σ-volume origin gated to D1 (QECDecoherence.lean) | Empirical | M | DONE | |
| 34 | 15a follow-up — DONE: degeneracy boundary (p₀=p₁ ⇒ ½I basis-invariant, einselection FAILS; iff `decohere_hadamard_offDiag_ne_zero_iff`) + general-N einselection (`einselectionN`, `decohereReducedN_acts_nontrivial`); ontic origin D1-gated (Einselection.lean) | Empirical | M | DONE | |
| 4 | Metrology A4: decoherence (Lindblad) | Metrology | XL | open | |

Per-area plans: [`lf6-plan.md`](lf6-plan.md), [the ecdsa.fail track](ecdsa/INDEX.md),
[`metrology-plan.md`](metrology-plan.md), [`INDEX.md`](INDEX.md).

## #16 — D1c plan (thread genuine Φ through concrete SectorData)

**Debt.** The concrete instances hard-code `Φ := id`: `kSectorData` (`LF4/KahlerInstance.lean:107`),
`cpSectorData` (`LF4/Instance.lean:64`). The flow lives in `SectorData.toOntic.Φ` (the LF1
`OnticSetup.Φ`); the load-bearing law is `hΦ_pres : MeasurePreserving Φ μL μL` (carried as
structural payload — LF1/LF2/LF3 proofs only use `measurable_Φ`).

**Asset (ready).** `LF4/KahlerFlow.lean` already has `kFlow sh : (p,t) ↦ (p, sh+t)` on
`KSigma N = ℂℙ^{N-1} × T²`, with `kFlow_measurePreserving`, `kFlow_ne_id` (sh≠0),
`kFlow_preserves_rays` (`π∘kFlow = π`), and `kFlow_frequency_convergence` (LF1 typicality
non-vacuous on the **evolved** states). But `kFlow` is NOT wired as any SectorData's `Φ`.

**D1c-1 (tractable, M — recommended first).** Build `kSectorData'` / a `kOnticSetup` variant
with `Φ := kFlow sh` (sh≠0) instead of `id`. Proof obligations, nearly all already proven:
- `Φ` measurable — `kFlow` is `id × (sh + ·)`, measurable.
- `hΦ_pres` = `kFlow_measurePreserving` (exists verbatim).
- SectorData G-action coherence (`hμL_inv`, equivariance `π∘onticAction = epAction∘π`) is
  about `onticAction`, NOT `Φ`, so it is unaffected; `kFlow_preserves_rays` confirms `Φ`
  commutes with the base/π structure.
- Non-vacuity: lift `kFlow_frequency_convergence` so the LF1/LF2 chain on `kSectorData'` is
  genuinely about a moving flow (`kFlow_ne_id`).
Result: a concrete SectorData carrying a genuine measure-preserving `Φ ≠ id`, discharging the
headline "every concrete instance has Φ=id" caveat for the Kähler instance.

**D1c-1 honest scope.** `kFlow` is a FREE T²-fibre translation — a genuine measure-preserving
`Φ≠id`, but trivial dynamics: not a measurement/de-isolation flow, not a symplectic/Hamiltonian
flow derived from the Kähler form. So D1c-1 discharges the STRUCTURAL debt (the instance carries
non-trivial dynamics), not the physical content.

**D1c-1 DONE 2026-06-29** (`LF4/KahlerFlow.lean`, self-verified, foundational-triple): `kOnticSetupFlow`
(= `kOnticSetup` with `Φ := kFlow sh`, `hΦ_pres := kFlow_measurePreserving`) + `kSectorDataFlow` (G-action
fields reused verbatim — none touch `Φ`) + `kSectorDataFlow_phi_ne_id` (instance's `Φ ≠ id`),
`_phi_measurePreserving`, `kSectorDataFlow_frequency_convergence` (LF1 typicality through the instance's
own `Φ ∘ sample` → `kMuL` volume, non-vacuous). Structural `Φ=id` debt discharged for the Kähler instance.
3 AxiomAudit pins. `cpSectorData` still `Φ=id`.

**D1c-2 DONE 2026-06-29** (`LF4/ObservableFlow.lean`, self-verified, foundational-triple): `cpSectorDataFlow`
= `cpSectorData` with `Φ := obsFlow lam t` (a diagonal-phase `e^{itÂ}` observable/Hamiltonian flow on the
actual Fubini–Study Kähler base ℂℙ^{N-1}, MOVING superposition rays — strictly stronger than D1c-1's
ray-fixing fibre translation), `hΦ_pres := obsFlow_measurePreserving`; `cpSectorDataFlow_phi_ne_id`,
`_phi_measurePreserving`, `cpSectorDataFlow_frequency_convergence` (LF1 via `freq_tendsto_of_iid`). 3 pins.
Honest: a single observable's PERIODIC phase flow — NOT ergodic/mixing, so A5 still untouched.

**A5 onramp (#29) DONE 2026-06-29** (`LF4/TypicalityForcing.lean`, auditor-SOUND, foundational-triple).
The naive "single ergodic flow forcing μFS" is MATHEMATICALLY OBSTRUCTED (a one-parameter unitary flow on
ℂℙ^{N-1} has torus orbit-closures + fixed basis rays). The honest content instead:
- (A) `fubiniStudy_forced_by_symmetry`: any U(N)-invariant probability (typicality) law on the sector IS
  μFS (one-line reuse of the axiom-free `invariant_measure_uniqueness_cpn`). So Born = FS-volume is DERIVED
  from the sector symmetry G, CONDITIONAL on positing G-invariance of the typicality law.
- (B) `obsFlow_not_uniquely_ergodic` (the honest negative, genuine new content): `obsFlow` fixes the
  eigenstate rays, so `δ_{[e₀]}` is invariant and ≠ μFS (distinctness via a swap-unitary + FS's
  U(N)-invariance) — TWO distinct invariant probability measures, so a single ontic flow does NOT force
  μFS. This is WHY D1c-1/2's single-flow instances do not discharge A5.
- `a5_onramp` capstone conjoins (A)+(B). HONEST: A5 is NOT closed; typicality is forced by the SYMMETRY
  (not a flow); the residual A5 primitive is G=U(N) ITSELF, reducing to D1 (deriving the U(N)-symmetry of
  the ontic dynamics from the substrate — the deepest open content). Nothing claimed about deriving G.
Follow-up #32: strengthen (B) to a continuum of invariant measures via the moment-fibre conserved
quantities (`momentMap ∘ obsFlow = momentMap`). The genuine A5/D1 frontier beyond: the entangled
de-isolation tier (Bell-forced non-locality), where G could begin to be derived rather than posited.

(superseded:) The fuller D1c-2 is threading the LF5/LF6 de-isolation/measurement `Φ_vN`
(needs the SectorData on the dilated space).

**Relation to A5 (#17).** D1c (Φ≠id) is necessary-but-not-sufficient for A5 (deriving (π,G) +
FS typicality from the dynamics). A5 additionally needs the flow to be ergodic/mixing so the FS
measure is FORCED (the quantum Liouville/equal-a-priori justification). D1c-1 is the structural
foothold; the flow choice in D1c-2 is what an A5 ergodicity argument would build on.

## #15 — open-system empirical targets: next-tranche scoping

LF6-B gives `decohereReduced` (the dephasing channel), `Channel`, `PartialTrace`,
`decoherence_dephases` (→ Born diagonal mixture), `_offdiagonal_vanish`, the purity drop (B.2).
Candidate first tranches, by tractability:

1. **Einselection / pointer-basis (M, DONE 2026-06-29 — `Empirical/CSD/Einselection.lean`).** Witness:
   `(qmH · decohereReduced ψ · qmH) 0 1 = (p₀−p₁)/2` (computed); `decohere_not_diagonal_in_rotated_basis`
   (off-diag ≠ 0 for `p₀≠p₁`); `einselection` capstone (diagonal in `{e_j}`, off-diag `3/2` in the
   Hadamard rotation). Decoherence is basis-SELECTIVE; the pointer basis is the de-isolation's context
   basis, contrasted honestly with #29's basis-covariant FS typicality. Follow-up #34: degeneracy boundary
   (`p₀=p₁ ⇒ scalar·I`, every basis diagonal) + general-N. (original scoping:) `decohereReduced` already yields the
   diagonal Born mixture IN THE MEASUREMENT BASIS — the pointer basis IS the einselected basis.
   Tranche: prove decoherence selects that basis as the preferred one — coherences vanish in the
   `e_j` basis (have B.1) but PERSIST in a generic rotated basis (the new content: the reduced
   state is NOT diagonal in a rotated frame, so the basis is genuinely selected, not arbitrary).
   Directly on the B.1/B.2 machinery, no new infra. Zurek einselection, the "why a preferred
   basis" foundational content.
2. **QEC-as-decoherence (M–L).** Connect LF5-G's syndrome readout to the error channel
   (`bitFlipChannel` / `Channel` + `PartialTrace`): the error channel as system→environment
   decoherence, syndrome extraction as partial de-isolation. Reuses LF5-G + the Channel branch.
3. **Weak / continuous measurement (M–L).** Partial de-isolation (a coupling-strength parameter),
   gradual decoherence interpolating identity↔full dephasing. New infra: parameterised weak
   coupling.
4. **Quantum Zeno (M, DONE 2026-06-30 — `Empirical/CSD/QuantumZeno.lean`).** Repeated projective
   re-measurement onto `|0⟩` freezes evolution. Mechanism DERIVED on the `σx`/`|0⟩` witness:
   variance `(ΔH)²=1` from the matrices, the quadratic short-time bound `P(s)≥1−(ΔH)²s²`
   (`zeno_survival_quadratic`, coefficient = the computed variance) and the zero initial slope
   `P'(0)=0` (`zeno_survival_slope_zero`). Limit: Bernoulli lower bound `P_n≥1−(ΔH)²t²/n`
   (`zeno_survival_lower_bound`) + freezing `P_n→1` (`zeno_freezing`, full squeeze). Non-vacuity
   `(ΔH)²>0` with full free decay at `π/2` (`zeno_nonvacuous`). The closed-form `exp(-isσx)` is the
   asserted standard qubit rotation; all else derived. CSD re-carving reading; the dynamical
   measurement-interspersed Σ-flow `Φ≠id` is D1-gated (LF6).
5. **Channel capacities (L).** The de-isolation channel's classical/quantum capacity — needs the
   K1 entropy machinery + capacity definitions.

Recommended order: 1 (einselection) → 2 (QEC-as-decoherence) → 3/4 (weak/Zeno) → 5 (capacities).
Status: 1, 2, 3, 4 DONE; 5 (channel capacities, 15e) is the remaining open-system empirical entry.

## FRAMING CORRECTION (2026-06-29, per user / papers A & B): typicality is forced by the LLN, NOT ergodicity

CSD forces **typicality** (frequencies → ontic volume weights) by the **law of large numbers** (LF1,
`LF1_main_theorem_ae` / `freq_tendsto_of_iid`, over repeated i.i.d. preparations) — papers A & B. There is
NO time-average / Birkhoff / single-flow-ergodicity hypothesis in the forcing. Earlier A5-onramp docs
(below, #29/#32/#33) used an ergodicity framing imported from stat mech; that is the WRONG mechanism.
Re-classification of the onramp results (the theorems are correct; only the framing was off):
- **#29 `fubiniStudy_forced_by_symmetry` is a MEASURE-CHARACTERISATION, not a forcing.** FS is the unique
  U(N)-invariant measure → it is the symmetry-CANONICAL measure to sample from on the sector. It bears on
  the measure CHOICE; the LLN then forces frequencies to its volume ratios. NOT "typicality forced by
  symmetry."
- **#32/#33 are honest NEGATIVES about the single-flow Birkhoff (time-average) route — which CSD does NOT
  use.** They show you cannot shortcut typicality via one flow's ergodicity (conserved Born coordinates
  block it), which REINFORCES that the LLN/i.i.d. route is the right one. They are not an obstruction to
  CSD's typicality (there is none — the LLN does the forcing).
Net: typicality-forcing is SETTLED (LLN, A&B). Measure-choice is symmetry-canonical (#29). The A5 residue
is just the SECTOR/SYMMETRY origin = G-from-D1; typicality-forcing is NOT part of the residue.

### Byproducts of the (mis-framed) ergodicity exploration — KEEP (they were net-positive)

The ergodicity framing was wrong, but the WORK yielded three durable things:
1. **The negative results JUSTIFY the LLN route (not just decline ergodicity).** #32/#33 prove a single
   one-parameter unitary flow CANNOT be μFS-ergodic (the Born coordinates are constants of motion; orbit
   closures are tori, real-dim ≤ N−1 inside the 2(N−1)-dim sector). So CSD's LLN/ensemble route is FORCED,
   not a stylistic choice.
2. **Individual-vs-ensemble typicality — a genuine D1 constraint.** The LLN gives ENSEMBLE typicality
   (many fresh preparations). An ergodic flow would give the stronger SINGLE-TRAJECTORY / individual-system
   account (one system's time-average self-averages to Born, Boltzmann's actual ergodic hypothesis). #33
   shows the single-trajectory account is BLOCKED under unitary dynamics. CONSTRAINT FOR D1: any
   individual-system Born account must come from genuinely mixing — i.e. NON-UNITARY / open-system or
   entangled de-isolation — dynamics, never unitary time-evolution. (Paper-worthy: A/B/D — flag for the
   user; do not touch preprints.)
3. **Reusable framing-independent lemmas** (in `LF4/TypicalityForcing.lean`): `map_withDensity_of_conserved`
   (reweighting an invariant measure by a conserved quantity preserves invariance — general Mathlib-grade)
   and `fubiniStudyMeasure_pos_of_isOpen` (FS has FULL SUPPORT: every nonempty open set has positive
   measure — directly useful for any "generic ψ" / open-dense genericity argument across the corpus).


# LF4 TODO: items deferred from LF2

Items LF2 deliberately left for LF4, with rationale and concrete pickup notes.

> **Orientation:** see [`INDEX.md`](INDEX.md) for the full doc map. The next major
> tranche is the POVM extension — [`povm-plan.md`](povm-plan.md).

## Status header (updated 2026-06-02)

Recent closures, so this ledger is read in context:

- **§14.2 observable correspondence + Robertson** — CLOSED (six commits, two witnesses).
- **General-N Duistermaat–Heckman / Born-from-Kähler-volume** — CLOSED. Born = FS
  typicality volume on `ℂℙ^{N-1}` for general `N`, Gleason-free, with the empirical
  capstone `born_frequency_convergence_N` and the N=2 reduction cross-check. See
  [`general-n-dh-plan.md`](general-n-dh-plan.md).
- **LF3 empirical chain re-routed off Busch** (2026-06-02) — `weight_eq_P_st` now goes
  through `OP_p_at_jointEig_eq_P_st_direct`; the six chain capstones + the LF4 singlet
  instance + the Empirical Bell re-export are foundational-triple-only.
  `busch_effect_gleason` is retained only as the **operational-stratum** statement
  (`pure_state_born_weights_of_certainty`, `born_rank_one`, `OP_p_at_jointEig_eq_P_st`,
  `ontic_born_frequency`). Two-strata reading: [`../AXIOMS.md`](../AXIOMS.md) §2.4.
- **POVMs CLOSED 2026-06-03** ([`povm-plan.md`](povm-plan.md)) — the ontic Born derivation
  now covers general measurements via Naimark dilation; `busch_effect_gleason` is off the
  ontic path entirely (operational-stratum only).
- **§2 preparation-to-Hilbert correspondence — DONE for pure-state classes** (see §2 below,
  2026-06-08 audit); mixed/multi-particle residue tracked under §8.
- **Open frontier: D1** ([`carve-out-plan.md`](carve-out-plan.md)) — exercising real
  measurement dynamics on `Σ` (`Φ = id` in every concrete sector instance today). §13
  (ontic→Hilbert isometry lift) is coupled to it (needs the Wigner / FS-rigidity lemma + the
  D1 flow), not to §2.

The numbered items below (§1–§14) remain as the standing ledger.

## Bridge-discipline rules (added 2026-05-21)

`Empirical/CSD/<phenomenon>.lean` files carry LF4-discharge hypotheses
as bundle fields. Three discipline rules govern how those hypotheses
interact with this LF4-todo list:

1. **Every load-bearing Bridge bundle field carries a docstring
   `**Status: load-bearing, externally supplied, undischarged.**`
   marker + a one-line citation to a numbered item in this file.**
   See `LF3.PureSingletPreparation.bridge_op_p` (cites §2 + §7) for
   the canonical template.

2. **No new LF4 obligations can be introduced by a Bridge file
   landing PR.** If a new Bridge file needs a new obligation:
   - Land a separate PR amending this file (`LF4-todo.md`) with
     explicit justification.
   - **Then** land the Bridge file referencing the new numbered item.

   Prevents Bridge accretion from quietly expanding LF4 scope by
   piecemeal addition.

3. **`BRIDGE-OBLIGATIONS.md` is the canonical ledger** listing every
   load-bearing Bridge field with its LF4-todo cross-reference. Audit
   cross-Bridge-file drift per release. Updated in the same commit as
   any change to a Bridge bundle field or to a numbered LF4-todo item.

See `specs/empirical-csd-bridge-plan.md` §5 for the rationale, and
`BRIDGE-OBLIGATIONS.md` for the current ledger state.


## 1. Unitary covariance clause of OperationalPackage (spec Def 5.1 clause 3)

**Status:** LF2 omits the `unitary_covariance` field. `Effect.conjugateBy` is in place as the structural helper.

**Why deferred:** Two readings of spec clause 3, and the wrong one over-constrains:

- **Invariance reading** — `p (Effect.conjugateBy U E) = p E` for all U. Rules out pure-state packages.
- **Covariant reading** — a functor `OperationalPackage.conjugateBy U : OperationalPackage N → OperationalPackage N` with `(conjugateBy U OP).p E = OP.p (Effect.conjugateBy U E)`. Mathematically correct, type-heavy.

**Pickup:**
1. Implement `OperationalPackage.conjugateBy` as a function producing a new package.
2. Prove the structure fields (nonneg, le_one, total_one, additivity) carry through conjugation. Most reduce to applying `Effect.conjugateBy` inside and invoking the original field.
3. `total_one` requires showing `Effect.conjugateBy U Effect.one = Effect.one` (since `U† · 1 · U = 1` for unitary `U`).
4. `additivity` requires `Effect.conjugateBy U (Effect.add E F hLe) = Effect.add (conjugateBy U E) (conjugateBy U F) hLe'` for some derived `hLe'`. Distributivity of conjugation over matrix addition closes it.
5. Once the functor is in place, state a covariance theorem: `(conjugateBy U OP).p E = OP.p (Effect.conjugateBy U E)` — tautological by construction.

**Depends on:** `Matrix.unitaryGroup` (already imported in LF2), `Effect.conjugateBy` (LF2).

---

## 2. Preparation-to-Hilbert-vector correspondence — **DONE for pure-state classes (LF4, 2026-06-08 audit); mixed/multi-particle residue tracked under §8**

**Status update (2026-06-08).** The three "remaining LF4 work" items below were
discharged by the LF4 §8 + moment-map work that postdates this entry's original
2026-05-18 draft; verified in-code 2026-06-08:

1. **Specialise `P` to `Projectivization` — DONE.** `cpSectorData` / `kSectorData`
   instantiate `P := CPN N := ℙ ℂ (EuclideanSpace ℂ (Fin N))`
   (`LF4/Instance.lean:47,70`, `LF4/KahlerInstance.lean:103`).
2. **`bridge_op_p` discharge in a concrete instance — DONE.** Proved as a theorem in
   `LF4/SingletKahler.lean:277-290` (foundational-triple-only), via the fibre-arc carving
   identity. Tier-2 honesty: this *realises* the Born value (the fibre partition is cut to
   the Born volume), it does not *derive* it; the carving-free *derivation* (Born = FS
   volume, general `N`) is the separate moment-map cluster `born_frequency_convergence_N`.
   Note the target was revised by the 2026-05-25 posited-fibre migration — discharged
   against the posited fibre law `μψ`, not `prepMeasure` (a μL-conditional pure preparation
   is μL-null hence uninhabitable under the continuous bridge).
3. **`ofKählerPreparation` from a concrete Kähler `SectorData` — DONE.**
   `LF4/SingletKahler.lean:290`, with the capstone
   `ofKählerPreparation_singlet_frequency_convergence`.

**Residue (genuinely open):** only the **mixed-state / multi-particle** preparation classes,
which are tracked under §8 (additional preparation classes), not as a missing piece of the
pure-state correspondence. Note for §13: this entry being done does **not** unblock §13 —
§2 is the *static* preparation→Born-weight correspondence; §13 needs *dynamical*
inner-product preservation (the rigidity lemma + the D1 flow), which is the real blocker.

---

### Original 2026-05-18 record (superseded by the status update above)

**Status:** Substantial structural progress. Pre-LF4 work landed:

- `LF2.PurePreparation` (`CsdLean4/LF2/Preparation.lean`, Phase 4) carries the static pure-preparation data: `ψ` (unit vector), `rep : P → EuclideanSpace ℂ (Fin N)` (caller-supplied projective representative), `ray_point : P`, `rep_at_ray : rep ray_point = ψ`, and the Dirac concentration `push_dirac : Measure.map D.π μprep = Measure.dirac ray_point`.
- `LF2.PurePreparation.born_rank_one` and `LF2.PurePreparation.born_rank_one_direct` (Phase 4) prove `OP.p (rankOneEffect φ hφ) = ‖⟨ψ, φ⟩‖²` for the OP built by `OperationalPackage.fromPreparation`.
- `LF3.PureSingletPreparation` (`CsdLean4/LF3/PurePreparation.lean`, Phase 7) rewrote the LF3 chain bundle in option (B) form: carries `LF2.PurePreparation` + `MeasurementJointEig` + ontic outcome regions + the **ontic-weight ↔ OP.p bridge** `bridge_op_p` as the new LF4 discharge target.

**Design-space decision (resolved 2026-05-18).** Option (b) of the 2026-05-17 design discussion (bundle the discharge into a preparation structure) was adopted. Option (a) — permanent hypothesis — was ruled out per the 2026-05-17 decision. Option (c) — Born-ready typeclass — was rejected at pre-LF4 plan time on ergonomic grounds.

**Remaining LF4 work (the actual discharge):**

1. Specialise LF2's abstract `P` to `Projectivization ℂ (EuclideanSpace ℂ (Fin N))` (waits on §12: `Projectivization` topology / measure API).
2. Construct `LF2.PurePreparation` from a concrete preparation `μprep` whose pushforward `Measure.map D.π μprep` concentrates Dirac on `[ψ]`. This is the **`bridge_op_p` discharge proper**: in a concrete `(Σ, π, Φ, μprep)` instantiation, prove
   `prepMeasure((O_region s t).preEvent) = ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t) _))`.
3. Construct `LF3.PureSingletPreparation.ofKählerPreparation` from a concrete Kähler `SectorData` (per §8).

The Phase 4 + 7 work staged the *structural shape* of the chain. The actual measure-theoretic content discharging `bridge_op_p` is LF4 work pending §8 + §12. See also `specs/pre-LF4-plan.md` for the full execution log.

---

## 3. Rank-1 effects from projective points (not from unit vectors) — **PARTIAL (pre-LF4 Phase 1, 2026-05-18)**

**Status:** Step 1 (phase invariance) **DONE**. Steps 2-3 (projective-point lifts) deferred to LF4 + §12 (`Projectivization` topology API).

Pre-LF4 Phase 1 delivered (`CsdLean4/LF2/PhaseInvariance.lean`):

- `outerProduct_phase_invariant : ‖c‖ = 1 → outerProduct (c • φ) = outerProduct φ` — the algebraic phase invariance of the outer product. Algebraic content: `(c • φ) ⊗ (c • φ)* = c · c̄ · (φ ⊗ φ*) = ‖c‖² · (φ ⊗ φ*) = φ ⊗ φ*`.
- `rankOneEffect_phase_invariant` and `rankOneDensity_phase_invariant` — phase invariance of the structure-level wrappers.

Additionally, the LF3 measurement-context bundle (`LF3.MeasurementJointEig`, Phase 6) is parametric in the abstract joint eigenstate vectors rather than requiring projective points; it stages the projective lift as an LF4-discharge target without committing to a `Projectivization` realisation pre-LF4.

**Remaining LF4 work:**

2. Lift to projective points: for `[φ] : Projectivization ℂ (EuclideanSpace ℂ (Fin N))`, define `rankOneEffectProj [φ]` via `Projectivization.lift` + `outerProduct_phase_invariant`. Waits on §12 (Mathlib `Projectivization.lift` measurability API).
3. Similarly for `rankOneDensityProj`.

**Depends on:** §12 (`Projectivization` topology / measure API as a Cat-1 Mathlib contribution).

---

## 4. Prove `rankOneDensity_unique_of_certainty` (remove axiom) — DISCHARGED 2026-05-18

**Status:** Proved in `CsdLean4/LF2/BornWrapper.lean`. Axiom retired; the
declaration is now a `theorem`. AxiomAudit regression updated to drop the
axiom from `pure_state_born_weights_of_certainty`'s `#print axioms` output.

**How discharged.** The route avoided the spectral theorem entirely:

1. **Trace-form to inner-product equation.** `traceForm ρ (rankOneEffect ψ hψ) = 1`
   unfolds to `RCLike.re ((ρ.M * outerProduct ψ).trace) = 1`. Hermitian-product
   trace is real (`Tr(AB)` = `Tr((AB)ᴴ)*` = `Tr(BA)`), so the imaginary part
   is zero and `(ρ.M * P).trace = (1 : ℂ)` outright.
2. **`(I − P) ρ (I − P)` is PSD with trace zero.** Trace cyclicity plus
   `(I − P)² = (I − P)` gives `Tr((I−P) ρ (I−P)) = Tr(ρ) − Tr(ρ · P) = 1 − 1 = 0`.
   `Matrix.PosSemidef.trace_eq_zero_iff` collapses this to `(I − P) ρ (I − P) = 0`.
3. **`ρ · (I − P) = 0`.** Apply `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`
   to `ρ.M` (which is PSD): for any v, `star (Qv) ⬝ᵥ ρ Qv = star v ⬝ᵥ Q ρ Q v = 0`,
   so `ρ Qv = 0` for all v; hence `ρ · Q = 0` (via `Matrix.ext_iff_mulVec`).
4. **`ρ = ρ · P = P · ρ · P`.** Subtraction + Hermitian-adjoint reasoning.
5. **Rank-1 sandwich.** `P · M · P = Tr(M · P) • P` for any `M`, proved
   entry-wise from the `vecMulVec` definition of `outerProduct`. With
   `Tr(ρ · P) = 1`, we get `ρ = 1 • P = P = outerProduct ψ`. Structure
   equality closes.

The key Mathlib infrastructure used: `Matrix.PosSemidef.trace_eq_zero_iff`,
`Matrix.PosSemidef.dotProduct_mulVec_zero_iff`, `Matrix.ext_iff_mulVec`,
`Matrix.vecMulVec_apply` + `Finset.sum_comm`. No spectral theorem; no CFC
sqrt; no `Star (Matrix _ _ _ →L[ℂ] _)` synthesis. This makes the proof
robust to the typeclass landscape at Lean 4.29.0-rc8.

**Note for future archaeology.** Earlier scaffolding in the module docstring
sketched a CFC sqrt route. That route would have worked if Matrix had a
`NonUnitalContinuousFunctionalCalculus ℝ (Matrix _ _ _) IsSelfAdjoint`
instance, but Mathlib does not synthesize this for `Matrix (Fin N) (Fin N) ℂ`
under our context. The PSD inner-product route above bypasses the issue.

---

## 5. Prove the two spec-mandated axioms (long-term)

**Status:** `invariant_measure_uniqueness` and `busch_effect_gleason` remain axioms. Spec §7.4 accepts this.

**Why deferred:** Each is a Mathlib-scale contribution.

- `invariant_measure_uniqueness` — Haar measure on compact homogeneous spaces (`SU(N)/U(N-1) ≅ CP^{N-1}`). Mathlib has Haar on topological groups; the quotient/homogeneous-space case requires more work. **Concrete realisation PROVED 2026-05-24**: the `CP^{N-1}` / `U(N)` content of this axiom is now an axiom-free theorem, `Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn` (`CsdLean4/Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean`), built on the §12 projectivization API + `fubiniStudyMeasure_unique` (Phase G4) + `invariant_finiteMeasure_eq_smul_fubiniStudy` (Phase G5, finite-measure normalisation). The abstract axiom is **not** discharged (it is stated over an arbitrary pretransitive `(P, G)` with no topology, so is strictly stronger than provable); the remaining work is the §8 instantiation that lets LF2's `measure_bridge` route through the concrete theorem. See `AXIOMS.md §2.1`.

- `busch_effect_gleason` — effect-algebra infrastructure (not currently in Mathlib), plus Busch 2003's proof. Larger task; full effect-algebra / POVM machinery is an open Mathlib gap. No concrete-realisation thread yet (cf. the projectivization thread for the other axiom; the analogous target here is a finite-dimensional Gleason/Busch formalisation).

**Pickup:**
- `invariant_measure_uniqueness`: the math core is done. The count drop (two axioms → one) happens at §8 instantiation — set `P := ℙ ℂ (EuclideanSpace ℂ (Fin N))`, `G := U(N)`, `μFS := fubiniStudyMeasure p₀`, and add a concrete `measure_bridge` citing `invariant_measure_uniqueness_cpn` rather than the axiom. Signatures are already shape-compatible.
- `busch_effect_gleason`: remains an axiom until Mathlib integration. When it lands, swap `axiom` for `theorem`-via-import in LF2.

---

## 6. σ-additivity vs finite additivity of OperationalPackage

**Status:** LF2 encodes only finite additivity (pairwise). Busch's original result uses σ-additivity.

**Why deferred:** In finite dimension the distinction is usually inessential — the effect algebra is "compact enough" that finite additivity implies σ-additivity. But we haven't verified this formally.

**Pickup:**
1. Before LF4 attempts to *prove* `busch_effect_gleason` (rather than import), verify: in finite dim, finite additivity + other Def 5.1 clauses imply σ-additivity.
2. If yes, no code change needed. If no, weaken `OperationalPackage.additivity` to a `σ`-additive form over countable effect families.

---

## 7. Outcome specification: ontic-first vs projective-first — **DONE (pre-LF4 Phase 5, 2026-05-18)**

**Status:** Both pickup items delivered in `CsdLean4/LF2/Interface.lean` (Phase 5).

- `SectorData.outcomeOfProjective : {Oep : Set P} → MeasurableSet Oep → D.toOntic.OutcomeRegion` constructs the ontic outcome region with `Ω := D.π ⁻¹' Oep`.
- `SectorData.outcomeOfProjective_preEvent` discharges the correspondence: under the **flow-projection compatibility** hypothesis `h_flow_π : ∀ x, D.π (D.toOntic.Φ x) = D.π x` (CSD's constraint-surface preservation reading — the ontic flow preserves projective rays), the constructor-built outcome's pre-event equals `D.π ⁻¹' Oep` exactly. Callers of `LF1_main_theorem_projective` no longer need to supply `hCorresp` manually for the constructor-built outcome.
- `SectorData.outcomeOfProjective_weight_eq_projectiveWeight` gives the full weight-side identity by composition with `lf1_weight_eq_projective_weight`.

The flow-projection compatibility hypothesis `h_flow_π` is taken as a constructor argument rather than a `SectorData` field; adding it as a field would commit all `SectorData` instances to the constraint-surface reading at v1.x. LF4 instantiations may elect to promote it to a structural field.

All three exports are foundational-axiom-only; `#guard_msgs` regressions in AxiomAudit pin them.

---

## 8. Concrete SigmaSpace / P / G instantiation

**Status:** **Structural part DONE 2026-05-24** (`CsdLean4/LF4/Instance.lean`).
`CSD.LF4.cpSectorData` is the first concrete `SectorData` (`Σ = P = ℂℙ^{N-1}`,
`G = U(N)`, `π = id`, `μL = fubiniStudyMeasure`), proving LF2's abstract
framework is **inhabited** (it never had been). `cp_measure_bridge` holds
**axiom-free** for the instance (foundational triple only; the abstract
`measure_bridge` carries `invariant_measure_uniqueness`). Both AxiomAudit-pinned.

**Honest scope of the base case.** `π = id` ⇒ trivial (point) fibres, bridge
constant `c = 1`. It does *not* reproduce any Born prediction.

**Ambient/fibre finding (2026-05-25) and the preparation-primitive fix.** The
naive "non-trivial fibres via a product `ℂℙ^{N-1} × ℂℙ^{N-1}`" route **fails**:
under the continuous measure bridge `π∗μL = c·μFS`, every single quantum state's
fibre is `μL`-null (`μL(π⁻¹([ψ])) = c·μFS({[ψ]}) = 0`), so a pure-state
preparation cannot be a positive-measure `μL`-conditional. The measure bridge and
positive-measure pure-state preparation are **incompatible on one `Σ`**. This also
means the LF3 `PureSingletPreparation` bundle (carrying `push_dirac` *via* a
`μL`-conditional + the bridge) is **uninhabitable as designed**. Resolution (Paper
A / Σ0, revised): the preparation is a **probability measure**, ambient
`μL`-conditional for mixed states and a **posited fibre measure `μ_[ψ]`** for pure
states (extra ontic structure, not a `μL`-conditional — so no disintegration
machinery is required; `μ_[ψ]` is the trial law directly).

**Lean discharge (Phases 1–3, 2026-05-25):**
- `CSD.LF1.freq_tendsto_of_iid` (`LF1/GeneralFrequency.lean`) — the law-agnostic
  frequency theorem: i.i.d. trials with *any* common law `μp` ⇒ frequencies →
  `(μp O).toReal`. Additive; foundational-triple-only.
- `CSD.LF4.ontic_born_frequency` (`LF4/OnticBorn.lean`) — the **non-vacuous**
  general pure-state ontic Born capstone: composes `freq_tendsto_of_iid` with
  `pure_state_born_weights_of_certainty` to give frequencies → `|⟨ψ,φ⟩|²`.
  Conditional on operational consistency (`OP`, `h_certain`) + the eq-12 bridge
  (`h_bridge`); Born form *derived* via the Busch axiom. Cites
  `[propext, Classical.choice, Quot.sound, busch_effect_gleason]`.

**Migration DONE (2026-05-25).** The LF3 `PureSingletPreparation` bundle has been
re-expressed in the posited-fibre-measure form. It now carries a posited trial law
`μψ : Measure SigmaSpace` (+ `hμψ_prob`) with `PP : LF2.PurePreparation D μψ N` and
`bridge_op_p : μψ((O_region s t).preEvent) = ENNReal.ofReal (OP.p …)` built from `μψ`;
the uninhabitable `μL`-conditional `prepMeasure` is gone. The six chain capstones in
`LF3/Interface.lean` (3 per-sector + 3 joint) now take i.i.d. trials
`X : ℕ → Ω → SigmaSpace` with common law `μψ` (`hlaw : map (X n) Pr = prep.μψ`) and
route through `LF1.freq_tendsto_of_iid` instead of `LF1_main_theorem_ae`, landing on
the raw indicator-sum frequency. `weight_eq_P_st` and all capstones keep their axiom
pins `[propext, Classical.choice, Quot.sound, busch_effect_gleason]`; `ofHypothesis`
stays foundational-triple-only. The `Empirical/CSD/Bell.lean` wrappers and the
`Tests/Examples.lean` smoke tests were updated to the new signature. The bundle now
inhabits the same model as `ontic_born_frequency`: a posited fibre measure pushing to
a Dirac on `[ψ]`, with the continuous measure bridge living on the ambient `μL`
separately — no contradiction.

**Constructor DONE (2026-05-28).** The full `ofKählerPreparation` tranche
landed: a concrete `LF3.PureSingletPreparation` for the singlet on the
non-trivial-fibre compact-Kähler instance `Σ = ℂℙ³ × T²`, with every
load-bearing field discharged as a **theorem**.

The four committed modules:

- `CsdLean4/LF3/Singlet/JointProjector.lean` — `singlet_jointSpinProj_expectation`,
  the genuine Born identity `⟨ψ⁻|Πˢ(a)⊗Πᵗ(b)|ψ⁻⟩ = P_st`, proved from matrix
  entries. Foundational triple.
- `CsdLean4/LF3/Singlet/JointEig.lean` — `singletJointEig s t` (the actual
  normalised projection eigenstate) with `singletJointEig_norm`,
  `singletJointEig_born` (the joint-spin Born identity for genuine eigenvectors),
  `singletJointEig_orthogonal` — all theorems. Foundational triple.
- `CsdLean4/LF4/KahlerInstance.lean` — `kSectorData : SectorData (ℂℙ^{N-1} × T²) …`,
  the first non-trivial-fibre, genuinely compact-Kähler `SectorData`;
  `k_measure_bridge : π∗μL = μFS` (`c = 1`), axiom-free marginal bridge via
  `Measure.fst_prod`. Foundational triple.
- `CsdLean4/LF4/SingletKahler.lean` — `ofKählerPreparation`, the constructor:
  re-index isometry `Fin 2×Fin 2 → Fin 4`, the `AddCircle` arc carving
  (`fibreArc_volume = ENNReal.ofReal ℓ` for `ℓ ∈ [0,1]`), the constant
  representative `rep := singletPsi` (Dirac integration makes the value at
  `ray_point` the only one that matters — no measurable-section rabbit hole),
  the axiom-free `kBridge`, the `MeasurementJointEig` assembly, and
  `bridge_op_p` proved Busch-free via `born_rank_one_direct` +
  `kMuPsi_kRegion` + `kEig_born`. Foundational triple. AxiomAudit-pinned.
- Concrete capstone `ofKählerPreparation_singlet_frequency_convergence`:
  applies `LF3_singlet_frequency_convergence` to the constructed prep,
  giving a non-parametric a.s. statement; cites
  `[propext, Classical.choice, Quot.sound, busch_effect_gleason]`.

Restricted to **generic contexts** `|a·b| < 1` (all four `P_st > 0`);
all Bell-test settings qualify.

The LF3 chain is now **non-vacuous on a genuinely compact-Kähler `Σ`**: the
capstone has a concrete exhibited inhabitant.

**Honest framing (Tier-2, per the 2026-05-25 "correct, not vacuous" call).**
`bridge_op_p` holds because the outcome regions are *carved* to fibre-volume
`P_st`. This realises Paper B's eq-12 (Born = volume ratio) concretely on a
compact-Kähler manifold, but does not *derive* `P_st` from independent
geometry. The Kähler dressing is a faithful realisation, not a derivation.

**Still open (the genuinely hard part):** deriving the outcome regions / the fibre
measure from deterministic dynamics so the Born weights come out *without* the
construction encoding them (the constraint-surface-dynamics content;
Sigma0 §5/§9.5; Papers C/D / TN-series). The capstone is conditional on
operational consistency, which is the legitimate stopping line (no theory
derives its own objects).

**Original pickup notes (for the deeper realisation):**
1. In LF4, take `SigmaSpace := ` a specific phase space (or continue abstract).
2. `P := Projectivization ℂ (EuclideanSpace ℂ (Fin N))` with `[Fintype (Fin N)]`, `[DecidableEq (Fin N)]`.
3. `G := Matrix.specialUnitaryGroup (Fin N) ℂ` (or `Matrix.unitaryGroup` for the full unitary case).
4. Construct the Fubini–Study measure `μFS` as a probability measure on `P` (concretely: via the normalised round measure on the sphere, pushed forward through the quotient `S^{2N-1} → CP^{N-1}`).
5. Verify the invariance / equivariance hypotheses of `SectorData`.

**Depends on:** `Mathlib.LinearAlgebra.Projectivization.Basic`, `Matrix.specialUnitaryGroup` (if available; otherwise construct), the quotient measure theory for compact groups.

---

## 9. Unify `MeasurablePartition` (LF2) with LF1's "intersect full-measure sets" sketch — **DONE 2026-05-29**

**Status: DISCHARGED.** `CSD.LF4.born_frequency_convergence_partition`
(`CsdLean4/LF4/BornFrequencyPartition.lean`, foundational triple,
AxiomAudit-pinned) writes the joint a.e. convergence lemma: for a finite
(`[Countable ι]`) family of measurable outcome regions `region i` with
`(μ (region i)).toReal = b i`, i.i.d. trials give
`∀ᵐ ω, ∀ i, Tendsto (freq i) atTop (nhds (b i))`. Proof is exactly the sketched
`ae_all_iff` (intersect full-measure sets) + `freq_tendsto_of_iid` per index.
Stated law-agnostically (any common law `μ`, à la `freq_tendsto_of_iid`) rather
than via an LF2 `MeasurablePartition`/`TrialModel`, so it applies to the
posited-fibre-law chain and the Kähler instance uniformly. The "Born = ontic
measure" content is the hypothesis `hborn`, discharged for the qubit by
`fs_born_volume_ratio_qubit`; general-`N` awaits the `(N-1)`-barycentric +
Duistermaat–Heckman (carve-out plan, Tranche M).

**Original framing (retained):** LF1's `OutcomeRegion` formalises one measurable region at a time; the joint almost-sure statement for a finite partition is sketched in the LF1 docstring as "apply the theorem once per element and intersect the resulting full-measure sets" but not written as a lemma. LF2's `Weights.lean` defines `MeasurablePartition` as the partition object the LF1 docstring defers. The two are not yet linked.

**Why deferred:** LF1 deliberately avoided introducing a partition type ("a partition type may become necessary at LF2/LF4 for POVM completeness", per the LF1 `Outcomes.lean` docstring). LF2 introduced `MeasurablePartition` for projective-weight normalisation. The link, "given a `MeasurablePartition`, the LF1 joint almost-sure convergence statement follows from per-element applications of `LF1_main_theorem_ae`", was not written because LF1's frequency theorem is for a single region and no LF2/LF3 consumer needed the joint version.

**Pickup:**
1. In LF4, write a lemma `MeasurablePartition.LF1_joint_convergence` consuming an LF2 `MeasurablePartition π_part` and an LF1 `TrialModel` and yielding the joint almost-sure convergence statement: `∀ᵐ ω, ∀ i, Tendsto (T.empiricalFreq (partElement i) · ω) atTop (nhds (partElement i).weightReal)`.
2. The proof is finite-intersection-of-full-measure-sets, exactly as the LF1 docstring sketches. No new mathematics; just write down the lemma.
3. Once written, the LF3 chain capstones that currently apply `LF1_main_theorem_ae` once per `(s, t) ∈ Sign × Sign` can route through this lemma instead.

**Depends on:** nothing structural; LF1 and LF2 already provide all ingredients. This is bookkeeping that LF4 should land before consuming joint-partition statements at scale.

---

## 10. Framework/ extraction candidates (post-CONVENTIONS.md adoption)

**Status:** All current LF1/LF2/LF3 modules are tagged `Category: 3-Local` per `CONVENTIONS.md`. The initial pass classified by current location, not conceptual category. Several modules are conceptually Cat-2 (framework-level, CSD-adjacent but reusable beyond CSD) and should be extracted to `CsdLean4/Framework/` when LF4 needs them in CSD-free form.

This section is a punch list of the specific modules to consider for extraction, surfaced by the 2026-05-18 OpenAI Codex CLI review. Do not bulk-refactor; reclassify a module only when LF4 has a concrete consumer that needs it CSD-free.

### 10.1 `LF2/BornWrapper.lean` — split into Cat-1 and Cat-2

The matrix lemmas (`outerProduct_posSemidef`, `traceForm`, `mul_conj` and related rank-1 matrix identities) are Cat-1: pure linear-algebra facts on `Matrix (Fin N) (Fin N) ℂ`, no CSD content. They belong at `CsdLean4/Mathlib/LinearAlgebra/Matrix/RankOne.lean` (or a similar Mathlib-natural path) eventually.

The structural machinery (`Effect`, `DensityOperator`, `OperationalPackage`, `rankOneEffect`, `rankOneDensity`, `born_quadratic`) is Cat-2: it encodes the operational-package interface and the Born quadratic form for finite-dimensional effect algebras. Any formalisation programme that needs the Born wrapper would consume this; it does not depend on CSD's ontic typicality story.

**Pickup:**
1. Identify which lemmas are pure matrix algebra vs which carry operational-package structure. Most pure-matrix lemmas are at the top of the file; the `Effect`/`DensityOperator`/`OperationalPackage` block starts further down.
2. Move the Cat-1 lemmas to `CsdLean4/Mathlib/LinearAlgebra/Matrix/RankOne.lean` (or appropriate path). Stage as Mathlib upstream candidates.
3. Move the Cat-2 block to `CsdLean4/Framework/OperationalPackage.lean`. Adjust imports in `LF3/Projectors/LF2Interface.lean` and downstream consumers.

### 10.2 `LF3/Setup.lean::BinaryPointerProjectors` + `LF3/Projectors/Core.lean::ProjectorAlgebra`

`BinaryPointerProjectors` is a framework-level pointer-algebra structure (two-element projective decomposition on an inner-product space). `ProjectorAlgebra` is the corresponding four-element structure for the bipartite case. Together with `StrongReadoutCompat` and `LeakageCompat`, these encode the abstract pointer-readout pattern that any measurement-model formalisation would need — they do not depend on Bell singlet content.

**Pickup:**
1. Move `BinaryPointerProjectors` (and its theorems) to `CsdLean4/Framework/Measurement/BinaryPointer.lean`.
2. Move `ProjectorAlgebra`, `StrongReadoutCompat`, `LeakageCompat` to `CsdLean4/Framework/Measurement/ProjectorAlgebra.lean`.
3. Keep `mHat`, `sectorVolume`, and other LF3-specific consumers in `LF3/Projectors/`. They depend on Framework but stay Cat-3.

### 10.3 `LF3/Projectors/TensorModel.lean::TensorEmbedding`

`TensorEmbedding K_A K_B H_SA` is an abstract bipartite tensor-factor interface (per-wing algebra-homomorphism lifts with commuting images). Not Bell-singlet-specific; usable for any bipartite quantum-system formalisation.

`UnitaryTensorEmbedding` is the same pattern at the unitary-equivalence level.

**Pickup:**
1. Move `TensorEmbedding` and `UnitaryTensorEmbedding` (with their construction lemmas `ProjectorAlgebra.ofTensorEmbedding` and `MeasurementUnitary.ofUnitaryTensorEmbedding`) to `CsdLean4/Framework/TensorProduct/BipartiteEmbedding.lean`.
2. If sufficiently general, these could eventually become Cat-1 — the tensor-product-of-CLM machinery they encode is Mathlib-track material. Defer that promotion until they have actually been used by a non-CSD consumer.

### Ordering note

These three extractions are independent. Do them on demand as LF4 produces specific Framework-level consumers, not preemptively. Bulk reclassification risks regressing the axiom-clean / tagged-release stability of LF1-3 without proportionate benefit. The CONVENTIONS.md "initial pass by current location" policy was chosen precisely to avoid that risk.

---

## 11. Self-adjointness convention switch (deferred to Framework extraction)

**Status:** LF3 modules currently state self-adjointness on continuous linear maps via the inner-product equation `∀ x y, inner ℂ (T x) y = inner ℂ x (T y)`. The canonical Mathlib spelling is `IsSelfAdjoint T`.

**Why deferred:** Diagnostic re-audit on 2026-05-18 (against Mathlib at Lean 4.29.0-rc8) confirmed:

- The `Star (H →L[ℂ] H)` instance required for `IsSelfAdjoint T` synthesis lives in a Mathlib section with `[CompleteSpace E]` as a section hypothesis.
- Mathlib does NOT automatically chain `[FiniteDimensional ℂ H] → [CompleteSpace H]` via `FiniteDimensional.proper_real` (the chain exists for `ℝ`-finite-dim but doesn't navigate `ℂ`-finite-dim through the `NormedSpace ℝ ℂ` link in typeclass synthesis).
- Adding `[CompleteSpace H]` as an explicit typeclass argument resolves the issue but cascades to every caller of LF3 structures.

The inner-product-equation spelling avoids the cascade and is mathematically equivalent.

**Pickup (when extracting to `Framework/Measurement/`):**

1. Add `[CompleteSpace K]` to `BinaryPointerProjectors` (and to `K_A`, `K_B`, `H_SA` for the bipartite structures).
2. Replace `selfAdjoint : ∀ x y, inner ℂ (proj s x) y = inner ℂ x (proj s y)` with `selfAdjoint : ∀ s, IsSelfAdjoint (proj s)`.
3. Same pattern for `TensorFactorReadoutAlgebra.hA_selfAdjoint` / `hB_selfAdjoint`, `ProjectorAlgebra.selfAdjoint`, `mHat_isSelfAdjoint`.
4. Update consumers — `IsSelfAdjoint T` unfolds to `T = star T`, equivalent via `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` to `LinearMap.IsSymmetric (T : K →ₗ[ℂ] K)`, from which `inner` form follows by `IsSymmetric` field application.
5. Concrete `Framework/` callers (typically `K = EuclideanSpace ℂ (Fin n)`) get `CompleteSpace` automatically via Mathlib's `EuclideanSpace.instCompleteSpace`.

**Alternative:** wait for Mathlib's instance synthesis to chain `FiniteDimensional ℂ → CompleteSpace`. If that lands, the refactor becomes a no-op rename (`IsSelfAdjoint T` synthesizes without adding `[CompleteSpace _]` arguments).

**Depends on:** the Framework/ extraction (§10) being underway. Standalone refactor is mechanical but cost is the typeclass-argument cascade.

---

## 12. `Projectivization` topology / measure / lift API in Mathlib — **DONE (Groups 1–6, 2026-05-19/2026-05-20)**

**Status:** Identified as a Mathlib gap via the pre-LF4 spike on 2026-05-18 (see `specs/pre-LF4-plan.md` Spike 1). The pre-LF4 option-(b) chain initially scoped a commitment `ProjectiveHilbert N := Projectivization ℂ (EuclideanSpace ℂ (Fin N))` at the LF2 level; the spike found Mathlib has no `TopologicalSpace`, `MeasurableSpace`, or `BorelSpace` instance on `Projectivization` outside the projective-line case (`OnePoint/ProjectiveLine.lean`). The architectural workaround keeps `SectorData.P` abstract and supplies a caller-side `representative : P → EuclideanSpace ℂ (Fin N)` map.

**Group 1 delivered 2026-05-19** in `CsdLean4/Mathlib/LinearAlgebra/Projectivization/Topology.lean` (Cat-1, namespace `Projectivization`, no CSD prefix, strict Mathlib style). Covers items 3.1–3.4 of the `specs/projectivization-plan.md` execution plan:

- `Projectivization.instTopologicalSpace`: explicit forwarding of the quotient topology instance (required because `Projectivization` is a `def`, not `@[reducible]`).
- `Projectivization.continuous_mk'`: continuity of the canonical surjection `{v : V // v ≠ 0} → ℙ K V`.
- `Projectivization.scaleNonzero` + `scaleNonzeroHomeo`: the `Kˣ`-scaling action on the nonzero subtype as a self-homeomorphism (gated on `[TopologicalSpace V] [ContinuousConstSMul K V]`).
- `Projectivization.mk'_preimage_mk'_image`: saturation lemma `mk' ⁻¹' (mk' '' U) = ⋃ a : Kˣ, scaleNonzero a '' U` (the projectivization analogue of `MulAction.quotient_preimage_image_eq_union_mul`).
- `Projectivization.isOpenMap_mk'`: openness of the canonical surjection.
- `Projectivization.isQuotientMap_mk'` + `isOpenQuotientMap_mk'`: quotient-map and open-quotient-map characterisations.

Hypothesis pattern at Group 1: `[DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [ContinuousConstSMul K V]` for the topological-action lemmas (continuity / openness); algebraic infrastructure (`scaleNonzero_mul`, `scaleNonzero_one`, `mk'_preimage_mk'_image`) does not require any topology. No topology on K is needed — `ContinuousConstSMul K V` is purely a property of the `V`-side action.

**Group 2 delivered 2026-05-20** in the same `CsdLean4/Mathlib/LinearAlgebra/Projectivization/Topology.lean` file, under a new `section NormedFiniteDim`. Adopted the `[RCLike K]` scalar-hypothesis option (per plan §7.2): simpler proofs and sufficient for the LF4 critical path. The earlier sections were enclosed in a new `section AlgebraicTopology` so the `[AddCommGroup V]` from the outer variable block does not create an instance diamond with `[NormedAddCommGroup V]` in the new section. Covers items 3.5–3.6:

- `Projectivization.instT2Space`: Hausdorffness via the open-quotient-map criterion `t2Space_iff_of_isOpenQuotientMap` applied to `isOpenQuotientMap_mk'`, reducing T2 to closedness of the K-collinearity relation `{(v, w) | mk' v = mk' w}`. Closedness routes through `LinearIndependent.pair_iff'` + `isOpen_setOf_linearIndependent` (the set of linearly independent pairs is open in finite-dim normed K-modules over `[RCLike K]`).
- `Projectivization.instCompactSpace`: compactness via continuous surjection from the unit sphere. The sphere `Metric.sphere (0 : V) 1` is compact (`isCompact_sphere` + `FiniteDimensional.proper_rclike`); the map `g : sphere → ℙ K V, v ↦ mk K v hv` is continuous; surjectivity uses normalisation `((‖p.rep‖⁻¹ : ℝ) : K) • p.rep` of the representative.
- `Projectivization.isClosed_collinearity_relation`: closedness of the K-collinearity relation, the supporting lemma for T2.

**Measure-core delivered 2026-05-20** in `CsdLean4/Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean` (new file, Cat-1, namespace `Projectivization`). Covers plan items 4.1, 4.3, 4.4, plus a free `SecondCountableTopology` bonus:

- `Projectivization.instMeasurableSpace`: Borel σ-algebra from the quotient topology, gated on `[RCLike K]` + finite-dim normed `V`.
- `Projectivization.instBorelSpace`: witness that the installed measurable space coincides with `borel _` (`rfl`).
- `Projectivization.instMeasurableSingletonClass`: singletons are measurable; T2 (Group 2) + Borel ⟹ closed singletons measurable.
- `Projectivization.measurable_mk'`: the canonical surjection is measurable, via `continuous_mk'.measurable`. Caller supplies `[MeasurableSpace V] [BorelSpace V]` so the source subtype inherits a Borel structure.
- `Projectivization.instSecondCountableTopology`: free consequence of `isQuotientMap_mk'` + `isOpenMap_mk'` + `secondCountable_of_proper`.

**Group 4 + Group 5 delivered 2026-05-20** in the same `MeasureSpace.lean` file:

- `Projectivization.borel_eq_map_mk'`: the coincidence lemma. The Borel σ-algebra on `ℙ K V` equals `MeasurableSpace.map mk' (borel V₀)`. Routes through Mathlib's `Continuous.map_borel_eq` (`Mathlib.MeasureTheory.Constructions.Polish.Basic`), given `PolishSpace V` (automatic from `FiniteDimensional.proper_rclike K V` + `secondCountable_of_proper` + the `Polish.lean:65` instance for separable + completely metrizable) and `PolishSpace {v : V // v ≠ 0}` (via `IsOpen.polishSpace` applied to `isClosed_singleton.isOpen_compl`).
- `Projectivization.lift_measurable`: the **load-bearing user-facing lemma for LF4 §3 + §8**. Lets callers derive measurability of `Projectivization.lift f hf` from measurability of `f` and the scale-invariance hypothesis. Routes through `borel_eq_map_mk'` + `MeasurableSpace.map_def`.
- `Projectivization.measurable_iff_measurable_comp_mk'`: companion characterisation. A function out of `ℙ K V` is measurable iff its precomposition with `mk'` is.

Both `lift_measurable` and `measurable_iff_measurable_comp_mk'` take additional `[MeasurableSpace V] [BorelSpace V]` hypotheses so the source subtype's `Subtype.instMeasurableSpace` coincides with `borel _` via the `Subtype.borelSpace` instance. The `‹BorelSpace ({v // v ≠ 0})›.measurable_eq` bridge inside the proofs handles the conversion.

The §12 API is now feature-complete for LF4 consumption. LF4 §3 + §8 can use `lift_measurable` directly to lift measurable scale-invariant functions on `V \ {0}` to measurable functions on `ℙ K V`, rather than carrying `hrep_meas` as a structural hypothesis at the chain capstone. The pre-LF4 chain (LF3 `PurePreparation` etc.) currently still threads `hrep_meas`; the LF4 instantiation can switch to `lift_measurable` once the concrete `SectorData` is in place.

**Pickup pointer:** see `specs/projectivization-plan.md` for the per-section design plan; `specs/projectivization-plan.md` §6 records the resolved Mathlib infrastructure investigations.

**Why partial:** Building the full quotient-topology + Borel-structure + `Projectivization.lift`-measurability stack for arbitrary `K`, `V` is a multi-day Mathlib contribution. Group 1 (the openness-of-canonical-surjection backbone) is landed; the remaining Groups 2–5 are blocked on a scalar-hypothesis decision and a non-trivial closedness proof.

**Pickup (Cat-1 Mathlib contribution, when scheduled):**

1. ~~Define `TopologicalSpace (Projectivization K V)`.~~ **DONE 2026-05-19 (Group 1).**
1b. ~~T2Space + CompactSpace under `[RCLike K]` + finite-dim normed `V`.~~ **DONE 2026-05-20 (Group 2).**
2. ~~Prove `BorelSpace (Projectivization K V)` for the appropriate `K`-and-`V`-flavoured cases.~~ **DONE 2026-05-20 (measure-core).**
3. ~~Prove `MeasurableSingletonClass (Projectivization K V)`.~~ **DONE 2026-05-20 (measure-core).**
4. ~~Prove `Projectivization.lift_measurable`: if `f : V \ {0} → α` is measurable and `f`-phase-invariant, then `Projectivization.lift f hf : Projectivization K V → α` is measurable.~~ **DONE 2026-05-20** (with the coincidence lemma `borel_eq_map_mk'` + companion `measurable_iff_measurable_comp_mk'`).
5. ~~Land in `CsdLean4/Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean` per CONVENTIONS.md `1-Mathlib` tagging.~~ **DONE 2026-05-20.**

**Effect on pre-LF4 / LF4 work:** Until landed, `SectorData.P` stays abstract and `OperationalPackage.fromPreparation` takes a caller-supplied `rep : P → EuclideanSpace ℂ (Fin N)`. When this lands, LF4 can specialise `P := Projectivization ℂ (EuclideanSpace ℂ (Fin N))` and the `rep` argument resolves to `Projectivization.rep` or similar. No retrofit needed; the abstract API is monomorphic in `P` so any concrete `P` works at instantiation time.

**Depends on:** nothing in CSD; this is a self-contained Mathlib contribution that other projectivization-using formalisations (algebraic geometry, projective representations of Lie groups, etc.) would also benefit from.

## 13. Ontic-isometry ↔ Hilbert-isometry bridge for unitaries (added 2026-05-21, generalised 2026-05-21)

**Status:** load-bearing, externally supplied, undischarged.

Originally framed for cloning (§13.1 below); generalised to arbitrary
N-qubit unitaries when the Tranche 1 Tier A gate work introduced
`Empirical.CSDBridge.Gates.CSDUnitaryBundle` (§13.2 below). The two
sub-items share a discharge route; LF4 closes both simultaneously.

### 13.1 Cloning case (original framing)

Carried by `Empirical.CSDBridge.NoCloning.CSDCloningBundle` in
`CsdLean4/Empirical/CSD/NoCloning.lean`. Specifically: a
measure-preserving π-equivariant flow on `Σ × Σ → Σ × Σ` (the ontic
operation hypothetically realising a cloning unitary) induces a
Hilbert-space isometry on the tensor space `Htensor`.

### 13.2 General N-qubit case (added 2026-05-21 for Tranche 1 Tier A)

Carried by `Empirical.CSDBridge.Gates.CSDUnitaryBundle` in
`CsdLean4/Empirical/Gates/Framework.lean`. For any `N`-qubit unitary
`U` on `H_n = EuclideanSpace ℂ (Fin (2^N))`, a measure-preserving
π-equivariant flow on `Σ^N → Σ^N` induces a Hilbert-space isometry
on `H_n` that realises the projective action of `U`.

This is the generalisation of §13.1 from the cloning tensor structure
to arbitrary unitaries. The 1-qubit case (Hadamard, phase gates) is
the simplest instance; the 2-qubit case (CNOT, SWAP, CZ) generalises
the cloning tensor `Htensor` to arbitrary 4-dimensional unitaries;
the 3-qubit case (Toffoli, Fredkin) extends to `Σ^3`.

**Claim:** Under a concrete Kähler `SectorData` instantiation, a
measure-preserving π-equivariant flow on `Σ × Σ → Σ × Σ` (the ontic
operation hypothetically realising a cloning unitary) induces a Hilbert-
space isometry on the tensor space `Htensor` (preservation of the inner
product). Equivalently: the projective pushforward of the ontic flow is
a Hilbert-space unitary up to phase, and tensor structure transfers
across the bridge.

**Why load-bearing.** The CSD-side no-cloning theorem
(`no_csd_cloning_bundle`) reduces to the QM-side Wootters-Zurek result
(`Empirical.QM.NoCloning.no_cloning_two_state`) only via this bridge:
the bundle's measure-preservation + π-equivariance + cloning identities
yield an *ontic* operation matching the cloning recipe, but to invoke
the QM theorem we need a *Hilbert-space isometry* `U : Htensor → Htensor`
with `⟨U x, U y⟩ = ⟨x, y⟩`. Inner-product preservation does not follow
from measure-preservation + π-equivariance alone; it needs the concrete
ontic-to-Hilbert lift that the Kähler instantiation supplies.

**Discharge in principle.** Under the concrete Kähler `SectorData` from
§8, the projective pushforward of a measure-preserving symplectomorphism
of Σ is determined by its action on projective rays. For the cone over
the projective ray, the symplectomorphism lifts to a complex-linear
(unitary-up-to-phase) action on the tangent Hilbert space. The induced
isometry on `Htensor` then follows from the tensor product of the
single-system lifts.

**Discharge prerequisites:**
- §2 (preparation-to-Hilbert correspondence) — **DONE for pure-state classes** (2026-06-08;
  see §2). Not the real blocker.
- §7 (projective-first outcomes, DONE).
- §8 (concrete Kähler `SectorData`).
- The real blocker: a **Wigner / Fubini–Study rigidity lemma** — "a transition-probability-
  preserving self-map of `ℙ ℂ E` is induced by a unitary" (equivalently
  `Isom(ℂℙⁿ) = PU(n+1)`; the cone-of-ℂℙⁿ symplectomorphism lifts to `U(n+1)` up to phase).
  Not in Mathlib; genuinely multi-session.
  - **Foundation + forward direction LANDED 2026-06-08**
    (`CsdLean4/Mathlib/LinearAlgebra/Projectivization/TransitionProbability.lean`): the
    `transProb` API, the realisability half `transProb_smul_unitary` (`U(N) ⊆`
    transition-preservers), and the converse hooks `transProb_eq_one_iff` /
    `transProb_eq_zero_iff` (equality + orthogonality characterisations). Foundational-
    triple-only, AxiomAudit-pinned, Tier-A audited SOUND.
  - **Converse still OPEN** (the rigidity theorem proper). Decomposition:
    - **(1) DONE 2026-06-08** (`Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean`):
      the `TransProbPreserving` predicate, `.injective` (Wigner "no information loss", derived
      from the predicate alone), the `U(N) → TransProbPreserving` realisability inclusion,
      orthogonality preservation (`.orthogonal`, `.inner_rep_eq_zero_iff`), and
      orthonormal-frame preservation (`.pairwise_orthogonal`,
      `orthonormalBasis_pairwise_orthogonal`). Foundational-triple-only, AxiomAudit-pinned,
      Tier-A audited SOUND (predicate satisfiable AND restrictive).
    - **(2) PARTIAL.** Extract a (semi)linear map agreeing with `f`. Sub-decomposition:
      - **(2a) DONE 2026-06-09** (`WignerRigidity.lean`): the image of an ONB is an ONB frame —
        `imageVec` (unit-normalised image-ray reps), `imageVec_orthonormal` (orthonormality
        routed through `hf.inner_rep_eq_zero_iff`, so `hf` is load-bearing), `imageOrthonormalBasis`
        (via `OrthonormalBasis.mk` + span-from-cardinality), `mk_imageOrthonormalBasis` (its
        i-th ray = the image ray `f (mk (b i))`).
      - **(2b) DONE 2026-06-09** (`WignerRigidity.lean`): the candidate UNITARY — `candidateUnitary
        hf b := b.equiv (imageOrthonormalBasis hf b) (Equiv.refl _) : E ≃ₗᵢ[ℂ] E`, with headline
        `candidateUnitary_agrees_on_basis : mk (candidateUnitary (b i)) = f (mk (b i))`. Tier-A
        audited SOUND: agreement is PER-BASIS-POINT only (not full agreement — the central
        no-over-claim check), `candidateUnitary` is a genuine isometry equiv. Both pinned.
      - **(2c) frame reduction DONE 2026-06-09** (`WignerRigidity.lean`); the residual
        normal-form lemma is the OPEN crux. Landed via the direct isometry route (no
        `≃ₗᵢ ↔ Matrix.unitaryGroup` bridge needed): `projMap (e : E ≃ₗᵢ[ℂ] E)` (projective map
        of an isometry equiv) + `transProb_projMap` (isometry preserves `transProb`, subsuming
        the matrix-unitary case) + `projMap_transProbPreserving` + `TransProbPreserving.comp`,
        giving `reducedMap hf b := projMap (candidateUnitary hf b).symm ∘ f` with
        `reducedMap_transProbPreserving` and `reducedMap_fixes_basis`
        (`reducedMap hf b (mk (b i)) = mk (b i)`). Tier-A audited SOUND, **no over-claim**:
        fixing the basis rays does NOT make `reducedMap` the identity — the diagonal-phase
        freedom is genuine. So the whole converse now reduces to ONE residual lemma:
        **a `TransProbPreserving` map fixing every basis ray is the identity on rays**, proved
        by extracting the phase cocycle from the superposition rays `mk(bᵢ+bⱼ)` and showing it
        trivial. This is the genuine research-grade crux.
      - **(2d) OPEN.** Semilinearity / agreement assembly downstream of the normal-form lemma.
      - **Audit watch (highest-value, per the step-2c audit):** the residual normal-form proof
        must DERIVE its conclusion from the overlap/cocycle data + the Kähler complex structure;
        it must NOT take ℂ-linearity (or `f` = a fixed unitary) as a hypothesis — a smuggled
        linearity input is the one way this converse could become circular.
    - **(3) OPEN.** Rule out the antiunitary branch via the Kähler complex structure.
    **Audit watch (per the foundation + step-1 audits):** step (3) must DERIVE ℂ-linearity,
    not assume it as a hypothesis (smuggled linearity would beg the question — attempt to
    inhabit the step-(2)/(3) hypotheses with an antiunitary witness to check).
    Two completion routes are a posture decision for the maintainer: a full sorry-free proof
    (multi-session; preserves the one-axiom posture — the chosen route, in progress), or a
    busch-style "library-debt" axiom `wigner_fs_rigidity` (closes §13 now but reintroduces a
    second imported axiom).
  - This step is additionally coupled to **D1**: the "ontic flow realising the unitary" in
    the §13 hypothesis is itself a `Φ≠id` dynamics, the open frontier.

**Effect on pre-LF4 / LF4 work:** Pre-LF4, `CSDCloningBundle` carries
`bridge_isometry` as a structural field. Callers attempting to
construct a `CSDCloningBundle` for any specific (ψ, φ, blank) must
supply the isometry hypothesis explicitly. `no_csd_cloning_bundle`
then shows the bundle is uninhabitable for non-orthogonal non-equal
unit ψ, φ. Post-LF4, the `bridge_isometry` field becomes provable from
the concrete Kähler `SectorData`'s pushforward properties, eliminating
the need for explicit caller-supplied isometry.

**Depends on:** §2, §7, §8 (load-bearing); §10 if the bridge is
extracted as Cat-2 Framework infrastructure.

**Audit:** Listed in `BRIDGE-OBLIGATIONS.md` §2.2 against the
`bridge_isometry` field. Per the bridge-discipline rules at the top
of this file, this entry was added in a separate PR before the
`Empirical/CSD/NoCloning.lean` file landed.

### 13.3 Deletion case (added 2026-05-28)

Carried by `Empirical.CSDBridge.NoDeleting.CSDDeletingBundle` in
`CsdLean4/Empirical/CSD/NoDeleting.lean`. Logical dual of §13.1:
a measure-preserving π-equivariant flow on `Σ × Σ → Σ × Σ`
hypothetically realising a Pati-Braunstein 2000 deletion isometry
(`U(tensor ψ ψ) = tensor ψ blank`) induces a Hilbert-space isometry
on `Htensor`. Identical realisability content to §13.1, applied to
the deletion direction instead of the cloning direction.

**Why load-bearing.** Same as §13.1: the CSD-side no-deleting theorem
(`no_csd_deleting_bundle`) reduces to the QM-side Pati-Braunstein result
(`Empirical.QM.NoDeleting.no_universal_deleter_of_witness`) only via
the ontic-to-Hilbert isometry lift the Kähler instantiation supplies.

**Discharge:** identical to §13.1 (cone-of-CPⁿ symplectomorphism →
unitary-up-to-phase lemma). One single discharge addresses §13.1, §13.2
*and* §13.3 simultaneously, since all three are instances of the same
"ontic flow on `Σ^k` induces Hilbert-space isometry" content with
different downstream identities (cloning, general unitary, deletion).

**Effect on pre-LF4 / LF4 work:** Pre-LF4, `CSDDeletingBundle` extends
`CSDBridge.Context D` and carries the same QM-side fields as
`CSDCloningBundle` with `clone_ψ/φ` swapped for `delete_ψ/φ`.
`no_csd_deleting_bundle` is uninhabitable for non-orthogonal non-equal
unit `ψ, φ`. Post-LF4, the realisability is provable from the concrete
Kähler `SectorData`'s pushforward properties.

**Depends on:** §13.1 (same proof structure), §2 + §7 + §8 + the
cone-symplectomorphism lemma.

**Audit:** Listed in `BRIDGE-OBLIGATIONS.md` §2.3 (deletion row).

---

## 14. Observable correspondence (added 2026-05-28)

**Status:** **PROJECTOR-LEVEL DISCHARGE DONE 2026-05-28**
(`CsdLean4/LF4/SingleQubitKahler.lean`). Full self-adjoint case via
spectral decomposition remains; the projector case suffices for the
Stern-Gerlach LF3-chain lift, which is the concrete payoff.

New realisability obligation, distinct from §13. Carried by
`Empirical.CSDBridge.Uncertainty.CSDUncertaintyBundle` in
`CsdLean4/Empirical/CSD/Uncertainty.lean` and four other §14-dependent
CSD bridge bundles (SternGerlach, SuperdenseCoding's Bell-projector
half, MerminPeres, Hardy).

### 14.1 Projector-level discharge (DONE 2026-05-28)

`CsdLean4/LF4/SingleQubitKahler.lean` discharges §14 for **single-qubit
projector observables on the `|+z⟩` preparation**:

- `sg_observable_correspondence (s : Sign) (a : DetectorSetting)`:
  `inner ℂ zPlusVec (toEuclideanLin (spinProj s a) zPlusVec)
       = ((sgMuPsi (sgRegion s a)).toReal : ℂ)`.
  Both sides equal `sgBorn s a := (1 + s · a_z)/2`; the Hilbert side
  via the `(0,0)` entry of `spinProj s a`, the ontic side via the
  carving identity `sgMuPsi_sgRegion`. Foundational triple only.

- `sg_frequency_convergence (s a) (X) (hX) (hlaw) (hindep)`: the
  **non-vacuous LF3-chain Stern-Gerlach capstone**. For i.i.d. trials
  with the posited fibre law `sgMuPsi`, empirical frequencies converge
  a.s. to `(1 + s · a_z)/2`. Parallel to
  `ofKählerPreparation_singlet_frequency_convergence` at `N = 4`, but
  at the single-qubit level (`N = 2`) and via direct
  `freq_tendsto_of_iid` + carving (no Busch routing, so the chain is
  Busch-free at this layer; the LF3 singlet chain still routes via
  Busch through `pure_state_born_weights_of_certainty`).

The Stern-Gerlach bridge bundle in `Empirical/CSD/SternGerlach.lean`
is now non-vacuous in the strong sense: the LF3 chain has a concrete
exhibited inhabitant. AxiomAudit-pinned (both theorems, foundational
triple).

### 14.2 General self-adjoint case (DONE 2026-05-28 — Hilbert + ontic + integration)

The projector discharge lifts to arbitrary bounded self-adjoint
observables by spectral decomposition `A = ∑ λᵢ Pᵢ`.

**First step beyond projectors (DONE 2026-05-28).** The Pauli observable
`σ·a` has two-eigenvalue spectral decomposition `(+1)·spinProj(+a) +
(−1)·spinProj(−a)`. Its ontic counterpart is the signed indicator
`pauliDotOntic a σ := 2·1_{R_+(a)}(σ) − 1` — `+1` on the `+`-outcome
region, `−1` everywhere else (the `−`-outcome region by measurable
partition). The integral identity

```
∫ pauliDotOntic a dμψ = a_z = ⟨zPlus, (toEuclideanLin (pauliDot a)) zPlus⟩
```

is `pauliDot_observable_correspondence` in `CsdLean4/LF4/SingleQubitKahler.lean`.
Foundational triple; AxiomAudit-pinned. This demonstrates the spectral-
decomposition pattern at the simplest non-projector case (two
eigenvalues, signed indicator).

**General N×N Hilbert-side spectral identity (DONE 2026-05-28).** The
Hilbert-side spectral expansion

```
⟨ψ, A ψ⟩ = ∑ᵢ (λᵢ : ℂ) · ‖⟨uᵢ, ψ⟩‖²
```

for arbitrary Hermitian `A : Matrix (Fin N) (Fin N) ℂ` and any state
`ψ : EuclideanSpace ℂ (Fin N)` is `hermitian_inner_spectral_expansion`
in `CsdLean4/LF4/SpectralExpansion.lean` (real-valued form
`hermitian_inner_spectral_expansion_re` for variance / uncertainty
consumers). Proof route: Parseval on the eigenbasis via
`OrthonormalBasis.sum_inner_mul_inner` + self-adjointness via
`Matrix.isHermitian_iff_isSymmetric` + eigenvalue equation via
`LinearMap.IsSymmetric.apply_eigenvectorBasis` (bridged to the
Matrix-level reindexed eigenbasis as Mathlib's `Matrix.Spectrum`
does internally). Foundational triple; AxiomAudit-pinned.

**General N×N ontic-side carving (DONE 2026-05-28).** The Hilbert-side
spectral expansion is composed with a genuine N-arc fibre partition in
`CsdLean4/LF4/SpectralCarving.lean`:

- **Phase A**: `fibreShiftedArc c ℓ := (equivIoc 1 0)⁻¹ (Ioc c (c+ℓ))` — a
  shifted-anchor primitive that fixes the nesting issue of the original
  `fibreArc ℓ = (0, ℓ]`. Measurability, volume `= ofReal ℓ` for
  `[c, c+ℓ] ⊆ [0,1]`, and pairwise disjointness via `Set.Ioc_disjoint_Ioc_of_le`.

- **Phase B**: `cumWeights w : Fin (N+1) → ℝ` via `Finset.filter`. Clean
  proofs of `cumWeights_zero`, `cumWeights_succ_castSucc` (the recursive
  step), `cumWeights_last` (`= ∑ w`), monotonicity, and the carving bound
  `cumWeights w i.castSucc + w i ≤ 1` when `∑ w ≤ 1`.

- **Phase C**: `spectralRegion (w : Fin N → ℝ) (i : Fin N) : Set (KSigma M)`
  with measurability, `diracProd_spectralRegion` (the per-region carving
  identity), and `spectralRegion_pairwise_disjoint`. The N regions are
  genuinely disjoint (unlike the existing Hardy four-region setup, where
  three of the four arcs are zero-length and disjointness is vacuous).

- **Phase D**: `bornWeights hA ψ i := ‖⟨uᵢ, ψ⟩‖²` (with `Parseval` /
  `OrthonormalBasis.sum_sq_norm_inner_right` giving `∑ = ‖ψ‖²`),
  `spectralOntic := ∑ᵢ λᵢ · 1_{R_i}` with measurability and integrability,
  and the headline
  `integral_spectralOntic_eq_inner_re : ∫ spectralOntic dμψ = re ⟨ψ, A ψ⟩`
  for any Hermitian `A`, unit `ψ`, and any base ray `p₀ : CPN M`. Composes
  `diracProd_spectralRegion` (per-region carving) with
  `hermitian_inner_spectral_expansion_re` (Hilbert spectral expansion)
  through `integral_finset_sum`, `integral_indicator_one`,
  `measureReal_def`, and `ENNReal.toReal_ofReal`.

The headline at Phase D is the **§14.2 ontic-Hilbert observable
correspondence at the integration level**, fully discharged on the
existing Kähler instance for any concrete Dirac × T² preparation.
Foundational triple; AxiomAudit-pinned (`fibreShiftedArc_volume`,
`diracProd_spectralRegion`, `integral_spectralOntic_eq_inner_re`).

Tier-2 honesty: the N-arc fibre partition is carved to the Born weights
**by construction** (the i-th arc has length `‖⟨uᵢ, ψ⟩‖²` because the
cumulative-sum boundaries are defined that way). What the integration
theorem proves is that this construction, fed through Mathlib's measure-
theoretic integral and combined with the Hilbert-side spectral expansion
(genuine spectral content), recovers `re ⟨ψ, A ψ⟩` via independent routes
— ontic via partition sum + Lebesgue integral, Hilbert via Parseval +
self-adjointness + eigenvalue equation. Both ends compute the same value
through structurally distinct machinery.

**Variance identity (DONE 2026-05-28).** `CsdLean4/LF4/SpectralVariance.lean`
delivers both the Hilbert-side spectral form and the ontic ↔ Hilbert
correspondence at the integration level:

- `inner_eigenvector_image` (extracted helper): `⟨uᵢ, A ψ⟩ = (λᵢ : ℂ) · ⟨uᵢ, ψ⟩`
  for Hermitian `A` and eigenvector `uᵢ`. Used by `hilbert_norm_sq_apply_hermitian`
  and exported for downstream consumers.
- `hilbert_norm_sq_apply_hermitian`: `‖A ψ‖² = ∑ᵢ λᵢ² · bornWeights i` via
  `OrthonormalBasis.sum_sq_norm_inner_right` + `inner_eigenvector_image`.
- `spectralVariance := ∑ᵢ (λᵢ − ⟨A⟩)² · bornWeights i` (the spectral form).
- `spectralVariance_nonneg` (trivially, sum of nonneg terms).
- `spectralVariance_eq_hilbert_norm_sq_diff` (under `‖ψ‖ = 1`):
  `spectralVariance = ‖A ψ‖² − ⟨A⟩²`. Composes `hilbert_norm_sq_apply_hermitian`
  + `hermitian_inner_spectral_expansion_re` + `bornWeights_sum_eq_one` +
  algebraic expansion `(λᵢ − μ)² = λᵢ² − 2λᵢμ + μ²` distributed over the sum.
  For self-adjoint `A`, `‖A ψ‖² = re ⟨ψ, A² ψ⟩`, so this matches the standard
  QM `Var = ⟨A²⟩ − ⟨A⟩²`.
- `spectralOnticCentered := ∑ᵢ (λᵢ − ⟨A⟩)² · 1_{R_i}` (ontic centered observable).
- `integral_spectralOnticCentered_eq_variance` (under `‖ψ‖ = 1`, headline):
  `∫ spectralOnticCentered dμψ = spectralVariance hA ψ`.
- `integral_spectralOnticCentered_eq_hilbert_norm_sq_diff` (composite headline):
  `∫ spectralOnticCentered dμψ = ‖A ψ‖² − ⟨A⟩²` — the **ontic variance ↔
  Hilbert variance correspondence at the integration level**.

Tier-2 honesty unchanged: `spectralVariance` is *defined* as the spectral
form. The Hilbert ↔ spectral identity is a genuine algebraic theorem;
the ontic ↔ spectral identity is a genuine measure-theoretic theorem
(via the Phase C carving + integral linearity). Both ends meet at the
same value through structurally distinct machinery. The squared-indicator
identity `(A_ontic − ⟨A⟩)² ↔ ∑ᵢ (λᵢ − ⟨A⟩)² · 1_{R_i}` is sidestepped
by defining `spectralOnticCentered` directly; the a.e. equivalence to
`(spectralOntic − ⟨A⟩)²` follows on the full-measure region `⋃ᵢ R_i`
(under `‖ψ‖ = 1`), but is not currently formalised since the integration
identity needs only the direct form.

AxiomAudit-pinned (4 new pins: `hilbert_norm_sq_apply_hermitian`,
`spectralVariance_eq_hilbert_norm_sq_diff`, `integral_spectralOnticCentered_eq_variance`,
`integral_spectralOnticCentered_eq_hilbert_norm_sq_diff`). All
foundational triple.

**Robertson uncertainty on the Kähler instance (DONE 2026-05-28).**
`CsdLean4/LF4/UncertaintyKahler.lean` connects the variance identity
above to `Empirical/QM/Uncertainty.lean`'s Robertson bound. For any
Hermitian `A, B : Matrix (Fin N) (Fin N) ℂ` and unit
`ψ : EuclideanSpace ℂ (Fin N)`, on any Kähler instance `KSigma M` with
preparation `(Dirac p₀) × vol_T²`:

- `variance_eq_norm_sq_sub_expectation_sq` (generic): for symmetric `T`
  and unit `ψ`, `Var T ψ = ‖T ψ‖² − (re ⟨ψ, T ψ⟩)²`. Proves the
  standard QM `Var = ⟨A²⟩ − ⟨A⟩²` via `norm_sub_sq` + `RCLike.mul_conj`
  + self-adjoint expectation real (`Complex.conj_eq_iff_im`).
- `QM_variance_eq_spectralVariance` (the bridge):
  `Empirical.Uncertainty.variance A.toEuclideanLin ψ = spectralVariance hA ψ`.
- `QM_variance_eq_integral_spectralOnticCentered` (the composition):
  `Empirical.Uncertainty.variance A.toEuclideanLin ψ
    = ∫ spectralOnticCentered hA ψ dμψ`.
- **`kahler_robertson_ontic_variance`** (the headline ontic-variance
  Robertson bound): for Hermitian `A, B` and unit `ψ`,
  ```
  (∫ spectralOnticCentered hA ψ dμψ) · (∫ spectralOnticCentered hB ψ dμψ)
    ≥ ¼ ‖⟨ψ, [A.toEuclideanLin, B.toEuclideanLin] ψ⟩‖²
  ```
  on the Kähler instance. The LHS is purely ontic-side (per-observable
  integrals of the centered indicator-sum); the RHS is the Hilbert
  commutator overlap (the Robertson lower bound, QM-side). Composes
  `QM_variance_eq_integral_spectralOnticCentered` (applied to A and B)
  with `Empirical.Uncertainty.robertson_uncertainty`.

This is the **LF4 §14.2 unlock for the Uncertainty bundle**. Pre-LF4
`csd_robertson_uncertainty` was a transport theorem (any Hilbert state
satisfies Robertson). With `kahler_robertson_ontic_variance`, the
**physical content** (ontic variances satisfy the Robertson bound,
not just Hilbert variances) is realisable on the Kähler instance for
any concrete pair of bounded Hermitian observables.

Two additional AxiomAudit pins (`QM_variance_eq_spectralVariance` and
`kahler_robertson_ontic_variance`); both foundational triple.

**First concrete witness (DONE 2026-05-28).** `CsdLean4/LF4/PauliRobertson.lean`
instantiates `kahler_robertson_ontic_variance` for the canonical textbook
example — Pauli observables `σ_x, σ_y` on the spin-up state `|0⟩`:

- `pauliX`, `pauliY` defined as raw `Matrix (Fin 2) (Fin 2) ℂ`.
- `pauliX_isHermitian`, `pauliY_isHermitian` via direct entry-wise
  `Matrix.conjTranspose_apply` + `Complex.conj_I` + `star_neg`.
- `pauliX_apply_zPlusVec : pauliX · |0⟩ = |1⟩`, `pauliX_apply_zMinusVec : |1⟩ → |0⟩`.
- `pauliY_apply_zPlusVec : pauliY · |0⟩ = i·|1⟩`, `pauliY_apply_zMinusVec : |1⟩ → -i·|0⟩`.
- Expectations `⟨0,σ_x 0⟩ = ⟨0,σ_y 0⟩ = 0` via `zPlus_expectation` +
  matrix `(0,0)` entries.
- Norm-squareds `‖σ_x|0⟩‖² = ‖σ_y|0⟩‖² = 1` via `‖|1⟩‖ = 1` and `‖i‖ = 1`.
- Spectral variances `spectralVariance hA |0⟩ = 1` for both, via
  `spectralVariance_eq_hilbert_norm_sq_diff`.
- Ontic integrals `∫ spectralOnticCentered hA |0⟩ dμψ = 1` for both, via
  `integral_spectralOnticCentered_eq_variance`.
- Commutator action `[σ_x, σ_y] |0⟩ = 2i·|0⟩` via two-step composition
  (σ_x σ_y |0⟩ = i|0⟩, σ_y σ_x |0⟩ = -i|0⟩, subtract).
- Commutator inner `⟨0, [σ_x, σ_y] 0⟩ = 2i` via `inner_smul_right` +
  `inner_self_eq_norm_sq_to_K` + `‖|0⟩‖ = 1`.
- Commutator norm-squared `‖2i‖² = 4` via `Complex.norm_I` + `norm_mul`.
- **HEADLINE** `pauli_xy_robertson_saturation`:
    `(∫ spectralOnticCentered σ_x |0⟩ dμψ) · (∫ spectralOnticCentered σ_y |0⟩ dμψ)
      = (1/4) · ‖⟨0, [σ_x, σ_y] 0⟩‖² = 1`.
  Both sides equal `1`; the inequality of `kahler_robertson_ontic_variance`
  is saturated to equality. `|0⟩` is a minimum-uncertainty state for the
  pair `(σ_x, σ_y)` — the canonical textbook example, realised at the
  ontic level on the Kähler instance.

AxiomAudit pin: `pauli_xy_robertson_saturation` (foundational triple).

**Parametric Robertson on |0⟩ (DONE 2026-05-28).**
`CsdLean4/LF4/PauliDotRobertson.lean` extends `pauli_xy_robertson_saturation`
to arbitrary unit-vector axes `â, b̂` (the `DetectorSetting` constraint).
The Robertson bound becomes a **geometric inequality** between component
polynomials:

  `(1 − a_z²)(1 − b_z²) ≥ (a_x b_y − a_y b_x)²`.

Both sides are explicit polynomials in `â.vec 0, â.vec 1, â.vec 2`
(similarly for `b̂`). Equality holds when both axes lie in the xy-plane
and are perpendicular — `pauli_xy_robertson_saturation` recovered as
the special case.

Key lemmas:
- `pauliDot_zPlus_norm_sq â : ‖(σ·â).toEuclideanLin · |0⟩‖² = 1` via
  entry-wise computation of `pauliDot a · zPlusVec.ofLp` (entries
  `(a_z, a_x + i·a_y)`) + `Complex.normSq_apply` + the unit-vector
  property `a.sum_sq_components_eq_one`.
- `pauliDot_zPlus_spectralVariance â : spectralVariance _ |0⟩ = 1 − a_z²`
  via `spectralVariance_eq_hilbert_norm_sq_diff` + `zPlus_expectation`
  + `pauliDot[0,0] = ((a.vec 2 : ℝ) : ℂ)` + `RCLike.ofReal_re`.
- `pauliDot_zPlus_ontic_integral â p₀ : ∫ spectralOnticCentered · dμψ
  = 1 − a_z²` via `integral_spectralOnticCentered_eq_variance`.
- `toEuclideanLin_mul_apply` (private bridge):
  `(A * B).toEuclideanLin v = A.toEuclideanLin (B.toEuclideanLin v)`
  via `Matrix.mulVec_mulVec`.
- `pauliDot_commutator_matrix_00 â b̂ : (pauliDot â * pauliDot b̂
  − pauliDot b̂ * pauliDot â) 0 0 = 2i (a_x b_y − a_y b_x)` via
  `Matrix.mul_apply` + `Fin.sum_univ_two` + `push_cast; ring`.
- `pauliDot_commutator_inner_zPlus â b̂` (Module.End form): bridge
  via `Module.End.mul_apply` + `← toEuclideanLin_mul_apply` + `map_sub`,
  then `zPlus_expectation` + matrix-entry lemma.
- `pauliDot_commutator_inner_zPlus_norm_sq â b̂ : ‖2i(a_x b_y − a_y b_x)‖²
  = 4(a_x b_y − a_y b_x)²` via factoring out `Complex.I` + `Complex.norm_I
  + Complex.norm_real`.
- **HEADLINE** `pauliDot_robertson_zPlus â b̂ p₀`:
    `(1 − a_z²)(1 − b_z²) ≥ (a_x b_y − a_y b_x)²`
  via `kahler_robertson_ontic_variance` + rewrites + `linarith`.

AxiomAudit pin: `pauliDot_robertson_zPlus` (foundational triple).
Both `pauli_xy_robertson_saturation` (the saturated special case at
`â = x̂, b̂ = ŷ`) and `pauliDot_robertson_zPlus` (the parametric family)
are now in place, giving the spin-½ Robertson uncertainty bound at both
endpoints — the canonical textbook saturation and the geometric
parametric form.

---

### 14 — original framing (pre-discharge)

**Claim.** A self-adjoint Hilbert operator `A : H →ₗ[ℂ] H` arises as the
Hilbert-space lift of a measurable function `A_ontic : Σ → ℝ`, with the
expectation identity `⟨ψ, A ψ⟩ = ∫ A_ontic dμψ` whenever `ψ` is the
Hilbert-space lift of the CSD preparation `μψ`. The variance identity
`Var_ψ(A) = Var_{μψ}(A_ontic)` follows.

**Why distinct from §13.** §13.x is about *isometries / unitaries*
realised as measure-preserving π-equivariant Σ-flows. §14 is about
*self-adjoint operators* realised as measurable Σ-valued functions
(the ontic counterpart of observables). These are different kinds of
mathematical object (operator on `H` vs function on `Σ`) and the
discharge routes differ accordingly.

**Why load-bearing.** The CSD-side Robertson uncertainty
(`csd_robertson_uncertainty`) reduces to the QM-side `robertson_uncertainty`
by direct field extraction, but the *physical content* (ontic
variances satisfy the bound, not just Hilbert variances) requires the
observable correspondence to relate Hilbert variance to ontic variance.

**Discharge in principle.** Under the concrete Kähler `SectorData` from
§8, the observable correspondence is realised by the Hilbert-space
lift of `effectProjFn` (the volume-ratio effect function) and its
self-adjoint analog for unbounded operators. For bounded self-adjoint
`A`, the corresponding ontic function is `A_ontic : Σ → ℝ` defined via
`A_ontic σ := ⟨rep(π σ), A rep(π σ)⟩` (the expectation in the lifted
state at the projective ray, taking the real part). The
expectation-integral identity then follows from `OP.p = ∫ effectProjFn`
applied to the spectral decomposition of `A`.

**Discharge prerequisites:**
- §8 (concrete Kähler `SectorData`) — DONE.
- §2 (preparation-to-Hilbert correspondence, PARTIAL).
- Spectral-theorem infrastructure for bounded self-adjoint operators on
  finite-dim complex inner-product spaces (Mathlib has this for
  matrices via `Matrix.IsHermitian.spectralTheorem`; lifts to
  `Module.End` exist for the finite-dim case).

**Effect on pre-LF4 work:** Pre-LF4, `CSDUncertaintyBundle` carries
the Hilbert state + observables and the realisability is prose-only.
`csd_robertson_uncertainty` is a transport-only theorem proving the
QM-side Robertson bound for any bundle. Post-LF4, the observable
correspondence is provable from the concrete `SectorData`'s spectral
machinery + the lifted preparation, and the ontic variance identity
becomes a theorem rather than a prose claim.

**Depends on:** §8 (done), §2 (partial), spectral-theorem infrastructure.

**Audit:** Listed in `BRIDGE-OBLIGATIONS.md` §2.3.1.

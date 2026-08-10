# C1 correction and formal closure: implementation plan

Created 2026-08-10, revised the same day against the author's review of the work
order. Baseline commit `f5384515724754d4035d9feb2326e11e1ce8afb9` (verified by
`git rev-parse HEAD` after `git pull --ff-only`).

A correction and closure exercise, not a research expansion. No axioms, no
`sorry`, no assumptions disguised as theorems.

## 0. Premises verified before planning

Checked against the tree at the baseline commit. All hold: the false claim in
`LF3/ContextMap.lean` (line 52, and the module category line 13); `hgen` on
`localDeisolation_pointer_volume` (line 297); `SigmaLayer/TheoremTargets.lean`
exists; all 16 named theorems exist. `docs/C1-FORMAL-SUPPORT.md` and
`Tests/AxiomAudit/C1.lean` are absent, as expected.

Four findings that change the plan:

**F1. `ContextIndexedOutcomeMaps` has no downstream code users.** The only hit
outside `ContextMap.lean` is a prose mention in `LF5/Capstone.lean:59`. So
deprecation is viable and preferred over maintaining two interfaces; only that
one docstring needs updating.

**F2. The volume engine is already unconditional.**
`localDeisolation_pointer_volume` routes through
`povm_born_eq_dilated_volume_uncond` (line 309) — the hpos-free form. The
boundary extension that a closed BACKLOG row once asked for landed 2026-06-11.
So `hgen` does **not** come from the volume machinery.

**F3. `hgen` enters in exactly two places, and both are singlet-side.** In the
proof it is used only at `nudgedSinglet_norm a b hgen` and
`nudgedSinglet_born a b hgen s t`. Downstream of those,
`nudgedSinglet_coord` is already `hgen`-free; the positivity enters through
`singletJointEig_born (hP : 0 < P_st a b s t)`.

**F4. The endpoint case looks closable, not open.** At `P_st = 0` we have
`‖Π^s(a) ⊗ Π^t(b) ψ⁻‖² = P_st = 0`, so the projected vector is genuinely zero and
`singletJointEig = (√0)⁻¹ • 0 = 0` under Lean's junk convention. Then the Born
identity reads `0 = 0`, and the norm identity still sums `Σ_{s,t} P_st = 1`
because the vanishing cells contribute nothing. See §5.

## 1. The L2′ correction, and what it costs the paper

Pointwise parameter independence on both wings over a deterministic shared state
*is* setting-local responses, which `no_product_partition_realises_singlet` rules
out. Withdrawn.

**Carry into the paper, in these words.** Replacing it by the measure-level
condition makes L2′ close to a restatement of the conclusion rather than a
premise doing derivational work. Section 4.2 is therefore **not a derivation of
no-signalling from primitives; it is a verification of no-signalling in the
constructed sector.** Item 16 carries the real open problem. The measure-level
predicate must not be presented as a repaired hypothesis.

**Measurement independence must be named.** `OperationalNoSignalling` is stated
relative to a single fixed `μ` used for all four contexts. That fixture *is*
measurement independence. Name it in the predicate's docstring so C1 can state
plainly which premise the no-signalling result rests on. This is a genuine Bell
assumption and it was previously invisible.

## 2. Phasing: three gates, three commits, stop for review after each

Thirty-six items in one run produces an unreferee-able diff. Split, with the
audit first because its outcome can invalidate documentation written before it.

### Phase 0 — audit only (items 23, 24). **Blocking.**

Nothing else may be touched. Create `Tests/AxiomAudit/C1.lean` pinning verbatim
`#print axioms` output for the listed theorems and, specifically, the Born-volume
footprint of `localDeisolation_pointer_volume` through
`povm_born_eq_dilated_volume_uncond`.

**Stop and report before Phase 1.** If that chain pulls Busch effect-Gleason, the
C1 narrative and several docstrings change, and any prose written first would be
written twice. This mirrors the Phase 0.3 blocking pattern from the README work
order.

⚠️ Resolve fully-qualified names when writing the file rather than transcribing
the work order's list: `lhvCHSH_abs_le_two` is in `Empirical/CSD/Crypto/E91.lean`
while `e91_no_lhv_reproduces_singlet` is in `Empirical/QM/Crypto/E91.lean`, so
the uniform `CSD.Empirical.QM.E91.*` prefix in the order is wrong for at least
one.

### Phase 1 — mathematics (items 2–8, 11, 13–15, plus pins for new theorems)

### Phase 2 — documentation and bookkeeping (items 1, 9, 10, 12, 17–22, 25–31)

## 3. Phase 1 design corrections

### D1. Derive measurability; do not assume it

Do **not** add measurability to `GlobalCHSHAssignment` as a hypothesis. Require it
on `SharedContextOutcomeMaps` — the object C1 actually posits, with
`F_C : Λ → Sign × Sign` measurable — and **derive** the four component
measurabilities from compatibility, since `A_i = Prod.fst ∘ F_ij` and
`B_j = Prod.snd ∘ F_ij`.

The capstone then reads: *no measurable shared-context outcome family compatible
with any global assignment reproduces the singlet.* That assumes measurability
only where C1 assumes it.

### D2. The capstone needs a non-vacuity companion

`no_product_partition_realises_singlet` has `productPartition_nonvacuous` for
exactly this reason. Add the analogue: exhibit a shared-context family that *is*
compatible with a global assignment and reproduces some correlation, so the new
theorem is a **separation** and not a type-level artefact. Without it the
capstone is open to the objection item 32 forbids.

### D3. Item 7 constructive, with a single global phase

Define the wing unitary explicitly rather than asserting existence, so nothing
downstream needs `Classical.choose` and item 8 composes:

* `wingBasisUnitary : DetectorSetting → Matrix (Fin 2) (Fin 2) ℂ`, columns the
  detector-axis spinors, proved unitary;
* `nudgedSinglet a b = c • (wingBasisUnitary a ⊗ₖ wingBasisUnitary b)ᴴ *ᵥ singlet`
  for some `c` with `‖c‖ = 1`.

**Route, so the agent does not flail.** First prove
`singletJointEig s t a b = spinor a s ⊗ spinor b t` and orthonormality of
`{spinor a s}ₛ` for each `a`. Given those, `nudgedSinglet` is by definition the
coordinate vector of `ψ⁻` in a product orthonormal basis and the change-of-basis
matrix factorises automatically. `jointSpinProj` is already
`spinProj s a ⊗ spinProj t b` (`LF3/Setup.lean:163`) and each `spinProj` is
rank one, so the product-vector step is close to definitional.

⚠️ **Phase trap.** `c` must be a **single global constant, independent of
`(s,t)`**. Per-cell phases collapse the result to equality of squared amplitudes,
which reproduces probabilities without proving locality. The `∼` notation in the
work order invites exactly that; the constructive form above forecloses it.

*(An earlier note in this plan observed that per-eigenvector phase freedom is
itself a product unitary. True of the freedom in **choosing** `U_A`, `U_B`, but it
does not license per-cell phases in the **statement**. D3 is the operative form.)*

### D4. Item 7 is a hard gate

Items 8, 19 and parts of 27 are contingent on it. **If nudge locality does not
close, stop and report. Do not proceed to item 8, and do not soften item 19.**

## 3b. ★★ Task 7 is FALSE as stated (Phase 1 probe, 2026-08-10)

⚠️ **This supersedes D3's optimism above.** D3's construction is still the right
*repair*, but the theorem it was meant to prove about the **existing**
`nudgedSinglet` does not hold.

`singletJointEig_born`'s own proof contains

    inner ℂ singlet (singletJointEig s t a b) = (Real.sqrt (P_st a b s t) : ℂ)

so with `nudgedSinglet_coord`, **`nudgedSinglet a b` is the vector
`(√P_st)_{s,t}` — all real, all non-negative, every phase stripped.**

**Counterexample.** With `c = a·b` and `P_st = (1 − s·t·c)/4`, as a 2×2 matrix
`M = ½[[√(1−c), √(1+c)], [√(1+c), √(1−c)]]`, giving
`MᵀM = ½[[1, √(1−c²)], [√(1−c²), 1]]` and Schmidt coefficients
`½(1 ± √(1−c²))`. Local unitaries preserve Schmidt spectra and `ψ⁻` is maximally
entangled, so `(U_A ⊗ U_B)ᴴψ⁻` is maximally entangled for **any** unitaries. At
`a ⊥ b` all four `P_st = ¼`, so `nudgedSinglet = ½(1,1,1,1)`, a **product
state**. No local unitary carries a maximally entangled state to a product state.

`nudgedSinglet` is a local-unitary image of the singlet **only at `a·b = ±1`** —
precisely the endpoint set `hgen` excludes.

**Diagnosis.** `singletJointEig := (√P_st)⁻¹ • (Πˢ(a) ⊗ Πᵗ(b)) ψ⁻` fixes each
basis vector's phase by projecting `ψ⁻` itself: four independent phases, where a
product unitary supplies only separable ones (`α_s + β_t`). **The phase trap,
baked into the definition rather than the statement.**

**Why nothing caught it.** Every consumer uses only `‖·‖²`, so any
phase-representative passes every existing proof. Lean cannot help:
`nudgedSinglet` is a *definition* (true by fiat) and the false claim lived only
in a docstring.

### Resolution options

* **A.** Fix the definition: `spinor a s`, `wingBasisUnitary a`, and
  `nudgedSinglet' a b := (wingBasisUnitary a ⊗ₖ wingBasisUnitary b)ᴴ *ᵥ singlet`.
  Locality becomes definitional.
* **B.** Keep the definition, drop the claim. C1 then asserts only that the
  *coupling* factorises (`localDeisolation_factorises`, genuinely proved).
  Documentation-only.
* **C.** Chain locality at `a·b = ±1` only. True, measure-zero, same set `hgen`
  excludes.
* **D. A, staged — recommended.** Add `nudgedSinglet'` alongside, prove equal
  moduli, re-route the pointer-volume theorem, deprecate the old object.

**Why D is cheaper than it looks:** downstream uses *only* moduli, and
`|⟨u_s ⊗ w_t, ψ⁻⟩|² = P_st` still holds, so the pointer-volume theorem and the
capstone should transfer with proofs essentially intact.

### Probe result: option D is viable

Machine-checked on a scratch file: **`‖col₀ s a‖² = (1 + s·a_z)/2`**, via
`DetectorSetting.sum_sq_components_eq_one` and `Complex.sq_norm`. So column 0 of
`Πˢ(a)` vanishes **iff** `a_z = −s`, column 1 **iff** `a_z = +s`, never both
(that would need `s = −s`). The two-case spinor definition is therefore total and
the pole is a clean `by_cases`, not a chart obstruction. Matrix entries fall to
`simp [spinProj, pauliDot]`. Estimate **M**, with the residual risk in
orthonormality/unitarity bookkeeping rather than the construction.

**Blocked pending the author's choice of A/B/C/D:** tasks 8, 19, part of 27.

## 4. Phase 1 order

1. **T2** `LF3/SharedContextMap.lean`: `SharedContextOutcomeMaps Λ` with
   `F : MeasurementContext → Λ → Sign × Sign`, measurable wrapper. State type must
   not depend on context.
2. **T3** measurability per D1 (derived, not assumed).
3. **T4** `LF6/C1BellConsistency.lean` (in LF6, avoiding an LF3→LF6 back-edge):
   `CompatibleWithGlobalCHSH`, component-wise at the four CHSH settings.
4. **T5** `no_compatible_global_chsh_assignment_realises_singlet`, reducing
   directly to `lhvCHSH_abs_le_two`. Plus **D2's non-vacuity companion**.
5. **T6** adapter to `IsProductPartition` only if clean; otherwise use E91
   directly and say so.
6. **T7** `LF6/NudgeLocality.lean` per D3. **Gate.**
7. **T8** `localMeasurementChain_factorises`, scoped to the finite dilated
   construction, never to arbitrary ontic Σ.
8. **T11** `chsh_contexts_generic` + `localDeisolation_pointer_volume_chsh`.
9. **T13–T15** measure-level no-signalling per §1, including the measurement
   independence docstring. T15 proves equality of **marginal volumes**.

## 5. Item 12 is upgraded from debt to timeboxed attempt

The excluded case `a·b = ±1` is perfect anticorrelation, the most cited Bell
datum, and a guaranteed referee target. F2–F4 say the obstruction is narrower
than assumed:

* the volume engine is already hpos-free (F2), so nothing is needed there;
* `hgen` enters only via `nudgedSinglet_norm` and `nudgedSinglet_born` (F3);
* at `P_st = 0` both look to hold trivially (F4): the projected vector is
  genuinely zero, so the Born identity is `0 = 0`, and the norm identity still
  sums to one.

**Instruction.** Attempt the endpoint with a timebox. The two lemmas to
generalise are `singletJointEig_born` (currently `hP : 0 < P_st`) and
`nudgedSinglet_norm`. If it fails, report the **precise blocking lemma and the
goal state**, not a general debt note.

## 6. Item 29 — decision made in advance

Citing the **repository** at a tagged release, with commit SHA, module path and
theorem name, is not a dependency-order violation: the repository is one artefact
with its own DOI, and no unpublished prerequisite is being cited. Citing **"LF6"
as a document** would be a violation, since that manuscript layer is unpublished.

`docs/C1-FORMAL-SUPPORT.md` must therefore never present LF6 (or LF5) as a
manuscript. Extend existing `CITATION.cff` / release machinery; prepare but do
**not** create or push a tag without explicit approval.

## 7. Additions carried from the review

* **Deprecate `ContextIndexedOutcomeMaps`** rather than maintain two interfaces
  (F1: no code users; update the `LF5/Capstone.lean` prose mention).
* **Item 36 requires verbatim `#print axioms` output and explicit hypothesis
  lists**, not prose summaries of signatures.
* **Verify the correlation sign convention against C1's before the adapter
  lands.** Note: the work order's suggested name `singletCorrelation` does not
  appear in `LF3/`; locate the actual definition first rather than assuming the
  name.

## 8. Risks

* **T7 slipping** takes T8, T19 and part of T27 with it. D4 makes that a stop,
  not a silent softening.
* **T5's reduction shape**: `lhvCHSH_abs_le_two` must accept the responses as T4
  produces them. Adapt at T4 rather than restating Bell.
* **Phase 0 is the one that can force claim changes.** If the footprint
  contradicts a registry claim, fix the claim.
* **Estimates here have been optimistic before.** Probe D3's rank-1-to-spinor
  step on a scratch file before committing the tranche shape.

## 9. Definition of done

As the work order states, and explicitly: *closed* requires a theorem where one
was required, or an explicitly corrected claim recording that the theorem is not
established. Documentation edits alone never close an item.

## References

`CsdLean4/LF3/{ContextMap,Setup}.lean`, `LF3/Singlet/JointEig.lean`;
`CsdLean4/LF6/{ForcedContextuality,SingletDeisolationFlow,LocalDeisolationFlow}.lean`;
`CsdLean4/Empirical/{CSD,QM}/Crypto/E91.lean`;
`CsdLean4/SigmaLayer/TheoremTargets.lean`; `specs/necessity-audit.md`;
`specs/BACKLOG.md`.

# CV-25 scoping: channel-level RG at the cutoff — the coarse dynamics as a priced CPTP statement

Status: **SCOPING COMPLETE 2026-08-18 — and the arc it named is now EXECUTED
(CV-26, same day)**: CR-1/CR-2/CR-3 all landed in
`Mathlib/QuantumInfo/UnitaryPerturbation.lean` and `CV/ChannelRG.lean` (7 pins), exactly
as scoped below — mode tracing as the route, trace distance as the norm, the budget
`ε = 2n·|τ|·|λ|·C_v`, and both §5 "missing, provable" links discharged with no
re-scoping. This document is therefore a **spent scoping pass**: it is kept as the
feasibility record (and as the model for the check-before-scoping discipline), not as an
open plan. Deviations from the plan: none in substance; CR-2's proof turned out simpler
than the §5 sketch (the traced mode's phase cancels its own conjugate entrywise, so the
Kronecker factorisation the sketch anticipated was never needed). (BACKLOG row Q21, the third Stage-7 row;
[`eft-stage7-plan.md`](eft-stage7-plan.md) row CV-25). One focused pass, per the gate
agreed in advance. Deliverable of this document: the CPTP coarse-graining candidates
mapped, the norm fixed, the error-budget chain checked link by link against the
existing bricks, and **the first brick named** — the gate's success criterion ("a
statement with a *provable* error budget emerges") is met, so the row does **not**
return to unqueued. No theorems are claimed here.

## 1. The gap, restated precisely

The Stage-4 record ([`CV/Decimation.lean`](../CsdLean4/CV/Decimation.lean)) is the
floor. `compressCfg_interactingU` gives exact matching (couplings unchanged) for the
occupation-defined class, and ★★ `exists_unitary_compress_not_unitary` /
`compress_hopU_not_unitary` prove that for support-spreading drives exact **unitary**
matching is impossible — the decimated drive loses norm; amplitude genuinely leaves
the retained sector. The module's own conclusion stands: an honest RG statement must
be about **channels with an error budget**. What Stage 4 said the corpus lacked was
"a leakage estimate"; this pass determines whether the bricks landed since (K2/K3
channels, the CV-9/CV-12 price ladder, CV-13/CV-23 correlators) now supply one.

The target shape, fixed here: a coarse-graining CPTP map `C`, an effective coarse
drive, and a bound

  `traceDist( C(U_int^n ρ U_int^{n†}), U_eff^n C(ρ) U_eff^{n†} ) ≤ ε(λ, τ, n)`

for every density operator `ρ` — approximate channel intertwining with a priced
defect, exactly the "agreement of low-energy state assignments up to a bound" the
Stage-4 record called for.

## 2. The Lean surfaces available

* **Channels (K2, [`channels-plan.md`](channels-plan.md)):** `QuantumInfo.Channel`
  (Kraus form, `tp`), `Channel.apply_trace` / `apply_posSemidef` /
  `apply_isHermitian`; `unitaryChannel`, `mixedUnitaryChannel`, `tensorRight`,
  Stinespring `ofIsometry`; ★ **`traceOutChannel s env : Channel (s × env) s env`**
  with `traceOutChannel_apply : … = Matrix.traceRight` — the partial trace IS a
  channel, today.
* **The metric (K3):** `traceNorm` / `traceDist` (Hermitian-difference API),
  `traceDist_triangle`, `traceDist_le_one`, ★ **`channel_traceDist_le`** — the data
  processing inequality, and `traceDist_conj_unitary` (unitary invariance). The
  variational surface for traceless Hermitian differences
  (`traceDist_eq_re_trace_posPart`, the `posPart`/`posProj` battery) is landed.
* **Partial trace mechanics:** `Matrix.traceRight` / `traceLeft` with
  `traceRight_kronecker`, `traceRight_kronecker_one_mul`,
  `traceRight_mul_kronecker_one`, `trace_traceRight`, `PosSemidef.traceRight`.
* **The mode split:** `modeSplit k : FieldConfig K N ≃ ({j // j ≠ k} → Fin N) × Fin N`
  (`CV/PowerCounting.lean`) — the reindex bridge from field configurations to the
  `s × env` product shape the partial-trace API speaks.
* **The price ladder:** `interactingU_dist_le` — `‖U_int − U_free‖ ≤ |τ|·|λ|·C` per
  period in the L2 operator norm (CV-9, Duhamel), and
  `Matrix.norm_pow_sub_pow_le_of_unitary` — the `n`-period telescoping (CV-12),
  already composed in `twoPoint_interacting_dist_le`.
* **The cone (for the distance refinement only):** `graphNeighborhood`,
  `heisenberg_graphInteractingU_pow_supportedOn`,
  `commute_heisenberg_graphInteractingU_pow` (CV-18/20).

## 3. The two coarse-graining candidates, mapped

**(a) Mode tracing — `traceOutChannel` across `modeSplit`.** Reindex by `modeSplit k`
(a permutation conjugation — itself a unitary channel, `traceDist`-invariant), then
trace out the mode-`k` factor. This is a genuine CPTP map **with the bricks already
landed**: `traceOutChannel ({j // j ≠ k} → Fin N) (Fin N)`. The coarse system is the
spectator field; the coarse free drive is the spectator phase diagonal. This is
momentum-shell/mode decimation, and it is the route this scoping selects.

**(b) Level decimation — `compressCfg`-conjugation.** The Stage-4 map
`ρ ↦ (embed)ᴴ-conjugated block`. **Not a channel as-is**: the map is trace-decreasing
— it discards the population of the levels above the lower cutoff — and the Stage-4
loss-of-norm no-go is exactly this fact seen at the unitary level. It becomes CPTP
only with an explicit **leakage arm** (a second Kraus branch collecting the discarded
sector into a sink), and the quantitative content of that arm is a leakage estimate
for the drive — level-occupation growth under `interactingU` — which the corpus still
does not have (the CV-24 truncation-edge bookkeeping is the nearest surface, and it
is a statement about the free walk, not about interacting leakage). Candidate (b) is
therefore **recorded, not selected**: it re-enters only after a leakage estimate
exists, and nothing in the route-(a) arc below depends on it.

## 4. The norm, fixed

**States are compared in trace distance** (`traceDist`, the K3 metric): it is the
corpus's channel-contractive metric (`channel_traceDist_le` is stated for it), it is
the operational distinguishability bound, and both sides of the target are density
operators, so the Hermitian-difference API applies with no extension. **The price
enters in the L2 operator norm** (the corpus's C*-norm discipline for drives); the
interface between the two norms is exactly one missing lemma (CR-1 below). Diamond
norm is *not* adopted: the corpus does not have it, and the target is a bound uniform
over input states, which trace distance against arbitrary `ρ` already expresses;
promoting to diamond distance is a strengthening for a later decision, not a need.

## 5. The error budget, checked link by link

For `ρ` a density operator, `U := (interactingU K N τ lam v)^n`,
`F := (freeFieldU K N τ)^n`, `C := traceOutChannel ∘ reindex (modeSplit k)`:

  `traceDist(C(UρU†), U_eff^n C(ρ) U_eff^{n†})`
  `  ≤ traceDist(C(UρU†), C(FρF†))` `+ 0`
  `  ≤ traceDist(UρU†, FρF†)` `≤ 2‖U − F‖` `≤ 2n‖U₁ − F₁‖` `≤ 2n·|τ|·|λ|·C_v`

| Link | Statement | Status |
|---|---|---|
| free intertwining | `C(FρF†) = U_eff^n C(ρ) U_eff^{n†}` **exactly**, `U_eff` the spectator free drive: `fieldEnergy` is additive across `modeSplit`, so `F` reindexes to a Kronecker product of diagonal phases, and the traced factor's unitary cancels under `traceRight` | **missing, provable — CR-2** (S/M: `Complex.exp_add` + `traceRight_kronecker_one_mul`-family + one new lemma `traceRight ((1 ⊗ B) X (1 ⊗ B)ᴴ) = traceRight X` for unitary `B`, a direct `Matrix.mul_apply` computation) |
| triangle | `traceDist_triangle` | **have** |
| data processing | `channel_traceDist_le` at `C` | **have** (the reindex leg via `traceDist_conj_unitary`) |
| the bridge | `traceDist(UρU†, VρV†) ≤ 2‖U − V‖` for unitaries, `ρ` a state | **missing, provable — CR-1** (the norm interface; see §6) |
| telescoping | `Matrix.norm_pow_sub_pow_le_of_unitary` | **have** |
| one-period price | `interactingU_dist_le` | **have** |

**Conclusion: the ladder supplies the budget.** `ε(λ, τ, n) = 2·n·|τ|·|λ|·C_v`, with
two missing links, both checked for walls (§6). The `distance` argument of the
row's `ε(λ, τ, distance)`: the budget above is **uniform in distance**; a
distance-resolved refinement (error decaying with graph distance between the traced
mode and the observed spectators) would ride the CV-18/20 cone bricks, and is a
*refinement row*, not a requirement for the first statement — deferred to a queue
decision after CR-3.

## 6. The first brick, named: CR-1, then the arc

**CR-1 — the unitary-perturbation bridge** (the first brick):

  `traceDist(UρU†, VρV†) ≤ 2·‖U − V‖`  (`U, V` unitary, `ρ` PSD with `trace ρ = 1`).

Feasibility, checked before naming (the check-impossible-first record): the
difference is Hermitian and **traceless**, so the landed variational collapse
`traceDist_eq_re_trace_posPart` applies; splitting
`UρU† − VρV† = (U−V)ρU† + Vρ(U−V)†` reduces the bound to two instances of
**`|re tr(ρ M)| ≤ ‖M‖ · tr ρ` for PSD `ρ`** (a Hölder-lite the corpus does not have
but whose spectral route is fully paved: `cfc_eq_conj_diagonal` diagonalises `ρ`,
and the L2Operator scope bounds the quadratic form), plus submultiplicativity and
`‖posProj‖ ≤ 1` (spectral: `posProj` is a `cfc` of an indicator). No wall; size M.
CR-1 is a Category-1 `Mathlib/QuantumInfo` lemma (it mentions nothing CSD).

**CR-2 — free-drive intertwining across the mode split** (S/M, §5 table).

**CR-3 — the capstone**: the assembled channel-RG statement of §5 with
`ε = 2n|τ||λ|C_v`, landed where the CV chain lives, citing CR-1/CR-2 and the price
ladder. Assembly-size S/M once CR-1/CR-2 stand. Per §8.3b this is a **new**
claim-surface (the corpus has no channel-level dynamics statement), so a capstone is
warranted; it strengthens nothing existing and duplicates nothing.

## 7. What this scoping does NOT claim

- **No RG flow, no fixed points, no beta function** — unchanged from the Stage-4
  record; CR-3 is a single coarse-graining step with a priced defect, not a flow.
- **No leakage estimate and no level-decimation channel** — candidate (b) stays
  recorded-not-selected until a leakage estimate exists.
- **No diamond norm**, no uniformity claim beyond per-state trace distance (§4).
- **No distance-resolved budget** in the first arc — the cone refinement is a
  separate, later decision.
- **No continuum limit** (`ApproxCCR.no_exact_finite_ccr` stands), and the Stage-4
  no-go is not weakened: CR-3 is exactly the channel-level statement that no-go said
  must replace unitary matching.

## 8. Sequencing

CR-1 (Cat-1, `Mathlib/QuantumInfo`) → CR-2 (CV) → CR-3 (CV capstone). CR-1 is
independently valuable (the trace-distance/operator-norm interface serves any future
perturbation-to-distinguishability statement). Whether to run the arc is a **queue
decision** — this document only establishes that the budget is provable and names
the bricks; recorded as row CV-26 in [`future-work.md`](future-work.md), queued on
decision, per the deliberate go/no-go culture.

## References

[`eft-stage7-plan.md`](eft-stage7-plan.md) (row CV-25, the gate);
[`specs/BACKLOG.md`](BACKLOG.md) (Q21); [`future-work.md`](future-work.md) (rows
CV-25/CV-26); [`channels-plan.md`](channels-plan.md) (K2);
`CV/Decimation.lean` (`exists_unitary_compress_not_unitary`,
`compressCfg_interactingU` — the floor); `Mathlib/QuantumInfo/DataProcessing.lean`
(`channel_traceDist_le`, `traceDist_conj_unitary`);
`Mathlib/QuantumInfo/CanonicalChannels.lean` (`traceOutChannel`);
`Mathlib/QuantumInfo/TraceDistance.lean` (`traceDist`, the variational battery);
`Mathlib/LinearAlgebra/Matrix/PartialTrace.lean` (`traceRight` + Kronecker family);
`CV/PowerCounting.lean` (`modeSplit`); `CV/InteractionPrice.lean`
(`interactingU_dist_le`); `CV/SupportSpreading.lean` (the cone, for the deferred
refinement); [`unitary-tpp-scoping.md`](unitary-tpp-scoping.md) (the Q11 mold this
pass follows).

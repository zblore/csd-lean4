# One finite two-wing CSD experiment: compatibility audit (BACKLOG #131)

**Status:** AUDITED 2026-10-10, at the author's instruction and to the author's specification. The audit was
read-only: every claim below about the corpus was read from a theorem or definition *type* in
`CsdLean4/LF6/LocalDeisolationFlow.lean`, `CsdLean4/LF3/SettingLocality.lean`,
`CsdLean4/CV/RecordInfluence.lean`, `CsdLean4/RecordLayer/RecordMacrostate.lean`, and the supporting
modules those four name. **Nothing was built.** §6 prices what could be; §5 states the two incompatibilities
that must be designed around first, and §4 the one place the corpus is emptier than its headline suggests.

The author's framing, which this note adopts: build **one** finite two-wing experiment and require it to
satisfy record stability, causal separation, Bell correlations and no-signalling *within the same dynamical
model*. That is far narrower than deriving spacetime, and it directly tests Conjecture `C-1`.

## 1. The question the audit had to answer

> Can the existing setting-contextual singlet record construction and the finite causal-influence
> construction be instantiated on one ontic arena, without introducing Bell-local pointwise outcome
> factorisation, while preserving their current dynamical and measure-theoretic guarantees?

**Answer: yes on the arena, yes on the Bell question, no on the fibre's role.** The obstruction is not where
it was expected — not in Bell, and not in the arena — but in what the record fibre is *used for*.

## 2. The exact types

| Interface | Ontic arena | Measure | Outcome / record object |
| --- | --- | --- | --- |
| `LF6/LocalDeisolationFlow` | `CPN 16 = ℙ ℂ (EuclideanSpace ℂ (Fin 16))` — **no fibre** | `fsMeasure q₀` (flow clause); `epistemicMeasure (mk ψ')` (Born clause) | `RecordLayer.globalBasin (momentContext (M+1)) (e (n, stIdx (s,t)))` |
| `LF3/SettingLocality` | `SigmaSpace : Type*` with `[MeasurableSpace SigmaSpace]` — **polymorphic** | any `μ : Measure SigmaSpace` | `SharedContextOutcomeMaps`, `F : MeasurementContext → SigmaSpace → Sign × Sign` |
| `CV/RecordInfluence` | `FibredFieldArena K N = ℙ ℂ (EuclideanSpace ℂ (Fin K → Fin N)) × RecordFibre` | `μ.prod μ` on the fibre; base pointwise | `arenaObs A`, `recordStroke₂`, graph `E : Finset (Fin K × Fin K)` |
| `RecordLayer/RecordMacrostate` | `LF4.KSigma N = CPN N × KTorus` | `epistemicMeasure p = δ_p ⊗ vol_{T²}` | `outcomeCode c`, `recordString c` |

## 3. What already lines up, and the transport maps

* **The fibres are the same type.** `CV.RecordFibre` and `LF4.KTorus` are both `AddCircle (1:ℝ) × AddCircle
  (1:ℝ)`. No transport is needed on the fibre at all.
* **The bases differ only by an index equivalence.** `FieldArena K N` and `CPN M` are both
  `ℙ ℂ (EuclideanSpace ℂ ι)`; the transport is `LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e` along any
  `e : ι ≃ ι'`, lifted to the projectivisation. **`LF6`'s own capstone already uses this gadget internally**
  (`e : Fin 4 × Fin 4 ≃ Fin (M+1)`), so the transport is not new machinery.
* **The sizes match the physics.** For two qubits and two pointers, `FieldConfig 4 2 = Fin 4 → Fin 2` has
  cardinality `16`, so `FieldArena 4 2 ≃ CPN 16` and the single arena `KSigma 16 = CPN 16 × KTorus` carries
  all four interfaces. `Fin K = Fin 4` is then *exactly* the mode index `CV`'s coupling graph
  `E : Finset (Fin 4 × Fin 4)` wants, and the two-wing graph `{(A-sys, A-ptr), (B-sys, B-ptr)}` with no A–B
  edge is the spacelike separation of the wings in the sense `CV.Spacelike` defines.
* **`LF6` and the record layer are connected today, not in prospect.** `LF6`'s Born clause evaluates
  `epistemicMeasure` of `RecordLayer.globalBasin`, and ties basins to pointer blocks through `e (n, stIdx
  (s,t))`. That bridge exists in the corpus now.

## 4. The Bell question, and where the corpus is emptier than its headline

The author's collapse argument is exact and the corpus already encodes it. `LF6.IsProductPartition` is over
`RA RB : DetectorSetting → SigmaSpace → ℝ` — the arity has **no slot for the remote setting**, which is
precisely why demanding `A(a,b,σ) = A(a,b',σ)` kills the model, and why Q10's route (a) died.
`RemoteSettingLocalityA` does not impose it: `wingA ⟨a,b⟩` keeps the full context and the `b`-dependence is
carried by a measure-preserving `reroute`. So instantiating `LF3` on the shared arena introduces no pointwise
factorisation.

The record layer already supplies a contextual outcome map of the admissible shape:

```
globalBasin c i = {x | x.2.1 ∈ circleCell (c.rate x.1) i}
```

**Rates from the base, selector from the fibre.** For a joint context carrying `P_st a b`, changing `b` moves
the cell *boundaries*, so A's outcome moves with `b` pointwise while A's marginal is the total arc width. The
contextuality is in the cell geometry — which is what would make a `reroute` here **forced by `P_st`** rather
than chosen to fit the marginals, meeting the author's requirement that the relabelling correspond to an
admissible interaction. Concretely it would be a piecewise rotation (interval exchange) of `AddCircle 1`,
measure-preserving for Lebesgue.

⚠️ **But there is no `RemoteSettingLocalityB` witness anywhere in the corpus.** The only witness is
`LF3.translationLocality`, which supplies the **A-wing only**, and whose `fB C.b l` ignores `a` entirely — so
*its* B-wing is of product-partition arity and it cannot reproduce the singlet. Consequently
`operationalNoSignalling_of_settingLocality`, which consumes both wings, has **no witness at all**. The
author's instinct to push on the relabelling found the real soft spot: the primitive is derived and
non-vacuous on one wing, and unwitnessed as a pair.

## 5. The two incompatibilities

**(I) `globalBasin`'s selector is one-dimensional.** It reads `x.2.1` only; `KTorus`'s second coordinate plays
no role in it. `CV.recordStroke₂` writes *both* fibre coordinates, as two independent record channels, one per
wing. So the existing record layer models **a single joint outcome**, not two independently-recorded wings.

A two-wing experiment with per-wing records therefore needs a **two-selector basin**, and that is exactly
where Bell bites: a per-wing basin `{x | x.2.1 ∈ cell (rate_A (x.1, a))}` whose rates depend only on `a` is
*precisely* the product-partition form `no_product_partition_realises_singlet` kills. So at least one wing's
cell geometry must depend on the **joint** context. **This is a physics design decision, not a formalisation
detail**, and it is the first thing the programme has to choose.

**(II) Two measures, two dynamics.** `LF6`'s flow preserves `fsMeasure` on the base. The Born and record
statements are made in `epistemicMeasure p = δ_p ⊗ vol`, which a base-moving flow does **not** preserve — it
moves the Dirac. The record layer's own dynamics `RecordLayer.sigmaShift` is a *fibre* translation and does
preserve it (`measurePreserving_sigmaShift`). The composite preserves `kMuL = fsMeasure ⊗ vol` but not
`δ_p ⊗ vol`. A single experiment needs both dynamics composed, so the measure in which the Born statement is
made and the measure the dynamics preserves have to be reconciled rather than left implicit.

## 6. The five obligations, priced against what exists

The author's ordering is kept. Prices are for the two-qubit/two-pointer model on `KSigma 16`.

1. **One physical record history** — **S–M.** `LF6` clause (6) gives the flow realising the Naimark dilation
   and clause (3) ties the pointer blocks to basins; what is missing is the lift of the flow to the product
   (`Prod.map localDeisolationFlow id`, measure-preserving by `MeasurePreserving.prod`) and the composition
   with `outcomeCode`. Blocked on **(II)**, which this obligation is the cheapest test of.
2. **Dynamical record stability** — **S, conditional.** The ε(T) form already exists and is *proved*, not
   declared: `measure_drift_recordString_ne_le` bounds the exceptional set by `k·N·ω·T` for a fibre drift at
   rate `ω` over `[0,T]`. For a general `Φ_t` it does not exist, so this obligation is cheap for the fibre
   dynamics and open for any other.
3. **Records to causal regions** — **M.** The graph is supplied as `E`, as the author intends, and
   `CV.recordStroke_heisenberg_comm_kick_of_spacelike` is the exact unsteerability statement. The work is
   transporting it along the index equivalence of §3 and matching `arenaObs` observables to the wings.
4. **Joint Bell and no-signalling** — **M–L, and gated on a choice.** Consumes `LF6` and `LF3`, but only after
   **(I)** is decided, and it needs the missing B-wing witness of §4. The honest first brick here is the
   `RemoteSettingLocalityA`/`B` pair instantiated at the record-layer basins, with the `reroute` read off the
   cell geometry.
5. **The coarse projection retains the properties** — **S–M.** `MacroProjection.FactorsThrough`,
   `factorsThrough_globalBasin` and `RecordMacrostate.noSignalling_pairFamily` are the machinery, and the last
   is already proved *in `epistemicMeasure`*, which is the right measure for one prepared singlet.

## 7. What this would and would not establish

A finite-model existence theorem with an explicit admissible witness — not five desired conclusions packaged
as fields of a structure — would show the five properties **compatible within one finite CSD model**. It would
**not** establish `C-1`: causal adjacency and spatial separation are still supplied through `E`, and nothing
would show that all apparent nonlocality is a consequence of projection alone. The author's §5 move — replacing
`E` by an effective adjacency read off the generator — is a further row and is not priced here; as the author
notes, that candidate presupposes a choice of local subalgebras and can be defeated by cancellations, so it
needs checking against the intended locality relation rather than adopting.

## 8. The finding

The arena is not the obstacle and Bell is not the obstacle. The corpus can carry this experiment on one
`KSigma 16`, with transports it already uses internally, and its contextual outcome map is of the shape Bell
permits. What stands in the way is narrower and more interesting than either: **the record fibre is currently
one selector, and a two-wing experiment needs two** — which forces a choice about whose cell geometry sees the
joint context. And the **no-signalling primitive is unwitnessed as a pair**, so the one general theorem that
would deliver the author's obligation 4 has, today, no model at all.

Both are stateable, finite and checkable. Neither is research-grade. That is why #131 is priced rather than
parked.

## References

`CsdLean4/LF6/LocalDeisolationFlow.lean` (`localDeisolationFlow`, `localDeisolation_capstone`);
`CsdLean4/LF6/ForcedContextuality.lean` (`IsProductPartition`, `no_product_partition_realises_singlet`);
`CsdLean4/LF3/SettingLocality.lean` (`RemoteSettingLocalityA`/`B`, `translationLocality`,
`operationalNoSignalling_of_settingLocality`); `CsdLean4/LF3/SharedContextMap.lean`
(`SharedContextOutcomeMaps`); `CsdLean4/CV/RecordInfluence.lean` (`Spacelike`, `recordStroke₂`,
`recordStroke_heisenberg_comm_kick_of_spacelike`); `CsdLean4/CV/FibredArenaBridge.lean`
(`FibredFieldArena`, `RecordFibre`); `CsdLean4/RecordLayer/RecordMacrostate.lean` (`outcomeCode`,
`recordString`, `noSignalling_pairFamily`); `CsdLean4/RecordLayer/GlobalBasin.lean` (`globalBasin`,
`epistemicMeasure`, `momentContext`); `CsdLean4/RecordLayer/MacrostateStability.lean`
(`measure_drift_recordString_ne_le`, `measurePreserving_sigmaShift`);
`CsdLean4/RecordLayer/MacroProjection.lean` (`FactorsThrough`, `MacroProjection`);
`CsdLean4/LF4/KahlerInstance.lean` (`KSigma`, `KTorus`, `kMuL`);
[`records-to-spacetime-scoping.md`](records-to-spacetime-scoping.md) (rows 38 and 39, and `C-1`);
[`q10-no-signalling-scoping.md`](q10-no-signalling-scoping.md) (route (a)'s death and candidate (b));
[`POSITS.md`](POSITS.md) (`C-1`); [`BACKLOG.md`](BACKLOG.md) rows 131, 39.

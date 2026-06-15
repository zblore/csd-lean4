# LF5 — measurement dynamics on Σ (the D1 frontier), staged plan

**STATUS: COMPLETE 2026-06-11; LF5-F post-plan extension DONE 2026-06-14.** LF5-A..E all DONE
(A 2026-06-09, B 2026-06-10, C/D/E 2026-06-11); layer headline `measurement_flow_born_frequency`
(`CsdLean4/LF5/Capstone.lean`). **LF5-F (2026-06-14)**: bornRegion pairwise disjointness →
the per-microstate outcome map `vnPointerOutcome` → the single-union-event outcome-frequency
capstone `measurement_flow_outcome_frequency` (`CsdLean4/LF4/BornRegionDisjoint.lean` +
`CsdLean4/LF5/PointerOutcome.lean`); closes the owed-since-`aeece86` outcome-function caveat.
The single-system projective tier of D1 is closed (incl. the per-microstate outcome
function, LF5-F). Remaining D1 strata (not this plan): entangled / non-local de-isolation,
outcome-*conditioned* update (Lüders / sequential), the A5 sector origin, and threading the
flow through the concrete `SectorData` instances (still `Φ = id`).

Drafted 2026-06-09. **The deepest open debt (D1): `Φ = id` in every concrete sector
instance, so no measurement *dynamics* is yet exercised** (status at drafting). This plan
attacks the single-system, projective tier under the de-isolation reading fixed in
[`carve-out-plan.md`](carve-out-plan.md) §6.

## 0. Goal and honest scope

**Goal.** Realise a projective measurement as a deterministic, measure-preserving
**von Neumann correlating flow `Φ_vN ≠ id`** on a joint system+apparatus ontic space
`Σ_joint = ℂℙ^{N·N−1}`, with **context-fixed pointer-outcome regions** (the apparatus
basis, not carved to Born), and prove the typicality volume committed to pointer `i`
equals the Born weight `‖⟨eᵢ, ψ⟩‖²`, then chain through LF1 to frequencies.

**This is reading (c) of D1** (carve-out-plan §6): the apparatus *de-isolates* a region;
the outcome is fixed by the isolated-region microstate (deterministic, god's-eye-certain);
it looks random to us via typicality over the isolated DOF, which is the LF1
ignorance-of-microstate, with the FS measure as the A5 typicality law.

**Honest non-goals (named, deferred):**
- **Entangled measurements.** Need a *non-local* de-isolation map (Bell forces it, given the
  corpus CHSH = 2√2). Single-system only here.
- **Independent re-derivation of Born.** The Born *number* reuses the existing
  FS-volume = Born engine (`povm_born_eq_dilated_volume`); LF5 makes the measurement
  *dynamics* genuine (`Φ ≠ id`), it does not eliminate the A5 sector posit. The increment is
  "the measurement flow is exercised and its committed volume is Born", not "Born from
  nothing". This is exactly the D1-memory framing: *same engine as `fs_born_volume_ratio_N`,
  now dynamical.*
- **A5 derivation.** The isolated-region typicality measure is posited (FS), not derived;
  A5 reduces to the dynamical sector origin, still open.

## 1. The key reuse insight (why this is tractable now)

The **POVM Naimark tranche already did the hard volume/frequency work** on the dilated
projective space `ℂℙ^{N·|ι|−1}` (index `Fin N × ι` = system × apparatus-outcome):

- `blockProj N i : Matrix (Fin N × ι) (Fin N × ι) ℂ` (= `I_N ⊗ |i⟩⟨i|`) + `blockProj_mulVec`
  — **the pointer-`i` projector** = the de-isolated-to-`i` region.
- `NaimarkDilation P` (isometry `V`, `Vᴴ Πᵢ V = Eᵢ`); `born_transfer : ⟨ψ,Eᵢψ⟩ = ⟨Vψ,ΠᵢVψ⟩`.
- `povm_born_eq_dilated_volume` — block-Born = FS-volume of the barycentric cell on `ℂℙ^{N·|ι|−1}`.
- `povm_born_frequency_volume` — i.i.d. FS trials ⟹ pointer-`i` frequency → `⟨ψ,Eᵢψ⟩`.

The dilation isometry `V` is currently **static**. **LF5's genuine content: realise `V` as
`V = U_vN ∘ (·⊗a₀)`** — embed the system in the apparatus ground state `a₀`, then evolve by a
fixed measure-preserving von Neumann coupling unitary `U_vN`. The de-isolation flow
`Φ_vN := projMap U_vN` (Φ≠id) replaces the unmotivated static embedding. Then the existing
POVM volume/frequency theorems apply to the projective POVM `Eᵢ = |eᵢ⟩⟨eᵢ|` for free.

## 2. Decomposition (tranches, new-vs-reuse, risk)

### LF5-A — the von Neumann measurement unitary  [NEW; bounded] — **DONE 2026-06-09** (`CsdLean4/LF5/VonNeumannUnitary.lean`)
`vnPerm` (adder bijection), `vnUnitary := permMatrix (vnPerm N).symm`, `vnUnitary_unitary`,
`vnUnitary_mem_unitaryGroup`, `vnUnitary_mulVec_ground : vnUnitary N *ᵥ e_{(j,0)} = e_{(j,j)}`
(the copy `eⱼ⊗a₀ ↦ eⱼ⊗aⱼ`). Foundational-triple-only, AxiomAudit-pinned, Tier-A audited SOUND
(coupling verified correct at N=3 with a negative control). Detail of the original spec below.


`vnUnitary {N} : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ` — the **permutation matrix** of the
"adder" bijection `σ (j,k) = (j, j+k)` on `Fin N × Fin N` (apparatus = `Fin N`, ground `a₀ = 0`).
Then `σ (j,0) = (j,j)`: the generalized-CNOT copy `eⱼ⊗a₀ ↦ eⱼ⊗aⱼ`. Being a permutation matrix
it is **manifestly unitary** (`vnUnitaryᴴ * vnUnitary = 1`), sidestepping any
extend-a-partial-isometry problem. Deliver `vnUnitary`, `vnUnitary_unitary`, and
`vnUnitary_apply_ground : vnUnitary *ᵥ (eⱼ⊗a₀-basis) = (eⱼ⊗aⱼ-basis)`.
*Risk:* low — permutation-matrix unitarity + the `Equiv` arithmetic on `Fin N × Fin N`
(`ZMod`/`Fin` add). Reuse `Equiv.Perm` → `Matrix.PEquiv`/permutation-matrix API.

### LF5-B — the measurement flow  [REUSE; bounded] — **DONE 2026-06-10** (`CsdLean4/LF5/MeasurementFlow.lean`)
Delivered: `vnUnitaryReindexed N (e : Fin N × Fin N ≃ Fin m) : Matrix.unitaryGroup (Fin m) ℂ`
(transport of `vnUnitary` along an **arbitrary** reindex equiv, matching the LF4 POVM engine's
`e : Fin N × ι ≃ Fin (M+1)` signature so LF5-C/D share one equiv; helper
`reindex_mem_unitaryGroup`, Mathlib upstream candidate), `measurementFlow := (vnUnitaryReindexed N e • ·)`
on `ℙ ℂ (EuclideanSpace ℂ (Fin m))`, **`measurementFlow_measurePreserving`** (FS-invariance via
`fubiniStudyMeasure_smul_invariant` — the smul-action route, not `projMap`; agreement with the
projMap framing documented, not formalised), **`measurementFlow_ne_id`** (`1 < N`; the basis ray
at `e (1,0)` moves to `e (1,1)`), and `measurementFlow_mk_single` (the flow permutes basis rays by
the adder; at ground apparatus the projective copy `[eⱼ⊗a₀] ↦ [eⱼ⊗aⱼ]`, the LF5-C input).
Foundational-triple-only, AxiomAudit-pinned, Tier-A audited SOUND (witness verified to move;
direction convention killed with a positive/negative entry pair at N=3). Original spec below.

`measurementFlow := projMap (vnUnitary)` on `ℂℙ^{N·N−1}` (reuse `projMap` from
`WignerRigidity.lean` / the U(N)-action). Deliver `measurementFlow_measurePreserving`
(FS-invariance, reuse `fubiniStudyMeasure_smul_invariant` / `transProb_smul_unitary`) and
`measurementFlow_ne_id` (Φ≠id: it correlates — exhibit a point it moves). *Risk:* low.

### LF5-C — de-isolation realises the dilation  [NEW; the crux assembly] — **DONE 2026-06-11** (`CsdLean4/LF5/DilationFromFlow.lean`)
Delivered: `basisPOVM N : POVM N (Fin N)` (the rank-1 computational-basis projective POVM,
`Eᵢ = rankOneEffect eᵢ`, with `basisPOVM_weight : weight ψ i = ‖⟨eᵢ,ψ⟩‖²`); `embedGround N`
(the matrix of `ψ ↦ ψ ⊗ a₀`, isometry); `vnDilationV N := vnUnitary N * embedGround N` — the
**dynamically-realised dilation**, with columns `vnUnitary *ᵥ e_{(m,0)} = e_{(m,m)}` (LF5-A's
ground copy), post-flow coordinates `vnDilationV_mulVec : (Vψ)(j,k) = δ_{kj}·ψⱼ` (i.e.
`U_vN(ψ⊗a₀) = ∑ⱼ ψⱼ·eⱼ⊗aⱼ`), `vnDilationV_isom`, and the **pullback**
`vnDilationV_pullback : Vᴴ (blockProj N i) V = |eᵢ⟩⟨eᵢ|`, assembled into
**`vnNaimark N : NaimarkDilation (basisPOVM N)`**. Block-`i` weight via `born_transfer`:
`vnDilation_block_weight = ‖⟨eᵢ,ψ⟩‖²`. Projective-level tie to the LF5-B flow:
**`measurementFlow_realises_dilation`** — `Φ_vN [piLpCongrLeft e (ψ⊗a₀)] = [piLpCongrLeft e (Vψ)]`
for every `ψ ≠ 0` (in the exact `piLpCongrLeft` spelling LF5-D's volume engine consumes).
Foundational-triple-only, AxiomAudit-pinned (7 pins), Tier-A audited SOUND (copy convention
verified from raw `permMatrix` definitions at N=2 with negative controls killing the
transposed and no-op conventions; non-basis state gives the genuinely-correlated diagonal
output). Original spec below.

**LF5-D obstruction (recorded; load-bearing).** The post-flow state `Vψ` has zero amplitude
on every off-diagonal cell `(j,k), k ≠ j`, so the genericity hypothesis `hpos` of
`povm_born_eq_dilated_volume` / `povm_born_frequency_volume` is **unsatisfiable** at
`ψ' = piLpCongrLeft e (Vψ)` for `N ≥ 2` (auditor-confirmed by a `False`-derivation at N=2).
LF5-D therefore cannot be a blind P.3b/P.4 instantiation. Candidate routes: (a) a
zero-amplitude-tolerant volume reading restricted to the support cells (the diagonal block,
where `vnDilationV_mulVec` gives the exact amplitudes; the diagonal embeds as a coordinate
`ℂℙ^{N−1}` copy via `vnDilationV_column`); (b) weaken `bornRegion_fs_measure`'s `hpos` to the
single cell being read (feasibility scan of `MomentBornN.lean` first). Audit tripwire for
LF5-D: the danger mode is a "tolerant reading" that quietly re-carves the diagonal cells to
Born values instead of deriving the block volume from the FS law on the support subspace.

`embedGround : EuclideanSpace ℂ (Fin N) → EuclideanSpace ℂ (Fin N × Fin N)`, `ψ ↦ ψ ⊗ a₀`.
`V := (vnUnitary as linear map) ∘ embedGround`. Prove `V` is an isometry and the **pullback
identity** `Vᴴ (blockProj N i) V = |eᵢ⟩⟨eᵢ|` (= the projective POVM effect `Eᵢ`). Compute the
post-flow vector `vnUnitary *ᵥ (ψ⊗a₀) = ∑ⱼ ⟨eⱼ,ψ⟩ • (eⱼ⊗aⱼ)` and its block-`i` weight
`‖blockProj i (post)‖² = ‖⟨eᵢ,ψ⟩‖²` (reuse `blockProj_mulVec`). This inhabits
`NaimarkDilation P_proj` for the rank-1 projective POVM `P_proj` (`Eᵢ = |eᵢ⟩⟨eᵢ|`), with the
dilation now *dynamically realised* by `Φ_vN`. *Risk:* medium — the `Vᴴ Πᵢ V = Eᵢ`
bookkeeping and the tensor-index `Fin N × Fin N` ↔ `EuclideanSpace` plumbing; mirrors
`naimarkV_pullback` (reuse its proof shape).

### LF5-D — Born = volume + frequency, on the flow  [REUSE + engine upgrade] — **DONE 2026-06-11** (`CsdLean4/LF4/BornRegionUncond.lean` + `CsdLean4/LF5/FlowBornFrequency.lean`)
Resolved the LF5-C obstruction by **route (b): the unconditional engine** (decided 2026-06-11;
route (a), the system-side reduction, was assessed and rejected — it needs new face-restriction
geometry for the moment subdivision at a boundary Born vector, keeps `hpos` on `ψ`, and lands
the weaker system-factor-typicality statement). Two parts:

**Part 1 — the `hpos`-free engine** (`LF4/BornRegionUncond.lean`, additive — the audited
originals in `MomentBornN` / `BornFrequencyN` / `POVMVolume` are untouched): the bornRegion
volume/frequency theorems for **every unit `ψ`, vanishing amplitudes included**, via the
per-cell dichotomy — positive cells by the closed-simplex subset lemmas (interiority of the
Born vector is not needed: only `0 ≤ b`, `∑b ≤ 1`, per-cell `0 < bᵢ`), zero cells by the
det-0 null image (`det(replaceMap b i) = bᵢ = 0` ⟹ Lebesgue-null image, σ-compact hence
measurable) + the joint Dirichlet law with no subset hypothesis (`fs_volume_eq_dirichlet_inter`)
forcing FS-measure 0 = the Born weight. Delivered: `fs_born_volume_ratio_N_uncond` + `_apex_uncond`,
`bornRegion_measurable_uncond` (also drops `hψ`), `bornRegion_fs_measure_uncond`,
`born_frequency_convergence_N_uncond`, `povm_born_eq_dilated_volume_uncond`,
`povm_born_frequency_volume_uncond`. **This retires the genericity caveat of the general-`N`
headline and the POVM tranche** (additively at landing; the corpus-wide call-site migration
executed 2026-06-11 — ContextVolume, BellVolume, GHZVolume, and the six POVM witnesses now
consume the `_uncond` forms with their engine-inherited genericity hypotheses dropped).

**Part 2 — the instantiation** (`LF5/FlowBornFrequency.lean`): at `P = basisPOVM N`,
`D = vnNaimark N`, `ψ' = piLpCongrLeft e (Vψ)` (unit, derived; genuinely non-generic):
`vnDilation_pointer_volume` — pointer-`i` committed FS volume (block sum over `{(n,i)}`) =
`‖⟨eᵢ,ψ⟩‖²` for **every** unit `ψ`; `vnDilation_pointer_frequency` (the LF5-D capstone) —
i.i.d. FS trials on the dilated `ℂℙ^{N·N−1}` ⟹ a.s. pointer-block frequencies → the Born
weights. Foundational-triple-only, 8 AxiomAudit pins, Tier-A audited SOUND (carving tripwire
explicitly probed: `bornRegion` is the unchanged audited definition, the zero branch *derives*
measure 0 from `det = 0` geometry — executed probe confirmed the off-diagonal cell of `Vψ` gets
FS-measure 0 from the amplitude formula, not by assertion; statement identity with the audited
originals kernel-checked by `rfl` proof-term probes; capstone hypotheses inhabited by an
executed `Measure.infinitePi` i.i.d. construction at N=2). Original spec below.

Instantiate `povm_born_eq_dilated_volume` and `povm_born_frequency_volume` at `P_proj` + the
LF5-C dilation ⟹ pointer-`i` FS-volume = `⟨ψ,Eᵢψ⟩ = ‖⟨eᵢ,ψ⟩‖²`, and i.i.d. FS trials ⟹
pointer-`i` frequency → `‖⟨eᵢ,ψ⟩‖²`. *Risk:* low — direct instantiation, once LF5-C builds the
`NaimarkDilation` witness.

### LF5-E — capstone + honest documentation  [NEW; wiring] — **DONE 2026-06-11** (`CsdLean4/LF5/Capstone.lean`)
Delivered: the layer headline **`measurement_flow_born_frequency`** — a five-conjunct pure
assembly of the audited LF5-B/C/D results: (1) `Φ_vN ≠ id`; (2) FS measure-preserving, at the
same `p₀` the trials are drawn from; (3) the flow realises the dilation for **every**
preparation `φ` (the context-fixedness conjunct, ∀-quantified); (4) pointer-`i` committed FS
volume block sum = `‖⟨eᵢ,ψ⟩‖²`; (5) a.s. pointer-block frequencies → Born. Docstring records
the de-isolation reading, the context-fixedness distinction (flow + block partition
ψ-independent; the volume-realising `bornRegion ψ'` cells preparation-dependent with measures
forced by the unconditional engine, not cut to fit), the ContextMap connection (the LF3
contextual outcome-map slot realised dynamically as outcome *statistics*; a per-microstate
outcome *function* is owed on `bornRegion` pairwise disjointness, open since `aeece86`), and
the named non-goals (Born reused not re-derived; A5 posited; entanglement deferred).
Foundational-triple-only, AxiomAudit-pinned, Tier-A audited SOUND (tripwire clean: the pointer
index enters only through the fixed block `{(n,i)}` via `e (n,i)`; all five conjuncts
verbatim-match their sources; hypotheses inhabited at a concrete N=2 i.i.d. witness with
state-sensitive conclusion — block volumes 1 vs 0 at `ψ = e₀`). **The LF5 plan is complete:
the single-system projective tier of D1 is closed.** *Addendum 2026-06-11:* the audit-probe
i.i.d. witness is now an in-tree theorem — `measurement_flow_born_frequency_canonical`
(`CsdLean4/LF5/CapstoneCanonical.lean`) discharges the whole trial bundle with the canonical
coordinate process `fsTrialMeasure p₀ = Measure.infinitePi (fun _ => fubiniStudyMeasure p₀)`
(`CsdLean4/LF4/TrialWitness.lean`), conclusion verbatim, all `N`. Original spec below.

Named headline `measurement_flow_born_frequency`: for the von Neumann measurement flow `Φ_vN`
and the context-fixed pointer regions `blockProj i`, repeated trials (FS-typical over the joint
fibre, the isolated-region typicality) ⟹ pointer-`i` empirical frequency → `‖⟨eᵢ,ψ⟩‖²`, with
`Φ_vN ≠ id` the fixed de-isolation dynamics. Docstring records: single-system projective; flow
fixed (vN permutation coupling); pointer region context-fixed (apparatus basis), not carved;
Born from the reused FS-volume engine, now dynamical; entanglement/non-locality + A5 deferred.
Connect to `LF3/ContextMap.lean` (`MeasurementContext`): LF5 realises that context slot
*dynamically* rather than definitionally.

### LF5-F — bornRegion disjointness + the per-microstate outcome map  [post-plan extension] — **DONE 2026-06-14** (`CsdLean4/LF4/BornRegionDisjoint.lean` + `CsdLean4/LF5/PointerOutcome.lean`)
Closes the owed-since-`aeece86` caveat of LF5-E (outcome *statistics*, not an outcome
*function*). Delivered:

- **engine half** (`LF4/BornRegionDisjoint.lean`): image-level pairwise disjointness of the
  moment-subdivision cells, **unconditional** for any `b` in the closed free simplex —
  `replaceMap_image_disjoint_replaceMap` (free/free) and `replaceMap_image_disjoint_apexMap`
  (free/apex), division-free coordinate arguments (`x_j b_i − x_i b_j = t_j b_i ≥ 0` both ways
  ⟹ `b_i = b_j = 0` ⟹ contradiction); `bornRegion_pairwiseDisjoint` (preimages of disjoint
  sets, every `ψ ≠ 0`, no norm — the Born vector is in the closed free simplex by
  `ratioN_momentMap_nonneg` / `_sum_le_one`); a.e. coverage `bornRegion_ae_cover`
  (`measure_iUnion` over the disjoint measurable family sums to `∑‖⟨eᵢ,ψ⟩‖² = ‖ψ‖² = 1`); the
  per-microstate outcome map `bornOutcome : CPN (M+1) → Option (Fin (M+1))`
  (`bornOutcome_eq_some_iff`, `bornOutcome_preimage_some`, `bornOutcome_measurable` — `⊤`
  σ-algebra on the finite `Option (Fin ·)`, `bornOutcome_ae_isSome` total off an FS-null set);
  the indicator-of-disjoint-union bridge `indicator_iUnion_disjoint`
  (`Finset.indicator_biUnion_apply`).
- **LF5 half** (`LF5/PointerOutcome.lean`): `vnPointerOutcome = bornOutcome` post-composed with
  the **ψ-independent, context-fixed** block assignment `c ↦ (e.symm c).2` (the audited
  tripwire); `vnPointerOutcome_preimage_some` (the `some i` fibre = the pointer-`i` block union
  `⋃ n, bornRegion ψ' (e (n,i))`); `measurement_flow_outcome_frequency` — the conjunct-(5)
  **upgrade**: the frequency of trials whose microstate's *outcome* is pointer `i` (a **single**
  union event per pointer, not a sum of cell frequencies) → `‖⟨eᵢ,ψ⟩‖²`, same hypotheses as the
  capstone (conjuncts 1–4 referenced, not duplicated); `measurement_flow_outcome_frequency_canonical`
  on the canonical i.i.d. FS process.
- **debt closure** (`Empirical/CSD/ContextVolume.lean`): `block_born_frequency_volume_event` —
  the degenerate-block frequency as the frequency of a single union event (the `aeece86`-owed
  restatement), now that the per-ray cells are pairwise disjoint; the sum form untouched.

The ContextMap slot (`LF3/ContextMap.lean`) is now realised **both dynamically and
definitionally** for the single-system measurement: per-context state space = dilated `Σ'`,
outcome map = `vnPointerOutcome` (deterministic, total off an FS-null set, measurable fibres),
context enters through the fixed coupling + the ψ-independent block assignment. Honest residue
unchanged from LF5-D/E: cell *shapes* (`bornRegion ψ'`) remain ψ'-dependent (engine realisation,
measures forced by Kähler geometry not carved); Born number from the engine; A5 posited; `Φ = id`
in the static `SectorData` instances (the LF5 flow `Φ_vN ≠ id` is on `Σ'`); entanglement deferred.
Foundational-triple-only, 7 new AxiomAudit pins (`bornRegion_pairwiseDisjoint`,
`bornOutcome_preimage_some`, `bornOutcome_ae_isSome`, `vnPointerOutcome_preimage_some`,
`measurement_flow_outcome_frequency`, `_canonical`, `block_born_frequency_volume_event`).

## 3. What this closes, honestly

Closes the "`Φ = id` everywhere / no measurement dynamics exercised" debt **for the
single-system projective case**: a physically-meaningful measurement `Φ ≠ id` (the von Neumann
correlating / de-isolation flow) whose committed typicality volume is the Born weight, chained
to frequencies. The Born number reuses the FS-volume engine (not re-derived); the dynamics is
genuine (not assumed). Entangled / non-local de-isolation and the A5 derivation remain the
deeper open content.

## 4. Recommended order

LF5-A → LF5-B → LF5-C → LF5-D → LF5-E. Each via the expert→auditor→commit(+doc) loop, with the
doc-currency discipline (update this file + INDEX + carve-out-plan §6 in the landing commit).
LF5-A first (foundational, bounded, low-risk). The crux is LF5-C (the dilation-from-flow
pullback); if it resists, the fallback is to state the pullback as the honest LF5 hypothesis and
discharge LF5-D conditionally, never by carving.

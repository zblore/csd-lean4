# LF5 — measurement dynamics on Σ (the D1 frontier), staged plan

Drafted 2026-06-09. **The deepest open debt (D1): `Φ = id` in every concrete sector
instance, so no measurement *dynamics* is yet exercised.** This plan attacks the
single-system, projective tier under the de-isolation reading fixed in
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

### LF5-C — de-isolation realises the dilation  [NEW; the crux assembly]
`embedGround : EuclideanSpace ℂ (Fin N) → EuclideanSpace ℂ (Fin N × Fin N)`, `ψ ↦ ψ ⊗ a₀`.
`V := (vnUnitary as linear map) ∘ embedGround`. Prove `V` is an isometry and the **pullback
identity** `Vᴴ (blockProj N i) V = |eᵢ⟩⟨eᵢ|` (= the projective POVM effect `Eᵢ`). Compute the
post-flow vector `vnUnitary *ᵥ (ψ⊗a₀) = ∑ⱼ ⟨eⱼ,ψ⟩ • (eⱼ⊗aⱼ)` and its block-`i` weight
`‖blockProj i (post)‖² = ‖⟨eᵢ,ψ⟩‖²` (reuse `blockProj_mulVec`). This inhabits
`NaimarkDilation P_proj` for the rank-1 projective POVM `P_proj` (`Eᵢ = |eᵢ⟩⟨eᵢ|`), with the
dilation now *dynamically realised* by `Φ_vN`. *Risk:* medium — the `Vᴴ Πᵢ V = Eᵢ`
bookkeeping and the tensor-index `Fin N × Fin N` ↔ `EuclideanSpace` plumbing; mirrors
`naimarkV_pullback` (reuse its proof shape).

### LF5-D — Born = volume + frequency, on the flow  [REUSE]
Instantiate `povm_born_eq_dilated_volume` and `povm_born_frequency_volume` at `P_proj` + the
LF5-C dilation ⟹ pointer-`i` FS-volume = `⟨ψ,Eᵢψ⟩ = ‖⟨eᵢ,ψ⟩‖²`, and i.i.d. FS trials ⟹
pointer-`i` frequency → `‖⟨eᵢ,ψ⟩‖²`. *Risk:* low — direct instantiation, once LF5-C builds the
`NaimarkDilation` witness.

### LF5-E — capstone + honest documentation  [NEW; wiring]
Named headline `measurement_flow_born_frequency`: for the von Neumann measurement flow `Φ_vN`
and the context-fixed pointer regions `blockProj i`, repeated trials (FS-typical over the joint
fibre, the isolated-region typicality) ⟹ pointer-`i` empirical frequency → `‖⟨eᵢ,ψ⟩‖²`, with
`Φ_vN ≠ id` the fixed de-isolation dynamics. Docstring records: single-system projective; flow
fixed (vN permutation coupling); pointer region context-fixed (apparatus basis), not carved;
Born from the reused FS-volume engine, now dynamical; entanglement/non-locality + A5 deferred.
Connect to `LF3/ContextMap.lean` (`MeasurementContext`): LF5 realises that context slot
*dynamically* rather than definitionally.

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

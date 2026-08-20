# P2: the composite arena — scoping note

Created 2026-08-20, executed same day. Companion to
[`eft-pillars-plan.md`](eft-pillars-plan.md) (P2),
[`arena-bridge-plan.md`](arena-bridge-plan.md) (P1, whose machinery this
composes), and `SigmaLayer/TensorReconstruction.lean` /
`SigmaLayer/TensorSolved.lean` / `SigmaLayer/TensorGeneration.lean` (the
algebra half, already landed). See also `specs/future-work.md`.

## The gap, precisely

The algebra half of composition is done: `compositeAlgReconstruction` proves
any composite algebra carrying commuting, generating local matrix algebras IS
the tensor product, and `composite_dim_eq` forces the dimension. What P2 asks
is the **arena-side analogue**: what the composite of two ontic sectors *is*,
and whether the algebra-side forcing transports to it.

## The answer (all landed in `CV/CompositeArena.lean`)

**What the composite is: mode concatenation.** The composite of a `K₁`-mode
sector and a `K₂`-mode sector is the `(K₁ + K₂)`-mode sector — an arena the
corpus already has (`FieldArena (K₁+K₂) N`), not a new species. The
identification is `configSplit : FieldConfig (K₁+K₂) N ≃ C₁ × C₂` (split a
joint configuration into its two mode blocks), and everything else is read
through it:

1. **The join (Segre map)**: `sectorJoin u v` (the Kronecker vector in field
   coordinates, with `‖u ⊗ v‖ = ‖u‖·‖v‖`) and `arenaJoin : FieldArena K₁ N →
   FieldArena K₂ N → FieldArena (K₁+K₂) N`, well-defined on rays.
2. **The local subalgebras are mode-local**: `leftOp A` / `rightOp B`
   (reindexed `A ⊗ₖ 1` / `1 ⊗ₖ B`), with ★ `leftOp_supportedOn` /
   `rightOp_supportedOn` — they are `SupportedOn` their mode blocks, so
   **every P1 theorem (statics, cones, strokes) applies to the composite arena
   with zero new proofs**.
3. **State/observable/dynamics transport along the join**:
   `arenaDM_join` (`ρ_{p⊗q} = ρ_p ⊗ₖ ρ_q`), ★ `arenaObs_join_left/right`
   (marginal readings are exact), ★ `arenaObs_join_mul` (joint expectations of
   product observables factor — local tomography read on the arena), and
   ★ `arenaKick_join` (`(U ⊗ V)`-kicks restrict along the join to the product
   action).
4. ★★ **No-signalling on the composite arena, exactly and for ALL states**
   (`composite_no_signalling`): a kick built from a right-sector unitary
   leaves every left-sector arena observable invariant — on entangled points
   too, since it is an instance of P1's `arenaObs_kick_of_disjointSupport`,
   not a consequence of the join.
5. ★★ **Entanglement is real at the arena level** (`bell_not_join`): for
   `N ≥ 2` the Bell ray is not in the image of `arenaJoin` — the composite
   arena is strictly larger than the pair of components. This is the
   arena-side signature of `⊗` versus `×`.
6. ★★ **The algebra forcing transports** (`composite_generate` +
   `compositeArenaForced`): the composite arena's own operator algebra, with
   its two mode-local subalgebras, satisfies the reconstruction's premises —
   the subalgebras commute (`leftOp_comm_rightOp`) and generate
   (`composite_generate`) — so `compositeAlgReconstruction` applies and
   forces `Matrix C₁ ⊗[ℂ] Matrix C₂ ≃ₐ Matrix C₁₂`, with
   `compositeArenaForced_tmul` pinning the map as `A ⊗ₜ B ↦ leftOp A ·
   rightOp B`. The forcing is CONSUMED from the landed theorem (through
   `Fintype.equivFin` reindexing), not re-proved.

## Walls pre-checked (why this is bounded)

Mathlib has the whole Kronecker stack (`mul_kronecker_mul`,
`one_kronecker_one`, `conjTranspose_kronecker`, `trace_kronecker`,
`add/smul_kronecker` both sides), `submatrix_mul_equiv`, `reindexAlgEquiv`,
`Algebra.TensorProduct.congr`, `matrix_eq_sum_single`, and `Equiv.sum_comp`
for the reindexed sums. The one missing piece (trace is invariant under an
`Equiv` reindex) is a two-line local lemma. The projective-layer patterns
(rep-scalar dance through `mk_eq_mk_iff'`) are P1's own, reused.

## Honest boundary

Homogeneous field sectors only: both factors share the level count `N` and
compose mode-disjointly — the field-native case, which is what the CV chain
and P1's arenas are built from. Heterogeneous composites (`N₁ ≠ N₂`, or
non-field sectors) are not claimed here; they would need the arena API
generalised over its index type (a rule-of-two note, recorded in the module).
The fibre side of the composite is the product of record media
(`RecordFibre × RecordFibre`), and per-sector record strokes on the composite
follow from P1's generic fibred machinery through `leftOp_supportedOn` — the
demonstration is `composite_no_signalling`; no separate fibred-composite
module is warranted. States enter as rays (`arenaDM` is rank-one): composite
*mixed*-state theory (partial trace as a channel, reduced states of entangled
rays) is CV-26's coarse-graining territory, not this pillar's.

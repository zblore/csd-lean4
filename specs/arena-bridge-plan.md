# P1 first arc: the arena bridge — operator locality carried onto the record arena

Status: **SCOPED AND EXECUTED 2026-08-19** (pillar **P1** of
[`eft-pillars-plan.md`](eft-pillars-plan.md); module `CV/ArenaBridge.lean`).
Deliverable: the category bridge the pillars doc named as the twice-observed
bottleneck, plus the first theorem that was previously unstatable — a
Lieb-Robinson bound at the record-arena level.

## The gap, restated precisely

The CV chain proves locality as an **operator** notion: `SupportedOn S A` on
matrices over `FieldConfig K N`, commutators, generator splits, the LR cone. The
record/sector layers live on projective arenas where locality is a
**measure-and-set** notion: regions, volumes, records. On 2026-08-10 an LR bound
on record redundancy proved unstatable because nothing translated between the two
categories. That translation is the bridge.

## Feasibility, checked before writing (the check-impossible-first record)

The bridge turns out to be three short definitions away, because every hard
ingredient landed previously, several within the last two days:

* **The norm interface is CR-1.** `QuantumInfo.abs_re_trace_mul_le`
  (`|re tr(ρM)| ≤ ‖M‖·tr ρ`, 2026-08-19) is exactly the Lipschitz bound that turns
  an operator-norm estimate into a bound on arena observables. This did not exist
  a week ago; P1's bridge is its second consumer.
* **Rank-one densities from rays**: the `vecMulVec`/`posSemidef_vecMulVec_self_star`
  pattern (LF2 `outerProduct`) generalises verbatim to the field index.
* **Unitary kicks on rays**: `Projectivization.mk` + norm preservation (the LF5
  `toEuclideanLin_norm_map_of_isom` proof; restated locally to keep CV free of an
  LF5 import — rule-of-two note recorded there).
* **The dynamics**: `heisenbergFlow` and `norm_commutator_spatial_factorial_le`
  (CV-20) supply the cone; `Matrix.exp_mem_unitaryGroup_of_skew` (CV-12 staging)
  makes the flow a genuine arena kick.

## What lands (all in `CV/ArenaBridge.lean`)

| Piece | Content |
|---|---|
| `FieldArena K N` | `ℙ ℂ (EuclideanSpace ℂ (FieldConfig K N))` — the epistemic base over the field |
| `arenaDM p` | the rank-one density of a ray: PSD, trace 1 |
| `arenaObs A p` | `re tr(ρ_p A)` — a matrix observable read as a **function on the arena** |
| `arenaKick U p` | the unitary action as an arena map (constructed, no instance needed) |
| `arenaObs_kick` | **the bridge identity**: `arenaObs A (kick U p) = arenaObs (heisenberg U A) p` — Schrödinger on the arena = Heisenberg on the operator |
| `arenaObs_sub_le` | the CR-1 Lipschitz transport: arena observables are 1-Lipschitz in the operator norm |
| ★ `arenaObs_kick_of_disjointSupport` | **statics**: an arena observable of region `S` is *exactly* invariant under any kick supported on disjoint `T` — Haag–Kastler locality, now a statement about functions on the arena |
| ★★ `arena_lightcone` | **the previously unstatable theorem**: a kick outside the graph `d`-ball of `R` changes any region-`R` arena observable after time `t` by at most `2·(2‖S‖t)^d/d! · ‖A‖` — the LR cone, at the record-arena level |

## Honest scope

* **Base arena only.** The fibred arenas (`ℂℙ^{N-1} × T²`) are not touched;
  functions on the fibred arena that factor through the base inherit everything,
  and the fibre-active extension is the named follow-up.
* **The bridge, not the characterisation.** P1's definitional half — *a
  field-structured flow* as a structure, with the generator decomposing into local
  pieces — is not claimed here; this arc supplies the transport that any such
  definition will be stated against.
* Observables enter as `re tr(ρA)`; general measurable functions on the arena are
  outside this arc (the Lipschitz class through matrices is what the LR machinery
  can price).

## References

`specs/eft-pillars-plan.md` (P1, the bottleneck record);
`CV/ModeLocality.lean` (`SupportedOn`, `commute_of_disjointSupport`);
`CV/LiebRobinson.lean` (`heisenbergFlow`, `norm_commutator_spatial_factorial_le`);
`Mathlib/QuantumInfo/UnitaryPerturbation.lean` (CR-1, `abs_re_trace_mul_le`);
`Mathlib/Analysis/Matrix/TrotterProduct.lean` (`exp_mem_unitaryGroup_of_skew`);
`LF2/BornWrapper.lean` (the `outerProduct` pattern);
`LF5/DilationFromFlow.lean` (`toEuclideanLin_norm_map_of_isom`).

# P5-attainment: the linear price is attained — scoping note

Created 2026-08-20, executed same day. Companion to
[`eft-pillars-plan.md`](eft-pillars-plan.md) (P5, the attainment half) and
`CV/InteractionPrice.lean` (CV-9, the upper bound this matches). See also
`specs/future-work.md`.

## The gap, precisely

CV-9 prices locality violation from above:
`heisenberg_interactingU_near_supported` puts the interacting Heisenberg
observable of an `S`-supported `A` within `2·|τ|·|λ|·C·‖A‖` of an
`S`-supported operator. Its own scope block says what is missing: *"whether
the linear price is attained (an actual violation rate) is a dynamics
question not claimed here."* P5's attainment half: a matching **lower**
bound, turning "costs at most" into "costs exactly" (up to constants).

## The mechanism (all landed in `CV/PriceAttainment.lean`)

1. **The commutator functional prices distance from below**
   (`norm_commutator_le_of_commute`): any `S`-supported `B` commutes with a
   disjointly supported probe `P` (CV-2b), so
   `‖[X,P]‖ = ‖[X−B,P]‖ ≤ 2‖X−B‖‖P‖` — a commutator with a unit probe is a
   lower bound on the distance to the whole `S`-supported subalgebra.
2. **The witness computes exactly** (`K = N = 2`): observable
   `A = modeOp 0 (single 0 1)` on mode 0, probe `P = modeOp 1 (single 0 1)`
   on mode 1, pair coupling `v(c) = [c₀ = 1 ∧ c₁ = 1]`. The interacting
   drive is a diagonal phase, so the conjugated observable's entries are
   explicit phases, and the commutator entry at
   `(config (0,0), config (1,1))` is `e^{iα}(1 − e^{−iτλ})` — the two paths
   through the commutator pick up free phases that cancel (energy is
   mode-additive) and coupling phases that do not (the coupling reads both
   modes). Its modulus is `2·|sin(τλ/2)|`, exactly.
3. ★★ `price_lower_bound`: for EVERY `{0}`-supported `B`,
   `|sin(τλ/2)| ≤ ‖heisenberg (interactingU 2 2 τ λ v) A − B‖`.
4. ★★ `price_linear_attained` — **the sandwich** (for `0 ≤ τλ ≤ π`, via
   Jordan's inequality `Real.mul_le_sin`):
   `τλ/π ≤ dist ≤ 2·τλ`. The price of locality violation is **linear in
   the coupling on both sides** — attained, not just bounded.

## Walls pre-checked (why this is bounded)

`Matrix.norm_entry_le_l2_opNorm` is already staged (corpus,
`L2OpNormEntry.lean`); `l2_opNorm_modeOp_le` (CV-10) bounds the probe;
`heisenberg_phaseDiagU_apply` (CV-6) gives the conjugated entries in closed
form; `commute_of_disjointSupport` (CV-2b) gives the functional;
`Real.mul_le_sin` (Jordan) and `Real.abs_sin_half` are in Mathlib. The only
computation is a four-config finite sum collapse.

## Honest boundary

One witness, one coupling shape, at `K = N = 2` — attainment is an existence
claim, so a witness is exactly what it needs; no claim that every drive
saturates the bound, and the constants are not matched (`1/π` vs `2`; on
this witness the true distance is `2|sin(τλ/2)|`-shaped, but the exact
distance identification is not claimed). The upper bound stays CV-9's, with
`C = 1` and `‖A‖ ≤ 1`.

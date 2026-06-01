# Partial-trace infrastructure tranche (unblocks E2 + E3b)

Status: planning doc, 2026-06-01. Goal: add a partial-trace construction to the
CSD Mathlib staging tree (a genuine Mathlib gap) + the LF2 reduced-density
consumer, then discharge E3b (no-communication, reduced-density form). E2
(no-broadcasting) is statement-enabled but its proof is a separate future tranche.

## Reconnaissance verdict

**Mathlib has NO partial trace** (zero hits: `partialTrace`/`traceLeft`/`traceRight`).
Every supporting lemma exists, so this is assembly of a new Cat-1 definition + API,
not a blocked gap:
- `Matrix.trace_kronecker` (`Tr(A⊗B)=Tr A·Tr B`), `Matrix.trace_sum`.
- `Matrix.posSemidef_sum`, `Matrix.posSemidef_iff_dotProduct_mulVec`.
- `Matrix.submatrix`, `Fintype.sum_prod_type` / `Finset.sum_product`.

## Design decision (resolved 2026-06-01)

**Parametric `DensityOperatorIx ι`** chosen over keeping `Fin N` + a
`Fin (m*n) ≃ Fin m × Fin n` reindex bridge. Cleaner, no reindex friction, more
natural object. Mild duplication with the existing `DensityOperator (Fin N)`;
can later prove they agree via `finProdFinEquiv` if a consumer needs the bridge.

## Layer 1 — Cat-1 staging file `CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean`

Namespace `Matrix` (natural symbol namespace, CONVENTIONS §1 Cat-1). CSD-free.
`**Provenance.**` + `**Consumers.**` notes. AxiomAudit-pinned. Upstreamable
(partial trace is a longstanding Mathlib gap).

**Definition.**
```
def traceRight (A : Matrix (m × n) (m × n) R) : Matrix m m R :=
  fun i j => ∑ k, A (i, k) (j, k)        -- trace out the second (Bob) factor
def traceLeft  (A : Matrix (m × n) (m × n) R) : Matrix n n R :=
  fun i j => ∑ k, A (k, i) (k, j)        -- trace out the first (Alice) factor
```

**API lemmas (the upstreamable content):**
1. `traceRight_kronecker : traceRight (A ⊗ₖ B) = (trace B) • A` (defining
   property; `kroneckerMap_apply` + `Finset.sum` + `Matrix.trace`). Risk LOW.
2. `trace_traceRight : trace (traceRight A) = trace A` (trace-preserving;
   `∑ᵢ ∑ₖ A(i,k)(i,k) = trace A` via `Fintype.sum_prod_type`). Risk LOW.
3. `traceRight_add`, `traceRight_smul` (linearity; `Finset.sum_add_distrib`). LOW.
4. `traceRight_conjTranspose : (traceRight A)ᴴ = traceRight Aᴴ` ⟹
   `IsHermitian A → (traceRight A).IsHermitian`. LOW-MED.
5. `traceRight_posSemidef : A.PosSemidef → (traceRight A).PosSemidef`
   (LOAD-BEARING). Route: `posSemidef_iff_dotProduct_mulVec`; for test `x : m → R`,
   `star x ⬝ᵥ traceRight A *ᵥ x = ∑ₖ star(emb x k) ⬝ᵥ A *ᵥ (emb x k) ≥ 0` as a
   `posSemidef_sum` over the embedded vectors `emb x k := fun (i,l) => x i * (if l=k then 1 else 0)`.
   Risk MED (the embedding bookkeeping; mechanical via the iff).

(`traceLeft` symmetric; provide both or derive `traceLeft` from `traceRight` via
`submatrix Prod.swap`.)

## Layer 2 — LF2 consumer `DensityOperatorIx`

New parametric structure (new file `CsdLean4/LF2/ReducedDensity.lean`, or append):
```
structure DensityOperatorIx (ι : Type*) [Fintype ι] [DecidableEq ι] where
  M : Matrix ι ι ℂ ; isHermitian ; nonneg : M.PosSemidef ; trace_one : M.trace = 1
def DensityOperatorIx.reduced (ρ : DensityOperatorIx (m × n)) : DensityOperatorIx m
  -- M := traceRight ρ.M ; fields ← Layer-1 (4),(5),(2)+ρ.trace_one
```
Foundational triple; AxiomAudit-pinned.

## Payoffs (separate follow-up commits, NOT this tranche)

- **E3b** `no_communication_reduced`: `traceRight ((U⊗I) ρ (U⊗I)ᴴ) = traceRight ρ`
  for unitary `U` (Alice's local op leaves Bob's reduced state invariant). Small
  once Layer 1 lands — conjugation collapse via the kronecker mixed-product +
  `traceRight_kronecker`-style algebra. `specs/qm-empirical-tests.md` E3b row.
- **E2 no-broadcasting** (Barnum et al. 1996): needs partial trace PLUS a
  commuting-broadcast argument. Layer 1 unblocks the STATEMENT; the proof is its
  own tranche. NOT promised here.

## Sequencing

1. Layer 1 `PartialTrace.lean` (the reusable Cat-1 artifact). ← core of the tranche
2. Layer 2 `DensityOperatorIx` + `.reduced` (LF2 consumer).
3. E3b short follow-up.
4. E2 flagged separate (statement enabled, proof not promised).

## Progress (2026-06-01) — Layers 1 + 2 DONE

- **Layer 1** `CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean` — `traceRight`,
  `traceLeft` + full API: `traceRight_kronecker`/`traceLeft_kronecker` (defining
  property `traceRight (A ⊗ₖ B) = Tr B • A`), `trace_traceRight`/`trace_traceLeft`
  (trace-preserving, via `Fintype.sum_prod_type`), `traceRight_add`/`_smul`/`_zero`,
  `traceRight_conjTranspose` + `IsHermitian.traceRight`, and the load-bearing
  `PosSemidef.traceRight` (clean: `traceRight A = ∑ k, A.submatrix (·,k) (·,k)` +
  `PosSemidef.submatrix` + `posSemidef_sum`, no test-vector bookkeeping). All four
  `traceLeft` analogues. Foundational triple.
- **Layer 2** `CsdLean4/LF2/ReducedDensity.lean` — `DensityOperatorIx ι`
  (index-parametric) + `.reduced : DensityOperatorIx (m × n) → DensityOperatorIx m`
  and `.reducedLeft`, the three structure fields discharged from the Layer-1 API.
  Foundational triple.

Both AxiomAudit-pinned. Remaining: E3b (step 3), then E2 (step 4, separate tranche).

## Honesty

Real Mathlib-track infrastructure, foundational-triple throughout. Does NOT touch
the deeper CSD debts (D1, G3b, busch); it is empirical-suite enablement +
upstreamable library content.

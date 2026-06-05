# Trace-distance triangle inequality — plan

Completes the K3 metric core (`CsdLean4/Mathlib/QuantumInfo/TraceDistance.lean`). Drafted
2026-06-05. Status: **planned, not started.**

## 0. Goal

```
traceDist_triangle : traceDist (ρ - τ).herm ≤ traceDist (ρ - σ).herm + traceDist (σ - τ).herm
```

Reduces immediately to **trace-norm subadditivity** on Hermitian matrices:

```
traceNorm_add_le : (hA : A.IsHermitian) (hB : B.IsHermitian) →
    traceNorm (hA.add hB) ≤ traceNorm hA + traceNorm hB        -- ‖A+B‖₁ ≤ ‖A‖₁ + ‖B‖₁
```

because `ρ - τ = (ρ - σ) + (σ - τ)` and `traceDist = ½ traceNorm`. The whole tranche is
this one inequality; `traceNorm` is already defined as `∑ᵢ |λᵢ| = Tr|A|` for Hermitian `A`,
which is exactly the case we need (`A, B, A+B` all Hermitian).

## 1. Why the textbook proof needs care here

The clean proof is `Tr|A+B| = Tr(S·(A+B)) = Tr(S·A) + Tr(S·B) ≤ Tr|A| + Tr|B|` with
`S = sgn(A+B)` the signature (`−I ≤ S ≤ I`). Two Mathlib obstructions:

1. **No Loewner `≤` on matrices.** `Mathlib.Analysis.Matrix.Order` does **not** register a
   `LE (Matrix n n ℂ)` instance (it would clash with the entrywise order). So every "`0 ≤ M`"
   must be phrased as `M.PosSemidef`, and "`−I ≤ S ≤ I`" as `(I − S).PosSemidef ∧ (S + I).PosSemidef`.
2. **`sgn` / the positive-eigenspace projector are discontinuous**, so the *generic* `cfc`
   (which needs `ContinuousOn f (spectrum)`) cannot build them. **Resolution:**
   `Matrix.IsHermitian.cfc f = conjStarAlgAut U (diagonal (↑∘f∘eigenvalues))` is defined for
   *any* `f : ℝ → ℝ` (continuity is only needed to connect to generic `cfc` via `cfc_eq`).
   So we build the projector with `hH.cfc (indicator {x | 0 < x})` and reason at the explicit
   conjugated-diagonal level, never invoking generic `cfc` for it.

## 2. Proof strategy — the decomposition route (PSD-predicate only)

Let `H = A + B`, and for any Hermitian `M` write its parts via `IsHermitian.cfc`:

- `posPart M := hM.cfc (fun x => max x 0)`,  `negPart M := hM.cfc (fun x => max (-x) 0)`,
- `posProj M := hM.cfc (fun x => if 0 < x then 1 else 0)`  (the discontinuous projector).

The proof:

```
Tr(posPart H) = Tr(H · posProj H)                         -- H·P = H₊  (diagonal: x·1_{x>0} = x⁺)
              = Tr(A · posProj H) + Tr(B · posProj H)
              ≤ Tr(posPart A) + Tr(posPart B)              -- key bound, ×2
```
and symmetrically (apply to `−H`, whose positive part is `negPart H`):
```
Tr(negPart H) ≤ Tr(negPart A) + Tr(negPart B)
```
Summing and using `Tr(posPart M) + Tr(negPart M) = traceNorm M` (because
`posPart + negPart = hM.cfc |·| = |M|`) gives subadditivity.

**Key bound** (`Tr(A · P) ≤ Tr(posPart A)` for `0 ≤ P ≤ I`, A Hermitian):
```
Tr(A·P) = Tr(posPart A · P) − Tr(negPart A · P)
        ≤ Tr(posPart A · P)            -- TR-PSD: negPart A, P both PSD ⟹ Tr(negPart A · P) ≥ 0
        ≤ Tr(posPart A)               -- TR-PSD: posPart A, (I − P) both PSD ⟹ Tr(posPart A·(I−P)) ≥ 0
```

## 3. Lemma DAG (with Mathlib hooks / risks)

| # | Lemma | Hook / route | Risk |
|---|---|---|---|
| L1 | `tr_psd_mul_nonneg : S.PosSemidef → P.PosSemidef → 0 ≤ Re (S*P).trace` (**TR-PSD**, the linchpin) | `√S := cfc Real.sqrt S` (PSD, `√S·√S=S`); `Tr(SP)=Tr(√S·P·√S)` (trace_mul_cycle) `= Tr(√S·P·(√S)ᴴ)` (√S herm); PSD by `P.PosSemidef.mul_mul_conjTranspose_same √S`; `≥0` by `PosSemidef.trace_nonneg` | medium — assembling √S from cfc + the cyclic step |
| L2 | `IsHermitian.cfc` algebra: `hM.cfc f * hM.cfc g = hM.cfc (f*g)`, `hM.cfc 1 = 1`, `hM.cfc id = M` | explicit `conjStarAlgAut U (diagonal …)`; `UᴴU=1`, `diagonal_mul_diagonal`, spectral theorem for `id` | medium — diagonal/conjugation bookkeeping (re_trace_cfc already exercises this pattern) |
| L3 | `posPart/negPart/posProj` PSD; `(1 − posProj) PSD`; `posPart, negPart` PSD | `hM.cfc g` PSD when `g ≥ 0`: it is `U·diag(g∘λ)·Uᴴ = B·(B)ᴴ`-shaped with `B = U·diag(√(g∘λ))`; or `diagonal` of nonneg is PSD then conjugate (`PosSemidef.mul_mul_conjTranspose_same`) | low–medium |
| L4 | `H · posProj H = posPart H`; `posPart M + negPart M = hM.cfc \|·\|` | L2 + pointwise `x·1_{x>0} = max x 0`, `max x 0 + max (-x) 0 = \|x\|` (real lemmas) | low |
| L5 | `Tr(posPart M) + Tr(negPart M) = traceNorm M` | L4 + `re_trace_cfc hM (\|·\|)` (already proved) + traces of PSD are real (`PosSemidef.trace … `) | low |
| L6 | key bound `Tr(A·P) ≤ Tr(posPart A)` for `A` herm, `P, (1−P)` PSD | L1 (×2) + L3 + `Tr(A·P)=Tr(posPart A·P)−Tr(negPart A·P)` (`A = posPart−negPart`, `sub_mul`, `trace_sub`) | medium |
| L7 | `Tr(posPart H) ≤ Tr(posPart A) + Tr(posPart B)` | L4 (`Tr posPart H = Tr(H·P)`), `H=A+B` (`add_mul`, `trace_add`), L6 ×2 with `P = posProj H` | low |
| L8 | `traceNorm_add_le` (subadditivity) | L7 + the `−H` symmetric version + L5 | low |
| L9 | `traceDist_triangle` | L8 + `½` arithmetic + `(ρ-τ) = (ρ-σ)+(σ-τ)` (`traceNorm_congr`) | low |

All real-analysis pointwise facts (`x·1_{x>0}=x⁺`, `x⁺+x⁻=|x|`, `x⁺−x⁻=x`) are elementary
`Real` lemmas (`max`, `abs`), dischargeable by `rcases le_or_lt`/`simp`.

## 4. Risks & estimate

- **Linchpin risk:** L1 (TR-PSD). If a Mathlib lemma exists (`PosSemidef.trace_mul_nonneg`
  or via `inner`), L1 collapses to one line; `exact?` did not find it, so budget the √S route.
- **Bulk risk:** L2 (`IsHermitian.cfc` multiplicativity / `cfc id = M`). This is pure
  diagonal-conjugation algebra of the same flavour as the already-working `re_trace_cfc`.
  If it fights, fall back to proving L4 directly at the `conjStarAlgAut … diagonal` level
  without a general `cfc_mul` lemma.
- **Effort:** ~200–350 lines, one focused session (two if L2 is sticky). No new axioms;
  foundational-triple-only throughout; pins for `traceNorm_add_le` + `traceDist_triangle`.
- **Not in scope:** the CPTP data-processing inequality (still wants the variational
  characterisation; separate, larger tranche).

## 5. Open design choice

Whether to expose `posPart`/`negPart`/`posProj` as named `QuantumInfo` defs (reusable for
later K3 work — fidelity, the variational bound) or keep them `private` to the proof.
Recommendation: **named**, since the Jordan decomposition and the positive projector recur
in the data-processing inequality and in QEC fidelity.

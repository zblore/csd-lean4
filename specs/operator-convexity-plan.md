# Operator-convexity ladder → data-processing inequality (`hDPI`) for SSA

**Status:** L.0 (scout + predicate) **DONE 2026-06-17**; L.1 (operator convexity of
`x ↦ x⁻¹`) **DONE 2026-06-17**; L.2 (operator concavity of `log`) **WALLED** (precise
gap below); L.3–L.5 **not started**.

**Module:** `CsdLean4/Mathlib/Analysis/Matrix/OperatorConvex.lean` (Cat-1, CSD-free,
natural Mathlib namespace `Matrix`).

**Endpoint.** Discharge the `hDPI` hypothesis of
`CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity.strong_subadditivity_of_relEntropy_monotone`
(K1-C) by a genuine new-math route, NOT an axiom. `hDPI` is the data-processing inequality
(equivalently joint convexity of quantum relative entropy / Lieb concavity). This is a
multi-week ladder; this file is the live status + per-rung sizing.

---

## L.0 — Scout findings (current Mathlib pin: Lean 4.29.0-rc8 / Mathlib HEAD 2026-05-28)

What exists and is reused, by file:

- **Löwner order.** `Mathlib/Analysis/Matrix/Order.lean` (Monica Omar, 2025):
  - `Matrix.instPartialOrder` — scoped `MatrixOrder`, `A ≤ B := (B - A).PosSemidef`.
    `open scoped MatrixOrder` to use.
  - `Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef`.
  - `Matrix.nonneg_iff_posSemidef`, `LE.le.posSemidef`, `PosSemidef.nonneg`.
  - `Matrix.instStarOrderedRing`, `instIsOrderedAddMonoid`, `instNonnegSpectrumClass`.
  This is THE order for the whole ladder. Used: every rung.

- **Schur complement / block PSD.** `Mathlib/LinearAlgebra/Matrix/PosDef.lean`:
  - `Matrix.PosDef.fromBlocks₁₁ (B D) (hA : A.PosDef) [Invertible A] :`
    `(fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef` — the Schur PSD
    characterisation. **This is the engine of L.1.** Used: L.1.
  - `Matrix.PosDef.fromBlocks₂₂` (the `₂₂` mirror).
  - `Matrix.schur_complement_eq₁₁/₂₂` (Hermitian.lean) — the underlying quadratic identity.

- **PD / PSD algebra.** `LinearAlgebra/Matrix/PosDef.lean`, `Analysis/Matrix/PosDef.lean`:
  - `PosSemidef.add`, `PosSemidef.smul (ha : 0 ≤ a)` (complex-scalar; needs
    `0 ≤ (a:ℂ)` under `ComplexOrder`), `PosSemidef.zero`.
  - `PosDef.smul (ha : 0 < a)`, `PosDef.add`, `PosDef.add_posSemidef`, `PosDef.inv`.
  - `PosDef.isUnit`, `IsUnit.invertible` (noncomputable) → `[Invertible A]`.
  - `IsHermitian.posDef_iff_eigenvalues_pos`, `PosDef.eigenvalues_pos`.
  - `posSemidef_iff_isHermitian_and_spectrum_nonneg`.
  - `Matrix.spectrum_real_eq_range_eigenvalues` (Analysis/Matrix/Spectrum.lean).

- **CFC on matrices.** `Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean`:
  - `instance : ContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint` (the generic
    `cfc` works on Hermitian matrices). `Matrix.IsHermitian.cfc_eq` bridges to the explicit
    spectral triple product. Generic CFC lemmas used: `cfc_id`, `cfc_mul`, `cfc_one`,
    `cfc_congr`. Used: L.0 predicate, L.1 (`cfc_inv_posDef` bridge), L.2+.

- **Rpow / ExpLog CFC.** **NOT under `Analysis/Matrix/`** (the expert note's
  `Analysis/Matrix/Rpow/IntegralRepresentation.lean`, `Rpow/Order.lean`, `ExpLog/Order.lean`
  paths do not exist at this pin). They live under
  `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/`:
  - `Rpow/Basic.lean`: `CFC.rpow_neg_one_eq_cfc_inv`, `CFC.inverse_eq_rpow_neg_one`,
    `nnrpow_*`, `inverse_rpow`. (These are CStarAlgebra-generic; they need `NormedRing A`,
    which `Matrix n n ℂ` does NOT have by default — so the rpow API does NOT directly fire
    on the bare `Matrix` type. The L.1 inverse bridge `cfc_inv_posDef` is therefore proved
    by hand via `cfc_mul`/`inv_eq_left_inv`, not via the rpow lemmas.)
  - `Rpow/Order.lean`: `CFC.monotone_rpow`, `CFC.monotone_nnrpow`, `CFC.sqrt_le_sqrt`
    (`x^p` operator monotone for `p∈[0,1]`). Used: L.3 (rpow operator concavity) input.
  - `ExpLog/Order.lean`: `CFC.log_monotoneOn` (log operator MONOTONE, proved), and the
    explicit **`## TODO: Show that the log is operator concave` / `x ↦ x log x` operator
    convex`** — confirming L.2/L.4 are genuine new math (absent upstream).
  - `ExpLog/Order.lean` `CFC.tendsto_cfc_rpow_sub_one_log`: `cfc (p⁻¹(x^p−1)) a → CFC.log a`
    as `p → 0⁺`, uniform on the spectrum. This is the scaffold for the operator-concavity-
    of-log route that BYPASSES the integral representation (see L.2 wall).

- **NO integral representation of log/inverse** in Mathlib (`Rpow/IntegralRepresentation`
  does not exist at this pin). **NO** `OperatorConvexOn` / `OperatorMonotoneOn` /
  operator-Jensen predicate anywhere (confirmed absent by grep). The predicate in L.0 is the
  first such notion in this corpus.

- **No `Matrix.schur` def**; the Schur content is the `fromBlocks₁₁/₂₂` characterisations
  above. Block algebra: `Data/Matrix/Block.lean` `fromBlocks_add`, `fromBlocks_smul`,
  `fromBlocks_one`. Used: L.1 (collapsing the convex combination of block matrices).

---

## L.0 — The predicate (landed)

```lean
def Matrix.OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ},
    A.IsHermitian → B.IsHermitian →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 →
      spectrum ℝ ((t : ℂ) • A + ((1 : ℂ) - t) • B) ⊆ s →
      cfc f ((t : ℂ) • A + ((1 : ℂ) - t) • B)
        ≤ (t : ℂ) • cfc f A + ((1 : ℂ) - t) • cfc f B
```

plus `OperatorConcaveOn` (reversed Löwner inequality). Design notes:

- **All-dimensions quantification.** `∀ {n} [Fintype n] [DecidableEq n]` is in the predicate
  body: operator convexity is genuinely a dimension-uniform notion (strictly stronger than
  scalar convexity; e.g. `x²` is convex but only operator convex, `x³` is convex but NOT
  operator convex). This is the correct definition, not a single-`n` or scalar weakening.
- **Complex scalars `(t : ℂ)`** in the convex combination: `PosSemidef.smul` wants
  `0 ≤ (a:ℂ)` (`ComplexOrder`); `Complex.coe_smul` makes `(t:ℂ) • A = (t:ℝ) • A` so no loss.
- **Spectrum-of-combination hypothesis** is explicit (rather than derived from convexity of
  `s`): keeps the predicate usable for any `s`, and is automatically satisfiable for the
  convex `s = Ioi 0` used in L.1.
- **Löwner `≤`** is `Matrix.instPartialOrder` (scoped `MatrixOrder`), the genuine PSD-cone
  order, not a trace/scalar surrogate.

---

## L.1 — Operator convexity of `x ↦ x⁻¹` (LANDED, foundational rung)

```lean
theorem Matrix.inv_loewner_convex {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((t : ℂ) • A + ((1 : ℂ) - t) • B)⁻¹ ≤ (t : ℂ) • A⁻¹ + ((1 : ℂ) - t) • B⁻¹

theorem Matrix.operatorConvexOn_inv : OperatorConvexOn (Set.Ioi 0) (fun x : ℝ => x⁻¹)
```

**Route (Schur complement / block matrix).**
1. `fromBlocks_inv_posSemidef`: for PD `A`, `⟦A, 1; 1, A⁻¹⟧` is PSD — forward direction of
   `PosDef.fromBlocks₁₁` (`B = D = 1`), Schur complement `A⁻¹ − 1·A⁻¹·1 = 0 ≥ 0`.
2. `convexComb_posDef`: `t A + (1−t) B` is PD (boundary `t=0` handled separately, interior
   via `PosDef.add_posSemidef`).
3. The PSD cone is convex: `t • ⟦A,1;1,A⁻¹⟧ + (1−t) • ⟦B,1;1,B⁻¹⟧` is PSD.
4. `fromBlocks_smul` + `fromBlocks_add` collapse it to
   `⟦t A+(1−t)B, 1; 1, t A⁻¹+(1−t)B⁻¹⟧` (the off-diagonals `1` combine to `1` since
   `t·1+(1−t)·1 = 1`, via `module`).
5. Backward `PosDef.fromBlocks₁₁` with PD pivot `t A+(1−t)B` ⇒ Schur complement
   `(t A⁻¹+(1−t)B⁻¹) − (t A+(1−t)B)⁻¹` is PSD ⇒ the Löwner inequality (`Matrix.le_iff`).

Predicate form `operatorConvexOn_inv`: spectra ⊆ `Ioi 0` ⇒ PD (`posDef_of_spectrum_pos` via
`posDef_iff_eigenvalues_pos`), then `cfc_inv_posDef` rewrites `cfc (·⁻¹)` to matrix `⁻¹` on
each PD argument, and `inv_loewner_convex` closes it.

**CFC ↔ matrix-inverse bridge** `cfc_inv_posDef {A} (hA : A.PosDef) : cfc (·⁻¹) A = A⁻¹`:
proved by hand (`cfc (·⁻¹) A * A = cfc (x⁻¹·x) A = cfc 1 A = 1` on the positive spectrum via
`cfc_mul`/`cfc_congr`, then `inv_eq_left_inv`). The rpow API (`rpow_neg_one_eq_cfc_inv`) was
NOT usable: it requires `NormedRing (Matrix n n ℂ)`, not the default instance.

**Axioms (verified `#print axioms`):** `operatorConvexOn_inv`, `inv_loewner_convex`,
`cfc_inv_posDef` all `[propext, Classical.choice, Quot.sound]` — foundational triple only,
no new `axiom`, no `sorry`. AxiomAudit-pinned.

**Auditor probe (verified):** the concrete non-commuting PD pair `A = !![2,0;0,1]`,
`B = !![1,1;1,2]` is genuinely non-commuting (`(AB)(0,1)=2 ≠ 1=(BA)(0,1)`), `inv_loewner_convex`
applies to it (general over PD pairs), and the inequality direction is `(combination)⁻¹ ≤
combination-of-inverses` (operator CONVEX, correct).

---

## L.2 — Operator concavity of `log` (ATTEMPTED, WALLED — precise gap)

**Target:** `Matrix.operatorConcaveOn (Set.Ioi 0) Real.log`.

**Two standard routes, both walled at this pin:**

1. **Integral representation** (the prompt's route):
   `log x = ∫₀^∞ (1/(1+s) − 1/(x+s)) ds`; each `x ↦ −(x+s)⁻¹` is operator concave (shift +
   negate of L.1's `inv_loewner_convex`), and the integral preserves operator concavity.
   **Wall:** Mathlib has (a) NO log integral representation (the
   `Analysis/Matrix/Rpow/IntegralRepresentation.lean` cited by the expert note does not exist
   at this pin), and (b) NO "integral of a pointwise-operator-concave family is operator
   concave" lemma. Both are multi-day sub-builds: (b) requires Bochner-integral monotonicity
   of the PSD cone (`∫ (RHS − LHS) ds` PSD from pointwise PSD integrand), and (a) requires
   formalising the resolvent integral with its convergence. The single-shift rung
   `x ↦ −(x+s)⁻¹` operator concave IS one step from L.1 (negate + translate), but the
   integral-assembly is the wall.

2. **`p⁻¹(x^p−1) → log` limit** (the route Mathlib's own `CFC.log_monotoneOn` uses):
   `CFC.tendsto_cfc_rpow_sub_one_log` gives `cfc (p⁻¹(x^p−1)) a → CFC.log a` uniformly on the
   spectrum as `p → 0⁺`. Operator concavity of `x ↦ p⁻¹(x^p−1)` for `p∈[0,1]` reduces to
   operator concavity of `x^p` (= **L.3**, itself unbuilt), and the operator-concave set must
   be shown closed under this limit (an `isClosed_operatorConcaveOn`-style lemma, analogue of
   `isClosed_monotoneOn`, which does NOT yet exist for the convexity predicate).
   **Wall:** depends on L.3 (`x^p` operator concave, `p∈[0,1]`) AND a closedness lemma for the
   new `OperatorConcaveOn` predicate. This route does NOT use L.1's inverse.

**Honest verdict:** L.2 is not a one-or-two-lemma extension of L.1 at this Mathlib pin. It is a
genuine sub-build (estimate below). Not faked; the `_log` operator-concavity TODO is open
upstream too (`ExpLog/Order.lean ## TODO`).

---

## Remaining ladder L.2 → L.5 and realistic sizing

The honest path to `hDPI`/SSA does NOT go straight from L.1-inverse to relative entropy; the
load-bearing analytic facts are operator concavity of `log` (for `S(ρ) = −Tr ρ log ρ` and
relative entropy) and joint convexity / Lieb concavity. Realistic decomposition:

- **L.2 — `log` operator concave on `(0,∞)`.** ~3–6 working days. Via route 2: needs L.3 first,
  plus a `isClosed {f | OperatorConcaveOn s f}`-style limit lemma in the CFC-continuity
  topology (model on `isClosed_monotoneOn` + `tendsto_cfc_fun`). Via route 1: ~1–2 weeks
  (formalise the resolvent integral representation + integral-preserves-concavity). Route 2 is
  cheaper given Mathlib's existing `tendsto_cfc_rpow_sub_one_log` scaffold.

- **L.3 — `x ↦ x^p` operator concave for `p∈[0,1]` (and `x^p` operator convex for
  `p∈[1,2]∪[−1,0]`).** ~3–5 days. Löwner–Heinz territory. Mathlib has operator MONOTONICITY of
  rpow (`CFC.monotone_rpow`) but not operator CONCAVITY. The clean Lean route is again the
  Schur/`fromBlocks` 2×2 positivity argument or the integral representation
  `x^p = c_p ∫₀^∞ x/(x+s) s^{p−1} ds` (same integral-assembly wall as L.2 route 1, so L.3 and
  L.2-route-1 share the missing "integral preserves operator concavity" lemma — building that
  lemma once unlocks both).

- **L.4 — `x ↦ x log x` operator convex; operator Jensen.** ~3–5 days. `x log x` operator
  convexity is the other `ExpLog/Order.lean` TODO; follows from L.2 (`−log` operator convex)
  via the standard `x log x` manipulation, OR from the operator-Jensen inequality (which itself
  may want a separate dilation-theoretic build). Operator Jensen (for unital CP maps / general
  contractions) is the reusable headline.

- **L.5 — joint convexity of relative entropy / Lieb concavity ⇒ `hDPI`.** ~1–2 weeks. This is
  the summit: `(ρ,σ) ↦ Tr ρ(log ρ − log σ)` jointly convex, equivalently Lieb's concavity of
  `(A,B) ↦ Tr(KᴴA^t K B^{1−t})`. Standard derivations route through operator concavity of `log`
  (L.2) + the operator-Jensen / Ando convexity machinery (L.4), then DPI via the Stinespring /
  partial-trace contraction. Connecting to the existing `relEntropy` definition and
  `strong_subadditivity_of_relEntropy_monotone`'s exact `hDPI` shape is additional plumbing.

**Total remaining to discharge `hDPI`:** order **4–7 working weeks** beyond L.1, the bulk in
the shared "integral preserves operator concavity" lemma (unlocks L.2-route-1 + L.3) OR the
`isClosed`-of-operator-concave + L.3 chain (L.2-route-2), then L.4 + L.5. The single highest-
leverage next rung is **the operator-concavity closedness lemma + L.3 (`x^p` operator concave,
`p∈[0,1]`)**, since they jointly unlock L.2 route 2.

---

## Precise next rung (recommended)

**L.3a — `Matrix.operatorConcaveOn (Set.Ici 0) (fun x => x ^ p)` for `p ∈ [0,1]`**, via the
Schur/`fromBlocks` 2×2-positivity argument (the same engine as L.1, applied to the `x^p`
generalized-mean inequality), OR establish the reusable infrastructure lemma
**`isClosed {f | OperatorConcaveOn s f}` under `tendsto_cfc_fun`** first (analogue of
`isClosed_monotoneOn`). Either unlocks L.2 route 2. Estimate 3–5 days. Land it Gleason-free,
foundational-triple-only, AxiomAudit-pinned, and update this file's status row.

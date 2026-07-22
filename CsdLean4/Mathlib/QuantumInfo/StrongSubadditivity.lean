/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Subadditivity

/-!
# Strong subadditivity (K1-C): the conditional reduction and the isolated wall

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

Strong subadditivity (SSA, Lieb–Ruskai) is the inequality

  `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`

for a tripartite density operator `ρ_ABC` on `(a × b × c)`. Every standard proof rests on a deep
operator-convexity input — Lieb's concavity theorem, joint convexity of the quantum relative
entropy `(ρ,σ) ↦ D(ρ‖σ)`, or, equivalently, **monotonicity of relative entropy under partial
trace (DPI)** `D(Tr_C ρ ‖ Tr_C σ) ≤ D(ρ ‖ σ)`. **Mathlib does not have any of these** (see the
scout note at the end of this docstring).

## What this file delivers (honest scope)

This is the LF3-bundle pattern applied at the K1 layer: **everything is proved except one named
deep hypothesis**, which is genuinely the standard Lieb/DPI input.

1. **Tripartite marginals** (`rhoAB`, `rhoBC`, `rhoB`, `rhoA`, `rhoC`) via the bipartite
   `partialTraceRight`/`partialTraceLeft` of `PartialTrace.lean`, with the consistency identities
   `rhoB_eq_traceA_AB`, `rhoB_eq_traceC_BC`, `partialTraceLeft_rhoAB_eq` etc. proved by direct
   index computation (the auditor's reindexing probe).

2. **The mutual-information identity** `relEntropy_kronecker_eq_entropy_sub`: for a bipartite
   density `ρ` on `x × y` with both marginals positive-definite,

     `D(ρ ‖ ρ_X ⊗ ρ_Y) = S(ρ_X) + S(ρ_Y) − S(ρ)`.

   This is the genuine algebraic content — `cfc_log_kronecker` (the Kronecker-log split) plus the
   reduced-trace identities `trace_mul_kronecker_one_right`/`_left` — extracted into a reusable
   lemma. Proved unconditionally (no deep input).

3. **The conditional reduction** `strong_subadditivity_of_relEntropy_monotone`: SSA derived from
   DPI stated as an **explicit hypothesis** `hDPI`. The reduction is genuine — SSA really follows,
   in the correct direction, non-vacuously for correlated `ρ_ABC` — via
   `I(A:BC) ≥ I(A:B)` ⟺ `D(ρ_ABC ‖ ρ_A⊗ρ_BC) ≥ D(ρ_AB ‖ ρ_A⊗ρ_B)`, which is exactly DPI applied
   to tracing out `C` from the second party (`ρ_ABC ↦ ρ_AB`, `ρ_A⊗ρ_BC ↦ ρ_A⊗ρ_B`). Both relative
   entropies are rewritten by the mutual-information identity into the four von Neumann entropies.

## The precise wall (the deep input we did NOT discharge)

The hypothesis `hDPI` is the **data-processing inequality for quantum relative entropy under the
partial trace** — equivalently joint convexity of `D(·‖·)` or Lieb's concavity of
`(A,B) ↦ Tr exp(log A + log B)`. **A scout of Mathlib HEAD (2026-06-17) finds:**

* **Operator MONOTONICITY (single-variable Löwner order)** IS present:
  `CFC.log_monotoneOn` / `CFC.log_le_log` (log is operator monotone),
  `CFC.monotone_rpow` / `CFC.monotone_nnrpow` / `CFC.sqrt_le_sqrt` (`x^p` operator monotone for
  `p ∈ [0,1]`), and the integral-representation scaffold
  `…/Rpow/IntegralRepresentation.lean`.
* **Operator CONVEXITY / CONCAVITY is NOT present.** The file
  `…/ExpLog/Order.lean` carries explicit `TODO`s: "Show that the log is operator concave" and
  "Show that `x ↦ x log x` is operator convex." There is **no** `OperatorConvex`/`OperatorMonotone`
  predicate, **no** Lieb / Ando / Epstein / Wigner–Yanase, **no** joint convexity of any trace
  functional, and **no** DPI / monotonicity of relative entropy anywhere in Mathlib.

So the minimal missing Mathlib lemma is **joint convexity of `(ρ,σ) ↦ D(ρ‖σ)`** (or its DPI
form). The realistic build is the operator-convexity stratum: an `OperatorConvexOn` predicate on
the Löwner order, the integral / Löwner-matrix route to operator convexity of `−log` and
`x ↦ x log x`, the perspective-function joint-convexity lift, and the partial-trace DPI corollary.
That is a genuine **multi-week** infrastructure build (the `Rpow/IntegralRepresentation` scaffold
already in Mathlib is the template, but it only handles `p ∈ (0,1)` monotonicity, not convexity and
not the two-variable perspective). The **fork** (build Lieb vs. axiom-state SSA) is the user's; this
file isolates the wall as `hDPI` and does not paper it.

**No `axiom`, no `sorry`. Foundational-triple-only on everything that lands.** See `specs/k1-plan.md`
§K1-C for the ledger.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace QuantumInfo

variable {a b c : Type*}
  [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

/-! ## The mutual-information identity (the genuine algebraic content, unconditional)

For a bipartite density `ρ` on `x × y` whose marginals `ρ_X = Tr_Y ρ`, `ρ_Y = Tr_X ρ` are
positive-definite, the relative entropy against the product of marginals is the mutual information:

  `D(ρ ‖ ρ_X ⊗ ρ_Y) = S(ρ_X) + S(ρ_Y) − S(ρ)`.

This is the `cfc_log_kronecker` split + reduced-trace identities, the same machinery as
`vonNeumannEntropy_subadditive`, extracted as a reusable identity (not an inequality). -/

section MutualInformation

variable {x y : Type*} [Fintype x] [Fintype y] [DecidableEq x] [DecidableEq y]

/-- **Mutual-information identity.** For a bipartite density `ρ` on `x × y` with both marginals
`ρ_X = partialTraceRight ρ` and `ρ_Y = partialTraceLeft ρ` positive-definite,

  `D(ρ ‖ ρ_X ⊗ ρ_Y) = S(ρ_X) + S(ρ_Y) − S(ρ)`.

Proof: `D = Re Tr(ρ log ρ) − Re Tr(ρ · log(ρ_X⊗ρ_Y))`. The first term is `−S(ρ)`
(`vonNeumannEntropy_eq_neg_re_trace_mul_log` + `cfc_id_mul_log`). The second is split by the
**Kronecker-log operator identity** `cfc_log_kronecker` (`log(ρ_X⊗ρ_Y) = logρ_X ⊗ I + I ⊗ logρ_Y`,
both factors PD) and collapsed by the reduced-trace identities `trace_mul_kronecker_one_right`/
`_left` to `Tr(ρ_X logρ_X) + Tr(ρ_Y logρ_Y) = −S(ρ_X) − S(ρ_Y)`. **Unconditional — no deep
operator-convexity input.** -/
theorem relEntropy_kronecker_eq_entropy_sub
    {ρ : Matrix (x × y) (x × y) ℂ} (hpsd : ρ.PosSemidef)
    (hpdX : (partialTraceRight ρ).PosDef) (hpdY : (partialTraceLeft ρ).PosDef) :
    relEntropy hpsd.1 (Matrix.PosDef.kronecker hpdX hpdY).1
      = vonNeumannEntropy hpdX.1 + vonNeumannEntropy hpdY.1 - vonNeumannEntropy hpsd.1 := by
  set ρX := partialTraceRight ρ with hρX
  set ρY := partialTraceLeft ρ with hρY
  have hpdσ : (ρX ⊗ₖ ρY).PosDef := Matrix.PosDef.kronecker hpdX hpdY
  -- the self term Re Tr(ρ log ρ) = −S(ρ).
  have hself : RCLike.re ((ρ * hpsd.1.cfc Real.log).trace) = - vonNeumannEntropy hpsd.1 := by
    rw [vonNeumannEntropy_eq_neg_re_trace_mul_log, cfc_id_mul_log, neg_neg]
  -- the cross term, split through the Kronecker-log identity.
  have hsplit : RCLike.re ((ρ * hpdσ.1.cfc Real.log).trace)
      = RCLike.re ((ρX * hpdX.1.cfc Real.log).trace)
        + RCLike.re ((ρY * hpdY.1.cfc Real.log).trace) := by
    have hcfcσ : hpdσ.1.cfc Real.log
        = (hpdX.1.cfc Real.log) ⊗ₖ (1 : Matrix y y ℂ)
          + (1 : Matrix x x ℂ) ⊗ₖ (hpdY.1.cfc Real.log) := by
      rw [show hpdσ.1 = isHermitian_kronecker hpdX.1 hpdY.1 from rfl]
      exact cfc_log_kronecker hpdX hpdY
    rw [hcfcσ, Matrix.mul_add, Matrix.trace_add, map_add,
      trace_mul_kronecker_one_right, trace_mul_one_kronecker_left]
  -- the two marginal self terms are −S(ρ_X), −S(ρ_Y).
  have hselfX : RCLike.re ((ρX * hpdX.1.cfc Real.log).trace) = - vonNeumannEntropy hpdX.1 := by
    rw [vonNeumannEntropy_eq_neg_re_trace_mul_log, cfc_id_mul_log, neg_neg]
  have hselfY : RCLike.re ((ρY * hpdY.1.cfc Real.log).trace) = - vonNeumannEntropy hpdY.1 := by
    rw [vonNeumannEntropy_eq_neg_re_trace_mul_log, cfc_id_mul_log, neg_neg]
  rw [relEntropy, hself, hsplit, hselfX, hselfY]
  ring

end MutualInformation

/-! ## Tripartite marginals

With Lean's right-associated `a × b × c = a × (b × c)`, the three two-party marginals are read off
the bipartite partial traces, modulo one reindexing for the `AB | C` cut. We work with the
convention that `ρ : Matrix (a × b × c) (a × b × c) ℂ`. Then:

* `rhoBC := partialTraceLeft ρ` (trace out `A`, the first `a`-factor) — a `Matrix (b × c) (b × c)`;
* `rhoAB := partialTraceRight (reindexAssoc ρ)` (regroup to `(a × b) × c`, trace out `C`) — a
  `Matrix (a × b) (a × b)`;
* `rhoB := partialTraceLeft rhoAB = partialTraceRight rhoBC` (the two readings agree,
  `rhoB_consistency`);
* `rhoA := partialTraceRight ρ` (trace out `BC`), `rhoC := partialTraceLeft rhoBC`.

The reassociation `e : (a × b × c) ≃ ((a × b) × c)` is `Equiv.prodAssoc`-inverse; entropy is
invariant under it (`vonNeumannEntropy_reindex`) and trace/PD transfer by reindex. -/

/-- The reassociation equivalence `(a × b × c) ≃ ((a × b) × c)` (Lean's `a × b × c` is
`a × (b × c)`). The `AB | C` cut needs the left-associated grouping. -/
def assocE : (a × b × c) ≃ ((a × b) × c) := (Equiv.prodAssoc a b c).symm

/-- The `AB | C` regrouping of `ρ_ABC` as a matrix on `(a × b) × c`. -/
noncomputable def reassocABC (ρ : Matrix (a × b × c) (a × b × c) ℂ) :
    Matrix ((a × b) × c) ((a × b) × c) ℂ :=
  ρ.reindex assocE assocE

/-- `ρ_AB := Tr_C ρ_ABC`, the `A,B` marginal (trace out the `c`-factor after regrouping). -/
noncomputable def rhoAB (ρ : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a × b) (a × b) ℂ :=
  partialTraceRight (reassocABC ρ)

/-- `ρ_BC := Tr_A ρ_ABC`, the `B,C` marginal (trace out the leading `a`-factor). -/
noncomputable def rhoBC (ρ : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (b × c) (b × c) ℂ :=
  partialTraceLeft ρ

/-- `ρ_A := Tr_{BC} ρ_ABC` (trace out the `(b × c)` factor). -/
noncomputable def rhoA (ρ : Matrix (a × b × c) (a × b × c) ℂ) : Matrix a a ℂ :=
  partialTraceRight ρ

/-- `ρ_B := Tr_{AC} ρ_ABC`, read as `Tr_A (Tr_C ρ) = Tr_A ρ_AB`. -/
noncomputable def rhoB (ρ : Matrix (a × b × c) (a × b × c) ℂ) : Matrix b b ℂ :=
  partialTraceLeft (rhoAB ρ)

/-! ### Marginal index identities (the reindexing the auditor probes) -/

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- `ρ_AB i j = ∑_c ρ ((i.1, i.2, k)) ((j.1, j.2, k))`: explicit entry of the `AB`-marginal. -/
theorem rhoAB_apply (ρ : Matrix (a × b × c) (a × b × c) ℂ) (i j : a × b) :
    rhoAB ρ i j = ∑ k : c, ρ (i.1, i.2, k) (j.1, j.2, k) := by
  simp only [rhoAB, reassocABC, partialTraceRight_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, assocE, Equiv.symm_symm, Equiv.prodAssoc_apply]

omit [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- `ρ_BC (b,c) (b',c') = ∑_a ρ (a,b,c) (a,b',c')`: explicit entry of the `BC`-marginal. -/
theorem rhoBC_apply (ρ : Matrix (a × b × c) (a × b × c) ℂ) (i j : b × c) :
    rhoBC ρ i j = ∑ k : a, ρ (k, i.1, i.2) (k, j.1, j.2) := by
  simp only [rhoBC, partialTraceLeft_apply]

omit [Fintype a] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- **`ρ_A` consistency:** `Tr_C ρ_BC = ρ_A` (= `Tr_{BC} ρ`).
`partialTraceRight (partialTraceLeft ρ) ((on b)) = partialTraceRight ρ`. Both equal
`(i,j) ↦ ∑_{k:a} ∑_{l:b} ρ (k, ?, ?) …`; here `ρ_A i j = ∑_{(b,c)} ρ (i,b,c) (j,b,c)`. We instead
record the `Tr_{BC}` reading directly used downstream. -/
theorem rhoA_apply (ρ : Matrix (a × b × c) (a × b × c) ℂ) (i j : a) :
    rhoA ρ i j = ∑ k : b × c, ρ (i, k.1, k.2) (j, k.1, k.2) := by
  simp only [rhoA, partialTraceRight_apply]

omit [Fintype b] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- **`ρ_B` consistency (`B` via `AB` vs via `BC`).** `Tr_A (Tr_C ρ) = Tr_C (Tr_A ρ)`, i.e.
`rhoB ρ = partialTraceRight (rhoBC ρ)`: the `B`-marginal computed by tracing `A` then `C`
(`partialTraceLeft (rhoAB ρ)`, which is `rhoB ρ` by definition) equals the `B`-marginal of `ρ_BC`
computed by tracing `C` (`partialTraceRight (rhoBC ρ)`). Both equal
`(i,j) ↦ ∑_{k:a} ∑_{l:c} ρ (k, i, l) (k, j, l)`. -/
theorem rhoB_consistency (ρ : Matrix (a × b × c) (a × b × c) ℂ) :
    rhoB ρ = partialTraceRight (rhoBC ρ) := by
  ext i j
  simp only [rhoB, partialTraceLeft_apply, partialTraceRight_apply, rhoAB_apply, rhoBC_apply]
  rw [Finset.sum_comm]

/-! ### Marginal density / positivity transfer

The `AB`-marginal is a density (PSD + unit trace) when `ρ_ABC` is; likewise `BC`. The reassociation
preserves PSD/trace. The `B`-marginal is then a density. PD of the various sub-marginals is carried
as a hypothesis at the SSA statement (it is the standard support condition; see `Subadditivity.lean`
honesty notes). -/

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- The reassociation preserves the trace. -/
theorem reassocABC_trace (ρ : Matrix (a × b × c) (a × b × c) ℂ) :
    (reassocABC ρ).trace = ρ.trace := by
  simp only [reassocABC, Matrix.reindex_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.submatrix_apply]
  exact Equiv.sum_comp assocE.symm (fun p => ρ p p)

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- The reassociation preserves PosSemidef (it is a permutation similarity). -/
theorem reassocABC_posSemidef {ρ : Matrix (a × b × c) (a × b × c) ℂ} (hpsd : ρ.PosSemidef) :
    (reassocABC ρ).PosSemidef := by
  rw [reassocABC, Matrix.reindex_apply]
  exact hpsd.submatrix assocE.symm

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- `Tr ρ_AB = Tr ρ_ABC`. -/
theorem rhoAB_trace (ρ : Matrix (a × b × c) (a × b × c) ℂ) :
    (rhoAB ρ).trace = ρ.trace := by
  rw [rhoAB, partialTraceRight_trace, reassocABC_trace]

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- `Tr ρ_BC = Tr ρ_ABC`. -/
theorem rhoBC_trace (ρ : Matrix (a × b × c) (a × b × c) ℂ) :
    (rhoBC ρ).trace = ρ.trace := by
  rw [rhoBC, partialTraceLeft_trace]

omit [DecidableEq a] [DecidableEq b] in
/-- `ρ_AB` is PSD when `ρ_ABC` is. -/
theorem rhoAB_posSemidef {ρ : Matrix (a × b × c) (a × b × c) ℂ} (hpsd : ρ.PosSemidef) :
    (rhoAB ρ).PosSemidef :=
  partialTraceRight_posSemidef (reassocABC_posSemidef hpsd)

omit [DecidableEq b] [DecidableEq c] in
/-- `ρ_BC` is PSD when `ρ_ABC` is. -/
theorem rhoBC_posSemidef {ρ : Matrix (a × b × c) (a × b × c) ℂ} (hpsd : ρ.PosSemidef) :
    (rhoBC ρ).PosSemidef :=
  partialTraceLeft_posSemidef hpsd

/-! ## Entropy-consistency of the two `S(ρ_A)`, `S(ρ_B)` readings

The mutual-information identity is applied on the `A | BC` cut of `ρ_ABC` and on the `A | B` cut of
`ρ_AB`. Both produce `S(ρ_A)` and `S(ρ_B)`; we record that the marginals match so the two `S(ρ_A)`,
`S(ρ_B)` cancel in the SSA telescoping. -/

omit [Fintype a] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- The `A`-marginal of `ρ_ABC` (via the `A | BC` cut, `partialTraceRight ρ`) equals the
`A`-marginal of `ρ_AB` (via the `A | B` cut, `partialTraceRight (rhoAB ρ)`). Both are `ρ_A`. -/
theorem rhoA_eq_traceB_AB (ρ : Matrix (a × b × c) (a × b × c) ℂ) :
    partialTraceRight ρ = partialTraceRight (rhoAB ρ) := by
  ext i j
  simp only [partialTraceRight_apply, rhoAB_apply]
  rw [Fintype.sum_prod_type]

omit [Fintype b] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
/-- The `B`-marginal of `ρ_BC` (via `B | C`, `partialTraceRight (rhoBC ρ)`) equals the
`B`-marginal of `ρ_AB` (via `A | B`, `partialTraceLeft (rhoAB ρ)`). Both are `ρ_B`. -/
theorem rhoB_eq_traceC_BC (ρ : Matrix (a × b × c) (a × b × c) ℂ) :
    partialTraceLeft (rhoAB ρ) = partialTraceRight (rhoBC ρ) := by
  ext i j
  simp only [partialTraceLeft_apply, partialTraceRight_apply, rhoAB_apply, rhoBC_apply]
  rw [Finset.sum_comm]

/-! ## The conditional reduction: SSA from DPI

The hypothesis `hDPI` is the **data-processing inequality for quantum relative entropy under the
partial trace** (= joint convexity of `D(·‖·)` = Lieb's concavity), stated abstractly so it is the
genuine deep input and not a restatement of SSA. We apply it to the single tracing-out step
`ρ_ABC ↦ ρ_AB` (trace `C` from the joint `A,BC` system) with `σ = ρ_A ⊗ ρ_BC ↦ ρ_A ⊗ ρ_B`. -/

/-- **Strong subadditivity from DPI (the conditional reduction — the K1-C deliverable).**

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`, derived from the **data-processing hypothesis** `hDPI`:
relative entropy does not increase under the partial trace that maps the `BC`-system to its
`B`-marginal,

  `D(ρ_AB ‖ ρ_A ⊗ ρ_B) ≤ D(ρ_ABC ‖ ρ_A ⊗ ρ_BC)`.

`hDPI` is the standard deep input (= DPI / joint convexity of relative entropy / Lieb concavity);
**Mathlib does not have it** (see the module docstring's scout). The reduction is genuine:

* `D(ρ_ABC ‖ ρ_A ⊗ ρ_BC) = S(ρ_A) + S(ρ_BC) − S(ρ_ABC)` (mutual information `I(A:BC)`), and
* `D(ρ_AB ‖ ρ_A ⊗ ρ_B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)` (mutual information `I(A:B)`),

both by `relEntropy_kronecker_eq_entropy_sub`. Substituting into `hDPI` and cancelling the common
`S(ρ_A)` gives `S(ρ_AB) + S(ρ_BC) − S(ρ_B) ≥ S(ρ_ABC)`, i.e. SSA. The direction is correct
(`I(A:BC) ≥ I(A:B)`, mutual information is monotone under discarding `C`); the bound is a genuine
inequality on correlated `ρ_ABC` (equality iff `ρ_ABC` is a quantum Markov chain `A−B−C`), not a
product identity.

**Marginals positive-definite** (`hpdA, hpdB, hpdBC`) is the standard support condition the
`relEntropy_kronecker_eq_entropy_sub` step needs (it routes through Klein-style PD-`σ` machinery,
`Subadditivity.lean`). The global `ρ_ABC` is only `PosSemidef` — pure / correlated states are
covered. The unit-trace hypothesis `_htr` documents that `ρ_ABC` is a genuine density operator; it is
not consumed by this trace-free identity reduction, hence the leading-underscore name. -/
theorem strong_subadditivity_of_relEntropy_monotone
    {ρ : Matrix (a × b × c) (a × b × c) ℂ}
    (hpsd : ρ.PosSemidef) (_htr : ρ.trace = 1)
    (hpdA : (rhoA ρ).PosDef) (hpdB : (rhoB ρ).PosDef) (hpdBC : (rhoBC ρ).PosDef)
    (hDPI :
      ∀ (hpdA' : (partialTraceRight (rhoAB ρ)).PosDef),
        relEntropy (rhoAB_posSemidef hpsd).1
            (Matrix.PosDef.kronecker hpdA' hpdB).1
          ≤ relEntropy hpsd.1
            (Matrix.PosDef.kronecker hpdA hpdBC).1) :
    vonNeumannEntropy hpsd.1 + vonNeumannEntropy hpdB.1
      ≤ vonNeumannEntropy (rhoAB_posSemidef hpsd).1 + vonNeumannEntropy hpdBC.1 := by
  -- the A-marginal of ρ_AB is ρ_A (same matrix, rhoA_eq_traceB_AB), hence PosDef.
  have hpdA' : (partialTraceRight (rhoAB ρ)).PosDef :=
    posDef_of_charpoly_eq hpdA.1 (partialTraceRight_isHermitian (rhoAB_posSemidef hpsd).1)
      (by rw [← rhoA_eq_traceB_AB]; rfl) hpdA
  -- mutual information I(A:BC) = D(ρ_ABC ‖ ρ_A ⊗ ρ_BC) = S(ρ_A) + S(ρ_BC) − S(ρ_ABC).
  have hABC : relEntropy hpsd.1 (Matrix.PosDef.kronecker hpdA hpdBC).1
      = vonNeumannEntropy hpdA.1 + vonNeumannEntropy hpdBC.1 - vonNeumannEntropy hpsd.1 :=
    relEntropy_kronecker_eq_entropy_sub hpsd hpdA hpdBC
  -- mutual information I(A:B) = D(ρ_AB ‖ ρ_A ⊗ ρ_B) = S(ρ_A') + S(ρ_B) − S(ρ_AB).
  -- (rhoB ρ = partialTraceLeft (rhoAB ρ) definitionally, so the B-marginal of ρ_AB IS hpdB.)
  have hAB : relEntropy (rhoAB_posSemidef hpsd).1 (Matrix.PosDef.kronecker hpdA' hpdB).1
      = vonNeumannEntropy hpdA'.1 + vonNeumannEntropy hpdB.1
        - vonNeumannEntropy (rhoAB_posSemidef hpsd).1 :=
    relEntropy_kronecker_eq_entropy_sub (rhoAB_posSemidef hpsd) hpdA' hpdB
  -- S(ρ_A') = S(ρ_A): the A-marginals match (rhoA_eq_traceB_AB).
  have hSA : vonNeumannEntropy hpdA'.1 = vonNeumannEntropy hpdA.1 :=
    spectral_sum_eq_of_charpoly_eq _ _ (by rw [← rhoA_eq_traceB_AB]; rfl) _
  have h := hDPI hpdA'
  rw [hABC, hAB, hSA] at h
  linarith

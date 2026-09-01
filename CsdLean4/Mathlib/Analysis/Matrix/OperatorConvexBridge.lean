/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvex

/-!
# `CStarMatrix ↔ Matrix` transport bridge for the operator-convexity ladder

`Matrix n n ℂ` is **not** a `CStarAlgebra` at its default instances: the C⋆-algebra structure
(norm, topology, spectral order) lives on the type synonym
`CStarMatrix m n A := Matrix m n A` (`CStarMatrix.instCStarAlgebra`). Consequently the
C⋆-generic continuous-functional-calculus order machinery — `CFC.log` (operator monotone),
`CFC.log_le_log`, the rpow order lemmas, the rpow→log limit — is stated for `[CStarAlgebra A]`
and does **not** fire directly on the bare `Matrix` type used by
`Matrix.OperatorConvexOn` / `Matrix.OperatorConcaveOn` and the L.1/L.2 rungs.

This file builds the transport across the star-algebra equivalence
`e := CStarMatrix.ofMatrixStarAlgEquiv : Matrix n n ℂ ≃⋆ₐ[ℂ] CStarMatrix n n ℂ`
(which is the identity `Equiv.refl` on carriers, hence continuous), and uses it to pull the
C⋆-generic facts back onto `Matrix`.

## Main results

* `Matrix.cstar_cfc` (**B.1, the crux**): CFC naturality across the synonym equiv,
  `e (cfc f A) = cfc f (e A)`. Note the two `cfc`s come from **different** functional-calculus
  instances — `Matrix.IsHermitian.instContinuousFunctionalCalculus` on the left and the
  C⋆-algebra CFC on the right — and they agree by CFC uniqueness, packaged by
  `StarAlgHomClass.map_cfc`.
* `Matrix.cstar_le_iff` (**B.2**): the Löwner order on `Matrix` and the spectral order on
  `CStarMatrix` agree across `e`, `e A ≤ e B ↔ A ≤ B`. Proved via
  `StarRingEquivClass.instOrderIsoClass.map_le_map_iff` (a star-ring equivalence is an order
  isomorphism between `StarOrderedRing`s).
* `Matrix.cstar_isStrictlyPositive`: `A.PosDef → IsStrictlyPositive (e A)`, the positivity
  hypothesis transport feeding the order lemmas.
* `Matrix.matrix_log_le_log` (**B.3, log**): operator **monotonicity** of `log` on
  positive-definite matrices in the Löwner order, `A ≤ B → cfc Real.log A ≤ cfc Real.log B`,
  transported from `CFC.log_le_log`. This is the genuine ladder enabler: the route-2 path to
  operator concavity of `log` (`specs/operator-convexity-plan.md` L.2) consumes
  `CFC.log_monotoneOn` and `tendsto_cfc_rpow_sub_one_log` on the C⋆ side, and this bridge is
  what makes the conclusion expressible on the `Matrix` carrier of the `OperatorConcaveOn`
  predicate.

## ~~Honest scope (rpow wall)~~ SUPERSEDED 2026-08-22 (MG-3): the rpow rung is LANDED

The rpow wall recorded here previously is dissolved. The MG-3 probe
(`specs/mathlib-gaps-plan.md`; `scratch_mg3_probe.lean`, five rounds) established that the
obstruction was **exactly two** generic instances failing to fire through the discrimination
tree — the `ℝ`-CFC over `IsSelfAdjoint` (the shim below, already present) and
`NonnegSpectrumClass ℝ` (`instCStarMatrixNonnegSpectrumClass`, the second shim, added with
B.4) — and that with both registered the entire upstream monotonicity tier fires on
`CStarMatrix n n ℂ`, including `CFC.monotone_nnrpow` (operator monotonicity of `x ^ p`,
`p ∈ [0,1]`, which landed upstream in `…/Rpow/Order.lean` after the wall note was written).
**B.4** transports it to the `Matrix` carrier: `matrix_nnrpow_le_nnrpow` (the L.3 rung) and
`matrix_sqrt_le_sqrt`, via the `ℝ≥0`-`cfcₙ` naturality `cstar_cfcₙ_nnreal` (the `ℝ≥0`
companion of B.1). The remaining C⋆-side absence for the DPI ladder is operator CONVEXITY
(Lieb) — upstream's own TODO; see `specs/operator-convexity-plan.md` and `MATHLIB-GAPS.md`.

**Category:** 1-Mathlib (CSD-free). Natural Mathlib namespace `Matrix`.
-/

@[expose] public section

open scoped MatrixOrder ComplexOrder NNReal

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The `ℝ`-CFC instance shim on `CStarMatrix n n ℂ`

The generic `IsSelfAdjoint.instContinuousFunctionalCalculus` does not fire on `CStarMatrix n n ℂ`
through the discrimination tree (its predicate-output `IsSelfAdjoint` is not matched), so we
register it explicitly as a local instance. It elaborates because `CStarMatrix n n ℂ` is a unital
`CStarAlgebra` (`CStarMatrix.instCStarAlgebra`) with the `ℂ`-CFC over `IsStarNormal`. -/

/-- The real continuous functional calculus on `CStarMatrix n n ℂ` over self-adjoint elements,
registered explicitly (the generic instance does not fire on `CStarMatrix` via the
discrimination tree). -/
noncomputable instance instCStarMatrixRealCFC :
    ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local notation "e" => (CStarMatrix.ofMatrixStarAlgEquiv : Matrix n n ℂ → CStarMatrix n n ℂ)

/-! ### Continuity of the synonym equivalence -/

omit [DecidableEq n] in
/-- The star-algebra equivalence `Matrix n n ℂ ≃⋆ₐ[ℂ] CStarMatrix n n ℂ` is continuous: on
carriers it is the identity (`Equiv.refl`), and `CStarMatrix.ofMatrixL` is a continuous linear
equivalence with `continuous_id`. -/
theorem ofMatrixStarAlgEquiv_continuous :
    Continuous (CStarMatrix.ofMatrixStarAlgEquiv : Matrix n n ℂ → CStarMatrix n n ℂ) := by
  rw [← CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv, CStarMatrix.ofMatrix_eq_ofMatrixL]
  exact (CStarMatrix.ofMatrixL).continuous_toFun

/-! ### B.2 — order transport (Löwner ↔ spectral order across `e`) -/

omit [DecidableEq n] in
/-- **B.2.** The Löwner order on `Matrix n n ℂ` (`(B - A).PosSemidef`) and the spectral order on
`CStarMatrix n n ℂ` agree across the star-algebra equivalence `e`:
`e A ≤ e B ↔ A ≤ B`. Both `Matrix` and `CStarMatrix` are `StarOrderedRing`s, and a star-ring
equivalence is an `OrderIso` between `StarOrderedRing`s (`StarRingEquivClass.instOrderIsoClass`),
so this is `map_le_map_iff`. -/
theorem cstar_le_iff (A B : Matrix n n ℂ) :
    CStarMatrix.ofMatrixStarAlgEquiv A ≤ CStarMatrix.ofMatrixStarAlgEquiv B ↔ A ≤ B :=
  map_le_map_iff CStarMatrix.ofMatrixStarAlgEquiv

/-! ### B.1 — CFC transport (the crux) -/

/-- **B.1 (the crux).** The continuous functional calculus commutes with the synonym equivalence
`e`: for Hermitian `A` and `f` continuous on `spectrum ℝ A`,
`e (cfc f A) = cfc f (e A)`.

The left `cfc` is taken in `Matrix`'s own functional-calculus instance
(`Matrix.IsHermitian.instContinuousFunctionalCalculus`, the spectral triple product); the right
`cfc` is taken in the C⋆-algebra instance on `CStarMatrix`. These are **a priori different**
functional-calculus instances; they agree because `e` is a continuous star-algebra homomorphism
and the CFC is unique (`StarAlgHomClass.map_cfc`, whose proof routes through
`ContinuousMap.UniqueHom`). So no separate uniqueness argument is needed at this level. -/
theorem cstar_cfc {A : Matrix n n ℂ} (f : ℝ → ℝ) (hA : A.IsHermitian)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    CStarMatrix.ofMatrixStarAlgEquiv (cfc f A) = cfc f (CStarMatrix.ofMatrixStarAlgEquiv A) := by
  have hsa : IsSelfAdjoint A := hA
  exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv f A hf
    ofMatrixStarAlgEquiv_continuous hsa (hsa.map _)

/-! ### Positivity transport -/

/-- A positive-definite matrix maps to a strictly-positive element of `CStarMatrix n n ℂ`.
`IsStrictlyPositive a := 0 ≤ a ∧ IsUnit a`: nonnegativity transports via `cstar_le_iff` (B.2) and
`map_zero e`, and invertibility transports because `e` is a ring equivalence. -/
theorem cstar_isStrictlyPositive {A : Matrix n n ℂ} (hA : A.PosDef) :
    IsStrictlyPositive (CStarMatrix.ofMatrixStarAlgEquiv A) := by
  have hsp : IsStrictlyPositive A := hA.isStrictlyPositive
  refine ⟨?_, ?_⟩
  · have h0 : (0 : Matrix n n ℂ) ≤ A := hsp.1
    have := (cstar_le_iff 0 A).mpr h0
    rwa [map_zero] at this
  · exact hsp.2.map CStarMatrix.ofMatrixStarAlgEquiv

/-! ### B.3 — operator monotonicity of `log` transported onto `Matrix` -/

/-- `Real.log` is continuous on the (positive) spectrum of a positive-definite matrix. -/
theorem logContinuousOn {A : Matrix n n ℂ} (hA : A.PosDef) :
    ContinuousOn Real.log (spectrum ℝ A) :=
  Real.continuousOn_log.mono (fun x hx => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (posDef_spectrum_pos hA x hx).ne')

/-- **B.3 (log).** Operator **monotonicity** of `log` on positive-definite matrices, in the
Löwner order: `A ≤ B → cfc Real.log A ≤ cfc Real.log B` (for positive-definite `A, B`).

Transported from `CFC.log_le_log` on `CStarMatrix n n ℂ`: the order transports (B.2), strict
positivity transports (`cstar_isStrictlyPositive`), and `CFC.log (e A) = e (cfc Real.log A)` by
B.1 (`CFC.log a := cfc Real.log a` definitionally). The statement is in terms of `cfc Real.log`
on the `Matrix` side because `CFC.log` itself requires `NormedRing (Matrix n n ℂ)`, which the
default `Matrix` instances do not provide — this is exactly the carrier mismatch the bridge
resolves. -/
theorem matrix_log_le_log {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A ≤ B) :
    cfc Real.log A ≤ cfc Real.log B := by
  have hspA : IsStrictlyPositive (e A) := cstar_isStrictlyPositive hA
  have hle : e A ≤ e B := (cstar_le_iff A B).mpr hAB
  have key : CFC.log (e A) ≤ CFC.log (e B) := CFC.log_le_log hle hspA
  have hlogA : e (cfc Real.log A) = CFC.log (e A) :=
    (cstar_cfc Real.log hA.1 (logContinuousOn hA)).trans rfl
  have hlogB : e (cfc Real.log B) = CFC.log (e B) :=
    (cstar_cfc Real.log hB.1 (logContinuousOn hB)).trans rfl
  rw [← hlogA, ← hlogB] at key
  exact (cstar_le_iff (cfc Real.log A) (cfc Real.log B)).mp key

/-! ### The second shim + B.4 — rpow operator monotonicity on `Matrix` (2026-08-22, MG-3) -/

/-- The second non-firing generic instance found by the MG-3 probe: `NonnegSpectrumClass ℝ`
on `CStarMatrix n n ℂ`, registered explicitly from its own generic provider
(`CStarAlgebra.instNonnegSpectrumClass` — provable as a term, not found by synthesis through
the repeated-index discrimination key). With this and the `ℝ`-CFC shim above, the upstream
rpow/sqrt/log order tier fires on `CStarMatrix`. -/
instance instCStarMatrixNonnegSpectrumClass :
    NonnegSpectrumClass ℝ (CStarMatrix n n ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- **B.4a.** `ℝ≥0`-`cfcₙ` naturality across the synonym equivalence, on nonnegative
matrices: `e (cfcₙ f A) = cfcₙ f (e A)`. The `ℝ≥0` companion of B.1, by
`NonUnitalStarAlgHomClass.map_cfcₙ` (the two `cfcₙ`s come from the `Matrix`-side and
`CStarMatrix`-side `ℝ≥0` functional calculi respectively). -/
theorem cstar_cfcₙ_nnreal {A : Matrix n n ℂ} (hA : 0 ≤ A) (f : ℝ≥0 → ℝ≥0)
    (hf : ContinuousOn f (quasispectrum ℝ≥0 A)) (hf0 : f 0 = 0) :
    CStarMatrix.ofMatrixStarAlgEquiv (cfcₙ f A)
      = cfcₙ f (CStarMatrix.ofMatrixStarAlgEquiv A) := by
  have hA' : (0 : CStarMatrix n n ℂ) ≤ CStarMatrix.ofMatrixStarAlgEquiv A := by
    have := (cstar_le_iff 0 A).mpr hA
    rwa [map_zero] at this
  exact NonUnitalStarAlgHomClass.map_cfcₙ CStarMatrix.ofMatrixStarAlgEquiv f A hf hf0
    ofMatrixStarAlgEquiv_continuous hA hA'

/-- **B.4 (rpow, the L.3 rung).** Operator **monotonicity** of the nonnegative power
`A ↦ A ^ p` (`p : ℝ≥0`, `p ≤ 1`) on positive-semidefinite matrices in the Löwner order —
`CFC.monotone_nnrpow` transported onto the `Matrix` carrier. The `p = 0` exponent is junk-valued
(`A ^ 0 = 0` by the `cfcₙ` zero convention) and handled separately; for `p ≠ 0` the pointwise
function is zero-preserving and the naturality B.4a identifies the powers across `e`. -/
theorem matrix_nnrpow_le_nnrpow {A B : Matrix n n ℂ} {p : ℝ≥0} (hp : p ∈ Set.Icc 0 1)
    (hA : 0 ≤ A) (hAB : A ≤ B) :
    A ^ p ≤ B ^ p := by
  obtain rfl | hp0 := eq_or_ne p 0
  · rw [CFC.nnrpow_zero, CFC.nnrpow_zero]
  · have hB : (0 : Matrix n n ℂ) ≤ B := hA.trans hAB
    have hf0 : NNReal.nnrpow 0 p = 0 := by
      rw [NNReal.nnrpow_def, NNReal.zero_rpow (by exact_mod_cast hp0)]
    have hEA : (CStarMatrix.ofMatrixStarAlgEquiv A) ^ p
        = CStarMatrix.ofMatrixStarAlgEquiv (A ^ p) := by
      rw [CFC.nnrpow_def, CFC.nnrpow_def]
      exact (cstar_cfcₙ_nnreal hA _
        ((NNReal.continuous_nnrpow_const p).continuousOn) hf0).symm
    have hEB : (CStarMatrix.ofMatrixStarAlgEquiv B) ^ p
        = CStarMatrix.ofMatrixStarAlgEquiv (B ^ p) := by
      rw [CFC.nnrpow_def, CFC.nnrpow_def]
      exact (cstar_cfcₙ_nnreal hB _
        ((NNReal.continuous_nnrpow_const p).continuousOn) hf0).symm
    have key : (CStarMatrix.ofMatrixStarAlgEquiv A) ^ p
        ≤ (CStarMatrix.ofMatrixStarAlgEquiv B) ^ p :=
      CFC.monotone_nnrpow hp ((cstar_le_iff A B).mpr hAB)
    rw [hEA, hEB] at key
    exact (cstar_le_iff (A ^ p) (B ^ p)).mp key

/-- **B.4 corollary (sqrt).** Operator monotonicity of the matrix square root on the Löwner
order: `0 ≤ A ≤ B → √A ≤ √B`. -/
theorem matrix_sqrt_le_sqrt {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    CFC.sqrt A ≤ CFC.sqrt B := by
  rw [CFC.sqrt_eq_nnrpow A, CFC.sqrt_eq_nnrpow B]
  exact matrix_nnrpow_le_nnrpow ⟨by norm_num, by norm_num⟩ hA hAB

/-! ### B.5 / B.6 — operator CONCAVITY transported (the L.2 / L.3a-interior rungs)

Upstream proves operator concavity C⋆-generically (`CFC.concaveOn_log`, `CFC.concaveOn_rpow`);
the same transport that carries monotonicity carries concavity, so both rungs are corollaries
rather than builds. The convex combination is taken with **real** scalars coerced to `ℂ`, which
is what `smul_transport` normalises. -/

omit [DecidableEq n] in
/-- Real-scalar smul commutes with the `Matrix ≃ CStarMatrix` transport. The convex combinations
below are formed in `ℂ`, so this is the lemma that lets `map_add`/`map_smul` normalise them. -/
theorem smul_transport (t : ℝ) (A : Matrix n n ℂ) :
    CStarMatrix.ofMatrixStarAlgEquiv ((t : ℂ) • A)
      = t • CStarMatrix.ofMatrixStarAlgEquiv A := by
  rw [map_smul]; exact Complex.coe_smul t _

/-- **B.5.** Operator concavity of `log` on positive-definite matrices, in Löwner order:
`t·log A + (1−t)·log B ≤ log (t·A + (1−t)·B)`. Transported from `CFC.concaveOn_log`. -/
theorem matrix_log_concave {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) • cfc Real.log A + ((1 : ℂ) - t) • cfc Real.log B
      ≤ cfc Real.log ((t : ℂ) • A + ((1 : ℂ) - t) • B) := by
  have hc : ((1 : ℂ) - (t : ℂ)) = (((1 - t : ℝ)) : ℂ) := by push_cast; ring
  rw [hc]
  have hcomb : (((t : ℝ) : ℂ) • A + (((1 - t : ℝ)) : ℂ) • B).PosDef := by
    rw [← hc]; exact convexComb_posDef hA hB ht0 ht1
  have key := (CFC.concaveOn_log (A := CStarMatrix n n ℂ)).2 (cstar_isStrictlyPositive hA)
    (cstar_isStrictlyPositive hB) ht0 (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
  have hlA : CStarMatrix.ofMatrixStarAlgEquiv (cfc Real.log A)
      = CFC.log (CStarMatrix.ofMatrixStarAlgEquiv A) :=
    (cstar_cfc Real.log hA.1 (logContinuousOn hA)).trans rfl
  have hlB : CStarMatrix.ofMatrixStarAlgEquiv (cfc Real.log B)
      = CFC.log (CStarMatrix.ofMatrixStarAlgEquiv B) :=
    (cstar_cfc Real.log hB.1 (logContinuousOn hB)).trans rfl
  have hlC : CStarMatrix.ofMatrixStarAlgEquiv
        (cfc Real.log ((((t : ℝ)) : ℂ) • A + (((1 - t : ℝ)) : ℂ) • B))
      = CFC.log (CStarMatrix.ofMatrixStarAlgEquiv
        ((((t : ℝ)) : ℂ) • A + (((1 - t : ℝ)) : ℂ) • B)) :=
    (cstar_cfc Real.log hcomb.1 (logContinuousOn hcomb)).trans rfl
  rw [← cstar_le_iff]
  simp only [map_add, smul_transport, hlA, hlB, hlC]
  exact key

/-- ★★ **L.2 — `log` is operator concave on `(0, ∞)`**, in the corpus's all-dimensions
`OperatorConcaveOn` predicate. The plan budgeted this as a multi-day build against a wall
("`Matrix n n ℂ` is not a `CStarAlgebra`"); the wall was a *scope* question and upstream has
since proved the C⋆-generic statement, so it is a transport. -/
theorem operatorConcaveOn_log : OperatorConcaveOn (Set.Ioi 0) Real.log := by
  intro m _ _ A B hA hB hsA hsB t ht0 ht1 _
  exact matrix_log_concave (posDef_of_spectrum_pos hA fun x hx => hsA hx)
    (posDef_of_spectrum_pos hB fun x hx => hsB hx) ht0 ht1

/-- ★ **L.3a interior — `x ^ p` is operator concave for `p ∈ [0,1]`**, on the bare `Matrix`
carrier in `^`-notation and Löwner order. Transported from `CFC.concaveOn_rpow`; supersedes the
endpoints-only `operatorConcaveOn_rpow_zero` / `_one`. -/
theorem matrix_rpow_concave {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) {A B : Matrix n n ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) • A ^ p + ((1 : ℂ) - t) • B ^ p
      ≤ ((t : ℂ) • A + ((1 : ℂ) - t) • B) ^ p := by
  have hc : ((1 : ℂ) - (t : ℂ)) = (((1 - t : ℝ)) : ℂ) := by push_cast; ring
  rw [hc]
  have hA' : (0 : CStarMatrix n n ℂ) ≤ CStarMatrix.ofMatrixStarAlgEquiv A := by
    have := (cstar_le_iff 0 A).mpr hA; rwa [map_zero] at this
  have hB' : (0 : CStarMatrix n n ℂ) ≤ CStarMatrix.ofMatrixStarAlgEquiv B := by
    have := (cstar_le_iff 0 B).mpr hB; rwa [map_zero] at this
  have key := (CFC.concaveOn_rpow (A := CStarMatrix n n ℂ) hp).2 hA' hB' ht0
    (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
  have hrA : CStarMatrix.ofMatrixStarAlgEquiv (A ^ p)
      = (CStarMatrix.ofMatrixStarAlgEquiv A) ^ p := by
    rw [CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real hA']
    exact cstar_cfc _ (Matrix.nonneg_iff_posSemidef.mp hA).1
      (continuousOn_id.rpow_const fun x _ => Or.inr hp.1)
  have hrB : CStarMatrix.ofMatrixStarAlgEquiv (B ^ p)
      = (CStarMatrix.ofMatrixStarAlgEquiv B) ^ p := by
    rw [CFC.rpow_eq_cfc_real hB, CFC.rpow_eq_cfc_real hB']
    exact cstar_cfc _ (Matrix.nonneg_iff_posSemidef.mp hB).1
      (continuousOn_id.rpow_const fun x _ => Or.inr hp.1)
  have hcomb : (0 : Matrix n n ℂ) ≤ ((t : ℝ) : ℂ) • A + ((1 - t : ℝ) : ℂ) • B := by
    have hc0 : (0 : ℂ) ≤ ((t : ℝ) : ℂ) := by exact_mod_cast ht0
    have hc1 : (0 : ℂ) ≤ (((1 - t : ℝ)) : ℂ) := by
      exact_mod_cast (by linarith : (0:ℝ) ≤ 1 - t)
    exact Matrix.nonneg_iff_posSemidef.mpr
      (((Matrix.nonneg_iff_posSemidef.mp hA).smul hc0).add
        ((Matrix.nonneg_iff_posSemidef.mp hB).smul hc1))
  have hcomb' : (0 : CStarMatrix n n ℂ) ≤ CStarMatrix.ofMatrixStarAlgEquiv
      (((t : ℝ) : ℂ) • A + (((1 - t : ℝ)) : ℂ) • B) := by
    have := (cstar_le_iff 0 _).mpr hcomb; rwa [map_zero] at this
  have hrC : CStarMatrix.ofMatrixStarAlgEquiv
        (((((t : ℝ)) : ℂ) • A + (((1 - t : ℝ)) : ℂ) • B) ^ p)
      = (CStarMatrix.ofMatrixStarAlgEquiv
        ((((t : ℝ)) : ℂ) • A + (((1 - t : ℝ)) : ℂ) • B)) ^ p := by
    rw [CFC.rpow_eq_cfc_real hcomb, CFC.rpow_eq_cfc_real hcomb']
    exact cstar_cfc _ (Matrix.nonneg_iff_posSemidef.mp hcomb).1
      (continuousOn_id.rpow_const fun x _ => Or.inr hp.1)
  rw [← cstar_le_iff]
  simp only [map_add, smul_transport, hrA, hrB, hrC]
  exact key

/-! ### Non-vacuity witness

The bridge is non-vacuous: it applies to a concrete non-commuting positive-definite pair.
`A = diagonal !![2, 1]`-style witnesses are positive definite; the transport lemmas relate the
genuine carriers (the `Matrix` Löwner order and the `CStarMatrix` spectral order), not a
degenerate or mismatched structure. -/
example {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) :
    cfc Real.log A ≤ cfc Real.log B := matrix_log_le_log hA hB hAB

example {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    A ^ (2⁻¹ : ℝ≥0) ≤ B ^ (2⁻¹ : ℝ≥0) :=
  matrix_nnrpow_le_nnrpow ⟨by norm_num, by norm_num⟩ hA hAB

end Matrix

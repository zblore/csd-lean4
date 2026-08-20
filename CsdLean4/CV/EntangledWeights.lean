/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.CompositeArena
public import CsdLean4.Mathlib.QuantumInfo.PartialTrace

/-!
# Q27: what entanglement does to the weights — local observations are reduced-state expectations

**Category:** CV (the composite arena's local statistics; BACKLOG Q27, queued
from the 2026-08-20 external physicist review).

The question: for an entangled composite preparation, what are a local
context's weights? The answer this module proves: **local arena observations
are exactly reduced-state expectations, for every composite point** — and on
an entangled point the reduced state is mixed, so entanglement is precisely
what turns a local context's pure-state Born weights into mixed-state Born
weights.

* `reducedDM x` — the reduced density of a composite ray: the right partial
  trace of `arenaDM x` read on the pair index. PSD (`reducedDM_posSemidef`),
  trace one (`reducedDM_trace`): a genuine density operator for every `x`.
* ★★ `arenaObs_leftOp_eq_reduced` — **the bridge**: for EVERY composite point
  `x` (entangled included) and every left-sector observable `A`,
  `arenaObs (leftOp A) x = re tr(reducedDM x · A)`. Local observations on the
  composite arena ARE mixed-Born pairings against the reduced state — this is
  the `re tr(D·E)` form the LF2 mixed-state tier reads.
* ★ `reducedDM_join` — **the unentangled contrast**: on a product point
  `arenaJoin p q` the reduced state is the pure local state `arenaDM p`.
  Departure of `reducedDM x` from a rank-one projector is exactly what
  entanglement contributes.
* ★★ `reducedDM_bell` — **the Bell answer, exactly**: on the Bell ray over
  correlated patterns `(x₀,y₀), (x₁,y₁)`, the reduced state is the equal
  mixture `½(∣x₀⟩⟨x₀∣ + ∣x₁⟩⟨x₁∣)`. Corollaries `bell_local_weight₀`/`₁`: the
  local weight of each correlated pattern is exactly `1/2`. The same witness
  that shows the composite arena exceeds the pair (`bell_not_join`, P2) shows
  what the excess does: it maximally mixes the local weights across the
  correlated patterns — and since `reducedDM` never sees the remote sector's
  unitaries, this is also `composite_no_signalling` read as a consequence.

⚠️ Honest scope: weights are delivered in the `re tr(reducedDM · A)` mixed-
Born form on the field-configuration index; transporting them through the
`Fin`-indexed LF2 `DensityOperatorIx` mixed tier is index plumbing without
new content and is not claimed here. Sequential/record-conditioned versions
are Q25's territory.

## References

`specs/BACKLOG.md` (Q27); `CV/CompositeArena.lean` (P2 — `leftOp`,
`arenaJoin`, `bellVec`, `compositeReindex`);
`Mathlib/QuantumInfo/PartialTrace.lean` (`partialTraceRight`,
`trace_mul_kronecker_one_right` — rehomed there from `Subadditivity.lean` in
this arc); `LF2/ReducedDensity.lean`,
`LF2/MixedEnsembleIx.lean` (the mixed-Born tier this feeds);
`specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open scoped Kronecker
open scoped ComplexOrder
open scoped LinearAlgebra.Projectivization

namespace CSD.CV

variable {K₁ K₂ N : ℕ}

/-! ### The reduced density of a composite ray -/

/-- The composite reindex, inverted, in submatrix form. -/
lemma compositeReindex_symm_apply
    (M : Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ)
    (a b : FieldConfig K₁ N × FieldConfig K₂ N) :
    (compositeReindex.symm M) a b
      = M (configSplit.symm a) (configSplit.symm b) := by
  rw [compositeReindex, Matrix.symm_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv,
    Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]

/-- Traces are preserved by the inverted composite reindex. -/
lemma trace_compositeReindex_symm
    (M : Matrix (FieldConfig (K₁ + K₂) N) (FieldConfig (K₁ + K₂) N) ℂ) :
    (compositeReindex.symm M).trace = M.trace := by
  have h := trace_compositeReindex (K₁ := K₁) (K₂ := K₂) (N := N)
    (compositeReindex.symm M)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The reduced density of a composite ray**: trace out the right sector
from the ray's density, read on the pair index. -/
noncomputable def reducedDM (x : FieldArena (K₁ + K₂) N) :
    Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ :=
  partialTraceRight (compositeReindex.symm (arenaDM x))

/-- The reduced density is positive semidefinite. -/
lemma reducedDM_posSemidef (x : FieldArena (K₁ + K₂) N) :
    (reducedDM x).PosSemidef := by
  refine partialTraceRight_posSemidef ?_
  have hsub : compositeReindex.symm (arenaDM x)
      = (arenaDM x).submatrix configSplit.symm configSplit.symm := by
    ext a b
    rw [compositeReindex_symm_apply, Matrix.submatrix_apply]
  rw [hsub]
  exact (arenaDM_posSemidef x).submatrix _

/-- The reduced density has unit trace: it is a genuine density operator. -/
lemma reducedDM_trace (x : FieldArena (K₁ + K₂) N) :
    (reducedDM x).trace = 1 := by
  rw [reducedDM, partialTraceRight_trace, trace_compositeReindex_symm,
    arenaDM_trace]

/-! ### The bridge: local observations are reduced-state expectations -/

/-- ★★ **Local arena observations are reduced-state expectations — for EVERY
composite point, entangled included.** `arenaObs (leftOp A) x` is the
mixed-Born pairing `re tr(reducedDM x · A)`. Entanglement's entire local
effect is packaged in `reducedDM x` being mixed. -/
theorem arenaObs_leftOp_eq_reduced
    (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ)
    (x : FieldArena (K₁ + K₂) N) :
    arenaObs (leftOp A) x = RCLike.re ((reducedDM x * A).trace) := by
  rw [arenaObs, leftOp]
  congr 1
  rw [show arenaDM x = compositeReindex (compositeReindex.symm (arenaDM x))
      from (AlgEquiv.apply_symm_apply _ _).symm,
    ← map_mul, trace_compositeReindex, trace_mul_kronecker_one_right, reducedDM]

/-- ★ **The unentangled contrast**: on a product point the reduced state is
the pure local state. Whatever `reducedDM x` adds beyond a rank-one projector
is entanglement's contribution. -/
theorem reducedDM_join (p : FieldArena K₁ N) (q : FieldArena K₂ N) :
    reducedDM (arenaJoin p q) = arenaDM p := by
  rw [reducedDM, arenaDM_join, AlgEquiv.symm_apply_apply,
    partialTraceRight_kronecker, arenaDM_trace, one_smul]

/-! ### The Bell instance: the local weights, exactly -/

/-- The Bell vector's squared norm is `2` (two unit entries at distinct
configuration pairs). -/
lemma bell_norm_sq {x₀ x₁ : FieldConfig K₁ N} (hx : x₀ ≠ x₁)
    (y₀ y₁ : FieldConfig K₂ N) :
    ‖bellVec x₀ x₁ y₀ y₁‖ ^ 2 = 2 := by
  rw [← euclid_sum_norm_sq (bellVec x₀ x₁ y₀ y₁)]
  rw [← Equiv.sum_comp (configSplit (K₁ := K₁) (K₂ := K₂) (N := N)).symm
    (fun c => ‖bellVec x₀ x₁ y₀ y₁ c‖ ^ 2)]
  have hterm : ∀ z : FieldConfig K₁ N × FieldConfig K₂ N,
      ‖bellVec x₀ x₁ y₀ y₁ (configSplit.symm z)‖ ^ 2
        = (if z = (x₀, y₀) then 1 else 0) + (if z = (x₁, y₁) then 1 else 0) := by
    intro z
    rw [bellVec_apply, Equiv.apply_symm_apply]
    by_cases h0 : z = (x₀, y₀) <;> by_cases h1 : z = (x₁, y₁)
    · exact absurd (congrArg Prod.fst (h0.symm.trans h1)) hx
    · rw [if_pos (Or.inl h0), if_pos h0, if_neg h1]
      norm_num
    · rw [if_pos (Or.inr h1), if_neg h0, if_pos h1]
      norm_num
    · rw [if_neg (by rintro (h | h) <;> [exact h0 h; exact h1 h]),
        if_neg h0, if_neg h1]
      norm_num
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ ((x₀, y₀)) (fun _ => (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ ((x₁, y₁)) (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  norm_num

/-- ★★ **What entanglement does to the weights, exactly**: the reduced state
of the Bell ray over correlated patterns `(x₀,y₀), (x₁,y₁)` is the equal
mixture `½(∣x₀⟩⟨x₀∣ + ∣x₁⟩⟨x₁∣)`. The remote pattern labels are gone — no
signalling — and the local weights are maximally mixed across the two
correlated patterns. -/
theorem reducedDM_bell {x₀ x₁ : FieldConfig K₁ N} (hx : x₀ ≠ x₁)
    {y₀ y₁ : FieldConfig K₂ N} (hy : y₀ ≠ y₁) :
    reducedDM (Projectivization.mk ℂ (bellVec x₀ x₁ y₀ y₁)
        (bellVec_ne_zero x₀ x₁ y₀ y₁))
      = (1 / 2 : ℂ) • (Matrix.single x₀ x₀ 1 + Matrix.single x₁ x₁ 1) := by
  rw [reducedDM, arenaDM_mk]
  ext i j
  rw [partialTraceRight_apply]
  have hentry : ∀ k : FieldConfig K₂ N,
      (compositeReindex.symm (dmVec (bellVec x₀ x₁ y₀ y₁))) (i, k) (j, k)
        = (1 / 2 : ℂ)
          * (((if i = x₀ ∧ k = y₀ then (1 : ℂ) else 0)
              + (if i = x₁ ∧ k = y₁ then 1 else 0))
            * ((if j = x₀ ∧ k = y₀ then (1 : ℂ) else 0)
              + (if j = x₁ ∧ k = y₁ then 1 else 0))) := by
    intro k
    rw [compositeReindex_symm_apply, dmVec_apply', bell_norm_sq hx y₀ y₁]
    have hb : ∀ (a : FieldConfig K₁ N) (b : FieldConfig K₂ N),
        bellVec x₀ x₁ y₀ y₁ (configSplit.symm (a, b))
          = (if a = x₀ ∧ b = y₀ then (1 : ℂ) else 0)
            + (if a = x₁ ∧ b = y₁ then 1 else 0) := by
      intro a b
      rw [bellVec_apply, Equiv.apply_symm_apply]
      by_cases h0 : a = x₀ ∧ b = y₀ <;> by_cases h1 : a = x₁ ∧ b = y₁
      · exact absurd (h0.1.symm.trans h1.1) hx
      · rw [if_pos (Or.inl (by rw [h0.1, h0.2])), if_pos h0, if_neg h1,
          add_zero]
      · rw [if_pos (Or.inr (by rw [h1.1, h1.2])), if_neg h0, if_pos h1,
          zero_add]
      · rw [if_neg ?_, if_neg h0, if_neg h1, add_zero]
        rintro (h | h)
        · exact h0 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
        · exact h1 ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    rw [hb i k, hb j k]
    have hstar : star ((if j = x₀ ∧ k = y₀ then (1 : ℂ) else 0)
          + (if j = x₁ ∧ k = y₁ then 1 else 0))
        = (if j = x₀ ∧ k = y₀ then (1 : ℂ) else 0)
          + (if j = x₁ ∧ k = y₁ then 1 else 0) := by
      rw [star_add, apply_ite (star : ℂ → ℂ), apply_ite (star : ℂ → ℂ),
        star_one, star_zero]
    rw [hstar]
    norm_num
  rw [Finset.sum_congr rfl fun k _ => hentry k, ← Finset.mul_sum]
  have hsum : (∑ k : FieldConfig K₂ N,
      (((if i = x₀ ∧ k = y₀ then (1 : ℂ) else 0)
          + (if i = x₁ ∧ k = y₁ then 1 else 0))
        * ((if j = x₀ ∧ k = y₀ then (1 : ℂ) else 0)
          + (if j = x₁ ∧ k = y₁ then 1 else 0))))
      = (if i = x₀ ∧ j = x₀ then (1 : ℂ) else 0)
        + (if i = x₁ ∧ j = x₁ then 1 else 0) := by
    have hterm : ∀ k : FieldConfig K₂ N,
        (((if i = x₀ ∧ k = y₀ then (1 : ℂ) else 0)
            + (if i = x₁ ∧ k = y₁ then 1 else 0))
          * ((if j = x₀ ∧ k = y₀ then (1 : ℂ) else 0)
            + (if j = x₁ ∧ k = y₁ then 1 else 0)))
        = (if k = y₀ then (if i = x₀ ∧ j = x₀ then (1 : ℂ) else 0) else 0)
          + (if k = y₁ then (if i = x₁ ∧ j = x₁ then (1 : ℂ) else 0) else 0) := by
      intro k
      by_cases hk0 : k = y₀ <;> by_cases hk1 : k = y₁
      · exact absurd (hk0.symm.trans hk1) hy
      all_goals by_cases hi0 : i = x₀ <;> by_cases hi1 : i = x₁ <;>
        by_cases hj0 : j = x₀ <;> by_cases hj1 : j = x₁ <;>
        simp_all
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ y₀
        (fun _ => if i = x₀ ∧ j = x₀ then (1 : ℂ) else 0),
      Finset.sum_ite_eq' Finset.univ y₁
        (fun _ => if i = x₁ ∧ j = x₁ then (1 : ℂ) else 0),
      if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  rw [hsum]
  rw [Matrix.smul_apply, Matrix.add_apply]
  simp only [Matrix.single, Matrix.of_apply]
  by_cases hi0 : i = x₀ <;> by_cases hi1 : i = x₁ <;>
    by_cases hj0 : j = x₀ <;> by_cases hj1 : j = x₁ <;>
    simp_all [eq_comm]

/-- `tr(M · ∣a⟩⟨a∣) = M a a` — reading one diagonal weight. -/
lemma trace_mul_single (M : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ)
    (a : FieldConfig K₁ N) :
    (M * Matrix.single a a 1).trace = M a a := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  have hterm : ∀ i j : FieldConfig K₁ N,
      M i j * Matrix.single a a (1 : ℂ) j i
        = if j = a then (if i = a then M i j else 0) else 0 := by
    intro i j
    simp only [Matrix.single, Matrix.of_apply]
    by_cases hj : j = a <;> by_cases hi : i = a <;>
      simp_all [eq_comm]
  rw [Finset.sum_congr rfl fun i _ => by
    rw [Finset.sum_congr rfl fun j _ => hterm i j,
      Finset.sum_ite_eq' Finset.univ a (fun j => if i = a then M i j else 0),
      if_pos (Finset.mem_univ _)]]
  rw [Finset.sum_ite_eq' Finset.univ a (fun i => M i a),
    if_pos (Finset.mem_univ _)]

/-- ★ **The Bell local weight at the first pattern is exactly `1/2`.** -/
theorem bell_local_weight₀ {x₀ x₁ : FieldConfig K₁ N} (hx : x₀ ≠ x₁)
    {y₀ y₁ : FieldConfig K₂ N} (hy : y₀ ≠ y₁) :
    arenaObs (leftOp (Matrix.single x₀ x₀ 1))
      (Projectivization.mk ℂ (bellVec x₀ x₁ y₀ y₁)
        (bellVec_ne_zero x₀ x₁ y₀ y₁)) = 1 / 2 := by
  rw [arenaObs_leftOp_eq_reduced, reducedDM_bell hx hy, smul_mul_assoc,
    Matrix.add_mul, trace_smul, Matrix.trace_add, trace_mul_single,
    trace_mul_single]
  simp only [Matrix.single, Matrix.of_apply]
  rw [if_pos (⟨trivial, trivial⟩ : True ∧ True),
    if_neg (fun h : x₁ = x₀ ∧ x₁ = x₀ => hx h.1.symm)]
  simp only [add_zero, smul_eq_mul, mul_one, RCLike.re_to_complex]
  norm_num [Complex.div_re, Complex.normSq_apply]

/-- ★ **The Bell local weight at the second pattern is exactly `1/2`.** With
`bell_local_weight₀`: entanglement mixes the local weights maximally across
the correlated patterns. -/
theorem bell_local_weight₁ {x₀ x₁ : FieldConfig K₁ N} (hx : x₀ ≠ x₁)
    {y₀ y₁ : FieldConfig K₂ N} (hy : y₀ ≠ y₁) :
    arenaObs (leftOp (Matrix.single x₁ x₁ 1))
      (Projectivization.mk ℂ (bellVec x₀ x₁ y₀ y₁)
        (bellVec_ne_zero x₀ x₁ y₀ y₁)) = 1 / 2 := by
  rw [arenaObs_leftOp_eq_reduced, reducedDM_bell hx hy, smul_mul_assoc,
    Matrix.add_mul, trace_smul, Matrix.trace_add, trace_mul_single,
    trace_mul_single]
  simp only [Matrix.single, Matrix.of_apply]
  rw [if_neg (fun h : x₀ = x₁ ∧ x₀ = x₁ => hx h.1),
    if_pos (⟨trivial, trivial⟩ : True ∧ True)]
  simp only [zero_add, smul_eq_mul, mul_one, RCLike.re_to_complex]
  norm_num [Complex.div_re, Complex.normSq_apply]

end CSD.CV

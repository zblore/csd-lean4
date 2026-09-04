/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.HamiltonianSignature
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import CsdLean4.Mathlib.QuantumInfo.JointRegister

/-!
# SigmaLayer/OnticComposite: A6 step 1 — the Segre embedding, and non-factorisation as a theorem

**Category:** 7-SigmaLayer (Paper C A6 — composite systems).

## What A6's "non-factorising composite" means, made sharp

Paper C A6 says the composite ontic sector is **not** the product of the subsystem sectors — that is
where entanglement lives. The sharp Lean form: the **Segre embedding**

  `segre : ℙ(ℂ^{n_A}) × ℙ(ℂ^{n_B}) → ℙ(ℂ^{n_A × n_B})`,  `([u], [v]) ↦ [u ⊗ v]`

is **injective but not surjective** whenever both factors have dimension ≥ 2. Injectivity says the
product-state manifold sits faithfully inside the composite sector; **non-surjectivity — witnessed
by a Bell-type vector — says the composite sector strictly exceeds it**:

  `Σ_AB ⊋ image (Σ_A × Σ_B)`.

That is A6's non-factorisation claim as a machine-checked theorem rather than an architectural
remark.

## ⚠️ Honest scope

* This is the **witness-level** A6 content. The corpus *constructs* the composite sector from the
  composite Hilbert space; A6-as-philosophy ("`Σ_AB` is primitive, not built from anything") is not
  a formalisation target and is not claimed.
* Steps 2–3 of the A6 plan — ontic reduction maps via `partialTrace`, and marginal stability under
  local flows (ontic no-signalling) — are **not in this file**.
* ~~Measure statements are not attempted~~ **SUPERSEDED 2026-08-21 (Q28 item 2)**: the topological
  half is now here — ★ `segre_range_isClosed` (the product rays are a closed, hence measurable,
  set), the reusable minor criterion `not_mem_range_segre`, and ★ `exists_entangled_mem_nhds`
  (entangled rays in every open neighbourhood of every product ray). The measure half — the
  Fubini–Study weight of the entangled complement is positive, globally and in every open
  neighbourhood of a product ray — is `RecordLayer/EntangledMeasure.lean`. What is still NOT
  proved is the μ_FS-NULL strengthening ("almost every composite state is entangled"): that is
  research-gated on Mathlib-scale inputs (`MATHLIB-GAPS.md`, polynomial zero sets).

## References

`Mathlib/QuantumInfo/JointRegister.lean` (`tensorState` and its API — the product vector `u ⊗ v`,
`tensorState_ne_zero`, `tensorState_smul_smul`, `tensorState_continuous` — which this file's Segre
embedding is built from); `LF3/Projectors/TensorModel.lean`, `LF6/GisinTheorem.lean` (the corpus's
operational entanglement); `specs/reconstruction-status.md` §2 (the A6 row this addresses);
`specs/BACKLOG.md`.
-/

@[expose] public section

open Topology QuantumInfo
open scoped LinearAlgebra.Projectivization

namespace CSD.RecordLayer

variable {nA nB : ℕ}

/-! ### The Segre embedding -/

/-- **The Segre embedding**: the pair of subsystem rays `([u], [v])` goes to the composite ray
`[u ⊗ v]`. Defined through representatives; `segre_mk` is the working form. -/
noncomputable def segre
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA)) × ℙ ℂ (EuclideanSpace ℂ (Fin nB))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)) :=
  Projectivization.mk ℂ (tensorState p.1.rep p.2.rep)
    (tensorState_ne_zero p.1.rep_nonzero p.2.rep_nonzero)

/-- The Segre embedding on representatives. -/
theorem segre_mk (u : EuclideanSpace ℂ (Fin nA)) (v : EuclideanSpace ℂ (Fin nB))
    (hu : u ≠ 0) (hv : v ≠ 0) :
    segre (Projectivization.mk ℂ u hu, Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (tensorState u v) (tensorState_ne_zero hu hv) := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ u hu).rep u
        (Projectivization.rep_nonzero _) hu).mp (Projectivization.mk_rep _)
  obtain ⟨b, hb⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ v hv).rep v
        (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  unfold segre
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 ((a : ℂ) * b) (mul_ne_zero (Units.ne_zero a) (Units.ne_zero b)), ?_⟩
  show ((a : ℂ) * b) • tensorState u v = tensorState (Projectivization.mk ℂ u hu).rep
    (Projectivization.mk ℂ v hv).rep
  have hau : (a : ℂ) • u = (Projectivization.mk ℂ u hu).rep := by
    simpa [Units.smul_def] using ha
  have hbv : (b : ℂ) • v = (Projectivization.mk ℂ v hv).rep := by
    simpa [Units.smul_def] using hb
  rw [← tensorState_smul_smul, hau, hbv]

/-- **The Segre embedding is injective**: product rays remember their factors. -/
theorem segre_injective : Function.Injective (segre (nA := nA) (nB := nB)) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  unfold segre at h
  rw [Projectivization.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  -- `u ⊗ v = c • (u' ⊗ v')` coordinatewise.
  have hcoord : ∀ (j : Fin nA) (k : Fin nB),
      p.rep j * q.rep k = (c : ℂ) * (p'.rep j * q'.rep k) := by
    intro j k
    have := congrArg (fun w : EuclideanSpace ℂ (Fin nA × Fin nB) => w (j, k)) hc
    simpa [Units.smul_def, PiLp.smul_apply, smul_eq_mul] using this.symm
  -- A nonzero coordinate of `q`.
  obtain ⟨k₀, hk₀⟩ : ∃ k, q.rep k ≠ 0 := by
    by_contra hz
    push Not at hz
    exact q.rep_nonzero (by apply PiLp.ext; intro k; simpa using hz k)
  -- `q'` is nonzero at `k₀` too, else `p.rep = 0`.
  have hk₀' : q'.rep k₀ ≠ 0 := by
    intro hz
    apply p.rep_nonzero
    apply PiLp.ext
    intro j
    have := hcoord j k₀
    rw [hz, mul_zero, mul_zero] at this
    simpa using mul_eq_zero.mp this |>.resolve_right hk₀
  -- So `p.rep` is a nonzero multiple of `p'.rep`.
  have hp : p = p' := by
    have hscal : p.rep = ((c : ℂ) * q'.rep k₀ / q.rep k₀) • p'.rep := by
      apply PiLp.ext
      intro j
      have h1 := hcoord j k₀
      show p.rep j = ((c : ℂ) * q'.rep k₀ / q.rep k₀) * p'.rep j
      field_simp
      linear_combination h1 * (1 : ℂ)
    have hcne : ((c : ℂ) * q'.rep k₀ / q.rep k₀) ≠ 0 :=
      div_ne_zero (mul_ne_zero (Units.ne_zero c) hk₀') hk₀
    calc p = Projectivization.mk ℂ p.rep p.rep_nonzero := (Projectivization.mk_rep p).symm
      _ = Projectivization.mk ℂ p'.rep p'.rep_nonzero := by
          rw [Projectivization.mk_eq_mk_iff]
          exact ⟨Units.mk0 _ hcne, hscal.symm⟩
      _ = p' := Projectivization.mk_rep p'
  -- Symmetrically for the second factor.
  obtain ⟨j₀, hj₀⟩ : ∃ j, p.rep j ≠ 0 := by
    by_contra hz
    push Not at hz
    exact p.rep_nonzero (by apply PiLp.ext; intro j; simpa using hz j)
  have hj₀' : p'.rep j₀ ≠ 0 := by
    intro hz
    apply q.rep_nonzero
    apply PiLp.ext
    intro k
    have := hcoord j₀ k
    rw [hz, zero_mul, mul_zero] at this
    simpa using mul_eq_zero.mp this |>.resolve_left hj₀
  have hq : q = q' := by
    have hscal : q.rep = ((c : ℂ) * p'.rep j₀ / p.rep j₀) • q'.rep := by
      apply PiLp.ext
      intro k
      have h1 := hcoord j₀ k
      show q.rep k = ((c : ℂ) * p'.rep j₀ / p.rep j₀) * q'.rep k
      field_simp
      linear_combination h1 * (1 : ℂ)
    have hcne : ((c : ℂ) * p'.rep j₀ / p.rep j₀) ≠ 0 :=
      div_ne_zero (mul_ne_zero (Units.ne_zero c) hj₀') hj₀
    calc q = Projectivization.mk ℂ q.rep q.rep_nonzero := (Projectivization.mk_rep q).symm
      _ = Projectivization.mk ℂ q'.rep q'.rep_nonzero := by
          rw [Projectivization.mk_eq_mk_iff]
          exact ⟨Units.mk0 _ hcne, hscal.symm⟩
      _ = q' := Projectivization.mk_rep q'
  exact Prod.ext hp hq

/-! ### Non-surjectivity: the Bell-type witness -/

/-- The Bell-type vector `e₀⊗e₀ + e₁⊗e₁` (unnormalised), defined whenever both factors have
dimension ≥ 2. -/
noncomputable def bellVec (hA : 2 ≤ nA) (hB : 2 ≤ nB) :
    EuclideanSpace ℂ (Fin nA × Fin nB) :=
  WithLp.toLp 2 fun jk =>
    if jk.1 = (⟨0, by omega⟩ : Fin nA) ∧ jk.2 = (⟨0, by omega⟩ : Fin nB) then 1
    else if jk.1 = (⟨1, by omega⟩ : Fin nA) ∧ jk.2 = (⟨1, by omega⟩ : Fin nB) then 1
    else 0

theorem bellVec_ne_zero (hA : 2 ≤ nA) (hB : 2 ≤ nB) : bellVec hA hB ≠ 0 := by
  intro h0
  have := congrArg (fun w : EuclideanSpace ℂ (Fin nA × Fin nB) =>
    w (⟨0, by omega⟩, ⟨0, by omega⟩)) h0
  simp [bellVec] at this

/-- **★ The Segre embedding is NOT surjective: the Bell ray is not a product ray.**

If `u ⊗ v = c • bell` with `c ≠ 0`, the four corner coordinates give `u₀v₀ = c`, `u₁v₁ = c`,
`u₀v₁ = 0`, `u₁v₀ = 0` — and `(u₀v₀)(u₁v₁) = c² ≠ 0 = (u₀v₁)(u₁v₀)` is a contradiction. So

  `Σ_AB ⊋ image (Σ_A × Σ_B)`

whenever both factors have dimension ≥ 2: **the composite sector strictly exceeds the product of
the subsystem sectors.** Paper C A6's non-factorisation, as a theorem. -/
theorem segre_not_surjective (hA : 2 ≤ nA) (hB : 2 ≤ nB) :
    Projectivization.mk ℂ (bellVec hA hB) (bellVec_ne_zero hA hB)
      ∉ Set.range (segre (nA := nA) (nB := nB)) := by
  rintro ⟨⟨p, q⟩, hpq⟩
  -- Compare coordinates of `u ⊗ v = c • bell`.
  rw [show (p, q) = (Projectivization.mk ℂ p.rep p.rep_nonzero,
        Projectivization.mk ℂ q.rep q.rep_nonzero) by
      rw [Projectivization.mk_rep, Projectivization.mk_rep],
    segre_mk] at hpq
  rw [Projectivization.mk_eq_mk_iff] at hpq
  obtain ⟨c, hc⟩ := hpq
  set i0A : Fin nA := ⟨0, by omega⟩
  set i1A : Fin nA := ⟨1, by omega⟩
  set i0B : Fin nB := ⟨0, by omega⟩
  set i1B : Fin nB := ⟨1, by omega⟩
  have hcoord : ∀ (j : Fin nA) (k : Fin nB),
      p.rep j * q.rep k = (c : ℂ) * (bellVec hA hB) (j, k) := by
    intro j k
    have h := congrArg (fun w : EuclideanSpace ℂ (Fin nA × Fin nB) => w (j, k)) hc
    simpa [Units.smul_def, PiLp.smul_apply, smul_eq_mul, tensorState_apply] using h.symm
  have h00 := hcoord i0A i0B
  have h11 := hcoord i1A i1B
  have h01 := hcoord i0A i1B
  have h10 := hcoord i1A i0B
  have h0ne1A : i0A ≠ i1A := by
    intro h
    have := congrArg Fin.val h
    simp [i0A, i1A] at this
  have h0ne1B : i0B ≠ i1B := by
    intro h
    have := congrArg Fin.val h
    simp [i0B, i1B] at this
  rw [show (bellVec hA hB) (i0A, i0B) = 1 by
    simp [bellVec, i0A, i0B, Fin.ext_iff]] at h00
  rw [show (bellVec hA hB) (i1A, i1B) = 1 by
    simp [bellVec, i1A, i1B, Fin.ext_iff]] at h11
  rw [show (bellVec hA hB) (i0A, i1B) = 0 by
    simp [bellVec, i0A, i1B, Fin.ext_iff]] at h01
  rw [show (bellVec hA hB) (i1A, i0B) = 0 by
    simp [bellVec, i1A, i0B, Fin.ext_iff]] at h10
  -- `(u₀v₀)(u₁v₁) = c² ≠ 0`, but it also equals `(u₀v₁)(u₁v₀) = 0`.
  rw [mul_zero] at h01 h10
  have hprod : ((c : ℂ) * 1) * ((c : ℂ) * 1) = 0 := by
    nth_rewrite 2 [← h11]
    nth_rewrite 1 [← h00]
    calc p.rep i0A * q.rep i0B * (p.rep i1A * q.rep i1B)
        = (p.rep i0A * q.rep i1B) * (p.rep i1A * q.rep i0B) := by ring
      _ = 0 := by rw [h01, h10, mul_zero]
  have hcc : (c : ℂ) * c = 0 := by simp at hprod
  exact Units.ne_zero c (mul_self_eq_zero.mp hcc)

/-! ### Topology of the Segre image (Q28 item 2a)

The Segre embedding is continuous — descended through the open quotient maps
`mk'` on both factors — so its range, the continuous image of a compact space,
is closed. That measurability-grade fact is what the measure tier
(`RecordLayer/EntangledMeasure.lean`) consumes. -/

/-- **The Segre embedding is continuous.** Continuity descends through the open
quotient maps `mk'` on both factors (`IsOpenQuotientMap.prodMap`), where the
composite is `mk'` of the continuous nonvanishing `QuantumInfo.tensorState`. -/
theorem segre_continuous : Continuous (segre (nA := nA) (nB := nB)) := by
  have hq : IsQuotientMap
      (Prod.map (Projectivization.mk' ℂ) (Projectivization.mk' ℂ) :
        { v : EuclideanSpace ℂ (Fin nA) // v ≠ 0 } ×
          { v : EuclideanSpace ℂ (Fin nB) // v ≠ 0 } →
        ℙ ℂ (EuclideanSpace ℂ (Fin nA)) × ℙ ℂ (EuclideanSpace ℂ (Fin nB))) :=
    (Projectivization.isOpenQuotientMap_mk'.prodMap
      Projectivization.isOpenQuotientMap_mk').isQuotientMap
  rw [hq.continuous_iff]
  have h_eq : (segre ∘ Prod.map (Projectivization.mk' ℂ) (Projectivization.mk' ℂ))
      = fun uv : { v : EuclideanSpace ℂ (Fin nA) // v ≠ 0 } ×
          { v : EuclideanSpace ℂ (Fin nB) // v ≠ 0 } =>
        Projectivization.mk' ℂ
          ⟨tensorState uv.1.val uv.2.val, tensorState_ne_zero uv.1.property uv.2.property⟩ := by
    funext uv
    show segre (Projectivization.mk' ℂ uv.1, Projectivization.mk' ℂ uv.2) = _
    rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk, segre_mk,
      Projectivization.mk'_eq_mk]
  rw [h_eq]
  refine Projectivization.continuous_mk'.comp (Continuous.subtype_mk ?_ _)
  exact tensorState_continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- ★ **The Segre image is closed** (Q28 item 2a): the continuous image of the
compact product of projective spaces, in a Hausdorff target. In particular the
set of product rays is measurable and its complement — the entangled rays — is
open. -/
theorem segre_range_isClosed :
    IsClosed (Set.range (segre (nA := nA) (nB := nB))) :=
  (isCompact_range segre_continuous).isClosed

/-! ### The minor criterion (the reusable rank obstruction)

A ray is a product ray only if its coefficient matrix `w (j, k)` has all `2×2`
minors equal — the rank-one condition. The contrapositive is the reusable
entanglement witness: one unequal minor puts a ray outside the Segre image.
`segre_not_surjective`'s Bell computation is the special case
`(j,k,j',k') = (0,0,1,1)`. -/

/-- Membership in the Segre image forces every `2×2` minor of the coefficient
matrix to balance: `w (j,k) · w (j',k') = w (j,k') · w (j',k)`. -/
theorem segre_minor_eq {w : EuclideanSpace ℂ (Fin nA × Fin nB)} {hw : w ≠ 0}
    (h : Projectivization.mk ℂ w hw ∈ Set.range (segre (nA := nA) (nB := nB)))
    (j j' : Fin nA) (k k' : Fin nB) :
    w (j, k) * w (j', k') = w (j, k') * w (j', k) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := h
  unfold segre at hpq
  rw [Projectivization.mk_eq_mk_iff] at hpq
  obtain ⟨c, hc⟩ := hpq
  have hcoord : ∀ (a : Fin nA) (b : Fin nB),
      (c : ℂ) * w (a, b) = p.rep a * q.rep b := by
    intro a b
    have := congrArg
      (fun z : EuclideanSpace ℂ (Fin nA × Fin nB) => z (a, b)) hc
    simpa [Units.smul_def, PiLp.smul_apply, smul_eq_mul] using this
  have hcc : (c : ℂ) * (c : ℂ) ≠ 0 :=
    mul_ne_zero (Units.ne_zero c) (Units.ne_zero c)
  refine mul_left_cancel₀ hcc ?_
  calc (c : ℂ) * (c : ℂ) * (w (j, k) * w (j', k'))
      = ((c : ℂ) * w (j, k)) * ((c : ℂ) * w (j', k')) := by ring
    _ = (p.rep j * q.rep k) * (p.rep j' * q.rep k') := by
        rw [hcoord j k, hcoord j' k']
    _ = (p.rep j * q.rep k') * (p.rep j' * q.rep k) := by ring
    _ = ((c : ℂ) * w (j, k')) * ((c : ℂ) * w (j', k)) := by
        rw [hcoord j k', hcoord j' k]
    _ = (c : ℂ) * (c : ℂ) * (w (j, k') * w (j', k)) := by ring

/-- **The entanglement witness, reusable form**: one unbalanced `2×2` minor
puts a ray outside the Segre image. -/
theorem not_mem_range_segre {w : EuclideanSpace ℂ (Fin nA × Fin nB)}
    (hw : w ≠ 0) {j j' : Fin nA} {k k' : Fin nB}
    (h : w (j, k) * w (j', k') ≠ w (j, k') * w (j', k)) :
    Projectivization.mk ℂ w hw ∉ Set.range (segre (nA := nA) (nB := nB)) :=
  fun hmem => h (segre_minor_eq hmem j j' k k')

/-! ### Entangled rays are dense near every product ray (Q28 item 2b)

The path `t ↦ [a ⊗ b + t · e_{(j₁,k₁)}]` is continuous, lands on the product
ray at `t = 0`, and for `t ≠ 0` fails the minor criterion at the corner
`(j₀, j₁, k₀, k₁)` — a single standard-basis perturbation, no orthogonal
complements needed. -/

/-- ★ **Entangled rays in every neighbourhood of every product ray** (Q28 item
2b, topological form): whenever both factors have dimension ≥ 2, every open set
containing a product ray also contains a ray outside the Segre image. -/
theorem exists_entangled_mem_nhds (hA : 2 ≤ nA) (hB : 2 ≤ nB)
    {p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))}
    (hp : p ∈ Set.range (segre (nA := nA) (nB := nB)))
    {U : Set (ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)))}
    (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ q ∈ U, q ∉ Set.range (segre (nA := nA) (nB := nB)) := by
  obtain ⟨⟨pA, pB⟩, rfl⟩ := hp
  set a := pA.rep with ha_def
  set b := pB.rep with hb_def
  obtain ⟨j₀, hj₀⟩ : ∃ j, a j ≠ 0 := by
    by_contra h
    push Not at h
    exact pA.rep_nonzero (by apply PiLp.ext; intro j; simpa using h j)
  obtain ⟨k₀, hk₀⟩ : ∃ k, b k ≠ 0 := by
    by_contra h
    push Not at h
    exact pB.rep_nonzero (by apply PiLp.ext; intro k; simpa using h k)
  have : Nontrivial (Fin nA) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
    intro h; have := congrArg Fin.val h; simp at this⟩⟩
  have : Nontrivial (Fin nB) := ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
    intro h; have := congrArg Fin.val h; simp at this⟩⟩
  obtain ⟨j₁, hj₁⟩ := exists_ne j₀
  obtain ⟨k₁, hk₁⟩ := exists_ne k₀
  set e : EuclideanSpace ℂ (Fin nA × Fin nB) :=
    EuclideanSpace.single (j₁, k₁) 1 with he_def
  have he_apply : ∀ jk : Fin nA × Fin nB,
      e jk = if jk = (j₁, k₁) then 1 else 0 := by
    intro jk
    rw [he_def, PiLp.single_apply]
  have hw : ∀ t : ℂ, tensorState a b + t • e ≠ 0 := by
    intro t h0
    have h00 := congrArg
      (fun z : EuclideanSpace ℂ (Fin nA × Fin nB) => z (j₀, k₀)) h0
    have hsingle : e (j₀, k₀) = 0 := by
      rw [he_apply]
      exact if_neg (by intro h; exact hj₁ (congrArg Prod.fst h).symm)
    simp only [PiLp.add_apply, PiLp.smul_apply, tensorState_apply, hsingle,
      smul_eq_mul, mul_zero, add_zero, PiLp.zero_apply] at h00
    exact mul_ne_zero hj₀ hk₀ h00
  set γ : ℂ → ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)) :=
    fun t => Projectivization.mk' ℂ ⟨tensorState a b + t • e, hw t⟩ with hγ_def
  have hγc : Continuous γ := by
    refine Projectivization.continuous_mk'.comp (Continuous.subtype_mk ?_ _)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = segre (pA, pB) := by
    show Projectivization.mk' ℂ ⟨tensorState a b + (0 : ℂ) • e, hw 0⟩ = segre (pA, pB)
    rw [Projectivization.mk'_eq_mk]
    unfold segre
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    show (1 : ℂ) • tensorState pA.rep pB.rep = tensorState a b + (0 : ℂ) • e
    rw [one_smul, zero_smul, add_zero]
  have hnhds : γ ⁻¹' U ∈ nhds (0 : ℂ) :=
    hγc.continuousAt.preimage_mem_nhds (hU.mem_nhds (hγ0 ▸ hpU))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨t, ht_pos, ht_lt⟩ := NormedField.exists_norm_lt ℂ hε
  have ht0 : t ≠ 0 := norm_pos_iff.mp ht_pos
  have htU : γ t ∈ U := hball (by simpa [Metric.mem_ball, dist_zero_right] using ht_lt)
  refine ⟨γ t, htU, ?_⟩
  show Projectivization.mk' ℂ ⟨tensorState a b + t • e, hw t⟩ ∉
    Set.range (segre (nA := nA) (nB := nB))
  rw [Projectivization.mk'_eq_mk]
  refine not_mem_range_segre (hw t) (j := j₀) (j' := j₁) (k := k₀) (k' := k₁) ?_
  have hval : ∀ (j : Fin nA) (k : Fin nB),
      (tensorState a b + t • e) (j, k)
        = a j * b k + t * (if (j, k) = ((j₁ : Fin nA), (k₁ : Fin nB)) then 1 else 0) := by
    intro j k
    simp only [PiLp.add_apply, PiLp.smul_apply, tensorState_apply, he_apply,
      smul_eq_mul]
  rw [hval j₀ k₀, hval j₁ k₁, hval j₀ k₁, hval j₁ k₀]
  rw [if_neg (by intro h; exact hj₁ (congrArg Prod.fst h).symm),
    if_pos rfl,
    if_neg (by intro h; exact hj₁ (congrArg Prod.fst h).symm),
    if_neg (by intro h; exact hk₁ (congrArg Prod.snd h).symm)]
  intro heq
  have hz : a j₀ * b k₀ * t = 0 := by linear_combination heq
  exact mul_ne_zero (mul_ne_zero hj₀ hk₀) ht0 hz

end CSD.RecordLayer

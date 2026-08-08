/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.HamiltonianSignature

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
* Measure statements (e.g. the Segre image is `μ_FS`-null — "almost every composite state is
  entangled") are not attempted; the strict inclusion carries the axiom's weight.

## References

`LF3/Projectors/TensorModel.lean`, `LF6/GisinTheorem.lean` (the corpus's operational entanglement);
`specs/reconstruction-status.md` §2 (the A6 row this addresses); `specs/BACKLOG.md`.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace CSD.RecordLayer

variable {nA nB : ℕ}

/-! ### Product vectors -/

/-- The product (Kronecker) vector `u ⊗ v`: coordinates `(u ⊗ v)(j,k) = u j · v k`. -/
noncomputable def prodVec (u : EuclideanSpace ℂ (Fin nA)) (v : EuclideanSpace ℂ (Fin nB)) :
    EuclideanSpace ℂ (Fin nA × Fin nB) :=
  WithLp.toLp 2 fun jk => u jk.1 * v jk.2

@[simp] theorem prodVec_apply (u : EuclideanSpace ℂ (Fin nA)) (v : EuclideanSpace ℂ (Fin nB))
    (j : Fin nA) (k : Fin nB) : prodVec u v (j, k) = u j * v k := rfl

theorem prodVec_smul_smul (a b : ℂ) (u : EuclideanSpace ℂ (Fin nA))
    (v : EuclideanSpace ℂ (Fin nB)) :
    prodVec (a • u) (b • v) = (a * b) • prodVec u v := by
  apply PiLp.ext
  intro jk
  show (a • u) jk.1 * (b • v) jk.2 = (a * b) * (u jk.1 * v jk.2)
  simp [PiLp.smul_apply, smul_eq_mul]
  ring

theorem prodVec_ne_zero {u : EuclideanSpace ℂ (Fin nA)} {v : EuclideanSpace ℂ (Fin nB)}
    (hu : u ≠ 0) (hv : v ≠ 0) : prodVec u v ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (by apply PiLp.ext; intro j; simpa using h j)
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (by apply PiLp.ext; intro k; simpa using h k)
  intro h0
  have := congrArg (fun w : EuclideanSpace ℂ (Fin nA × Fin nB) => w (j, k)) h0
  simp only [prodVec_apply] at this
  exact mul_ne_zero hj hk (by simpa using this)

/-! ### The Segre embedding -/

/-- **The Segre embedding**: the pair of subsystem rays `([u], [v])` goes to the composite ray
`[u ⊗ v]`. Defined through representatives; `segre_mk` is the working form. -/
noncomputable def segre
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA)) × ℙ ℂ (EuclideanSpace ℂ (Fin nB))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)) :=
  Projectivization.mk ℂ (prodVec p.1.rep p.2.rep)
    (prodVec_ne_zero p.1.rep_nonzero p.2.rep_nonzero)

/-- The Segre embedding on representatives. -/
theorem segre_mk (u : EuclideanSpace ℂ (Fin nA)) (v : EuclideanSpace ℂ (Fin nB))
    (hu : u ≠ 0) (hv : v ≠ 0) :
    segre (Projectivization.mk ℂ u hu, Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (prodVec u v) (prodVec_ne_zero hu hv) := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ u hu).rep u
        (Projectivization.rep_nonzero _) hu).mp (Projectivization.mk_rep _)
  obtain ⟨b, hb⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ v hv).rep v
        (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  unfold segre
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 ((a : ℂ) * b) (mul_ne_zero (Units.ne_zero a) (Units.ne_zero b)), ?_⟩
  show ((a : ℂ) * b) • prodVec u v = prodVec (Projectivization.mk ℂ u hu).rep
    (Projectivization.mk ℂ v hv).rep
  have hau : (a : ℂ) • u = (Projectivization.mk ℂ u hu).rep := by
    simpa [Units.smul_def] using ha
  have hbv : (b : ℂ) • v = (Projectivization.mk ℂ v hv).rep := by
    simpa [Units.smul_def] using hb
  rw [← prodVec_smul_smul, hau, hbv]

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
    simpa [Units.smul_def, PiLp.smul_apply, smul_eq_mul, prodVec_apply] using h.symm
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

end CSD.RecordLayer

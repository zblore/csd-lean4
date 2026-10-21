/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.ClassicalOtoc
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Periodic points of the cat map grow at the Lyapunov exponent

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #176 (out of #19 and #150).

The fixed points of `cat^[t]` on `T²` are the kernel of the toral endomorphism `Aᵗ − I`. Lifting
to the plane, they are the points `C⁻¹m mod ℤ²` for `m ∈ ℤ²`, `C = Aᵗ − I`, so the fixed-point set
is `ℤ² / Cℤ²`, whose order is `|det C|` (Mathlib's `Submodule.natAbs_det_basis_change`). With
`Aᵗ = [[F₂ₜ₊₁, F₂ₜ], [F₂ₜ, F₂ₜ₋₁]]` (`catR_pow_apply`) and Cassini's identity,
`det C = 2 − tr Aᵗ = 2 − L₂ₜ` where `L₂ₜ = 2F₂ₜ₊₁ − F₂ₜ` is the Lucas number, so

  `#Fix(cat^[t]) = L₂ₜ − 2 = φ²ᵗ + φ⁻²ᵗ − 2 = (φᵗ − φ⁻ᵗ)²`,

and `(1/t) log #Fix(cat^[t]) → 2 log φ`: the periodic points grow at exactly the Lyapunov exponent
of `hasLyapunovExponent_catR` — the cat-map instance of *topological entropy = Lyapunov exponent*.

* `MeasureTheory.lucasEven` — `L₂ₜ = 2F₂ₜ₊₁ − F₂ₜ`, with ★ `lucasEven_eq` its Binet form
  `φ²ᵗ + ψ²ᵗ` and `three_le_lucasEven_succ`;
* `MeasureTheory.cassini` — `F₍ₙ₊₂₎Fₙ − F₍ₙ₊₁₎² = (−1)ⁿ⁺¹`;
* `MeasureTheory.catLatMat`, `catLat`, ★ `det_catLatMat` — the integer matrix `Aᵗ − I` and its
  determinant `2 − L₂ₜ`;
* `MeasureTheory.cat_iterate_coe` — `cat^[t]` descends from `catR ^ t`;
* `MeasureTheory.catFixLift`, `catFixLift_mem`, `catFixLift_surjective`, `ker_catFixLift` — the
  parametrisation of the fixed points by `ℤ²`, with kernel `Cℤ²`;
* ★★★ `MeasureTheory.card_fixedPoints_cat_iterate` — **`#Fix(cat^[t]) = L₂ₜ − 2`** for `t ≥ 1`;
* ★★ `MeasureTheory.tendsto_log_card_fixedPoints_cat` — **the growth rate is `2 log φ`**.

## Honest scope

* The cat matrix only; for a general hyperbolic `A ∈ SL₂(ℤ)` the same argument gives
  `|det(Aᵗ − I)| = |tr Aᵗ − 2|` and growth at `log` of the spectral radius.
* "Topological entropy" is not defined here; the statement is the growth rate of the periodic-point
  count, which is what that entropy equals for a hyperbolic toral automorphism.
* `t ≥ 1` throughout (`cat^[0] = id` has every point fixed).

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §1.8 and
§3.2 (periodic points of toral automorphisms, `|det(Aⁿ − I)|`); Walters, *An Introduction to Ergodic
Theory*, §8.2; `Mathlib/LinearAlgebra/FreeModule/Finite/CardQuotient.lean`
(`Submodule.natAbs_det_basis_change`); in-corpus `CatMapWitness.lean` (`cat`),
`LyapunovExponent.lean` (`catR`, `cat_coe`, `hasLyapunovExponent_catR`), `ClassicalOtoc.lean`
(`catR_pow_apply`); `specs/BACKLOG.md` #176, #19, #150, #148.
-/

@[expose] public section

open Filter Topology Function Module
open scoped goldenRatio

namespace MeasureTheory

/-! ### Lucas numbers and Cassini -/

/-- The even Lucas number `L₂ₙ = 2F₂ₙ₊₁ − F₂ₙ`, as an integer. -/
def lucasEven (n : ℕ) : ℤ := 2 * (Nat.fib (2 * n + 1) : ℤ) - (Nat.fib (2 * n) : ℤ)

/-- Cassini's identity, `F₍ₙ₊₂₎ Fₙ − F₍ₙ₊₁₎² = (−1)ⁿ⁺¹`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * Nat.fib n - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
        rw [show k + 3 = (k + 1) + 2 by ring, Nat.fib_add_two]
        push_cast
        ring
      have h2 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring, h, pow_succ]
      linear_combination (-1 : ℤ) * ih - (Nat.fib (k + 2) : ℤ) * h2

/-- `L₂ₜ ≥ 3` for `t ≥ 1`. -/
theorem three_le_lucasEven_succ (s : ℕ) : 3 ≤ lucasEven (s + 1) := by
  unfold lucasEven
  have h1 : Nat.fib (2 * (s + 1) + 1) = Nat.fib (2 * s + 1) + Nat.fib (2 * s + 2) := by
    rw [show 2 * (s + 1) + 1 = (2 * s + 1) + 2 by ring, Nat.fib_add_two]
  have h2 : 1 ≤ Nat.fib (2 * s + 1) := Nat.fib_pos.2 (by omega)
  have h3 : 1 ≤ Nat.fib (2 * s + 2) := Nat.fib_pos.2 (by omega)
  rw [show 2 * (s + 1) = 2 * s + 2 by ring] at *
  rw [h1]
  push_cast
  omega

/-- ★ **Binet for the even Lucas numbers**: `L₂ₙ = φ²ⁿ + ψ²ⁿ`. -/
theorem lucasEven_eq (n : ℕ) : (lucasEven n : ℝ) = φ ^ (2 * n) + ψ ^ (2 * n) := by
  unfold lucasEven
  push_cast
  rw [Real.coe_fib_eq, Real.coe_fib_eq]
  have h1 : φ + ψ = 1 := Real.goldenRatio_add_goldenConj
  have h2 : φ - ψ = √5 := Real.goldenRatio_sub_goldenConj
  have h5 : (√5 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [← h2]
  linear_combination (φ ^ (2 * n) - ψ ^ (2 * n)) * h1

/-! ### The lattice `Aᵗ − I` -/

/-- The integer matrix `Aᵗ − I = [[F₂ₜ₊₁ − 1, F₂ₜ], [F₂ₜ, F₂ₜ₊₁ − F₂ₜ − 1]]`. -/
def catLatMat (t : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(Nat.fib (2 * t + 1) : ℤ) - 1, (Nat.fib (2 * t) : ℤ);
     (Nat.fib (2 * t) : ℤ), (Nat.fib (2 * t + 1) : ℤ) - Nat.fib (2 * t) - 1]

/-- ★ `det(Aᵗ − I) = 2 − L₂ₜ` for `t ≥ 1`, by Cassini. -/
theorem det_catLatMat (s : ℕ) : (catLatMat (s + 1)).det = 2 - lucasEven (s + 1) := by
  rw [catLatMat, Matrix.det_fin_two_of, lucasEven]
  have hc := cassini (2 * s + 1)
  have hpow : (-1 : ℤ) ^ (2 * s + 1 + 1) = 1 := by
    rw [show 2 * s + 1 + 1 = 2 * (s + 1) by ring, pow_mul]
    simp
  rw [hpow, show 2 * s + 1 + 2 = 2 * (s + 1) + 1 by ring,
    show 2 * s + 1 + 1 = 2 * (s + 1) by ring] at hc
  have hf : (Nat.fib (2 * (s + 1) + 1) : ℤ) = Nat.fib (2 * s + 1) + Nat.fib (2 * (s + 1)) := by
    rw [show 2 * (s + 1) + 1 = (2 * s + 1) + 2 by ring, show 2 * (s + 1) = 2 * s + 1 + 1 by ring,
      Nat.fib_add_two]
    push_cast
    ring
  linear_combination hc + (Nat.fib (2 * (s + 1) + 1) : ℤ) * hf

/-- The lattice map `ℤ² → ℤ²`, `m ↦ (Aᵗ − I) m`. -/
noncomputable def catLat (t : ℕ) : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) := Matrix.toLin' (catLatMat t)

theorem catLat_apply (t : ℕ) (m : Fin 2 → ℤ) :
    catLat t m = ![((Nat.fib (2 * t + 1) : ℤ) - 1) * m 0 + (Nat.fib (2 * t) : ℤ) * m 1,
      (Nat.fib (2 * t) : ℤ) * m 0 + ((Nat.fib (2 * t + 1) : ℤ) - Nat.fib (2 * t) - 1) * m 1] := by
  rw [catLat, Matrix.toLin'_apply, catLatMat]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det_catLat (s : ℕ) : LinearMap.det (catLat (s + 1)) = 2 - lucasEven (s + 1) := by
  rw [catLat, LinearMap.det_toLin', det_catLatMat]

theorem det_catLat_ne_zero (s : ℕ) : LinearMap.det (catLat (s + 1)) ≠ 0 := by
  rw [det_catLat]
  have := three_le_lucasEven_succ s
  omega

/-- `Aᵗ − I` is injective on `ℤ²`: multiply by the adjugate. -/
theorem catLat_injective (s : ℕ) : Injective (catLat (s + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  have hdet : (catLatMat (s + 1)).det ≠ 0 := by
    rw [det_catLatMat]
    have := three_le_lucasEven_succ s
    omega
  have h := congrArg (fun v => (catLatMat (s + 1)).adjugate.mulVec v) hm
  simp only [catLat, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact (smul_eq_zero.1 h).resolve_left hdet


/-! ### The iterate descends from `catR ^ t` -/

/-- `cat^[t]` on the torus is the descent of `catR ^ t` on the plane. -/
theorem cat_iterate_coe (t : ℕ) (x y : ℝ) :
    cat^[t] ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = ((((catR ^ t) (x, y)).1 : AddCircle (1 : ℝ)), (((catR ^ t) (x, y)).2 : AddCircle (1 : ℝ))) := by
  induction t with
  | zero => simp
  | succ k ih =>
      rw [iterate_succ_apply', ih, cat_coe, pow_succ', ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply]

/-! ### The real matrices `Aᵗ − I` and its adjugate -/

/-- The real matrix `Aᵗ − I` acting on the plane. -/
noncomputable def catCr (t : ℕ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (((Nat.fib (2 * t + 1) : ℝ) - 1) * v.1 + (Nat.fib (2 * t) : ℝ) * v.2,
    (Nat.fib (2 * t) : ℝ) * v.1 + ((Nat.fib (2 * t + 1) : ℝ) - Nat.fib (2 * t) - 1) * v.2)

/-- The adjugate of `Aᵗ − I`, acting on the plane. -/
noncomputable def catAdjR (t : ℕ) (w : ℝ × ℝ) : ℝ × ℝ :=
  (((Nat.fib (2 * t + 1) : ℝ) - Nat.fib (2 * t) - 1) * w.1 - (Nat.fib (2 * t) : ℝ) * w.2,
    -(Nat.fib (2 * t) : ℝ) * w.1 + ((Nat.fib (2 * t + 1) : ℝ) - 1) * w.2)

/-- `det(Aᵗ − I)` as a real number. -/
noncomputable def catDetR (t : ℕ) : ℝ :=
  ((Nat.fib (2 * t + 1) : ℝ) - 1) * ((Nat.fib (2 * t + 1) : ℝ) - Nat.fib (2 * t) - 1)
    - (Nat.fib (2 * t) : ℝ) * Nat.fib (2 * t)

theorem catDetR_eq (t : ℕ) : catDetR t = ((catLatMat t).det : ℝ) := by
  rw [catLatMat, Matrix.det_fin_two_of, catDetR]
  push_cast
  ring

theorem catDetR_succ (s : ℕ) : catDetR (s + 1) = ((2 - lucasEven (s + 1) : ℤ) : ℝ) := by
  rw [catDetR_eq, det_catLatMat]

theorem catDetR_succ_ne_zero (s : ℕ) : catDetR (s + 1) ≠ 0 := by
  rw [catDetR_succ]
  have := three_le_lucasEven_succ s
  exact_mod_cast (by omega : (2 - lucasEven (s + 1) : ℤ) ≠ 0)

theorem catR_pow_eq_catCr_add (t : ℕ) (v : ℝ × ℝ) : (catR ^ t) v = catCr t v + v := by
  rw [catR_pow_apply]
  ext <;> simp only [catCr, Prod.fst_add, Prod.snd_add] <;> ring

theorem catCr_add (t : ℕ) (v w : ℝ × ℝ) : catCr t (v + w) = catCr t v + catCr t w := by
  ext <;> simp only [catCr, Prod.fst_add, Prod.snd_add] <;> ring

theorem catCr_smul (t : ℕ) (c : ℝ) (v : ℝ × ℝ) : catCr t (c • v) = c • catCr t v := by
  ext <;> simp only [catCr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem catAdjR_add (t : ℕ) (v w : ℝ × ℝ) : catAdjR t (v + w) = catAdjR t v + catAdjR t w := by
  ext <;> simp only [catAdjR, Prod.fst_add, Prod.snd_add] <;> ring

theorem catAdjR_catCr (t : ℕ) (v : ℝ × ℝ) : catAdjR t (catCr t v) = catDetR t • v := by
  ext <;> simp only [catAdjR, catCr, catDetR, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem catCr_catAdjR (t : ℕ) (w : ℝ × ℝ) : catCr t (catAdjR t w) = catDetR t • w := by
  ext <;> simp only [catAdjR, catCr, catDetR, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- On integer vectors, `catCr` is `catLat`. -/
theorem catCr_intCast (t : ℕ) (k : Fin 2 → ℤ) :
    catCr t ((k 0 : ℝ), (k 1 : ℝ)) = (((catLat t k) 0 : ℝ), ((catLat t k) 1 : ℝ)) := by
  rw [catLat_apply]
  ext <;> simp only [catCr, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    push_cast <;> ring

/-! ### The fixed points, parametrised by `ℤ²` -/

/-- The real lift of the fixed point attached to `m ∈ ℤ²`: `(Aᵗ − I)⁻¹ m`. -/
noncomputable def catFixVec (s : ℕ) (m : Fin 2 → ℤ) : ℝ × ℝ :=
  (catDetR (s + 1))⁻¹ • catAdjR (s + 1) ((m 0 : ℝ), (m 1 : ℝ))

theorem catCr_catFixVec (s : ℕ) (m : Fin 2 → ℤ) :
    catCr (s + 1) (catFixVec s m) = ((m 0 : ℝ), (m 1 : ℝ)) := by
  rw [catFixVec, catCr_smul, catCr_catAdjR, smul_smul,
    inv_mul_cancel₀ (catDetR_succ_ne_zero s), one_smul]

theorem catFixVec_add (s : ℕ) (m n : Fin 2 → ℤ) :
    catFixVec s (m + n) = catFixVec s m + catFixVec s n := by
  simp only [catFixVec, Pi.add_apply, Int.cast_add]
  rw [show (((m 0 : ℝ) + n 0, (m 1 : ℝ) + n 1) : ℝ × ℝ) = ((m 0 : ℝ), (m 1 : ℝ)) + ((n 0 : ℝ), (n 1 : ℝ))
    from rfl, catAdjR_add, smul_add]

/-- The integer `k` is `0` on the circle. -/
theorem coe_intCast_eq_zero (k : ℤ) : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨k, by simp⟩

/-- `ℤ² → T²`, `m ↦ (Aᵗ − I)⁻¹ m mod ℤ²`: the parametrisation of the fixed points. -/
noncomputable def catFixLift (s : ℕ) : (Fin 2 → ℤ) →+ Torus2 :=
  AddMonoidHom.mk'
    (fun m => (((catFixVec s m).1 : AddCircle (1 : ℝ)), ((catFixVec s m).2 : AddCircle (1 : ℝ))))
    (fun m n => by
      rw [catFixVec_add]
      ext <;> simp)

theorem catFixLift_apply (s : ℕ) (m : Fin 2 → ℤ) :
    catFixLift s m = (((catFixVec s m).1 : AddCircle (1 : ℝ)), ((catFixVec s m).2 : AddCircle (1 : ℝ))) :=
  rfl

/-- Every parametrised point is fixed. -/
theorem catFixLift_mem (s : ℕ) (m : Fin 2 → ℤ) : cat^[s + 1] (catFixLift s m) = catFixLift s m := by
  rw [catFixLift_apply, cat_iterate_coe, catR_pow_eq_catCr_add, catCr_catFixVec]
  ext
  · simp only [Prod.fst_add]
    rw [AddCircle.coe_add, coe_intCast_eq_zero, zero_add]
  · simp only [Prod.snd_add]
    rw [AddCircle.coe_add, coe_intCast_eq_zero, zero_add]

/-- A real number whose class is `0` is an integer. -/
theorem exists_int_of_coe_eq_zero {x : ℝ} (hx : (x : AddCircle (1 : ℝ)) = 0) : ∃ k : ℤ, (k : ℝ) = x := by
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 hx
  exact ⟨k, by simpa using hk⟩

/-- Every fixed point is parametrised. -/
theorem catFixLift_surjective (s : ℕ) (p : Torus2) (hp : cat^[s + 1] p = p) :
    ∃ m : Fin 2 → ℤ, catFixLift s m = p := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective p.1
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective p.2
  have hpxy : p = ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ))) := Prod.ext hx.symm hy.symm
  rw [hpxy, cat_iterate_coe, catR_pow_eq_catCr_add] at hp
  have h1 : ((catCr (s + 1) (x, y)).1 : AddCircle (1 : ℝ)) = 0 := by
    have := congrArg Prod.fst hp
    simp only [Prod.fst_add] at this
    rw [AddCircle.coe_add] at this
    exact add_right_cancel (this.trans (zero_add _).symm)
  have h2 : ((catCr (s + 1) (x, y)).2 : AddCircle (1 : ℝ)) = 0 := by
    have := congrArg Prod.snd hp
    simp only [Prod.snd_add] at this
    rw [AddCircle.coe_add] at this
    exact add_right_cancel (this.trans (zero_add _).symm)
  obtain ⟨k₀, hk₀⟩ := exists_int_of_coe_eq_zero h1
  obtain ⟨k₁, hk₁⟩ := exists_int_of_coe_eq_zero h2
  refine ⟨![k₀, k₁], ?_⟩
  have hv : catFixVec s ![k₀, k₁] = (x, y) := by
    rw [catFixVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hk₀, hk₁, Prod.mk.eta, catAdjR_catCr, smul_smul, inv_mul_cancel₀ (catDetR_succ_ne_zero s),
      one_smul]
  rw [catFixLift_apply, hv, hpxy]

/-- The kernel of the parametrisation is the lattice `(Aᵗ − I)ℤ²`. -/
theorem catFixLift_eq_zero_iff (s : ℕ) (m : Fin 2 → ℤ) :
    catFixLift s m = 0 ↔ m ∈ LinearMap.range (catLat (s + 1)) := by
  constructor
  · intro h
    rw [catFixLift_apply, Prod.ext_iff] at h
    obtain ⟨k₀, hk₀⟩ := exists_int_of_coe_eq_zero h.1
    obtain ⟨k₁, hk₁⟩ := exists_int_of_coe_eq_zero h.2
    refine ⟨![k₀, k₁], ?_⟩
    have hv : catFixVec s m = ((k₀ : ℝ), (k₁ : ℝ)) := Prod.ext hk₀.symm hk₁.symm
    have hC := catCr_catFixVec s m
    rw [hv] at hC
    have hC' := catCr_intCast (s + 1) ![k₀, k₁]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hC'
    rw [hC] at hC'
    have e0 : ((catLat (s + 1) ![k₀, k₁]) 0 : ℝ) = (m 0 : ℝ) := (congrArg Prod.fst hC').symm
    have e1 : ((catLat (s + 1) ![k₀, k₁]) 1 : ℝ) = (m 1 : ℝ) := (congrArg Prod.snd hC').symm
    funext i
    fin_cases i
    · exact_mod_cast e0
    · exact_mod_cast e1
  · rintro ⟨k, rfl⟩
    rw [catFixLift_apply]
    have hv : catFixVec s (catLat (s + 1) k) = ((k 0 : ℝ), (k 1 : ℝ)) := by
      rw [catFixVec, ← catCr_intCast, catAdjR_catCr, smul_smul,
        inv_mul_cancel₀ (catDetR_succ_ne_zero s), one_smul]
    rw [hv]
    ext <;> simp [coe_intCast_eq_zero]

/-! ### The count -/

/-- ★★★ **The number of fixed points of `cat^[t]` is `L₂ₜ − 2`** (`t ≥ 1`): the fixed-point set is
`ℤ² / (Aᵗ − I)ℤ²`, of order `|det(Aᵗ − I)| = L₂ₜ − 2`. -/
theorem card_fixedPoints_cat_iterate (s : ℕ) :
    Nat.card {p : Torus2 // cat^[s + 1] p = p} = (lucasEven (s + 1) - 2).natAbs := by
  -- the fixed points are the range of the parametrisation
  have hrange : ∀ p : Torus2, p ∈ (catFixLift s).range ↔ cat^[s + 1] p = p := by
    intro p
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact catFixLift_mem s m
    · exact catFixLift_surjective s p
  have e1 : {p : Torus2 // cat^[s + 1] p = p} ≃ (catFixLift s).range :=
    Equiv.subtypeEquivRight fun p => (hrange p).symm
  -- the range is the quotient by the kernel
  have e2 := (QuotientAddGroup.quotientKerEquivRange (catFixLift s)).toEquiv
  -- the kernel is the lattice
  have hker : (catFixLift s).ker = (LinearMap.range (catLat (s + 1))).toAddSubgroup := by
    ext m
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, catFixLift_eq_zero_iff]
  have e3 := (QuotientAddGroup.quotientAddEquivOfEq hker).toEquiv
  -- the lattice index is the determinant
  set bN : Basis (Fin 2) ℤ (LinearMap.range (catLat (s + 1))) :=
    (Pi.basisFun ℤ (Fin 2)).map (LinearEquiv.ofInjective (catLat (s + 1)) (catLat_injective s))
  have hdet := Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin 2))
    (LinearMap.range (catLat (s + 1))) bN
  have hbN : ((↑) ∘ bN : Fin 2 → Fin 2 → ℤ) = ⇑(catLat (s + 1)) ∘ ⇑(Pi.basisFun ℤ (Fin 2)) := by
    funext i
    simp [bN, Basis.map_apply, LinearEquiv.ofInjective_apply]
  rw [hbN, Basis.det_comp, Basis.det_self, mul_one, det_catLat] at hdet
  have hcard : Nat.card ((Fin 2 → ℤ) ⧸ (LinearMap.range (catLat (s + 1))).toAddSubgroup)
      = Nat.card ((Fin 2 → ℤ) ⧸ LinearMap.range (catLat (s + 1))) := rfl
  rw [Nat.card_congr e1, Nat.card_congr e2.symm, Nat.card_congr e3, hcard, ← hdet,
    show (2 - lucasEven (s + 1) : ℤ) = -(lucasEven (s + 1) - 2) by ring, Int.natAbs_neg]

/-- The count, as an integer: `L₂ₜ − 2`. -/
theorem card_fixedPoints_cat_iterate_int (s : ℕ) :
    (Nat.card {p : Torus2 // cat^[s + 1] p = p} : ℤ) = lucasEven (s + 1) - 2 := by
  rw [card_fixedPoints_cat_iterate, Int.natCast_natAbs, abs_of_nonneg]
  have := three_le_lucasEven_succ s
  omega

/-! ### The growth rate is the Lyapunov exponent -/

/-- The count in closed form: `φ²ᵗ + φ⁻²ᵗ − 2`. -/
theorem card_fixedPoints_cat_iterate_real (s : ℕ) :
    (Nat.card {p : Torus2 // cat^[s + 1] p = p} : ℝ)
      = φ ^ (2 * (s + 1)) + (φ ^ (2 * (s + 1)))⁻¹ - 2 := by
  have h := card_fixedPoints_cat_iterate_int s
  have h' : (Nat.card {p : Torus2 // cat^[s + 1] p = p} : ℝ) = ((lucasEven (s + 1) - 2 : ℤ) : ℝ) := by
    exact_mod_cast h
  rw [h']
  push_cast
  rw [lucasEven_eq]
  have hψ : ψ = -φ⁻¹ := by rw [Real.inv_goldenRatio, neg_neg]
  rw [hψ, Even.neg_pow ⟨s + 1, by ring⟩, inv_pow]

/-- ★★ **The periodic points of the cat map grow at the Lyapunov exponent**:
`(1/t) log #Fix(cat^[t]) → 2 log φ`. -/
theorem tendsto_log_card_fixedPoints_cat :
    Tendsto (fun s : ℕ => Real.log (Nat.card {p : Torus2 // cat^[s + 1] p = p}) / ((s : ℝ) + 1))
      atTop (𝓝 (2 * Real.log φ)) := by
  have hφ1 : 1 < φ := Real.one_lt_goldenRatio
  have hφ0 : 0 < φ := Real.goldenRatio_pos
  set c : ℝ := (1 - (φ ^ 2)⁻¹) ^ 2 with hc
  have hc0 : 0 < c := by
    have : (φ ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hφ1 two_ne_zero)
    positivity
  clear_value c
  -- the two-sided bound `c · φ^{2t} ≤ #Fix ≤ φ^{2t}`
  have hbound : ∀ s : ℕ, c * φ ^ (2 * (s + 1)) ≤ (Nat.card {p : Torus2 // cat^[s + 1] p = p} : ℝ)
      ∧ (Nat.card {p : Torus2 // cat^[s + 1] p = p} : ℝ) ≤ φ ^ (2 * (s + 1)) := by
    intro s
    rw [card_fixedPoints_cat_iterate_real]
    set x : ℝ := φ ^ (s + 1) with hx
    have hx1 : φ ≤ x := by
      rw [hx]
      exact le_self_pow₀ hφ1.le (by omega)
    have hx0 : 0 < x := hφ0.trans_le hx1
    have hx2 : φ ^ (2 * (s + 1)) = x ^ 2 := by rw [hx, ← pow_mul, mul_comm]
    rw [hx2]
    have hinv : (x ^ 2)⁻¹ ≤ (φ ^ 2)⁻¹ := by
      gcongr
    constructor
    · -- `(x − x⁻¹)² ≥ (x (1 − φ⁻²))²`
      have hsq : x ^ 2 + (x ^ 2)⁻¹ - 2 = (x - x⁻¹) ^ 2 := by field_simp; ring
      have hlin : x * (1 - (φ ^ 2)⁻¹) ≤ x - x⁻¹ := by
        have : x⁻¹ ≤ x * (φ ^ 2)⁻¹ := by
          rw [show x⁻¹ = x * (x ^ 2)⁻¹ by field_simp]
          exact mul_le_mul_of_nonneg_left hinv hx0.le
        linarith
      have h0 : 0 ≤ x * (1 - (φ ^ 2)⁻¹) := by
        have : (φ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hφ1.le)
        have := hx0.le
        nlinarith
      rw [hsq, hc]
      calc (1 - (φ ^ 2)⁻¹) ^ 2 * x ^ 2 = (x * (1 - (φ ^ 2)⁻¹)) ^ 2 := by ring
        _ ≤ (x - x⁻¹) ^ 2 := pow_le_pow_left₀ h0 hlin 2
    · have : 0 < (x ^ 2)⁻¹ := by positivity
      have : (x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (hφ1.le.trans hx1))
      linarith
  -- logs of the bounds
  have hlog : ∀ s : ℕ, 2 * Real.log φ + Real.log c / ((s : ℝ) + 1)
      ≤ Real.log (Nat.card {p : Torus2 // cat^[s + 1] p = p}) / ((s : ℝ) + 1)
      ∧ Real.log (Nat.card {p : Torus2 // cat^[s + 1] p = p}) / ((s : ℝ) + 1) ≤ 2 * Real.log φ := by
    intro s
    obtain ⟨hlo, hhi⟩ := hbound s
    have hpos : 0 < c * φ ^ (2 * (s + 1)) := by positivity
    have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have hlog_hi := Real.log_le_log (hpos.trans_le hlo) hhi
    have hlog_lo := Real.log_le_log hpos hlo
    rw [Real.log_mul hc0.ne' (by positivity), Real.log_pow φ (2 * (s + 1))] at hlog_lo
    rw [Real.log_pow φ (2 * (s + 1))] at hlog_hi
    push_cast at hlog_lo hlog_hi
    constructor
    · rw [le_div_iff₀ hs]
      have : 2 * Real.log φ * ((s : ℝ) + 1) + Real.log c
          = (2 * Real.log φ + Real.log c / ((s : ℝ) + 1)) * ((s : ℝ) + 1) := by
        field_simp
      linarith [this]
    · rw [div_le_iff₀ hs]
      linarith
  -- squeeze
  have hlim : Tendsto (fun s : ℕ => 2 * Real.log φ + Real.log c / ((s : ℝ) + 1)) atTop
      (𝓝 (2 * Real.log φ)) := by
    have h0 : Tendsto (fun s : ℕ => Real.log c / ((s : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun s => ?_
      simp [Function.comp]
    simpa using tendsto_const_nhds.add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
    (fun s => (hlog s).1) (fun s => (hlog s).2)

end MeasureTheory

end

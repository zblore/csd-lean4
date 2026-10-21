/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.ReturnCriterion
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Hyperbolic toral automorphisms have return growth: the criterion by the trace

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #178 (out of #19 and #177).

For an integer matrix `B ∈ SL₂(ℤ)` with `|tr B| > 2`, the toral automorphism `toral B` of `T²` has
return growth `log ρ`, `ρ = (|tr B| + √(tr B² − 4)) / 2 > 1` its spectral radius
(★★★ `hasReturnGrowth_toral`). The whole statement is read off one integer, the trace. Three facts
replace #176's Fibonacci-specific steps:

* the kernel of a toral endomorphism `toral C` with `det C ≠ 0` has exactly `|det C|` points
  (★★★ `card_ker_toral`): #176's parametrisation `m ↦ (1/det C)·adj(C)·m mod ℤ²` with the `2 × 2`
  adjugate written out, and Mathlib's `Submodule.natAbs_det_basis_change` for the lattice index;
* `det(M − 1) = det M − tr M + 1` for `2 × 2` matrices, so the fixed points of `toral Bᵗ` are
  `|2 − tr Bᵗ|` in number (★★ `card_fixedPoints_toral_pow`);
* Cayley–Hamilton `B² = (tr B)·B − (det B)·1` gives the trace recurrence
  `tr Bᵗ⁺² = tr B · tr Bᵗ⁺¹ − tr Bᵗ`, solved in closed form by `εᵗ(ρᵗ + ρ⁻ᵗ)` with `ε = ±1` the sign
  of the trace (★★ `trace_pow_eq`); `tr Bᵗ = 2` would force `ρᵗ = 1`, impossible, so every return
  set is finite and nonempty, and `(1 − ρ⁻¹)² ρᵗ ≤ #Fix ≤ 4 ρᵗ` squeezes the growth to `log ρ`.

The cat matrix is the instance `tr = 3`, `ρ = φ²`, recovering #176's `2 log φ` (`cat_eq_toral`,
`spectralRadius_catMat`).

## Honest scope

* `det B = 1` throughout; `det B = −1` (orientation-reversing automorphisms) would need
  `det(Bᵗ − 1) = (−1)ᵗ − tr Bᵗ + 1` and is not treated.
* The converse — `|tr B| ≤ 2` never has return growth — is #179.
* The sign of the trace is carried by `ε = ±1` and never split on: `|εᵗ(ρᵗ + ρ⁻ᵗ)| = ρᵗ + ρ⁻ᵗ`.

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §1.8, §3.2;
`Mathlib/Dynamics/CatMapPeriodicPoints.lean` (#176, the cat-matrix case this generalises),
`Mathlib/Dynamics/ReturnCriterion.lean` (#177, `HasReturnGrowth`); `specs/BACKLOG.md` #178, #19.
-/

@[expose] public section

open Filter Topology Function Module
open scoped goldenRatio

namespace MeasureTheory

/-! ### Toral endomorphisms -/

/-- The toral endomorphism of an integer `2 × 2` matrix. -/
noncomputable def toral (B : Matrix (Fin 2) (Fin 2) ℤ) (p : Torus2) : Torus2 :=
  (B 0 0 • p.1 + B 0 1 • p.2, B 1 0 • p.1 + B 1 1 • p.2)

theorem toral_one_apply (p : Torus2) : toral 1 p = p := by
  simp [toral]

theorem toral_mul (B C : Matrix (Fin 2) (Fin 2) ℤ) : toral (B * C) = toral B ∘ toral C := by
  funext p
  refine Prod.ext ?_ ?_ <;>
    simp only [toral, Function.comp, Matrix.mul_apply, Fin.sum_univ_two, add_zsmul, mul_zsmul,
      zsmul_add] <;> abel

theorem toral_pow (B : Matrix (Fin 2) (Fin 2) ℤ) (t : ℕ) : (toral B)^[t] = toral (B ^ t) := by
  induction t with
  | zero => funext p; simp [toral_one_apply]
  | succ k ih => rw [iterate_succ', ih, pow_succ', toral_mul]

theorem toral_sub (B C : Matrix (Fin 2) (Fin 2) ℤ) (p : Torus2) :
    toral (B - C) p = toral B p - toral C p := by
  refine Prod.ext ?_ ?_ <;> simp only [toral, Matrix.sub_apply, sub_zsmul, Prod.fst_sub,
    Prod.snd_sub] <;> abel

/-- Fixed points of `toral B` are the kernel of `toral (B − 1)`. -/
theorem toral_fixed_iff (B : Matrix (Fin 2) (Fin 2) ℤ) (p : Torus2) :
    toral B p = p ↔ toral (B - 1) p = 0 := by
  rw [toral_sub, toral_one_apply, sub_eq_zero]

/-! ### The real matrix, its adjugate, and the descent -/

/-- The matrix acting on the plane. -/
noncomputable def realMat (C : Matrix (Fin 2) (Fin 2) ℤ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((C 0 0 : ℝ) * v.1 + (C 0 1 : ℝ) * v.2, (C 1 0 : ℝ) * v.1 + (C 1 1 : ℝ) * v.2)

/-- The adjugate acting on the plane. -/
noncomputable def adjMat (C : Matrix (Fin 2) (Fin 2) ℤ) (w : ℝ × ℝ) : ℝ × ℝ :=
  ((C 1 1 : ℝ) * w.1 - (C 0 1 : ℝ) * w.2, -(C 1 0 : ℝ) * w.1 + (C 0 0 : ℝ) * w.2)

theorem det_cast (C : Matrix (Fin 2) (Fin 2) ℤ) :
    (C.det : ℝ) = (C 0 0 : ℝ) * C 1 1 - (C 0 1 : ℝ) * C 1 0 := by
  rw [Matrix.det_fin_two]; push_cast; ring

theorem adjMat_realMat (C : Matrix (Fin 2) (Fin 2) ℤ) (v : ℝ × ℝ) :
    adjMat C (realMat C v) = (C.det : ℝ) • v := by
  rw [det_cast]
  ext <;> simp only [adjMat, realMat, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem realMat_adjMat (C : Matrix (Fin 2) (Fin 2) ℤ) (w : ℝ × ℝ) :
    realMat C (adjMat C w) = (C.det : ℝ) • w := by
  rw [det_cast]
  ext <;> simp only [adjMat, realMat, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem realMat_smul (C : Matrix (Fin 2) (Fin 2) ℤ) (c : ℝ) (v : ℝ × ℝ) :
    realMat C (c • v) = c • realMat C v := by
  ext <;> simp only [realMat, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem adjMat_add (C : Matrix (Fin 2) (Fin 2) ℤ) (v w : ℝ × ℝ) :
    adjMat C (v + w) = adjMat C v + adjMat C w := by
  ext <;> simp only [adjMat, Prod.fst_add, Prod.snd_add] <;> ring

/-- On integer vectors `realMat` is `Matrix.toLin' C`. -/
theorem realMat_intCast (C : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin 2 → ℤ) :
    realMat C ((k 0 : ℝ), (k 1 : ℝ))
      = (((Matrix.toLin' C k) 0 : ℝ), ((Matrix.toLin' C k) 1 : ℝ)) := by
  rw [Matrix.toLin'_apply]
  ext <;> simp [realMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `toral B` descends from `realMat B`. -/
theorem toral_coe (B : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℝ) :
    toral B ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ)))
      = (((realMat B (x, y)).1 : AddCircle (1 : ℝ)), ((realMat B (x, y)).2 : AddCircle (1 : ℝ))) := by
  refine Prod.ext ?_ ?_ <;>
    simp only [toral, realMat, AddCircle.coe_add, ← AddCircle.coe_zsmul, zsmul_eq_mul]

/-! ### The kernel of a toral endomorphism has `|det|` points -/

/-- `toLin' C` is injective on `ℤ²` when `det C ≠ 0`: multiply by the adjugate. -/
theorem toLin'_injective_of_det_ne_zero (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det ≠ 0) :
    Injective (Matrix.toLin' C) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  have h := congrArg (fun v => C.adjugate.mulVec v) hm
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact (smul_eq_zero.1 h).resolve_left hC

/-- The real lift of the kernel point attached to `m ∈ ℤ²`: `C⁻¹ m`. -/
noncomputable def kerVec (C : Matrix (Fin 2) (Fin 2) ℤ) (m : Fin 2 → ℤ) : ℝ × ℝ :=
  ((C.det : ℝ))⁻¹ • adjMat C ((m 0 : ℝ), (m 1 : ℝ))

theorem realMat_kerVec (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det ≠ 0) (m : Fin 2 → ℤ) :
    realMat C (kerVec C m) = ((m 0 : ℝ), (m 1 : ℝ)) := by
  have hC' : (C.det : ℝ) ≠ 0 := by exact_mod_cast hC
  rw [kerVec, realMat_smul, realMat_adjMat, smul_smul, inv_mul_cancel₀ hC', one_smul]

theorem kerVec_add (C : Matrix (Fin 2) (Fin 2) ℤ) (m n : Fin 2 → ℤ) :
    kerVec C (m + n) = kerVec C m + kerVec C n := by
  simp only [kerVec, Pi.add_apply, Int.cast_add]
  rw [show (((m 0 : ℝ) + n 0, (m 1 : ℝ) + n 1) : ℝ × ℝ) = ((m 0 : ℝ), (m 1 : ℝ)) + ((n 0 : ℝ), (n 1 : ℝ))
    from rfl, adjMat_add, smul_add]

/-- `ℤ² → T²`, `m ↦ C⁻¹ m mod ℤ²`: the parametrisation of the kernel. -/
noncomputable def kerLift (C : Matrix (Fin 2) (Fin 2) ℤ) : (Fin 2 → ℤ) →+ Torus2 :=
  AddMonoidHom.mk'
    (fun m => (((kerVec C m).1 : AddCircle (1 : ℝ)), ((kerVec C m).2 : AddCircle (1 : ℝ))))
    (fun m n => by
      rw [kerVec_add]
      ext <;> simp)

theorem kerLift_apply (C : Matrix (Fin 2) (Fin 2) ℤ) (m : Fin 2 → ℤ) :
    kerLift C m = (((kerVec C m).1 : AddCircle (1 : ℝ)), ((kerVec C m).2 : AddCircle (1 : ℝ))) := rfl

theorem kerLift_mem (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det ≠ 0) (m : Fin 2 → ℤ) :
    toral C (kerLift C m) = 0 := by
  rw [kerLift_apply, toral_coe, realMat_kerVec C hC]
  ext
  · exact coe_intCast_eq_zero _
  · exact coe_intCast_eq_zero _

theorem kerLift_surjective (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det ≠ 0) (p : Torus2)
    (hp : toral C p = 0) : ∃ m : Fin 2 → ℤ, kerLift C m = p := by
  have hC' : (C.det : ℝ) ≠ 0 := by exact_mod_cast hC
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective p.1
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective p.2
  have hpxy : p = ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ))) := Prod.ext hx.symm hy.symm
  rw [hpxy, toral_coe] at hp
  obtain ⟨k₀, hk₀⟩ := exists_int_of_coe_eq_zero (congrArg Prod.fst hp)
  obtain ⟨k₁, hk₁⟩ := exists_int_of_coe_eq_zero (congrArg Prod.snd hp)
  refine ⟨![k₀, k₁], ?_⟩
  have hv : kerVec C ![k₀, k₁] = (x, y) := by
    rw [kerVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hk₀, hk₁, Prod.mk.eta, adjMat_realMat, smul_smul, inv_mul_cancel₀ hC', one_smul]
  rw [kerLift_apply, hv, hpxy]

theorem kerLift_eq_zero_iff (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det ≠ 0) (m : Fin 2 → ℤ) :
    kerLift C m = 0 ↔ m ∈ LinearMap.range (Matrix.toLin' C) := by
  have hC' : (C.det : ℝ) ≠ 0 := by exact_mod_cast hC
  constructor
  · intro h
    rw [kerLift_apply, Prod.ext_iff] at h
    obtain ⟨k₀, hk₀⟩ := exists_int_of_coe_eq_zero h.1
    obtain ⟨k₁, hk₁⟩ := exists_int_of_coe_eq_zero h.2
    refine ⟨![k₀, k₁], ?_⟩
    have hv : kerVec C m = ((k₀ : ℝ), (k₁ : ℝ)) := Prod.ext hk₀.symm hk₁.symm
    have hR := realMat_kerVec C hC m
    rw [hv] at hR
    have hR' := realMat_intCast C ![k₀, k₁]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hR'
    rw [hR] at hR'
    have e0 : ((Matrix.toLin' C ![k₀, k₁]) 0 : ℝ) = (m 0 : ℝ) := (congrArg Prod.fst hR').symm
    have e1 : ((Matrix.toLin' C ![k₀, k₁]) 1 : ℝ) = (m 1 : ℝ) := (congrArg Prod.snd hR').symm
    funext i
    fin_cases i
    · exact_mod_cast e0
    · exact_mod_cast e1
  · rintro ⟨k, rfl⟩
    rw [kerLift_apply]
    have hv : kerVec C (Matrix.toLin' C k) = ((k 0 : ℝ), (k 1 : ℝ)) := by
      rw [kerVec, ← realMat_intCast, adjMat_realMat, smul_smul, inv_mul_cancel₀ hC', one_smul]
    rw [hv]
    ext <;> simp [coe_intCast_eq_zero]

/-- ★★★ **The kernel of a toral endomorphism has `|det C|` points**: it is `ℤ² / Cℤ²`. -/
theorem card_ker_toral (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det ≠ 0) :
    Nat.card {p : Torus2 // toral C p = 0} = C.det.natAbs := by
  have hrange : ∀ p : Torus2, p ∈ (kerLift C).range ↔ toral C p = 0 := by
    intro p
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact kerLift_mem C hC m
    · exact kerLift_surjective C hC p
  have e1 : {p : Torus2 // toral C p = 0} ≃ (kerLift C).range :=
    Equiv.subtypeEquivRight fun p => (hrange p).symm
  have e2 := (QuotientAddGroup.quotientKerEquivRange (kerLift C)).toEquiv
  have hker : (kerLift C).ker = (LinearMap.range (Matrix.toLin' C)).toAddSubgroup := by
    ext m
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, kerLift_eq_zero_iff C hC]
  have e3 := (QuotientAddGroup.quotientAddEquivOfEq hker).toEquiv
  set bN : Basis (Fin 2) ℤ (LinearMap.range (Matrix.toLin' C)) :=
    (Pi.basisFun ℤ (Fin 2)).map
      (LinearEquiv.ofInjective (Matrix.toLin' C) (toLin'_injective_of_det_ne_zero C hC))
  have hdet := Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin 2))
    (LinearMap.range (Matrix.toLin' C)) bN
  have hbN : ((↑) ∘ bN : Fin 2 → Fin 2 → ℤ) = ⇑(Matrix.toLin' C) ∘ ⇑(Pi.basisFun ℤ (Fin 2)) := by
    funext i
    simp [bN, Basis.map_apply, LinearEquiv.ofInjective_apply]
  rw [hbN, Basis.det_comp, Basis.det_self, mul_one, LinearMap.det_toLin'] at hdet
  have hcard : Nat.card ((Fin 2 → ℤ) ⧸ (LinearMap.range (Matrix.toLin' C)).toAddSubgroup)
      = Nat.card ((Fin 2 → ℤ) ⧸ LinearMap.range (Matrix.toLin' C)) := rfl
  rw [Nat.card_congr e1, Nat.card_congr e2.symm, Nat.card_congr e3, hcard, ← hdet]

/-! ### Fixed points of a power -/

/-- `det(M − 1) = det M − tr M + 1` for `2 × 2` matrices. -/
theorem det_sub_one_fin_two (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (M - 1).det = M.det - M.trace + 1 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp [Matrix.sub_apply]
  ring

/-- ★★ The fixed points of `toral (Bᵗ)` are `|det(Bᵗ − 1)| = |2 − tr Bᵗ|` in number, when nonzero. -/
theorem card_fixedPoints_toral (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : (M - 1).det ≠ 0) :
    Nat.card {p : Torus2 // toral M p = p} = (M - 1).det.natAbs := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun p => toral_fixed_iff M p)]
  exact card_ker_toral (M - 1) hM

/-! ### Cayley–Hamilton and the trace recurrence -/

/-- Cayley–Hamilton for `2 × 2` integer matrices. -/
theorem cayley_hamilton_fin_two (M : Matrix (Fin 2) (Fin 2) ℤ) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta, Fin.mk_one] <;> ring

/-- The trace recurrence `tr Bᵗ⁺² = tr B · tr Bᵗ⁺¹ − tr Bᵗ` when `det B = 1`. -/
theorem trace_pow_add_two (B : Matrix (Fin 2) (Fin 2) ℤ) (hdet : B.det = 1) (t : ℕ) :
    (B ^ (t + 2)).trace = B.trace * (B ^ (t + 1)).trace - (B ^ t).trace := by
  rw [pow_add, cayley_hamilton_fin_two, hdet, one_smul, Matrix.mul_sub, Matrix.mul_smul, mul_one,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, ← pow_succ]

/-! ### The spectral radius and the closed form of the trace -/

/-- The spectral radius of a hyperbolic element of `SL₂(ℤ)`: `(|tr B| + √(tr B² − 4)) / 2`. -/
noncomputable def spectralRadius (B : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  (|(B.trace : ℝ)| + Real.sqrt ((B.trace : ℝ) ^ 2 - 4)) / 2

section Hyperbolic

variable (B : Matrix (Fin 2) (Fin 2) ℤ)

theorem one_lt_spectralRadius (hτ : 2 < |(B.trace : ℝ)|) : 1 < spectralRadius B := by
  have h4 : 0 < (B.trace : ℝ) ^ 2 - 4 := by
    have : (2 : ℝ) ^ 2 < |(B.trace : ℝ)| ^ 2 := pow_lt_pow_left₀ hτ (by norm_num) two_ne_zero
    rw [sq_abs] at this
    linarith
  have := Real.sqrt_pos.2 h4
  unfold spectralRadius
  linarith

/-- `ρ · ρ' = 1` with `ρ' = (|tr B| − √(tr B² − 4)) / 2`, so `ρ⁻¹ = ρ'` and `ρ + ρ⁻¹ = |tr B|`. -/
theorem spectralRadius_add_inv (hτ : 2 < |(B.trace : ℝ)|) :
    spectralRadius B + (spectralRadius B)⁻¹ = |(B.trace : ℝ)| := by
  have h4 : 0 ≤ (B.trace : ℝ) ^ 2 - 4 := by
    have : (2 : ℝ) ^ 2 < |(B.trace : ℝ)| ^ 2 := pow_lt_pow_left₀ hτ (by norm_num) two_ne_zero
    rw [sq_abs] at this
    linarith
  have hρ : spectralRadius B ≠ 0 := (zero_lt_one.trans (one_lt_spectralRadius B hτ)).ne'
  have hprod : spectralRadius B * ((|(B.trace : ℝ)| - Real.sqrt ((B.trace : ℝ) ^ 2 - 4)) / 2) = 1 := by
    unfold spectralRadius
    have hs := Real.sq_sqrt h4
    have ha := sq_abs (B.trace : ℝ)
    nlinarith [hs, ha]
  have hinv : (spectralRadius B)⁻¹ = (|(B.trace : ℝ)| - Real.sqrt ((B.trace : ℝ) ^ 2 - 4)) / 2 :=
    inv_eq_of_mul_eq_one_right hprod
  rw [hinv]
  unfold spectralRadius
  ring

/-- The sign of the trace. -/
noncomputable def traceSign (B : Matrix (Fin 2) (Fin 2) ℤ) : ℝ := if 0 ≤ (B.trace : ℝ) then 1 else -1

theorem traceSign_sq : traceSign B ^ 2 = 1 := by
  unfold traceSign
  split_ifs <;> norm_num

theorem traceSign_mul_abs : traceSign B * |(B.trace : ℝ)| = (B.trace : ℝ) := by
  unfold traceSign
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h), neg_neg]

theorem abs_traceSign_pow (t : ℕ) : |traceSign B ^ t| = 1 := by
  rw [abs_pow]
  unfold traceSign
  split_ifs <;> simp

/-- ★★ **The closed form of the trace**: `tr Bᵗ = εᵗ (ρᵗ + ρ⁻ᵗ)`. -/
theorem trace_pow_eq (hτ : 2 < |(B.trace : ℝ)|) (hdet : B.det = 1) (t : ℕ) :
    ((B ^ t).trace : ℝ) = traceSign B ^ t * (spectralRadius B ^ t + (spectralRadius B)⁻¹ ^ t) := by
  set ρ := spectralRadius B with hρ
  set σ := ρ⁻¹ with hσ
  set ε := traceSign B with hε
  have hρσ : ρ * σ = 1 := mul_inv_cancel₀ (zero_lt_one.trans (one_lt_spectralRadius B hτ)).ne'
  have hsum : ρ + σ = |(B.trace : ℝ)| := spectralRadius_add_inv B hτ
  have hε2 : ε ^ 2 = 1 := traceSign_sq B
  have hεabs : ε * |(B.trace : ℝ)| = (B.trace : ℝ) := traceSign_mul_abs B
  -- two-step induction
  have key : ∀ t : ℕ, ((B ^ t).trace : ℝ) = ε ^ t * (ρ ^ t + σ ^ t)
      ∧ ((B ^ (t + 1)).trace : ℝ) = ε ^ (t + 1) * (ρ ^ (t + 1) + σ ^ (t + 1)) := by
    intro t
    induction t with
    | zero =>
        constructor
        · simp [Matrix.trace_one]
          norm_num
        · rw [pow_one, pow_one, pow_one, pow_one, hsum, hεabs]
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have hrec := trace_pow_add_two B hdet k
        rw [show k + 1 + 1 = k + 2 by ring]
        have hrecR : ((B ^ (k + 2)).trace : ℝ) = (B.trace : ℝ) * ((B ^ (k + 1)).trace : ℝ)
            - ((B ^ k).trace : ℝ) := by exact_mod_cast hrec
        rw [hrecR, ih.1, ih.2, ← hεabs, ← hsum]
        linear_combination (ε ^ k * (ρ ^ k + σ ^ k) * ε ^ 2) * hρσ + (ε ^ k * (ρ ^ k + σ ^ k)) * hε2
  exact (key t).1


/-! ### Every return set is finite and nonempty -/

/-- `det(Bᵗ − 1) = 2 − tr Bᵗ` when `det B = 1`. -/
theorem det_pow_sub_one (hdet : B.det = 1) (t : ℕ) : (B ^ t - 1).det = 2 - (B ^ t).trace := by
  rw [det_sub_one_fin_two, Matrix.det_pow, hdet, one_pow]
  ring

/-- `tr Bᵗ ≠ 2` for `t ≥ 1`: it would force `ρᵗ = 1`. -/
theorem trace_pow_ne_two (hτ : 2 < |(B.trace : ℝ)|) (hdet : B.det = 1) (s : ℕ) :
    (B ^ (s + 1)).trace ≠ 2 := by
  intro h
  have hR : ((B ^ (s + 1)).trace : ℝ) = 2 := by exact_mod_cast h
  rw [trace_pow_eq B hτ hdet] at hR
  have hρ1 : 1 < spectralRadius B := one_lt_spectralRadius B hτ
  have hx : 1 < spectralRadius B ^ (s + 1) := one_lt_pow₀ hρ1 (by omega)
  have hx0 : 0 < spectralRadius B ^ (s + 1) := zero_lt_one.trans hx
  have habs := congrArg abs hR
  rw [abs_mul, abs_traceSign_pow, one_mul, abs_of_pos (by positivity), abs_two, inv_pow] at habs
  have hsq : (spectralRadius B ^ (s + 1) - 1) ^ 2
      = spectralRadius B ^ (s + 1)
        * (spectralRadius B ^ (s + 1) + (spectralRadius B ^ (s + 1))⁻¹ - 2) := by
    field_simp
    ring
  rw [habs, sub_self, mul_zero] at hsq
  have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hsq
  linarith

theorem det_pow_sub_one_ne_zero (hτ : 2 < |(B.trace : ℝ)|) (hdet : B.det = 1) (s : ℕ) :
    (B ^ (s + 1) - 1).det ≠ 0 := by
  rw [det_pow_sub_one B hdet]
  exact sub_ne_zero_of_ne (trace_pow_ne_two B hτ hdet s).symm

/-- ★★ **The fixed points of `toral Bᵗ` are `|2 − tr Bᵗ|` in number** (`t ≥ 1`). -/
theorem card_fixedPoints_toral_pow (hτ : 2 < |(B.trace : ℝ)|) (hdet : B.det = 1) (s : ℕ) :
    Nat.card {p : Torus2 // toral (B ^ (s + 1)) p = p} = (2 - (B ^ (s + 1)).trace).natAbs := by
  rw [card_fixedPoints_toral _ (det_pow_sub_one_ne_zero B hτ hdet s), det_pow_sub_one B hdet]

/-- The count in closed form: `|2 − εᵗ (ρᵗ + ρ⁻ᵗ)|`. -/
theorem card_fixedPoints_toral_pow_real (hτ : 2 < |(B.trace : ℝ)|) (hdet : B.det = 1) (s : ℕ) :
    (Nat.card {p : Torus2 // toral (B ^ (s + 1)) p = p} : ℝ)
      = |2 - traceSign B ^ (s + 1)
          * (spectralRadius B ^ (s + 1) + (spectralRadius B)⁻¹ ^ (s + 1))| := by
  rw [card_fixedPoints_toral_pow B hτ hdet, Nat.cast_natAbs]
  push_cast
  rw [trace_pow_eq B hτ hdet]

/-! ### The return growth is `log ρ` -/

/-- ★★★ **A hyperbolic toral automorphism has return growth `log ρ`**, `ρ` its spectral radius. -/
theorem hasReturnGrowth_toral (hτ : 2 < |(B.trace : ℝ)|) (hdet : B.det = 1) :
    HasReturnGrowth (toral B) (Real.log (spectralRadius B)) where
  finite t := by
    rw [toral_pow]
    have h : Nat.card {p : Torus2 // toral (B ^ (t + 1)) p = p} ≠ 0 := by
      rw [card_fixedPoints_toral_pow B hτ hdet]
      exact Int.natAbs_ne_zero.2 (sub_ne_zero_of_ne (trace_pow_ne_two B hτ hdet t).symm)
    exact Nat.finite_of_card_ne_zero h
  nonempty t := by
    rw [toral_pow]
    have h : Nat.card {p : Torus2 // toral (B ^ (t + 1)) p = p} ≠ 0 := by
      rw [card_fixedPoints_toral_pow B hτ hdet]
      exact Int.natAbs_ne_zero.2 (sub_ne_zero_of_ne (trace_pow_ne_two B hτ hdet t).symm)
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h Nat.card_of_isEmpty
  tendsto := by
    set ρ := spectralRadius B with hρdef
    have hρ1 : 1 < ρ := one_lt_spectralRadius B hτ
    have hρ0 : 0 < ρ := zero_lt_one.trans hρ1
    have hσ1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ1
    have hσ0 : 0 < ρ⁻¹ := inv_pos.2 hρ0
    set c : ℝ := (1 - ρ⁻¹) ^ 2 with hc
    have hc0 : 0 < c := by positivity
    clear_value c
    -- the count in closed form
    have hcount : ∀ s : ℕ, (returnCount (toral B) (s + 1) : ℝ)
        = |2 - traceSign B ^ (s + 1) * (ρ ^ (s + 1) + ρ⁻¹ ^ (s + 1))| := by
      intro s
      rw [returnCount, toral_pow, card_fixedPoints_toral_pow_real B hτ hdet]
    -- the two-sided bound `c ρᵗ ≤ #Fix ≤ 4 ρᵗ`
    have hbound : ∀ s : ℕ, c * ρ ^ (s + 1) ≤ (returnCount (toral B) (s + 1) : ℝ)
        ∧ (returnCount (toral B) (s + 1) : ℝ) ≤ 4 * ρ ^ (s + 1) := by
      intro s
      rw [hcount s]
      set x : ℝ := ρ ^ (s + 1) with hx
      have hx1 : ρ ≤ x := le_self_pow₀ hρ1.le (by omega)
      have hx0 : 0 < x := hρ0.trans_le hx1
      have hxinv : ρ⁻¹ ^ (s + 1) = x⁻¹ := by rw [hx, inv_pow]
      rw [hxinv]
      have hε : |traceSign B ^ (s + 1)| = 1 := abs_traceSign_pow B (s + 1)
      have hxpos : 0 < x + x⁻¹ := by positivity
      -- `|εᵗ(x + x⁻¹)| = x + x⁻¹`
      have hprod : |traceSign B ^ (s + 1) * (x + x⁻¹)| = x + x⁻¹ := by
        rw [abs_mul, hε, one_mul, abs_of_pos hxpos]
      have hinv_le : x⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ0 hx1
      have hinv_le1 : x⁻¹ ≤ 1 := (inv_anti₀ hρ0 hx1).trans hσ1.le
      constructor
      · -- lower bound: `|2 − a| ≥ |a| − 2 = x + x⁻¹ − 2 = x(1 − x⁻¹)² ≥ x(1 − ρ⁻¹)²`
        have h1 : x + x⁻¹ - 2 ≤ |2 - traceSign B ^ (s + 1) * (x + x⁻¹)| := by
          have := abs_sub_abs_le_abs_sub (traceSign B ^ (s + 1) * (x + x⁻¹)) 2
          rw [hprod, abs_two] at this
          rw [abs_sub_comm] at this
          linarith
        have h2 : x * (1 - ρ⁻¹) ^ 2 ≤ x + x⁻¹ - 2 := by
          have hsq : x + x⁻¹ - 2 = x * (1 - x⁻¹) ^ 2 := by field_simp; ring
          rw [hsq]
          have h0 : 0 ≤ 1 - x⁻¹ := by linarith
          have h3 : 1 - ρ⁻¹ ≤ 1 - x⁻¹ := by linarith
          have h4 : 0 ≤ 1 - ρ⁻¹ := by linarith
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 h3 2) hx0.le
        rw [hc]
        linarith
      · -- upper bound: `|2 − a| ≤ 2 + x + x⁻¹ ≤ 4x`
        have h1 : |2 - traceSign B ^ (s + 1) * (x + x⁻¹)| ≤ 2 + (x + x⁻¹) := by
          have := abs_sub (2 : ℝ) (traceSign B ^ (s + 1) * (x + x⁻¹))
          rw [hprod, abs_two] at this
          exact this
        have hx1' : 1 ≤ x := hρ1.le.trans hx1
        linarith
    -- logs of the bounds
    have hlog : ∀ s : ℕ, Real.log ρ + Real.log c / ((s : ℝ) + 1)
        ≤ Real.log (returnCount (toral B) (s + 1)) / ((s : ℝ) + 1)
        ∧ Real.log (returnCount (toral B) (s + 1)) / ((s : ℝ) + 1)
          ≤ Real.log ρ + Real.log 4 / ((s : ℝ) + 1) := by
      intro s
      obtain ⟨hlo, hhi⟩ := hbound s
      have hpos : 0 < c * ρ ^ (s + 1) := by positivity
      have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
      have hlog_hi := Real.log_le_log (hpos.trans_le hlo) hhi
      have hlog_lo := Real.log_le_log hpos hlo
      rw [Real.log_mul hc0.ne' (by positivity), Real.log_pow ρ (s + 1)] at hlog_lo
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow ρ (s + 1)] at hlog_hi
      push_cast at hlog_lo hlog_hi
      constructor
      · rw [le_div_iff₀ hs]
        have : (Real.log ρ + Real.log c / ((s : ℝ) + 1)) * ((s : ℝ) + 1)
            = ((s : ℝ) + 1) * Real.log ρ + Real.log c := by
          field_simp
        linarith [this]
      · rw [div_le_iff₀ hs]
        have : (Real.log ρ + Real.log 4 / ((s : ℝ) + 1)) * ((s : ℝ) + 1)
            = ((s : ℝ) + 1) * Real.log ρ + Real.log 4 := by
          field_simp
        linarith [this]
    -- squeeze
    have hlimL : Tendsto (fun s : ℕ => Real.log ρ + Real.log c / ((s : ℝ) + 1)) atTop
        (𝓝 (Real.log ρ)) := by
      have h0 : Tendsto (fun s : ℕ => Real.log c / ((s : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).comp (tendsto_add_atTop_nat 1)
        refine this.congr fun s => ?_
        simp [Function.comp]
      simpa using tendsto_const_nhds.add h0
    have hlimU : Tendsto (fun s : ℕ => Real.log ρ + Real.log 4 / ((s : ℝ) + 1)) atTop
        (𝓝 (Real.log ρ)) := by
      have h0 : Tendsto (fun s : ℕ => Real.log 4 / ((s : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 4)).comp (tendsto_add_atTop_nat 1)
        refine this.congr fun s => ?_
        simp [Function.comp]
      simpa using tendsto_const_nhds.add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlimL hlimU
      (fun s => (hlog s).1) (fun s => (hlog s).2)

/-! ### The cat map as the instance `tr = 3` -/

theorem cat_eq_toral : cat = toral !![2, 1; 1, 1] := by
  funext p
  simp [cat, toral]

theorem trace_catMat : (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ).trace = 3 := by
  rw [Matrix.trace_fin_two]
  simp

theorem det_catMat : (!![2, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [Matrix.det_fin_two]
  simp

/-- The spectral radius of the cat matrix is `φ²`. -/
theorem spectralRadius_catMat : spectralRadius !![2, 1; 1, 1] = φ ^ 2 := by
  rw [spectralRadius, trace_catMat, Real.goldenRatio_sq]
  push_cast
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3), show ((3 : ℝ) ^ 2 - 4) = 5 by norm_num]
  unfold Real.goldenRatio
  ring

/-- #176's exponent recovered: `log φ² = 2 log φ`. -/
theorem log_spectralRadius_catMat : Real.log (spectralRadius !![2, 1; 1, 1]) = 2 * Real.log φ := by
  rw [spectralRadius_catMat, Real.log_pow]
  push_cast
  ring

/-- The cat map has return growth `log φ²`, now as an instance of the general theorem. -/
theorem cat_hasReturnGrowth' : HasReturnGrowth cat (Real.log (spectralRadius !![2, 1; 1, 1])) := by
  rw [cat_eq_toral]
  refine hasReturnGrowth_toral _ ?_ det_catMat
  rw [trace_catMat]
  norm_num

end Hyperbolic

end MeasureTheory

end

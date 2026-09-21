/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.Complex.Basic

/-!
# The Jordan–von Neumann reconstruction of a Hermitian form from its quadratic form

**Category:** 1-Mathlib (CSD-free; staged for upstream). The engine behind both Gleason-type
theorems of this repository: Busch's effect version (`LF2/EffectGleason.lean`, where it was first
written) and the projection version (`Gleason/ProjectionPackage.lean`, `Gleason/Descent.lean`).

A function `q : ℂᴺ → ℝ` that scales like `q (c • v) = ‖c‖² q v`, satisfies the parallelogram
law `q (u + v) + q (u − v) = 2 q u + 2 q v`, and is squeezed between `0` and `‖·‖²` is the
quadratic form of a unique Hermitian matrix:

* `polar q u v = q (u + v) − q (u − v)` is bi-additive (`IsQuadraticLike.polar_add_left`, the
  Jordan–von Neumann halving identity) and `ℝ`-bihomogeneous (`IsQuadraticLike.polar_smul_real`),
  the upgrade from `ℚ` to `ℝ` coming from `additive_bounded_linear` (Cauchy's equation with a
  local bound) instead of continuity, which is not assumed;
* `sesq q u v = ¼ polar q u v − (i/4) polar q u (i • v)` is sesquilinear
  (`IsQuadraticLike.sesq_add_right`, `sesq_smul_right`, `sesq_conj_symm`) with
  `sesq q v v = q v` (`IsQuadraticLike.sesq_self`);
* `polarMatrix q` is its matrix on the standard basis: Hermitian
  (`IsQuadraticLike.polarMatrix_isHermitian`) with
  ★ `IsQuadraticLike.eq_dotProduct : q v = star v ⬝ᵥ polarMatrix q *ᵥ v`.

Also here, the two matrix facts every descent argument needs: a complex matrix is determined by
its quadratic form (`matrix_eq_zero_of_quadForm_zero`) and the trace of a product of Hermitian
matrices is real (`trace_mul_isHermitian_real`), with `trace_mul_vecMulVec` turning the trace
against a rank-one projector into the quadratic form.

## Source

Jordan–von Neumann 1935 (the parallelogram characterisation); Busch 2003,
`quant-ph/9909073` (where the bounded-additive substitute for continuity is used).
-/

@[expose] public section

open Matrix
open scoped ComplexConjugate

namespace Gleason

variable {N : ℕ}

/-! ### Cauchy's functional equation with a local bound -/

/-- **Cauchy's functional equation with a local bound.** An additive `g : ℝ → ℝ` that is bounded
on `[-1,1]` is linear: `g t = t · g 1`.

No continuity is assumed. The proof is the classical squeeze on `h y = g y − y · g 1`: `h` is
additive, kills every integer (`h m = m · h 1 = 0`), and is bounded on `[-1,1]`; for any `x` and
any `n ≥ 1`, `n · h x = h (n x − ⌊n x⌋)` lands in that bounded window, so
`|h x| ≤ (M + |g 1|)/n → 0`. -/
theorem additive_bounded_linear (g : ℝ → ℝ) (hadd : ∀ s t : ℝ, g (s + t) = g s + g t)
    {M : ℝ} (hM : ∀ t : ℝ, |t| ≤ 1 → |g t| ≤ M) (x : ℝ) : g x = x * g 1 := by
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, ∀ y, h y = g y - y * g 1 := ⟨_, fun _ => rfl⟩
  have hadd' : ∀ s t : ℝ, h (s + t) = h s + h t := by
    intro s t; rw [hh, hh, hh, hadd s t]; ring
  have hzero : h 0 = 0 := by
    have h0 := hadd' 0 0; rw [add_zero] at h0; linarith
  have hone : h 1 = 0 := by rw [hh]; ring
  have hnat : ∀ (n : ℕ) (y : ℝ), h ((n : ℝ) * y) = (n : ℝ) * h y := by
    intro n
    induction n with
    | zero => intro y; simp [hzero]
    | succ k ih =>
      intro y
      have hstep : ((k + 1 : ℕ) : ℝ) * y = (k : ℝ) * y + y := by push_cast; ring
      rw [hstep, hadd', ih]; push_cast; ring
  have hneg : ∀ y : ℝ, h (-y) = - h y := by
    intro y
    have hy := hadd' y (-y)
    rw [add_neg_cancel, hzero] at hy
    linarith
  have hnatz : ∀ n : ℕ, h ((n : ℝ)) = 0 := by
    intro n
    have hn := hnat n 1
    rw [mul_one, hone, mul_zero] at hn
    exact hn
  have hint : ∀ m : ℤ, h ((m : ℝ)) = 0 := by
    intro m
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = n ∨ m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    rcases hn with hn | hn
    · subst hn; exact_mod_cast hnatz n
    · subst hn
      have hcast : (((-(n : ℤ)) : ℤ) : ℝ) = -((n : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, hneg, hnatz n, neg_zero]
  have hM' : ∀ y : ℝ, |y| ≤ 1 → |h y| ≤ M + |g 1| := by
    intro y hy
    have h1 : |h y| ≤ |g y| + |y * g 1| := by
      rw [hh]
      have hg1 := le_abs_self (g y)
      have hg2 := neg_abs_le (g y)
      have hy1 := le_abs_self (y * g 1)
      have hy2 := neg_abs_le (y * g 1)
      rw [abs_le]
      constructor <;> linarith
    have h2 : |y * g 1| ≤ |g 1| := by
      rw [abs_mul]
      nlinarith [abs_nonneg (g 1), abs_nonneg y]
    linarith [hM y hy]
  have hsq : ∀ n : ℕ, 0 < n → |h x| ≤ (M + |g 1|) / n := by
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    have hr0 : 0 ≤ (n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) := sub_nonneg.mpr (Int.floor_le _)
    have hr1 : (n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) < 1 := by
      have hlt := Int.lt_floor_add_one ((n : ℝ) * x)
      linarith
    have hsplit : h ((n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ)) = (n : ℝ) * h x := by
      have hs := hadd' ((n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ)) (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ))
      have heq : (n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) + ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ)
          = (n : ℝ) * x := by ring
      rw [heq, hint, add_zero] at hs
      rw [← hs, hnat n x]
    have habs : |h ((n : ℝ) * x - ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ))| ≤ M + |g 1| :=
      hM' _ (by rw [abs_of_nonneg hr0]; linarith)
    rw [hsplit, abs_mul, abs_of_pos hn0] at habs
    rw [le_div_iff₀ hn0]
    linarith
  have hMnn : (0:ℝ) ≤ M := le_trans (abs_nonneg (g 0)) (hM 0 (by norm_num))
  have hx0 : h x = 0 := by
    by_contra hne
    have hpos : 0 < |h x| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt ((M + |g 1|) / |h x|)
    have hq : (0:ℝ) ≤ (M + |g 1|) / |h x| := by positivity
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exfalso; rw [Nat.cast_zero] at hn; linarith
      · exact hp
    have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
    have hb := hsq n hnpos
    rw [div_lt_iff₀ hpos] at hn
    rw [le_div_iff₀ hn0] at hb
    nlinarith
  rw [hh] at hx0
  linarith

/-! ### Quadratic-like functions -/

/-- **A quadratic-like function** on `ℂᴺ`: degree-2 homogeneous under complex scaling, obeying
the parallelogram law, and squeezed between `0` and `‖·‖²`. The last two conditions replace
continuity in the Jordan–von Neumann argument (`polar_smul_real`). -/
structure IsQuadraticLike (q : EuclideanSpace ℂ (Fin N) → ℝ) : Prop where
  /-- `q (c • v) = ‖c‖² q v`. -/
  smul : ∀ (c : ℂ) (v : EuclideanSpace ℂ (Fin N)), q (c • v) = ‖c‖ ^ 2 * q v
  /-- The parallelogram law. -/
  parallelogram : ∀ u v : EuclideanSpace ℂ (Fin N), q (u + v) + q (u - v) = 2 * q u + 2 * q v
  /-- `0 ≤ q`. -/
  nonneg : ∀ v : EuclideanSpace ℂ (Fin N), 0 ≤ q v
  /-- `q v ≤ ‖v‖²`. -/
  le_normSq : ∀ v : EuclideanSpace ℂ (Fin N), q v ≤ ‖v‖ ^ 2

/-- **The polarisation difference** `polar q u v = q (u + v) − q (u − v)` — four times the real
part of the sesquilinear form being reconstructed. -/
def polar (q : EuclideanSpace ℂ (Fin N) → ℝ) (u v : EuclideanSpace ℂ (Fin N)) : ℝ :=
  q (u + v) - q (u - v)

/-- **The polarised sesquilinear form** `sesq q u v = ¼ polar q u v − (i/4) polar q u (i • v)`,
the complex polarisation of `q`. -/
noncomputable def sesq (q : EuclideanSpace ℂ (Fin N) → ℝ) (u v : EuclideanSpace ℂ (Fin N)) : ℂ :=
  ((polar q u v : ℝ) : ℂ) / 4 - Complex.I * ((polar q u (Complex.I • v) : ℝ) : ℂ) / 4

/-- **The matrix of the polarised form** on the standard basis, `polarMatrix q j k =
sesq q eⱼ eₖ`. -/
noncomputable def polarMatrix (q : EuclideanSpace ℂ (Fin N) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => sesq q (EuclideanSpace.single j (1:ℂ)) (EuclideanSpace.single k (1:ℂ))

namespace IsQuadraticLike

variable {q : EuclideanSpace ℂ (Fin N) → ℝ} (hq : IsQuadraticLike q)
include hq

/-- `q 0 = 0`. -/
theorem zero : q 0 = 0 := by
  have h := hq.smul 0 0
  simpa using h

/-- `q (−v) = q v`. -/
theorem neg (v : EuclideanSpace ℂ (Fin N)) : q (-v) = q v := by
  have h := hq.smul (-1) v
  simpa using h

/-- `polar` is symmetric: `q (v − u) = q (−(u − v)) = q (u − v)`. -/
theorem polar_symm (u v : EuclideanSpace ℂ (Fin N)) : polar q u v = polar q v u := by
  have h : v - u = -(u - v) := by abel
  rw [polar, polar, h, hq.neg, add_comm]

/-- `polar q 0 v = q v − q (−v) = 0`. -/
theorem polar_zero_left (v : EuclideanSpace ℂ (Fin N)) : polar q 0 v = 0 := by
  rw [polar, zero_add, zero_sub, hq.neg, sub_self]

omit hq in
/-- `polar q u (−v) = − polar q u v`. -/
theorem polar_neg_right (u v : EuclideanSpace ℂ (Fin N)) :
    polar q u (-v) = - polar q u v := by
  rw [polar, polar, ← sub_eq_add_neg, sub_neg_eq_add]; ring

/-- **The halving identity (Jordan–von Neumann core).** `polar u v + polar w v =
2 polar ((u+w)/2) v`: apply the parallelogram law at `(a ± v, b)` with `a = (u+w)/2`,
`b = (u−w)/2` and subtract the two instances — the `q b` terms cancel. -/
theorem polar_add_half (u w v : EuclideanSpace ℂ (Fin N)) :
    polar q u v + polar q w v = 2 * polar q (((2:ℂ)⁻¹) • (u + w)) v := by
  have h2 : (2:ℂ) ≠ 0 := by norm_num
  set a : EuclideanSpace ℂ (Fin N) := ((2:ℂ)⁻¹) • (u + w) with ha
  set b : EuclideanSpace ℂ (Fin N) := ((2:ℂ)⁻¹) • (u - w) with hb
  have hab1 : a + b = u := by
    rw [ha, hb, ← smul_add, show (u + w) + (u - w) = (2:ℂ) • u from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hab2 : a - b = w := by
    rw [ha, hb, ← smul_sub, show (u + w) - (u - w) = (2:ℂ) • w from by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ h2, one_smul]
  have par1 := hq.parallelogram (a + v) b
  have par2 := hq.parallelogram (a - v) b
  rw [show a + v + b = u + v from by rw [← hab1]; abel,
    show a + v - b = w + v from by rw [← hab2]; abel] at par1
  rw [show a - v + b = u - v from by rw [← hab1]; abel,
    show a - v - b = w - v from by rw [← hab2]; abel] at par2
  simp only [polar]
  linarith

/-- **Additivity of `polar` in the first slot.** The halving identity at `(u, w)` and at
`(u + w, 0)` share a right-hand side. -/
theorem polar_add_left (u w v : EuclideanSpace ℂ (Fin N)) :
    polar q (u + w) v = polar q u v + polar q w v := by
  have h1 := hq.polar_add_half u w v
  have h2 := hq.polar_add_half (u + w) 0 v
  simp only [hq.polar_zero_left, add_zero] at h2
  linarith

/-- **Real homogeneity of `polar` in the first slot.** Additivity alone gives `ℚ`-homogeneity;
the upgrade to `ℝ` is `additive_bounded_linear`, whose local bound is `0 ≤ q ≤ ‖·‖²`. -/
theorem polar_smul_real (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    polar q (((t : ℝ) : ℂ) • u) v = t * polar q u v := by
  have hadd : ∀ s r : ℝ, polar q ((((s + r : ℝ)) : ℂ) • u) v
      = polar q (((s : ℝ) : ℂ) • u) v + polar q (((r : ℝ) : ℂ) • u) v := by
    intro s r
    rw [show (((s + r : ℝ)) : ℂ) • u = ((s : ℝ) : ℂ) • u + ((r : ℝ) : ℂ) • u from by
      push_cast; rw [add_smul], hq.polar_add_left]
  have hbound : ∀ s : ℝ, |s| ≤ 1 → |polar q (((s : ℝ) : ℂ) • u) v| ≤ (‖u‖ + ‖v‖) ^ 2 := by
    intro s hs
    have hsn : ‖((s : ℝ) : ℂ) • u‖ ≤ ‖u‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [norm_nonneg u, abs_nonneg s]
    have hp : ‖((s:ℝ):ℂ) • u + v‖ ≤ ‖u‖ + ‖v‖ := le_trans (norm_add_le _ _) (by linarith)
    have hm : ‖((s:ℝ):ℂ) • u - v‖ ≤ ‖u‖ + ‖v‖ := le_trans (norm_sub_le _ _) (by linarith)
    have h1 := hq.nonneg (((s:ℝ):ℂ) • u + v)
    have h2 := hq.nonneg (((s:ℝ):ℂ) • u - v)
    have h3 := hq.le_normSq (((s:ℝ):ℂ) • u + v)
    have h4 := hq.le_normSq (((s:ℝ):ℂ) • u - v)
    rw [abs_le, polar]
    constructor
    · nlinarith [norm_nonneg (((s:ℝ):ℂ) • u - v), norm_nonneg u, norm_nonneg v]
    · nlinarith [norm_nonneg (((s:ℝ):ℂ) • u + v), norm_nonneg u, norm_nonneg v]
  have hlin := additive_bounded_linear (fun s : ℝ => polar q (((s : ℝ) : ℂ) • u) v) hadd
    hbound t
  simpa using hlin

omit hq in
/-- `sesq q u 0 = 0`. -/
theorem sesq_zero_right (u : EuclideanSpace ℂ (Fin N)) : sesq q u 0 = 0 := by
  simp [sesq, polar]

/-- Additivity of `polar` in the second slot (by symmetry). -/
theorem polar_add_right (u v w : EuclideanSpace ℂ (Fin N)) :
    polar q u (v + w) = polar q u v + polar q u w := by
  rw [hq.polar_symm u (v + w), hq.polar_add_left, hq.polar_symm v u, hq.polar_symm w u]

/-- Real homogeneity of `polar` in the second slot (by symmetry). -/
theorem polar_smul_real_right (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    polar q u (((t : ℝ) : ℂ) • v) = t * polar q u v := by
  rw [hq.polar_symm u (((t : ℝ) : ℂ) • v), hq.polar_smul_real, hq.polar_symm v u]

/-- **Additivity of `sesq` in the second slot.** -/
theorem sesq_add_right (u v w : EuclideanSpace ℂ (Fin N)) :
    sesq q u (v + w) = sesq q u v + sesq q u w := by
  simp only [sesq, smul_add, hq.polar_add_right]
  push_cast
  ring

/-- **Real homogeneity of `sesq` in the second slot.** -/
theorem sesq_smul_real_right (t : ℝ) (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q u (((t : ℝ) : ℂ) • v) = (t : ℂ) * sesq q u v := by
  have hcomm : Complex.I • (((t : ℝ) : ℂ) • v) = ((t : ℝ) : ℂ) • (Complex.I • v) :=
    smul_comm _ _ _
  simp only [sesq, hcomm, hq.polar_smul_real_right]
  push_cast
  ring

omit hq in
/-- **`sesq q u (i • v) = i · sesq q u v`** — pure algebra of the polarisation formula
(`i·(i·v) = −v`), no additivity needed. -/
theorem sesq_smul_I_right (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q u (Complex.I • v) = Complex.I * sesq q u v := by
  have hII : Complex.I • (Complex.I • v) = -v := by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  simp only [sesq, hII, polar_neg_right]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Complex homogeneity in the second slot:** `sesq q u (c • v) = c · sesq q u v`. Split
`c = Re c + i · Im c`. -/
theorem sesq_smul_right (c : ℂ) (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q u (c • v) = c * sesq q u v := by
  have hdecomp : c • v = ((c.re : ℝ) : ℂ) • v + ((c.im : ℝ) : ℂ) • (Complex.I • v) := by
    rw [smul_smul, ← add_smul]
    congr 1
    exact (Complex.re_add_im c).symm
  rw [hdecomp, hq.sesq_add_right, hq.sesq_smul_real_right, hq.sesq_smul_real_right,
    sesq_smul_I_right]
  have hc : ((c.re : ℝ) : ℂ) + ((c.im : ℝ) : ℂ) * Complex.I = c := Complex.re_add_im c
  linear_combination sesq q u v * hc

/-- **Conjugate symmetry:** `sesq q v u = conj (sesq q u v)`. The real part is symmetric
(`polar_symm`); the imaginary part flips because `q (v ± i·u) = q (u ∓ i·v)` (multiply by the
unit phase `∓i` and use `smul`). With `sesq_smul_right` this makes `sesq` conjugate-linear in
its *first* slot. -/
theorem sesq_conj_symm (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q v u = (starRingEnd ℂ) (sesq q u v) := by
  have h1 : q (v + Complex.I • u) = q (u - Complex.I • v) := by
    have hI : Complex.I • (u - Complex.I • v) = v + Complex.I • u := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add, add_comm]
    rw [← hI, hq.smul]
    simp
  have h2 : q (v - Complex.I • u) = q (u + Complex.I • v) := by
    have hI : (-Complex.I) • (u + Complex.I • v) = v - Complex.I • u := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
        add_comm, ← sub_eq_add_neg]
    rw [← hI, hq.smul]
    simp
  have hpol : polar q v (Complex.I • u) = - polar q u (Complex.I • v) := by
    simp only [polar, h1, h2]
    ring
  simp only [sesq, hq.polar_symm v u, hpol]
  simp only [map_sub, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-- **`sesq` restricts to `q` on the diagonal:** `sesq q v v = q v`. The diagonal value is
`polar q v v = 4 q v` (degree-2 homogeneity at `2`), and the imaginary term vanishes:
`q (v − i·v) = q (v + i·v)` (unit phase `−i`). Both steps are the same witness,
`IsQuadraticLike.smul` (`q (c • v) = ‖c‖² q v`): at `c = 2` it gives the diagonal value, and at
`c = −i` it gives `‖−i‖² = 1`, collapsing the imaginary term. -/
theorem sesq_self (v : EuclideanSpace ℂ (Fin N)) : sesq q v v = ((q v : ℝ) : ℂ) := by
  have hdiag : polar q v v = 4 * q v := by
    have h2 : v + v = ((2 : ℝ) : ℂ) • v := by push_cast; rw [two_smul]
    have hn2 : ‖((2 : ℝ) : ℂ)‖ ^ 2 = 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [polar, h2, hq.smul, hn2, sub_self, hq.zero, sub_zero]
  have hIv : polar q v (Complex.I • v) = 0 := by
    have hneg : (-Complex.I) • (v + Complex.I • v) = v - Complex.I • v := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul,
        add_comm, ← sub_eq_add_neg]
    rw [polar, ← hneg, hq.smul]
    simp
  rw [sesq, hdiag, hIv]
  push_cast
  ring

/-- **`sesq` is linear over finite sums in the second slot.** -/
theorem sesq_sum_right {ι : Type*} (u : EuclideanSpace ℂ (Fin N)) (s : Finset ι) (c : ι → ℂ)
    (e : ι → EuclideanSpace ℂ (Fin N)) :
    sesq q u (∑ i ∈ s, c i • e i) = ∑ i ∈ s, c i * sesq q u (e i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [sesq_zero_right]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hq.sesq_add_right, hq.sesq_smul_right, ih]

/-- **`sesq` is conjugate-linear over finite sums in the first slot.** -/
theorem sesq_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (e : ι → EuclideanSpace ℂ (Fin N)) (w : EuclideanSpace ℂ (Fin N)) :
    sesq q (∑ i ∈ s, c i • e i) w = ∑ i ∈ s, (starRingEnd ℂ) (c i) * sesq q (e i) w := by
  rw [hq.sesq_conj_symm w (∑ i ∈ s, c i • e i), hq.sesq_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  exact (hq.sesq_conj_symm w (e i)).symm

/-- **`polarMatrix q` is Hermitian**, directly from `sesq_conj_symm`. -/
theorem polarMatrix_isHermitian : (polarMatrix q).IsHermitian := by
  ext j k
  simp only [Matrix.conjTranspose_apply, polarMatrix, Matrix.of_apply, Complex.star_def]
  exact (hq.sesq_conj_symm (EuclideanSpace.single k (1:ℂ))
    (EuclideanSpace.single j (1:ℂ))).symm

omit hq in
/-- **Standard-basis expansion in `EuclideanSpace`:** `v = ∑ᵢ vᵢ • eᵢ`. -/
theorem _root_.Gleason.euclidean_sum_single (v : EuclideanSpace ℂ (Fin N)) :
    ∑ i, (v i) • (EuclideanSpace.single i (1:ℂ)) = v := by
  ext j
  simp
  refine (Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_).trans ?_
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- **`sesq` is the sesquilinear form of `polarMatrix`:** `sesq q u v = ⟨u, R v⟩`. Expand both
slots in the standard basis. -/
theorem sesq_eq_dotProduct (u v : EuclideanSpace ℂ (Fin N)) :
    sesq q u v = star (⇑u) ⬝ᵥ (polarMatrix q *ᵥ (⇑v)) := by
  conv_lhs => rw [← euclidean_sum_single u, ← euclidean_sum_single v]
  rw [hq.sesq_sum_left]
  simp only [hq.sesq_sum_right, dotProduct, Pi.star_apply, Matrix.mulVec, polarMatrix,
    Matrix.of_apply, Finset.mul_sum, Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- ★ **`q` is the quadratic form of `polarMatrix q`:** `q v = ⟨v, R v⟩`. -/
theorem eq_dotProduct (v : EuclideanSpace ℂ (Fin N)) :
    ((q v : ℝ) : ℂ) = star (⇑v) ⬝ᵥ (polarMatrix q *ᵥ (⇑v)) := by
  rw [← hq.sesq_self v, hq.sesq_eq_dotProduct]

end IsQuadraticLike

/-! ### Matrix facts for the descent -/

/-- **A complex matrix is determined by its quadratic form.** If `star x ⬝ᵥ (D *ᵥ x) = 0` for
every `x`, then `D = 0`: over `ℂ` the diagonal of a sesquilinear form recovers the whole form by
polarisation. -/
theorem matrix_eq_zero_of_quadForm_zero {D : Matrix (Fin N) (Fin N) ℂ}
    (hQ : ∀ x : Fin N → ℂ, star x ⬝ᵥ (D *ᵥ x) = 0) : D = 0 := by
  have hI : star (Complex.I) = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hB : ∀ u v : Fin N → ℂ, star u ⬝ᵥ (D *ᵥ v) = 0 := by
    intro u v
    have h1 := hQ (u + v)
    have h2 := hQ (u - v)
    have h3 := hQ (u + Complex.I • v)
    have h4 := hQ (u - Complex.I • v)
    simp only [star_add, star_sub, star_smul, hI, mulVec_add, mulVec_sub, Matrix.mulVec_smul,
      add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, neg_mul] at h1 h2 h3 h4
    have key : (4 : ℂ) * (star u ⬝ᵥ (D *ᵥ v)) = 0 := by
      linear_combination h1 - h2 - Complex.I * h3 + Complex.I * h4
        + (2 * (star u ⬝ᵥ (D *ᵥ v)) - 2 * (star v ⬝ᵥ (D *ᵥ u))) * hII
    have h4ne : (4 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp key).resolve_left h4ne
  ext j k
  have hjk := hB (Pi.single j 1) (Pi.single k 1)
  rw [Matrix.mulVec_single_one] at hjk
  simpa [dotProduct, Matrix.col_apply, Pi.single_apply, Finset.sum_ite_eq', eq_comm] using hjk

/-- **The trace of a product of two Hermitian matrices is real.** `conj Tr(A·B) = Tr(B·A) =
Tr(A·B)`. -/
theorem trace_mul_isHermitian_real {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (starRingEnd ℂ) ((A * B).trace) = (A * B).trace := by
  calc (starRingEnd ℂ) ((A * B).trace)
      = ((A * B)ᴴ).trace := by rw [starRingEnd_apply, ← Matrix.trace_conjTranspose]
    _ = (B * A).trace := by rw [Matrix.conjTranspose_mul, hA.eq, hB.eq]
    _ = (A * B).trace := Matrix.trace_mul_comm _ _

/-- **`Tr(R · |v⟩⟨v|) = ⟨v, R v⟩`.** The trace against a rank-one projector is the quadratic
form. -/
theorem trace_mul_vecMulVec (R : Matrix (Fin N) (Fin N) ℂ) (v : EuclideanSpace ℂ (Fin N)) :
    (R * Matrix.vecMulVec (⇑v) (star ⇑v)).trace = star (⇑v) ⬝ᵥ (R *ᵥ (⇑v)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Pi.star_apply, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

end Gleason

end

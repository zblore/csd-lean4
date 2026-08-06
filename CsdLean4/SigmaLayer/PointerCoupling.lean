/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerRotation
public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound
public import CsdLean4.Mathlib.Analysis.Matrix.L2OpNormEntry

/-!
# SigmaLayer/PointerCoupling: the weighted coupling and its exponential propagator (brick 2a)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 2, generator half).

The selector-modulated coupling is a **weighted sum of the plane-swap generators**:

  `couplingH w = Σⱼ wⱼ • hⱼ`,  `hⱼ = |f₀⟩⟨f_{j+1}| + |f_{j+1}⟩⟨f₀|`,

Hermitian for every real weight vector (`couplingH_isHermitian`) — the `hⱼ` do **not**
commute pairwise (all planes share `f₀`), so the propagator is the genuine matrix
exponential, not a closed form:

  `couplingU w = exp((π/2) • (−i • couplingH w))`,

unitary by the skew-Hermitian exponential theorem (`couplingU_mem_unitaryGroup`, via
`Matrix.StoneC1.exp_smul_unitary`). Three facts make it the right object:

* **On a pure weight it is the brick-1 rotation**: `couplingU (Pi.single j 1)
  = pointerRot (π/2) j` (`couplingU_single`) — through ★ `pointerRot_eq_exp`, the
  **Hamiltonian-generation identification** `pointerRot θ j = exp(θ • (−i • hⱼ))`, proved by
  ODE uniqueness (`Matrix.StoneC1.eq_exp_of_hasDeriv`: the closed form solves `Y' = Y·A`,
  `Y 0 = 1`). This was scheduled as brick 5 but is pulled forward: the landing theorem
  (brick 3) reads the propagator on pure cells through it.
* **It is entrywise Lipschitz in the weights** (`continuous_couplingU_entry`): the Duhamel
  bound `‖exp(t•(−iH)) − exp(t•(−iH₀))‖ ≤ |t|·‖H−H₀‖` plus the entry bound
  `‖M a b‖ ≤ ‖M‖` (staged `Matrix.norm_entry_le_l2_opNorm`) give
  `‖couplingU w − couplingU w'‖ ≤ (π/2)·(Σⱼ‖hⱼ‖)·dist(w,w')` — so each entry is a
  Lipschitz, hence continuous, function of the weight vector, **stated in the plain Pi
  topology** (no scoped norm instances leak into the statement).
* **Liouville preservation** on the pointer is FS unitary invariance
  (`couplingUU_measurePreserving`), as always.

⚠️ **Honest scope.** This is the generator half of brick 2: the weights here are a free
parameter `w : Fin K → ℝ`. The **bump weight field** `w(p,θ)` (trapezoids on `ε`-shrunk
context cells) and the joint continuity of the full arena propagator are brick 2b; record
landing, Born accounting, and the protocol are bricks 3–4. `pointerRot_eq_exp` upgrades
brick 1's honest-scope note: the closed form **is** now identified with the exponential of
its Hermitian generator — the generation statement at the formalisable level for the
single-plane rotation. The moment-map (symplectic) reading of "Hamiltonian" remains prose:
Mathlib has no symplectic API (`MATHLIB-GAPS.md`).

## References

`specs/pointer-witness-plan.md` (bricks 2, 5); `specs/BACKLOG.md` (the ★ L row);
`specs/future-work.md`. Reused corpus API: `Matrix.StoneC1.eq_exp_of_hasDeriv` /
`exp_smul_unitary` (`Mathlib/Analysis/Matrix/StoneC1.lean` staging),
`Matrix.norm_exp_smul_neg_I_sub_le` (`DuhamelBound.lean` staging),
`Matrix.norm_entry_le_l2_opNorm` (`L2OpNormEntry.lean` staging, new),
`pointerH`/`pointerRot` algebra (`SigmaLayer/PointerRotation.lean`),
`fubiniStudyMeasure_smul_invariant`.
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup NormedSpace
open scoped Matrix.Norms.L2Operator

variable {K : ℕ}

/-! ### The weighted coupling generator -/

/-- The weighted coupling `Σⱼ wⱼ • hⱼ`: the selector will set the weights; here they are a
free real vector. -/
noncomputable def couplingH (w : Fin K → ℝ) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  ∑ j, (w j : ℂ) • pointerH j

/-- **The coupling is Hermitian for every real weight vector.** -/
theorem couplingH_isHermitian (w : Fin K → ℝ) : (couplingH w).IsHermitian := by
  show (couplingH w)ᴴ = couplingH w
  unfold couplingH
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_smul, (pointerH_isHermitian j).eq, Complex.star_def,
    Complex.conj_ofReal]

/-- The Schrödinger generator `−i • couplingH w` is skew-Hermitian. -/
theorem couplingH_skew (w : Fin K → ℝ) :
    star ((-Complex.I) • couplingH w) = -((-Complex.I) • couplingH w) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, (couplingH_isHermitian w).eq,
    show star (-Complex.I) = Complex.I by simp]
  module

/-- On the pure weight vector of outcome `j`, the coupling is the plane swap `hⱼ`. -/
theorem couplingH_single (j : Fin K) : couplingH (Pi.single j 1) = pointerH j := by
  unfold couplingH
  rw [Finset.sum_eq_single j
    (fun k _ hk => by rw [Pi.single_eq_of_ne hk]; simp)
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [Pi.single_eq_same]
  simp

/-- The coupling difference is linear in the weight difference, in norm:
`‖couplingH w − couplingH w'‖ ≤ (Σⱼ ‖hⱼ‖) · dist(w, w')`. -/
theorem norm_couplingH_sub_le (w w' : Fin K → ℝ) :
    ‖couplingH w - couplingH w'‖ ≤ (∑ j : Fin K, ‖pointerH j‖) * dist w w' := by
  have h1 : couplingH w - couplingH w' = ∑ j, ((w j - w' j : ℝ) : ℂ) • pointerH j := by
    unfold couplingH
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, ← Complex.ofReal_sub]
  rw [h1]
  calc ‖∑ j : Fin K, ((w j - w' j : ℝ) : ℂ) • pointerH j‖
      ≤ ∑ j : Fin K, ‖((w j - w' j : ℝ) : ℂ) • pointerH j‖ := norm_sum_le _ _
    _ = ∑ j : Fin K, |w j - w' j| * ‖pointerH j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin K, dist w w' * ‖pointerH j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← Real.dist_eq]
        exact dist_le_pi_dist w w' j
    _ = (∑ j : Fin K, ‖pointerH j‖) * dist w w' := by rw [← Finset.mul_sum, mul_comm]

/-! ### The exponential propagator -/

/-- The coupling propagator at the measurement stroke: `exp((π/2) • (−i • couplingH w))`.
The `hⱼ` do not commute, so this is the honest matrix exponential — no closed form. -/
noncomputable def couplingU (w : Fin K → ℝ) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  NormedSpace.exp ((Real.pi / 2) • ((-Complex.I) • couplingH w))

/-- **The coupling propagator is unitary** — the skew-Hermitian exponential theorem. -/
theorem couplingU_mem_unitaryGroup (w : Fin K → ℝ) :
    couplingU w ∈ Matrix.unitaryGroup (Fin (K + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  show (couplingU w)ᴴ * couplingU w = 1
  unfold couplingU
  exact Matrix.StoneC1.exp_smul_unitary ((-Complex.I) • couplingH w) (couplingH_skew w)
    (Real.pi / 2)

/-- The coupling propagator as a unitary-group element. -/
noncomputable def couplingUU (w : Fin K → ℝ) : Matrix.unitaryGroup (Fin (K + 1)) ℂ :=
  ⟨couplingU w, couplingU_mem_unitaryGroup w⟩

/-- Liouville preservation on the pointer: FS unitary invariance. -/
theorem couplingUU_measurePreserving (w : Fin K → ℝ) (q₀ : Pointer K) :
    MeasurePreserving (fun q : Pointer K => couplingUU w • q)
      (fubiniStudyMeasure q₀) (fubiniStudyMeasure q₀) :=
  ⟨(continuous_const_smul _).measurable, fubiniStudyMeasure_smul_invariant _ q₀⟩

/-! ### The generation identification (brick 5's statement, pulled forward) -/

/-- The closed-form rotation, multiplied by its claimed generator on the right. -/
lemma pointerRot_mul_gen (t : ℝ) (j : Fin K) :
    pointerRot t j * ((-Complex.I) • pointerH j)
      = (-(Real.sin t : ℂ)) • pointerPlane j
        + (-(Complex.I * (Real.cos t : ℂ))) • pointerH j := by
  unfold pointerRot
  rw [Matrix.mul_smul, add_mul, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc,
    pointerPlane_mul_pointerH, pointerH_mul_self, smul_add, smul_add, smul_smul, smul_smul,
    show (-Complex.I) * (-(Complex.I * (Real.sin t : ℂ)))
        = Complex.I * Complex.I * (Real.sin t : ℂ) from by ring,
    Complex.I_mul_I]
  module

/-- ★ **The Hamiltonian-generation identification for the plane rotation**: the brick-1
closed form **is** the exponential of its Hermitian generator,

  `pointerRot θ j = exp(θ • (−i • hⱼ))`,

by ODE uniqueness (`Matrix.StoneC1.eq_exp_of_hasDeriv`): both sides solve `Y' = Y·(−i hⱼ)`
with `Y 0 = 1`. This discharges the single-plane half of brick 5's generation obligation. -/
theorem pointerRot_eq_exp (θ : ℝ) (j : Fin K) :
    pointerRot θ j = NormedSpace.exp (θ • ((-Complex.I) • pointerH j)) := by
  refine Matrix.StoneC1.eq_exp_of_hasDeriv ((-Complex.I) • pointerH j)
    (fun s => pointerRot s j) (fun t => ?_) (pointerRot_zero j) θ
  have ha : HasDerivAt (fun s : ℝ => ((Real.cos s : ℂ) - 1)) (-(Real.sin t : ℂ)) t := by
    have h1 := (Real.hasDerivAt_cos t).ofReal_comp
    rw [Complex.ofReal_neg] at h1
    exact h1.sub_const 1
  have hb : HasDerivAt (fun s : ℝ => (-(Complex.I * (Real.sin s : ℂ))))
      (-(Complex.I * (Real.cos t : ℂ))) t := by
    have h1 := (Real.hasDerivAt_sin t).ofReal_comp
    exact (h1.const_mul Complex.I).neg
  simp only [pointerRot_mul_gen]
  simp only [pointerRot]
  rw [← zero_add ((-(Real.sin t : ℂ)) • pointerPlane j)]
  exact ((hasDerivAt_const t 1).add (ha.smul_const (pointerPlane j))).add
    (hb.smul_const (pointerH j))

/-- **On a pure weight the coupling propagator is the brick-1 quarter rotation** — the pure
cells of the modulated witness run exactly the fixed-outcome record transport. -/
theorem couplingU_single (j : Fin K) :
    couplingU (Pi.single j 1) = pointerRot (Real.pi / 2) j := by
  unfold couplingU
  rw [couplingH_single, ← pointerRot_eq_exp]

/-! ### Entrywise Lipschitz continuity in the weights -/

/-- **The Duhamel estimate for the coupling propagator**:
`‖couplingU w − couplingU w'‖ ≤ (π/2)·(Σⱼ‖hⱼ‖)·dist(w, w')`. -/
theorem norm_couplingU_sub_le (w w' : Fin K → ℝ) :
    ‖couplingU w - couplingU w'‖
      ≤ Real.pi / 2 * (∑ j : Fin K, ‖pointerH j‖) * dist w w' := by
  have hd : ‖couplingU w - couplingU w'‖
      ≤ |Real.pi / 2| * ‖couplingH w - couplingH w'‖ := by
    unfold couplingU
    exact Matrix.norm_exp_smul_neg_I_sub_le _ _ (couplingH_isHermitian w)
      (couplingH_isHermitian w') _
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hd
  calc ‖couplingU w - couplingU w'‖
      ≤ Real.pi / 2 * ‖couplingH w - couplingH w'‖ := hd
    _ ≤ Real.pi / 2 * ((∑ j : Fin K, ‖pointerH j‖) * dist w w') := by
        exact mul_le_mul_of_nonneg_left (norm_couplingH_sub_le w w')
          (by positivity)
    _ = Real.pi / 2 * (∑ j : Fin K, ‖pointerH j‖) * dist w w' := by ring

/-- **Each entry of the coupling propagator is a continuous function of the weight
vector** — Lipschitz via the Duhamel estimate and the staged entry bound. The statement
mentions no matrix norm or matrix topology: it composes freely downstream. -/
theorem continuous_couplingU_entry (a b : Fin (K + 1)) :
    Continuous fun w : Fin K → ℝ => couplingU w a b := by
  have hlip : LipschitzWith (Real.toNNReal (Real.pi / 2 * ∑ j : Fin K, ‖pointerH j‖))
      (fun w : Fin K → ℝ => couplingU w a b) := by
    apply LipschitzWith.of_dist_le_mul
    intro w w'
    calc dist (couplingU w a b) (couplingU w' a b)
        = ‖couplingU w a b - couplingU w' a b‖ := dist_eq_norm _ _
      _ = ‖(couplingU w - couplingU w') a b‖ := by rw [Matrix.sub_apply]
      _ ≤ ‖couplingU w - couplingU w'‖ :=
          Matrix.norm_entry_le_l2_opNorm (couplingU w - couplingU w') a b
      _ ≤ Real.pi / 2 * (∑ j : Fin K, ‖pointerH j‖) * dist w w' := norm_couplingU_sub_le w w'
      _ ≤ (Real.toNNReal (Real.pi / 2 * ∑ j : Fin K, ‖pointerH j‖) : ℝ) * dist w w' := by
          refine mul_le_mul_of_nonneg_right ?_ dist_nonneg
          exact Real.le_coe_toNNReal _
  exact hlip.continuous

end CSD.RecordLayer

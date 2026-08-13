/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerArena
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
public import Mathlib.Tactic.Module

/-!
# SigmaLayer/PointerRotation: the fixed-outcome pointer rotation (brick 1)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 1).

The generator for outcome `j` is the Hermitian plane-swap
`hⱼ = |f₀⟩⟨f_{j+1}| + |f_{j+1}⟩⟨f₀|` (`pointerH`, `pointerH_isHermitian`). Its rotation family

  `pointerRot θ j = 1 + (cos θ − 1)•Pⱼ − (i sin θ)•hⱼ`,  `Pⱼ = |f₀⟩⟨f₀| + |f_{j+1}⟩⟨f_{j+1}|`

is a **continuous one-parameter unitary group** — machine-checked as: the group law
(`pointerRot_add`), the identity at `0` (`pointerRot_zero`), unitarity
(`pointerRot_mem_unitaryGroup`, via the closed form `(pointerRot θ)ᴴ = pointerRot (−θ)`), and
continuity in `θ`, both into the unitary group (`continuous_pointerRotU`) and through the
projective action (`continuous_pointerRotU_smul`). At the quarter turn it transports the ready
vertex to the record vertex, projectively:

  `pointerRotU (π/2) j • readyState = recordState j`  (`pointerRotU_pi_div_two_ready`),

and every `pointerRotU θ j` preserves the pointer Fubini–Study measure
(`pointerRotU_measurePreserving` — FS unitary invariance, the same one-liner as
`joinSwap_measurePreserving`). **This is the map the torus register provably could not give
as any continuous flow slice** (`shearEvolve_not_continuous`): here record transport is a
continuous curve of unitaries, no seams, no flux.

⚠️ **Honest scope.** The identification `pointerRot θ j = exp(−iθ hⱼ)` — the *generation*
statement — is brick 5 of the plan, not this module; here the family is given in closed
trigonometric form and its group properties are proved directly (the closed form and the
exponential agree because both solve the same linear recursion, but that identification is
not formalised yet, and nothing below cites it). What brick 1 delivers is exactly: a
continuous one-parameter unitary group on the pointer, with Hermitian infinitesimal data
`pointerH`, transporting ready → record and preserving Liouville. The selector-modulated
coupling (bump-weighted sums of the `pointerH j` — which do **not** commute pairwise, since
all planes share `f₀`) is brick 2 and will need the exponential route, not this closed form.

## References

`specs/pointer-witness-plan.md` (bricks 1, 2, 5); `specs/BACKLOG.md` (the ★ L row);
`specs/future-work.md`. Reused corpus API: `Matrix.single` algebra (Mathlib),
`smul_mk_eq_mk_toEuclideanLin` + `orbit_map_continuous`
(`Mathlib/LinearAlgebra/Projectivization/{TransitionProbability,FubiniStudy}.lean` staging),
`fubiniStudyMeasure_smul_invariant` (ibid.), `readyState`/`recordState`
(`SigmaLayer/PointerArena.lean`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup

variable {K : ℕ}

/-! ### The generator and its plane -/

/-- The plane projector `Pⱼ = |f₀⟩⟨f₀| + |f_{j+1}⟩⟨f_{j+1}|` onto the ready–record plane. -/
def pointerPlane (j : Fin K) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  Matrix.single 0 0 1 + Matrix.single j.succ j.succ 1

/-- The Hermitian generator `hⱼ = |f₀⟩⟨f_{j+1}| + |f_{j+1}⟩⟨f₀|`: the plane swap between the
ready direction and the `j`-th record direction. -/
def pointerH (j : Fin K) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  Matrix.single 0 j.succ 1 + Matrix.single j.succ 0 1

lemma succ_ne_zero' (j : Fin K) : (j.succ : Fin (K + 1)) ≠ 0 :=
  Fin.succ_ne_zero j

lemma pointerPlane_mul_self (j : Fin K) :
    pointerPlane j * pointerPlane j = pointerPlane j := by
  unfold pointerPlane
  rw [add_mul, mul_add, mul_add,
      Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne (h := (succ_ne_zero' j).symm),
      Matrix.single_mul_single_of_ne (h := succ_ne_zero' j),
      Matrix.single_mul_single_same, add_zero, zero_add, one_mul]

lemma pointerH_mul_self (j : Fin K) :
    pointerH j * pointerH j = pointerPlane j := by
  unfold pointerH pointerPlane
  rw [add_mul, mul_add, mul_add,
      Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne (h := succ_ne_zero' j),
      Matrix.single_mul_single_of_ne (h := (succ_ne_zero' j).symm),
      Matrix.single_mul_single_same, zero_add, add_zero, one_mul]

lemma pointerPlane_mul_pointerH (j : Fin K) :
    pointerPlane j * pointerH j = pointerH j := by
  unfold pointerPlane pointerH
  rw [add_mul, mul_add, mul_add,
      Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne (h := (succ_ne_zero' j).symm),
      Matrix.single_mul_single_of_ne (h := succ_ne_zero' j),
      Matrix.single_mul_single_same, add_zero, zero_add, one_mul]

lemma pointerH_mul_pointerPlane (j : Fin K) :
    pointerH j * pointerPlane j = pointerH j := by
  unfold pointerH pointerPlane
  rw [add_mul, mul_add, mul_add,
      Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne (h := succ_ne_zero' j),
      Matrix.single_mul_single_of_ne (h := (succ_ne_zero' j).symm),
      Matrix.single_mul_single_same, zero_add, add_zero, one_mul]

lemma single_one_conjTranspose (a b : Fin (K + 1)) :
    (Matrix.single a b (1 : ℂ))ᴴ = Matrix.single b a 1 := by
  ext i k
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply, apply_ite (star : ℂ → ℂ),
    star_one, star_zero]
  exact if_congr and_comm rfl rfl

lemma pointerPlane_conjTranspose (j : Fin K) :
    (pointerPlane j)ᴴ = pointerPlane j := by
  unfold pointerPlane
  rw [Matrix.conjTranspose_add, single_one_conjTranspose, single_one_conjTranspose]

/-- **The generator is Hermitian** — the coupling the smooth witness rotates by is honest
Hamiltonian data. -/
theorem pointerH_isHermitian (j : Fin K) : (pointerH j).IsHermitian := by
  show (pointerH j)ᴴ = pointerH j
  unfold pointerH
  rw [Matrix.conjTranspose_add, single_one_conjTranspose, single_one_conjTranspose]
  exact add_comm _ _

/-! ### The rotation family -/

/-- The pointer rotation at angle `θ` in the ready–record plane of outcome `j`:
`1 + (cos θ − 1)•Pⱼ − (i sin θ)•hⱼ` — the closed form of `exp(−iθ hⱼ)` (the identification
itself is brick 5; nothing here consumes it). -/
noncomputable def pointerRot (θ : ℝ) (j : Fin K) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  1 + ((Real.cos θ : ℂ) - 1) • pointerPlane j + (-(Complex.I * (Real.sin θ : ℂ))) • pointerH j

/-- The generic product in the rotation plane's algebra: `{1, Pⱼ, hⱼ}` is closed under
multiplication, with the stated structure constants. -/
lemma pointer_combo_mul (j : Fin K) (x₁ y₁ x₂ y₂ : ℂ) :
    (1 + x₁ • pointerPlane j + y₁ • pointerH j)
        * (1 + x₂ • pointerPlane j + y₂ • pointerH j)
      = 1 + (x₁ + x₂ + x₁ * x₂ + y₁ * y₂) • pointerPlane j
          + (y₁ + y₂ + x₁ * y₂ + y₁ * x₂) • pointerH j := by
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, Matrix.mul_smul, smul_smul,
    pointerPlane_mul_self, pointerH_mul_self, pointerPlane_mul_pointerH,
    pointerH_mul_pointerPlane]
  module

/-- The rotation at angle `0` is the identity. -/
theorem pointerRot_zero (j : Fin K) : pointerRot 0 j = 1 := by
  simp [pointerRot]

/-- **The group law**: rotations in a fixed plane compose additively in the angle. -/
theorem pointerRot_add (θ₁ θ₂ : ℝ) (j : Fin K) :
    pointerRot θ₁ j * pointerRot θ₂ j = pointerRot (θ₁ + θ₂) j := by
  have hA : ((Real.cos θ₁ : ℂ) - 1) + ((Real.cos θ₂ : ℂ) - 1)
      + ((Real.cos θ₁ : ℂ) - 1) * ((Real.cos θ₂ : ℂ) - 1)
      + (-(Complex.I * (Real.sin θ₁ : ℂ))) * (-(Complex.I * (Real.sin θ₂ : ℂ)))
      = ((Real.cos (θ₁ + θ₂) : ℂ) - 1) := by
    rw [show (-(Complex.I * (Real.sin θ₁ : ℂ))) * (-(Complex.I * (Real.sin θ₂ : ℂ)))
        = Complex.I * Complex.I * ((Real.sin θ₁ : ℂ) * (Real.sin θ₂ : ℂ)) from by ring,
      Complex.I_mul_I, Real.cos_add]
    push_cast
    ring
  have hB : (-(Complex.I * (Real.sin θ₁ : ℂ))) + (-(Complex.I * (Real.sin θ₂ : ℂ)))
      + ((Real.cos θ₁ : ℂ) - 1) * (-(Complex.I * (Real.sin θ₂ : ℂ)))
      + (-(Complex.I * (Real.sin θ₁ : ℂ))) * ((Real.cos θ₂ : ℂ) - 1)
      = -(Complex.I * (Real.sin (θ₁ + θ₂) : ℂ)) := by
    rw [Real.sin_add]
    push_cast
    ring
  unfold pointerRot
  rw [pointer_combo_mul, hA, hB]

/-- The conjugate transpose of a rotation is the reverse rotation. -/
theorem pointerRot_conjTranspose (θ : ℝ) (j : Fin K) :
    (pointerRot θ j)ᴴ = pointerRot (-θ) j := by
  have ha : star ((Real.cos θ : ℂ) - 1) = ((Real.cos (-θ) : ℂ) - 1) := by
    rw [Real.cos_neg, star_sub, star_one, Complex.star_def, Complex.conj_ofReal]
  have hb : star (-(Complex.I * (Real.sin θ : ℂ)))
      = -(Complex.I * (Real.sin (-θ) : ℂ)) := by
    rw [Real.sin_neg, star_neg, Complex.star_def, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    push_cast
    ring
  unfold pointerRot
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, pointerPlane_conjTranspose,
      (pointerH_isHermitian j).eq, ha, hb]

/-- **Every pointer rotation is unitary.** -/
theorem pointerRot_mem_unitaryGroup (θ : ℝ) (j : Fin K) :
    pointerRot θ j ∈ Matrix.unitaryGroup (Fin (K + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  show pointerRot θ j * (pointerRot θ j)ᴴ = 1
  rw [pointerRot_conjTranspose, pointerRot_add, add_neg_cancel, pointerRot_zero]

/-- The pointer rotation as a unitary-group element. -/
noncomputable def pointerRotU (θ : ℝ) (j : Fin K) : Matrix.unitaryGroup (Fin (K + 1)) ℂ :=
  ⟨pointerRot θ j, pointerRot_mem_unitaryGroup θ j⟩

/-- The group law at the unitary-group level. -/
theorem pointerRotU_add (θ₁ θ₂ : ℝ) (j : Fin K) :
    pointerRotU θ₁ j * pointerRotU θ₂ j = pointerRotU (θ₁ + θ₂) j :=
  Subtype.ext (pointerRot_add θ₁ θ₂ j)

/-! ### Continuity -/

/-- **The rotation family is continuous in the angle** — with the group law and unitarity,
`pointerRotU · j` is a continuous one-parameter unitary group. -/
theorem continuous_pointerRotU (j : Fin K) :
    Continuous fun θ : ℝ => pointerRotU θ j := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro a b
  simp only [pointerRot, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine (continuous_const.add ?_).add ?_
  · exact ((Complex.continuous_ofReal.comp Real.continuous_cos).sub continuous_const).mul
      continuous_const
  · exact ((continuous_const.mul
      (Complex.continuous_ofReal.comp Real.continuous_sin)).neg).mul continuous_const

/-- Continuity through the projective action: for every pointer state `q`, the rotation orbit
`θ ↦ Uⱼ(θ) • q` is a continuous curve on `ℂℙ^K`. -/
theorem continuous_pointerRotU_smul (j : Fin K) (q : Pointer K) :
    Continuous fun θ : ℝ => pointerRotU θ j • q :=
  (orbit_map_continuous q).comp (continuous_pointerRotU j)

/-! ### Liouville preservation and record transport -/

/-- **Every pointer rotation preserves the pointer Fubini–Study measure** — Liouville
preservation is FS unitary invariance, exactly as on the join arena. -/
theorem pointerRotU_measurePreserving (θ : ℝ) (j : Fin K) (q₀ : Pointer K) :
    MeasurePreserving (fun q : Pointer K => pointerRotU θ j • q)
      (fubiniStudyMeasure q₀) (fubiniStudyMeasure q₀) :=
  ⟨(continuous_const_smul _).measurable, fubiniStudyMeasure_smul_invariant _ q₀⟩

/-- **The quarter turn transports ready to record**: `Uⱼ(π/2) • [f₀] = [f_{j+1}]`
(projectively; the representative picks up the phase `−i`). -/
theorem pointerRotU_pi_div_two_ready (j : Fin K) :
    pointerRotU (Real.pi / 2) j • readyState = recordState (K := K) j := by
  unfold readyState recordState vertexPoint
  rw [Projectivization.smul_mk_eq_mk_toEuclideanLin]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨-Complex.I, ?_⟩
  apply PiLp.ext
  intro b
  have happ : (Matrix.toEuclideanLin (pointerRotU (Real.pi / 2) j).val
      (EuclideanSpace.single 0 (1 : ℂ))) b
      = pointerRot (Real.pi / 2) j b 0 := by
    show ((pointerRotU (Real.pi / 2) j).val *ᵥ _) b = _
    simp [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero, pointerRotU]
  rw [happ]
  simp only [pointerRot, Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.ofReal_zero,
    Complex.ofReal_one, mul_one, zero_sub, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, pointerPlane, pointerH, Matrix.single_apply, PiLp.smul_apply,
    PiLp.single_apply]
  rcases eq_or_ne b 0 with hb0 | hb0
  · subst hb0
    simp [(succ_ne_zero' j).symm, succ_ne_zero' j]
  · rcases eq_or_ne b j.succ with hbj | hbj
    · subst hbj
      simp [succ_ne_zero' j, (succ_ne_zero' j).symm]
    · simp [Ne.symm hb0, Ne.symm hbj, hb0, hbj]

end CSD.RecordLayer

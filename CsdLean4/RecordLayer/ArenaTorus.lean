/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerWeights
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# RecordLayer/ArenaTorus: the conserved-quantity torus acting on the pointer arena

**Category:** dynamical measurement — `specs/BACKLOG.md` §A (joint-arena lift), the
kinematic half of the joint lift `RecordLayer/JointLift.lean` builds.

## What this is

The arena `PointerArena N N = (ℂℙ^{N-1} × T²) × ℂℙ^{N-1}` carries an `(N+1)`-torus of
symmetries that **fix every quantity the measurement stroke reads**:

* `phaseUnitary g`, `g : Fin N → AddCircle 1`, is the diagonal unitary
  `diag (e^{2πi g₀}, …, e^{2πi g_{N-1}})`. It rotates the base point along its moment
  fibre — the moment map is exactly `|ψⱼ|²/‖ψ‖²`, which does not see the phases
  (`momentMap_phaseUnitary_smul`).
* the last circle translates the register's **conjugate** coordinate `θ₂`, leaving the
  register `θ₁` (what the weights read) alone.

`torusAct` is the resulting action of `ArenaTorus N := (Fin N → AddCircle 1) × AddCircle 1`
on the arena. It is jointly continuous, hence jointly measurable (`continuous_torusAct`,
`measurable_torusAct`), it composes (`torusAct_add`), and every `torusAct g` preserves the
arena Liouville measure `pointerLiouville p₀ q₀` (`torusAct_measurePreserving`) — the
Fubini–Study factor by `fubiniStudyMeasure_smul_invariant`, the torus factors by translation
invariance of Haar measure.

## Why it exists

A back-reacting joint flow moves the base — but by *how much and where* is governed by
conservation: the moments and the register are constants of motion (`IsJointLift`), so the
base can only move **along this torus**. The joint lift is therefore a twist of the
fibrewise witness by a torus element that depends on the conserved data alone, and the
general fact that such twists preserve measure is `MeasurePreserving.vadd_twist_of_invariant`
(`Mathlib/MeasureTheory/InvariantTwist.lean`). This module supplies every hypothesis of that
lemma for the arena.

`ContextField.TorusInvariant` names the one condition on a context field that the
construction needs — rates constant along base phase rotations — and `momentContext` has it.

## References

`specs/frozen-base-obstruction-scoping.md` (brick 3, joint lift); `specs/future-work.md`;
`RecordLayer/JointLift.lean` (the consumer); `RecordLayer/JointFlowTransfer.lean`
(`IsJointLift`); `Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`
(`fubiniStudyMeasure_smul_invariant`); `Mathlib/LinearAlgebra/Projectivization/
FubiniStudyUnique.lean` (`instContinuousSMul_projectivization`);
`Mathlib/LinearAlgebra/Projectivization/TransitionProbability.lean`
(`smul_mk_eq_mk_toEuclideanLin`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

variable {N K : ℕ}

/-! ### The diagonal phase unitary -/

/-- The unit-modulus phase `e^{2πi g}` of a point `g : AddCircle 1`, as a complex number. -/
noncomputable abbrev circlePhase (g : AddCircle (1 : ℝ)) : ℂ := ((AddCircle.toCircle g : Circle) : ℂ)

lemma norm_circlePhase (g : AddCircle (1 : ℝ)) : ‖circlePhase g‖ = 1 := Circle.norm_coe _

lemma circlePhase_add (a b : AddCircle (1 : ℝ)) :
    circlePhase (a + b) = circlePhase a * circlePhase b := by
  rw [circlePhase, AddCircle.toCircle_add, Circle.coe_mul]

@[simp] lemma circlePhase_zero : circlePhase (0 : AddCircle (1 : ℝ)) = 1 := by
  rw [circlePhase, AddCircle.toCircle_zero, Circle.coe_one]

lemma continuous_circlePhase : Continuous circlePhase :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

/-- The diagonal unitary `diag (e^{2πi g₀}, …, e^{2πi g_{N-1}})`, as an element of the
unitary group. This is the base torus of the joint lift: it rotates every coordinate of a
state vector by its own phase, and so moves a projective point along its moment fibre. -/
noncomputable def phaseUnitary (g : Fin N → AddCircle (1 : ℝ)) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨Matrix.diagonal fun j => circlePhase (g j), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]⟩

@[simp] lemma phaseUnitary_val (g : Fin N → AddCircle (1 : ℝ)) :
    (phaseUnitary g).val = Matrix.diagonal fun j => circlePhase (g j) := rfl

/-- The phase unitaries form a homomorphic image of the torus. -/
theorem phaseUnitary_add (a b : Fin N → AddCircle (1 : ℝ)) :
    phaseUnitary (a + b) = phaseUnitary a * phaseUnitary b := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, phaseUnitary_val, phaseUnitary_val, phaseUnitary_val,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  rw [Pi.add_apply, circlePhase_add]

@[simp] theorem phaseUnitary_zero : phaseUnitary (0 : Fin N → AddCircle (1 : ℝ)) = 1 := by
  apply Subtype.ext
  rw [phaseUnitary_val, Submonoid.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext j
  rw [Pi.zero_apply, circlePhase_zero]

theorem continuous_phaseUnitary : Continuous (phaseUnitary (N := N)) := by
  refine Continuous.subtype_mk ?_ _
  exact Continuous.matrix_diagonal (continuous_pi fun j =>
    continuous_circlePhase.comp (continuous_apply j))

/-- The coordinates of a phase-rotated vector are the rotated coordinates. -/
lemma toEuclideanLin_phaseUnitary_apply (g : Fin N → AddCircle (1 : ℝ))
    (v : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    (Matrix.toEuclideanLin (phaseUnitary g).val v) j = circlePhase (g j) * v j := by
  show (Matrix.diagonal (fun j => circlePhase (g j)) *ᵥ v.ofLp) j = _
  exact Matrix.mulVec_diagonal _ _ j

/-- Phase rotation preserves every coordinate norm. -/
lemma norm_toEuclideanLin_phaseUnitary_apply (g : Fin N → AddCircle (1 : ℝ))
    (v : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    ‖(Matrix.toEuclideanLin (phaseUnitary g).val v) j‖ = ‖v j‖ := by
  rw [toEuclideanLin_phaseUnitary_apply, norm_mul, norm_circlePhase, one_mul]

/-- **The moment map does not see the base phases.** `momentMap (phaseUnitary g • p) = momentMap
p`: the phase torus moves a projective point along its moment fibre. -/
theorem momentMap_phaseUnitary_smul (g : Fin N → AddCircle (1 : ℝ)) (p : LF4.CPN N) (i : Fin N) :
    LF4.momentMap (phaseUnitary g • p) i = LF4.momentMap p i := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.smul_mk_eq_mk_toEuclideanLin, LF4.momentMap_mk, LF4.momentMap_mk,
      norm_toEuclideanLin_phaseUnitary_apply, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp_rw [norm_toEuclideanLin_phaseUnitary_apply]

/-- A phase rotation that acts by **different** phases on two coordinates where the vector
is supported moves the projective point. This is the concrete "base-moves" witness the
joint lift hands to its consumers. -/
theorem phaseUnitary_smul_mk_ne_of_ne (g : Fin N → AddCircle (1 : ℝ))
    {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) {j k : Fin N}
    (hj : v j ≠ 0) (hk : v k ≠ 0) (hg : circlePhase (g j) ≠ circlePhase (g k)) :
    phaseUnitary g • Projectivization.mk ℂ v hv ≠ Projectivization.mk ℂ v hv := by
  rw [Projectivization.smul_mk_eq_mk_toEuclideanLin]
  intro h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ hv).mp h
  have hj' := congrArg (fun w : EuclideanSpace ℂ (Fin N) => w j) ha
  have hk' := congrArg (fun w : EuclideanSpace ℂ (Fin N) => w k) ha
  simp only [toEuclideanLin_phaseUnitary_apply] at hj' hk'
  rw [WithLp.ofLp_smul, Pi.smul_apply, Units.smul_def, smul_eq_mul] at hj' hk'
  exact hg ((mul_right_cancel₀ hj hj').symm.trans (mul_right_cancel₀ hk hk'))

/-! ### Torus-invariant context fields -/

/-- A context field whose rates are constant along base phase rotations. This is the single
condition the joint lift needs of the context: the conserved quantities that steer the twist
must not themselves move under the twist. -/
def ContextField.TorusInvariant (c : ContextField N) : Prop :=
  ∀ (g : Fin N → AddCircle (1 : ℝ)) (p : LF4.CPN N) (j : Fin N),
    c.rate (phaseUnitary g • p) j = c.rate p j

/-- The moment context is torus-invariant. -/
theorem momentContext_torusInvariant : (momentContext N).TorusInvariant :=
  fun g p j => momentMap_phaseUnitary_smul g p j

/-! ### The arena torus and its action -/

/-- The `(N+1)`-torus of conserved-quantity symmetries: `N` base phases and one translation of
the register's conjugate coordinate `θ₂`. -/
abbrev ArenaTorus (N : ℕ) : Type := (Fin N → AddCircle (1 : ℝ)) × AddCircle (1 : ℝ)

/-- The torus action on the arena: rotate the base along its moment fibre, translate `θ₂`,
fix the register `θ₁` and the pointer. -/
noncomputable def torusAct (g : ArenaTorus N) (y : PointerArena N K) : PointerArena N K :=
  ((phaseUnitary g.1 • y.1.1, (y.1.2.1, y.1.2.2 + g.2)), y.2)

@[simp] lemma torusAct_fst_fst (g : ArenaTorus N) (y : PointerArena N K) :
    (torusAct g y).1.1 = phaseUnitary g.1 • y.1.1 := rfl

@[simp] lemma torusAct_register (g : ArenaTorus N) (y : PointerArena N K) :
    (torusAct g y).1.2.1 = y.1.2.1 := rfl

@[simp] lemma torusAct_conjugate (g : ArenaTorus N) (y : PointerArena N K) :
    (torusAct g y).1.2.2 = y.1.2.2 + g.2 := rfl

@[simp] lemma torusAct_snd (g : ArenaTorus N) (y : PointerArena N K) :
    (torusAct g y).2 = y.2 := rfl

@[simp] theorem torusAct_zero (y : PointerArena N K) : torusAct (0 : ArenaTorus N) y = y := by
  unfold torusAct
  rw [Prod.fst_zero, Prod.snd_zero, phaseUnitary_zero, one_smul, add_zero]

/-- The action law: `torusAct a ∘ torusAct b = torusAct (a + b)`. -/
theorem torusAct_add (a b : ArenaTorus N) (y : PointerArena N K) :
    torusAct a (torusAct b y) = torusAct (a + b) y := by
  unfold torusAct
  rw [Prod.fst_add, Prod.snd_add, phaseUnitary_add, mul_smul, add_assoc, add_comm b.2 a.2]

/-- The action is jointly continuous. -/
theorem continuous_torusAct :
    Continuous (Function.uncurry (torusAct (N := N) (K := K))) := by
  unfold Function.uncurry torusAct
  refine Continuous.prodMk (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)) ?_
  · exact (continuous_phaseUnitary.comp (continuous_fst.comp continuous_fst)).smul
      (continuous_fst.comp (continuous_fst.comp continuous_snd))
  · exact continuous_fst.comp (continuous_snd.comp (continuous_fst.comp continuous_snd))
  · exact (continuous_snd.comp (continuous_snd.comp (continuous_fst.comp continuous_snd))).add
      (continuous_snd.comp continuous_fst)
  · exact continuous_snd.comp continuous_snd

/-- The action is jointly measurable — the hypothesis `MeasurePreserving.vadd_twist_of_invariant`
asks for. -/
theorem measurable_torusAct :
    Measurable (Function.uncurry (torusAct (N := N) (K := K))) :=
  haveI : OpensMeasurableSpace (ArenaTorus N × PointerArena N K) := Prod.opensMeasurableSpace
  continuous_torusAct.measurable

/-- **Every torus element preserves the arena Liouville measure.** Fubini–Study is unitarily
invariant; Haar measure on the register torus is translation invariant; the pointer factor
is untouched. -/
theorem torusAct_measurePreserving (g : ArenaTorus N) (p₀ : LF4.CPN N) (q₀ : Pointer K) :
    MeasurePreserving (torusAct g) (pointerLiouville p₀ q₀) (pointerLiouville p₀ q₀) := by
  have hbase : MeasurePreserving (fun p : LF4.CPN N => phaseUnitary g.1 • p)
      (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
    ⟨(continuous_const_smul _).measurable, fubiniStudyMeasure_smul_invariant _ _⟩
  have htor : MeasurePreserving (Prod.map (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
      (fun θ : AddCircle (1 : ℝ) => θ + g.2)) (volume : Measure LF4.KTorus) volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id _).prod (measurePreserving_add_right _ g.2)
  have h : torusAct g = Prod.map (Prod.map (fun p : LF4.CPN N => phaseUnitary g.1 • p)
      (Prod.map (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))
        (fun θ : AddCircle (1 : ℝ) => θ + g.2))) (id : Pointer K → Pointer K) := by
    funext y; rfl
  rw [h]
  unfold pointerLiouville LF4.kMuL
  exact (hbase.prod htor).prod (MeasurePreserving.id _)

/-- Haar measure on the arena torus is the product of the coordinate Haar measures. -/
noncomputable def torusHaar (N : ℕ) : Measure (ArenaTorus N) :=
  (volume : Measure (Fin N → AddCircle (1 : ℝ))).prod (volume : Measure (AddCircle (1 : ℝ)))

instance : (torusHaar N).IsAddLeftInvariant := Measure.prod.instIsAddLeftInvariant

instance : IsProbabilityMeasure (torusHaar N) := by
  unfold torusHaar
  infer_instance

end CSD.RecordLayer

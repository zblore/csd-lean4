/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.TwoWingFactorisation
public import CsdLean4.LF6.LocalDeisolationFlow
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Congr

/-!
# The de-isolation flow **is** the wing-factorised flow

**Category:** 3-Local (CV; the instantiation BACKLOG #139 was left owing).
BACKLOG #139, second half; closes #131's two-dynamics gap.

[`TwoWingFactorisation.lean`](TwoWingFactorisation.lean) proved the cone for *any* wing-factorised
flow and instantiated it at `CompositeArena`'s `leftOp`/`rightOp`. What it did **not** do was plug in
`LF6.localFlowUnitary` itself — the index alignment was checked by hand and left as a claim about
conventions. This file formalises it, so "the cone comes from the measurement interaction" stops
being a reading of two index conventions and becomes a theorem.

## The alignment, written out

`LF6.jointFlowEquiv` is `jointDilEquiv.trans finProdFinEquiv`, and `jointDilEquiv`'s **source** is
`(sys_A ⊗ ptr_A) ⊗ (sys_B ⊗ ptr_B)` — per wing. So `localFlowUnitary` is a per-wing Kronecker
product `U_A ⊗ U_B` wearing a `Fin (4 * 4)` label. On the CV side `FieldConfig 4 2 = Fin 4 → Fin 2`
is four two-level modes. The identification is three steps, each already in the corpus:

* `wingIndexEquiv` — `FieldConfig 2 2 ≃ Fin 2 × Fin 2` (`piFinTwoEquiv`): a two-mode configuration
  *is* a (system, pointer) pair;
* `wingSplitEquiv` — `FieldConfig 4 2 ≃ (Fin 2 × Fin 2) × (Fin 2 × Fin 2)`, which is
  `CompositeArena.configSplit` followed by that, per wing;
* `configFlowEquiv` — the whole way across to `Fin (4 * 4)`, by composing with `jointFlowEquiv`.

Then:

* ★★★ `reindex_localFlowUnitary_eq_joinU` — **the de-isolation flow, read on the four-mode
  configuration space, is exactly `CompositeArena`'s product unitary `joinU wingU wingU`.** The
  `jointFlowEquiv` cancels against its own inverse, and what is left is the Kronecker product read
  through `configSplit` — which is what `compositeReindex` is;
* ★★★ `joinU_wingU_eq_mul` — and that product is the product of its two wing factors, so it
  satisfies the hypothesis of `TwoWingFactorisation`'s theorems;
* ★★★ `arenaObs_kick_deisolation` and ★★★ `recordStroke_comm_kick_deisolation` — **a B-wing
  intervention cannot steer A's reading or A's record write, at every power of the de-isolation
  flow**. No graph, no period count, and no second interaction: the cone is the measurement's own.

## What this closes, and what it does not

**#131's two-dynamics gap closes.** Causal separation and the Born/record/CHSH statements are now
about the *same interaction*: `localFlowUnitary`, up to the index relabelling written out above. The
experiment no longer takes its causal structure from one dynamics and its statistics from another.

⚠️ **Locality is still assumed, just once and physically.** `localDeisolation_factorises` holds by
construction — LF6-A.3 chose a product dilation — so what is derived is "the cone follows from the
product form", not "the product form follows from anything". Deriving *that* is `R-016`, untouched.

⚠️ **One thread remains, and it is about the projective action, not about which dynamics.** These
statements are about `arenaKick` of the pulled-back unitary on `FieldArena 4 2`;
`LF6.localDeisolationFlow` is `localFlowUnitary • ·` on `CPN (4 * 4)`. Those agree up to
[`ArenaIndexBridge.lean`](ArenaIndexBridge.lean)'s `arenaEquiv`, and the identity
`arenaKick (pullback) = arenaEquiv.symm ∘ localDeisolationFlow ∘ arenaEquiv` is **not proved here**.
It is bookkeeping about a projective action, with no choice left in it, and it is what a capstone
would need; it is recorded on #139 rather than claimed.

⚠️ **Static, not propagating** — inherited from `TwoWingFactorisation`: a product unitary gives
disjoint-support commutation, not a velocity. [`TwoWingCone.lean`](TwoWingCone.lean) keeps the graded
version for a coupled dynamics.

References: [`TwoWingFactorisation.lean`](TwoWingFactorisation.lean)
(`supportedOn_heisenberg_pow_of_factorised`, `arenaObs_kick_of_factorised`,
`recordStroke_comm_kick_of_factorised`, `leftModes_two_two`),
[`CompositeArena.lean`](CompositeArena.lean) (`configSplit`, `compositeReindex`, `joinU`, `leftU`,
`rightU`, `leftOp_mul_rightOp`, `leftOp_supportedOn`),
[`TwoWingCone.lean`](TwoWingCone.lean) (`wingAModes`, `wingBModes`),
`LF6/LocalDeisolationFlow.lean` (`localFlowUnitary`, `jointFlowEquiv`, `jointDilEquiv`,
`localDeisolation_factorises`), `LF5`'s `vnUnitary`;
`specs/BACKLOG.md` #139, #131, `R-016`.
-/

@[expose] public section

open Matrix
open scoped Kronecker

noncomputable section

namespace CSD.CV

/-! ### The alignment -/

/-- **A two-mode configuration is a (system, pointer) pair.** -/
def wingIndexEquiv : FieldConfig 2 2 ≃ Fin 2 × Fin 2 := piFinTwoEquiv _

/-- **The four-mode configuration space, split per wing** into the de-isolation's own index: modes
`0,1` are A's (system, pointer) and modes `2,3` are B's. -/
def wingSplitEquiv : FieldConfig 4 2 ≃ (Fin 2 × Fin 2) × (Fin 2 × Fin 2) :=
  (configSplit (K₁ := 2) (K₂ := 2) (N := 2)).trans
    (wingIndexEquiv.prodCongr wingIndexEquiv)

/-- **All the way across**, to the `Fin (4 * 4)` label `LF6` works in. -/
def configFlowEquiv : FieldConfig 4 2 ≃ Fin (4 * 4) :=
  wingSplitEquiv.trans LF6.jointFlowEquiv

/-- A per-wing unitary, read on a two-mode configuration space. -/
noncomputable def wingU : Matrix.unitaryGroup (FieldConfig 2 2) ℂ :=
  ⟨Matrix.reindex wingIndexEquiv.symm wingIndexEquiv.symm (LF5.vnUnitary 2),
   LF5.reindex_mem_unitaryGroup wingIndexEquiv.symm LF5.vnUnitary_mem_unitaryGroup⟩

theorem wingU_apply (c d : FieldConfig 2 2) :
    wingU.val c d = LF5.vnUnitary 2 (wingIndexEquiv c) (wingIndexEquiv d) := rfl

/-! ### The de-isolation flow is the product unitary -/

/-- ★★★ **The de-isolation flow, read on the four-mode configuration space, IS
`CompositeArena`'s product unitary.** The `jointFlowEquiv` cancels against its own inverse and what
is left is the per-wing Kronecker product read through `configSplit` — which is exactly what
`compositeReindex` does. So the measurement interaction and the composite arena's product dynamics
are the same matrix. -/
theorem reindex_localFlowUnitary_eq_joinU :
    Matrix.reindex configFlowEquiv.symm configFlowEquiv.symm LF6.localFlowUnitary.val
      = (joinU (K₁ := 2) (K₂ := 2) wingU wingU).val := by
  ext c d
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    LF6.localFlowUnitary, joinU, configFlowEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, wingSplitEquiv, Equiv.prodCongr_apply,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply]
  rw [compositeReindex_apply, Matrix.kroneckerMap_apply, wingU_apply, wingU_apply]
  rfl

/-! ### The two wing factors -/

/-- The A-wing factor of the de-isolation flow, as a unitary on the four-mode space.
(`CompositeArena` packages `rightU` but not its mirror, so both are spelled out here.) -/
noncomputable def wingLeftU : Matrix.unitaryGroup (FieldConfig 4 2) ℂ :=
  joinU (K₁ := 2) (K₂ := 2) wingU 1

/-- The B-wing factor. -/
noncomputable def wingRightU : Matrix.unitaryGroup (FieldConfig 4 2) ℂ :=
  joinU (K₁ := 2) (K₂ := 2) 1 wingU

theorem wingLeftU_val : wingLeftU.val = leftOp (K₂ := 2) wingU.val := rfl

theorem wingRightU_val : wingRightU.val = rightOp (K₁ := 2) wingU.val := rfl

/-- ★★★ **A product unitary is the product of its two wing factors**, so the de-isolation flow meets
the hypothesis of `TwoWingFactorisation`'s theorems. -/
theorem joinU_wingU_eq_mul :
    joinU (K₁ := 2) (K₂ := 2) wingU wingU = wingLeftU * wingRightU := by
  refine Subtype.ext ?_
  show compositeReindex (wingU.val ⊗ₖ wingU.val)
      = leftOp (K₂ := 2) wingU.val * rightOp (K₁ := 2) wingU.val
  rw [leftOp_mul_rightOp]

theorem supportedOn_wingAModes_wingLeftU : SupportedOn wingAModes wingLeftU.val := by
  rw [wingLeftU_val]
  exact supportedOn_wingAModes_leftOp wingU.val

theorem supportedOn_wingBModes_wingRightU : SupportedOn wingBModes wingRightU.val := by
  rw [wingRightU_val]
  exact supportedOn_wingBModes_rightOp wingU.val

/-- ★★ **The flow the next two theorems are about is the de-isolation flow**, read on the four-mode
configuration space. -/
theorem wingLeftU_mul_wingRightU_eq_reindex_localFlowUnitary :
    (wingLeftU * wingRightU).val
      = Matrix.reindex configFlowEquiv.symm configFlowEquiv.symm LF6.localFlowUnitary.val := by
  rw [reindex_localFlowUnitary_eq_joinU, joinU_wingU_eq_mul]

/-! ### The cone, for the de-isolation flow itself -/

/-- ★★★ **A B-wing intervention cannot steer A's reading, at every power of the de-isolation
flow.** The cone is the measurement interaction's own: no coupling graph is supplied and no period
budget is tracked, because the interaction does not couple the wings at all. -/
theorem arenaObs_kick_deisolation
    {A : Matrix (FieldConfig 4 2) (FieldConfig 4 2) ℂ} (hA : SupportedOn wingAModes A)
    {W : Matrix.unitaryGroup (FieldConfig 4 2) ℂ} (hW : SupportedOn wingBModes W.val)
    (n : ℕ) (p : FieldArena 4 2) :
    arenaObs (heisenberg ((wingLeftU * wingRightU) ^ n) A) (arenaKick W p)
      = arenaObs (heisenberg ((wingLeftU * wingRightU) ^ n) A) p :=
  arenaObs_kick_of_factorised disjoint_wingModes hA
    supportedOn_wingAModes_wingLeftU supportedOn_wingBModes_wingRightU n hW p

/-- ★★★ **And it cannot steer A's record write.** This is #131's causal-separation property with its
causal structure read off the *measurement*, which closes that row's two-dynamics gap. -/
theorem recordStroke_comm_kick_deisolation
    {A : Matrix (FieldConfig 4 2) (FieldConfig 4 2) ℂ} (hA : SupportedOn wingAModes A)
    {W : Matrix.unitaryGroup (FieldConfig 4 2) ℂ} (hW : SupportedOn wingBModes W.val)
    (n : ℕ) (g : ℝ → RecordFibre) (x : FibredFieldArena 4 2) :
    recordStroke (heisenberg ((wingLeftU * wingRightU) ^ n) A) g (fibredKick W x)
      = fibredKick W (recordStroke (heisenberg ((wingLeftU * wingRightU) ^ n) A) g x) :=
  recordStroke_comm_kick_of_factorised disjoint_wingModes hA
    supportedOn_wingAModes_wingLeftU supportedOn_wingBModes_wingRightU n hW g x

/-! ### The arena identification intertwines the two actions

The theorems above are about `arenaKick` of the pulled-back unitary on `FieldArena 4 2`, while
`LF6.localDeisolationFlow` acts on `CPN (4 * 4)`. This section closes that last thread: the aligned
arena identification carries one to the other, so the CV statements and the `LF6` statements are
about the same map and not merely the same space. -/

/-- The identification of the **state spaces**, aligned with the de-isolation's own wing split. (Not
`ArenaIndexBridge`'s `fieldSpaceEquiv`, whose index change is an arbitrary
`Fintype.equivFinOfCardEq` and therefore carries no wing structure.) -/
noncomputable def flowFieldSpaceEquiv :
    EuclideanSpace ℂ (FieldConfig 4 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (4 * 4)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ configFlowEquiv

/-- **The aligned arena identification**: the CV field arena and the projective space `LF6` works
in, identified so that the wing split is respected. -/
noncomputable def flowArenaEquiv : FieldArena 4 2 ≃ LF4.CPN (4 * 4) :=
  Projectivization.congr flowFieldSpaceEquiv.toLinearEquiv

theorem flowFieldSpaceEquiv_apply (v : EuclideanSpace ℂ (FieldConfig 4 2)) (i : Fin (4 * 4)) :
    flowFieldSpaceEquiv v i = v (configFlowEquiv.symm i) := rfl

/-- ★★ **The pulled-back unitary acts as the de-isolation unitary, through the identification.**
A coordinate computation: reindexing the matrix and reindexing the vector cancel, the sum being
reindexed by `configFlowEquiv`. -/
theorem flowFieldSpaceEquiv_toEuclideanLin (v : EuclideanSpace ℂ (FieldConfig 4 2)) :
    flowFieldSpaceEquiv (Matrix.toEuclideanLin (wingLeftU * wingRightU).val v)
      = Matrix.toEuclideanLin LF6.localFlowUnitary.val (flowFieldSpaceEquiv v) := by
  ext i
  have hW : ∀ (c d : FieldConfig 4 2), (wingLeftU * wingRightU).val c d
      = LF6.localFlowUnitary.val (configFlowEquiv c) (configFlowEquiv d) := by
    intro c d
    rw [wingLeftU_mul_wingRightU_eq_reindex_localFlowUnitary]
    simp [Matrix.reindex_apply]
  show ((wingLeftU * wingRightU).val *ᵥ (fun k => v k)) (configFlowEquiv.symm i)
    = (LF6.localFlowUnitary.val *ᵥ (fun k => flowFieldSpaceEquiv v k)) i
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp configFlowEquiv
    (fun j => LF6.localFlowUnitary.val i j * flowFieldSpaceEquiv v j)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hW, Equiv.apply_symm_apply, flowFieldSpaceEquiv_apply, Equiv.symm_apply_apply]

/-- ★★★ **The identification intertwines the CV kick with the de-isolation flow.** So every
statement proved above about `arenaKick (wingLeftU * wingRightU)` is a statement about
`LF6.localDeisolationFlow`, transported — the CV cone and the `LF6` Born/record/CHSH statements are
about the **same map**, not merely the same space.

This is the last thread #131 was carrying. -/
theorem flowArenaEquiv_arenaKick (p : FieldArena 4 2) :
    flowArenaEquiv (arenaKick (wingLeftU * wingRightU) p)
      = LF6.localDeisolationFlow (flowArenaEquiv p) := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [arenaKick_mk, flowArenaEquiv, Projectivization.congr_apply,
        Projectivization.congr_apply, Projectivization.map_mk, Projectivization.map_mk,
        LF6.localDeisolationFlow, Projectivization.smul_mk_eq_mk_toEuclideanLin]
      refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
      rw [one_smul]
      exact (flowFieldSpaceEquiv_toEuclideanLin v).symm

end CSD.CV

end

end

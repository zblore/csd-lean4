/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.TwoWingCone
public import CsdLean4.LF4.KahlerInstance
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Congr

/-!
# One arena: the field arena **is** `Σ`, up to the index of its configurations

**Category:** 3-Local (CV; the bridge BACKLOG #133 is about).
BACKLOG #133, and the last structural gap in #131.

#131 asks for four properties "within the *same* dynamical model". Three of them — Born weights,
record stability, no-signalling, and the CHSH violation — are statements about `LF4.KSigma 16`. The
fourth, causal separation ([`TwoWingCone.lean`](TwoWingCone.lean)), is a statement about
`FibredFieldArena 4 2`. Those are the same space: `FieldConfig 4 2 = Fin 4 → Fin 2` has `16`
elements. But "the same space" was, until now, a remark — there was no map, because
`Projectivization.map` has no inverse and the corpus had no equivalence of projectivizations.

[`Congr.lean`](../Mathlib/LinearAlgebra/Projectivization/Congr.lean) supplies that, and this file
uses it.

* `configEquiv K N` — `FieldConfig K N ≃ Fin (N ^ K)`, the index change, from
  `Fintype.equivFinOfCardEq`;
* `fieldSpaceEquiv K N` — the induced **linear isometry** of the state spaces, through
  `LinearIsometryEquiv.piLpCongrLeft`, so norms and inner products are untouched;
* ★★★ `arenaEquiv K N : FieldArena K N ≃ LF4.CPN (N ^ K)` — **the field arena and LF4's projective
  space are one arena**, with ★ `continuous_arenaEquiv` and ★ `measurable_arenaEquiv`;
* ★★★ `fibredArenaEquiv K N : FibredFieldArena K N ≃ LF4.KSigma (N ^ K)` — and so are the fibred
  arena and `Σ`. The fibre needs no transport at all: `CV.RecordFibre` and `LF4.KTorus` are the
  **same type**;
* `twoWingArenaEquiv : FibredFieldArena 4 2 ≃ LF4.KSigma 16` — the instance #131 needs;
* `sigmaRecordStroke`, `sigmaFibredKick` — the CV record write and the CV mode-local intervention,
  **transported to `Σ`**, with ★★★ `sigmaRecordStroke_comm_sigmaFibredKick_twoWing`: a B-wing
  intervention cannot steer A's record write, **as a statement about `Σ`**, at every period count.

## What this buys, stated exactly

⚠️ **The transported operations are *defined* through the equivalence**, so
`sigmaRecordStroke_comm_sigmaFibredKick_twoWing` is `TwoWingCone`'s theorem conjugated, and no new
mathematics is in it. What it buys is the one thing #131 was missing: **all four properties are now
statements about `LF4.KSigma 16`**, so "within the same dynamical model" is a fact about the
corpus rather than a remark about two spaces being isomorphic.

⚠️ **It does not identify CV's record write with the record layer's own.** `recordStroke` is a
base-dependent shift of the fibre read through an arena observable; `RecordLayer.sigmaShift` is a
constant translation of the record coordinate. They are different maps and this file does not claim
otherwise — `sigmaRecordStroke` is the *former*, carried across.

⚠️ **No measure preservation is claimed.** `measurable_arenaEquiv` says the identification is
measurable, not that it carries `fsMeasure` to `fsMeasure` or `epistemicMeasure` to
`epistemicMeasure`. The transported statements here are **pointwise**, which is why they need
nothing more; a measure-theoretic statement crossing the bridge would need that lemma first, and it
is not in this file.

⚠️ **The CV arena API is still `FieldConfig`-indexed.** #133 also asks for `arenaObs`, `arenaDM`,
`arenaKick` and `SupportedOn` to be *generalised* over the index type, which would let the CV
notions themselves be read on `Σ` rather than transported wholesale. That is not done here, and it
is the difference between "one arena" (this file) and "one API" (the rest of the row).

References: [`Congr.lean`](../Mathlib/LinearAlgebra/Projectivization/Congr.lean)
(`Projectivization.congr`, the piece this needed),
[`TwoWingCone.lean`](TwoWingCone.lean) (`recordStroke_comm_kick_twoWing`, the statement transported),
[`FibredArenaBridge.lean`](FibredArenaBridge.lean) (`FibredFieldArena`, `RecordFibre`,
`recordStroke`, `fibredKick`), [`ArenaBridge.lean`](ArenaBridge.lean) (`FieldArena`),
[`FieldModes.lean`](FieldModes.lean) (`FieldConfig`),
`LF4/KahlerInstance.lean` (`CPN`, `KSigma`, `KTorus`);
`specs/BACKLOG.md` #133, #131; `specs/two-wing-experiment-scoping.md` §3.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace CSD.CV

/-! ### The index change -/

/-- **The configuration space is a `Fin (N ^ K)`**: there are `N ^ K` ways to assign one of `N`
levels to each of `K` modes. -/
def configEquiv (K N : ℕ) : FieldConfig K N ≃ Fin (N ^ K) :=
  Fintype.equivFinOfCardEq (by simp)

/-- **The induced linear isometry of state spaces.** An index change is an isometry, so norms and
inner products — and therefore every Born weight — are untouched by it. -/
noncomputable def fieldSpaceEquiv (K N : ℕ) :
    EuclideanSpace ℂ (FieldConfig K N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N ^ K)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (configEquiv K N)

/-! ### One arena -/

/-- ★★★ **The field arena and LF4's projective space are one arena.** The equivalence is the index
change, lifted to the projectivization by `Projectivization.congr`. -/
noncomputable def arenaEquiv (K N : ℕ) : FieldArena K N ≃ LF4.CPN (N ^ K) :=
  Projectivization.congr (fieldSpaceEquiv K N).toLinearEquiv

theorem continuous_arenaEquiv (K N : ℕ) : Continuous (arenaEquiv K N) :=
  Projectivization.congr_continuous _ (fieldSpaceEquiv K N).continuous

theorem measurable_arenaEquiv (K N : ℕ) : Measurable (arenaEquiv K N) :=
  (continuous_arenaEquiv K N).measurable

/-- ★★★ **And the fibred arena is `Σ`.** The fibre needs no transport whatever: `CV.RecordFibre` and
`LF4.KTorus` are the same type, both `AddCircle 1 × AddCircle 1`. -/
noncomputable def fibredArenaEquiv (K N : ℕ) :
    FibredFieldArena K N ≃ LF4.KSigma (N ^ K) :=
  (arenaEquiv K N).prodCongr (Equiv.refl RecordFibre)

theorem measurable_fibredArenaEquiv (K N : ℕ) : Measurable (fibredArenaEquiv K N) :=
  (measurable_arenaEquiv K N).prodMap measurable_id

/-- **The two-wing experiment's arena**: `FieldConfig 4 2` has `2 ^ 4 = 16` configurations, so the
CV arena of four modes at two levels **is** `Σ = ℂℙ¹⁵ × T²`. -/
noncomputable def twoWingArenaEquiv : FibredFieldArena 4 2 ≃ LF4.KSigma 16 :=
  fibredArenaEquiv 4 2

/-! ### The cone theorems, as statements about `Σ` -/

/-- **The CV record write, transported to `Σ`.** -/
noncomputable def sigmaRecordStroke (A : Matrix (FieldConfig 4 2) (FieldConfig 4 2) ℂ)
    (g : ℝ → RecordFibre) (y : LF4.KSigma 16) : LF4.KSigma 16 :=
  twoWingArenaEquiv (recordStroke A g (twoWingArenaEquiv.symm y))

/-- **A CV mode-local intervention, transported to `Σ`.** -/
noncomputable def sigmaFibredKick (W : Matrix.unitaryGroup (FieldConfig 4 2) ℂ)
    (y : LF4.KSigma 16) : LF4.KSigma 16 :=
  twoWingArenaEquiv (fibredKick W (twoWingArenaEquiv.symm y))

/-- ★★★ **A B-wing intervention cannot steer A's record write — on `Σ`.** This is
`recordStroke_comm_kick_twoWing` carried across the arena identification, and it is the statement
#131 needed: the causal-separation property now lives on `LF4.KSigma 16`, the same space as the Born
weights, the record stability bound and the CHSH violation.

⚠️ The transported operations are *defined* through `twoWingArenaEquiv`, so this contains no new
mathematics. What it establishes is that the four properties of #131 are about **one** space. -/
theorem sigmaRecordStroke_comm_sigmaFibredKick_twoWing (τ lam : ℝ)
    (gc : Fin 4 × Fin 4 → Fin 2 → Fin 2 → ℝ)
    {A : Matrix (FieldConfig 4 2) (FieldConfig 4 2) ℂ} (hA : SupportedOn wingAModes A)
    {W : Matrix.unitaryGroup (FieldConfig 4 2) ℂ} (hW : SupportedOn wingBModes W.val)
    (n : ℕ) (g : ℝ → RecordFibre) (y : LF4.KSigma 16) :
    sigmaRecordStroke (heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) A) g
        (sigmaFibredKick W y)
      = sigmaFibredKick W
        (sigmaRecordStroke (heisenberg (graphInteractingU 4 2 τ lam twoWingGraph gc ^ n) A) g y) := by
  show twoWingArenaEquiv (recordStroke _ g (twoWingArenaEquiv.symm
      (twoWingArenaEquiv (fibredKick W (twoWingArenaEquiv.symm y)))))
    = twoWingArenaEquiv (fibredKick W (twoWingArenaEquiv.symm
      (twoWingArenaEquiv (recordStroke _ g (twoWingArenaEquiv.symm y)))))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact congrArg twoWingArenaEquiv
    (recordStroke_comm_kick_twoWing τ lam gc hA hW n g (twoWingArenaEquiv.symm y))

end CSD.CV

end

end

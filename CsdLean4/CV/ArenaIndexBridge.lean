/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.TwoWingCone
public import CsdLean4.LF4.KahlerInstance
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Congr
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.ReindexTrace
public import CsdLean4.LF5.MeasurementFlow

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

▸ **The CV arena API was generalised 2026-10-12** ([`ArenaBridge.lean`](ArenaBridge.lean)):
`arenaObs`, `arenaDM` and `arenaKick` read over any finite index through `GenArena`, so the CV
notions are now stated on `Σ` rather than transported wholesale. ~~That is not done here~~ —
and the transport section below closes the row's remaining half, so "one arena" and "one API" are
no longer different things. ⚠️ `SupportedOn` is the exception and **cannot** be generalised:
its content is that an operator leaves the modes outside a region alone, which needs the index to
*be* a function space. Nothing below is stated for it.

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


/-! ### Transport along an index equivalence

#133's second half, and the piece that turns "one arena" into "one reading".
[`ArenaBridge.lean`](ArenaBridge.lean)'s `GenArena` made the CV vocabulary index-generic, so a
reading can be *stated* over either index. What follows lets it be **carried**: an index
equivalence transports rays (`idxArenaEquiv`), operators (`Matrix.reindex`) and unitaries
(`idxUnitary`), and the arena observable is **invariant** under the transport, so a number read on
one arena is the same number on the other rather than a number related to it.

The specific equivalence of the previous section is an instance of this one on the nose:
`arenaEquiv K N = idxArenaEquiv (configEquiv K N)` by `rfl` (★ `arenaEquiv_eq_idxArenaEquiv`),
which is what makes the generic lemmas apply to the field-arena-is-`Σ` identification without a
second construction. -/

section Transport

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The index change as a **linear isometry** of state spaces, over an arbitrary finite index. -/
noncomputable def idxSpaceEquiv (e : ι ≃ κ) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma idxSpaceEquiv_apply (e : ι ≃ κ) (v : EuclideanSpace ℂ ι) (k : κ) :
    idxSpaceEquiv e v k = v (e.symm k) := rfl

omit [DecidableEq ι] [DecidableEq κ] in
lemma idxSpaceEquiv_ne_zero (e : ι ≃ κ) {v : EuclideanSpace ℂ ι} (hv : v ≠ 0) :
    idxSpaceEquiv e v ≠ 0 := fun h =>
  hv ((idxSpaceEquiv e).injective (by rw [h, map_zero]))

/-- ★★★ **The arena transported along an index equivalence.** -/
noncomputable def idxArenaEquiv (e : ι ≃ κ) : GenArena ι ≃ GenArena κ :=
  Projectivization.congr (idxSpaceEquiv e).toLinearEquiv

omit [DecidableEq ι] [DecidableEq κ] in
lemma idxArenaEquiv_mk (e : ι ≃ κ) {v : EuclideanSpace ℂ ι} (hv : v ≠ 0) :
    idxArenaEquiv e (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (idxSpaceEquiv e v) (idxSpaceEquiv_ne_zero e hv) := rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- The transported ray, through the canonical representative. -/
lemma idxArenaEquiv_eq_mk (e : ι ≃ κ) (p : GenArena ι) :
    idxArenaEquiv e p = Projectivization.mk ℂ (idxSpaceEquiv e p.rep)
      (idxSpaceEquiv_ne_zero e (Projectivization.rep_nonzero p)) := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  rfl

/-- **The transported unitary**: relabel the matrix, which stays unitary. -/
def idxUnitary (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup κ ℂ :=
  ⟨Matrix.reindex e e U.val, LF5.reindex_mem_unitaryGroup e U.property⟩

@[simp] lemma idxUnitary_val (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    (idxUnitary e U).val = Matrix.reindex e e U.val := rfl

/-! #### The density, the observable and the kick -/

omit [DecidableEq ι] [DecidableEq κ] in
/-- The unit representative is **relabelled, not rescaled**: an index change is an isometry, so the
normalisation is the same number on both sides. -/
lemma unitVec_idxSpaceEquiv (e : ι ≃ κ) (v : EuclideanSpace ℂ ι) (k : κ) :
    unitVec (idxSpaceEquiv e v) k = unitVec v (e.symm k) := by
  have hn : ‖idxSpaceEquiv e v‖ = ‖v‖ := (idxSpaceEquiv e).norm_map v
  simp only [unitVec, hn, idxSpaceEquiv_apply]

omit [DecidableEq ι] [DecidableEq κ] in
/-- ★★ **The rank-one density is reindexed.** -/
lemma dmVec_idxSpaceEquiv (e : ι ≃ κ) (v : EuclideanSpace ℂ ι) :
    dmVec (idxSpaceEquiv e v) = Matrix.reindex e e (dmVec v) := by
  ext k l
  rw [dmVec_apply, Matrix.reindex_apply, Matrix.submatrix_apply, dmVec_apply,
    unitVec_idxSpaceEquiv, unitVec_idxSpaceEquiv]

omit [DecidableEq ι] [DecidableEq κ] in
/-- ★★ **The density of a transported ray is the reindexed density.** -/
lemma arenaDM_idxArenaEquiv (e : ι ≃ κ) (p : GenArena ι) :
    arenaDM (idxArenaEquiv e p) = Matrix.reindex e e (arenaDM p) := by
  rw [idxArenaEquiv_eq_mk e p,
    arenaDM_mk (idxSpaceEquiv_ne_zero e (Projectivization.rep_nonzero p)),
    dmVec_idxSpaceEquiv]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- ★★★ **Arena observables transport.** Reading the reindexed operator on the transported ray
gives the same real number, so a CV reading is *carried* between arenas rather than merely stated
over either. The proof is the two facts a relabelling has: it is multiplicative
(`Matrix.reindex_mul`) and it fixes the trace (`Matrix.trace_reindex`). -/
theorem arenaObs_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (p : GenArena ι) :
    arenaObs (Matrix.reindex e e A) (idxArenaEquiv e p) = arenaObs A p := by
  simp only [arenaObs, arenaDM_idxArenaEquiv, Matrix.reindex_mul, Matrix.trace_reindex]

/-- The reindexed matrix acting on a transported vector is the transport of the action. -/
lemma toEuclideanLin_reindex (e : ι ≃ κ) (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (Matrix.reindex e e M) (idxSpaceEquiv e v)
      = idxSpaceEquiv e (Matrix.toEuclideanLin M v) := by
  refine PiLp.ext fun k => ?_
  rw [toEuclideanLin_coord, idxSpaceEquiv_apply, toEuclideanLin_coord]
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    idxSpaceEquiv_apply]
  exact Equiv.sum_comp e.symm fun j => M (e.symm k) j * v j

/-- ★★★ **Unitary kicks transport.** The relabelled kick on the transported ray is the
transport of the kick, so a CV intervention and its image on the other arena are one map read two
ways. -/
theorem arenaKick_reindex (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) (p : GenArena ι) :
    arenaKick (idxUnitary e U) (idxArenaEquiv e p) = idxArenaEquiv e (arenaKick U p) := by
  have hv : p.rep ≠ 0 := Projectivization.rep_nonzero p
  have hne : idxSpaceEquiv e p.rep ≠ 0 := idxSpaceEquiv_ne_zero e hv
  have hR : idxArenaEquiv e (arenaKick U p)
      = Projectivization.mk ℂ (idxSpaceEquiv e (Matrix.toEuclideanLin U.val p.rep))
          (idxSpaceEquiv_ne_zero e (toEuclideanLin_ne_zero U hv)) :=
    idxArenaEquiv_mk e (toEuclideanLin_ne_zero U hv)
  rw [idxArenaEquiv_eq_mk e p, arenaKick_mk (idxUnitary e U) hne, hR]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul, idxUnitary_val, toEuclideanLin_reindex]

end Transport

/-! ### The field arena, through the generic transport

The previous section's `arenaEquiv` is the generic one at the configuration index, so the transport
lemmas apply to it with no second construction. -/

/-- ★ **The two halves of #133 are one construction.** -/
theorem arenaEquiv_eq_idxArenaEquiv (K N : ℕ) :
    arenaEquiv K N = idxArenaEquiv (configEquiv K N) := rfl

/-- ★★★ **A CV reading, carried to `Σ`.** The expectation of a field operator in a field ray
is the expectation of the relabelled operator in the corresponding ray of `LF4.CPN (N ^ K)` — the
same real number, not a number related to it by an unproved identification. -/
theorem arenaObs_arenaEquiv (K N : ℕ) (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (p : FieldArena K N) :
    arenaObs (Matrix.reindex (configEquiv K N) (configEquiv K N) A) (arenaEquiv K N p)
      = arenaObs A p :=
  arenaObs_reindex _ A p

/-- ★★ **And a CV intervention, carried to `Σ`.** -/
theorem arenaKick_arenaEquiv (K N : ℕ) (U : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (p : FieldArena K N) :
    arenaKick (idxUnitary (configEquiv K N) U) (arenaEquiv K N p)
      = arenaEquiv K N (arenaKick U p) :=
  arenaKick_reindex _ U p

end CSD.CV

end

end

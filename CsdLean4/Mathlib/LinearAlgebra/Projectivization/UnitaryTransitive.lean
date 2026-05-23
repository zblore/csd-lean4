import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Unitary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Transitivity of the matrix unitary group action on complex projective space

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

Proves that `Matrix.unitaryGroup (Fin N) ℂ` acts transitively on
`ℙ ℂ (EuclideanSpace ℂ (Fin N))` for `[NeZero N]`, via the standard
orthonormal-basis-extension construction.

## Argument

1. For any unit vector `v`, extend `{v}` to an orthonormal basis `b_v`
   indexed by `Fin N` with `b_v 0 = v` (via
   `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`).

2. The change-of-basis matrix `M_v := b_std.toBasis.toMatrix b_v.toBasis`
   (where `b_std = EuclideanSpace.basisFun (Fin N) ℂ`) is unitary
   (via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`) and
   has first column equal to `v`.

3. Applying `M_v` to the standard basis vector `e_0` recovers `v`.

4. For two unit vectors `v, w`, the composition `M_w * M_v⁻¹` is a
   unitary that maps `v ↦ w`. Lifted to projective space, this gives
   transitivity (any two projective points are related by a unitary,
   after normalisation of representatives).

## Main result

`Matrix.UnitaryGroup.instIsPretransitive_projectivization` — the
`IsPretransitive` instance for the matrix unitary group on `ℂℙ^(N-1)`.

## Provenance

Staged as upstream Mathlib material. Intended location:
`Mathlib/LinearAlgebra/Projectivization/UnitaryTransitive.lean`.

## Tags

projectivization, unitary group, transitive action, orthonormal basis
-/

open Matrix
open scoped LinearAlgebra.Projectivization

namespace Matrix.UnitaryGroup

variable {N : ℕ}

/-! ## Step 1 — unitary with prescribed first column -/

/-- Build a unitary matrix from an orthonormal basis: the matrix whose
columns are the coordinates of the basis vectors in the standard basis. -/
private noncomputable def unitaryOfONB (b : OrthonormalBasis (Fin N) ℂ
      (EuclideanSpace ℂ (Fin N))) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin N) ℂ).toBasis.toMatrix b.toBasis,
   (EuclideanSpace.basisFun (Fin N) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

/-- The matrix `unitaryOfONB b`, applied to the standard basis vector
`e_j`, recovers `b j`. -/
private lemma unitaryOfONB_apply_single (b : OrthonormalBasis (Fin N) ℂ
      (EuclideanSpace ℂ (Fin N))) (j : Fin N) :
    (Matrix.toEuclideanLin (unitaryOfONB b).val) (EuclideanSpace.single j (1 : ℂ))
      = b j := by
  ext i
  show ((Matrix.toEuclideanLin (unitaryOfONB b).val)
          (EuclideanSpace.single j (1 : ℂ))).ofLp i = (b j).ofLp i
  -- toEuclideanLin M v reduces to (M *ᵥ v.ofLp) componentwise
  show (((unitaryOfONB b).val) *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp) i
        = (b j).ofLp i
  -- (single j 1).ofLp = Pi.single j 1
  have h_sng : ((EuclideanSpace.single j (1 : ℂ)).ofLp : Fin N → ℂ)
                = Pi.single j (1 : ℂ) :=
    WithLp.ofLp_toLp _ _
  rw [h_sng, Matrix.mulVec_single]
  simp only [MulOpposite.op_one, one_smul, Matrix.col_apply]
  -- Goal: ((unitaryOfONB b).val) i j = (b j).ofLp i
  show (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.toMatrix b.toBasis i j
       = (b j).ofLp i
  rw [Module.Basis.toMatrix_apply,
      (EuclideanSpace.basisFun (Fin N) ℂ).coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
  rfl

/-- For any unit vector `v`, there exists a unitary matrix whose action
on the standard basis vector `e_0` is `v`. -/
lemma exists_unitary_e_zero_eq [NeZero N]
    (v : EuclideanSpace ℂ (Fin N)) (hv : ‖v‖ = 1) :
    ∃ M : Matrix.unitaryGroup (Fin N) ℂ,
      (Matrix.toEuclideanLin M.val) (EuclideanSpace.single 0 (1 : ℂ)) = v := by
  -- Build a single-element "orthonormal subset" {v} indexed via s = {0} ⊂ Fin N.
  let s : Set (Fin N) := {0}
  let f : Fin N → EuclideanSpace ℂ (Fin N) := fun i => if i = 0 then v else 0
  have hf_orth : Orthonormal ℂ (s.restrict f) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, (hi : i = 0)⟩ ⟨j, (hj : j = 0)⟩
    subst hi; subst hj
    simp only [Set.restrict_apply, if_true, f]
    rw [inner_self_eq_norm_sq_to_K, hv]
    simp
  have card_eq : Module.finrank ℂ (EuclideanSpace ℂ (Fin N))
                  = Fintype.card (Fin N) :=
    finrank_euclideanSpace
  obtain ⟨b_v, hb_v⟩ :=
    hf_orth.exists_orthonormalBasis_extension_of_card_eq card_eq
  have hb_v_zero : b_v 0 = v := by
    have := hb_v 0 (by simp [s])
    simpa [f] using this
  refine ⟨unitaryOfONB b_v, ?_⟩
  rw [unitaryOfONB_apply_single, hb_v_zero]

/-- For any two unit vectors `v, w`, there exists a unitary matrix
`U ∈ Matrix.unitaryGroup (Fin N) ℂ` whose action on `v` is `w`. -/
lemma exists_unitary_map_unit [NeZero N]
    (v w : EuclideanSpace ℂ (Fin N)) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin N) ℂ,
      (Matrix.toEuclideanLin U.val) v = w := by
  obtain ⟨M_v, hM_v⟩ := exists_unitary_e_zero_eq v hv
  obtain ⟨M_w, hM_w⟩ := exists_unitary_e_zero_eq w hw
  refine ⟨M_w * M_v⁻¹, ?_⟩
  -- Rewrite v = M_v · e_0 (from hM_v), then collapse the matrix product.
  rw [← hM_v]
  -- Goal: toEuclideanLin (M_w * M_v⁻¹).val (toEuclideanLin M_v.val e_0) = w
  -- Compose via toLpLin_mul_same:
  --   toEuclideanLin A (toEuclideanLin B v) = toEuclideanLin (A * B) v
  -- Specifically: toEuclideanLin (M_w * M_v⁻¹).val (toEuclideanLin M_v.val e_0)
  --             = toEuclideanLin ((M_w * M_v⁻¹).val * M_v.val) e_0
  have h_collapse :
      Matrix.toEuclideanLin (M_w * M_v⁻¹).val
          ((Matrix.toEuclideanLin M_v.val) (EuclideanSpace.single 0 (1 : ℂ)))
        = Matrix.toEuclideanLin ((M_w * M_v⁻¹).val * M_v.val)
            (EuclideanSpace.single 0 (1 : ℂ)) := by
    rw [Matrix.toLpLin_mul_same]; rfl
  rw [h_collapse]
  -- (M_w * M_v⁻¹).val * M_v.val = (M_w * M_v⁻¹ * M_v).val = M_w.val
  -- (by group axioms: M_v⁻¹ * M_v = 1)
  have h_simp : (M_w * M_v⁻¹).val * M_v.val = M_w.val := by
    rw [← Matrix.UnitaryGroup.mul_val, mul_assoc, inv_mul_cancel,
        mul_one]
  rw [h_simp]
  exact hM_w

/-- A unitary matrix's `toEuclideanLin` action preserves non-zero. -/
private lemma toEuclideanLin_unitary_ne_zero
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    (Matrix.toEuclideanLin U.val) v ≠ 0 := by
  intro h
  apply hv
  exact (toEuclideanLinearEquiv U).injective (h.trans (LinearEquiv.map_zero _).symm)

/-- For any two nonzero vectors `v, w`, there exists a unitary matrix
`U` and a nonzero complex scalar `c` with `(toEuclideanLin U.val) v = c • w`. -/
lemma exists_unitary_mapping_nonzero [NeZero N]
    {v w : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ (U : Matrix.unitaryGroup (Fin N) ℂ) (c : ℂ), c ≠ 0 ∧
      (Matrix.toEuclideanLin U.val) v = c • w := by
  -- Normalise both vectors.
  have hv_norm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hw_norm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hv_norm_cx : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv_norm
  have hw_norm_cx : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw_norm
  have hw_norm_inv_cx : ((‖w‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_inv]
    exact inv_ne_zero hw_norm_cx
  set v' : EuclideanSpace ℂ (Fin N) := ((‖v‖⁻¹ : ℝ) : ℂ) • v with v'_def
  set w' : EuclideanSpace ℂ (Fin N) := ((‖w‖⁻¹ : ℝ) : ℂ) • w with w'_def
  have hv' : ‖v'‖ = 1 := by
    rw [v'_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv)), inv_mul_cancel₀ hv_norm]
  have hw' : ‖w'‖ = 1 := by
    rw [w'_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hw)), inv_mul_cancel₀ hw_norm]
  obtain ⟨U, hU⟩ := exists_unitary_map_unit v' w' hv' hw'
  refine ⟨U, ((‖v‖ : ℂ) * (‖w‖⁻¹ : ℂ)), ?_, ?_⟩
  · -- c ≠ 0
    exact mul_ne_zero hv_norm_cx (inv_ne_zero hw_norm_cx)
  · -- (toEuclideanLin U.val) v = c • w
    have h_v_recover : v = ((‖v‖ : ℝ) : ℂ) • v' := by
      rw [v'_def, ← smul_assoc, smul_eq_mul, Complex.ofReal_inv,
          mul_inv_cancel₀ hv_norm_cx, one_smul]
    calc (Matrix.toEuclideanLin U.val) v
        = (Matrix.toEuclideanLin U.val) (((‖v‖ : ℝ) : ℂ) • v') := by
            conv_lhs => rw [h_v_recover]
      _ = ((‖v‖ : ℝ) : ℂ) • (Matrix.toEuclideanLin U.val) v' := by
            rw [map_smul]
      _ = ((‖v‖ : ℝ) : ℂ) • w' := by rw [hU]
      _ = ((‖v‖ : ℝ) : ℂ) • (((‖w‖⁻¹ : ℝ) : ℂ) • w) := rfl
      _ = (((‖v‖ : ℝ) : ℂ) * ((‖w‖⁻¹ : ℝ) : ℂ)) • w := by rw [smul_smul]
      _ = ((‖v‖ : ℂ) * (‖w‖⁻¹ : ℂ)) • w := by rw [Complex.ofReal_inv]

/-- For unitary `U` and nonzero `v`, the projective action is given by
`mk` of the matrix action on `v`. Both sides reduce to the same
`Quotient.mk''` term by definitional unfolding of `MulAction.compHom`,
`mapEquiv`, and `Projectivization.map`. -/
lemma smul_mk_eq_mk [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : EuclideanSpace ℂ (Fin N)) (hv : v ≠ 0) :
    U • Projectivization.mk ℂ v hv
      = Projectivization.mk ℂ ((Matrix.toEuclideanLin U.val) v)
          (toEuclideanLin_unitary_ne_zero U hv) :=
  rfl

/-- **Transitivity of the matrix unitary group action on `ℂℙ^(N-1)`.**
For any two projective points, there is a unitary mapping one to the other. -/
instance instIsPretransitive_projectivization [NeZero N] :
    MulAction.IsPretransitive (Matrix.unitaryGroup (Fin N) ℂ)
      (ℙ ℂ (EuclideanSpace ℂ (Fin N))) where
  exists_smul_eq p q := by
    obtain ⟨U, c, hc, hUv⟩ :=
      exists_unitary_mapping_nonzero p.rep_nonzero q.rep_nonzero
    refine ⟨U, ?_⟩
    -- Goal: U • p = q. Rewrite both sides via mk_rep.
    conv_lhs => rw [← p.mk_rep]
    conv_rhs => rw [← q.mk_rep]
    rw [smul_mk_eq_mk]
    -- Goal: mk ℂ ((toEuclideanLin U.val) p.rep) (...) = mk ℂ q.rep q.rep_nonzero
    -- Use hUv : (toEuclideanLin U.val) p.rep = c • q.rep, then mk_eq_mk_iff' with a := c.
    -- The `rw` form trips the motive check (the `mk`'s non-vanishing proof is
    -- proof-irrelevant but Lean can't abstract); apply `.mpr` directly.
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _
            (hUv ▸ toEuclideanLin_unitary_ne_zero U p.rep_nonzero)
            q.rep_nonzero).mpr ⟨c, hUv.symm⟩

end Matrix.UnitaryGroup

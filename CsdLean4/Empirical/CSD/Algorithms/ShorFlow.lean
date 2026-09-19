/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Algorithms.CircuitFlow
public import CsdLean4.Empirical.QM.Algorithms.ShorCore
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Empirical/CSD: Shor's period finding as a flow on `Σ`

**Category:** 3-Local (CSD-side twin of `Empirical/QM/Algorithms/ShorCore.lean`).

`ShorCore.lean` proves the order-finding circuit on the QM side: on the joint register
`Fin T × ZMod N`, the modular-exponentiation oracle followed by the inverse Fourier transform on
the counting register sends the prepared state `uniformCount ⊗ |1⟩` to a state whose counting
register reads each multiple `s·(T/r)` of the order's phase with probability `1/r`, and nothing
else (`shor_order_distribution`, `shor_order_distribution_zero`, the ideal case `r ∣ T`). This
file is the same circuit on the CSD side: the oracle is the permutation matrix of
`(c, y) ↦ (c, (a^c)⁻¹ y)`, the inverse Fourier transform is the Kronecker factor `(qftMatrix T)ᴴ ⊗ 1`,
their product is a `Circuit` and hence a **flow on the joint register's sector**, and the readout
of the counting register is the union of the record basins of the joint outcomes `(c, y)` over
the work register.

* `modexpPerm a`, `modexpMatrix a` — the oracle as a permutation and its matrix, with
  `toEuclideanLin_modexpMatrix` (it acts as `jointModexp`) and `permMatrix_conjTranspose_mul`
  (a permutation matrix is unitary);
* `qftInvJoint` — the inverse Fourier transform on the counting register as a matrix on the
  joint register, with `toEuclideanLin_qftInvJoint` (it acts as `qftInvCount`) and
  `qftInvJoint_conjTranspose_mul`;
* `shorCircuit a : Circuit (Fin T × ZMod N)` — **period finding as a circuit**, hence
  `(shorCircuit a).flow` is **period finding as a `Σ`-flow**; `shorReady`, the prepared state as
  a point of the sector (`initialState_norm`);
* ★★ `shor_flow_born_count` — **Shor on `Σ`**: at the point reached from the ready point by the
  flow, the counting-register readout `s·(T/r)` — the union over the work register of the record
  basins of the joint outcomes — has Born weight `1/r`; and ★ `shor_flow_born_count_zero`, the
  other counting outcomes have weight `0`.

⚠️ **Honest scope.** The QM-side theorems carry the mathematics, in the ideal case `r ∣ T`; this
file adds the ontic reading and no new analysis. The circuit is one unitary; no gate
decomposition of the modular exponentiation and no Hamiltonian generating it is modelled
(`R-015`). The classical post-processing (continued fractions, the random base) is
`ShorRecovery.lean` / `ShorCapstone.lean` on the QM side and is not restated here.

References: `Empirical/QM/Algorithms/ShorCore.lean`; `Empirical/CSD/Algorithms/CircuitFlow.lean`;
`specs/BACKLOG.md` #34; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped LinearAlgebra.Projectivization ComplexConjugate Kronecker

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Algorithms

open CSD.LF2 CSD.LF4 CSD.RecordLayer CSD.Empirical.QM.Shor

/-! ### Permutation matrices are unitary -/

section Perm

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
/-- The conjugate transpose of a permutation matrix is its transpose (its entries are `0` and
`1`). -/
theorem permMatrix_conjTranspose (σ : Equiv.Perm κ) :
    (σ.permMatrix ℂ)ᴴ = (σ.permMatrix ℂ)ᵀ := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, apply_ite]

omit [Fintype κ] in
/-- The transpose of a permutation matrix is the matrix of the inverse permutation. -/
theorem permMatrix_transpose (σ : Equiv.Perm κ) :
    (σ.permMatrix ℂ)ᵀ = σ⁻¹.permMatrix ℂ := by
  rw [Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, ← PEquiv.toMatrix_symm, Equiv.Perm.inv_def,
    Equiv.toPEquiv_symm]

/-- A permutation matrix is unitary. -/
theorem permMatrix_conjTranspose_mul (σ : Equiv.Perm κ) :
    (σ.permMatrix ℂ)ᴴ * σ.permMatrix ℂ = 1 := by
  rw [permMatrix_conjTranspose, permMatrix_transpose, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

end Perm

variable {N : ℕ} [NeZero N] (T : ℕ) [NeZero T] (a : (ZMod N)ˣ)

/-! ### The oracle and the inverse Fourier transform as matrices -/

/-- The permutation `(c, y) ↦ (c, (a^c)⁻¹ · y)` whose pullback is the modular-exponentiation
oracle `jointModexp`. -/
noncomputable def modexpPerm : Equiv.Perm (Fin T × ZMod N) :=
  Equiv.prodShear (Equiv.refl (Fin T)) fun c => Units.mulLeft ((a ^ (c : ℕ))⁻¹)

omit [NeZero N] [NeZero T] in
theorem modexpPerm_apply (p : Fin T × ZMod N) :
    modexpPerm T a p = (p.1, (((a ^ (p.1 : ℕ))⁻¹ : (ZMod N)ˣ) : ZMod N) * p.2) :=
  rfl

/-- **The oracle as a matrix**: the permutation matrix of `modexpPerm`. -/
noncomputable def modexpMatrix : Matrix (Fin T × ZMod N) (Fin T × ZMod N) ℂ :=
  (modexpPerm T a).permMatrix ℂ

omit [NeZero T] in
/-- The oracle matrix acts as `jointModexp`. -/
theorem toEuclideanLin_modexpMatrix (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) :
    Matrix.toEuclideanLin (modexpMatrix T a) Φ = jointModexp T a Φ := by
  ext ⟨c, y⟩
  simp [Matrix.toLpLin_apply, modexpMatrix, Matrix.permMatrix_mulVec, modexpPerm_apply,
    jointModexp_apply]

/-- **The inverse Fourier transform on the counting register as a matrix on the joint
register**: `(qftMatrix T)ᴴ ⊗ 1`. -/
noncomputable def qftInvJoint : Matrix (Fin T × ZMod N) (Fin T × ZMod N) ℂ :=
  (qftMatrix T)ᴴ ⊗ₖ (1 : Matrix (ZMod N) (ZMod N) ℂ)

omit [NeZero T] in
/-- The joint inverse-Fourier matrix acts as `qftInvCount`. -/
theorem toEuclideanLin_qftInvJoint (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) :
    Matrix.toEuclideanLin (qftInvJoint T (N := N)) Φ = qftInvCount T Φ := by
  ext ⟨c, y⟩
  simp [Matrix.toLpLin_apply, qftInvJoint, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, qftInvCount_apply]

/-- The joint inverse-Fourier matrix is unitary. -/
theorem qftInvJoint_conjTranspose_mul :
    (qftInvJoint T (N := N))ᴴ * qftInvJoint T = 1 := by
  rw [qftInvJoint, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    mul_eq_one_comm.mp (qft_unitary T), Matrix.one_kronecker_one]

/-! ### Period finding as a circuit and as a flow -/

/-- **Shor's period-finding circuit as a matrix**: the oracle, then the inverse Fourier transform
on the counting register. -/
noncomputable def shorMatrix : Matrix (Fin T × ZMod N) (Fin T × ZMod N) ℂ :=
  qftInvJoint T * modexpMatrix T a

omit [NeZero T] in
/-- The circuit matrix acts as the circuit. -/
theorem toEuclideanLin_shorMatrix (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) :
    Matrix.toEuclideanLin (shorMatrix T a) Φ = qftInvCount T (jointModexp T a Φ) := by
  rw [shorMatrix, toEuclideanLin_mul_apply', toEuclideanLin_modexpMatrix, toEuclideanLin_qftInvJoint]

/-- The circuit matrix is unitary. -/
theorem shorMatrix_conjTranspose_mul : (shorMatrix T a)ᴴ * shorMatrix T a = 1 := by
  rw [shorMatrix, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (qftInvJoint T)ᴴ,
    qftInvJoint_conjTranspose_mul, Matrix.one_mul, modexpMatrix, permMatrix_conjTranspose_mul]

/-- **Period finding as a circuit** on the joint register. -/
noncomputable def shorCircuit : Circuit (Fin T × ZMod N) :=
  ⟨shorMatrix T a, shorMatrix_conjTranspose_mul T a⟩

theorem shorCircuit_U : (shorCircuit T a).U = shorMatrix T a :=
  rfl

/-- The prepared state `uniformCount ⊗ |1⟩` is a unit vector. -/
theorem initialState_norm : ‖initialState T (N := N)‖ = 1 := by
  have hT : (0 : ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  have hcoord : ∀ p : Fin T × ZMod N,
      initialState T (N := N) p = (Real.sqrt T : ℂ)⁻¹ * (if p.2 = 1 then 1 else 0) := by
    rintro ⟨c, y⟩
    rw [initialState, tensorCN_apply, uniformCount, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      sum_coord, Finset.sum_eq_single c (fun x _ hx => by rw [basisState_apply, if_neg hx.symm])
        (fun h => absurd (Finset.mem_univ _) h), basisState_apply, if_pos rfl, mul_one,
      basisState_apply]
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, EuclideanSpace.norm_sq_eq]
  simp_rw [hcoord]
  rw [Fintype.sum_prod_type]
  simp only [apply_ite norm, norm_zero, apply_ite (· ^ 2),
    zero_pow two_ne_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hT.le]
  exact mul_inv_cancel₀ hT.ne'

theorem initialState_ne_zero : initialState T (N := N) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [initialState_norm]; exact one_ne_zero)

/-- The prepared state, enumerated. -/
noncomputable def shorReadyVec : EuclideanSpace ℂ (Fin (Fintype.card (Fin T × ZMod N))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idx (Fin T × ZMod N)) (initialState T (N := N))

theorem shorReadyVec_norm : ‖shorReadyVec T (N := N)‖ = 1 := by
  rw [shorReadyVec, LinearIsometryEquiv.norm_map, initialState_norm]

theorem shorReadyVec_ne_zero : shorReadyVec T (N := N) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [shorReadyVec_norm]; exact one_ne_zero)

/-- **The ready point**: the prepared state `uniformCount ⊗ |1⟩` as a point of the sector. -/
noncomputable def shorReady : RegisterSector (Fin T × ZMod N) :=
  Projectivization.mk ℂ (shorReadyVec T (N := N)) (shorReadyVec_ne_zero T)

/-- The Born weight of the joint outcome `(c, y)`'s basin at the flowed ready point is the
circuit's output amplitude squared. -/
theorem shor_flow_born (c : Fin T) (y : ZMod N) :
    epistemicMeasure ((shorCircuit T a).flow (shorReady T))
        (globalBasin (momentContext (Fintype.card (Fin T × ZMod N))) (idx (Fin T × ZMod N) (c, y)))
      = ENNReal.ofReal (‖qftInvCount T (postModexpState T a) (c, y)‖ ^ 2) := by
  rw [show (shorCircuit T a).flow (shorReady T) = (shorCircuit T a).flow^[1] (shorReady T) from rfl,
    shorReady, Circuit.epistemicMeasure_globalBasin_flow_iterate _ _ _ _ (shorReadyVec_norm T),
    pow_one, Circuit.coe_toUnitaryGroup, shorReadyVec, toEuclideanLin_reindex_piLpCongrLeft,
    piLpCongrLeft_apply_apply, shorCircuit_U, toEuclideanLin_shorMatrix, jointModexp_initial]

/-- ★★ **Shor on `Σ`.** In the ideal case `r ∣ T`, at the point reached from the ready point by
the flow, the counting-register outcome `s·(T/r)` — the union over the work register of the
record basins of the joint outcomes `(s·(T/r), y)` — has Born weight `1/r`. -/
theorem shor_flow_born_count (hr : 0 < ord a) (hT : 0 < T) (hdvd : ord a ∣ T) (s : Fin (ord a)) :
    ∑ y : ZMod N, epistemicMeasure ((shorCircuit T a).flow (shorReady T))
        (globalBasin (momentContext (Fintype.card (Fin T × ZMod N)))
          (idx (Fin T × ZMod N) (⟨(s : ℕ) * (T / ord a), bridgeIndex_lt hr hT hdvd s⟩, y)))
      = ENNReal.ofReal ((ord a : ℝ)⁻¹) := by
  simp_rw [shor_flow_born]
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity,
    ← shor_order_distribution a T hr hT hdvd s, probCount, probLeft]

/-- ★ **The other counting outcomes have weight zero on `Σ`.** -/
theorem shor_flow_born_count_zero (hr : 0 < ord a) (hT : 0 < T) (hdvd : ord a ∣ T) (c : Fin T)
    (hc : ∀ s : Fin (ord a), (c : ℕ) ≠ (s : ℕ) * (T / ord a)) :
    ∑ y : ZMod N, epistemicMeasure ((shorCircuit T a).flow (shorReady T))
        (globalBasin (momentContext (Fintype.card (Fin T × ZMod N))) (idx (Fin T × ZMod N) (c, y)))
      = 0 := by
  simp_rw [shor_flow_born]
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, ENNReal.ofReal_eq_zero]
  exact le_of_eq (by rw [← probLeft, ← probCount, shor_order_distribution_zero a T hr hT hdvd c hc])

end Algorithms
end CSDBridge
end Empirical
end CSD

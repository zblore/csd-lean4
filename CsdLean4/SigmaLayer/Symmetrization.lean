import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.Module

/-!
# SigmaLayer/Symmetrization: the two-particle symmetrization postulate (identical particles)

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle / exchange-statistics pillar.

For two identical particles the joint Hilbert space is `H ⊗ H`, realised concretely as
`EuclideanSpace ℂ (Fin N × Fin N)` (functions on ordered pairs). Particle EXCHANGE is the `swap` operator
`(swap x)(i,j) = x(j,i)`. This module builds the symmetrization postulate at `n = 2`:

* `swap` is a self-adjoint involution (`swap_involutive`, `swap_isSymmetric`) — a genuine `±1`-valued
  exchange observable;
* the symmetric/antisymmetric projectors `symProj = ½(1 + swap)`, `antisymProj = ½(1 − swap)` are
  complementary orthogonal projections summing to the identity (`symProj_idem`, `antisymProj_idem`,
  `symProj_antisymProj`, `symProj_add_antisymProj`, and symmetry of each);
* the **exchange dichotomy**: the symmetric subspace is exactly the `+1` eigenspace of `swap` and the
  antisymmetric subspace the `−1` eigenspace (`swap_eq_self_iff`, `swap_eq_neg_iff`), and the two intersect
  only in `0` (`eq_zero_of_swap_self_and_neg`) — so `H ⊗ H = Sym ⊕ Anti` (bosons ⊕ fermions);
* **Pauli exclusion**: a product state of two particles in the SAME single-particle state `v` has zero
  antisymmetric component, `antisymProj (v ⊗ v) = 0` (`antisymProj_tprod_self`) — no two fermions occupy
  the same state.

This is the finite-dimensional `n = 2` core of the symmetrization postulate (the exchange-statistics
pillar); the general-`n` symmetric group action / exterior-power Fock structure is a further extension.

References: `SigmaLayer/TensorReconstruction.lean` (composite two-system structure); `specs/future-work.md`
(identical-particle statistics). Uses Mathlib `LinearIsometryEquiv.piLpCongrLeft`,
`LinearMap.IsSymmetric`.
-/

open scoped InnerProductSpace

namespace CSD.SigmaLayer

variable {N : ℕ}

/-- The two-particle Hilbert space `H ⊗ H` for `H = ℂ^N`, realised as functions on ordered pairs. -/
abbrev TwoParticle (N : ℕ) : Type := EuclideanSpace ℂ (Fin N × Fin N)

/-- **Particle exchange as a linear isometry.** The unitary that swaps the two tensor factors,
`(x)(i,j) ↦ x(j,i)`, from `Equiv.prodComm` via `piLpCongrLeft`. -/
noncomputable def exchangeEquiv (N : ℕ) : TwoParticle N ≃ₗᵢ[ℂ] TwoParticle N :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm (Fin N) (Fin N))

/-- **The exchange (swap) operator.** Particle exchange as an endomorphism of `H ⊗ H`. -/
noncomputable def swap (N : ℕ) : TwoParticle N →ₗ[ℂ] TwoParticle N :=
  (exchangeEquiv N).toLinearMap

theorem exchangeEquiv_symm : (exchangeEquiv N).symm = exchangeEquiv N := by
  rw [exchangeEquiv, LinearIsometryEquiv.piLpCongrLeft_symm, Equiv.prodComm_symm]

theorem exchangeEquiv_involutive (x : TwoParticle N) : exchangeEquiv N (exchangeEquiv N x) = x := by
  have h := (exchangeEquiv N).symm_apply_apply x
  rwa [exchangeEquiv_symm] at h

/-- **Exchange is an involution:** swapping twice is the identity (`swap² = 1`). -/
@[simp] theorem swap_involutive (x : TwoParticle N) : swap N (swap N x) = x :=
  exchangeEquiv_involutive x

/-- **Exchange is self-adjoint:** a self-inverse unitary, so `swap† = swap`. Hence the exchange
observable has real (`±1`) spectrum. -/
theorem swap_isSymmetric : (swap N).IsSymmetric := fun x y => by
  show inner ℂ (exchangeEquiv N x) y = inner ℂ x (exchangeEquiv N y)
  rw [← (exchangeEquiv N).inner_map_map x (exchangeEquiv N y), exchangeEquiv_involutive]

/-! ### The symmetric and antisymmetric projectors -/

/-- **The symmetric (bosonic) projector** `½(1 + swap)`. -/
noncomputable def symProj (N : ℕ) : TwoParticle N →ₗ[ℂ] TwoParticle N :=
  (1 / 2 : ℂ) • (LinearMap.id + swap N)

/-- **The antisymmetric (fermionic) projector** `½(1 − swap)`. -/
noncomputable def antisymProj (N : ℕ) : TwoParticle N →ₗ[ℂ] TwoParticle N :=
  (1 / 2 : ℂ) • (LinearMap.id - swap N)

@[simp] theorem symProj_apply (x : TwoParticle N) : symProj N x = (1 / 2 : ℂ) • (x + swap N x) := by
  simp [symProj]

@[simp] theorem antisymProj_apply (x : TwoParticle N) :
    antisymProj N x = (1 / 2 : ℂ) • (x - swap N x) := by
  simp [antisymProj]

theorem symProj_idem (x : TwoParticle N) : symProj N (symProj N x) = symProj N x := by
  simp only [symProj_apply, map_smul, map_add, swap_involutive]
  module

theorem antisymProj_idem (x : TwoParticle N) : antisymProj N (antisymProj N x) = antisymProj N x := by
  simp only [antisymProj_apply, map_smul, map_sub, swap_involutive]
  module

/-- The two projectors sum to the identity: every two-particle state splits into a symmetric and an
antisymmetric part. -/
theorem symProj_add_antisymProj (x : TwoParticle N) : symProj N x + antisymProj N x = x := by
  simp only [symProj_apply, antisymProj_apply]
  module

/-- The projectors are orthogonal (their product is zero): the symmetric and antisymmetric sectors are
complementary. -/
theorem symProj_antisymProj (x : TwoParticle N) : symProj N (antisymProj N x) = 0 := by
  simp only [antisymProj_apply, symProj_apply, map_smul, map_sub, swap_involutive]
  module

/-- Each projector is self-adjoint — so `Sym ⊕ Anti` is an ORTHOGONAL direct sum. -/
theorem symProj_isSymmetric : (symProj N).IsSymmetric :=
  (LinearMap.IsSymmetric.id.add swap_isSymmetric).smul (by simp [Complex.ext_iff])

theorem antisymProj_isSymmetric : (antisymProj N).IsSymmetric :=
  (LinearMap.IsSymmetric.id.sub swap_isSymmetric).smul (by simp [Complex.ext_iff])

/-! ### The exchange dichotomy: Sym = (+1)-eigenspace, Anti = (−1)-eigenspace -/

/-- **The symmetric subspace is the `+1` eigenspace of exchange:** a state is exchange-symmetric iff it is
fixed by `symProj` (a boson). -/
theorem swap_eq_self_iff (x : TwoParticle N) : swap N x = x ↔ symProj N x = x := by
  rw [symProj_apply]
  constructor
  · intro h; rw [h]; module
  · intro h
    have hx : swap N x = (2 : ℂ) • ((1 / 2 : ℂ) • (x + swap N x)) - x := by module
    rw [h] at hx; rw [hx]; module

/-- **The antisymmetric subspace is the `−1` eigenspace of exchange:** a state is exchange-antisymmetric
iff it is fixed by `antisymProj` (a fermion). -/
theorem swap_eq_neg_iff (x : TwoParticle N) : swap N x = -x ↔ antisymProj N x = x := by
  rw [antisymProj_apply]
  constructor
  · intro h; rw [h]; module
  · intro h
    have hx : swap N x = x - (2 : ℂ) • ((1 / 2 : ℂ) • (x - swap N x)) := by module
    rw [h] at hx; rw [hx]; module

/-- **The two sectors meet only in `0`:** no nonzero state is both exchange-symmetric and
exchange-antisymmetric. With `symProj_add_antisymProj`, this makes `H ⊗ H = Sym ⊕ Anti` a genuine direct
sum (bosons ⊕ fermions). -/
theorem eq_zero_of_swap_self_and_neg (x : TwoParticle N) (h1 : swap N x = x) (h2 : swap N x = -x) :
    x = 0 := by
  have h2x : (2 : ℂ) • x = 0 := by
    rw [two_smul]; nth_rewrite 2 [← h1]; rw [h2, add_neg_cancel]
  exact (smul_eq_zero.mp h2x).resolve_left (by norm_num)

/-! ### Product states and Pauli exclusion -/

/-- **A product (unentangled) two-particle state** `v ⊗ w`: `(i,j) ↦ vᵢ wⱼ`. -/
noncomputable def tprod (v w : EuclideanSpace ℂ (Fin N)) : TwoParticle N :=
  (WithLp.equiv 2 (Fin N × Fin N → ℂ)).symm (fun p => v p.1 * w p.2)

@[simp] theorem tprod_apply (v w : EuclideanSpace ℂ (Fin N)) (p : Fin N × Fin N) :
    tprod v w p = v p.1 * w p.2 := rfl

theorem swap_apply (x : TwoParticle N) (p : Fin N × Fin N) : swap N x p = x (p.2, p.1) := by
  show exchangeEquiv N x p = x (p.2, p.1)
  rw [exchangeEquiv, LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

/-- **Exchange swaps the two factors of a product state:** `swap (v ⊗ w) = w ⊗ v`. -/
theorem swap_tprod (v w : EuclideanSpace ℂ (Fin N)) : swap N (tprod v w) = tprod w v := by
  ext p
  rw [swap_apply, tprod_apply, tprod_apply, mul_comm]

/-- **Pauli exclusion (`n = 2`).** A product state of two identical particles in the SAME single-particle
state `v` is exchange-symmetric, so its antisymmetric (fermionic) component vanishes:
`antisymProj (v ⊗ v) = 0`. No two fermions occupy the same state. -/
theorem antisymProj_tprod_self (v : EuclideanSpace ℂ (Fin N)) : antisymProj N (tprod v v) = 0 := by
  rw [antisymProj_apply, swap_tprod]
  module

end CSD.SigmaLayer

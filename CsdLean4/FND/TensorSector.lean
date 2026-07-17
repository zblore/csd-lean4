import CsdLean4.FND.CompositeInterface
import CsdLean4.Empirical.QM.NoCommunication

/-!
# FND/TensorSector: weaving the tensor product into the ledger

**Category:** 7-FND (the Choice A ontological layer).

How the composite/tensor structure sits in the base. The honest split is:

* **Derived (theorems, NOT posits).** The finite tensor product `ℂ^{NA} ⊗ ℂ^{NB}` is a genuine,
  constructible object: it is the Choice A sector on the PRODUCT index `Fin NA × Fin NB`, identified with
  `Fin (NA · NB)` by `finProdFinEquiv` (`tensorIndexEquiv`). On it the local operator algebra is real:
  Alice's `U ⊗ I` and Bob's `I ⊗ Q` commute (`aliceOp_bobOp_commute`), and Alice cannot signal to Bob
  (the operator-level no-signalling `CSD.Empirical.QM.NoCommunication.no_communication`). None of this is
  assumed; it follows from the Kronecker algebra.

* **Bridge B6 (dim `= NA·NB`) — now DERIVABLE, still a structure field here.** The reconstruction claim
  that a composite's Choice A sector IS this tensor sector with `dim = NA · NB` is
  `CompositeSector.tensor_dimension`, a named field. As of 2026-07-17 it is no longer *parked*: the
  abstract theorem `CSD.FND.compositeAlgReconstruction` (`FND/TensorReconstruction.lean`) PROVES that
  commuting local algebras `M_m, M_n` that GENERATE a composite `𝒜` force `𝒜 ≃ₐ M_m ⊗ M_n`, and
  `CSD.FND.composite_dim_eq` derives `k = m·n` for `𝒜 = M_k` — i.e. B6's dimension relation is a THEOREM
  under locality + generation. It remains a `CompositeSector` FIELD only because the sector interface has
  not yet been refactored to CONSTRUCT instances via the reconstruction (the residual bridge step); the
  by-hand entangled tier (singlet, GHZ, CGLMP on `Fin 2 × Fin 2`) still supplies the field per instance.

So tensors ARE woven in: the tensor product, its no-signalling algebra, AND now the composite-is-tensor
reconstruction are theorems; the only residue is threading `composite_dim_eq` into `CompositeSector`'s
constructor.
-/

open CSD.Empirical.QM
open Matrix

namespace CSD.FND

variable {m n : ℕ}

/-- **The finite tensor index equivalence.** `Fin NA × Fin NB ≃ Fin (NA · NB)` (`finProdFinEquiv`): the
joint Choice A sector `CP^{NA·NB−1}` is genuinely the tensor product `ℂ^{NA} ⊗ ℂ^{NB}`, realised on the
product index, not posited. -/
def tensorIndexEquiv (NA NB : ℕ) : Fin NA × Fin NB ≃ Fin (NA * NB) := finProdFinEquiv

/-- **The composite dimension is the tensor-product index.** For any composite sector, the posited
dimension relation `NA · NB = Njoint` (B6) transports the tensor index equivalence to
`Fin NA × Fin NB ≃ Fin Njoint`: the joint sector index IS the pair of party indices. This exhibits the
B6 posit as exactly the tensor-product identification. -/
def CompositeSector.tensorIndex {NA NB Njoint : ℕ} {Sigma : Type*} [MeasurableSpace Sigma]
    {D : ConstraintDynamics Sigma} (C : CompositeSector NA NB Njoint D) :
    Fin NA × Fin NB ≃ Fin Njoint :=
  (tensorIndexEquiv NA NB).trans (finCongr C.tensor_dimension)

/-- **The local operator algebra commutes (derived).** Alice's `U ⊗ I` and Bob's `I ⊗ Q` commute on the
bipartite tensor sector: `(U ⊗ I)(I ⊗ Q) = (I ⊗ Q)(U ⊗ I)`, both equal to `U ⊗ Q`. This is the algebraic
root of no-signalling, and it is a theorem of the Kronecker algebra, not a postulate. -/
theorem aliceOp_bobOp_commute (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) :
    NoCommunication.aliceOp U * NoCommunication.bobOp Q
      = NoCommunication.bobOp Q * NoCommunication.aliceOp (n := n) U := by
  unfold NoCommunication.aliceOp NoCommunication.bobOp
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul, one_mul, mul_one]

/-- **Operator-level no-signalling on the tensor sector (re-exposed).** Bob's expectation of `I ⊗ Q` is
unchanged by Alice's local unitary `U ⊗ I`: Alice cannot signal to Bob. This is the operator-form
companion of the singlet marginal `HasNoSignalling` (T15), on the genuine tensor sector. From
`NoCommunication.no_communication`. -/
theorem tensorSector_no_signalling (U : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ * U = 1) (ψ : EuclideanSpace ℂ (Fin m × Fin n)) :
    inner ℂ (Matrix.toEuclideanLin (NoCommunication.aliceOp U) ψ)
        (Matrix.toEuclideanLin (NoCommunication.bobOp Q)
          (Matrix.toEuclideanLin (NoCommunication.aliceOp U) ψ))
      = inner ℂ ψ (Matrix.toEuclideanLin (NoCommunication.bobOp Q) ψ) :=
  NoCommunication.no_communication U Q hU ψ

end CSD.FND

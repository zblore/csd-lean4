import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Empirical/QM: Quantum teleportation (E5)

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

Quantum teleportation (Bennett et al. 1993): Alice transmits an unknown qubit
`|ψ⟩ = α|0⟩ + β|1⟩` to Bob using one shared Bell pair `|Φ⁺⟩` and two classical
bits. Alice performs a Bell-basis measurement on her input qubit together with
her half of the entangled pair; the two-bit outcome tells Bob which of the four
Pauli corrections `{I, Z, X, ZX}` to apply to his half to recover `|ψ⟩`.

This file delivers the **algebraic core** — the branch-conditional form
(§0.1 QM-validity layer, branch-conditional reading; see `specs/qm-empirical-tests.md`):

1. `teleState_factorises` — the three-qubit input state is genuinely
   `|ψ⟩₁ ⊗ |Φ⁺⟩₂₃` (amplitude factorisation `Ψ(a,b,c) = ψ(a)·Φ⁺(b,c)`).
2. `teleportation_bell_expansion` — the teleportation identity: re-expanding in
   Alice's Bell basis on qubits (1,2),
   `Ψ = ½ Σₖ |Bellₖ⟩₁₂ ⊗ (Cₖ|ψ⟩)₃`, with `Cₖ ∈ {I, Z, X, XZ}` the Pauli image
   in branch `k`. So in each Bell-measurement branch Bob holds a Pauli image of
   `|ψ⟩`.
3. `teleportation_branch_recovers_input` — applying the branch correction recovers
   `|ψ⟩` exactly in all four branches (branch-conditional; the measurement-collapse /
   ¼-branch-probability layer is out of scope, see the honesty note below).

The three qubits live in `EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)` (matching
`Empirical/QM/Multipartite/GHZ.lean`), with qubit 1 = Alice's input, qubit 2 =
Alice's half of the pair, qubit 3 = Bob's half. This is the **dual** of
superdense coding (`Resources/SuperdenseCoding.lean`): there one entangled qubit
carries two classical bits; here two classical bits + one entangled qubit carry
one quantum state.

## Honesty note

This is the QM-validity layer in **branch-conditional** form: it proves the
Bell-basis expansion and per-branch recovery as exact algebraic identities. The
**measurement step proper** — collapsing the four-branch superposition to a single
classical outcome with probability ¼ each — is the measurement-update notion the
corpus does not yet have (the same LF5 obligation that gates BB84). The
no-signalling content ("Bob's marginal is `I/2` independent of the branch before
he learns the outcome") likewise needs the reduced-state / partial-trace
machinery absent from Mathlib; it is not asserted here.

## Source

Bennett, Brassard, Crépeau, Jozsa, Peres, Wootters 1993,
*Phys. Rev. Lett.* **70**, 1895. Experimental: Bouwmeester et al. 1997,
*Nature* **390**, 575.
-/

open Matrix ComplexConjugate

namespace CSD
namespace Empirical
namespace QM
namespace Teleportation

/-! ## States -/

/-- The input qubit `|ψ⟩ = α|0⟩ + β|1⟩ : EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def teleInput (α β : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 α + EuclideanSpace.single 1 β

/-- The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` on qubits (2,3). -/
noncomputable def bellPhiPlus : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single (0, 0) (1 : ℂ) + EuclideanSpace.single (1, 1) (1 : ℂ))

/-- `|Φ⁻⟩ = (|00⟩ − |11⟩)/√2`. -/
noncomputable def bellPhiMinus : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single (0, 0) (1 : ℂ) - EuclideanSpace.single (1, 1) (1 : ℂ))

/-- `|Ψ⁺⟩ = (|01⟩ + |10⟩)/√2`. -/
noncomputable def bellPsiPlus : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single (0, 1) (1 : ℂ) + EuclideanSpace.single (1, 0) (1 : ℂ))

/-- `|Ψ⁻⟩ = (|01⟩ − |10⟩)/√2`. -/
noncomputable def bellPsiMinus : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single (0, 1) (1 : ℂ) - EuclideanSpace.single (1, 0) (1 : ℂ))

/-- The full three-qubit input `|ψ⟩₁ ⊗ |Φ⁺⟩₂₃`, written out in components:
`(1/√2)(α|000⟩ + α|011⟩ + β|100⟩ + β|111⟩)`. (The tensor structure is verified
by `teleState_factorises`.) -/
noncomputable def teleState (α β : ℂ) : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single (0, 0, 0) α + EuclideanSpace.single (0, 1, 1) α
      + EuclideanSpace.single (1, 0, 0) β + EuclideanSpace.single (1, 1, 1) β)

/-! ## Bob's conditional vectors (the Pauli images of `|ψ⟩`) -/

/-- Branch `|Φ⁺⟩`: Bob holds `I|ψ⟩ = |ψ⟩`. -/
noncomputable def bobPhiPlus (α β : ℂ) : EuclideanSpace ℂ (Fin 2) := teleInput α β

/-- Branch `|Φ⁻⟩`: Bob holds `Z|ψ⟩ = α|0⟩ − β|1⟩`. -/
noncomputable def bobPhiMinus (α β : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 α + EuclideanSpace.single 1 (-β)

/-- Branch `|Ψ⁺⟩`: Bob holds `X|ψ⟩ = β|0⟩ + α|1⟩`. -/
noncomputable def bobPsiPlus (α β : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 β + EuclideanSpace.single 1 α

/-- Branch `|Ψ⁻⟩`: Bob holds `XZ|ψ⟩ = −β|0⟩ + α|1⟩`. -/
noncomputable def bobPsiMinus (α β : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (-β) + EuclideanSpace.single 1 α

/-! ## Pauli correction matrices -/

/-- Pauli `X = !![0, 1; 1, 0]`. (Not in `Gates/SingleQubit.lean`, which has only
`H, S, T, Z`.) -/
noncomputable def teleX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Z = !![1, 0; 0, −1]`. -/
noncomputable def teleZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The `|Ψ⁻⟩`-branch correction `ZX = !![0, 1; −1, 0]` (apply `X` then `Z`). -/
noncomputable def teleZX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-! ## Faithfulness: the input state is genuinely `|ψ⟩ ⊗ |Φ⁺⟩` -/

/-- The three-qubit amplitude factorises as `Ψ(a,b,c) = ψ(a)·Φ⁺(b,c)`, i.e.
`teleState` is the tensor product `|ψ⟩₁ ⊗ |Φ⁺⟩₂₃`. -/
theorem teleState_factorises (α β : ℂ) (a b c : Fin 2) :
    teleState α β (a, b, c) = teleInput α β a * bellPhiPlus (b, c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [teleState, teleInput, bellPhiPlus, EuclideanSpace.single] <;> ring

/-! ## The teleportation identity (Bell-basis expansion) -/

/-- **Teleportation identity.** Re-expanding the input `|ψ⟩₁ ⊗ |Φ⁺⟩₂₃` in Alice's
Bell basis on qubits (1,2):
`Ψ(a,b,c) = ½ ( Φ⁺(a,b)·(I|ψ⟩)(c) + Φ⁻(a,b)·(Z|ψ⟩)(c)
              + Ψ⁺(a,b)·(X|ψ⟩)(c) + Ψ⁻(a,b)·(XZ|ψ⟩)(c) )`.
So a Bell measurement on qubits (1,2) collapses Bob's qubit 3 to a Pauli image of
`|ψ⟩`, the image determined by the two-bit outcome. -/
theorem teleportation_bell_expansion (α β : ℂ) (a b c : Fin 2) :
    teleState α β (a, b, c)
      = (1 / 2 : ℂ) *
          (bellPhiPlus (a, b) * bobPhiPlus α β c
            + bellPhiMinus (a, b) * bobPhiMinus α β c
            + bellPsiPlus (a, b) * bobPsiPlus α β c
            + bellPsiMinus (a, b) * bobPsiMinus α β c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [teleState, bellPhiPlus, bellPhiMinus, bellPsiPlus, bellPsiMinus,
      bobPhiPlus, bobPhiMinus, bobPsiPlus, bobPsiMinus, teleInput,
      EuclideanSpace.single] <;>
    ring

/-! ## Per-branch recovery -/

/-- The matrix-vector image collapses to a `Fin 2` sum (helper for recovery). -/
private lemma mulVec_fin2 (M : Matrix (Fin 2) (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2))
    (i : Fin 2) :
    (M *ᵥ v.ofLp) i = M i 0 * v.ofLp 0 + M i 1 * v.ofLp 1 := by
  show ∑ j, M i j * v.ofLp j = _
  rw [Fin.sum_univ_two]

/-- **Branch `|Φ⁺⟩` recovery:** `I · (I|ψ⟩) = |ψ⟩`. -/
theorem recover_phiPlus (α β : ℂ) :
    (Matrix.toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℂ)) (bobPhiPlus α β)
      = teleInput α β := by
  ext i
  show (Matrix.toLpLin 2 2 (1 : Matrix (Fin 2) (Fin 2) ℂ)) (bobPhiPlus α β) i = teleInput α β i
  rw [Matrix.toLpLin_apply]
  show ((1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (bobPhiPlus α β).ofLp) i = (teleInput α β).ofLp i
  rw [mulVec_fin2]
  fin_cases i <;>
    simp [bobPhiPlus, teleInput, EuclideanSpace.single, Matrix.one_apply]

/-- **Branch `|Φ⁻⟩` recovery:** `Z · (Z|ψ⟩) = |ψ⟩`. -/
theorem recover_phiMinus (α β : ℂ) :
    (Matrix.toEuclideanLin teleZ) (bobPhiMinus α β) = teleInput α β := by
  ext i
  show (Matrix.toLpLin 2 2 teleZ) (bobPhiMinus α β) i = teleInput α β i
  rw [Matrix.toLpLin_apply]
  show (teleZ *ᵥ (bobPhiMinus α β).ofLp) i = (teleInput α β).ofLp i
  rw [mulVec_fin2]
  fin_cases i <;>
    simp [teleZ, bobPhiMinus, teleInput, EuclideanSpace.single,
      Matrix.of_apply]

/-- **Branch `|Ψ⁺⟩` recovery:** `X · (X|ψ⟩) = |ψ⟩`. -/
theorem recover_psiPlus (α β : ℂ) :
    (Matrix.toEuclideanLin teleX) (bobPsiPlus α β) = teleInput α β := by
  ext i
  show (Matrix.toLpLin 2 2 teleX) (bobPsiPlus α β) i = teleInput α β i
  rw [Matrix.toLpLin_apply]
  show (teleX *ᵥ (bobPsiPlus α β).ofLp) i = (teleInput α β).ofLp i
  rw [mulVec_fin2]
  fin_cases i <;>
    simp [teleX, bobPsiPlus, teleInput, EuclideanSpace.single,
      Matrix.of_apply]

/-- **Branch `|Ψ⁻⟩` recovery:** `ZX · (XZ|ψ⟩) = |ψ⟩`. -/
theorem recover_psiMinus (α β : ℂ) :
    (Matrix.toEuclideanLin teleZX) (bobPsiMinus α β) = teleInput α β := by
  ext i
  show (Matrix.toLpLin 2 2 teleZX) (bobPsiMinus α β) i = teleInput α β i
  rw [Matrix.toLpLin_apply]
  show (teleZX *ᵥ (bobPsiMinus α β).ofLp) i = (teleInput α β).ofLp i
  rw [mulVec_fin2]
  fin_cases i <;>
    simp [teleZX, bobPsiMinus, teleInput, EuclideanSpace.single,
      Matrix.of_apply]

/-- **Teleportation recovers the input in every branch.** Bundles the four
per-branch corrections: with the two-bit Bell-measurement outcome, Bob's Pauli
correction returns `|ψ⟩` exactly. -/
theorem teleportation_branch_recovers_input (α β : ℂ) :
    (Matrix.toEuclideanLin (1 : Matrix (Fin 2) (Fin 2) ℂ)) (bobPhiPlus α β) = teleInput α β ∧
    (Matrix.toEuclideanLin teleZ) (bobPhiMinus α β) = teleInput α β ∧
    (Matrix.toEuclideanLin teleX) (bobPsiPlus α β) = teleInput α β ∧
    (Matrix.toEuclideanLin teleZX) (bobPsiMinus α β) = teleInput α β :=
  ⟨recover_phiPlus α β, recover_phiMinus α β, recover_psiPlus α β, recover_psiMinus α β⟩

/-! ## Input normalisation -/

/-- The input qubit is a unit vector when `‖α‖² + ‖β‖² = 1`. -/
theorem teleInput_norm (α β : ℂ) (h : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1) :
    ‖teleInput α β‖ = 1 := by
  have h0 : (teleInput α β).ofLp 0 = α := by
    simp [teleInput, EuclideanSpace.single]
  have h1 : (teleInput α β).ofLp 1 = β := by
    simp [teleInput, EuclideanSpace.single]
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, h0, h1, h, Real.sqrt_one]

end Teleportation
end QM
end Empirical
end CSD

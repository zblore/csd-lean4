/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.QM.Crypto.QuantumMoney
import CsdLean4.Empirical.QM.Protocols.Basic

/-!
# Empirical/QM: Wiesner quantum-money minting / verification protocol

**Category:** 3-Local (QM-validity content, no CSD ontology), like the rest of
`Crypto/`.

A deliberately **simple, single-slot** Wiesner money protocol built on the
unforgeability foundation of `Crypto/QuantumMoney.lean`. A full Wiesner banknote
slot is a pair `(basis, value) ∈ {comp, had} × {0, 1}` selecting one of the four
BB84 states, secret to the bank. The representative **2-state model** used here
keeps the two non-orthogonal alternatives already proved in
`Crypto/QuantumMoney.lean` — `|0⟩` (`QuantumMoney.ket0`, computational) and `|+⟩`
(`QuantumMoney.ketPlus`, Hadamard) — selected by a single secret bit. This is the
minimal pair that carries the security content (non-orthogonality ⟹ no cloning).

## What this delivers

- `mint` — the slot state from the secret bit (`false ↦ |0⟩`, `true ↦ |+⟩`).
- `verifyProb note recorded` — the acceptance probability, the Born weight
  `‖⟨recorded, note⟩‖²` of the submitted `note` projected onto the bank's recorded
  eigenstate (`Mathlib/QuantumInfo/Register.prob` is the same `‖·‖²` Born weight on
  `QReg`; here we state it directly via the inner product on
  `EuclideanSpace ℂ (Fin 2)`).
- `wiesner_verify_honest` — **completeness**: honest money verifies with
  certainty, `verifyProb (mint b) (mint b) = 1` (the prepared state *is* the
  recorded eigenstate).
- `wiesner_forge_impossible` — **no perfect forgery**: no isometry clones both
  Wiesner notes against a fixed blank, a direct instantiation of
  `QuantumMoney.quantum_money_unforgeable`.
- `wiesnerSecurity : Protocols.SecurityBound` and `wiesner_forge_advantage_le` —
  the reusable `Protocols` security interface (shared with the E91 tranche),
  genuinely consumed by a proved per-slot acceptance bound.

## Honest scope: the security bound is qualitative

`QuantumMoney.quantum_money_unforgeable` is **qualitative** — it rules out a
*perfect* cloner, not a quantitative cloning fidelity. The corpus does **not**
contain the optimal single-qubit cloning bound (the `3/4` per-qubit Wiesner
counterfeiting probability of Wiesner 1983 / Molina-Vidick-Watrous 2013), so a
non-trivial quantitative forgery `ε` is **not** available here. Accordingly
`wiesnerSecurity.ε := 1` is the **trivial** probability bound (every acceptance
probability is `≤ 1`, proved via Cauchy-Schwarz in `wiesner_forge_advantage_le`),
and the genuine security content is split off as the *qualitative* impossibility
`wiesner_forge_impossible`: the bound-attaining perfect forgery (a cloning
isometry, advantage `= 1`) does not exist. A quantitative `ε` (the optimal cloning
fidelity) is named here as **out of scope** — a separate later tranche.

`ε := 1/2` (the cross-basis overlap `‖⟨0|+⟩‖² = 1/2`) is deliberately *not* used
as the bound: it is an *attained* per-slot value of one wrong-guess strategy, not
a valid *upper* bound on adversary advantage (an adversary can do strictly better,
up to the `3/4` cloning value not in the corpus), so reporting it as a
`SecurityBound` would be dishonest.

## Source

Wiesner 1983, *SIGACT News* **15**(1), 78 ("Conjugate Coding"); unforgeability via
the no-cloning theorem (Wootters-Zurek 1982 / Dieks 1982), as packaged in
`Crypto/QuantumMoney.quantum_money_unforgeable`.
-/

namespace CSD
namespace Empirical
namespace QM
namespace Wiesner

/-- **Mint.** The single-slot Wiesner money state selected by the bank's secret
bit: `false` mints the computational state `|0⟩`, `true` the Hadamard state `|+⟩`
(the representative non-orthogonal 2-state model; see the module docstring). -/
noncomputable def mint : Bool → EuclideanSpace ℂ (Fin 2)
  | false => QuantumMoney.ket0
  | true => QuantumMoney.ketPlus

/-- Every minted note is a unit vector (`|0⟩` and `|+⟩` are normalised). -/
lemma mint_unit (b : Bool) : ‖mint b‖ = 1 := by
  cases b
  · exact QuantumMoney.ket0_unit
  · exact QuantumMoney.ketPlus_unit

/-- **Verify.** The bank's acceptance probability for a submitted `note` against
its recorded eigenstate `recorded`: the Born weight `‖⟨recorded, note⟩‖²` of the
note measured in the recorded basis (accept iff the outcome equals the recorded
value). -/
noncomputable def verifyProb (note recorded : EuclideanSpace ℂ (Fin 2)) : ℝ :=
  ‖inner ℂ recorded note‖ ^ 2

/-- A unit state verified against itself accepts with certainty: the Born weight
`‖⟨ψ, ψ⟩‖² = ‖(‖ψ‖ : ℂ)²‖² = 1`. -/
lemma verifyProb_self_of_unit {ψ : EuclideanSpace ℂ (Fin 2)} (h : ‖ψ‖ = 1) :
    verifyProb ψ ψ = 1 := by
  unfold verifyProb
  rw [inner_self_eq_norm_sq_to_K, h]
  norm_num

/-- **Completeness: honest money always verifies.** Measuring the minted state in
its own (recorded) basis returns the recorded value with probability one:
`verifyProb (mint b) (mint b) = 1`. The prepared state *is* the recorded
eigenstate, so the Born weight is `1`. -/
theorem wiesner_verify_honest (b : Bool) :
    verifyProb (mint b) (mint b) = 1 :=
  verifyProb_self_of_unit (mint_unit b)

/-- **No perfect forgery (protocol level).** Over any tensor structure with the
inner-product factorisation `⟨a⊗b, c⊗d⟩ = ⟨a,c⟩·⟨b,d⟩` and a fixed unit blank
`e0`, no isometry `U` can forge (clone) both minted Wiesner notes — `mint false =
|0⟩` and `mint true = |+⟩` — against the same blank. A perfect counterfeiter would
in particular clone one of two non-orthogonal states, which is impossible. Direct
instantiation of `QuantumMoney.quantum_money_unforgeable` (no new content beyond
the proved non-orthogonality witness `QuantumMoney.wiesner_nonorthogonal`). -/
theorem wiesner_forge_impossible
    {Htensor : Type*} [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]
    (tensor : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) → Htensor)
    (h_tensor_inner : ∀ a b c d : EuclideanSpace ℂ (Fin 2),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (e0 : EuclideanSpace ℂ (Fin 2)) (he0 : ‖e0‖ = 1) :
    ¬ ∃ U : Htensor → Htensor,
        (∀ x y, inner ℂ (U x) (U y) = inner ℂ x y) ∧
        U (tensor (mint false) e0) = tensor (mint false) (mint false) ∧
        U (tensor (mint true) e0) = tensor (mint true) (mint true) :=
  QuantumMoney.quantum_money_unforgeable tensor h_tensor_inner e0 he0

/-- The Wiesner money protocol's `Protocols.SecurityBound`, reusing the interface
shared with the E91 QKD tranche (`Crypto/E91KeyRate.e91Security`). The bound is
`ε := 1`, the **trivial** probability bound: every single-slot acceptance / forgery
probability is `≤ 1` (proved in `wiesner_forge_advantage_le`). A non-trivial
quantitative `ε` (the optimal `3/4` cloning fidelity) is **out of scope** (not in
the corpus); the genuine security content is the *qualitative* impossibility of a
bound-attaining perfect forgery, `wiesner_forge_impossible`. See the module
docstring. -/
def wiesnerSecurity : Protocols.SecurityBound where
  ε := 1
  ε_nonneg := by norm_num
  ε_le_one := le_refl 1

/-- **The per-slot forgery / acceptance advantage is bounded by the protocol's
`SecurityBound`.** For any unit `note` and unit recorded eigenstate, the bank's
acceptance probability `verifyProb note recorded` is at most
`wiesnerSecurity.ε = 1`, proved from Cauchy-Schwarz (`norm_inner_le_norm`):
`‖⟨recorded, note⟩‖² ≤ (‖recorded‖·‖note‖)² = 1`. This is the genuine consumer that
makes `SecurityBound` load-bearing for the money tranche (exactly as
`e91_eavesdropper_advantage` consumes it for QKD): the field is a *proved* upper
bound on the acceptance probability, not decoration. The bound is trivial (`ε =
1`) because only the *qualitative* no-perfect-forgery content
(`wiesner_forge_impossible`) is available from the corpus; the quantitative `3/4`
cloning bound is a separate tranche. -/
theorem wiesner_forge_advantage_le
    {note recorded : EuclideanSpace ℂ (Fin 2)}
    (hn : ‖note‖ = 1) (hr : ‖recorded‖ = 1) :
    verifyProb note recorded ≤ wiesnerSecurity.ε := by
  show verifyProb note recorded ≤ 1
  unfold verifyProb
  have h : ‖inner ℂ recorded note‖ ≤ 1 := by
    have hcs := norm_inner_le_norm (𝕜 := ℂ) recorded note
    rw [hr, hn, mul_one] at hcs
    exact hcs
  nlinarith [norm_nonneg (inner ℂ recorded note : ℂ), h]

end Wiesner
end QM
end Empirical
end CSD

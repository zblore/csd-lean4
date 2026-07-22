/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Empirical/QM: minimal reusable security-protocol interface

**Category:** 3-Local (QM-validity scaffolding, no CSD ontology).

A small, deliberately **minimal** set of definitions giving the cryptographic
tranches (`Crypto/E91KeyRate.lean`, `Crypto/QuantumMoney.lean`) a shared
vocabulary for "an adversary's advantage is bounded" and "a real protocol
extracts a positive secret-key rate".

**Honest scope.** These are *formal stand-ins* for the protocol / security
framing, **not** a full composable security model. There is no
universally-composable (UC) / abstract-cryptography (AC) simulator, no
adversarial-view (AVS) distinguisher, no finite-key smoothing, and no
information-theoretic ε-secrecy proof here. `SecurityBound` records a single
real number ε with the "adversary cannot do better than ε" reading;
`IdealQKD` records only a key length plus a `Prop`-valued secrecy stand-in;
`RealProtocol.secure` is the bare "positive key rate ⟹ extractable key"
predicate. The deeper notions (composability, min-entropy accounting,
finite-key corrections) are named here and left out of scope; this file
provides only the reusable interface that the key-rate and forgery statements
instantiate.

**Field consumption (honest, future-facing).** `SecurityBound.ε` is consumed
now by `Crypto/E91KeyRate.e91_eavesdropper_advantage`, which proves the
LHV/eavesdropper advantage is bounded by it (grounded in `lhvCHSH_abs_le_two`),
and is the slot the quantum-money tranche will reuse as forgery probability.
`IdealQKD.idealSecret` is a placeholder carried for the QKD finite-key /
composable-secrecy tranche that will consume it; at this interface layer it is
deliberately abstract.
-/

namespace CSD
namespace Empirical
namespace Protocols

/-- An adversary's success / distinguishing bound: the single number `ε`,
constrained to a probability `0 ≤ ε ≤ 1`, with the reading "no adversary
succeeds (forges / distinguishes / learns the key) with probability greater
than `ε`". Reused by both the QKD tranche (eavesdropper information) and the
quantum-money tranche (forgery probability). Minimal by design: a richer
security object (min-entropy, smoothing parameters) is out of scope here. -/
structure SecurityBound where
  /-- The adversary-advantage bound. -/
  ε : ℝ
  /-- Advantages are nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- Advantages are probabilities, hence `≤ 1`. -/
  ε_le_one : ε ≤ 1

/-- The ideal QKD functionality, as a **minimal stand-in**: a key length
`keyLength` (in bits) together with a `Prop`-valued placeholder `idealSecret`
standing for "the ideal key is uniform and independent of any adversary".
This is explicitly *not* a uniform-distribution object or a composable ideal
functionality; it is the smallest datum the real-vs-ideal predicate below
needs to mention. -/
structure IdealQKD where
  /-- The ideal key length in bits. -/
  keyLength : ℕ
  /-- Stand-in proposition for "the ideal key is uniform and secret". Carried
  abstractly; a concrete uniform-distribution / min-entropy witness is out of
  scope at this interface layer. -/
  idealSecret : Prop

/-- A real protocol producing a key: an asymptotic secret-key rate
`keyRate` (secret bits per signal) together with the `SecurityBound` it
achieves against the eavesdropper. -/
structure RealProtocol where
  /-- Asymptotic secret bits extracted per transmitted signal. -/
  keyRate : ℝ
  /-- The adversary-advantage bound the protocol guarantees. -/
  security : SecurityBound

/-- A real protocol is **secure** when it extracts a strictly positive
secret-key rate: a positive asymptotic rate means a genuine secret key can be
distilled (for `keyRate ≤ 0` no key is extractable). -/
def RealProtocol.secure (P : RealProtocol) : Prop := 0 < P.keyRate

/-- `P` **emulates** the ideal functionality `I` over `n` signals (asymptotic
stand-in): the ideal `keyLength` bits are covered by the `n · keyRate` secret
bits the real protocol produces. This is the single consuming use of
`IdealQKD`; it is an asymptotic accounting identity, not a composable-security
emulation. -/
def RealProtocol.emulates (P : RealProtocol) (I : IdealQKD) (n : ℕ) : Prop :=
  (I.keyLength : ℝ) ≤ n * P.keyRate

/-- A secure protocol (positive key rate) emulates **any** ideal key length
once enough signals are sent: the asymptotic rate amortises any fixed key
length. Binds `secure`, `emulates`, `RealProtocol`, and `IdealQKD` into one
statement, so each definition has a genuine consumer. -/
theorem secure_emulates (P : RealProtocol) (hP : P.secure) (I : IdealQKD) :
    ∃ n : ℕ, P.emulates I n := by
  obtain ⟨n, hn⟩ := exists_nat_ge ((I.keyLength : ℝ) / P.keyRate)
  exact ⟨n, (div_le_iff₀ hP).mp hn⟩

end Protocols
end Empirical
end CSD

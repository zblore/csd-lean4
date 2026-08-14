/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.SharedContextMap

/-!
# LF3/OperationalNoSignalling: remote marginal invariance, at the measure level

**Category:** 3-Local (the operational no-signalling predicate).

## Why this is stated at the measure level

The tempting formulation is **pointwise**: `F_A(a, b, x) = F_A(a, b', x)` for
every `x`, and symmetrically for B. That is not merely too strong — over a
deterministic shared state it is **inconsistent with the rest of the
programme**. Setting `A(a,x) := F_A(a, b₀, x)` and `B(b,x) := F_B(a₀, b, x)`
recovers exactly the setting-local response pair that
`LF6.no_product_partition_realises_singlet` rules out for the singlet. An
assumption that is false in the sector under discussion is worse than a missing
one.

So the correct operational condition is equality of **marginal measures** under
a remote setting change, never equality of the underlying outcome regions.

## ⚠️ What this rests on: measurement independence

`OperationalNoSignalling` is stated relative to **one fixed `μ`**, used for all
four contexts. **That fixture is measurement independence** (the assumption that
the ontic distribution does not depend on which settings are chosen). It is a
genuine Bell premise, and naming it here is deliberate: it was previously
invisible, carried silently by the shape of the definition rather than stated.

Anything downstream that appeals to these predicates is therefore assuming
measurement independence, and should say so.

## ⚠️ What this is not

Verifying this predicate in a constructed sector is **not** a derivation of
no-signalling from primitives. Sufficient primitive conditions on
setting-dependent measure-preserving dynamics over a non-factorising ontic `Σ`
that *imply* remote marginal invariance remain **open** — see
`specs/BACKLOG.md`.

## References

`LF3/SharedContextMap.lean`; `LF3/ContextMap.lean`
(`context_no_signalling_a/b`); `LF6/ForcedContextuality.lean`;
`specs/c1-correction-plan.md` §1.
-/

@[expose] public section

open MeasureTheory

namespace CSD.LF3

variable {SigmaSpace : Type*} [MeasurableSpace SigmaSpace]

/-- **A-wing remote marginal invariance.** The measure of the event "A reads
`s`" is unchanged when B's setting moves from `b` to `b'`.

Equality of **measures**, not of the underlying outcome sets: the microscopic
region realising "A reads `s`" may differ entirely between the two contexts. -/
def RemoteMarginalInvariantA (μ : Measure SigmaSpace) (S : SharedContextOutcomeMaps SigmaSpace) : Prop :=
  ∀ (a b b' : DetectorSetting) (s : Sign),
    μ {l | S.wingA ⟨a, b⟩ l = s} = μ {l | S.wingA ⟨a, b'⟩ l = s}

/-- **B-wing remote marginal invariance**, symmetrically. -/
def RemoteMarginalInvariantB (μ : Measure SigmaSpace) (S : SharedContextOutcomeMaps SigmaSpace) : Prop :=
  ∀ (a a' b : DetectorSetting) (t : Sign),
    μ {l | S.wingB ⟨a, b⟩ l = t} = μ {l | S.wingB ⟨a', b⟩ l = t}

/-- **Operational no-signalling**: both wings' marginals are invariant under a
remote setting change.

⚠️ Stated relative to a single fixed `μ` across all four contexts. That fixture
is **measurement independence**, and it is a premise, not a consequence. -/
def OperationalNoSignalling (μ : Measure SigmaSpace) (S : SharedContextOutcomeMaps SigmaSpace) : Prop :=
  RemoteMarginalInvariantA μ S ∧ RemoteMarginalInvariantB μ S

/-! ### The singlet kernel is operationally no-signalling -/

/-- ★ **The singlet kernel satisfies remote marginal invariance on both wings**,
in one statement.

This is the kernel-level fact, assembled from the machine-checked
`context_no_signalling_a` and `context_no_signalling_b`. It is a **verification
in the constructed sector**, not a derivation from primitives. -/
theorem singlet_operational_no_signalling
    (ctx : MeasurementContext) (a' b' : DetectorSetting) :
    (∀ s : Sign, ∑ t : Sign, P_st ctx.a ctx.b s t = ∑ t : Sign, P_st ctx.a b' s t)
      ∧ (∀ t : Sign, ∑ s : Sign, P_st ctx.a ctx.b s t = ∑ s : Sign, P_st a' ctx.b s t) :=
  ⟨fun s => context_no_signalling_a ctx b' s, fun t => context_no_signalling_b ctx a' t⟩

/-- Both wings' marginals are `1/2` at every context: the singlet is locally
maximally mixed, which is the strongest form of "the remote setting is
invisible". -/
theorem singlet_marginals_eq_half (ctx : MeasurementContext) :
    (∀ s : Sign, ∑ t : Sign, P_st ctx.a ctx.b s t = 1 / 2)
      ∧ (∀ t : Sign, ∑ s : Sign, P_st ctx.a ctx.b s t = 1 / 2) :=
  ⟨fun s => context_marginal_a ctx s, fun t => context_marginal_b ctx t⟩

end CSD.LF3

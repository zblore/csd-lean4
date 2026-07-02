import CsdLean4.Empirical.CSD.Framework
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Empirical/CSD: Gate framework (CSDUnitaryBundle)

**Category:** 3-Local (CSD-side shared framework for quantum-gate
bundles). Sibling of `Empirical/CSD/Framework.lean`; depends on it
via `CSDBridgeContext`.

## What this file provides

The `CSDUnitaryBundle D N H_n U` structure: a CSD-side carrier for
the claim "the Hilbert-space unitary `U` on an `N`-qubit space `H_n`
arises as the projective-action lift of a measure-preserving
π-equivariant flow on `Σ^N → Σ^N` for the `SectorData D`". This
generalises `CSDCloningBundle` (which is the `Σ × Σ` case fixed to
the cloning tensor structure).

## Polarity

Positive-existence-conditional-on-LF4. The bundle's existence
asserts the LF4-§13.2 obligation. Pre-LF4 callers supply the
bundle by hypothesis; post-LF4 the Kähler `SectorData` discharges
it (per LF4-todo §13.2 + §2 + §7 + §8). The four bundle polarities
established by Tranche 0:

- **Bell**: positive frequency convergence (LF3 chain re-exports).
- **NoCloning**: Hilbert-side negative existential.
- **KS/GHZ**: ontic-partition negative existential.
- **Gates (new this file)**: positive-existence-conditional-on-LF4.

## LF4 obligation

`CSDUnitaryBundle.U_isometry` is the load-bearing field carrying
the LF4-§13.2 obligation. **Status: load-bearing, externally supplied,
undischarged.** LF4-todo §13.2.

Per the bridge-discipline rules at the top of `specs/LF4-todo.md`,
§13.2 was added in the same change-set as this file's first use
(the Tranche 1 Tier A gate work).

### Wigner availability (2026-07-02) — NOT a clean discharge of this field

`Projectivization.wigner_rigidity` / `wigner_rigidity_unitaryGroup`
(`Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean`, axiom-free)
now close the *operational/projective* correspondence: a
`TransProbPreserving` self-map of `ℂℙ^{N-1}` is `U • ·` for a
`Matrix.unitaryGroup` element (or `U • conjProj ·`). That is the converse of
the realisability inclusion `transProbPreserving_unitary`, on the same stratum
as `U_isometry` here. It does **not** discharge this field, for two precise
reasons:

1. **Wrong side / wrong direction.** Wigner runs *projective symmetry ⟹
   unitary*. The §13.2 obligation is *ontic ⟹ isometry*: `U_isometry` should
   FOLLOW from a measure-preserving, `π`-equivariant flow `Φ : Σ^N → Σ^N` whose
   projective pushforward realises `U`. Wigner supplies no `Σ`-flow, no
   `π`-equivariance, and no `μL`-preservation — that content (the D1 ontic
   stratum) is exactly what remains open.
2. **No map to feed Wigner (schema-mismatch, PLACEHOLDERS.md §7).** This
   structure carries only `U : H_n → H_n` and `U_isometry`; it exposes no
   `TransProbPreserving` projective map and no `Σ`-flow. To route through
   Wigner one must first (a) re-architect the bundle to carry `Φ` and its
   projective pushforward `f_Φ`, then (b) PROVE `TransProbPreserving f_Φ` from
   measure-preservation + `π`-equivariance on a concrete Kähler `SectorData`
   (§8). Step (b) is the load-bearing lift `U_isometry` abbreviates; Wigner
   presupposes it, so it cannot supply it. Only *after* (b) does
   `wigner_rigidity_unitaryGroup` yield the unitary whose isometry is
   `U_isometry`.

Net: Wigner closes the projective↔unitary half and is the correct final step of
the §13.2 chain, but the remaining gap (`Σ`-flow ⟹ `TransProbPreserving`
pushforward on a Kähler Σ) is untouched by it. STAGED, not discharged.

## Composition

`CSDUnitaryBundle.comp` composes two bundles on the same context +
qubit count into a single bundle whose `U` is the function
composition. Used by the Bell-state preparation circuit
(`Empirical/CSD/Gates/BellPrep.lean`) to compose Hadamard + CNOT.

## Honest reading

This is a Cat-3 structural carrier. The bundle does not establish
that any specific unitary IS realisable through a CSD ontic flow
(that is LF4 content); it provides a uniform interface for asserting
the realisability and reducing gate-identity statements across the
bridge.
-/

open MeasureTheory

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Gates

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: docstring claims CSD-side content the type does not carry.**

The only non-`Context` fields in the type are `U : H_n → H_n` (a
function) and `U_isometry` (inner-product preservation). Neither
encodes any `Σ`-side flow, `π`-equivariance, or measure-preservation
hypothesis. The "projective-action lift of a measure-preserving
π-equivariant flow on `Σ^N`" claim below is **non-syntactic prose**;
Lean cannot check it. The type, as a proposition, is equivalent to
"there exists a `Context D` plus a Hilbert-space isometry on `H_n`."

See `PLACEHOLDERS.md §7` for the canonical schema-mismatch ledger.

## Original (over-claiming) docstring follows

**CSD unitary bundle.** Structural carrier for a hypothetical
`N`-qubit unitary realised through CSD's ontic substrate on a
`SectorData D`.

The bundle extends `CSDBridge.Context D` (LF2-level discharge data)
and adds:

- `H_n`: the `N`-qubit Hilbert space (abstract; concrete instantiations
  use `EuclideanSpace ℂ (Fin (2^N))` or product `Fin`-indexed forms).
- `U`: the carried unitary as a function `H_n → H_n`.
- `U_isometry`: inner-product preservation (the LF4-§13.2 obligation).

## LF4-discharge content (prose-only; no field encodes this)

By calling the structure `CSDUnitaryBundle`, callers implicitly assert
that `U` arises as the projective-action lift of a measure-preserving
π-equivariant flow on `Σ^N`. Pre-LF4 this is at construction site;
post-LF4 it follows from the concrete Kähler `SectorData` discharging
LF4-todo §13.2 (+ §2 + §7 + §8).

**Status: load-bearing, externally supplied, undischarged.**
LF4-todo §13.2.

(The above "status" applies to the *prose claim*, not to any field of
this structure. See `PLACEHOLDERS.md §7` discharge route.) -/
structure CSDUnitaryBundle
    (D : CSD.LF2.SectorData SigmaSpace P G) (N : ℕ)
    (H_n : Type*) [NormedAddCommGroup H_n] [InnerProductSpace ℂ H_n]
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The Hilbert-space unitary carried by the bundle. -/
  U          : H_n → H_n
  /-- `U` preserves inner products. -/
  U_isometry : ∀ x y : H_n, inner ℂ (U x) (U y) = inner ℂ x y

/-- **Composition of two CSD unitary bundles.** Given two bundles on
the same context + qubit count, produces a third bundle whose `U` is
the function composition. Used to chain gate-level CSD-side statements
(e.g. the Bell-state preparation circuit composes a Hadamard bundle
and a CNOT bundle).

The composition's `U_isometry` follows in two lines from the two
input isometries. -/
def CSDUnitaryBundle.comp
    {D : CSD.LF2.SectorData SigmaSpace P G} {N : ℕ}
    {H_n : Type*} [NormedAddCommGroup H_n] [InnerProductSpace ℂ H_n]
    (b₁ b₂ : CSDUnitaryBundle D N H_n) :
    CSDUnitaryBundle D N H_n where
  toContext := b₁.toContext
  U         := b₂.U ∘ b₁.U
  U_isometry := by
    intro x y
    show inner ℂ (b₂.U (b₁.U x)) (b₂.U (b₁.U y)) = inner ℂ x y
    rw [b₂.U_isometry, b₁.U_isometry]

end Gates
end CSDBridge
end Empirical
end CSD

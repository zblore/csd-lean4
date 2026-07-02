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

## LF4 obligation — DISCHARGED via Wigner modulo A5 (2026-07-02)

`CSDUnitaryBundle.U_isometry` carries the LF4-§13.2 obligation. It is now
**discharged through Wigner from the intrinsic transition-probability
condition**, modulo the sector symmetry (A5). See
`Empirical/CSD/Gates/WignerDischarge.lean`.

Per the bridge-discipline rules at the top of `specs/LF4-todo.md`,
§13.2 was added in the same change-set as this file's first use
(the Tranche 1 Tier A gate work).

### The discharge route (WignerDischarge.lean)

`CSDUnitaryBundle.ofTransProbPreserving` builds a bundle whose `U` is the
Wigner OUTPUT and whose `U_isometry` is a THEOREM (`e.inner_map_map`), from:

- `hf : Projectivization.TransProbPreserving f` — the intrinsic
  transition-probability condition on the projective dynamics `f`;
- `hsel` — a no-time-reversal selection (`f` is not the antiunitary branch),
  a discrete `ℤ/2` orientation datum (the Kähler / ℂ-linearity choice), **not**
  the isometry data.

`u_isometry_of_transProbPreserving` is the headline: Wigner
(`wigner_rigidity`) *produces* the `≃ₗᵢ[ℂ]` `e` with `⟪e x, e y⟫ = ⟪x, y⟫`.
Unitarity — hence `U_isometry` — is the OUTPUT, never an input. The primitive
moves from "posit the Hilbert isometry `U`" to "posit the projective dynamics
preserves transition probabilities and is not time-reversal", a weaker and more
physical primitive. `transProbPreserving_isometry_dichotomy` exposes the
antiunitary (anti-isometry, `⟪e (conjVec x), e (conjVec y)⟫ = conj ⟪x, y⟫`)
branch honestly; it is not dropped. `cpSectorActionBundle` is the non-vacuous
instantiation on `cpSectorData p₀`: the sector action `g • ·` is
`TransProbPreserving` (`transProbPreserving_unitary`) and not time-reversal
(`smul_action_not_antiunitary`, `N ≥ 2`), so its `U_isometry` is derived.

### True residue (D1) — the false "measure ⟹ metric" claim, corrected

The transition-probability preservation `hf` is FORCED by the **sector
symmetry** — the sector group `G` acting by Fubini–Study isometries, which is
the A5 datum (`SectorData.(π, G)`) — **not** by `μL`-measure-preservation. The
earlier reading of this obligation, that `U_isometry` "follows from a
measure-preserving π-equivariant Σ-flow", is **false**: measure-preservation is
strictly weaker than metric preservation. A `μFS`-measure-preserving self-map of
`ℂℙ^{N-1}` need not preserve the Fubini–Study metric / transition probability, so
no lemma "measure-preserving `f_Φ` ⟹ `TransProbPreserving f_Φ`" is (or can be)
proved. Deriving `TransProbPreserving f_Φ` from a *general* `μL`-flow for a
non-symmetry flow is the open **D1** gap. §13.2 therefore discharges exactly
modulo the posited sector symmetry (A5), which is CSD's intended structure.

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

## LF4-discharge content

`U_isometry` is discharged via Wigner from the intrinsic
transition-probability condition by
`CSDUnitaryBundle.ofTransProbPreserving`
(`Empirical/CSD/Gates/WignerDischarge.lean`): unitarity is the Wigner
OUTPUT, `U_isometry` a theorem. Non-vacuously instantiated by the sector
action on the concrete Kähler instance (`cpSectorActionBundle`).

**Status: DISCHARGED via Wigner modulo the sector symmetry (A5).**
LF4-todo §13.2. The transition-probability preservation is forced by A5
(G acting by FS isometries), not by `μL`-measure-preservation (measure ≠
metric); the general-flow ⟹ isometry direction is the open D1 gap. A
directly-posited `CSDUnitaryBundle` (via the primitive constructor) still
carries `U_isometry` as a hypothesis at its construction site. -/
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

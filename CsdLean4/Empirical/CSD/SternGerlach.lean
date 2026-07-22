/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.SternGerlach
import CsdLean4.LF4.SingleQubitKahler

/-!
# Empirical/CSD: Stern-Gerlach Born probabilities (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/SternGerlach.lean`).

Pairs with `Empirical/QM/SternGerlach.lean` (Stern, Gerlach 1922). The
QM file states the four canonical spin-1/2 Born identities for
preparation `|+_z⟩` and measurement in either `Z` or `X` basis:

```
P(+_z | +_z) = 1          P(+_x | +_z) = 1/2
P(-_z | +_z) = 0          P(-_x | +_z) = 1/2
```

plus the two basis-completeness identities.

This file states the **CSD volume-ratio reading**: under CSD's ontic
substrate, each Born value is the volume fraction of the corresponding
outcome region within the posited fibre law `μψ` realising the prep
state `|+_z⟩`, given the LF4-§14 observable correspondence for the
spin-1/2 observables `σ_z` and `σ_x`.

## Polarity (transport, no parameters)

Unlike the parameterised bundles (`Bell`, `NoCloning`, `NoDeleting`,
`Uncertainty`), the SG Born identities are fixed numerical predictions
(`1`, `0`, `1/2`). The CSD-side bundle is therefore a **tag bundle** —
extends `CSDBridge.Context D` with no new fields. Its *existence* is
the load-bearing assertion that the spin-1/2 SG configuration is
realised through CSD's ontic substrate on this `SectorData D` (the
LF4-§14 observable correspondence applied to `σ_z` and `σ_x`).

## LF4 obligations carried

LF4-todo §14 (observable correspondence): the Hilbert operators `σ_z`
and `σ_x` arise as Hilbert-space lifts of measurable functions on `Σ`,
and `|+_z⟩` arises as the lift of a CSD preparation. Pre-LF4 this is
prose-only on the bundle; post-LF4 it is provable from the concrete
`SectorData` instantiation + spectral machinery.

## Schema-mismatch acknowledgement

Per the NoCloning template's discipline: the transport theorems below
prove numerical Born equalities that are **purely QM-side** at the
Lean level. The CSD content is the bundle's prose claim about
LF4-§14 realisability of the spin-1/2 observables. Lean does not
check that claim. See `PLACEHOLDERS.md §7`.

## LF4 lift availability

With `LF4/SingletKahler.lean`'s `ofKählerPreparation` now constructed
for `N = 4` (the 2-qubit case for the singlet), an analog at `N = 2`
(single qubit) would lift the SG Born identities through the LF3
chain — a `singlet_frequency_convergence`-style capstone landing
on `1`, `1/2`, etc. instead of `P_st`. That is a natural follow-on
tranche (LF4-todo §8 sub-item, currently unscheduled).

## Experimental verification

- Stern, Gerlach 1922: *Z. Phys.* **9**, 349 (original silver-atom beam).
- Phipps, Taylor 1927: *Phys. Rev.* **29**, 309 (hydrogen confirmation).

The four Born identities + basis completeness are the foundational
verification of QM's probabilistic structure on a single qubit.
-/

namespace CSD
namespace Empirical
namespace CSDBridge
namespace SternGerlach

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **SCHEMA-MISMATCH: bundle is a CSD-realisability tag, no fields beyond
`CSDBridge.Context D`.** See module docstring + `PLACEHOLDERS.md §7`.

**CSD Stern-Gerlach bundle.** Extends `CSDBridge.Context D` with no
additional fields. Its *existence* is the load-bearing assertion that
the spin-1/2 SG configuration — preparation `|+_z⟩`, measurements in
the `Z` and `X` bases — is realised through CSD's ontic substrate on
this `SectorData D` via the LF4-§14 observable correspondence.

**Status: ONTIC-BACKED (§14 CONNECTED 2026-07-19).** The SG reading is no longer a
bare QM transport: the genuine ontic derivation on the single-qubit Kähler instance
`Σ = ℂℙ¹ × T²` is proved in `LF4/SingleQubitKahler.lean`
(`sg_observable_correspondence`, `sg_frequency_convergence`) and exercised as a
Born-as-volume derivation in `Empirical/CSD/SternGerlachVolume.lean`; the
`csd_sg_ontic_*` theorems below expose that backing in this module. Honest scope: the
bundle type itself still carries only a `Context` (`PLACEHOLDERS.md §7`); the ontic
content lives in the cited theorems, which the transport predictions now point to.
LF4-todo §14. -/
structure CSDSternGerlachBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
  extends CSD.Empirical.CSDBridge.Context D

/-! ### Transport-only Born identities (CSD reading)

Each theorem below transports a QM-side Stern-Gerlach Born identity
through the bundle, framing it as the CSD volume-ratio prediction.
Foundational triple only. -/

variable {D : CSD.LF2.SectorData SigmaSpace P G}

/-- **CSD `P(+_z | +_z) = 1`.** Preparation along `+z`, measurement
along `z`, `+`-outcome: certainty. Transported from
`Empirical.QM.SternGerlach.born_zPlus_zPlus`. -/
theorem csd_sg_born_zPlus_zPlus (_b : CSDSternGerlachBundle D) :
    CSD.Empirical.SternGerlach.bornProb
        CSD.Empirical.SternGerlach.zPlus
        CSD.Empirical.SternGerlach.zPlus = 1 :=
  CSD.Empirical.SternGerlach.born_zPlus_zPlus

/-- **CSD `P(−_z | +_z) = 0`.** Preparation along `+z`, measurement
along `z`, `−`-outcome: forbidden. Transported from
`Empirical.QM.SternGerlach.born_zMinus_zPlus`. -/
theorem csd_sg_born_zMinus_zPlus (_b : CSDSternGerlachBundle D) :
    CSD.Empirical.SternGerlach.bornProb
        CSD.Empirical.SternGerlach.zMinus
        CSD.Empirical.SternGerlach.zPlus = 0 :=
  CSD.Empirical.SternGerlach.born_zMinus_zPlus

/-- **CSD `P(+_x | +_z) = 1/2`.** Preparation along `+z`, measurement
along `x`, `+`-outcome: half. The canonical 50/50 SG split.
Transported from `Empirical.QM.SternGerlach.born_xPlus_zPlus`. -/
theorem csd_sg_born_xPlus_zPlus (_b : CSDSternGerlachBundle D) :
    CSD.Empirical.SternGerlach.bornProb
        CSD.Empirical.SternGerlach.xPlus
        CSD.Empirical.SternGerlach.zPlus = 1 / 2 :=
  CSD.Empirical.SternGerlach.born_xPlus_zPlus

/-- **CSD `P(−_x | +_z) = 1/2`.** The other half of the SG x-axis
split. Transported from `Empirical.QM.SternGerlach.born_xMinus_zPlus`. -/
theorem csd_sg_born_xMinus_zPlus (_b : CSDSternGerlachBundle D) :
    CSD.Empirical.SternGerlach.bornProb
        CSD.Empirical.SternGerlach.xMinus
        CSD.Empirical.SternGerlach.zPlus = 1 / 2 :=
  CSD.Empirical.SternGerlach.born_xMinus_zPlus

/-- **CSD Z-basis completeness** (prep `+z`): the two `Z`-outcome
probabilities sum to 1. The CSD-side mirror of
`Empirical.QM.SternGerlach.born_z_basis_complete`. -/
theorem csd_sg_born_z_basis_complete (_b : CSDSternGerlachBundle D) :
    CSD.Empirical.SternGerlach.bornProb
        CSD.Empirical.SternGerlach.zPlus
        CSD.Empirical.SternGerlach.zPlus
    + CSD.Empirical.SternGerlach.bornProb
        CSD.Empirical.SternGerlach.zMinus
        CSD.Empirical.SternGerlach.zPlus = 1 :=
  CSD.Empirical.SternGerlach.born_z_basis_complete

/-- **CSD X-basis completeness** (prep `+z`): the two `X`-outcome
probabilities sum to 1. The CSD-side mirror of
`Empirical.QM.SternGerlach.born_x_basis_complete`. -/
theorem csd_sg_born_x_basis_complete (_b : CSDSternGerlachBundle D) :
    CSD.Empirical.SternGerlach.bornProb
        CSD.Empirical.SternGerlach.xPlus
        CSD.Empirical.SternGerlach.zPlus
    + CSD.Empirical.SternGerlach.bornProb
        CSD.Empirical.SternGerlach.xMinus
        CSD.Empirical.SternGerlach.zPlus = 1 :=
  CSD.Empirical.SternGerlach.born_x_basis_complete

/-! ### Genuine ontic backing (§14 CONNECTED 2026-07-19)

The transport theorems above restate the QM Born identities. The CSD reading is
GENUINELY backed by the proved ontic derivation on the single-qubit Kähler instance
(`LF4/SingleQubitKahler.lean`): the two theorems here expose that backing in this
module, so the SG reading cites the ontic substrate, not only the QM fact. The same
pattern (import the `LF4` observable-correspondence / frequency-convergence for the
phenomenon) connects the other §14 transport modules (Hardy, Uncertainty, Mermin–Peres)
to their proved ontic content. -/

/-- **Ontic observable correspondence (§14).** The Hilbert expectation of each SG spin
projector equals the ONTIC measure of the SG outcome region `sgMuPsi (sgRegion s a)` —
the observable-as-ontic-function correspondence, proved axiom-free in
`CSD.LF4.sg_observable_correspondence`. So the SG Born predictions are ontic region
volumes, not posited numbers. (Re-exported into this module so the CSD SG reading cites
its ontic derivation.) -/
alias csd_sg_ontic_observable_correspondence := CSD.LF4.sg_observable_correspondence

/-- **Ontic frequency convergence (§14).** i.i.d. sampling of the ONTIC fibre law
`sgMuPsi` (the `|+z⟩` preparation) gives SG outcome frequencies converging a.s. to the
QM Born value — the genuine CSD derivation, `CSD.LF4.sg_frequency_convergence`, not a
transport. Re-exported here so the CSD SG reading owns its ontic derivation. -/
alias csd_sg_ontic_frequency_convergence := CSD.LF4.sg_frequency_convergence

end SternGerlach
end CSDBridge
end Empirical
end CSD

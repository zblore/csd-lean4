/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.Crypto.E91

/-!
# Empirical/CSD: E91 device-independent security (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/Crypto/E91.lean`).

Pairs with `Empirical/QM/Crypto/E91.lean` (Ekert 1991; CHSH 1969). The QM file builds a
genuine measure-theoretic local-hidden-variable model — a hidden-variable probability
space `(Λ, μ)` with `±1` local responses — and proves the Bell/CHSH bound `|S| ≤ 2`,
together with the device-independent witness that the singlet attains `2√2 > 2` and so is
unreproducible by any LHV model.

This file states the **CSD reading**, whose polarity is the sharpest in the suite. A
`CSDLHVBundle` posits a *local-realist reading of the CSD source*: a hidden-variable
space `(Λ, μ)` with `±1` responses standing in for a would-be local description of the
ontic substrate. The theorem `csd_lhv_chsh_bound` shows every such reading is capped at
`|S| ≤ 2`. CSD's own predictions, by contrast, reach the Tsirelson value `2√2` — the
singlet correlation `−cos θ` is *derived* on the CSD substrate in
`Empirical/CSD/BellVolume.lean` (`bell_singlet_volume_correlation`) as a Fubini-Study
volume, and at the CHSH angles this gives `|S| = 2√2`. So the CSD source provably **has
no local-realist (LHV) description**: CSD is a non-local-realist ontic theory, exactly as
device-independent security requires.

## Polarity (no undischarged realisability obligation)

Unlike the other bridges, this one carries **no** LF4 realisability marker. The bundle's
LHV fields are *not* claimed to be CSD-realisable; the content is the opposite — the
bound certifies that a local-realist reading cannot match CSD's derived Tsirelson value.
The transport is therefore a clean reduction with no externally-supplied ontic posit.

## Source

Ekert 1991, *Phys. Rev. Lett.* **67**, 661; CHSH 1969, *Phys. Rev. Lett.* **23**, 880.
-/

open MeasureTheory

namespace CSD
namespace Empirical
namespace CSDBridge
namespace E91

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **CSD LHV bundle.** A posited local-realist reading of the CSD source: a
hidden-variable probability space `(Λ, μ)` with `±1`-valued, measurable local response
functions `A, B`, packaged in a `SectorData D` context. Extends `CSDBridge.Context D`.
The fields match the argument list of `Empirical.QM.E91.lhvCHSH_abs_le_two`.

No LF4 realisability marker: the bundle's LHV fields are deliberately *not* asserted to
be CSD-realisable. The point of `csd_lhv_chsh_bound` is that any such reading is bounded
away from CSD's derived Tsirelson value. -/
structure CSDLHVBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
    (Λ : Type*) [MeasurableSpace Λ] (SettingA SettingB : Type*)
  extends CSD.Empirical.CSDBridge.Context D where
  /-- The hidden-variable measure. -/
  μ      : Measure Λ
  /-- `μ` is a probability measure. -/
  hμ     : IsProbabilityMeasure μ
  /-- Alice's local response function (per setting). -/
  A      : SettingA → Λ → ℝ
  /-- Bob's local response function (per setting). -/
  B      : SettingB → Λ → ℝ
  hA     : ∀ a, Measurable (A a)
  hB     : ∀ b, Measurable (B b)
  hApm   : ∀ a l, A a l = 1 ∨ A a l = -1
  hBpm   : ∀ b l, B b l = 1 ∨ B b l = -1

/-- **TRANSPORT-ONLY: proof body unpacks the bundle's LHV fields and calls the QM-side
theorem.**

**The Bell/CHSH bound in the CSD reading.** Any posited local-realist reading of the CSD
source obeys `|S| ≤ 2`. Reduces to the QM-side `Empirical.QM.E91.lhvCHSH_abs_le_two` by
direct field extraction. Combined with the *derived* CSD singlet correlation reaching the
Tsirelson value `2√2` (`Empirical/CSD/BellVolume.lean`), this certifies that the CSD
source admits no local-realist description — the device-independent security guarantee.

**Experimental verification:** Ekert 1991; loophole-free Bell tests Hensen 2015,
Giustina 2015, Shalm 2015. -/
theorem csd_lhv_chsh_bound
    {D : CSD.LF2.SectorData SigmaSpace P G}
    {Λ : Type*} [MeasurableSpace Λ] {SettingA SettingB : Type*}
    (bun : CSDLHVBundle D Λ SettingA SettingB)
    (a a' : SettingA) (b b' : SettingB) :
    |CSD.Empirical.QM.E91.lhvCHSH bun.μ bun.A bun.B a a' b b'| ≤ 2 := by
  haveI := bun.hμ
  exact CSD.Empirical.QM.E91.lhvCHSH_abs_le_two bun.μ bun.A bun.B
    bun.hA bun.hB bun.hApm bun.hBpm a a' b b'

end E91
end CSDBridge
end Empirical
end CSD

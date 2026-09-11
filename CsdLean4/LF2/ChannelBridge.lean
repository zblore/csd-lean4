/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.QuantumChannel
public import CsdLean4.Mathlib.QuantumInfo.Stinespring
public import CsdLean4.Mathlib.QuantumInfo.CanonicalChannels
public import CsdLean4.Mathlib.QuantumInfo.DataProcessing
public import CsdLean4.Mathlib.QuantumInfo.ChannelComp

/-!
# The bridge between `LF2.QuantumChannel` and `QuantumInfo.Channel`

**Category:** 3-Local (W5 of `specs/qit-chain-scoping.md`, second half).

The corpus carries two Kraus-form channel types: `CSD.LF2.QuantumChannel ι N M` (`Fin`-indexed,
2026-05, with the Stinespring dilation, the Choi matrix and Choi's theorem built on it) and
`QuantumInfo.Channel n m ι` (index-generic, the type every entropy, distance and data-processing
theorem of `Mathlib/QuantumInfo/` takes). They are **the same data** with the index order swapped,
and until 2026-09-11 nothing said so, so no QIT theorem applied to an LF2 channel. This module is
the bridge:

* `toChannel` / `ofChannel` / `channelEquiv` — the equivalence, with `toChannel_apply`,
  `ofChannel_apply` (the actions agree, by `rfl`) and `channelApply_M_eq` for density operators;
* `toChannel_stinespringIsom` (the LF2 dilation is the `QuantumInfo` Stinespring isometry),
  `unitaryChannel_apply_eq`, `toChannel_comp` — the derived notions correspond;
* ★ `traceDist_channelApply_le` — the data-processing inequality for LF2 channels, one `exact`
  through the bridge.

**Interface status.** `CSD.LF2.QuantumChannel` is henceforth an *interface* to
`QuantumInfo.Channel`: kept for its Choi results (`choiMatrix`, `choi_iff_posSemidef` in
`LF2/ChoiConverse.lean`) and its existing consumers, not extended. New work states channels as
`QuantumInfo.Channel` and moves through `toChannel` / `ofChannel` when it needs the Choi layer.

References: `specs/qit-chain-scoping.md` (W5); `LF2/QuantumChannel.lean`;
`Mathlib/QuantumInfo/{Channel,Stinespring,CanonicalChannels,DataProcessing,ChannelComp}.lean`;
`LF6/DecoherenceChannel.lean` (W5's witness half).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder

/-! ### The bridge `LF2.QuantumChannel ↔ QuantumInfo.Channel` -/

namespace CSD.LF2
namespace QuantumChannel

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {N M P : ℕ}

/-- The LF2 channel as a `QuantumInfo.Channel`: the same Kraus family, index order swapped. -/
def toChannel (Φ : QuantumChannel ι N M) : Channel (Fin N) (Fin M) ι :=
  ⟨Φ.kraus, Φ.isTracePreserving⟩

/-- A `QuantumInfo.Channel` between `Fin`-indexed spaces as an LF2 channel. -/
def ofChannel (Φ : Channel (Fin N) (Fin M) ι) : QuantumChannel ι N M :=
  ⟨Φ.kraus, Φ.tp⟩

@[simp] theorem toChannel_kraus (Φ : QuantumChannel ι N M) : Φ.toChannel.kraus = Φ.kraus := rfl
@[simp] theorem ofChannel_kraus (Φ : Channel (Fin N) (Fin M) ι) : (ofChannel Φ).kraus = Φ.kraus := rfl

/-- **The two channel types are the same data.** -/
def channelEquiv : QuantumChannel ι N M ≃ Channel (Fin N) (Fin M) ι where
  toFun := toChannel
  invFun := ofChannel
  left_inv Φ := by cases Φ; rfl
  right_inv Φ := by cases Φ; rfl

/-- **The actions agree.** -/
theorem toChannel_apply (Φ : QuantumChannel ι N M) (ρ : Matrix (Fin N) (Fin N) ℂ) :
    Φ.toChannel.apply ρ = Φ.apply ρ := rfl

theorem ofChannel_apply (Φ : Channel (Fin N) (Fin M) ι) (ρ : Matrix (Fin N) (Fin N) ℂ) :
    (ofChannel Φ).apply ρ = Φ.apply ρ := rfl

/-- The action on density operators is the `QuantumInfo` action on the underlying matrix. -/
theorem channelApply_M_eq (Φ : QuantumChannel ι N M) (ρ : DensityOperator N) :
    (Φ.channelApply ρ).M = Φ.toChannel.apply ρ.M := rfl

/-- The LF2 dilation is the `QuantumInfo` Stinespring isometry. -/
theorem toChannel_stinespringIsom (Φ : QuantumChannel ι N M) :
    Φ.toChannel.stinespringIsom = Φ.dilation := rfl

/-- The LF2 unitary channel and the `QuantumInfo` one act identically. -/
theorem unitaryChannel_apply_eq (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin N) (Fin N) ℂ) :
    (unitaryChannel U hU).toChannel.apply ρ = (Channel.unitaryChannel U hU).apply ρ := by
  rw [toChannel_apply, unitaryChannel_apply, Channel.unitaryChannel_apply]

/-- Composition is respected. -/
theorem toChannel_comp (Ψ : QuantumChannel κ M P) (Φ : QuantumChannel ι N M) :
    (Ψ.comp Φ).toChannel = Ψ.toChannel.comp Φ.toChannel := rfl

/-- ★ **The QIT layer applies to LF2 channels through the bridge**: the data-processing inequality
for the trace distance of two density operators under an LF2 channel. -/
theorem traceDist_channelApply_le (Φ : QuantumChannel ι N M) (ρ σ : DensityOperator N) :
    traceDist ((Φ.channelApply ρ).isHermitian.sub (Φ.channelApply σ).isHermitian)
      ≤ traceDist (ρ.isHermitian.sub σ.isHermitian) :=
  channel_traceDist_le Φ.toChannel ρ.isHermitian σ.isHermitian
    (ρ.trace_one.trans σ.trace_one.symm)

end QuantumChannel
end CSD.LF2

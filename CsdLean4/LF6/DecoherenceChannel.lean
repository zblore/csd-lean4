/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.FlowChannel
public import CsdLean4.LF6.Decoherence

/-!
# The de-isolation channel: `decohereReduced` is the action of a `QuantumInfo.Channel`

**Category:** 3-Local (W5's witness half, `specs/qit-chain-scoping.md`; the LF6 instance of
`LF2/FlowChannel.lean`).

`LF6/Decoherence.lean` computes the system's reduced state after the von Neumann de-isolation
and the pointer trace, `decohereReduced ψ = Tr_ptr (V |ψ⟩⟨ψ| Vᴴ)` with `V = vnDilationV N =
vnUnitary N * embedGround N`. Until now it was a matrix nothing in `Mathlib/QuantumInfo/` could
consume as a channel output. This module states it as one:

* `embedGround_eq_embedEnv` — LF5's ground embedding is `embedEnv` with the ready vector
  `a₀ = e₀`, so `vnDilationV N` is the isometry `U · embedEnv e₀` of `stinespringChannel`;
* `deisolationChannel N` — **the de-isolation channel**, the Stinespring channel of `vnUnitary N`
  with the apparatus ready in `a₀`: a `QuantumInfo.Channel (Fin N) (Fin N) (Fin N)`;
* ★ `deisolationChannel_apply_outerProduct` — `(deisolationChannel N).apply |ψ⟩⟨ψ| =
  decohereReduced ψ`, and `deisolationChannel_apply` on any input.

So every channel theorem of the QIT layer (`apply_posSemidef`, `apply_trace`, data processing,
`Stinespring.lean`) applies to the decohered state by instantiation, and the LF6 decoherence
results become statements about a channel produced by a `Σ`-flow (`traceRight_barycenter_flow`
in `LF2/FlowChannel.lean` with `U := vnUnitary N`, `e₀ := a₀`).

Scope: the channel-level bridge for the decohered state. The other half of W5, the equivalence
`LF2.QuantumChannel ≃ QuantumInfo.Channel` with the parallel type marked an interface, is
`LF2/ChannelBridge.lean`.

References: `specs/qit-chain-scoping.md` (W5, W6); `LF2/FlowChannel.lean`;
`LF5/DilationFromFlow.lean` (`embedGround`, `vnDilationV`, `vnDilationV_isom`);
`LF6/Decoherence.lean` (`decohereReduced`, `decoherence_dephases`).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder Kronecker

namespace CSD
namespace LF6

open CSD.LF2 CSD.LF5

variable {N : ℕ} [NeZero N]

/-- The LF5 ground embedding is `embedEnv` with the ready vector `a₀ = e₀`. -/
theorem embedGround_eq_embedEnv :
    embedGround N = embedEnv (Fin N) (EuclideanSpace.single (0 : Fin N) (1 : ℂ)) := by
  ext ⟨j, k⟩ m
  rw [embedGround_apply, embedEnv_apply]
  simp only [PiLp.single_apply, Prod.mk.injEq]
  by_cases hj : j = m
  · subst hj
    by_cases hk : k = 0
    · subst hk; simp
    · simp [hk]
  · simp [hj]

/-- `vnUnitary N` in the `Uᴴ U = 1` form the channel constructor takes. -/
theorem vnUnitary_conjTranspose_mul : (vnUnitary N)ᴴ * vnUnitary N = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp vnUnitary_mem_unitaryGroup

/-- **The de-isolation channel**: the Stinespring channel of the von Neumann coupling with the
apparatus ready in `a₀`. -/
noncomputable def deisolationChannel (N : ℕ) [NeZero N] : Channel (Fin N) (Fin N) (Fin N) :=
  stinespringChannel (vnUnitary N) vnUnitary_conjTranspose_mul
    (EuclideanSpace.single (0 : Fin N) (1 : ℂ)) (by rw [PiLp.norm_single]; exact norm_one)

/-- ★ **`decohereReduced` IS the action of a `QuantumInfo.Channel`** — the de-isolation channel
applied to the pure input `|ψ⟩⟨ψ|`. W5's witness half. -/
theorem deisolationChannel_apply_outerProduct (ψ : EuclideanSpace ℂ (Fin N)) :
    (deisolationChannel N).apply (outerProduct ψ) = decohereReduced ψ := by
  rw [deisolationChannel, stinespringChannel, Channel.ofIsometry_apply, decohereReduced,
    ← embedGround_eq_embedEnv]
  rfl

/-- The de-isolation channel on any input is `Tr_ptr (V ρ Vᴴ)` with `V = vnDilationV N`. -/
theorem deisolationChannel_apply (ρ : Matrix (Fin N) (Fin N) ℂ) :
    (deisolationChannel N).apply ρ
      = partialTraceRight (vnDilationV N * ρ * (vnDilationV N)ᴴ) := by
  rw [deisolationChannel, stinespringChannel, Channel.ofIsometry_apply, ← embedGround_eq_embedEnv]
  rfl

end LF6
end CSD

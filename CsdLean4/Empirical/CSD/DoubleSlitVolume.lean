/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.MachZehnderVolume
import CsdLean4.LF6.Decoherence

/-!
# Empirical/CSD: Double-slit interference and Bohr complementarity

**Category:** 3-Local (CSD-ontic layer).

The double slit. A particle in a coherent superposition of two paths (slits `|0⟩`, `|1⟩`)
with relative phase `φ` shows an interference fringe on the screen; measuring **which
slit** the particle went through destroys the fringe. Both halves are here.

**Coherent fringe — the same 2-path physics as Mach–Zehnder.** A two-path single particle
is a qubit, so the screen probability is the FS-volume fringe `cos²(φ/2)` with full
visibility `1` — identical mathematics to `MachZehnderVolume` (both are 2-path qubit
interference), reused honestly rather than re-derived.

**Which-path complementarity — the genuinely distinct content.** When the path is measured
(entangled with a which-path marker and traced out), the reduced state DECOHERES: its
interference coherence — the off-diagonal `decohereReduced ψ i i'` — vanishes
(`CSD.LF6.decoherence_offdiagonal_vanish`), and the pattern collapses to the flat classical
mixture of the two slit Born intensities (`CSD.LF6.decoherence_diagonal_born`). So the fringe
disappears: **visibility drops from 1 to 0.** This is Bohr complementarity, the physical
heart of the double slit and the part Mach–Zehnder does not carry.

## Honest scope

The fringe value reuses the qubit interference derivation (`MachZehnder`/`Ramsey`); the new
content is the complementarity (which-path ⇒ zero interference coherence), built on the LF6-B
decoherence stratum. As with the whole volume series, the moment-region ↔ physical-screen-
point labelling is the interpretive LF4-todo §14 boundary; the fringe `cos²(φ/2)`, the
visibility `1`, and the which-path coherence loss are derived.

References: `Empirical/CSD/MachZehnderVolume.lean`, `LF6/Decoherence.lean`
(`decohereReduced`, `decoherence_offdiagonal_vanish`, `decoherence_diagonal_born`),
`Empirical/CSD/Einselection.lean`, `specs/qm-empirical-tests.md`.
-/

open CSD.Empirical.CSDBridge

namespace CSD
namespace Empirical
namespace CSDBridge
namespace DoubleSlit

/-- **Coherent double-slit fringe: full visibility `1`.** With indistinguishable paths the
two-slit single particle is a qubit interferometer, so the screen fringe is `cos²(φ/2)` with
visibility `1` (`MachZehnder.mz_visibility_one`; same 2-path physics). -/
theorem doubleslit_coherent_visibility_one : MachZehnder.mzVisibility = 1 :=
  MachZehnder.mz_visibility_one

/-- **Which-path measurement destroys the interference (Bohr complementarity).** After the
path is measured, the reduced state's interference coherence — the off-diagonal
`decohereReduced ψ i i'` for `i ≠ i'` — vanishes. The phase-dependent cross term that produces
the fringe is gone. -/
theorem doubleslit_whichpath_coherence_vanishes
    {N : ℕ} [NeZero N] (ψ : EuclideanSpace ℂ (Fin N)) {i i' : Fin N} (h : i ≠ i') :
    CSD.LF6.decohereReduced ψ i i' = 0 :=
  CSD.LF6.decoherence_offdiagonal_vanish ψ h

/-- **The which-path pattern is the flat classical mixture of slit intensities.** The surviving
diagonal of the decohered state is the Born weight `‖⟨eᵢ, ψ⟩‖²` of each slit — a
`φ`-independent (fringe-free) sum of the two single-slit patterns
(`CSD.LF6.decoherence_diagonal_born`). -/
alias doubleslit_whichpath_pattern_born := CSD.LF6.decoherence_diagonal_born

/-- **Double-slit complementarity, in one statement.** With indistinguishable paths the fringe
has full visibility `1`; once which-path is measured, every interference coherence vanishes,
so the fringe is gone (visibility `0`). Interference and which-path knowledge are mutually
exclusive. -/
theorem doubleslit_complementarity {N : ℕ} [NeZero N] (ψ : EuclideanSpace ℂ (Fin N)) :
    MachZehnder.mzVisibility = 1
      ∧ ∀ {i i' : Fin N}, i ≠ i' → CSD.LF6.decohereReduced ψ i i' = 0 :=
  ⟨MachZehnder.mz_visibility_one, fun h => CSD.LF6.decoherence_offdiagonal_vanish ψ h⟩

end DoubleSlit
end CSDBridge
end Empirical
end CSD

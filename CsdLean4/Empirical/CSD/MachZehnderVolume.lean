/-
Copyright (c) 2026 CSD contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CsdLean4.Empirical.Metrology.Ramsey

/-!
# Empirical/CSD: Mach–Zehnder single-photon interference (CSD Born-as-volume)

**Category:** 3-Local (CSD-ontic layer; genuine volume derivation).

The Mach–Zehnder interferometer — a single photon split by a beam splitter, given a
relative phase `φ` in one arm, recombined by a second beam splitter, then detected — is
the most iconic interference experiment, and was the one conspicuous phenomenon missing
from the empirical tree (roadmap B4). This module supplies it as a CSD Born-as-volume
derivation.

**A single photon in two modes IS a qubit**, and the MZ circuit is the qubit phase
circuit `H · D(φ) · H · |0⟩` (beam splitter = `H`, arm phase = `D(φ) = diag(1, e^{iφ})`).
The corpus already has this state as `Metrology.ramseyVec φ` — and `ramseyVec_eq_circuit`
*machine-checks* that the closed form genuinely equals the interferometer circuit output.
So the MZ fringe legitimately reuses the qubit interference machinery
(`ramsey_fringe_volume`): the detector-0 probability is the Fubini–Study volume
`cos²(φ/2)`, `Born = FS volume` derived one layer down (Duistermaat–Heckman), carving-
free and Gleason-free.

## What is genuinely new here (beyond the Ramsey fringe)

The **interferometric visibility** `V = (P_max − P_min)/(P_max + P_min) = 1` for a pure
single photon — the canonical full-coherence result. `mz_bright`/`mz_dark` give the
constructive (`P(0) = 1`) and destructive (`P(π) = 0`) fringes, `mzProb_{nonneg,le_one}`
show these are the genuine extrema of `cos²(φ/2) ∈ [0,1]`, and `mz_visibility_one`
concludes `V = 1`.

## Honest scope

The fringe *value* reuses the Ramsey qubit derivation (same physics: a two-mode single
photon is a qubit). The new content is the visibility. As with the whole volume series,
the moment-region ↔ physical-detector-outcome labelling is the interpretive LF4-todo §14
boundary; the number `cos²(φ/2)` and the visibility `1` are derived.

References: `Empirical/Metrology/Ramsey.lean` (`ramseyVec`, `ramseyVec_eq_circuit`,
`ramseyFringe`, `ramsey_fringe_volume`, `ramsey_fringe_max/min`), `FND/Interference.lean`
(`HasBornInterference`), `specs/qm-empirical-tests.md` (B4).
-/

open CSD.Empirical.Metrology

namespace CSD
namespace Empirical
namespace CSDBridge
namespace MachZehnder

/-- **The Mach–Zehnder output state.** The two-beam-splitter-plus-phase circuit
`H · D(φ) · H · |0⟩`, which the corpus proves (machine-checked, `ramseyVec_eq_circuit`)
equals `ramseyVec φ`. -/
noncomputable def mzOutput (φ : ℝ) : EuclideanSpace ℂ (Fin 2) := ramseyVec φ

/-- **The Mach–Zehnder detector-0 probability** as a function of the arm phase `φ`:
the Fubini–Study volume `cos²(φ/2)` (`= ramseyFringe φ`). -/
noncomputable def mzProb (φ : ℝ) : ℝ := ramseyFringe φ

theorem mzProb_eq (φ : ℝ) : mzProb φ = Real.cos (φ / 2) ^ 2 := rfl

/-- The MZ probability is a genuine probability in `[0, 1]` — lower bound. -/
theorem mzProb_nonneg (φ : ℝ) : 0 ≤ mzProb φ := by
  rw [mzProb_eq]; exact sq_nonneg _

/-- The MZ probability is a genuine probability in `[0, 1]` — upper bound. -/
theorem mzProb_le_one (φ : ℝ) : mzProb φ ≤ 1 := by
  rw [mzProb_eq]
  nlinarith [Real.cos_le_one (φ / 2), Real.neg_one_le_cos (φ / 2)]

/-- **Bright fringe** (constructive interference): at zero relative phase the photon exits
detector 0 with certainty, `P(0) = 1`. -/
theorem mz_bright : mzProb 0 = 1 := ramsey_fringe_max

/-- **Dark fringe** (destructive interference): at phase `π` detector 0 never fires,
`P(π) = 0`. -/
theorem mz_dark : mzProb Real.pi = 0 := ramsey_fringe_min

/-- **Interferometric visibility** `V = (P_max − P_min)/(P_max + P_min)`, with the extrema
attained at the bright (`φ = 0`) and dark (`φ = π`) fringes (`mzProb_{nonneg,le_one}`
confirm these bound `cos²(φ/2)`). -/
noncomputable def mzVisibility : ℝ :=
  (mzProb 0 - mzProb Real.pi) / (mzProb 0 + mzProb Real.pi)

/-- **Mach–Zehnder visibility = 1 for a pure single photon.** The canonical full-coherence
result: the fringe swings between `P = 1` (bright) and `P = 0` (dark), so
`V = (1 − 0)/(1 + 0) = 1`. This is the iconic interference signature, here derived from the
Born-as-volume fringe `cos²(φ/2)` (`mz_bright`, `mz_dark`). -/
theorem mz_visibility_one : mzVisibility = 1 := by
  unfold mzVisibility
  rw [mz_bright, mz_dark]
  norm_num

/-- **The MZ fringe as a genuine Fubini–Study volume.** i.i.d. FS-typicality trials scoring
the moment-sublevel region cut by the MZ output ray have empirical frequency converging
a.s. to `cos²(φ/2)` — `Born = FS volume`, carving-free and Gleason-free (reused from the
qubit interference derivation `Metrology.ramsey_fringe_volume`; the MZ output IS
`ramseyVec φ`). -/
alias mz_fringe_volume := ramsey_fringe_volume

end MachZehnder
end CSDBridge
end Empirical
end CSD

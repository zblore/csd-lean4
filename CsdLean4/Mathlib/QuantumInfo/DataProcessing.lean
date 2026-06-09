import CsdLean4.Mathlib.QuantumInfo.Channel
import CsdLean4.Mathlib.QuantumInfo.CanonicalChannels
import CsdLean4.Mathlib.QuantumInfo.TraceDistance

/-!
# Data-processing inequality for the trace distance (K3)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **CPTP data-processing inequality** for the trace distance: a quantum channel cannot
increase distinguishability,

  `traceDist (Φ ρ) (Φ σ) ≤ traceDist ρ σ`     (`channel_traceDist_le`),

for Hermitian, equal-trace `ρ, σ` (in particular any two density operators). This is the
final K3 metric property after non-negativity, the distinguishability headline, symmetry,
and the triangle inequality (`TraceDistance.lean`).

## Route — the variational characterisation

For a **traceless** Hermitian difference `D = ρ − σ` the trace distance collapses to a single
trace,

  `traceDist D = Re Tr(D₊)`     (`traceDist_eq_re_trace_posPart`),

since `Tr|D| = Tr(D₊) + Tr(D₋)` while `Tr(D₊) − Tr(D₋) = Tr D = 0` forces the two parts to
have equal trace. The positive part is realised as `D₊ = D · P₊` at the positive-eigenspace
projector `P₊` (`mul_posProj_eq_posPart`), giving the variational reading
`Re Tr(D₊) = Re Tr(P₊ · D) = max₀≤P≤I Re Tr(P · D)` — the maximum is *attained* at `P = P₊`,
so no `sSup` is needed.

The headline then chains: the optimal projector on the channel side, `P := P₊(Φ ρ − Φ σ)`,
is pulled back through the **channel adjoint** (`Channel.adjoint`, `Φ†(P) = ∑ᵢ Kᵢᴴ P Kᵢ`)
using the trace duality `Tr(P · Φ D) = Tr(Φ† P · D)` (`adjoint_trace_mul`). Unitality and
positivity of the adjoint give `0 ≤ Φ† P ≤ I` (`adjoint_le_one`), so `Φ† P` is an admissible
projector *candidate* on the input side, and the operator bound
`Re Tr(D · Q) ≤ Re Tr(D₊)` (`re_trace_mul_le_re_trace_posPart`, the L6 key bound from
`TraceDistance.lean`) closes the inequality. The whole argument consumes the channel adjoint
(unital + positive ⟹ `0 ≤ Φ† P ≤ I`) and the `posPart`/`posProj` Jordan machinery.
-/

open Matrix
open scoped ComplexOrder

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Variational collapse for a traceless Hermitian difference:** `traceDist D = Re Tr(D₊)`.
From `traceNorm D = Re Tr(D₊) + Re Tr(D₋)` (Jordan split) and `Re Tr(D₊) = Re Tr(D₋)`, which
holds because `Tr(D₊) − Tr(D₋) = Tr D = 0`. -/
lemma traceDist_eq_re_trace_posPart {ρ σ : Matrix n n ℂ} (h : (ρ - σ).IsHermitian)
    (htr : (ρ - σ).trace = 0) :
    traceDist h = RCLike.re (posPart h).trace := by
  -- Re Tr(D₊) − Re Tr(D₋) = Re Tr D = 0.
  have hdiff : RCLike.re (posPart h).trace - RCLike.re (negPart h).trace = 0 := by
    have hps : (posPart h - negPart h).trace = (ρ - σ).trace := by
      rw [posPart_sub_negPart h]
    rw [Matrix.trace_sub] at hps
    rw [← map_sub, hps, htr, map_zero]
  -- traceDist = (Re Tr(D₊) + Re Tr(D₋)) / 2 = Re Tr(D₊).
  rw [traceDist, traceNorm_eq_re_trace_posPart_add_negPart h]
  have : RCLike.re (negPart h).trace = RCLike.re (posPart h).trace := by linarith
  rw [this]; ring

/-- **Data-processing inequality for the trace distance.** A quantum channel cannot increase
distinguishability: `traceDist (Φ ρ) (Φ σ) ≤ traceDist ρ σ`, for Hermitian, equal-trace
`ρ, σ` (so in particular for any two density operators). Via the variational characterisation
`traceDist D = Re Tr(D₊)`, the channel adjoint pull-back `Tr(P · Φ D) = Tr(Φ† P · D)`, and the
operator bound `Re Tr(D · Q) ≤ Re Tr(D₊)` at the admissible `Q = Φ† P₊` with `0 ≤ Q ≤ I`. -/
theorem channel_traceDist_le {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq m]
    (Φ : Channel n m ι) {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (htr : ρ.trace = σ.trace) :
    traceDist ((Φ.apply_isHermitian hρ).sub (Φ.apply_isHermitian hσ)) ≤ traceDist (hρ.sub hσ) := by
  set h : (ρ - σ).IsHermitian := hρ.sub hσ with hh
  set hΦ : (Φ.apply ρ - Φ.apply σ).IsHermitian :=
    (Φ.apply_isHermitian hρ).sub (Φ.apply_isHermitian hσ) with hhΦ
  -- The two difference matrices are traceless.
  have htrD : (ρ - σ).trace = 0 := by rw [Matrix.trace_sub, htr, sub_self]
  have hΦeq : Φ.apply ρ - Φ.apply σ = Φ.apply (ρ - σ) := (Φ.apply_sub ρ σ).symm
  have htrΦ : (Φ.apply ρ - Φ.apply σ).trace = 0 := by
    rw [hΦeq, Φ.apply_trace, htrD]
  -- Variational form on the channel side.
  rw [traceDist_eq_re_trace_posPart hΦ htrΦ, traceDist_eq_re_trace_posPart h htrD]
  -- D₊(ΦD) = (ΦD)·P₊, then rotate and pull through the adjoint.
  set Pproj : Matrix m m ℂ := posProj hΦ with hPproj
  have step1 : RCLike.re (posPart hΦ).trace
      = RCLike.re (Pproj * Φ.apply (ρ - σ)).trace := by
    rw [← mul_posProj_eq_posPart hΦ, ← hPproj, Matrix.trace_mul_comm, hΦeq]
  -- Pull the projector through the adjoint: Tr(P · Φ D) = Tr(Φ† P · D).
  have step2 : RCLike.re (Pproj * Φ.apply (ρ - σ)).trace
      = RCLike.re (Φ.adjoint Pproj * (ρ - σ)).trace := by
    rw [Φ.adjoint_trace_mul Pproj (ρ - σ)]
  -- Q := Φ† P₊ is an admissible projector candidate on the input: 0 ≤ Q ≤ I.
  set Q : Matrix n n ℂ := Φ.adjoint Pproj with hQ
  have hQpsd : Q.PosSemidef := Φ.adjoint_posSemidef (posProj_posSemidef hΦ)
  have hQle : ((1 : Matrix n n ℂ) - Q).PosSemidef :=
    Φ.adjoint_le_one (posProj_posSemidef hΦ) (one_sub_posProj_posSemidef hΦ)
  -- Operator bound: Re Tr((ρ−σ)·Q) ≤ Re Tr((ρ−σ)₊).
  have step3 : RCLike.re (Q * (ρ - σ)).trace ≤ RCLike.re (posPart h).trace := by
    rw [Matrix.trace_mul_comm]
    exact re_trace_mul_le_re_trace_posPart h hQpsd hQle
  rw [step1, step2]
  exact step3

/-- **The trace distance of two states is at most one** (boundedness of the metric on the
density-operator set). For PSD unit-trace `ρ, σ`, `traceDist ρ σ ≤ 1`. Via the variational
form `traceDist D = Re Tr(D₊) = Re Tr((ρ−σ)·P₊)`, dropping the `σ` term (`Tr(σ·P₊) ≥ 0`) and
bounding `Re Tr(ρ·P₊) ≤ Re Tr ρ = 1` (from `Tr(ρ·(1−P₊)) ≥ 0`), both by `tr_psd_mul_nonneg`. -/
lemma traceDist_le_one {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htrρ : ρ.trace = 1) (htrσ : σ.trace = 1) :
    traceDist (hρ.1.sub hσ.1) ≤ 1 := by
  set h : (ρ - σ).IsHermitian := hρ.1.sub hσ.1 with hh
  -- The difference is traceless.
  have htrD : (ρ - σ).trace = 0 := by rw [Matrix.trace_sub, htrρ, htrσ, sub_self]
  -- Variational form: traceDist = Re Tr((ρ−σ)·P₊).
  set Pp : Matrix n n ℂ := posProj h with hPp
  rw [traceDist_eq_re_trace_posPart h htrD]
  have step1 : RCLike.re (posPart h).trace = RCLike.re ((ρ - σ) * Pp).trace := by
    rw [← mul_posProj_eq_posPart h, ← hPp]
  rw [step1, Matrix.sub_mul, Matrix.trace_sub, map_sub]
  -- Drop the σ-term: 0 ≤ Re Tr(σ·P₊).
  have hσP : 0 ≤ RCLike.re (σ * Pp).trace :=
    tr_psd_mul_nonneg hσ (posProj_posSemidef h)
  -- Bound Re Tr(ρ·P₊) ≤ Re Tr ρ = 1, since 0 ≤ Re Tr(ρ·(1−P₊)) = Re Tr ρ − Re Tr(ρ·P₊).
  have hρsplit : RCLike.re (ρ * Pp).trace ≤ RCLike.re ρ.trace := by
    have hnn : 0 ≤ RCLike.re (ρ * ((1 : Matrix n n ℂ) - Pp)).trace :=
      tr_psd_mul_nonneg hρ (one_sub_posProj_posSemidef h)
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, map_sub] at hnn
    linarith
  have htrρ_re : RCLike.re ρ.trace = 1 := by rw [htrρ]; simp
  -- Chain: Re Tr(ρ·P₊) − Re Tr(σ·P₊) ≤ Re Tr(ρ·P₊) ≤ Re Tr ρ = 1.
  rw [htrρ_re] at hρsplit
  linarith

/-- **Unitary invariance of the trace distance** (the equality case of data processing): for a
unitary `U` (`Uᴴ U = 1`) and Hermitian, equal-trace `ρ, σ`,
`traceDist (UρUᴴ − UσUᴴ) = traceDist (ρ − σ)`. Proved via `channel_traceDist_le` applied to
the `unitaryChannel` in **both directions** (the reverse using the channel of `Uᴴ`, which is
unitary since `U Uᴴ = 1` by `Matrix.mul_eq_one_comm`), then `le_antisymm` after collapsing
`Uᴴ(UρUᴴ)U = ρ`. -/
lemma traceDist_conj_unitary {U : Matrix n n ℂ} (hU : Uᴴ * U = 1)
    {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (htr : ρ.trace = σ.trace)
    (hUconj : (U * ρ * Uᴴ - U * σ * Uᴴ).IsHermitian) :
    traceDist hUconj = traceDist (hρ.sub hσ) := by
  -- The reverse-direction unitary: Uᴴ, with (Uᴴ)ᴴ Uᴴ = U Uᴴ = 1 (mul_eq_one_comm).
  have hUUstar : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hUstar : (Uᴴ)ᴴ * Uᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hUUstar
  -- Name the two channels with the universe of the Kraus index pinned to `PUnit.{1}`.
  set ΦU : Channel n n PUnit.{1} := Channel.unitaryChannel U hU with hΦU
  set ΦUs : Channel n n PUnit.{1} := Channel.unitaryChannel Uᴴ hUstar with hΦUs
  -- The unitaryChannel actions.
  have hapU : ∀ τ : Matrix n n ℂ, ΦU.apply τ = U * τ * Uᴴ :=
    fun τ => Channel.unitaryChannel_apply U hU τ
  have hapUs : ∀ τ : Matrix n n ℂ, ΦUs.apply τ = Uᴴ * τ * U := by
    intro τ; rw [hΦUs, Channel.unitaryChannel_apply Uᴴ hUstar τ, Matrix.conjTranspose_conjTranspose]
  -- Trace of the conjugated states: Tr(UτUᴴ) = Tr τ (cyclicity + Uᴴ U = 1).
  have htrconj : ∀ τ : Matrix n n ℂ, (U * τ * Uᴴ).trace = τ.trace := by
    intro τ; rw [Matrix.trace_mul_comm (U * τ) Uᴴ, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have htr' : (U * ρ * Uᴴ).trace = (U * σ * Uᴴ).trace := by rw [htrconj ρ, htrconj σ, htr]
  -- Hermiticity of the conjugated states.
  have hUrhoUs_herm : (U * ρ * Uᴴ).IsHermitian := by
    have := ΦU.apply_isHermitian hρ; rwa [hapU ρ] at this
  have hUsigUs_herm : (U * σ * Uᴴ).IsHermitian := by
    have := ΦU.apply_isHermitian hσ; rwa [hapU σ] at this
  -- Forward DP: traceDist (UρUᴴ − UσUᴴ) ≤ traceDist (ρ − σ).
  have hfwd := channel_traceDist_le ΦU hρ hσ htr
  -- Reverse DP applied to the conjugated states with the channel of Uᴴ.
  have hrev := channel_traceDist_le ΦUs hUrhoUs_herm hUsigUs_herm htr'
  -- The collapse Uᴴ(UτUᴴ)U = τ.
  have hcollapse : ∀ τ : Matrix n n ℂ, Uᴴ * (U * τ * Uᴴ) * U = τ := by
    intro τ
    rw [show Uᴴ * (U * τ * Uᴴ) * U = (Uᴴ * U) * τ * (Uᴴ * U) by
          simp only [Matrix.mul_assoc],
      hU, Matrix.one_mul, Matrix.mul_one]
  -- Restate hfwd in terms of hUconj (the LHS difference matrices agree).
  have hfwd' : traceDist hUconj ≤ traceDist (hρ.sub hσ) := by
    rw [traceDist_congr hUconj
      ((ΦU.apply_isHermitian hρ).sub (ΦU.apply_isHermitian hσ))
      (by rw [hapU ρ, hapU σ])]
    exact hfwd
  -- Restate hrev: its LHS difference is ρ − σ (after collapse), its RHS is traceDist hUconj.
  have hrev' : traceDist (hρ.sub hσ) ≤ traceDist hUconj := by
    rw [traceDist_congr (hρ.sub hσ)
      ((ΦUs.apply_isHermitian hUrhoUs_herm).sub (ΦUs.apply_isHermitian hUsigUs_herm))
      (by rw [hapUs (U * ρ * Uᴴ), hapUs (U * σ * Uᴴ), hcollapse ρ, hcollapse σ])]
    -- hrev's RHS is traceDist (UρUᴴ − UσUᴴ); rewrite it to traceDist hUconj.
    rw [show traceDist (hUrhoUs_herm.sub hUsigUs_herm) = traceDist hUconj from
      traceDist_congr (hUrhoUs_herm.sub hUsigUs_herm) hUconj rfl] at hrev
    exact hrev
  exact le_antisymm hfwd' hrev'

end QuantumInfo

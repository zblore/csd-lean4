import CsdLean4.Mathlib.QuantumInfo.Channel
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

end QuantumInfo

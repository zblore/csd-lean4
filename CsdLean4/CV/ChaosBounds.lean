/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.InteractionPrice
public import CsdLean4.CV.SupportSpreading
public import CsdLean4.Incubator.QuantumChaos.EchoBound
public import CsdLean4.Incubator.QuantumChaos.Otoc
public import CsdLean4.Incubator.QuantumChaos.SpectralFormFactor

/-!
# Chaos diagnostics meet Stage 3: the light-cone gate and the echo price

**Category:** CV (continuous variables — the multi-mode field).

The §H diagnostics (`Diagnostics`, `EchoBound`, `Otoc`,
`SpectralFormFactor`) instantiated on the Stage-3 interacting field, where
the CV structure turns a-priori envelopes into sharp structural statements:

* ★★ `otoc_graphInteractingU_eq_zero` — **the OTOC light-cone gate**:
  for `A` supported on `R` and a static probe `B` supported on `T`, the
  out-of-time-order commutator is EXACTLY zero at every period `n` for
  which the coupling graph's `n`-ball of `R` is still disjoint from `T`.
  **Scrambling cannot begin before `A`'s light cone reaches the probe** —
  the CV-8 cone re-expressed as the standard chaos diagnostic.
* ★★ `one_sub_loschmidtEcho_interacting_le` — **the echo price**:
  Loschmidt decay between the free and interacting drives is at most
  `2n·|τ|·|λ|·C` — linear in period count and coupling, with the CV-9
  Duhamel price as the per-period rate. The third linear-pricing rhyme
  (records: `μ ≤ n·ε`; locality: `2|τ||λ|C‖A‖`; echo: `2n|τ||λ|C`).
* `sff_freeFieldU` — the free field's spectral form factor as an explicit
  exponential sum over configurations: the integrable-case baseline that
  chaotic drives are diagnosed against.
* `heisenberg_eq_chaos` — the definitional bridge between the CV-6
  Heisenberg conjugation and the interface-level one (same formula, one
  seam).

Honest scope: the gate is exact but one-directional (no claim the OTOC
grows once the cones touch); the echo bound is an upper bound on decay;
no random-matrix or Lyapunov-rate statements — growth rates and level
statistics are the §H thread's recorded continuation.

## References

`CV/SupportSpreading.lean` (CV-8, the cone);
`CV/InteractionPrice.lean` (CV-9, the price);
`Incubator/QuantumChaos/{Diagnostics,EchoBound,Otoc,SpectralFormFactor}.lean`;
`specs/external-library-map.md` §H; `specs/future-work.md`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ}

/-- The CV-6 Heisenberg conjugation and the interface-level one agree
definitionally. -/
lemma heisenberg_eq_chaos (U : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    heisenberg U A = _root_.QuantumChaos.heisenberg U A := rfl

/-- ★★ **The OTOC light-cone gate**: for `A` supported on `R` and a static
probe `B` supported on `T`, the out-of-time-order commutator vanishes
EXACTLY at every period for which the coupling graph's `n`-ball of `R` is
still disjoint from `T` — scrambling cannot begin before `A`'s light cone
reaches the probe. -/
theorem otoc_graphInteractingU_eq_zero {R T : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ lam : ℝ)
    (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) (n : ℕ)
    (hRT : Disjoint (graphBall E R n) T)
    (hA : SupportedOn R A) (hB : SupportedOn T B) :
    _root_.QuantumChaos.otoc (graphInteractingU K N τ lam E g) A B n = 0 :=
  (_root_.QuantumChaos.otoc_eq_zero_iff _ _ _ _).mpr
    (commute_of_disjointSupport hRT
      (heisenberg_graphInteractingU_pow_supportedOn τ lam E g n hA) hB)

/-- ★★ **The echo price**: Loschmidt decay between the free and the
interacting drive is at most `2n·|τ|·|λ|·C` — linear in period count and
coupling, at the CV-9 Duhamel rate. -/
theorem one_sub_loschmidtEcho_interacting_le [NeZero N] (τ lam : ℝ)
    (v : FieldConfig K N → ℝ) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ c, |v c| ≤ C)
    {ψ : FieldSpace K N} (hψ : ‖ψ‖ = 1) (n : ℕ) :
    1 - _root_.QuantumChaos.loschmidtEcho (freeFieldFloquet K N τ)
        (interactingFloquet K N τ lam v) ψ n
      ≤ 2 * (n * (|τ| * (|lam| * C))) := by
  refine le_trans (_root_.QuantumChaos.one_sub_loschmidtEcho_le
    (freeFieldU K N τ) (interactingU K N τ lam v) hψ n) ?_
  gcongr
  rw [norm_sub_rev]
  exact interactingU_dist_le τ lam v hC hv

/-- **The free field's spectral form factor is an explicit exponential
sum** over configurations — the integrable baseline. -/
theorem sff_freeFieldU (K N : ℕ) (τ : ℝ) (n : ℕ) :
    _root_.QuantumChaos.sff (freeFieldU K N τ) n
      = ‖∑ c : FieldConfig K N,
          Complex.exp (-(Complex.I * ((τ * fieldEnergy c : ℝ) : ℂ))) ^ n‖ ^ 2
        / (Fintype.card (FieldConfig K N) : ℝ) ^ 2 :=
  _root_.QuantumChaos.sff_diagonal
    (u := fun c => Complex.exp
      (-(Complex.I * ((τ * fieldEnergy c : ℝ) : ℂ)))) rfl n

end CSD.CV

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.CarrierPersistence
public import CsdLean4.CV.DynamicalLocality
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

/-! ### Q3: diagnostics beyond the gate — slow scrambling, exact revival

The OTOC gate above says scrambling cannot *begin* before the light cone
arrives. The two results below complete the diagnostics pair
(`specs/BACKLOG.md` §Q Q3): once the cone does arrive, scrambling in the
kicked-diagonal family grows at most **linearly** — there is no fast
scrambling in this model — and the free field's spectral form factor shows
**exact periodic revivals**, the clean integrable signature against which
chaotic ramps would be measured. -/

/-- ★★ **Slow scrambling — the OTOC growth cap.** For disjointly supported
observable and probe, the out-of-time-order commutator after `n` interacting
periods is at most `4n·|τ|·|λ|·C·‖A‖·‖B‖`: linear in period count at the
Duhamel rate. The free evolution keeps `A` on its support (so the OTOC is
zero along the free comparison), and the interacting evolution differs from
it by at most the telescoped drive distance — scrambling in the
kicked-diagonal family is at most linear, never exponential. -/
theorem otoc_interactingU_le [NeZero N] {R T : Finset (Fin K)}
    (hRT : Disjoint R T) (τ lam : ℝ) (v : FieldConfig K N → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ c, |v c| ≤ C)
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) (hB : SupportedOn T B) (n : ℕ) :
    _root_.QuantumChaos.otoc (interactingU K N τ lam v) A B n
      ≤ 4 * n * (|τ| * (|lam| * C)) * ‖A‖ * ‖B‖ := by
  set Aint := heisenberg (interactingU K N τ lam v ^ n) A with hAint
  set Afree := heisenberg (freeFieldU K N τ ^ n) A with hAfree
  have hfree_comm : Afree * B = B * Afree :=
    commute_of_disjointSupport hRT
      (heisenberg_freeFieldU_pow_supportedOn τ n hA) hB
  have hdist : ‖Aint - Afree‖ ≤ 2 * (n * (|τ| * (|lam| * C))) * ‖A‖ := by
    have h1 : ‖((interactingU K N τ lam v) ^ n).val
          - ((freeFieldU K N τ) ^ n).val‖
        ≤ n * ‖(interactingU K N τ lam v).val - (freeFieldU K N τ).val‖ :=
      norm_unitary_pow_sub_pow_le _ _ n
    have h2 := interactingU_dist_le τ lam v hC hv
    have h3 : ‖((interactingU K N τ lam v) ^ n).val
          - ((freeFieldU K N τ) ^ n).val‖
        ≤ n * (|τ| * (|lam| * C)) := by
      refine h1.trans ?_
      gcongr
    refine (heisenberg_dist_le _ _ A).trans ?_
    gcongr
  have hcomm_id : Aint * B - B * Aint
      = (Aint - Afree) * B - B * (Aint - Afree) := by
    have hz : Afree * B - B * Afree = 0 := by rw [hfree_comm, sub_self]
    have hexpand : (Aint - Afree) * B - B * (Aint - Afree)
        = (Aint * B - B * Aint) - (Afree * B - B * Afree) := by
      noncomm_ring
    rw [hexpand, hz, sub_zero]
  have hfinal : ‖Aint * B - B * Aint‖
      ≤ 4 * n * (|τ| * (|lam| * C)) * ‖A‖ * ‖B‖ := by
    calc ‖Aint * B - B * Aint‖
        = ‖(Aint - Afree) * B - B * (Aint - Afree)‖ := by rw [hcomm_id]
      _ ≤ ‖(Aint - Afree) * B‖ + ‖B * (Aint - Afree)‖ := norm_sub_le _ _
      _ ≤ ‖Aint - Afree‖ * ‖B‖ + ‖B‖ * ‖Aint - Afree‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (2 * (n * (|τ| * (|lam| * C))) * ‖A‖) * ‖B‖
            + ‖B‖ * (2 * (n * (|τ| * (|lam| * C))) * ‖A‖) := by
          gcongr
      _ = 4 * n * (|τ| * (|lam| * C)) * ‖A‖ * ‖B‖ := by ring
  exact hfinal

/-- The free field's phases all coincide at `τ = 2π`: the spectrum is
integer-spaced (`oscEnergy n = n + ½`), so `2π·E(c) ≡ πK (mod 2π)` for
every configuration. -/
lemma freeField_phase_two_pi (K N : ℕ) (c : FieldConfig K N) :
    Complex.exp (-(Complex.I * ((2 * Real.pi * fieldEnergy c : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * Real.pi * K)) := by
  have hE : (fieldEnergy c : ℝ) = ((∑ k, (c k : ℕ) : ℕ) : ℝ) + K * 2⁻¹ := by
    rw [fieldEnergy]
    unfold oscEnergy
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  set m : ℕ := ∑ k, (c k : ℕ) with hm
  rw [hE]
  have hsplit : -(Complex.I * ((2 * Real.pi * ((m : ℝ) + K * 2⁻¹) : ℝ) : ℂ))
      = -(((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        + -(Complex.I * Real.pi * K) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add,
    show -(((m : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
      = ((-(m : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by
      push_cast
      ring,
    Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- ★ **Exact revival — the integrable signature.** At `τ = 2π` the free
field's spectral form factor is exactly `1` at every period count: all
phases coincide, the trace never decays, and the SFF shows none of the
dip–ramp–plateau structure of a scrambling system. The clean baseline the
OTOC cap above is measured against. -/
theorem sff_freeFieldU_revival (K N : ℕ) [NeZero N] (n : ℕ) :
    _root_.QuantumChaos.sff (freeFieldU K N (2 * Real.pi)) n = 1 := by
  rw [_root_.QuantumChaos.sff_diagonal (u := fun c : FieldConfig K N =>
      Complex.exp (-(Complex.I
        * ((2 * Real.pi * fieldEnergy c : ℝ) : ℂ)))) rfl n]
  rw [show ∑ c : FieldConfig K N,
        Complex.exp (-(Complex.I
          * ((2 * Real.pi * fieldEnergy c : ℝ) : ℂ))) ^ n
      = ∑ _c : FieldConfig K N,
          Complex.exp (-(Complex.I * Real.pi * K)) ^ n from
    Finset.sum_congr rfl fun c _ => by rw [freeField_phase_two_pi K N c]]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnorm1 : ‖Complex.exp (-(Complex.I * Real.pi * K))‖ = 1 := by
    rw [Complex.norm_exp]
    rw [show (-(Complex.I * Real.pi * K)).re = 0 from by simp]
    exact Real.exp_zero
  have hcard : (0:ℝ) < (Fintype.card (FieldConfig K N) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [norm_mul, norm_pow, hnorm1, one_pow, mul_one,
    show ‖(Fintype.card (FieldConfig K N) : ℂ)‖
      = (Fintype.card (FieldConfig K N) : ℝ) from Complex.norm_natCast _]
  field_simp

end CSD.CV

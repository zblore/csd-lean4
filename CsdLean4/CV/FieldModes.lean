/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.OscillatorBorn

/-!
# CV/FieldModes: a free scalar field at a cutoff as a product of modes (EFT Stage 1)

**Category:** CV (continuous variables — the multi-mode field).

Stage 1 of the EFT direction: a **free field at a cutoff** = finitely many modes, each a truncated
oscillator. The field Hilbert space is the (truncated) tensor product of the single-mode spaces,
indexed by occupation **configurations** `c : Fin K → Fin N` (mode `k` has `c k` quanta):
`FieldSpace K N = EuclideanSpace ℂ (FieldConfig K N)`.

* `fieldEnergy` / `fieldHamiltonian` / `fieldHamiltonian_mulVec_single` — the free-field Hamiltonian is
  the **sum of the single-mode Hamiltonians**: diagonal in the configuration basis with eigenvalue
  `fieldEnergy c = ∑ₖ oscEnergy (c k)` (free field = sum of oscillators);
* `fieldEnergy_cutoff_independent` — the field energy of a configuration is cutoff-independent
  (the multi-mode analogue of `oscEnergy_cutoff_independent`);
## Honest residue for the CV track

⚠️ CV has no root module, so `EMPIRICAL.md`'s honest-residue paragraph is carried here, at the
field-side entry point (CR-8, 2026-09-05).

The concrete `SectorData` instances behind the CV volume readings still carry `Φ = id` — LF5
exercises a genuine `Φ_vN ≠ id` only on the dilated `Σ'`, not in these instances — so these readings
remain **realisation, not derivation**. The Born value is derived from the posited sector geometry
on `Σ`, which is the standing assumption these results rest on. The Born content additionally rests
on the record layer's cell law: a posit with a characterisation (`specs/POSITS.md` Posit 1; torus
*generation* pins the rate field, torus invariance does not). And the locality proved on this track
is **mode-disjoint commutation**, not the Haag–Kastler axiom — mode sets, no net, no covariance
(`CV/ModeLocality.lean`).

* `fieldBornProb` / `sum_fieldBornProb_unit` — the full-configuration measurement is a standard-basis
  (record-layer) measurement: `‖⟨c|Ψ⟩‖²`, a probability distribution over configurations;
* `tprodState` / `norm_sq_tprodState` — a **product state** `Ψ = ⊗ₖ ψₖ` has `‖Ψ‖² = ∏ₖ ‖ψₖ‖²`; a
  product of unit modes is a unit state (`norm_tprodState_unit`) — the composite (tensor) structure.

This is the free field at a finite cutoff: a finite product `Σ`, with the record layer applying
mode-by-mode. Relativistic dispersion, microcausality, and interactions are the later EFT stages.
Foundational-triple, no `sorry`.

## References
`CV/OscillatorBorn.lean` (the single mode as a record-layer measurement); `CV/OscillatorSpectrum.lean`
(`oscEnergy`, `oscEnergy_cutoff_independent`); `CV/Position.lean` (the spatial-lattice seed);
`RecordLayer/Measurement.lean` (the record layer).
-/

@[expose] public section

open MeasureTheory Matrix

namespace CSD.CV

variable {K N : ℕ}

/-- A field-mode **configuration**: mode `k` carries `c k` quanta (`K` modes, each truncated to `N`
levels). -/
abbrev FieldConfig (K N : ℕ) := Fin K → Fin N

/-- The truncated **multi-mode field Hilbert space**: the (truncated) tensor product of `K` single-mode
spaces, indexed by occupation configurations. -/
abbrev FieldSpace (K N : ℕ) := EuclideanSpace ℂ (FieldConfig K N)

/-- The **field energy** of a configuration: the sum of the mode energies `E_{c_k} = c_k + ½`. -/
noncomputable def fieldEnergy (c : FieldConfig K N) : ℝ := ∑ k, oscEnergy (c k)

/-- The **free-field Hamiltonian**: diagonal in the configuration basis with eigenvalue the field
energy — the sum of the single-mode oscillator Hamiltonians. -/
noncomputable def fieldHamiltonian (K N : ℕ) : Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  Matrix.diagonal (fun c => ((fieldEnergy c : ℝ) : ℂ))

/-- **The configuration `c` is a field-energy eigenstate with eigenvalue `∑ₖ oscEnergy (c k)`.** -/
theorem fieldHamiltonian_mulVec_single (c : FieldConfig K N) :
    (fieldHamiltonian K N).mulVec (Pi.single c 1)
      = ((fieldEnergy c : ℝ) : ℂ) • (Pi.single c 1) := by
  funext d
  rw [fieldHamiltonian, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [h]
  · rw [mul_zero, mul_zero]

/-- **Cutoff-independence of the field energy.** Configurations with the same per-mode occupation have
the same field energy, regardless of the truncation. The multi-mode analogue of
`oscEnergy_cutoff_independent`. -/
theorem fieldEnergy_cutoff_independent {K N M : ℕ} (c : FieldConfig K N) (d : FieldConfig K M)
    (h : ∀ k, (c k : ℕ) = (d k : ℕ)) : fieldEnergy c = fieldEnergy d :=
  Finset.sum_congr rfl fun k _ => oscEnergy_cutoff_independent (c k) (d k) (h k)

/-- The **Born probability of the full occupation configuration `c`** in field state `Ψ`: `‖⟨c|Ψ⟩‖²`.
The configuration basis is the standard basis, so this is the record-layer Born weight. -/
noncomputable def fieldBornProb (Ψ : FieldSpace K N) (c : FieldConfig K N) : ℝ := ‖Ψ c‖ ^ 2

theorem fieldBornProb_eq (Ψ : FieldSpace K N) (c : FieldConfig K N) :
    fieldBornProb Ψ c = ‖Ψ c‖ ^ 2 := rfl

/-- The configuration Born probabilities sum to `1` on a unit field state — a probability distribution
over occupation configurations. -/
theorem sum_fieldBornProb_unit (Ψ : FieldSpace K N) (hΨ : ‖Ψ‖ = 1) :
    ∑ c, fieldBornProb Ψ c = 1 := by
  simp only [fieldBornProb]
  rw [show (∑ c, ‖Ψ c‖ ^ 2) = ‖Ψ‖ ^ 2 from by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)], hΨ, one_pow]

/-- A **product (tensor) field state** `Ψ = ⊗ₖ ψₖ`: the amplitude of configuration `c` is the product
of the per-mode amplitudes `∏ₖ ψₖ (c k)`. -/
noncomputable def tprodState (ψ : Fin K → EuclideanSpace ℂ (Fin N)) : FieldSpace K N :=
  WithLp.toLp 2 (fun c : FieldConfig K N => ∏ k, ψ k (c k))

theorem tprodState_apply (ψ : Fin K → EuclideanSpace ℂ (Fin N)) (c : FieldConfig K N) :
    (tprodState ψ) c = ∏ k, ψ k (c k) := by
  simp [tprodState, WithLp.ofLp_toLp]

/-- **The composite (tensor) structure: norms multiply.** A product state's squared norm is the
product of the mode squared norms, `‖⊗ₖ ψₖ‖² = ∏ₖ ‖ψₖ‖²`. -/
theorem norm_sq_tprodState (ψ : Fin K → EuclideanSpace ℂ (Fin N)) :
    ‖tprodState ψ‖ ^ 2 = ∏ k, ‖ψ k‖ ^ 2 := by
  have hns : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ ^ 2 = ∑ m, ‖v m‖ ^ 2 := fun v => by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [tprodState_apply, norm_prod, ← Finset.prod_pow]
  rw [show (∏ k, ‖ψ k‖ ^ 2) = ∏ k, ∑ m, ‖ψ k m‖ ^ 2 from
    Finset.prod_congr rfl fun k _ => hns (ψ k), Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- A product of unit modes is a unit field state. -/
theorem norm_tprodState_unit (ψ : Fin K → EuclideanSpace ℂ (Fin N)) (hψ : ∀ k, ‖ψ k‖ = 1) :
    ‖tprodState ψ‖ = 1 := by
  have h0 : (0 : ℝ) ≤ ‖tprodState ψ‖ := norm_nonneg _
  have h2 : ‖tprodState ψ‖ ^ 2 = 1 := by
    rw [norm_sq_tprodState, Finset.prod_eq_one fun k _ => by rw [hψ k, one_pow]]
  rw [← Real.sqrt_sq h0, h2, Real.sqrt_one]

/-- The **single-mode marginal Born probability**: the probability that mode `k₀` carries `n` quanta,
summed over the occupations of all the other modes. -/
noncomputable def modeMarginal (Ψ : FieldSpace K N) (k₀ : Fin K) (n : Fin N) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c : FieldConfig K N => c k₀ = n), fieldBornProb Ψ c

/-- **Mode-wise Born (the marginal of a product state).** For a product field state, the marginal Born
probability that mode `k₀` carries `n` quanta factorises as `‖ψ_{k₀} n‖² · ∏_{k≠k₀} ‖ψ k‖²` — the
single-mode Born weight of `k₀`, times the norms of the spectator modes. The modes are independent. -/
theorem modeMarginal_tprod (ψ : Fin K → EuclideanSpace ℂ (Fin N)) (k₀ : Fin K) (n : Fin N) :
    modeMarginal (tprodState ψ) k₀ n
      = ‖ψ k₀ n‖ ^ 2 * ∏ k ∈ Finset.univ.erase k₀, ‖ψ k‖ ^ 2 := by
  classical
  have hns : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ ^ 2 = ∑ m, ‖v m‖ ^ 2 := fun v => by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hb : ∀ c : FieldConfig K N,
      fieldBornProb (tprodState ψ) c = ∏ k, ‖ψ k (c k)‖ ^ 2 := fun c => by
    rw [fieldBornProb, tprodState_apply, norm_prod, ← Finset.prod_pow]
  set H : Fin K → Fin N → ℝ :=
    fun k m => if k = k₀ then (if m = n then ‖ψ k m‖ ^ 2 else 0) else ‖ψ k m‖ ^ 2 with hH
  -- Each masked summand equals the product of the folded per-mode factors `H`.
  have hstep : ∀ c : FieldConfig K N,
      (if c k₀ = n then fieldBornProb (tprodState ψ) c else 0) = ∏ k, H k (c k) := by
    intro c
    rw [hb c, ← Finset.mul_prod_erase _ (fun k => ‖ψ k (c k)‖ ^ 2) (Finset.mem_univ k₀),
      ← Finset.mul_prod_erase _ (fun k => H k (c k)) (Finset.mem_univ k₀)]
    have herase : ∏ k ∈ Finset.univ.erase k₀, H k (c k)
        = ∏ k ∈ Finset.univ.erase k₀, ‖ψ k (c k)‖ ^ 2 :=
      Finset.prod_congr rfl fun k hk => by
        simp only [hH, if_neg (Finset.ne_of_mem_erase hk)]
    rw [herase]
    simp only [hH, if_pos rfl]
    by_cases hck : c k₀ = n
    · rw [if_pos hck, if_pos hck]
    · rw [if_neg hck, if_neg hck, zero_mul]
  rw [modeMarginal, Finset.sum_filter, Finset.sum_congr rfl fun c _ => hstep c,
    ← Fintype.piFinset_univ, ← Finset.prod_univ_sum,
    ← Finset.mul_prod_erase _ (fun k => ∑ m, H k m) (Finset.mem_univ k₀)]
  congr 1
  · simp only [hH, if_pos rfl, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · exact Finset.prod_congr rfl fun k hk => by
      simp only [hH, if_neg (Finset.ne_of_mem_erase hk)]; exact (hns (ψ k)).symm

/-- **Mode-wise Born for unit modes.** For a product of unit modes, the marginal Born probability that
mode `k₀` carries `n` quanta is exactly the single-mode Born weight `‖ψ_{k₀} n‖²` — measuring one mode
of the field reproduces the single-mode record-layer Born rule. -/
theorem modeMarginal_tprod_unit (ψ : Fin K → EuclideanSpace ℂ (Fin N)) (hψ : ∀ k, ‖ψ k‖ = 1)
    (k₀ : Fin K) (n : Fin N) :
    modeMarginal (tprodState ψ) k₀ n = ‖ψ k₀ n‖ ^ 2 := by
  rw [modeMarginal_tprod, Finset.prod_eq_one fun k _ => by rw [hψ k, one_pow], mul_one]

end CSD.CV

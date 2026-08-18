/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Propagator
public import CsdLean4.CV.PowerCounting
public import CsdLean4.Mathlib.QuantumInfo.UnitaryPerturbation

/-!
# CV-26: channel-level RG at the cutoff — coarse-graining with a priced defect

**Category:** CV (continuous variables — the multi-mode field).

The Stage-4 no-go (`exists_unitary_compress_not_unitary`) proved that exact **unitary**
RG matching is impossible: decimating a support-spreading drive loses norm. Its own
conclusion was that an honest RG statement has to be about **channels with an error
budget**. This module is that statement.

The coarse-graining is **mode tracing**: keep the spectator modes, discard mode `k`.

* `coarseIsom k` / `coarseChannel k` — the coarse-graining as a genuine **CPTP map**,
  built as the Stinespring channel of the mode-split permutation isometry
  (`Channel.ofIsometry`), so complete positivity and trace preservation come for free.
  `coarseChannel_apply_entry`: `C(ρ)ᵢⱼ = ∑ₘ ρ(i⊕m, j⊕m)` — trace out mode `k`.
* `spectatorEnergy` / `spectatorU` — the coarse system's own free drive, the diagonal
  phase of the spectator energy. `fieldEnergy_modeSplit_symm` is the split that makes it
  work: `E(s ⊕ m) = E_spec(s) + E_osc(m)`.
* ★ `coarseChannel_free_intertwine` (**CR-2**) — the free drive intertwines the
  coarse-graining **exactly**: `C(F ρ F†) = U_eff · C(ρ) · U_eff†`. The traced mode's
  phase cancels against its own conjugate under the trace — the same `m` appears on both
  sides of every surviving entry — so no error is incurred: at zero coupling the RG step
  is exact, and the whole budget below is the price of the interaction.
* ★★ `channelRG_dist_le` (**CR-3**, the capstone) — **the priced RG step**:

    `D( C(U^n ρ U^{n†}), U_eff^n · C(ρ) · U_eff^{n†} ) ≤ 2n·|τ|·|λ|·C`

  for every density operator `ρ`. Coarse-graining the interacting evolution and evolving
  the coarse-grained state with the free effective drive agree up to a defect linear in
  the period count and in the coupling — the channel-level replacement for the matching
  the no-go forbids.

## The budget, and where each factor comes from

`2` from the unitary-perturbation bridge (`traceDist_conj_sub_le`, CR-1); `n` from the
growth-free telescoping (`Matrix.norm_pow_sub_pow_le_of_unitary`, CV-12); `|τ|·|λ|·C`
from the one-period Duhamel price (`interactingU_dist_le`, CV-9). The data-processing
inequality (`channel_traceDist_le`, K3) is what lets the coarse-graining be applied
**after** the estimate rather than before — it is the step that makes a channel-level
statement cheaper than an operator-level one, not more expensive.

⚠️ Honest scope, unchanged from the scoping pass. **No RG flow**: this is one
coarse-graining step with a priced defect — no iteration, no fixed point, no beta
function. **No level decimation**: the `compressCfg` route of CV-16 is trace-decreasing
and needs a leakage arm the corpus does not have; mode tracing is the route that is CPTP
today. **Uniform in distance**: the cone-refined budget `ε(distance)` is a deferred
refinement, not claimed here. No continuum limit (`ApproxCCR.no_exact_finite_ccr`
stands); the diamond norm is not used, and no claim is made beyond per-state trace
distance.

## References

`specs/channel-rg-scoping.md` (the CV-25 scoping pass: rows CR-1/CR-2/CR-3, the budget
chain, the wall-checks this module discharges); `specs/BACKLOG.md` (Q21 → CV-26);
`specs/future-work.md` (row CV-26); `CV/Decimation.lean` (CV-16, the no-go this answers);
`Mathlib/QuantumInfo/UnitaryPerturbation.lean` (CR-1, `traceDist_conj_sub_le`);
`Mathlib/QuantumInfo/DataProcessing.lean` (`channel_traceDist_le`);
`Mathlib/QuantumInfo/Stinespring.lean` (`Channel.ofIsometry`);
`CV/PowerCounting.lean` (`modeSplit`); `CV/InteractionPrice.lean`
(`interactingU_dist_le`); `CV/FreeFieldFloquet.lean` (`phaseDiagU`, `freeFieldU`).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder

namespace CSD.CV

variable {K N : ℕ}

/-! ### The coarse system: spectator modes -/

/-- The **spectator configuration space**: the occupation configuration of every mode
but `k` — the system that survives the coarse-graining. -/
abbrev SpectatorCfg (K N : ℕ) (k : Fin K) : Type := {j : Fin K // j ≠ k} → Fin N

/-- The **spectator energy**: the free energy carried by the modes the coarse-graining
keeps. -/
noncomputable def spectatorEnergy (k : Fin K) (s : SpectatorCfg K N k) : ℝ :=
  ∑ j : {j : Fin K // j ≠ k}, oscEnergy (s j)

/-- **The energy splits across the mode split**: `E(s ⊕ m) = E_spec(s) + E_osc(m)`. This
additivity is what makes the free drive factorise, and hence CR-2 exact. -/
lemma fieldEnergy_modeSplit_symm (k : Fin K) (s : SpectatorCfg K N k) (m : Fin N) :
    fieldEnergy ((modeSplit (N := N) k).symm (s, m))
      = spectatorEnergy k s + oscEnergy m := by
  classical
  set c : FieldConfig K N := (modeSplit (N := N) k).symm (s, m) with hc
  have hck : c k = m := modeSplit_symm_apply_self k s m
  have hcj : ∀ (j : Fin K) (h : j ≠ k), c j = s ⟨j, h⟩ := by
    intro j h
    rw [hc]
    show (if hj : j = k then m else s ⟨j, hj⟩) = s ⟨j, h⟩
    rw [dif_neg h]
  have hsplit : fieldEnergy c
      = oscEnergy (c k) + ∑ j ∈ Finset.univ.erase k, oscEnergy (c j) :=
    (Finset.add_sum_erase _ (fun j => oscEnergy (c j)) (Finset.mem_univ k)).symm
  rw [hsplit, hck, add_comm]
  congr 1
  rw [spectatorEnergy,
    Finset.sum_subtype (p := fun x : Fin K => x ≠ k) (Finset.univ.erase k)
      (fun x => by simp [Finset.mem_erase]) (fun j => oscEnergy (c j))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hcj a a.2]

/-! ### The coarse-graining channel -/

/-- The **mode-split isometry**: the permutation matrix carrying a field configuration to
its (spectators, mode-`k`) pair. -/
noncomputable def coarseIsom (k : Fin K) :
    Matrix (SpectatorCfg K N k × Fin N) (FieldConfig K N) ℂ :=
  Matrix.of fun p c => if p = modeSplit k c then 1 else 0

@[simp] lemma coarseIsom_apply (k : Fin K) (p : SpectatorCfg K N k × Fin N)
    (c : FieldConfig K N) :
    coarseIsom k p c = if p = modeSplit k c then 1 else 0 := rfl

/-- The mode-split matrix is an isometry — it is a permutation of the index set. -/
lemma coarseIsom_isometry (k : Fin K) :
    (coarseIsom (K := K) (N := N) k)ᴴ * coarseIsom (K := K) (N := N) k = 1 := by
  classical
  ext c c'
  rw [Matrix.mul_apply, Finset.sum_eq_single (modeSplit (N := N) k c)]
  · rw [Matrix.conjTranspose_apply, coarseIsom_apply, coarseIsom_apply, if_pos rfl]
    by_cases h : c = c'
    · subst h
      rw [if_pos rfl, Matrix.one_apply_eq]
      simp
    · rw [if_neg (fun heq => h ((modeSplit (N := N) k).injective heq)),
        Matrix.one_apply_ne h]
      simp
  · intro b _ hb
    rw [Matrix.conjTranspose_apply, coarseIsom_apply, if_neg hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- ★ **The coarse-graining channel**: trace out mode `k`, keeping the spectators. A
genuine CPTP map — the Stinespring channel of the mode-split isometry — so the
data-processing inequality applies to it. -/
noncomputable def coarseChannel (k : Fin K) :
    Channel (FieldConfig K N) (SpectatorCfg K N k) (Fin N) :=
  Channel.ofIsometry (coarseIsom k) (coarseIsom_isometry k)

/-- Conjugating by the mode-split isometry is reindexing. -/
lemma coarseIsom_conj (k : Fin K) (X : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (p q : SpectatorCfg K N k × Fin N) :
    (coarseIsom (K := K) (N := N) k * X * (coarseIsom (K := K) (N := N) k)ᴴ) p q
      = X ((modeSplit (N := N) k).symm p) ((modeSplit (N := N) k).symm q) := by
  classical
  have hrow : ∀ (pp : SpectatorCfg K N k × Fin N) (c : FieldConfig K N),
      coarseIsom (K := K) (N := N) k pp c
        = if c = (modeSplit (N := N) k).symm pp then 1 else 0 := by
    intro pp c
    have hiff : (pp = modeSplit (N := N) k c) ↔ (c = (modeSplit (N := N) k).symm pp) :=
      ⟨fun hh => by rw [hh, Equiv.symm_apply_apply],
        fun hh => by rw [hh, Equiv.apply_symm_apply]⟩
    rw [coarseIsom_apply]
    by_cases h : c = (modeSplit (N := N) k).symm pp
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
  rw [Matrix.mul_apply, Finset.sum_eq_single ((modeSplit (N := N) k).symm q)]
  · rw [Matrix.conjTranspose_apply, hrow q, if_pos rfl, star_one, mul_one,
      Matrix.mul_apply, Finset.sum_eq_single ((modeSplit (N := N) k).symm p)]
    · rw [hrow p, if_pos rfl, one_mul]
    · intro b _ hb
      rw [hrow p b, if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    rw [Matrix.conjTranspose_apply, hrow q b, if_neg hb, star_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The coarse-graining, entrywise**: `C(ρ)ᵢⱼ = ∑ₘ ρ(i ⊕ m, j ⊕ m)` — mode `k` is
traced out. -/
theorem coarseChannel_apply_entry (k : Fin K)
    (ρ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (i j : SpectatorCfg K N k) :
    ((coarseChannel k).apply ρ) i j
      = ∑ m : Fin N, ρ ((modeSplit (N := N) k).symm (i, m))
          ((modeSplit (N := N) k).symm (j, m)) := by
  rw [coarseChannel, Channel.ofIsometry_apply, Matrix.traceRight_apply]
  exact Finset.sum_congr rfl fun m _ => coarseIsom_conj k ρ (i, m) (j, m)

/-! ### The effective (coarse) free drive -/

/-- **The effective free drive** on the coarse system: the diagonal phase of the
spectator energy. -/
noncomputable def spectatorU (k : Fin K) (θ : ℝ) :
    Matrix.unitaryGroup (SpectatorCfg K N k) ℂ :=
  phaseDiagU (fun s => θ * spectatorEnergy k s)

/-- The effective drive at `n` periods is the `n`-th power of the one-period drive — the
coarse dynamics is a genuine stroboscopic evolution. -/
theorem spectatorU_pow (k : Fin K) (τ : ℝ) (n : ℕ) :
    (spectatorU (K := K) (N := N) k τ) ^ n = spectatorU k ((n : ℝ) * τ) := by
  rw [spectatorU, spectatorU, phaseDiagU_pow]
  congr 1
  funext s
  ring

/-- A pure phase times its own conjugate is `1` — the cancellation that makes the traced
mode drop out of CR-2. -/
lemma exp_phase_mul_star_self (r : ℝ) :
    Complex.exp (-(Complex.I * (r : ℂ)))
        * star (Complex.exp (-(Complex.I * (r : ℂ)))) = 1 := by
  rw [mul_comm, star_exp_phase_mul, sub_self]
  simp

/-- Conjugation by a diagonal matrix, entrywise. -/
lemma diagonal_conj_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℂ)
    (X : Matrix ι ι ℂ) (i j : ι) :
    (Matrix.diagonal g * X * (Matrix.diagonal g)ᴴ) i j = g i * X i j * star (g j) := by
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Pi.star_apply, ← mul_assoc]

/-- ★ **CR-2: the free drive intertwines the coarse-graining exactly.**
`C(F ρ F†) = U_eff · C(ρ) · U_eff†`, with no error term: the traced mode's phase meets
its own conjugate in every surviving entry and cancels. At zero coupling the RG step is
exact — every bit of the CR-3 budget is the price of the interaction. -/
theorem coarseChannel_free_intertwine (k : Fin K) (τ : ℝ) (n : ℕ)
    (ρ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    (coarseChannel k).apply
        ((freeFieldU K N τ ^ n).val * ρ * ((freeFieldU K N τ ^ n).val)ᴴ)
      = (spectatorU (K := K) (N := N) k ((n : ℝ) * τ)).val
          * ((coarseChannel k).apply ρ)
          * ((spectatorU (K := K) (N := N) k ((n : ℝ) * τ)).val)ᴴ := by
  classical
  ext i j
  have hF : (freeFieldU K N τ ^ n).val
      = Matrix.diagonal (fun c : FieldConfig K N =>
          Complex.exp (-(Complex.I * ((n * (τ * fieldEnergy c) : ℝ) : ℂ)))) := by
    rw [freeFieldU_pow, phaseDiagU_val]
  have hA : (spectatorU (K := K) (N := N) k ((n : ℝ) * τ)).val
      = Matrix.diagonal (fun s : SpectatorCfg K N k =>
          Complex.exp (-(Complex.I * (((n : ℝ) * τ * spectatorEnergy k s : ℝ) : ℂ)))) := by
    rw [spectatorU, phaseDiagU_val]
  rw [hA, diagonal_conj_apply, coarseChannel_apply_entry, coarseChannel_apply_entry,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hF, diagonal_conj_apply, fieldEnergy_modeSplit_symm, fieldEnergy_modeSplit_symm]
  -- split each field phase into its spectator and traced-mode factors
  have hsplit : ∀ s : SpectatorCfg K N k,
      Complex.exp (-(Complex.I
          * (((n : ℝ) * (τ * (spectatorEnergy k s + oscEnergy m)) : ℝ) : ℂ)))
        = Complex.exp (-(Complex.I * (((n : ℝ) * τ * spectatorEnergy k s : ℝ) : ℂ)))
          * Complex.exp (-(Complex.I * (((n : ℝ) * τ * oscEnergy m : ℝ) : ℂ))) := by
    intro s
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit, hsplit, star_mul']
  set Em := Complex.exp (-(Complex.I * (((n : ℝ) * τ * oscEnergy m : ℝ) : ℂ)))
    with hEmdef
  set Ei := Complex.exp (-(Complex.I * (((n : ℝ) * τ * spectatorEnergy k i : ℝ) : ℂ)))
    with hEidef
  set Ej := Complex.exp (-(Complex.I * (((n : ℝ) * τ * spectatorEnergy k j : ℝ) : ℂ)))
    with hEjdef
  set r := ρ ((modeSplit (N := N) k).symm (i, m))
    ((modeSplit (N := N) k).symm (j, m)) with hrdef
  have hcancel : Em * star Em = 1 := by
    rw [hEmdef]
    exact exp_phase_mul_star_self _
  linear_combination (Ei * r * star Ej) * hcancel

/-! ### The priced RG step -/

/-- Conjugation by a unitary preserves Hermiticity. -/
lemma isHermitian_unitary_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) : (A * ρ * Aᴴ).IsHermitian := by
  show (A * ρ * Aᴴ)ᴴ = A * ρ * Aᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hρ.eq, Matrix.mul_assoc]

/-- Conjugation by a unitary preserves the trace. -/
lemma trace_unitary_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A ρ : Matrix ι ι ℂ} (hA : Aᴴ * A = 1) : (A * ρ * Aᴴ).trace = ρ.trace := by
  rw [Matrix.trace_mul_cycle, hA, Matrix.one_mul]

/-- **The coarse-grained interacting evolution**: run the true (interacting) dynamics for
`n` periods, then coarse-grain. -/
noncomputable def coarseInteracting (k : Fin K) (τ lam : ℝ) (v : FieldConfig K N → ℝ)
    (n : ℕ) (ρ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    Matrix (SpectatorCfg K N k) (SpectatorCfg K N k) ℂ :=
  (coarseChannel k).apply
    ((interactingU K N τ lam v ^ n).val * ρ * ((interactingU K N τ lam v ^ n).val)ᴴ)

/-- **The effective coarse evolution**: coarse-grain first, then run the free effective
drive on the coarse system for `n` periods. -/
noncomputable def coarseEffective (k : Fin K) (τ : ℝ) (n : ℕ)
    (ρ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    Matrix (SpectatorCfg K N k) (SpectatorCfg K N k) ℂ :=
  (spectatorU (K := K) (N := N) k ((n : ℝ) * τ)).val * ((coarseChannel k).apply ρ)
    * ((spectatorU (K := K) (N := N) k ((n : ℝ) * τ)).val)ᴴ

lemma coarseInteracting_def (k : Fin K) (τ lam : ℝ) (v : FieldConfig K N → ℝ) (n : ℕ)
    (ρ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    coarseInteracting k τ lam v n ρ
      = (coarseChannel k).apply
          ((interactingU K N τ lam v ^ n).val * ρ
            * ((interactingU K N τ lam v ^ n).val)ᴴ) := rfl

lemma coarseEffective_def (k : Fin K) (τ : ℝ) (n : ℕ)
    (ρ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    coarseEffective k τ n ρ
      = (spectatorU (K := K) (N := N) k ((n : ℝ) * τ)).val
          * ((coarseChannel k).apply ρ)
          * ((spectatorU (K := K) (N := N) k ((n : ℝ) * τ)).val)ᴴ := rfl

/-- **The RG step is exact at zero coupling**: the effective coarse evolution IS the
coarse-grained free evolution (CR-2, in the named form the capstone consumes). -/
theorem coarseEffective_eq_coarse_free (k : Fin K) (τ : ℝ) (n : ℕ)
    (ρ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    coarseEffective k τ n ρ
      = (coarseChannel k).apply
          ((freeFieldU K N τ ^ n).val * ρ * ((freeFieldU K N τ ^ n).val)ᴴ) :=
  (coarseChannel_free_intertwine k τ n ρ).symm

set_option maxHeartbeats 1600000 in
/-- ★★ **CR-3: the channel-level RG step, priced** (the CV-26 capstone).

  `D( C(U^n ρ U^{n†}), U_eff^n · C(ρ) · U_eff^{n†} ) ≤ 2n·|τ|·|λ|·C`

for every density operator `ρ`: coarse-graining the *interacting* evolution and running
the coarse-grained state under the *free effective* drive agree up to a defect linear in
the period count and in the coupling strength.

This is the statement the Stage-4 no-go said had to replace unitary RG matching
(`exists_unitary_compress_not_unitary`: exact unitary matching is impossible for
support-spreading drives). The coarse-graining is CPTP, the comparison is in trace
distance, and the defect is the CV-9 Duhamel price carried through the CV-12 telescoping
by the CR-1 bridge, with the data-processing inequality applying the channel *after* the
estimate.

⚠️ One coarse-graining step, not a flow: no iteration, no fixed point, no beta function.
The bound is uniform in `ρ` and in the distance between modes. -/
theorem channelRG_dist_le [NeZero N] (k : Fin K) (τ lam : ℝ)
    (v : FieldConfig K N → ℝ) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ c, |v c| ≤ C) (n : ℕ)
    {ρ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1)
    (h : (coarseInteracting k τ lam v n ρ - coarseEffective k τ n ρ).IsHermitian) :
    traceDist h ≤ 2 * ((n : ℝ) * (|τ| * (|lam| * C))) := by
  classical
  set U : Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
    (interactingU K N τ lam v ^ n).val with hU
  set F : Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
    (freeFieldU K N τ ^ n).val with hFdef
  have hUmem : U ∈ Matrix.unitaryGroup (FieldConfig K N) ℂ :=
    (interactingU K N τ lam v ^ n).property
  have hFmem : F ∈ Matrix.unitaryGroup (FieldConfig K N) ℂ :=
    (freeFieldU K N τ ^ n).property
  have hUU : Uᴴ * U = 1 := by
    have := hUmem; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  have hFF : Fᴴ * F = 1 := by
    have := hFmem; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  -- the two evolved states
  have hXherm : (U * ρ * Uᴴ).IsHermitian := isHermitian_unitary_conj hρ.1
  have hYherm : (F * ρ * Fᴴ).IsHermitian := isHermitian_unitary_conj hρ.1
  have hXtr : (U * ρ * Uᴴ).trace = (F * ρ * Fᴴ).trace := by
    rw [trace_unitary_conj hUU, trace_unitary_conj hFF]
  -- CR-2 puts the target's second argument in channel form
  have hherm2 : ((coarseChannel k).apply (U * ρ * Uᴴ)
      - (coarseChannel k).apply (F * ρ * Fᴴ)).IsHermitian :=
    ((coarseChannel k).apply_isHermitian hXherm).sub
      ((coarseChannel k).apply_isHermitian hYherm)
  rw [traceDist_congr h hherm2
    (by rw [coarseInteracting_def, coarseEffective_eq_coarse_free])]
  -- data processing, then the bridge, then the price ladder
  refine le_trans (channel_traceDist_le (coarseChannel k) hXherm hYherm hXtr) ?_
  refine le_trans (traceDist_conj_sub_le hUmem hFmem hρ htr (hXherm.sub hYherm)) ?_
  have hstep : ‖U - F‖ ≤ (n : ℝ) * (|τ| * (|lam| * C)) := by
    have hpow : ‖(interactingU K N τ lam v).val ^ n - (freeFieldU K N τ).val ^ n‖
        ≤ (n : ℝ) * ‖(interactingU K N τ lam v).val - (freeFieldU K N τ).val‖ :=
      Matrix.norm_pow_sub_pow_le_of_unitary
        (interactingU K N τ lam v).property (freeFieldU K N τ).property n
    refine le_trans hpow ?_
    exact mul_le_mul_of_nonneg_left (interactingU_dist_le τ lam v hC hv)
      (Nat.cast_nonneg n)
  exact mul_le_mul_of_nonneg_left hstep (by norm_num)

end CSD.CV

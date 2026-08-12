/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.SupportSpreading
public import CsdLean4.CV.InteractionPrice

/-!
# CV-20: carrier persistence priced by locality (H7, level 1)

**Category:** 3-Local (CV track; CSD-free construction).

The first statements in which a record **carrier**'s stability is priced by
field locality rather than posited (`specs/BACKLOG.md` H7). Framing
constraint, binding per the row: these are theorems about *carriers* — the
present-tense evolution of readout observables — never about "the past
changing"; the record *event* is trajectory-indexed and invariant by
construction (the level-2 lemmas in
`Empirical/CSD/QuantumChaos/CarrierPersistence.lean`), and information is
conserved outright (`perturbed_overlap_invariant` below — every global
overlap is exact at every period, so what a perturbation does to a carrier
is *relocation*, never loss).

* ★ `heisenberg_perturbed_pow_eq` — **exactness in the cone-complement**:
  perturbing the interacting drive by an *arbitrary* unitary `W` supported
  on `R` leaves the Heisenberg evolution of every readout supported on `Q`
  **exactly** unchanged for `n` periods, provided the coupling graph's
  `n`-ball of `Q` has not reached `R`. Not a bound — an equality.
* ★ `heisenberg_diagonal_pow_eq` — **einselection of the configuration
  basis**: a diagonal readout is exactly invariant under the *entire*
  diagonal-phase drive family, at every period and every coupling. In this
  model the pointer basis is the configuration basis, and carriers written
  in it are eternally intact under every diagonal drive — degradation can
  only enter through genuinely non-diagonal perturbations, which is what
  `W` above and below is for.
* `norm_unitary_pow_sub_pow_le` — the telescoping bound `‖Xⁿ − Yⁿ‖ ≤ n·‖X − Y‖`
  for unitary steps (each factor is an isometry).
* ★ `heisenberg_perturbed_pow_dist_le` — **the bounded half**: with no
  geometric hypothesis at all, `n` perturbed periods move a readout by at
  most `2n·‖W − 1‖·‖B‖` — the Duhamel rate of `heisenberg_dist_le`.
* ★★ `carrier_persistence_window` — **the window form, the H7 level-1
  headline**: if the perturbation stays outside the readout's `m`-ball,
  the deviation after `n ≥ m` periods is at most
  `2·(n − m)·‖W − 1‖·‖B‖` — **zero until the cone arrives, the Duhamel
  rate only after**. Locality itself supplies the isolation window; `ε` is
  derived, not posited.

## Scope

Finite cutoff throughout (`K` modes, `N` levels); the base drive is the
kicked diagonal-phase family (`graphInteractingU`), the perturbation `W` an
arbitrary unitary with stated support. The ontic-level lift (feeding the
derived rate into `recordFlip`/`recordIntact_compl_measure_le`) is recorded
in the H7 row as the remaining level; the operational-fixedness clause (d)
is the finite-arena `csd_repeatability_same`, cited at level 2.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ}

/-! ### (c1) Exactness in the cone-complement -/

/-- ★ **Exactness in the cone-complement.** Perturbing each period of the
interacting drive by an arbitrary unitary `W` supported on `R` leaves the
Heisenberg evolution of a `Q`-supported readout **exactly** unchanged for
`n` periods, provided the coupling graph's `n`-ball of `Q` is still disjoint
from `R`: the readout's cone has not reached the perturbation, so every
`W`-conjugation acts trivially on the evolved readout
(`heisenberg_eq_of_disjoint`). -/
theorem heisenberg_perturbed_pow_eq {Q R : Finset (Fin K)}
    (τ lam : ℝ) (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn R W.val)
    {B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hB : SupportedOn Q B)
    (n : ℕ) (hdisj : Disjoint (graphBall E Q n) R) :
    heisenberg ((graphInteractingU K N τ lam E g * W) ^ n) B
      = heisenberg (graphInteractingU K N τ lam E g ^ n) B := by
  induction n with
  | zero => rw [pow_zero, pow_zero]
  | succ n ih =>
    have hdisj_n : Disjoint (graphBall E Q n) R :=
      Finset.disjoint_of_subset_left
        (graphBall_mono E Q (Nat.le_succ n)) hdisj
    rw [pow_succ, heisenberg_mul, ih hdisj_n, heisenberg_mul,
      show heisenberg (graphInteractingU K N τ lam E g)
          (heisenberg (graphInteractingU K N τ lam E g ^ n) B)
        = heisenberg (graphInteractingU K N τ lam E g ^ (n + 1)) B from by
        rw [← heisenberg_mul, ← pow_succ]]
    exact heisenberg_eq_of_disjoint hdisj hW
      (heisenberg_graphInteractingU_pow_supportedOn τ lam E g (n + 1) hB)

/-! ### (c1′) Einselection of the configuration basis -/

/-- Conjugation by a diagonal unitary fixes every diagonal observable. -/
theorem heisenberg_diagonal_of_diagonal
    {U : Matrix.unitaryGroup (FieldConfig K N) ℂ}
    {u : FieldConfig K N → ℂ} (hU : U.val = Matrix.diagonal u)
    (b : FieldConfig K N → ℂ) :
    heisenberg U (Matrix.diagonal b) = Matrix.diagonal b := by
  have hcomm : Matrix.diagonal b * U.val = U.val * Matrix.diagonal b := by
    rw [hU, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    exact mul_comm _ _
  have h1 : star U.val * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  calc heisenberg U (Matrix.diagonal b)
      = star U.val * (Matrix.diagonal b * U.val) := by
        rw [heisenberg, mul_assoc]
    _ = star U.val * (U.val * Matrix.diagonal b) := by rw [hcomm]
    _ = star U.val * U.val * Matrix.diagonal b := by rw [mul_assoc]
    _ = Matrix.diagonal b := by rw [h1, one_mul]

/-- ★ **Einselection of the configuration basis**: a diagonal readout is
exactly invariant under the whole diagonal-phase drive family — every
coupling graph, every strength, every period count. Carriers written in the
pointer (configuration) basis are eternally intact under every diagonal
drive; only genuinely non-diagonal perturbations can move them. -/
theorem heisenberg_diagonal_pow_eq (τ lam : ℝ)
    (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ) (n : ℕ)
    (b : FieldConfig K N → ℂ) :
    heisenberg (graphInteractingU K N τ lam E g ^ n) (Matrix.diagonal b)
      = Matrix.diagonal b := by
  rw [show graphInteractingU K N τ lam E g
      = phaseDiagU (fun c =>
          τ * (fieldEnergy c + lam * graphPotential E g c)) from rfl]
  have hval : ((phaseDiagU (fun c =>
        τ * (fieldEnergy c + lam * graphPotential E g c)) ^ n).val
      : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
      = Matrix.diagonal (fun x => Complex.exp (-(Complex.I
          * ((τ * (fieldEnergy x + lam * graphPotential E g x) : ℝ) : ℂ))) ^ n) := by
    rw [show (phaseDiagU (fun c =>
          τ * (fieldEnergy c + lam * graphPotential E g c)) ^ n).val
        = (phaseDiagU (fun c =>
            τ * (fieldEnergy c + lam * graphPotential E g c))).val ^ n from
        rfl,
      phaseDiagU_val, Matrix.diagonal_pow]
    rfl
  exact heisenberg_diagonal_of_diagonal hval b

/-! ### (c2) The bounded half -/

/-- Iterated unitary steps separate at most linearly: `‖Xⁿ − Yⁿ‖ ≤ n·‖X − Y‖`
(one fresh `X − Y` per period, the other factors isometries). -/
theorem norm_unitary_pow_sub_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (X Y : Matrix.unitaryGroup ι ℂ) (n : ℕ) :
    ‖(X ^ n).val - (Y ^ n).val‖ ≤ n * ‖X.val - Y.val‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (X ^ (n + 1)).val - (Y ^ (n + 1)).val
        = ((X ^ n).val - (Y ^ n).val) * X.val
          + (Y ^ n).val * (X.val - Y.val) := by
      rw [show (X ^ (n + 1)).val = (X ^ n).val * X.val from by
          rw [pow_succ]; rfl,
        show (Y ^ (n + 1)).val = (Y ^ n).val * Y.val from by
          rw [pow_succ]; rfl]
      noncomm_ring
    have hXn : ‖X.val‖ = 1 := CStarRing.norm_of_mem_unitary X.property
    have hYn : ‖(Y ^ n).val‖ = 1 :=
      CStarRing.norm_of_mem_unitary (Y ^ n).property
    calc ‖(X ^ (n + 1)).val - (Y ^ (n + 1)).val‖
        = ‖((X ^ n).val - (Y ^ n).val) * X.val
            + (Y ^ n).val * (X.val - Y.val)‖ := by rw [hsplit]
      _ ≤ ‖((X ^ n).val - (Y ^ n).val) * X.val‖
            + ‖(Y ^ n).val * (X.val - Y.val)‖ := norm_add_le _ _
      _ ≤ ‖(X ^ n).val - (Y ^ n).val‖ * ‖X.val‖
            + ‖(Y ^ n).val‖ * ‖X.val - Y.val‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (n * ‖X.val - Y.val‖) * 1 + 1 * ‖X.val - Y.val‖ := by
          rw [hXn, hYn]
          exact add_le_add (mul_le_mul_of_nonneg_right ih (by norm_num))
            (le_refl _)
      _ = (n + 1) * ‖X.val - Y.val‖ := by ring
      _ = ((n + 1 : ℕ) : ℝ) * ‖X.val - Y.val‖ := by push_cast; ring

/-- The per-period perturbation distance: `‖UW − U‖ ≤ ‖W − 1‖`. -/
lemma norm_mul_sub_self_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (U W : Matrix.unitaryGroup ι ℂ) :
    ‖(U * W).val - U.val‖ ≤ ‖W.val - 1‖ := by
  rw [show (U * W).val - U.val = U.val * (W.val - 1) from by
    rw [mul_sub, mul_one]; rfl]
  refine (norm_mul_le _ _).trans ?_
  rw [CStarRing.norm_of_mem_unitary U.property, one_mul]

/-- Conjugation contracts: `‖heisenberg U B‖ ≤ ‖B‖`. -/
lemma norm_heisenberg_le [NeZero N]
    (U : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    ‖heisenberg U B‖ ≤ ‖B‖ := by
  have hUs : ‖star U.val‖ = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    exact CStarRing.norm_of_mem_unitary U.property
  have hU : ‖U.val‖ = 1 := CStarRing.norm_of_mem_unitary U.property
  calc ‖heisenberg U B‖ = ‖star U.val * B * U.val‖ := rfl
    _ ≤ ‖star U.val * B‖ * ‖U.val‖ := norm_mul_le _ _
    _ ≤ ‖star U.val‖ * ‖B‖ * ‖U.val‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖B‖ := by rw [hUs, hU, one_mul, mul_one]

/-- ★ **The bounded half**: with no geometric hypothesis, `n` perturbed
periods move any readout by at most `2n·‖W − 1‖·‖B‖` — the Duhamel rate of
`heisenberg_dist_le`, telescoped. -/
theorem heisenberg_perturbed_pow_dist_le [NeZero N]
    (U W : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (n : ℕ) :
    ‖heisenberg ((U * W) ^ n) B - heisenberg (U ^ n) B‖
      ≤ 2 * n * ‖W.val - 1‖ * ‖B‖ := by
  have h3 : ‖((U * W) ^ n).val - (U ^ n).val‖ ≤ n * ‖W.val - 1‖ :=
    (norm_unitary_pow_sub_pow_le (U * W) U n).trans
      (mul_le_mul_of_nonneg_left (norm_mul_sub_self_le U W) (Nat.cast_nonneg n))
  calc ‖heisenberg ((U * W) ^ n) B - heisenberg (U ^ n) B‖
      ≤ 2 * ‖((U * W) ^ n).val - (U ^ n).val‖ * ‖B‖ :=
        heisenberg_dist_le ((U * W) ^ n) (U ^ n) B
    _ ≤ 2 * (n * ‖W.val - 1‖) * ‖B‖ := by
        gcongr
    _ = 2 * n * ‖W.val - 1‖ * ‖B‖ := by ring

/-! ### ★★ The window form — the H7 level-1 headline -/

/-- ★★ **Carrier persistence, the window form.** A readout supported on `Q`,
evolved under the interacting drive perturbed each period by an arbitrary
unitary `W` supported on `R`: if `R` is outside the readout's `m`-ball, the
deviation after `n ≥ m` periods is at most `2·(n − m)·‖W − 1‖·‖B‖` —
**exactly zero until the cone arrives, the Duhamel rate only after**.
Locality supplies the isolation window; the rate is derived, not posited. -/
theorem carrier_persistence_window [NeZero N] {Q R : Finset (Fin K)}
    (τ lam : ℝ) (E : Finset (Fin K × Fin K))
    (g : Fin K × Fin K → Fin N → Fin N → ℝ)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn R W.val)
    {B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hB : SupportedOn Q B)
    {m n : ℕ} (hmn : m ≤ n) (hdisj : Disjoint (graphBall E Q m) R) :
    ‖heisenberg ((graphInteractingU K N τ lam E g * W) ^ n) B
        - heisenberg (graphInteractingU K N τ lam E g ^ n) B‖
      ≤ 2 * (n - m : ℕ) * ‖W.val - 1‖ * ‖B‖ := by
  set U := graphInteractingU K N τ lam E g with hU
  have hsplitUW : (U * W) ^ n = (U * W) ^ m * (U * W) ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hmn]
  have hsplitU : U ^ n = U ^ m * U ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hsplitUW, hsplitU, heisenberg_mul, heisenberg_mul,
    heisenberg_perturbed_pow_eq τ lam E g hW hB m hdisj]
  calc ‖heisenberg ((U * W) ^ (n - m)) (heisenberg (U ^ m) B)
        - heisenberg (U ^ (n - m)) (heisenberg (U ^ m) B)‖
      ≤ 2 * (n - m : ℕ) * ‖W.val - 1‖ * ‖heisenberg (U ^ m) B‖ :=
        heisenberg_perturbed_pow_dist_le U W (heisenberg (U ^ m) B) (n - m)
    _ ≤ 2 * (n - m : ℕ) * ‖W.val - 1‖ * ‖B‖ := by
        gcongr
        exact norm_heisenberg_le (U ^ m) B

/-! ### (b) Information conservation, instantiated -/

/-- Every global overlap is exactly conserved under the perturbed drive, at
every period: what a perturbation does to a carrier is relocation, never
loss. Instantiates the Floquet-interface conservation law at the perturbed
CV drive. -/
theorem perturbed_overlap_invariant
    (U W : Matrix.unitaryGroup (FieldConfig K N) ℂ) (n : ℕ)
    (ψ φ : EuclideanSpace ℂ (FieldConfig K N)) :
    inner ℂ ((_root_.QuantumChaos.FloquetEvolution.ofUnitaryMatrix
        (U * W)).iterate n ψ)
      ((_root_.QuantumChaos.FloquetEvolution.ofUnitaryMatrix
        (U * W)).iterate n φ)
      = inner ℂ ψ φ :=
  _root_.QuantumChaos.FloquetEvolution.inner_iterate_iterate _ n ψ φ

end CSD.CV

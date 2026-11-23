/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderMeeting

/-!
# The departure starts when the packet's box reaches the transponder

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, items (1) and (2) in one run, the
caused return: the integrals of UD-254 for a packet).

`transponder_launch_meeting_ge` bounds the departure from the free orbit below by
`|g| (t − t₁) ‖X‖` less three integrals along the free orbit, for a matrix `X` and a
parameter `t₁`. Here `X` is the state of the flat packet and a transponder at rest, and the
integrals are bounded from the packet's moving box.

* `sum_norm_sq_flatPacketD` — the flat packet has norm `1` at every flow time;
* `sum_norm_sq_prod`, `norm_vecMulVec_star_of_sum_eq_one` — the product state has norm `1`,
  and so has its rank-one matrix;
* ★★ `norm_coincProj_freeOrbit_flatPacket_resting_le` — for any relation `ρ`: at a flow time
  `s ≥ 0` at which no site of the packet's moving box is `ρ`-related to a site of `B`, the
  amplitude of the free orbit on the `ρ`-related configurations is at most `√(flatTailD s)`;
* ★★★ `transponder_launch_flatPacket_meeting_ge` — **for `0 ≤ t₁ ≤ t₂ ≤ t`: if the moving box
  is not in contact with `B` up to `t₁` and every site of it is in contact with every site of
  `B` from `t₂` to `t`, the state departs from the free orbit by at least**

  `|g| (t − t₂) − |g| (√ε₁ t₁ + (t₂ − t₁)) − |g| √ε (t − t₂) − |g|² (√ε₁ t₁ + (t − t₁)) t`,

  `ε₁ = flatTailD t₁`, `ε = flatTailD t`.

## Honest scope

⚠️ **The two box conditions are hypotheses.** No relation, sites and times are exhibited for
which the box is apart up to `t₁` and wholly in contact from `t₂`. The time `t₂ − t₁` of
partial contact is counted in full as error.

⚠️ **The transponder is at rest with one energy for both levels.** Its state is any state of
norm `1` supported on `B`; it is not required to be in the first level, and the departure is
not stated to be in the second.

⚠️ **First order.** The last term is of order `g² t²`: the bound is positive only for
`|g| t` small against `(t − t₂)/t`.

⚠️ **The carriers' own Hamiltonians and the contact term only.** No pointer, no arena, no
reading of the launched part (items (3) to (5) of UO-26).

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-222, UD-240, UD-252, UD-254, UD-255); `RecordLayer/TransponderMeeting.lean`
(`transponder_launch_meeting_ge`); `RecordLayer/TransponderFirstOrder.lean`
(`levelSwap_mul_blockDiagonal_smul_one`); `RecordLayer/TransponderAtRest.lean`
(`norm_exp_mulVec_stationary`, `blockDiagonal_smul_one_mulVec`);
`RecordLayer/TransponderLaunchState.lean` (`norm_mul_vecMulVec`, `l2_opNorm_vecMulVec`);
`RecordLayer/CoincidenceOrbit.lean` (`sum_norm_sq_coincProj_freeOrbit_prod_le`);
`RecordLayer/TorusArrival.lean` (`flatTailD`, `flatTailD_mono`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### Norms -/

section Norms

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The norm of a product state is the product of the norms. -/
theorem sum_norm_sq_prod (ψ : ι → ℂ) (φ : κ → ℂ) :
    ∑ x : ι × κ, ‖ψ x.1 * φ x.2‖ ^ 2 = (∑ p, ‖ψ p‖ ^ 2) * ∑ q, ‖φ q‖ ^ 2 := by
  simp only [norm_mul, mul_pow]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

variable [DecidableEq ι]

/-- A state of norm `1` has a rank-one matrix of norm `1`, and its conjugate has norm
`1`. -/
theorem norm_vecMulVec_star_of_sum_eq_one {Ψ : ι → ℂ} (h : ∑ x, ‖Ψ x‖ ^ 2 = 1) :
    Real.sqrt (∑ x, ‖star Ψ x‖ ^ 2) = 1 ∧ ‖Matrix.vecMulVec Ψ (star Ψ)‖ = 1 := by
  have hs : ∑ x, ‖star Ψ x‖ ^ 2 = 1 := by
    simpa using h
  refine ⟨by rw [hs, Real.sqrt_one], ?_⟩
  rw [l2_opNorm_vecMulVec, hs, h, Real.sqrt_one, one_mul]

end Norms

section Packet

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}

omit [Nonempty Sp] in
/-- The flat packet has norm `1` at every flow time. -/
theorem sum_norm_sq_flatPacketD (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀)
    (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ) (lo : κ → ℤ) {Nw : κ → ℕ}
    (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L) (s : ℝ) :
    ∑ p, ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) s p‖ ^ 2 = 1 := by
  obtain ⟨-, hD⟩ := noWrapD_distinctD_of_box (L := L) (W := boxWindowD lo Nw) (lo := lo)
    (fun m hm j => by
      have a := (Fintype.mem_piFinset.1 hm) j
      have b := hNL j
      simp only [Finset.mem_Ico] at a
      omega)
  rw [← re_chainInnerD_self, chainInnerD_packetD_unitAmpD h he hn hμ hD, sum_flatAmpD_sq lo hN,
    Complex.ofReal_re]

omit [Nonempty Sp] [Nonempty n] in
/-- ★★ **The free orbit's amplitude on related configurations, from the moving box.** The
state is the flat packet times a transponder at rest (one energy for both levels) of norm
`1` supported on `B`. For any relation `ρ`, at a flow time `s ≥ 0` at which no site of the
packet's moving box is `ρ`-related to a site of `B`, the amplitude of the free orbit on the
`ρ`-related configurations is at most `√(flatTailD s)`. -/
theorem norm_coincProj_freeOrbit_flatPacket_resting_le (τ : n × Fin 2 → κ → ZMod L)
    (ρ : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel ρ]
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (E : ℝ)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφn : ∑ q, ‖φ q‖ ^ 2 = 1)
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {s : ℝ} (hs : 0 ≤ s)
    (hρ : ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B, ¬ ρ a b) :
    ‖coincProj Prod.fst τ ρ
        * exp (s • ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
            (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
        * Matrix.vecMulVec
          (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
            packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
              (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
          (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
            packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
              (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)‖
      ≤ Real.sqrt (flatTailD L J μ Nw w γ s) := by
  have hΨ1 : ∑ x : ((κ → ZMod L) × Sp) × (n × Fin 2),
      ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) 0 x.1 * φ x.2‖ ^ 2 = 1 := by
    rw [sum_norm_sq_prod, sum_norm_sq_flatPacketD h he hn hμ lo hN hNL 0, hφn, one_mul]
  have hstat : Matrix.blockDiagonal (fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      *ᵥ φ = ((E : ℝ) : ℂ) • φ := by
    funext q
    rw [blockDiagonal_smul_one_mulVec (fun _ => E) φ q, Pi.smul_apply, smul_eq_mul]
  rw [norm_mul_vecMulVec, (norm_vecMulVec_star_of_sum_eq_one hΨ1).1, mul_one,
    ← Matrix.mulVec_mulVec]
  refine Real.sqrt_le_sqrt ?_
  have h1 := sum_norm_sq_coincProj_freeOrbit_prod_le
    (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ ρ (latticeDiracHam (L := L) α β J μ)
    (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)) s
    (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) 0) φ
    (B := B) hρ
  rw [exp_mulVec_packetD h J μ e₀ _ _ s, sum_ite_fst_eq_regionWeightD_compl,
    sum_norm_sq_flatPacketD h he hn hμ lo hN hNL s, one_mul] at h1
  simp only [norm_exp_mulVec_stationary hstat] at h1
  have hB0 : (∑ q, if τ q ∈ B then (0 : ℝ) else ‖φ q‖ ^ 2) = 0 :=
    Finset.sum_eq_zero fun q _ => by
      split_ifs with hq
      · rfl
      · rw [hφB q hq, norm_zero]
        norm_num
  rw [hφn, hB0, mul_one, add_zero] at h1
  have hh := regionWeightD_flatPacket_compl_movedBoxD_le_window (L := L) (J := J) h he hn hμ
    lo hN hNL k₀ hw0 hw s hγ
  rw [abs_of_nonneg hs] at hh
  refine h1.trans ?_
  rw [flatTailD]
  exact hh

/-- ★★★ **The departure starts when the packet's box reaches the transponder.** The messenger
is the flat packet of the lattice Dirac field of any dimension; the transponder is at rest
with one energy for both levels, in a state of norm `1` supported on the sites `B`. For
`0 ≤ t₁ ≤ t₂ ≤ t`: if no site of the packet's moving box is related to a site of `B` up to
`t₁`, and every site of it is related to every site of `B` from `t₂` to `t`, then the state
at `t` departs from the free orbit by at least

`|g| (t − t₂) − |g| (√ε₁ t₁ + (t₂ − t₁)) − |g| √ε (t − t₂) − |g| (|g| (√ε₁ t₁ + (t − t₁))) t`,

`ε₁ = flatTailD t₁`, `ε = flatTailD t`. -/
theorem transponder_launch_flatPacket_meeting_ge (τ : n × Fin 2 → κ → ZMod L)
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (E g : ℝ)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφn : ∑ q, ‖φ q‖ ^ 2 = 1)
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {t₁ t₂ t : ℝ} (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (h2t : t₂ ≤ t)
    (hsep : ∀ s, 0 ≤ s → s ≤ t₁ → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      ¬ r a b)
    (hcon : ∀ s, t₂ ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      r a b) :
    |g| * (t - t₂)
        - |g| * (Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁))
        - |g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * (t - t₂))
        - |g| * (|g| * (Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t - t₁))) * t
      ≤ Real.sqrt (∑ x, ‖((exp (t • ((-Complex.I)
            • (compositeH (latticeDiracHam (L := L) α β J μ)
                (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))
              + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n))))
          - exp (t • ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
              (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)))))
        *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2) := by
  have ht2 : 0 ≤ t₂ := h1.trans h12
  have ht : 0 ≤ t := ht2.trans h2t
  have hΨ1 : ∑ x : ((κ → ZMod L) × Sp) × (n × Fin 2),
      ‖packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
        (unitAmpD L J μ (flatAmpD lo Nw)) 0 x.1 * φ x.2‖ ^ 2 = 1 := by
    rw [sum_norm_sq_prod, sum_norm_sq_flatPacketD h he hn hμ lo hN hNL 0, hφn, one_mul]
  obtain ⟨hstar, hX1⟩ := norm_vecMulVec_star_of_sum_eq_one hΨ1
  have hT : ∀ l : Fin 2, (((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun _ =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hM := latticeDiracHam_isHermitian (L := L) h J μ
  have hH₀ := compositeH_isHermitian hM (blockDiagonal_isHermitian hT)
  have hA := Matrix.conjTranspose_neg_I_smul hH₀
  have key := transponder_launch_meeting_ge (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r hτ
    hM hT (levelSwap_mul_blockDiagonal_smul_one E) g
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)) ht2 h2t
  rw [norm_mul_vecMulVec, hstar, mul_one, hX1, mul_one] at key
  -- the pointwise bounds
  have hP : ∀ s, 0 ≤ s → s ≤ t₁ → _ ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) :=
    fun s hs hs1 => (norm_coincProj_freeOrbit_flatPacket_resting_le τ r h he hn hμ E lo hN hNL
      k₀ hw0 hw hγ φ hφn B hφB hs (hsep s hs hs1)).trans
      (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hs1))
  have hP' : ∀ s, t₂ ≤ s → s ≤ t → _ ≤ Real.sqrt (flatTailD L J μ Nw w γ t) :=
    fun s hs hst => (norm_coincProj_freeOrbit_flatPacket_resting_le τ (fun a b => ¬ r a b) h
      he hn hμ E lo hN hNL k₀ hw0 hw hγ φ hφn B hφB (ht2.trans hs)
      (fun a ha b hb => not_not.2 (hcon s hs hst a ha b hb))).trans
      (Real.sqrt_le_sqrt (flatTailD_mono (J := J) hμ Nw hw0 hγ hst))
  have hP1 : ‖coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r‖ ≤ 1 := by
    rw [coincProj]
    exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun p => by split_ifs <;> simp
  have hcrude : ∀ s : ℝ, ‖coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r
      * exp (s • ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
          (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ))))
      * Matrix.vecMulVec
        (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
        (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
          packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
            (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)‖ ≤ 1 := fun s => by
    refine (norm_mul_le _ _).trans ?_
    rw [hX1, mul_one]
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_exp_smul_skew _ hA s, mul_one]
    exact hP1
  -- the integrals
  have hcont := Matrix.continuous_norm_mul_exp_smul_mul
    ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
      (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
    (coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ r)
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2))
  have hcont' := Matrix.continuous_norm_mul_exp_smul_mul
    ((-Complex.I) • compositeH (latticeDiracHam (L := L) α β J μ)
      (Matrix.blockDiagonal fun _ : Fin 2 => ((E : ℝ) : ℂ) • (1 : Matrix n n ℂ)))
    (coincProj (Prod.fst : (κ → ZMod L) × Sp → κ → ZMod L) τ (fun a b => ¬ r a b))
    (Matrix.vecMulVec
      (fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2)
      (star fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
        packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2))
  have hIa := intervalIntegral.integral_mono_on h1 (hcont.intervalIntegrable 0 t₁)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t₁))) fun s hs => hP s hs.1 hs.2
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hIa
  have hIb : ∀ u : ℝ, t₁ ≤ u → ∫ s in t₁..u, _ ≤ u - t₁ := fun u hu => by
    have := intervalIntegral.integral_mono_on hu (hcont.intervalIntegrable t₁ u)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun s _ => hcrude s
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  have hsplit : ∀ u : ℝ, (∫ s in (0 : ℝ)..u, _) = (∫ s in (0 : ℝ)..t₁, _) + ∫ s in t₁..u, _ :=
    fun u => (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 t₁) (hcont.intervalIntegrable t₁ u)).symm
  have hI1 := hsplit t₂
  have hI3 := hsplit t
  have hIc := intervalIntegral.integral_mono_on h2t (hcont'.intervalIntegrable t₂ t)
    (intervalIntegrable_const (μ := volume)
      (c := Real.sqrt (flatTailD L J μ Nw w γ t))) fun s hs => hP' s hs.1 hs.2
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hIc
  have hb2 := hIb t₂ h12
  have hb3 := hIb t (h12.trans h2t)
  have hg := abs_nonneg g
  have e1 := mul_le_mul_of_nonneg_left (by linarith [hI1, hIa, hb2] :
    (∫ s in (0 : ℝ)..t₂, _) ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t₂ - t₁)) hg
  have e2 := mul_le_mul_of_nonneg_left hIc hg
  have e3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (by linarith [hI3, hIa, hb3] :
      (∫ s in (0 : ℝ)..t, _) ≤ Real.sqrt (flatTailD L J μ Nw w γ t₁) * t₁ + (t - t₁)) hg)
    hg) ht
  linarith [key, e1, e2, e3]

end Packet

end CSD.RecordLayer

end

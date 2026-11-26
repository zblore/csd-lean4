/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderPlace

/-!
# A band for the transponder's second level: the two levels' free motion

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26; the transponder of UA-21, first
brick: its free motion, and item (1) for it).

By `RecordLayer/TransponderPlace.lean` a transponder that does not hop keeps what is launched
at its own sites. UA-21 gives the second level a band: the first level has one energy and no
hopping, the second has a Hamiltonian `H₁` on the same sites. Here the two levels' free
motion is read off, with no contact term.

* `bandBlocks`, `bandBlocks_isHermitian` — the transponder's two blocks;
* `inLevel`, `inLevel_smul`, `inLevel_zero_apply_of_snd_eq_one`, `sum_norm_sq_inLevel`;
* `blockDiagonal_mulVec_inLevel`, `inLevel_sum`, ★ `exp_blockDiagonal_mulVec_inLevel_of_eigen`
  — an eigenvector of one level's block, placed in that level, moves by a phase;
* `levelSwap_mulVec_inLevel_zero` — the swap takes a first-level state to the same wave
  function in the second level;
* ★★ `exp_bandBlocks_mulVec_inLevel_zero` — **the first level rests**: every state of it
  moves by the phase `e^{−iE₀s}`;
* ★★★ `transponder_band_swapped_moves` — **with the lattice Dirac band, the swap of a flat
  packet resting in the first level is that packet in the second level; it then moves, and
  its weight outside the box moving at the band's group velocity is at most `flatTailD s`**;
* `levelSwap_apply_of_site_ne`;
* ★★★ `transponder_band_launch_le` — **item (1) of UO-26 holds as it stood**: while the
  messenger's box is not in contact with the transponder's sites, the part in the second
  level is at most `‖Q‖ |g| √(flatTailD t) · t`.

## Honest scope

⚠️ **No launch is shown for this transponder.** The second and third statements have no
contact term: they say what a swapped state would do, not that the meeting swaps it. The
level swap does not commute with these blocks, so the lower bounds of UD-253 to UD-263 do
not apply.

⚠️ **The direction and the speed are those of the prepared packet** (UA-21, risk (i)): the
central momentum of the transponder's wave function is chosen in the preparation.

⚠️ **A first level with no hopping** is a carrier of infinite mass; that is why it rests
exactly.

⚠️ **Flow times.** No pointer, no arena, no reading.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UA-21,
UO-26, UD-252, UD-264, UD-265); `RecordLayer/TransponderPlace.lean`
(`transponder_site_conserved`); `RecordLayer/TransponderAtRest.lean`
(`exp_mulVec_stationary`, `transponder_launch_flatPacket_stationary_le`);
`RecordLayer/TorusDetector.lean` (`exp_mulVec_packetD`); `CV/DiracPacketWindowD.lean`
(`regionWeightD_flatPacket_compl_movedBoxD_le_window`); `RecordLayer/TorusArrival.lean`
(`flatTailD`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### The two blocks and a state in one level -/

section Blocks

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The transponder's two blocks** (UA-21): the first level has the energy `E₀` and no
hopping, the second level has the Hamiltonian `H₁`. -/
def bandBlocks (E₀ : ℝ) (H₁ : Matrix n n ℂ) : Fin 2 → Matrix n n ℂ :=
  ![((E₀ : ℝ) : ℂ) • (1 : Matrix n n ℂ), H₁]

omit [Fintype n] in
/-- Both blocks are Hermitian when the second level's Hamiltonian is. -/
theorem bandBlocks_isHermitian (E₀ : ℝ) {H₁ : Matrix n n ℂ} (hH₁ : H₁.IsHermitian) :
    ∀ l, (bandBlocks E₀ H₁ l).IsHermitian := by
  intro l
  fin_cases l
  · exact Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  · exact hH₁

/-- **A wave function on the sites, placed in one level.** -/
def inLevel (l : Fin 2) (χ : n → ℂ) : n × Fin 2 → ℂ := fun q => if q.2 = l then χ q.1 else 0

omit [Fintype n] [DecidableEq n] in
theorem inLevel_smul (l : Fin 2) (c : ℂ) (χ : n → ℂ) :
    inLevel l (c • χ) = c • inLevel l χ := by
  funext q
  by_cases h : q.2 = l <;> simp [inLevel, h]

omit [Fintype n] [DecidableEq n] in
/-- A state placed in the first level has no part in the second. -/
theorem inLevel_zero_apply_of_snd_eq_one (χ : n → ℂ) :
    ∀ q : n × Fin 2, q.2 = 1 → inLevel 0 χ q = 0 := by
  intro q hq
  simp [inLevel, hq]

omit [DecidableEq n] in
/-- Placing a wave function in a level keeps its squared norm. -/
theorem sum_norm_sq_inLevel (l : Fin 2) (χ : n → ℂ) :
    ∑ q, ‖inLevel l χ q‖ ^ 2 = ∑ p, ‖χ p‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  fin_cases l <;> simp [inLevel, Fin.sum_univ_two]

omit [DecidableEq n] in
/-- A block-diagonal Hamiltonian acts on a state in one level by that level's block. -/
theorem blockDiagonal_mulVec_inLevel (T : Fin 2 → Matrix n n ℂ) (l : Fin 2) (χ : n → ℂ) :
    Matrix.blockDiagonal T *ᵥ inLevel l χ = inLevel l (T l *ᵥ χ) := by
  funext ⟨p, k⟩
  have e : (Matrix.blockDiagonal T *ᵥ inLevel l χ) (p, k)
      = ∑ q, T k p q * inLevel l χ (q, k) := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Fin.sum_univ_two]
    fin_cases k <;> simp
  rw [e]
  by_cases hk : k = l
  · subst hk
    simp [inLevel, Matrix.mulVec, dotProduct]
  · simp [inLevel, hk]

omit [Fintype n] [DecidableEq n] in
/-- Placing in a level is additive over finite sums. -/
theorem inLevel_sum {ι : Type*} (l : Fin 2) (W : Finset ι) (f : ι → n → ℂ) :
    inLevel l (∑ m ∈ W, f m) = ∑ m ∈ W, inLevel l (f m) := by
  funext q
  by_cases h : q.2 = l <;> simp [inLevel, h, Finset.sum_apply]

/-- ★ **An eigenvector of one level's block moves by a phase**, placed in that level. -/
theorem exp_blockDiagonal_mulVec_inLevel_of_eigen (T : Fin 2 → Matrix n n ℂ) (l : Fin 2)
    {χ : n → ℂ} {c : ℂ} {s : ℝ} (h : (s • ((-Complex.I) • T l)) *ᵥ χ = c • χ) :
    exp (s • ((-Complex.I) • Matrix.blockDiagonal T)) *ᵥ inLevel l χ
      = exp c • inLevel l χ := by
  refine exp_mulVec_of_mulVec_eq_smul ?_
  have h' : (((s : ℝ) : ℂ) * (-Complex.I)) • (T l *ᵥ χ) = c • χ := by
    rw [← Matrix.smul_mulVec, ← Complex.real_smul, smul_assoc]
    exact h
  rw [← smul_assoc, Complex.real_smul, Matrix.smul_mulVec, blockDiagonal_mulVec_inLevel,
    ← inLevel_smul, h', inLevel_smul]

/-- The swap takes a first-level state to the same wave function in the second level. -/
theorem levelSwap_mulVec_inLevel_zero (χ : n → ℂ) :
    levelSwap n *ᵥ inLevel 0 χ = inLevel 1 χ := by
  funext ⟨p, k⟩
  fin_cases k
  · show (levelSwap n *ᵥ inLevel 0 χ) (p, 0) = inLevel 1 χ (p, 0)
    rw [levelSwap_mulVec_zero]
    simp [inLevel]
  · show (levelSwap n *ᵥ inLevel 0 χ) (p, 1) = inLevel 1 χ (p, 1)
    rw [levelSwap_mulVec_one]
    simp [inLevel]

/-- ★★ **The first level rests.** Every state of it moves by the phase `e^{−iE₀s}`. -/
theorem exp_bandBlocks_mulVec_inLevel_zero (E₀ : ℝ) (H₁ : Matrix n n ℂ) (χ : n → ℂ)
    (s : ℝ) :
    exp (s • ((-Complex.I) • Matrix.blockDiagonal (bandBlocks E₀ H₁))) *ᵥ inLevel 0 χ
      = Complex.exp (-(Complex.I * E₀) * s) • inLevel 0 χ := by
  refine exp_mulVec_stationary ?_ s
  rw [blockDiagonal_mulVec_inLevel]
  show inLevel 0 ((((E₀ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ χ) = _
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, inLevel_smul]

omit [Fintype n] in
/-- The level swap has no entry between different sites, for any site map that reads the
first component. -/
theorem levelSwap_apply_of_site_ne {V : Type*} (π : n → V) :
    ∀ i j : n × Fin 2, π i.1 ≠ π j.1 → levelSwap n i j = 0 := by
  intro i j hij
  have h1 : i.1 ≠ j.1 := fun h => hij (by rw [h])
  simp [levelSwap, h1]

end Blocks

/-! ### The lattice Dirac band -/

section Dirac

variable {κ Sp St : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype St] [DecidableEq St] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}
  {α' : κ → Matrix St St ℂ} {β' : Matrix St St ℂ}

omit [Fintype Sp] [DecidableEq Sp] [Nonempty Sp] in
/-- ★★★ **The swap of a packet resting in the first level leaves at the band's group
velocity.** The transponder of UA-21 with the lattice Dirac band `(α', β', J', μ')`,
`μ' > 0`, and no contact term. Its first level holds the wave function of the flat packet
about `k₀'`. The level swap of that state is the packet in the second level; after the flow
time `s ≥ 0` it is the packet at `s`, whose weight outside the box moving at the band's
group velocity is at most `flatTailD s`. -/
theorem transponder_band_swapped_moves (h' : IsCliffordFamily α' β') {e₀' : St → ℂ}
    (he' : β' *ᵥ e₀' = e₀') (hn' : star e₀' ⬝ᵥ e₀' = 1) {J' μ' : ℝ} (hμ' : 0 < μ')
    (E₀ : ℝ) (lo' : κ → ℤ) {Nw' : κ → ℕ} (hN' : ∀ j, 0 < Nw' j) (hNL' : ∀ j, Nw' j < L)
    (k₀' : κ → ℝ) {w' : κ → ℝ} (hw0' : ∀ j, 0 ≤ w' j)
    (hw' : ∀ m ∈ boxWindowD lo' Nw', ∀ j, |angleZD L m j - k₀' j| ≤ w' j) {γ' : κ → ℝ}
    (hγ' : ∀ i, γ' i < 1) {s : ℝ} (hs : 0 ≤ s) :
    exp (s • ((-Complex.I) • Matrix.blockDiagonal
          (bandBlocks E₀ (latticeDiracHam (L := L) α' β' J' μ'))))
        *ᵥ (levelSwap ((κ → ZMod L) × St) *ᵥ inLevel 0
          (packetD (L := L) α' β' J' μ' e₀' (boxWindowD lo' Nw')
            (unitAmpD L J' μ' (flatAmpD lo' Nw')) 0))
      = inLevel 1 (packetD (L := L) α' β' J' μ' e₀' (boxWindowD lo' Nw')
          (unitAmpD L J' μ' (flatAmpD lo' Nw')) s)
    ∧ regionWeightD (packetD (L := L) α' β' J' μ' e₀' (boxWindowD lo' Nw')
          (unitAmpD L J' μ' (flatAmpD lo' Nw')) s)
        (movedBoxD L J' μ' k₀' (fun _ => 1) γ' s)ᶜ
      ≤ flatTailD L J' μ' Nw' w' γ' s := by
  refine ⟨?_, ?_⟩
  · rw [levelSwap_mulVec_inLevel_zero]
    unfold packetD
    rw [inLevel_sum, inLevel_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm : (s • ((-Complex.I) • bandBlocks E₀ (latticeDiracHam (L := L) α' β' J' μ') 1))
          *ᵥ diracModeD α' β' J' μ' (castZ L m) e₀'
        = (-(Complex.I * latticeED J' μ' (angleZD L m)) * s)
          • diracModeD α' β' J' μ' (castZ L m) e₀' := by
      show (s • ((-Complex.I) • latticeDiracHam (L := L) α' β' J' μ'))
          *ᵥ diracModeD α' β' J' μ' (castZ L m) e₀' = _
      rw [← smul_assoc, Complex.real_smul, Matrix.smul_mulVec,
        latticeDiracHam_mulVec_diracModeD h', dispE_modeSD_castZ, smul_smul]
      congr 1
      ring
    rw [inLevel_smul, inLevel_smul, Matrix.mulVec_smul,
      exp_blockDiagonal_mulVec_inLevel_of_eigen _ 1 hm, smul_smul, ← Complex.exp_eq_exp_ℂ]
    congr 1
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  · have hh := regionWeightD_flatPacket_compl_movedBoxD_le_window (L := L) (J := J') h' he'
      hn' hμ' lo' hN' hNL' k₀' hw0' hw' s hγ'
    rw [abs_of_nonneg hs] at hh
    rw [flatTailD]
    exact hh

/-- ★★★ **Item (1) of UO-26 for the transponder with a band.** The messenger is the flat
packet of the lattice Dirac field; the transponder has the blocks of UA-21 with any
Hermitian `H₁` for its second level and starts in its first level with a wave function `χ`
of norm at most `1` supported on the sites `B`. If up to the flow time `t` no site of the
messenger's moving box is in the relation `r` with a site of `B`, the part with the
transponder in its second level at `t` has norm at most `‖Q‖ |g| √(flatTailD t) · t`. -/
theorem transponder_band_launch_le [Nonempty St]
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (E₀ : ℝ) {H₁ : Matrix ((κ → ZMod L) × St) ((κ → ZMod L) × St) ℂ}
    (hH₁ : H₁.IsHermitian) (g : ℝ)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (χ : (κ → ZMod L) × St → ℂ) (hχn : ∑ p, ‖χ p‖ ^ 2 ≤ 1)
    (B : Finset (κ → ZMod L)) (hχB : ∀ p : (κ → ZMod L) × St, p.1 ∉ B → χ p = 0) {t : ℝ}
    (ht : 0 ≤ t)
    (hsep : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      ¬ r a b) :
    Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
          ⊗ₖ levelProj ((κ → ZMod L) × St) 1)
        * exp (t • ((-Complex.I) • (compositeH (latticeDiracHam (L := L) α β J μ)
              (Matrix.blockDiagonal (bandBlocks E₀ H₁))
            + (g : ℂ) • gateOp Prod.fst
                (fun q : ((κ → ZMod L) × St) × Fin 2 => q.1.1) r
                (levelSwap ((κ → ZMod L) × St))))))
          *ᵥ fun y : ((κ → ZMod L) × Sp) × (((κ → ZMod L) × St) × Fin 2) =>
            packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
              (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * inLevel 0 χ y.2) x‖ ^ 2)
      ≤ ‖(1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
          ⊗ₖ levelProj ((κ → ZMod L) × St) 1‖
        * (|g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * t)) := by
  have hstat : Matrix.blockDiagonal (bandBlocks E₀ H₁) *ᵥ inLevel 0 χ
      = ((E₀ : ℝ) : ℂ) • inLevel 0 χ := by
    rw [blockDiagonal_mulVec_inLevel]
    show inLevel 0 ((((E₀ : ℝ) : ℂ) • (1 : Matrix _ _ ℂ)) *ᵥ χ) = _
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, inLevel_smul]
  exact transponder_launch_flatPacket_stationary_le
    (fun q : ((κ → ZMod L) × St) × Fin 2 => q.1.1) r
    (levelSwap_apply_of_site_ne (fun p : (κ → ZMod L) × St => p.1)) h he hn hμ
    (bandBlocks_isHermitian E₀ hH₁) g lo hN hNL k₀ hw0 hw hγ (inLevel 0 χ)
    (inLevel_zero_apply_of_snd_eq_one χ) hstat (by rw [sum_norm_sq_inLevel]; exact hχn) B
    (fun q hq => by
      have := hχB q.1 hq
      simp [inLevel, this]) ht hsep

end Dirac

end CSD.RecordLayer

end

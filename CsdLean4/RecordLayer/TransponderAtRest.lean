/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderLaunchState
public import CsdLean4.RecordLayer.DiracArrival

/-!
# No launch before the packet's box reaches a transponder at rest

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (1), the caused return;
remainder (a) of the row: a transponder state that meets the hypotheses of UD-251).

`transponder_launch_flatPacket_le` takes as hypotheses that the transponder has norm at most
`1` along its own orbit and keeps all but `ε_B` of its weight on the sites `B`. Here they are
met: by any stationary state of the transponder supported on `B`, and so by a transponder at
rest (no hopping, one energy for each level).

* `exp_mulVec_stationary`, `norm_exp_mulVec_stationary` — a stationary state moves by a phase,
  so every component keeps its size;
* `blockDiagonal_smul_one_mulVec` — a transponder with no hopping acts on a state by the
  energy of each component's level;
* ★★★ `transponder_launch_flatPacket_stationary_le` — the messenger is the flat packet, the
  transponder is in a stationary state of norm at most `1`, in its first level, supported on
  the sites `B`: while no site of the packet's moving box is related to a site of `B`, the
  part with the transponder in its second level at `t` has norm at most
  `‖Q‖ |g| √(flatTailD t) · t`;
* ★★★ `transponder_launch_flatPacket_resting_le` — **the same for a transponder at rest**
  (energies `E 0`, `E 1`, no hopping), for any state in the first level supported on `B`. No
  hypothesis is left on the transponder's orbit.

## Honest scope

⚠️ **An upper bound: nothing is shown to be launched.** Item (1) of UO-26 only.

⚠️ **The bound grows like `t`**, with the square root of the packet's tail.

⚠️ **The relation `r` and the sites `B` are parameters.** That the moving box is not in
contact with `B` up to `t` is a hypothesis; no instance with numbers.

⚠️ **The carriers' own Hamiltonians and the contact term only.** No pointer, no arena.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-251, UD-252); `RecordLayer/TransponderLaunchState.lean`
(`transponder_launch_flatPacket_le`); `RecordLayer/DiracArrival.lean`
(`exp_mulVec_of_mulVec_eq_smul`); `RecordLayer/UnifiedTransponder.lean` (`levelProj`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### A stationary state -/

section Stationary

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A stationary state moves by a phase. -/
theorem exp_mulVec_stationary {C : Matrix m m ℂ} {φ : m → ℂ} {E : ℝ}
    (h : C *ᵥ φ = (E : ℂ) • φ) (s : ℝ) :
    exp (s • ((-Complex.I) • C)) *ᵥ φ = Complex.exp (-(Complex.I * E) * s) • φ := by
  have hm : (s • ((-Complex.I) • C)) *ᵥ φ = (-(Complex.I * E) * s) • φ := by
    rw [← smul_assoc, Complex.real_smul, Matrix.smul_mulVec, h, smul_smul]
    congr 1
    ring
  rw [exp_mulVec_of_mulVec_eq_smul hm, ← Complex.exp_eq_exp_ℂ]

/-- Along the orbit of a stationary state every component keeps its size. -/
theorem norm_exp_mulVec_stationary {C : Matrix m m ℂ} {φ : m → ℂ} {E : ℝ}
    (h : C *ᵥ φ = (E : ℂ) • φ) (s : ℝ) (q : m) :
    ‖(exp (s • ((-Complex.I) • C)) *ᵥ φ) q‖ = ‖φ q‖ := by
  rw [exp_mulVec_stationary h, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_exp]
  have : (-(Complex.I * (E : ℂ)) * (s : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, one_mul]

end Stationary

/-! ### The transponder -/

section Rest

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A transponder with no hopping acts on a state by the energy of each component's level. -/
theorem blockDiagonal_smul_one_mulVec (E : Fin 2 → ℝ) (φ : n × Fin 2 → ℂ) (q : n × Fin 2) :
    (Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *ᵥ φ) q
      = (E q.2 : ℂ) * φ q := by
  have hd : Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = Matrix.diagonal fun x : n × Fin 2 => ((E x.2 : ℝ) : ℂ) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.blockDiagonal_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
    split_ifs <;> simp_all
  rw [hd, Matrix.mulVec_diagonal]

end Rest

section Boxes

variable {κ Sp n : Type*} [Fintype κ] [DecidableEq κ] [Fintype Sp] [DecidableEq Sp]
  [Nonempty Sp] [Fintype n] [DecidableEq n] [Nonempty n] {L : ℕ} [NeZero L]
  {α : κ → Matrix Sp Sp ℂ} {β : Matrix Sp Sp ℂ}

/-- ★★★ **No launch before the packet's box reaches a transponder in a stationary state.** The
messenger is the flat packet of the lattice Dirac field of any dimension. The transponder is
in a stationary state of its own Hamiltonian, of norm at most `1`, in its first level and
supported on the sites `B`. If up to the flow time `t` no site of the packet's moving box is
in the relation `r` with a site of `B`, the part with the transponder in its second level at
`t` has norm at most `‖Q‖ |g| √(flatTailD t) · t`. -/
theorem transponder_launch_flatPacket_stationary_le (τ : n × Fin 2 → κ → ZMod L)
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian) (g : ℝ)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0) {E : ℝ}
    (hstat : Matrix.blockDiagonal T *ᵥ φ = (E : ℂ) • φ) (hφn : ∑ q, ‖φ q‖ ^ 2 ≤ 1)
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {t : ℝ} (ht : 0 ≤ t)
    (hsep : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      ¬ r a b) :
    Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
          ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH (latticeDiracHam (L := L) α β J μ)
              (Matrix.blockDiagonal T)
            + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))))
          *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
            packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
              (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2)
      ≤ ‖(1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1‖
        * (|g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * t)) := by
  have key := transponder_launch_flatPacket_le τ r hτ h he hn hμ hT g lo hN hNL k₀ hw0 hw hγ φ
    hφ B ht le_rfl hsep
    (fun s _ _ => by
      simp only [norm_exp_mulVec_stationary hstat]
      exact hφn)
    (fun s _ _ => by
      simp only [norm_exp_mulVec_stationary hstat]
      refine le_of_eq (Finset.sum_eq_zero fun q _ => ?_)
      split_ifs with hq
      · rfl
      · rw [hφB q hq, norm_zero]
        norm_num)
  rwa [add_zero] at key

/-- ★★★ **No launch before the packet's box reaches a transponder at rest.** As
`transponder_launch_flatPacket_stationary_le` for a transponder with no hopping and the
energies `E 0`, `E 1`: any state of norm at most `1` in the first level, supported on the
sites `B`. -/
theorem transponder_launch_flatPacket_resting_le (τ : n × Fin 2 → κ → ZMod L)
    (r : (κ → ZMod L) → (κ → ZMod L) → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0)
    (h : IsCliffordFamily α β) {e₀ : Sp → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (E : Fin 2 → ℝ) (g : ℝ)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (φ : n × Fin 2 → ℂ) (hφ : ∀ q : n × Fin 2, q.2 = 1 → φ q = 0)
    (hφn : ∑ q, ‖φ q‖ ^ 2 ≤ 1)
    (B : Finset (κ → ZMod L)) (hφB : ∀ q, τ q ∉ B → φ q = 0) {t : ℝ} (ht : 0 ≤ t)
    (hsep : ∀ s, 0 ≤ s → s ≤ t → ∀ a ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s, ∀ b ∈ B,
      ¬ r a b) :
    Real.sqrt (∑ x, ‖((((1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ)
          ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH (latticeDiracHam (L := L) α β J μ)
              (Matrix.blockDiagonal fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
            + (g : ℂ) • gateOp Prod.fst τ r (levelSwap n)))))
          *ᵥ fun y : ((κ → ZMod L) × Sp) × (n × Fin 2) =>
            packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
              (unitAmpD L J μ (flatAmpD lo Nw)) 0 y.1 * φ y.2) x‖ ^ 2)
      ≤ ‖(1 : Matrix ((κ → ZMod L) × Sp) ((κ → ZMod L) × Sp) ℂ) ⊗ₖ levelProj n 1‖
        * (|g| * (Real.sqrt (flatTailD L J μ Nw w γ t) * t)) := by
  have hT : ∀ l : Fin 2, (((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := fun l =>
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.2 (by
      rw [Complex.star_def, Complex.conj_ofReal]))
  have hstat : Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      *ᵥ φ = ((E 0 : ℝ) : ℂ) • φ := by
    funext q
    rw [blockDiagonal_smul_one_mulVec, Pi.smul_apply, smul_eq_mul]
    by_cases hq : q.2 = 1
    · rw [hφ q hq, mul_zero, mul_zero]
    · have h0 : q.2 = 0 := by
        have := q.2.isLt
        ext
        have h1 : (q.2 : ℕ) ≠ 1 := fun h => hq (Fin.ext h)
        simp only [Fin.val_zero]
        omega
      rw [h0]
  exact transponder_launch_flatPacket_stationary_le τ r hτ h he hn hμ hT g lo hN hNL k₀ hw0 hw
    hγ φ hφ hstat hφn B hφB ht hsep

end Boxes

end CSD.RecordLayer

end

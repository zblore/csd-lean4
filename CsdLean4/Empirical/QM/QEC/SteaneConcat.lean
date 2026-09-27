/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneEncoder
public import CsdLean4.Empirical.QM.QEC.SteaneThreshold

/-!
# The concatenated Steane code: the quantum recovery at level `k`

**Category:** 3-Local (Empirical, QM twin). BACKLOG #86, the second half of #61: the *quantum*
statement at every level of concatenation, where `SteaneThreshold.lean` (#51) had it at level one and
the pattern recursion (`concatMeasure_concatBad_le`) at every level.

## One level up, over any register

`concatEnc W = blockKron (fun _ => W) * steaneEnc` puts seven `W`-encoded blocks under one Steane
layer; it is an isometry when `W` is (`concatEnc_conjTranspose_mul`). The engine is
★★ `exists_concatEnc_step`: **if a pair of block-wise errors acts as a scalar on the encoded qubit of
every block but at most two named ones, it acts as a scalar one level up.** The good blocks give
their scalars, and the tensor of the two remaining logical operators is scalar because the Steane code
has distance three (`exists_steaneEnc_blockKron` in `SteaneEncoder.lean`). Two blocks, not one: the
Knill–Laflamme condition is a condition on *pairs* of errors, and each error of the pair may spend its
one arbitrary block somewhere else.

## The tower

`cLabel` is the label space (`cLabel 0 = Fin 2`, `cLabel (k+1) = Fin 7 → cLabel k`, literally
recursive, with its `Fintype`/`DecidableEq` by recursion), `cEnc` the encoder, `cProj` the code
projector, and `cFam`/`cErr` the error family: **a level-`k` error in every block and optionally one
block carrying an arbitrary operator**, addressed by a matrix unit. Then

* ★★★ `encoderKL_cErr`: Knill–Laflamme at every level, in the encoder form of
  `Mathlib/QuantumInfo/KnillLaflamme.lean` — `cEnc kᴴ Eᵢᴴ Eⱼ cEnc k = γ • 1`. The induction is the
  step above, with the two named blocks the arbitrary blocks of the two errors;
* ★★★ `exists_cErr_recovery`: **one recovery channel per level** for that family.

## The patterns, and the failure bound

`PatErr k x E` says `E` is an error *of the pattern* `x`: a tensor over the tree with the identity at
every unhit leaf and an arbitrary operator at every hit one. `isBad 7 k x = false` — at most one bad
sub-block at every level — is the good event of the code-capacity recursion, and

* ★★ `patErr_mem_span`: **every good pattern's errors lie in the span of the family.** The good
  blocks are spans by induction, the one bad block is a combination of matrix units
  (`Matrix.matrix_eq_sum_single`), and `blockKron` is multilinear (`blockKron_sum_smul`), so the
  tensor expands over exactly `cErr (k + 1)`;
* ★★★ `exists_concat_recovery`: the recovery returns the code state up to a scalar for every good
  pattern, through #61's span step (`exists_smul_recovery_apply_of_eq_lin_comb`);
* ★★★ `exists_concat_recovery_unitary`: for a **unitary** error the scalar is `1`
  (`smul_eq_one_of_unitary`: the error and the channel both preserve the trace), so the level-`k` code
  **restores every code state exactly** from every good pattern. What it says nothing about is
  `concatBad 7 k` (`good_eq_compl_concatBad`), whose probability under independent noise of rate `p`
  is at most `(21 p)^{2^k}/21` (`steane_concatBad_le`) — the encoded failure bound at every level.

## Honest scope

⚠️ Code capacity still: the noise is on the data qubits, the recovery is applied once, and the
gates of the encoder and of the recovery are perfect. Faulty gates, error propagation and extended
rectangles are BACKLOG #62, deliberately not claimed.
⚠️ The recovery is a *Knill–Laflamme* channel, not the block-by-block decoder a compiler would
run: what is proved is that a correcting channel exists at every level (and is the one
`exists_recovery_of_encoderKL` builds), not that the hierarchical decoder is optimal or efficient.
⚠️ The scalar of `exists_concat_recovery` is existential, as in #61: for a non-unitary error the
recovery returns the code state with a weight, and nothing here normalises it.
⚠️ `ρ.trace ≠ 0` in the unitary statement is what turns "up to a scalar" into "exactly"; a density
operator has trace one, so it is no restriction in use.
⚠️ The family `cErr` addresses its one arbitrary block by matrix units, a spanning set, not by
Paulis. That is enough for the span argument and avoids Pauli bookkeeping at every level; the price is
that the family is larger than it needs to be.

## Source

A. Steane, *Error correcting codes in quantum theory*, PRL 77 (1996); E. Knill, R. Laflamme, W. Zurek,
*Science* 279 (1998) 342 (concatenation and the threshold); M. Nielsen, I. Chuang, §10.6.1;
`Mathlib/QuantumInfo/BlockKron.lean`, `Mathlib/QuantumInfo/KnillLaflamme.lean` (the encoder form and
the span step), `Empirical/QM/QEC/SteaneEncoder.lean`, `Empirical/QM/QEC/SteaneArbitrary.lean` (#61),
`Empirical/QM/QEC/SteaneThreshold.lean` (#51), `Mathlib/Probability/CodeCapacityThreshold.lean`;
`specs/BACKLOG.md` #86; `specs/steane-plan.md`; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo QuantumInfo.Controlled

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### One level up -/

section OneLevel

variable {L : Type*} [Fintype L]

/-- **One level up**: seven blocks, each carrying the encoder `W`, then the Steane encoder on the
seven encoded qubits. -/
noncomputable def concatEnc (W : Matrix L (Fin 2) ℂ) : Matrix (Fin 7 → L) (Fin 2) ℂ :=
  blockKron (fun _ : Fin 7 => W) * steaneEnc

/-- The level-up encoder is an isometry if `W` is. -/
theorem concatEnc_conjTranspose_mul {W : Matrix L (Fin 2) ℂ} (hW : Wᴴ * W = 1) :
    (concatEnc W)ᴴ * concatEnc W = 1 := by
  have hb : blockKron (fun _ : Fin 7 => Wᴴ) * blockKron (fun _ : Fin 7 => W)
      = 1 := by
    rw [blockKron_mul,
      show (fun _ : Fin 7 => Wᴴ * W) = (fun _ : Fin 7 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) from
        funext fun _ => hW,
      blockKron_one]
  calc (concatEnc W)ᴴ * concatEnc W
      = steaneEncᴴ * (blockKron (fun _ : Fin 7 => Wᴴ) * blockKron (fun _ : Fin 7 => W))
          * steaneEnc := by
        rw [concatEnc, conjTranspose_mul, blockKron_conjTranspose]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hb, Matrix.mul_one, steaneEnc_conjTranspose_mul]

/-- ★★ **The induction step.** A pair of block-wise errors whose logical actions are scalars on
every block but at most two named ones acts as a scalar on the qubit encoded one level up: the good
blocks contribute their scalars and the tensor of the remaining logical operators is scalar by the
Steane code's distance (`exists_steaneEnc_blockKron`). -/
theorem exists_concatEnc_step {W : Matrix L (Fin 2) ℂ} (b₀ b₁ : Fin 7)
    (A A' : Fin 7 → Matrix L L ℂ)
    (h : ∀ b, b ≠ b₀ → b ≠ b₁ → ∃ γ : ℂ, Wᴴ * (A b)ᴴ * A' b * W = γ • 1) :
    ∃ δ : ℂ, (concatEnc W)ᴴ * (blockKron A)ᴴ * blockKron A' * concatEnc W = δ • 1 := by
  have hb : blockKron (fun _ : Fin 7 => Wᴴ) * blockKron (fun b => (A b)ᴴ) * blockKron A'
      * blockKron (fun _ : Fin 7 => W) = blockKron (fun b => Wᴴ * (A b)ᴴ * A' b * W) := by
    rw [blockKron_mul, blockKron_mul, blockKron_mul]
  have key : (concatEnc W)ᴴ * (blockKron A)ᴴ * blockKron A' * concatEnc W
      = steaneEncᴴ * blockKron (fun b => Wᴴ * (A b)ᴴ * A' b * W) * steaneEnc := by
    rw [← hb]
    rw [concatEnc, conjTranspose_mul, blockKron_conjTranspose, blockKron_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [key]
  exact exists_steaneEnc_blockKron b₀ b₁ _ h

end OneLevel

/-! ### The tower of concatenated registers -/

/-- The label space of the level-`k` concatenated register: one qubit at level `0`, seven blocks of
the previous level after that. -/
def cLabel : ℕ → Type
  | 0 => Fin 2
  | k + 1 => Fin 7 → cLabel k

instance instFintypeCLabel : ∀ k, Fintype (cLabel k)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | k + 1 =>
      have : Fintype (cLabel k) := instFintypeCLabel k
      inferInstanceAs (Fintype (Fin 7 → cLabel k))

instance instDecidableEqCLabel : ∀ k, DecidableEq (cLabel k)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | k + 1 =>
      have : DecidableEq (cLabel k) := instDecidableEqCLabel k
      inferInstanceAs (DecidableEq (Fin 7 → cLabel k))

/-- The encoder of the level-`k` concatenated code: nothing at level `0`, one more Steane layer at
every step. -/
noncomputable def cEnc : ∀ k, Matrix (cLabel k) (Fin 2) ℂ
  | 0 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | k + 1 => concatEnc (cEnc k)

/-- The code projector of the level-`k` code. -/
noncomputable def cProj (k : ℕ) : Matrix (cLabel k) (cLabel k) ℂ := cEnc k * (cEnc k)ᴴ

theorem cEnc_zero : cEnc 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl

theorem cEnc_conjTranspose_mul : ∀ k, (cEnc k)ᴴ * cEnc k = 1
  | 0 => by
      show ((1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
      rw [conjTranspose_one, Matrix.one_mul]
  | k + 1 => by
      rw [cEnc]
      exact concatEnc_conjTranspose_mul (cEnc_conjTranspose_mul k)

theorem isCodeProjector_cProj (k : ℕ) : IsCodeProjector (cProj k) :=
  isCodeProjector_mul_conjTranspose (cEnc_conjTranspose_mul k)

/-! ### The error family of the level-`k` code -/

/-- The index of the level-`k` error family: at level `k + 1`, a level-`k` error in every block and
optionally **one** block carrying an arbitrary operator, addressed by a matrix unit. -/
def cFam : ℕ → Type
  | 0 => Unit
  | k + 1 => (Fin 7 → cFam k) × Option (Fin 7 × cLabel k × cLabel k)

instance instFintypeCFam : ∀ k, Fintype (cFam k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 =>
      have : Fintype (cFam k) := instFintypeCFam k
      inferInstanceAs (Fintype ((Fin 7 → cFam k) × Option (Fin 7 × cLabel k × cLabel k)))

instance instDecidableEqCFam : ∀ k, DecidableEq (cFam k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 =>
      have : DecidableEq (cFam k) := instDecidableEqCFam k
      inferInstanceAs (DecidableEq ((Fin 7 → cFam k) × Option (Fin 7 × cLabel k × cLabel k)))

/-- The level-`k` error family. -/
noncomputable def cErr : ∀ k, cFam k → Matrix (cLabel k) (cLabel k) ℂ
  | 0, _ => 1
  | k + 1, ⟨g, none⟩ => blockKron fun b => cErr k (g b)
  | k + 1, ⟨g, some (b₀, u, v)⟩ =>
      blockKron fun b => if b = b₀ then Matrix.single u v 1 else cErr k (g b)

theorem cErr_zero (i : cFam 0) : cErr 0 i = (1 : Matrix (cLabel 0) (cLabel 0) ℂ) := rfl

/-- The blocks of a level-`(k + 1)` family member. -/
noncomputable def cBlocks (k : ℕ) (i : cFam (k + 1)) (b : Fin 7) :
    Matrix (cLabel k) (cLabel k) ℂ :=
  match i.2 with
  | none => cErr k (i.1 b)
  | some (b₀, u, v) => if b = b₀ then Matrix.single u v 1 else cErr k (i.1 b)

/-- The block a level-`(k + 1)` family member may treat as arbitrary. -/
def cBadPos (k : ℕ) (i : cFam (k + 1)) : Fin 7 :=
  match i.2 with
  | none => 0
  | some (b₀, _, _) => b₀

theorem cErr_succ (k : ℕ) (i : cFam (k + 1)) : cErr (k + 1) i = blockKron (cBlocks k i) := by
  obtain ⟨g, bad⟩ := i
  cases bad with
  | none => rfl
  | some p =>
      obtain ⟨b₀, u, v⟩ := p
      rfl

/-- Away from its one arbitrary block, a family member carries a level-`k` family error. -/
theorem exists_cBlocks_eq (k : ℕ) (i : cFam (k + 1)) {b : Fin 7} (hb : b ≠ cBadPos k i) :
    ∃ f : cFam k, cBlocks k i b = cErr k f := by
  obtain ⟨g, bad⟩ := i
  cases bad with
  | none => exact ⟨g b, rfl⟩
  | some p =>
      obtain ⟨b₀, u, v⟩ := p
      exact ⟨g b, by
        show (if b = b₀ then Matrix.single u v 1 else cErr k (g b)) = cErr k (g b)
        rw [if_neg (show b ≠ b₀ from hb)]⟩

/-- ★★★ **Knill–Laflamme at every level, in encoder form.** Every pair of the level-`k` family acts
on the encoded qubit as a scalar: the good blocks by induction, the one arbitrary block of each error
by the Steane code's distance. -/
theorem encoderKL_cErr : ∀ k, EncoderKL (cEnc k) (cErr k)
  | 0 => by
      rw [encoderKL_iff]
      intro i j
      refine ⟨1, ?_⟩
      show ((1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * ((1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ
          * (1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) = (1 : ℂ) • 1
      rw [conjTranspose_one, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul, one_smul]
  | k + 1 => by
      rw [encoderKL_iff]
      intro i j
      have hstep := exists_concatEnc_step (W := cEnc k) (cBadPos k i) (cBadPos k j)
        (cBlocks k i) (cBlocks k j) (fun b hb₀ hb₁ => by
          obtain ⟨f, hf⟩ := exists_cBlocks_eq k i hb₀
          obtain ⟨f', hf'⟩ := exists_cBlocks_eq k j hb₁
          rw [hf, hf']
          exact (encoderKL_iff.mp (encoderKL_cErr k)) f f')
      obtain ⟨δ, hδ⟩ := hstep
      refine ⟨δ, ?_⟩
      rw [cErr_succ, cErr_succ]
      exact hδ

/-- ★★★ **The recovery of the level-`k` concatenated code.** One channel corrects the whole family:
a level-`k` error in every block and one arbitrary block at every level. -/
theorem exists_cErr_recovery (k : ℕ) :
    ∃ (c : Matrix (cFam k) (cFam k) ℂ) (R : Channel (cLabel k) (cLabel k) (Option (cFam k))),
      ∀ ρ : Matrix (cLabel k) (cLabel k) ℂ, ρ = cProj k * ρ * cProj k →
        ∀ i j, R.apply (cErr k i * ρ * (cErr k j)ᴴ) = c j i • ρ :=
  exists_recovery_of_encoderKL (cEnc_conjTranspose_mul k) (encoderKL_cErr k)

/-! ### The errors of a pattern -/

/-- **The errors of an error pattern**: at level `0` the identity unless the qubit is hit, and at
level `k + 1` a tensor over the blocks whose factors are errors of the sub-patterns. The operators at
the hit leaves are arbitrary — this is the error set the code capacity argument counts. -/
def PatErr : ∀ k, ConcatPat 7 k → Matrix (cLabel k) (cLabel k) ℂ → Prop
  | 0, x, E => x = false → E = 1
  | k + 1, x, E => ∃ N : Fin 7 → Matrix (cLabel k) (cLabel k) ℂ,
      E = blockKron N ∧ ∀ b, PatErr k (x b) (N b)

theorem patErr_zero {x : ConcatPat 7 0} {E : Matrix (cLabel 0) (cLabel 0) ℂ} :
    PatErr 0 x E ↔ (x = false → E = 1) := by
  show (x = false → E = 1) ↔ (x = false → E = 1)
  exact Iff.rfl

theorem patErr_succ {k : ℕ} {x : ConcatPat 7 (k + 1)}
    {E : Matrix (cLabel (k + 1)) (cLabel (k + 1)) ℂ} :
    PatErr (k + 1) x E ↔ ∃ N : Fin 7 → Matrix (cLabel k) (cLabel k) ℂ,
      E = blockKron N ∧ ∀ b, PatErr k (x b) (N b) := by
  show (∃ N : Fin 7 → Matrix (cLabel k) (cLabel k) ℂ,
      E = blockKron N ∧ ∀ b, PatErr k (x b) (N b)) ↔ _
  exact Iff.rfl

/-- A filler index of the level-`k` family: the identity error. -/
def cIdOne : ∀ k, cFam k
  | 0 => ()
  | k + 1 => ⟨fun _ => cIdOne k, none⟩

/-- The per-block spanning family of the span argument: the level-`k` family for the good blocks,
and the matrix units for the one block treated as arbitrary. -/
noncomputable def cSpanFam (k : ℕ) :
    cFam k ⊕ (cLabel k × cLabel k) → Matrix (cLabel k) (cLabel k) ℂ :=
  Sum.elim (cErr k) fun p => Matrix.single p.1 p.2 (1 : ℂ)

/-- The coefficients of the span argument: the good blocks use the coefficients the induction gives,
the one arbitrary block the entries of its own operator. -/
noncomputable def cSpanCoef (k : ℕ) (b₀ : Fin 7) (a : Fin 7 → cFam k → ℂ)
    (X : Matrix (cLabel k) (cLabel k) ℂ) (b : Fin 7) :
    cFam k ⊕ (cLabel k × cLabel k) → ℂ :=
  Sum.elim (fun i => if b = b₀ then 0 else a b i) fun p => if b = b₀ then X p.1 p.2 else 0

/-- ★★ **Every good pattern's errors lie in the span of the family.** A pattern with at most one bad
sub-block at every level: the good blocks are in the span of the level-`k` family by induction, the
one bad block carries an arbitrary operator and so a combination of matrix units, and `blockKron` is
multilinear — so the tensor expands over exactly the family `cErr (k + 1)`. -/
theorem patErr_mem_span : ∀ (k : ℕ) (x : ConcatPat 7 k), isBad 7 k x = false →
    ∀ E : Matrix (cLabel k) (cLabel k) ℂ, PatErr k x E →
      E ∈ Submodule.span ℂ (Set.range (cErr k))
  | 0, x, hx, E, hE => by
      refine Submodule.subset_span ⟨cIdOne 0, ?_⟩
      rw [cErr_zero, patErr_zero.mp hE hx]
  | k + 1, x, hx, E, hE => by
      classical
      obtain ⟨N, hEN, hN⟩ := patErr_succ.mp hE
      have hcard : (Finset.univ.filter fun b : Fin 7 => isBad 7 k (x b) = true).card ≤ 1 := by
        by_contra hc
        rw [show isBad 7 (k + 1) x
            = decide (2 ≤ (Finset.univ.filter fun b : Fin 7 => isBad 7 k (x b) = true).card)
            from rfl, decide_eq_false_iff_not] at hx
        exact hx (by omega)
      obtain ⟨b₀, hb₀⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
      have hgood : ∀ b, b ≠ b₀ → isBad 7 k (x b) = false := by
        intro b hb
        rcases Bool.eq_false_or_eq_true (isBad 7 k (x b)) with h | h
        · exact absurd (Finset.mem_singleton.mp
            (hb₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ b, h⟩))) hb
        · exact h
      have hIH : ∀ b, ∃ a : cFam k → ℂ, b ≠ b₀ → ∑ i, a i • cErr k i = N b := by
        intro b
        by_cases hb : b = b₀
        · exact ⟨0, fun hc => absurd hb hc⟩
        · obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
            (patErr_mem_span k (x b) (hgood b hb) (N b) (hN b))
          exact ⟨a, fun _ => ha⟩
      choose a ha using hIH
      have hbad : ∑ p : cLabel k × cLabel k,
          N b₀ p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ) = N b₀ := by
        conv_rhs => rw [Matrix.matrix_eq_sum_single (N b₀)]
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [Matrix.smul_single, smul_eq_mul, mul_one]
      have hblock : ∀ b : Fin 7,
          (∑ t, cSpanCoef k b₀ a (N b₀) b t • cSpanFam k t) = N b := by
        intro b
        rw [Fintype.sum_sum_type]
        simp only [cSpanCoef, cSpanFam, Sum.elim_inl, Sum.elim_inr]
        by_cases hb : b = b₀
        · simp only [if_pos hb, zero_smul, Finset.sum_const_zero, zero_add]
          rw [hb]
          exact hbad
        · simp only [if_neg hb, zero_smul, Finset.sum_const_zero, add_zero]
          exact ha b hb
      have hexp : E = ∑ g : Fin 7 → (cFam k ⊕ (cLabel k × cLabel k)),
          (∏ b, cSpanCoef k b₀ a (N b₀) b (g b)) • blockKron (fun b => cSpanFam k (g b)) := by
        rw [hEN]
        conv_lhs =>
          rw [show N = (fun b => ∑ t, cSpanCoef k b₀ a (N b₀) b t • cSpanFam k t) from
            funext fun b => (hblock b).symm]
        exact blockKron_sum_smul _ fun _ => cSpanFam k
      rw [hexp]
      refine Submodule.sum_mem _ fun g _ => ?_
      by_cases hzero : (∏ b, cSpanCoef k b₀ a (N b₀) b (g b)) = 0
      · rw [hzero, zero_smul]
        exact Submodule.zero_mem _
      refine Submodule.smul_mem _ _ ?_
      have hne : ∀ b, cSpanCoef k b₀ a (N b₀) b (g b) ≠ 0 := fun b hb0 =>
        hzero (Finset.prod_eq_zero (Finset.mem_univ b) hb0)
      obtain ⟨p, hp⟩ : ∃ p, g b₀ = Sum.inr p := by
        cases hg : g b₀ with
        | inl i =>
            refine absurd ?_ (hne b₀)
            rw [hg]
            show (if b₀ = b₀ then (0 : ℂ) else a b₀ i) = 0
            rw [if_pos rfl]
        | inr q => exact ⟨q, rfl⟩
      have hinl : ∀ b, b ≠ b₀ → ∃ i, g b = Sum.inl i := by
        intro b hb
        cases hg : g b with
        | inl i => exact ⟨i, rfl⟩
        | inr q =>
            refine absurd ?_ (hne b)
            rw [hg]
            show (if b = b₀ then N b₀ q.1 q.2 else (0 : ℂ)) = 0
            rw [if_neg hb]
      refine Submodule.subset_span
        ⟨((fun b => Sum.elim id (fun _ => cIdOne k) (g b), some (b₀, p.1, p.2)) : cFam (k + 1)), ?_⟩
      show blockKron (fun b => if b = b₀ then Matrix.single p.1 p.2 (1 : ℂ)
          else cErr k (Sum.elim id (fun _ => cIdOne k) (g b)))
        = blockKron (fun b => cSpanFam k (g b))
      refine congrArg blockKron (funext fun b => ?_)
      by_cases hb : b = b₀
      · subst hb
        rw [if_pos rfl, hp]
        rfl
      · obtain ⟨i, hi⟩ := hinl b hb
        rw [if_neg hb, hi]
        rfl

/-! ### The concatenated quantum recovery -/

/-- The good patterns are the complement of `concatBad`, whose probability `steane_concatBad_le`
bounds by `(21 p)^{2^k}/21`. -/
theorem good_eq_compl_concatBad (k : ℕ) :
    {x : ConcatPat 7 k | isBad 7 k x = false} = (concatBad 7 k)ᶜ := by
  ext x
  show isBad 7 k x = false ↔ ¬(isBad 7 k x = true)
  rw [Bool.not_eq_true]

/-- ★★★ **The concatenated quantum recovery, up to a scalar.** At every level one channel serves
every good pattern: for a pattern with at most one bad sub-block at every level, and arbitrary
operators on the hit leaves, the recovery returns the code state up to a scalar. -/
theorem exists_concat_recovery (k : ℕ) :
    ∃ R : Channel (cLabel k) (cLabel k) (Option (cFam k)),
      ∀ x : ConcatPat 7 k, isBad 7 k x = false →
        ∀ E : Matrix (cLabel k) (cLabel k) ℂ, PatErr k x E →
          ∃ γ : ℂ, ∀ ρ : Matrix (cLabel k) (cLabel k) ℂ, ρ = cProj k * ρ * cProj k →
            R.apply (E * ρ * Eᴴ) = γ • ρ := by
  obtain ⟨c, R, hR⟩ := exists_cErr_recovery k
  refine ⟨R, fun x hx E hE => ?_⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (patErr_mem_span k x hx E hE)
  exact exists_smul_recovery_apply_of_eq_lin_comb hR ha.symm

/-- ★★★ **The concatenated quantum recovery, exactly.** For a unitary error the scalar is `1`: the
level-`k` code restores every code state from every good pattern of unitary errors. The patterns for
which this says nothing are `concatBad 7 k`, whose probability under independent noise of rate `p` is
at most `(21 p)^{2^k}/21` (`steane_concatBad_le`, `good_eq_compl_concatBad`) — so the quantum
statement holds at every level, where the chain's document had it at level one. -/
theorem exists_concat_recovery_unitary (k : ℕ) :
    ∃ R : Channel (cLabel k) (cLabel k) (Option (cFam k)),
      ∀ x : ConcatPat 7 k, isBad 7 k x = false →
        ∀ E : Matrix (cLabel k) (cLabel k) ℂ, PatErr k x E → Eᴴ * E = 1 →
          ∀ ρ : Matrix (cLabel k) (cLabel k) ℂ, ρ = cProj k * ρ * cProj k → ρ.trace ≠ 0 →
            R.apply (E * ρ * Eᴴ) = ρ := by
  obtain ⟨c, R, hR⟩ := exists_cErr_recovery k
  refine ⟨R, fun x hx E hE hU ρ hρ htr => ?_⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (patErr_mem_span k x hx E hE)
  obtain ⟨γ, hγ⟩ := exists_smul_recovery_apply_of_eq_lin_comb hR ha.symm
  have h1 : γ = 1 := smul_eq_one_of_unitary R hU (hγ ρ hρ) htr
  rw [hγ ρ hρ, h1, one_smul]

end Steane
end QEC
end QM
end Empirical
end CSD

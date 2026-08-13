/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.ThreeQubit
public import CsdLean4.Empirical.QM.QEC.PhaseFlip

/-!
# The Shor 9-qubit code, by concatenation (§Q Q5, E1)

**Category:** 5-Empirical-QM. The last iconic empirical item
(`specs/BACKLOG.md` E1 / §Q Q5): the 9-qubit code that corrects an
arbitrary single-qubit Pauli error, built as the **concatenation** of the
two landed 3-qubit halves — the phase-flip code (`PhaseFlip.lean`) outside,
the bit-flip code (`ThreeQubit.lean`) inside.

## The combinator, and why 512 dimensions never appear entry-wise

The E1 row recorded the obstacle as dimensional: entry-wise tactics do not
survive `2⁹ = 512`. The route chosen here is the row's **code-concatenation
combinator** option. One structural lemma does all the lifting:

* `kron_mulVec` / `tel9_bkron_vkron` — the block Kronecker action
  factorises, `(A ⊗ B ⊗ C)(u ⊗ v ⊗ w) = (Au) ⊗ (Bv) ⊗ (Cw)`.

Every 9-qubit statement then reduces to the **8-dimensional block facts**
(where `fin_cases` is viable and mostly already proven): the inner code's
stabiliser fixing and syndromes are `ThreeQubit`'s lemmas applied to the
block states `B± = |000⟩ ± |111⟩ = logical 1 (±1)`, and the outer code's
action rides two new 8-dim computations (`tel_Xall_logical`,
`tel_Zin_logical`). Nothing above 8 dimensions is ever proved entry-wise.

## The code and its statements

`shorLogical a b = a·(B₊⊗B₊⊗B₊) + b·(B₋⊗B₋⊗B₋)` (unnormalised
coefficients, as in the 3-qubit modules — every statement is linear).

* **Codespace:** all eight stabilisers fix `shorLogical` —
  `innerStab_fixes_shorLogical` (the six `Z_iZ_j` pairs, via the bit-flip
  code's fixing lemmas) and `outerStab_fixes_shorLogical` (the two `X^{⊗6}`
  operators, via `B±` being `±1`-eigenstates of `X^{⊗3}`).
* **Syndromes:** ★ `innerStab_syndrome_X` — a bit flip at inner position
  `j` of block `s` trips block `s`'s stabiliser pair with exactly the
  3-qubit sign pattern (`xSyndromeSign`, injective:
  `xSyndromeSign_injective`), while every other-block inner stabiliser
  (`innerStab_fixes_X_other`) and both outer stabilisers
  (`outerStab_fixes_X`) read `+1`. ★ `outerStab_syndrome_Z` — a phase flip
  anywhere in block `s` trips the outer pair with the block pattern
  (`zSyndromeSign`, injective: `zSyndromeSign_injective`),
  **independent of which qubit inside was hit**, while every inner
  stabiliser reads `+1` (`innerStab_fixes_Z`). X errors trip only inner
  stabilisers and Z errors only outer ones, so the classes are separated
  by construction.
* **Corrections** (★★ the headline set): for every block `s : Fin 3` and
  inner position `j : Fin 3`,
  - `shor_corrects_X` — re-applying the identified bit flip restores the
    state;
  - `shor_corrects_Z_degenerate` — applying `Z` to the **first** qubit of
    the identified block restores the state *whichever* qubit inside was
    hit: the code is degenerate, and the recovery needs only the
    block-level syndrome;
  - `shor_corrects_XZ` — the composite error `X_j Z_j` (Y up to phase) is
    corrected by composing the two recoveries.
  With `pauli_decomposition` (`ErrorDiscretization.lean`: every 2×2 error
  is a combination of `I, X, Z, XZ`), this is the discretised form of
  "corrects an arbitrary single-qubit error".

## Honest scope

Correctable set: single-qubit errors (one position, one block). No claim
about two-error patterns, measurement dynamics (the syndrome extraction is
the eigenvalue reading, as in the 3-qubit modules — the collapse half at
9 qubits is not restated), or fault tolerance. The syndrome lemmas give
the eigenvalue table and the two injectivity facts; the full 28-row
distinctness tabulation is their mechanical product and is not separately
enumerated.

Cross-references: `specs/future-work.md`, `specs/BACKLOG.md` §Q (Q5) and
the E1 assessment row; `three_qubit_corrects_single_bitflip`,
`syndromePF_Z1` (the phase-flip half), `pauli_decomposition`,
`syndrome_collapse` (`SyndromeCollapse.lean`, the 3-qubit collapse half).

## Source

Shor 1995; Nielsen–Chuang §10.2 (the 9-qubit code as concatenation).
-/

@[expose] public section

open Matrix
open scoped Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

/-! ### The 9-qubit space and the block Kronecker combinator -/

/-- The inner-block index: one 3-qubit register. -/
abbrev I3 := Fin 2 × Fin 2 × Fin 2

/-- The 9-qubit Hilbert space, blocked as three 3-qubit registers. -/
abbrev H9 := EuclideanSpace ℂ (I3 × I3 × I3)

/-- Three-fold block Kronecker product of 8×8 block operators. -/
def bkron (A B C : Matrix I3 I3 ℂ) : Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ :=
  A ⊗ₖ (B ⊗ₖ C)

/-- Three-fold block tensor of block vectors:
`vkron u v w = u ⊗ v ⊗ w` entry-wise on the blocked index. -/
noncomputable def vkron (u v w : H3) : H9 :=
  ∑ p : I3 × I3 × I3, EuclideanSpace.single p (u p.1 * v p.2.1 * w p.2.2)

@[simp] lemma vkron_apply (u v w : H3) (p : I3 × I3 × I3) :
    vkron u v w p = u p.1 * v p.2.1 * w p.2.2 := by
  rw [vkron]
  simp [Finset.sum_apply]

/-- Mixed product for block Kroneckers. -/
lemma bkron_mul (A B C A' B' C' : Matrix I3 I3 ℂ) :
    bkron A B C * bkron A' B' C' = bkron (A * A') (B * B') (C * C') := by
  simp only [bkron, ← Matrix.mul_kronecker_mul]

@[simp] lemma bkron_one : bkron 1 1 1 = 1 := by
  simp only [bkron, Matrix.one_kronecker_one]

lemma bkron_neg_left (A B C : Matrix I3 I3 ℂ) :
    bkron (-A) B C = - bkron A B C := by
  rw [bkron, bkron, ← neg_one_smul ℂ A, Matrix.smul_kronecker, neg_one_smul]

lemma bkron_neg_mid (A B C : Matrix I3 I3 ℂ) :
    bkron A (-B) C = - bkron A B C := by
  rw [bkron, bkron, ← neg_one_smul ℂ B, Matrix.smul_kronecker,
    Matrix.kronecker_smul, neg_one_smul]

lemma bkron_neg_right (A B C : Matrix I3 I3 ℂ) :
    bkron A B (-C) = - bkron A B C := by
  rw [bkron, bkron, ← neg_one_smul ℂ C, Matrix.kronecker_smul,
    Matrix.kronecker_smul, neg_one_smul]

/-- Abbreviation for the 9-qubit matrix action. -/
noncomputable abbrev tel9 (M : Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ)
    (ψ : H9) : H9 :=
  Matrix.toEuclideanLin M ψ

lemma tel9_mul (M N : Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ) (ψ : H9) :
    tel9 (M * N) ψ = tel9 M (tel9 N ψ) := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

lemma tel9_smul (c : ℂ) (M : Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ)
    (ψ : H9) : tel9 (c • M) ψ = c • tel9 M ψ := by
  ext q
  show ((c • M) *ᵥ WithLp.ofLp ψ) q = (c • (M *ᵥ WithLp.ofLp ψ)) q
  rw [Matrix.smul_mulVec]

lemma tel9_one (ψ : H9) : tel9 1 ψ = ψ := by
  ext q
  show ((1 : Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ) *ᵥ WithLp.ofLp ψ) q = ψ q
  rw [Matrix.one_mulVec]

/-- **The generic two-factor combinator**: a Kronecker product acts on a
product vector factor-wise (function level, arbitrary finite index
types). -/
lemma kron_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (f : ι → ℂ) (g : κ → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun q : ι × κ => f q.1 * g q.2)
      = fun q : ι × κ => (A *ᵥ f) q.1 * (B *ᵥ g) q.2 := by
  funext q
  obtain ⟨i, j⟩ := q
  show ∑ x : ι × κ, (A ⊗ₖ B) (i, j) x * (f x.1 * g x.2)
      = (∑ a, A i a * f a) * (∑ b, B j b * g b)
  calc ∑ x : ι × κ, (A ⊗ₖ B) (i, j) x * (f x.1 * g x.2)
      = ∑ x : ι × κ, (A i x.1 * f x.1) * (B j x.2 * g x.2) :=
        Finset.sum_congr rfl fun x _ => by
          rw [Matrix.kroneckerMap_apply]; ring
    _ = ∑ a, ∑ b, (A i a * f a) * (B j b * g b) := Fintype.sum_prod_type _
    _ = (∑ a, A i a * f a) * (∑ b, B j b * g b) := by
        rw [Finset.sum_mul_sum]

/-- The three-factor version, by iterating `kron_mulVec`. -/
lemma kron3_mulVec {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (C : Matrix ν ν ℂ)
    (f : ι → ℂ) (g : κ → ℂ) (h : ν → ℂ) :
    (A ⊗ₖ (B ⊗ₖ C)) *ᵥ (fun q : ι × κ × ν => f q.1 * (g q.2.1 * h q.2.2))
      = fun q : ι × κ × ν =>
          (A *ᵥ f) q.1 * ((B *ᵥ g) q.2.1 * (C *ᵥ h) q.2.2) := by
  have h2 := kron_mulVec B C g h
  have h1 := kron_mulVec A (B ⊗ₖ C) f (fun r : κ × ν => g r.1 * h r.2)
  rw [h2] at h1
  exact h1

/-- ★ **The combinator**: the block Kronecker action factorises through the
block tensor — `(A ⊗ B ⊗ C)(u ⊗ v ⊗ w) = (Au) ⊗ (Bv) ⊗ (Cw)`. The one
lemma that reduces every 512-dimensional statement to 8-dimensional block
facts. -/
theorem tel9_bkron_vkron (A B C : Matrix I3 I3 ℂ) (u v w : H3) :
    tel9 (bkron A B C) (vkron u v w)
      = vkron (Matrix.toEuclideanLin A u) (Matrix.toEuclideanLin B v)
          (Matrix.toEuclideanLin C w) := by
  ext q
  rw [vkron_apply]
  show ((bkron A B C) *ᵥ WithLp.ofLp (vkron u v w)) q
      = (A *ᵥ WithLp.ofLp u) q.1
          * (B *ᵥ WithLp.ofLp v) q.2.1 * (C *ᵥ WithLp.ofLp w) q.2.2
  rw [show WithLp.ofLp (vkron u v w)
      = fun r : I3 × I3 × I3 =>
          WithLp.ofLp u r.1 * (WithLp.ofLp v r.2.1 * WithLp.ofLp w r.2.2) from
    funext fun r => by
      show vkron u v w r = _
      rw [vkron_apply, mul_assoc]]
  rw [show bkron A B C = A ⊗ₖ (B ⊗ₖ C) from rfl, kron3_mulVec]
  show (A *ᵥ WithLp.ofLp u) q.1
      * ((B *ᵥ WithLp.ofLp v) q.2.1 * (C *ᵥ WithLp.ofLp w) q.2.2) = _
  exact (mul_assoc _ _ _).symm

lemma vkron_neg_left (u v w : H3) : vkron (-u) v w = - vkron u v w := by
  ext p; simp

lemma vkron_neg_mid (u v w : H3) : vkron u (-v) w = - vkron u v w := by
  ext p; simp

lemma vkron_neg_right (u v w : H3) : vkron u v (-w) = - vkron u v w := by
  ext p; simp

/-! ### The block-level facts (8-dimensional, `fin_cases`-viable) -/

/-- The block states `B± = |000⟩ ± |111⟩`: the bit-flip code's encodings of
`|±⟩`. `Bp = logical 1 1`. -/
noncomputable def Bp : H3 := logical 1 1

/-- `Bm = logical 1 (−1)`. -/
noncomputable def Bm : H3 := logical 1 (-1)

/-- The all-block bit flip `X^{⊗3} = X₁X₂X₃` — the outer code's stabiliser
factor on one block. -/
def Xall : Matrix I3 I3 ℂ := kron3 pX pX pX

@[simp] lemma Xall_mul_Xall : Xall * Xall = 1 := by
  rw [Xall, kron3_mul, pX_mul_pX]
  simp only [kron3, Matrix.one_kronecker_one]

/-- `X^{⊗3}` swaps `|000⟩ ↔ |111⟩`: on the logical block it exchanges the
coefficients. -/
lemma tel_Xall_logical (a b : ℂ) :
    Matrix.toEuclideanLin Xall (logical a b) = logical b a := by
  ext i
  simp only [Matrix.toLpLin_apply, logical, Xall, kron3, pX]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Prod.ext_iff]

/-- `B₊` is a `+1` eigenstate of `X^{⊗3}`. -/
lemma tel_Xall_Bp : Matrix.toEuclideanLin Xall Bp = Bp :=
  tel_Xall_logical 1 1

/-- `B₋` is a `−1` eigenstate of `X^{⊗3}`. -/
lemma tel_Xall_Bm : Matrix.toEuclideanLin Xall Bm = - Bm := by
  rw [Bm, tel_Xall_logical]
  ext i
  simp only [logical, PiLp.neg_apply, PiLp.add_apply]
  fin_cases i <;> simp [EuclideanSpace.single, Prod.ext_iff]

/-- The inner-position phase flips (`PhaseFlip.lean`'s `Z₁, Z₂, Z₃`), as a
`Fin 3`-indexed family. -/
def Zin : Fin 3 → Matrix I3 I3 ℂ
  | 0 => Z1
  | 1 => Z2
  | 2 => Z3

/-- The inner-position bit flips (`ThreeQubit.lean`'s `X₁, X₂, X₃`), as a
`Fin 3`-indexed family. -/
def Xin : Fin 3 → Matrix I3 I3 ℂ
  | 0 => X1
  | 1 => X2
  | 2 => X3

@[simp] lemma Xin_mul_self (j : Fin 3) : Xin j * Xin j = 1 := by
  fin_cases j <;> simp [Xin]

/-- **The block phase-flip action**: every single `Z` inside a block flips
the sign of the `|111⟩` component — `Z_j (a|000⟩ + b|111⟩) = a|000⟩ − b|111⟩`,
the *same* action for all three positions `j`. The germ of the code's
degeneracy. -/
lemma tel_Zin_logical (j : Fin 3) (a b : ℂ) :
    Matrix.toEuclideanLin (Zin j) (logical a b) = logical a (-b) := by
  fin_cases j <;>
  · ext i
    simp only [Zin, Matrix.toLpLin_apply, logical, Z1, Z2, Z3, kron3, pZ]
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
        EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.one_apply,
        Prod.ext_iff]

/-- **Block-level degeneracy**: `Z₁ Z_j` fixes the logical block for every
`j` — the two sign flips cancel, so recovering with `Z₁` corrects a `Z`
error at *any* inner position. -/
lemma tel_Z1_Zin_logical (j : Fin 3) (a b : ℂ) :
    Matrix.toEuclideanLin Z1 (Matrix.toEuclideanLin (Zin j) (logical a b))
      = logical a b := by
  rw [tel_Zin_logical, show (Z1 : Matrix I3 I3 ℂ) = Zin 0 from rfl,
    tel_Zin_logical, neg_neg]

/-! ### The 9-qubit operators: placement and the code space -/

/-- Place a block operator in slot `s` (identity on the other blocks). -/
def place : Fin 3 → Matrix I3 I3 ℂ → Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ
  | 0, M => bkron M 1 1
  | 1, M => bkron 1 M 1
  | 2, M => bkron 1 1 M

lemma place_mul (s : Fin 3) (M N : Matrix I3 I3 ℂ) :
    place s M * place s N = place s (M * N) := by
  fin_cases s <;> simp [place, bkron_mul]

@[simp] lemma place_one (s : Fin 3) : place s 1 = 1 := by
  fin_cases s <;> simp [place]

lemma place_smul (s : Fin 3) (c : ℂ) (M : Matrix I3 I3 ℂ) :
    place s (c • M) = c • place s M := by
  fin_cases s <;>
    simp only [place, bkron, Matrix.smul_kronecker, Matrix.kronecker_smul]

/-- The Shor logical state
`a·(B₊ ⊗ B₊ ⊗ B₊) + b·(B₋ ⊗ B₋ ⊗ B₋)` (unnormalised coefficients). -/
noncomputable def shorLogical (a b : ℂ) : H9 :=
  a • vkron Bp Bp Bp + b • vkron Bm Bm Bm

/-- Block `s`'s stabiliser pair member: `Z₁Z₂` (`t = 0`) or `Z₂Z₃`
(`t = 1`). -/
def innerStabBlock : Fin 2 → Matrix I3 I3 ℂ
  | 0 => Z1Z2
  | 1 => Z2Z3

/-- The six inner stabilisers: block `s`'s pair, chosen by `t`. -/
def innerStab (s : Fin 3) (t : Fin 2) :
    Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ :=
  place s (innerStabBlock t)

/-- The two outer stabilisers: `X^{⊗6}` on blocks 1–2 (`t = 0`) and 2–3
(`t = 1`). -/
def outerStab : Fin 2 → Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ
  | 0 => bkron Xall Xall 1
  | 1 => bkron 1 Xall Xall

/-- The single-qubit bit-flip error at inner position `j` of block `s`. -/
def errX (s j : Fin 3) : Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ :=
  place s (Xin j)

/-- The single-qubit phase-flip error at inner position `j` of block `s`. -/
def errZ (s j : Fin 3) : Matrix (I3 × I3 × I3) (I3 × I3 × I3) ℂ :=
  place s (Zin j)

/-! ### The codespace: all eight stabilisers fix the logical state -/

/-- The six inner stabilisers fix `shorLogical`: within each block the
bit-flip code's stabilisers fix both `B₊` and `B₋` (they are `logical`
instances). -/
theorem innerStab_fixes_shorLogical (s : Fin 3) (t : Fin 2) (a b : ℂ) :
    tel9 (innerStab s t) (shorLogical a b) = shorLogical a b := by
  have hBp : Matrix.toEuclideanLin (innerStabBlock t) Bp = Bp := by
    fin_cases t <;>
      first
        | exact stab_Z1Z2_fixes_logical 1 1
        | exact stab_Z2Z3_fixes_logical 1 1
  have hBm : Matrix.toEuclideanLin (innerStabBlock t) Bm = Bm := by
    fin_cases t <;>
      first
        | exact stab_Z1Z2_fixes_logical 1 (-1)
        | exact stab_Z2Z3_fixes_logical 1 (-1)
  rw [innerStab]
  fin_cases s <;>
    simp only [place, shorLogical, map_add, map_smul, tel9_bkron_vkron,
      tel_one, hBp, hBm]

/-- The two outer stabilisers fix `shorLogical`: `B₊` is a `+1` eigenstate
of `X^{⊗3}` and `B₋` a `−1` eigenstate, and each outer stabiliser touches
exactly two blocks, so the signs cancel. -/
theorem outerStab_fixes_shorLogical (t : Fin 2) (a b : ℂ) :
    tel9 (outerStab t) (shorLogical a b) = shorLogical a b := by
  fin_cases t <;>
    simp only [outerStab, shorLogical, map_add, map_smul, tel9_bkron_vkron,
      tel_one, tel_Xall_Bp, tel_Xall_Bm, vkron_neg_left, vkron_neg_mid,
      vkron_neg_right, neg_neg]

/-! ### Syndromes: the eigenvalue table -/

/-- The bit-flip syndrome signs: position `j` against the stabiliser pair,
exactly the 3-qubit code's table `(−,+), (−,−), (+,−)`. -/
def xSyndromeSign : Fin 3 → Fin 2 → ℂ
  | 0, 0 => -1
  | 0, 1 => 1
  | 1, 0 => -1
  | 1, 1 => -1
  | 2, 0 => 1
  | 2, 1 => -1

/-- The phase-flip block-syndrome signs: block `s` against the outer pair —
the same mirror table `(−,+), (−,−), (+,−)`, now reading the *block*. -/
def zSyndromeSign : Fin 3 → Fin 2 → ℂ := xSyndromeSign

/-- The bit-flip syndrome pattern is injective: the pair of inner readings
identifies the position within the block. (The 3-qubit
`three_qubit_syndromes_distinct`, at the level of the sign table.) -/
theorem xSyndromeSign_injective : Function.Injective xSyndromeSign := by
  intro j k h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases j <;> fin_cases k <;>
    first
      | rfl
      | (exfalso; revert h0 h1; norm_num [xSyndromeSign])

/-- The phase-flip block-syndrome pattern is injective: the pair of outer
readings identifies the block. -/
theorem zSyndromeSign_injective : Function.Injective zSyndromeSign :=
  xSyndromeSign_injective

/-- ★ **Bit-flip syndrome, same block**: an `X` error at position `j` of
block `s` makes the errored state an eigenstate of block `s`'s stabiliser
pair with the 3-qubit sign pattern `xSyndromeSign j`. -/
theorem innerStab_syndrome_X (s j : Fin 3) (t : Fin 2) (a b : ℂ) :
    tel9 (innerStab s t) (tel9 (errX s j) (shorLogical a b))
      = xSyndromeSign j t • tel9 (errX s j) (shorLogical a b) := by
  have hkey : innerStabBlock t * Xin j
      = xSyndromeSign j t • (Xin j * innerStabBlock t) := by
    fin_cases j <;> fin_cases t <;>
      simp only [Xin, innerStabBlock, xSyndromeSign, neg_smul, one_smul] <;>
      first
        | exact Z1Z2_anticomm_X1
        | exact Z1Z2_anticomm_X2
        | exact Z1Z2_comm_X3
        | exact Z2Z3_comm_X1
        | exact Z2Z3_anticomm_X2
        | exact Z2Z3_anticomm_X3
  have hfix := innerStab_fixes_shorLogical s t a b
  rw [innerStab] at hfix
  rw [← tel9_mul, innerStab, errX, place_mul, hkey, place_smul, tel9_smul,
    ← place_mul, tel9_mul, hfix]

/-- **Bit flips are invisible to the other blocks' stabilisers**: the inner
pair of any block `s' ≠ s` still reads `+1`. -/
theorem innerStab_fixes_X_other {s s' : Fin 3} (hss : s' ≠ s) (j : Fin 3)
    (t : Fin 2) (a b : ℂ) :
    tel9 (innerStab s' t) (tel9 (errX s j) (shorLogical a b))
      = tel9 (errX s j) (shorLogical a b) := by
  rw [← tel9_mul]
  have hcomm : innerStab s' t * errX s j = errX s j * innerStab s' t := by
    rw [innerStab, errX]
    fin_cases s <;> fin_cases s' <;>
      first
        | exact absurd rfl hss
        | simp [place, bkron_mul]
  rw [hcomm, tel9_mul, innerStab_fixes_shorLogical]

/-- **Bit flips are invisible to the outer stabilisers**: `X` commutes with
`X^{⊗6}`, so both outer readings stay `+1`. -/
theorem outerStab_fixes_X (s j : Fin 3) (t : Fin 2) (a b : ℂ) :
    tel9 (outerStab t) (tel9 (errX s j) (shorLogical a b))
      = tel9 (errX s j) (shorLogical a b) := by
  have hXcomm : Xall * Xin j = Xin j * Xall := by
    fin_cases j <;>
      simp only [Xin, Xall, X1, X2, X3, kron3_mul, pX_mul_pX, one_mul, mul_one]
  rw [← tel9_mul]
  have hcomm : outerStab t * errX s j = errX s j * outerStab t := by
    rw [errX]
    fin_cases t <;> fin_cases s <;>
      simp [outerStab, place, bkron_mul, hXcomm]
  rw [hcomm, tel9_mul, outerStab_fixes_shorLogical]

/-- The block-level anticommutation behind the phase-flip syndrome:
`X^{⊗3}` anticommutes with every single `Z` in the block. -/
lemma Xall_anticomm_Zin (j : Fin 3) : Xall * Zin j = - (Zin j * Xall) := by
  fin_cases j
  · show Xall * Zin 0 = - (Zin 0 * Xall)
    rw [show Xall * Zin 0 = kron3 (pX * pZ) pX pX from by
        rw [Xall, Zin, Z1, kron3_mul, mul_one],
      show Zin 0 * Xall = kron3 (pZ * pX) pX pX from by
        rw [Xall, Zin, Z1, kron3_mul, one_mul],
      pX_mul_pZ, kron3_neg_left]
  · show Xall * Zin 1 = - (Zin 1 * Xall)
    rw [show Xall * Zin 1 = kron3 pX (pX * pZ) pX from by
        rw [Xall, Zin, Z2, kron3_mul, mul_one],
      show Zin 1 * Xall = kron3 pX (pZ * pX) pX from by
        rw [Xall, Zin, Z2, kron3_mul, one_mul],
      pX_mul_pZ, kron3_neg_mid]
  · show Xall * Zin 2 = - (Zin 2 * Xall)
    rw [show Xall * Zin 2 = kron3 pX pX (pX * pZ) from by
        rw [Xall, Zin, Z3, kron3_mul, mul_one],
      show Zin 2 * Xall = kron3 pX pX (pZ * pX) from by
        rw [Xall, Zin, Z3, kron3_mul, one_mul],
      pX_mul_pZ, kron3_neg_right]

/-- ★ **Phase-flip syndrome, degenerate**: a `Z` error at *any* inner
position `j` of block `s` makes the errored state an eigenstate of the
outer pair with the block pattern `zSyndromeSign s` — the reading depends
only on the block, never on `j`. -/
theorem outerStab_syndrome_Z (s j : Fin 3) (t : Fin 2) (a b : ℂ) :
    tel9 (outerStab t) (tel9 (errZ s j) (shorLogical a b))
      = zSyndromeSign s t • tel9 (errZ s j) (shorLogical a b) := by
  have hkey : outerStab t * errZ s j
      = zSyndromeSign s t • (errZ s j * outerStab t) := by
    rw [errZ]
    fin_cases s <;> fin_cases t <;>
      simp only [outerStab, place, bkron_mul, zSyndromeSign, xSyndromeSign,
        one_mul, mul_one, neg_smul, one_smul] <;>
      first
        | rfl
        | rw [Xall_anticomm_Zin, bkron_neg_left]
        | rw [Xall_anticomm_Zin, bkron_neg_mid]
        | rw [Xall_anticomm_Zin, bkron_neg_right]
  rw [← tel9_mul, hkey, tel9_smul, tel9_mul, outerStab_fixes_shorLogical]

/-- **Phase flips are invisible to every inner stabiliser**: `Z`'s commute,
so all six inner readings stay `+1`. -/
theorem innerStab_fixes_Z (s' s j : Fin 3) (t : Fin 2) (a b : ℂ) :
    tel9 (innerStab s' t) (tel9 (errZ s j) (shorLogical a b))
      = tel9 (errZ s j) (shorLogical a b) := by
  have hZcomm : innerStabBlock t * Zin j = Zin j * innerStabBlock t := by
    fin_cases t <;> fin_cases j <;>
      simp only [Zin, innerStabBlock, Z1Z2, Z2Z3, Z1, Z2, Z3, kron3_mul,
        one_mul, mul_one]
  rw [← tel9_mul]
  have hcomm : innerStab s' t * errZ s j = errZ s j * innerStab s' t := by
    rw [innerStab, errZ]
    fin_cases s <;> fin_cases s' <;> simp [place, bkron_mul, hZcomm]
  rw [hcomm, tel9_mul, innerStab_fixes_shorLogical]

/-! ### Corrections: the headline theorems -/

/-- ★★ **Bit-flip correction at every position**: re-applying the
syndrome-identified `X` restores the Shor logical state exactly. -/
theorem shor_corrects_X (s j : Fin 3) (a b : ℂ) :
    tel9 (errX s j) (tel9 (errX s j) (shorLogical a b)) = shorLogical a b := by
  rw [← tel9_mul, errX, place_mul, Xin_mul_self, place_one, tel9_one]

/-- The recovery core: `Z₁·Z_j` placed in any slot fixes the logical
state — the block degeneracy, lifted. -/
lemma tel9_place_Z1_Zin (s j : Fin 3) (a b : ℂ) :
    tel9 (place s (Z1 * Zin j)) (shorLogical a b) = shorLogical a b := by
  have hBp : Matrix.toEuclideanLin (Z1 * Zin j) Bp = Bp := by
    rw [tel_mul, Bp, tel_Z1_Zin_logical]
  have hBm : Matrix.toEuclideanLin (Z1 * Zin j) Bm = Bm := by
    rw [tel_mul, Bm, tel_Z1_Zin_logical]
  fin_cases s <;>
    simp only [place, shorLogical, map_add, map_smul, tel9_bkron_vkron,
      tel_one, hBp, hBm]

/-- ★★ **Degenerate phase-flip correction**: applying `Z` to the *first*
qubit of the syndrome-identified block restores the state **whichever**
inner qubit was hit — the outer syndrome cannot see `j`, and thanks to the
code's degeneracy the recovery does not need to. -/
theorem shor_corrects_Z_degenerate (s j : Fin 3) (a b : ℂ) :
    tel9 (place s Z1) (tel9 (errZ s j) (shorLogical a b))
      = shorLogical a b := by
  rw [← tel9_mul, errZ, place_mul]
  exact tel9_place_Z1_Zin s j a b

/-- ★★ **Composite (`XZ`, i.e. `Y` up to phase) correction**: the two
recoveries compose — apply the identified `X`, then the block's `Z₁`. With
`pauli_decomposition` this completes the discretised single-error set
`{I, X, Z, XZ}` at every one of the nine positions. -/
theorem shor_corrects_XZ (s j : Fin 3) (a b : ℂ) :
    tel9 (place s Z1) (tel9 (errX s j)
        (tel9 (errX s j * errZ s j) (shorLogical a b)))
      = shorLogical a b := by
  rw [← tel9_mul, ← tel9_mul, errX, errZ, place_mul, place_mul, place_mul,
    show Z1 * Xin j * (Xin j * Zin j) = Z1 * Zin j from by
      rw [mul_assoc Z1 (Xin j), ← mul_assoc (Xin j) (Xin j), Xin_mul_self,
        one_mul]]
  exact tel9_place_Z1_Zin s j a b

end QEC
end QM
end Empirical
end CSD

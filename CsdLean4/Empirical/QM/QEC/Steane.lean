/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Stabilizer

/-!
# The Steane seven-qubit code as a stabiliser family (CSS from Hamming [7,4])

**Category:** 3-Local (QM-validity).

**Glossary:** https://glossary.constraintsurfacedynamics.com/steane-code/
Plain-language, CSD-role and formal statements of the Steane code, with this module as its
Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

The Steane `[[7,1,3]]` code, built as the first genuine **CSS instance** of the Cat-1
stabiliser layer (`Mathlib/QuantumInfo/Stabilizer.lean`, GK-3; plan `specs/steane-plan.md`):
the parity-check rows of the classical Hamming `[7,4]` code give three `X`-type and three
`Z`-type stabiliser generators, and the CSS condition — every row orthogonal to every row,
`H Hᵀ = 0` over `𝔽₂` — makes the trivial sign function coherent, so the whole GK-3 layer
instantiates:

* `steane_code_dimension` — the stabiliser-family trace is `2⁷/2⁶ = 2`: a **one-logical-qubit**
  code space, by the general `stabProjector_trace`.
* ★ **The logical states**: `steaneZero ∝ ∑_{c ∈ C₂} |c⟩` (the row space of `H`) and
  `steaneOne ∝ ∑_{c ∈ C₂} |c + 1⃗⟩`, each **stabilised by all sixty-four group elements**
  (`steaneZero_stabilised`/`steaneOne_stabilised`), and **orthonormal**
  (`inner_steaneZero_steaneOne`, `inner_steaneZero_self`, `inner_steaneOne_self`) — the
  two-dimensional code space exhibited concretely, matching the trace count.
* ★ **The logical operators**: `X̄ = X^{1⃗}` swaps the logical states
  (`logicalX_steaneZero`/`logicalX_steaneOne`), `Z̄ = Z^{1⃗}` fixes `|0̄⟩` and negates `|1̄⟩`
  (`logicalZ_steaneZero`/`logicalZ_steaneOne`) — a genuine encoded qubit.
* ★ **The distance mechanism**: single-qubit errors have **nonzero, pairwise-distinct
  syndromes** (`steane_syndrome_single_ne_zero`, `steane_syndrome_single_injective`) — the
  classical Hamming distance-3 property, which via `pauliOp_comm` (the symplectic
  commutation criterion) is exactly the statement that every single-qubit `X`- or `Z`-error
  anticommutes with a generator identified by its syndrome. Both error types use the same
  matrix: the code is CSS-self-dual.

**Honest scope.** The code space is exhibited (two orthonormal stabilised states) and the
error-detection mechanism is stated in syndrome form; the full recovery map, the
Knill–Laflamme conditions, and fault-tolerance claims are not attempted — the same posture
as the three-qubit modules. The `𝔽₂` facts about the concrete Hamming rows (orthogonality,
independence, column distinctness) are closed by `decide` — kernel-checked finite
computation, the right tool for a fixed `7 × 3` matrix.
-/

@[expose] public section

open scoped ComplexConjugate
open QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-- The parity-check rows of the Hamming `[7,4]` code: column `j` is the binary expansion of
`j + 1`. -/
def hammingRow : Fin 3 → Fin 7 → Fin 2 :=
  ![![1, 0, 1, 0, 1, 0, 1], ![0, 1, 1, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 1, 1]]

/-- An `𝔽₂` combination of the Hamming rows — the row space `C₂` (eight elements), the
support of the logical states. -/
def rowComb (c : Fin 3 → Fin 2) : Fin 7 → Fin 2 :=
  fun j => ∑ i, c i * hammingRow i j

/-- The all-ones vector: the logical-`X`/`Z` label, a Hamming codeword outside the row
space. -/
def allOnes : Fin 7 → Fin 2 := fun _ => 1

/-- The `X`-labels of the stabiliser family: the first three bits of `x` combine the rows. -/
def steaneA (x : Fin 6 → Fin 2) : Fin 7 → Fin 2 :=
  rowComb fun i => x (Fin.castAdd 3 i)

/-- The `Z`-labels: the last three bits of `x` combine the rows. -/
def steaneB (x : Fin 6 → Fin 2) : Fin 7 → Fin 2 :=
  rowComb fun i => x (Fin.natAdd 3 i)

/-! ## The `𝔽₂` facts about the Hamming rows (kernel-checked) -/

/-- Row combinations are additive. -/
lemma rowComb_add (c d : Fin 3 → Fin 2) : rowComb (c + d) = rowComb c + rowComb d := by
  funext j
  rw [Pi.add_apply, rowComb, rowComb, rowComb, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply]
  exact (by decide : ∀ x y w : Fin 2, (x + y) * w = x * w + y * w) _ _ _

/-- **The CSS condition:** every row combination is orthogonal to every row combination
(`H Hᵀ = 0` over `𝔽₂`). -/
lemma bdot_rowComb_rowComb (c d : Fin 3 → Fin 2) : bdot (rowComb c) (rowComb d) = 0 := by
  revert c d
  decide

/-- Every row combination is orthogonal to the all-ones vector (rows have even weight). -/
lemma bdot_rowComb_allOnes (c : Fin 3 → Fin 2) : bdot (rowComb c) allOnes = 0 := by
  revert c
  decide

/-- The all-ones vector pairs to `1` with itself (seven is odd). -/
lemma bdot_allOnes_allOnes : bdot allOnes allOnes = 1 := by decide

/-- The rows are independent: only the trivial combination vanishes. -/
lemma rowComb_eq_zero (c : Fin 3 → Fin 2) (h : rowComb c = 0) : c = 0 := by
  revert c
  decide

/-- The all-ones vector is not in the row space: the two logical supports are disjoint
cosets. -/
lemma rowComb_ne_allOnes (c : Fin 3 → Fin 2) : rowComb c ≠ allOnes := by
  revert c
  decide

/-- The row-combination map is injective (the eight support strings are distinct). -/
lemma rowComb_injective (c d : Fin 3 → Fin 2) (h : rowComb c = rowComb d) : c = d := by
  revert c d
  decide

/-! ## The stabiliser-family axioms, and the GK-3 instantiation -/

lemma steaneA_add (x y : Fin 6 → Fin 2) : steaneA (x + y) = steaneA x + steaneA y := by
  rw [steaneA, steaneA, steaneA, ← rowComb_add]
  congr 1

lemma steaneB_add (x y : Fin 6 → Fin 2) : steaneB (x + y) = steaneB x + steaneB y := by
  rw [steaneB, steaneB, steaneB, ← rowComb_add]
  congr 1

/-- The trivial sign function is coherent: the CSS condition kills the pairing. -/
lemma steane_sigma_coherent (x y : Fin 6 → Fin 2) :
    (fun _ : Fin 6 → Fin 2 => (0 : Fin 2)) (x + y)
      = (fun _ : Fin 6 → Fin 2 => (0 : Fin 2)) x
        + (fun _ : Fin 6 → Fin 2 => (0 : Fin 2)) y + bdot (steaneB x) (steaneA y) := by
  rw [steaneB, steaneA, bdot_rowComb_rowComb]
  rfl

/-- The six generators are independent. -/
lemma steane_labels_injective (x : Fin 6 → Fin 2) (hA : steaneA x = 0)
    (hB : steaneB x = 0) : x = 0 := by
  have hc := rowComb_eq_zero _ hA
  have hd := rowComb_eq_zero _ hB
  funext i
  rcases Fin.lt_or_ge i 3 with hi | hi
  · have := congrFun hc ⟨i, hi⟩
    rwa [show Fin.castAdd 3 (⟨(i : ℕ), hi⟩ : Fin 3) = i from Fin.ext rfl] at this
  · have hi' : (i : ℕ) - 3 < 3 := by omega
    have := congrFun hd ⟨(i : ℕ) - 3, hi'⟩
    rwa [show Fin.natAdd 3 (⟨(i : ℕ) - 3, hi'⟩ : Fin 3) = i from Fin.ext (by
      simp [Fin.natAdd]
      omega)] at this

/-- **The code space is one logical qubit:** the stabiliser-family trace is `2⁷/2⁶ = 2` —
the general GK-3 dimension count at the Steane labels. -/
theorem steane_code_dimension :
    ∑ z : Fin 7 → Fin 2,
        stabProjector steaneA steaneB (fun _ => 0) (basisState z) z = 2 := by
  rw [stabProjector_trace steaneA_add steaneB_add steane_sigma_coherent
    steane_labels_injective]
  norm_num

/-! ## The logical states -/

/-- The logical zero: the uniform superposition over the row space `C₂`. -/
noncomputable def steaneZero : QReg 7 :=
  (Real.sqrt 8 : ℂ)⁻¹ • ∑ c : Fin 3 → Fin 2, basisState (rowComb c)

/-- The logical one: the uniform superposition over the coset `C₂ + 1⃗`. -/
noncomputable def steaneOne : QReg 7 :=
  (Real.sqrt 8 : ℂ)⁻¹ • ∑ c : Fin 3 → Fin 2, basisState (rowComb c + allOnes)

/-- ★ **The logical zero is stabilised by every element of the sixty-four-element stabiliser
group.** `Z`-type parts act trivially by the CSS orthogonality; `X`-type parts permute the
row space. -/
theorem steaneZero_stabilised (x : Fin 6 → Fin 2) :
    pauliOp (steaneA x) (steaneB x) steaneZero = steaneZero := by
  rw [steaneZero, pauliOp_smul, pauliOp_sum,
    Finset.sum_congr rfl fun c _ => by
      rw [pauliOp_basisState, pauliSign, steaneB, bdot_rowComb_rowComb, signChar_zero,
        one_smul, steaneA, ← rowComb_add]]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight fun i => x (Fin.castAdd 3 i)) _ _ fun c => rfl

/-- ★ **The logical one is stabilised by every element** — the coset shifts through. -/
theorem steaneOne_stabilised (x : Fin 6 → Fin 2) :
    pauliOp (steaneA x) (steaneB x) steaneOne = steaneOne := by
  have hsign : ∀ c : Fin 3 → Fin 2,
      pauliSign (steaneB x) (rowComb c + allOnes) = 1 := by
    intro c
    rw [pauliSign, bdot_add_right, steaneB, bdot_rowComb_rowComb, bdot_rowComb_allOnes,
      add_zero, signChar_zero]
  have harg : ∀ c : Fin 3 → Fin 2,
      rowComb c + allOnes + steaneA x
        = rowComb (c + fun i => x (Fin.castAdd 3 i)) + allOnes := by
    intro c
    rw [rowComb_add, steaneA]
    abel
  rw [steaneOne, pauliOp_smul, pauliOp_sum,
    Finset.sum_congr rfl fun c _ => by
      rw [pauliOp_basisState, hsign c, one_smul, harg c]]
  congr 1
  exact Fintype.sum_equiv (Equiv.addRight fun i => x (Fin.castAdd 3 i)) _ _ fun c => rfl

/-! ## The logical operators: a genuine encoded qubit -/

/-- ★ `X̄ = X^{1⃗}` maps `|0̄⟩` to `|1̄⟩`. -/
theorem logicalX_steaneZero : pauliOp allOnes 0 steaneZero = steaneOne := by
  rw [steaneZero, steaneOne, pauliOp_smul, pauliOp_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pauliOp_basisState, pauliSign, bdot_zero_left, signChar_zero, one_smul]

/-- ★ `X̄` maps `|1̄⟩` back to `|0̄⟩`. -/
theorem logicalX_steaneOne : pauliOp allOnes 0 steaneOne = steaneZero := by
  have hones : allOnes + allOnes = 0 := funext fun i => fin2_add_self _
  rw [steaneOne, steaneZero, pauliOp_smul, pauliOp_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pauliOp_basisState, pauliSign, bdot_zero_left, signChar_zero, one_smul, add_assoc,
    hones, add_zero]

/-- ★ `Z̄ = Z^{1⃗}` fixes `|0̄⟩`. -/
theorem logicalZ_steaneZero : pauliOp 0 allOnes steaneZero = steaneZero := by
  rw [steaneZero, pauliOp_smul, pauliOp_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pauliOp_basisState, pauliSign, bdot_comm, bdot_rowComb_allOnes, signChar_zero,
    one_smul, add_zero]

/-- ★ `Z̄` negates `|1̄⟩`: the encoded qubit's phase degree of freedom is real. -/
theorem logicalZ_steaneOne : pauliOp 0 allOnes steaneOne = -steaneOne := by
  have hsign : ∀ c : Fin 3 → Fin 2,
      pauliSign allOnes (rowComb c + allOnes) = -1 := by
    intro c
    rw [pauliSign, bdot_add_right, bdot_comm allOnes (rowComb c), bdot_rowComb_allOnes,
      bdot_allOnes_allOnes, zero_add]
    rfl
  rw [steaneOne, pauliOp_smul, pauliOp_sum,
    Finset.sum_congr rfl fun c _ => by
      rw [pauliOp_basisState, hsign c, add_zero, neg_one_smul],
    Finset.sum_neg_distrib, smul_neg]

/-! ## Orthogonality: the code space is two-dimensional as exhibited -/

/-- The two logical states are orthogonal: their supports are disjoint cosets. -/
theorem inner_steaneZero_steaneOne : inner ℂ steaneZero steaneOne = 0 := by
  have hdisj : ∀ c d : Fin 3 → Fin 2, rowComb c ≠ rowComb d + allOnes := by
    intro c d h
    apply rowComb_ne_allOnes (c + d)
    rw [rowComb_add]
    have h2 : rowComb d + rowComb c = rowComb d + (rowComb d + allOnes) := by rw [h]
    rw [← add_assoc, show rowComb d + rowComb d = 0 from funext fun i => fin2_add_self _,
      zero_add] at h2
    rw [add_comm (rowComb c) (rowComb d)]
    exact h2
  have hbasis : ∀ c d : Fin 3 → Fin 2,
      inner ℂ (basisState (rowComb c) : QReg 7) (basisState (rowComb d + allOnes)) = 0 := by
    intro c d
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [RCLike.inner_apply', basisState_apply, basisState_apply]
    by_cases hz : z = rowComb c
    · rw [if_pos hz,
        if_neg (fun h : z = rowComb d + allOnes => hdisj c d (by rw [← hz]; exact h)),
        mul_zero]
    · rw [if_neg hz, map_zero, zero_mul]
  rw [steaneZero, steaneOne, inner_smul_left, inner_smul_right, sum_inner,
    Finset.sum_congr rfl fun c _ => by
      rw [inner_sum, Finset.sum_congr rfl fun d _ => hbasis c d, Finset.sum_const_zero],
    Finset.sum_const_zero, mul_zero, mul_zero]

/-- Basis states are orthonormal (local form). -/
lemma inner_basisState (u v : Fin 7 → Fin 2) :
    inner ℂ (basisState u : QReg 7) (basisState v) = if v = u then 1 else 0 := by
  rw [PiLp.inner_apply]
  by_cases huv : v = u
  · subst huv
    rw [if_pos rfl, Finset.sum_eq_single v
      (fun z _ hz => by
        rw [RCLike.inner_apply', basisState_apply, if_neg hz, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h),
      RCLike.inner_apply', basisState_apply, if_pos rfl, map_one, one_mul]
  · rw [if_neg huv]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [RCLike.inner_apply', basisState_apply, basisState_apply]
    by_cases hz : z = u
    · rw [if_neg (fun h : z = v => huv (by rw [← h]; exact hz)), mul_zero]
    · rw [if_neg hz, map_zero, zero_mul]

/-- The normalisation constant: `(1/√8)·(1/√8)·8 = 1`. -/
lemma sqrt_eight_inv_sq :
    (starRingEnd ℂ) ((Real.sqrt 8 : ℂ)⁻¹) * ((Real.sqrt 8 : ℂ)⁻¹ * (8 : ℂ)) = 1 := by
  rw [map_inv₀, Complex.conj_ofReal, ← mul_assoc, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The logical zero is a unit vector: the eight support strings are distinct. -/
theorem inner_steaneZero_self : inner ℂ steaneZero steaneZero = 1 := by
  have hrow : ∀ c : Fin 3 → Fin 2,
      (∑ d : Fin 3 → Fin 2,
        inner ℂ (basisState (rowComb c) : QReg 7) (basisState (rowComb d))) = 1 := by
    intro c
    rw [Finset.sum_congr rfl fun d _ => inner_basisState (rowComb c) (rowComb d),
      Finset.sum_eq_single c
        (fun d _ hd => by rw [if_neg fun h => hd (rowComb_injective d c h)])
        (fun h => absurd (Finset.mem_univ _) h),
      if_pos rfl]
  rw [steaneZero, inner_smul_left, inner_smul_right, sum_inner,
    Finset.sum_congr rfl fun c _ => by rw [inner_sum, hrow c],
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul, mul_one,
    show ((2 ^ 3 : ℕ) : ℂ) = 8 from by norm_num, sqrt_eight_inv_sq]

/-- The logical one is a unit vector: the coset strings are distinct. -/
theorem inner_steaneOne_self : inner ℂ steaneOne steaneOne = 1 := by
  have hinj1 : ∀ c d : Fin 3 → Fin 2,
      rowComb c + allOnes = rowComb d + allOnes → c = d := by
    intro c d h
    apply rowComb_injective
    have h2 : rowComb c + allOnes + allOnes = rowComb d + allOnes + allOnes := by rw [h]
    rwa [add_assoc, add_assoc, show allOnes + allOnes = 0 from
      funext fun i => fin2_add_self _, add_zero, add_zero] at h2
  have hrow : ∀ c : Fin 3 → Fin 2,
      (∑ d : Fin 3 → Fin 2,
        inner ℂ (basisState (rowComb c + allOnes) : QReg 7)
          (basisState (rowComb d + allOnes))) = 1 := by
    intro c
    rw [Finset.sum_congr rfl fun d _ =>
        inner_basisState (rowComb c + allOnes) (rowComb d + allOnes),
      Finset.sum_eq_single c
        (fun d _ hd => by rw [if_neg fun h => hd (hinj1 d c h)])
        (fun h => absurd (Finset.mem_univ _) h),
      if_pos rfl]
  rw [steaneOne, inner_smul_left, inner_smul_right, sum_inner,
    Finset.sum_congr rfl fun c _ => by rw [inner_sum, hrow c],
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul, mul_one,
    show ((2 ^ 3 : ℕ) : ℂ) = 8 from by norm_num, sqrt_eight_inv_sq]

/-! ## The distance mechanism: single-error syndromes -/

/-- The syndrome of an error pattern: its pairing against each Hamming row. Via
`pauliOp_comm`, a nonzero syndrome is exactly anticommutation with the corresponding
generator. -/
def syndrome (e : Fin 7 → Fin 2) : Fin 3 → Fin 2 :=
  fun i => bdot (hammingRow i) e

/-- The single-bit error at position `j`. -/
def unitErr (j : Fin 7) : Fin 7 → Fin 2 :=
  fun i => if i = j then 1 else 0

/-- ★ **Every single-qubit error is detected:** its syndrome is nonzero (every Hamming
column is nonzero). By CSS symmetry the same statement covers both `X`- and `Z`-type
single-qubit errors. -/
theorem steane_syndrome_single_ne_zero (j : Fin 7) : syndrome (unitErr j) ≠ 0 := by
  revert j
  decide

/-- ★ **Distinct single-qubit errors are distinguished:** the seven columns of the Hamming
matrix are pairwise distinct — the distance-3 property that makes single errors
*correctable*, not merely detectable. -/
theorem steane_syndrome_single_injective (j j' : Fin 7)
    (h : syndrome (unitErr j) = syndrome (unitErr j')) : j = j' := by
  revert j j'
  decide

end Steane
end QEC
end QM
end Empirical
end CSD

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.TransversalClifford

/-!
# Syndrome extraction as a circuit

**Category:** 1-Mathlib. Matrix algebra only; nothing here mentions CSD or a particular code.
BACKLOG #94, split out of #62 (c1).

The corpus measures a syndrome as a **projective measurement** on the data register
(`Empirical/QM/QEC/SyndromeRecovery.lean`). A circuit-level fault-tolerance argument needs it as a
**circuit**: an ancilla block prepared in `0`, a ladder of transversal `CNOT`s from data to ancilla,
and a measurement of the ancilla. This file builds that gadget and proves what it does when nothing
fails.

The whole construction is one observation: a `CNOT` ladder from data to ancilla is a **permutation of
basis labels**, `(z, a) ↦ (z, a + H z)` for the check map `H`, so it is `permMat` of
`TransversalClifford.lean` — no amplitudes to track, and the circuit's action on the computational
basis is a relabelling.

## What is proved

* `extractPerm H`, `extractMat H` — the label permutation and its matrix, with
  `extractPerm_involutive`, `extractMat_conjTranspose`, `extractMat_mul_self` and
  ★ `extractMat_mem_unitaryGroup`: the gadget is a self-inverse unitary, exactly as a `CNOT` ladder
  is. Only `H z + H z = 0` is needed — characteristic two, nothing else;
* `ancInit` — the ancilla preparation `z ↦ (z, 0)`, an isometry (`ancInit_conjTranspose_mul`);
* `ancProj s` — the projector reading the ancilla block as `s`, and `synProj H s` the projector on the
  **data** onto `{z | H z = s}`; both are Hermitian idempotents summing to `1`
  (`sum_ancProj`, `sum_synProj`);
* ★★ `extractMat_mul_ancInit_apply` — **extraction tags the data with its syndrome**: the circuit
  sends the basis state `z` with a fresh ancilla to `(z, H z)`, and that single matrix-entry
  computation is the content of the gadget;
* ★★★ `ancProj_mul_extractMat_mul_ancInit` — **extraction returns the syndrome**: reading the ancilla
  as `s` after extraction is *the same operator* as projecting the data onto the syndrome-`s`
  subspace. The circuit implements the projective measurement the corpus had been assuming;
* ★★★ `extractMat_mul_ancInit_mul_synProj_zero` and ★★★ `extractMat_conj_codeState` — **extraction
  leaves a code state alone**: on the syndrome-`0` subspace the circuit acts as the identity, ancilla
  included, so for any operator supported on the code the extracted state is the input with a fresh
  ancilla and nothing else;
* ★★ `ancProj_zero_mul_extractMat_conj_codeState` — and the syndrome-`0` outcome is then **certain**:
  the extracted code state is already in that branch;
* ★ `ancProj_mul_extractMat_mul_ancInit_of_ne` — a syndrome the data does not have has **zero**
  amplitude, which is the statement that the measurement is not merely consistent but exhaustive.

## Honest scope

⚠️ **No faults are modelled.** Every theorem here is about the gadget when nothing fails: this is the
fault-free extraction circuit, and the faulty version — a fault in the ladder or in the ancilla — is
BACKLOG #95 (the verified ancilla) and #96 (the extended rectangle). Nothing here says the gadget is
*fault-tolerant*; it says what it computes.

⚠️ **The ancilla is one unverified block.** `ancInit` prepares the all-zero ancilla and the gadget
reads it; no cat-state preparation, no verification step, and therefore no protection against a single
ancilla fault spreading to the data. That is exactly what #95 is for.

⚠️ **One check map, measured once.** `H` is a single map to the syndrome labels, applied once; nothing
here iterates extraction, interleaves it with gates, or composes rounds. Repeated extraction with
faults is #96's extended rectangle.

⚠️ **`X`-type only, as a relabelling.** The construction works because the ladder permutes
computational-basis labels. A `Z`-type check is the same statement in the conjugate basis and is
**not** derived here; combining both bases for a CSS code is further work.

⚠️ **No decoder.** The syndrome is produced, not interpreted: nothing here maps a syndrome to a
correction, and the recovery maps of the corpus are not re-derived or connected.

## References

`Mathlib/QuantumInfo/TransversalClifford.lean` (`permMat`);
`Empirical/QM/QEC/SyndromeRecovery.lean` (the projective-measurement form this replaces with a
circuit); `specs/BACKLOG.md` #94, #95, #96, #62; `specs/future-work.md`.
-/

@[expose] public section

namespace QuantumInfo

open Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [AddCommGroup β]

/-! ### The extraction gadget -/

/-- **The label permutation a `CNOT` ladder performs**: the data is untouched and the ancilla block
is shifted by the data's check value. -/
def extractPerm (H : α → β) (p : α × β) : α × β := (p.1, p.2 + H p.1)

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] theorem extractPerm_fst (H : α → β) (p : α × β) : (extractPerm H p).1 = p.1 := rfl

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] theorem extractPerm_snd (H : α → β) (p : α × β) :
    (extractPerm H p).2 = p.2 + H p.1 := rfl

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- The ladder is an involution — the only arithmetic the gadget needs is characteristic two. -/
theorem extractPerm_involutive {H : α → β} (hH : ∀ z, H z + H z = 0) :
    Function.Involutive (extractPerm H) := by
  intro p
  refine Prod.ext rfl ?_
  simp only [extractPerm]
  rw [add_assoc, hH, add_zero]

/-- **The extraction circuit**: the transversal `CNOT` ladder from data to ancilla, as the matrix of
its basis relabelling. -/
noncomputable def extractMat (H : α → β) : Matrix (α × β) (α × β) ℂ := permMat (extractPerm H)

omit [Fintype α] [Fintype β] in
theorem extractMat_apply (H : α → β) (p q : α × β) :
    extractMat H p q = if p = extractPerm H q then 1 else 0 := rfl

omit [Fintype α] [Fintype β] in
theorem extractMat_conjTranspose {H : α → β} (hH : ∀ z, H z + H z = 0) :
    (extractMat H)ᴴ = extractMat H :=
  permMat_conjTranspose (extractPerm_involutive hH)

theorem extractMat_mul_self {H : α → β} (hH : ∀ z, H z + H z = 0) :
    extractMat H * extractMat H = 1 :=
  permMat_mul_self (extractPerm_involutive hH)

/-- ★ The gadget is unitary, as a `CNOT` ladder must be. -/
theorem extractMat_mem_unitaryGroup {H : α → β} (hH : ∀ z, H z + H z = 0) :
    extractMat H ∈ Matrix.unitaryGroup (α × β) ℂ :=
  permMat_mem_unitaryGroup (extractPerm_involutive hH)

/-! ### The ancilla block: preparation and readout -/

/-- **The ancilla preparation**: adjoin a fresh ancilla block in the all-zero state. -/
def ancInit : Matrix (α × β) α ℂ := Matrix.of fun p z => if p = (z, 0) then 1 else 0

omit [Fintype α] [Fintype β] in
theorem ancInit_apply (p : α × β) (z : α) :
    (ancInit : Matrix (α × β) α ℂ) p z = if p = (z, 0) then 1 else 0 := rfl

/-- Preparing an ancilla is an isometry. -/
theorem ancInit_conjTranspose_mul :
    (ancInit : Matrix (α × β) α ℂ)ᴴ * ancInit = (1 : Matrix α α ℂ) := by
  ext z w
  rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (w, (0 : β))]
  · by_cases h : z = w
    · subst h
      simp [Matrix.conjTranspose_apply, ancInit_apply]
    · simp [Matrix.conjTranspose_apply, ancInit_apply, h, Ne.symm h]
  · intro p _ hp
    simp [Matrix.conjTranspose_apply, ancInit_apply, hp]
  · intro h
    exact absurd (Finset.mem_univ ((w, (0 : β)))) h

/-- **The ancilla readout**: the projector onto the ancilla block reading `s`. -/
def ancProj (s : β) : Matrix (α × β) (α × β) ℂ :=
  Matrix.diagonal fun p => if p.2 = s then 1 else 0

/-- **The syndrome projector on the data**: the projector onto `{z | H z = s}`, which is what the
corpus's projective-measurement form of the syndrome is. -/
def synProj (H : α → β) (s : β) : Matrix α α ℂ :=
  Matrix.diagonal fun z => if H z = s then 1 else 0

omit [Fintype α] [Fintype β] in
omit [AddCommGroup β] in
theorem ancProj_conjTranspose (s : β) : (ancProj (α := α) s)ᴴ = ancProj s := by
  rw [ancProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p.2 = s <;> simp [h]

omit [Fintype α] [Fintype β] [AddCommGroup β] in
theorem synProj_conjTranspose (H : α → β) (s : β) : (synProj H s)ᴴ = synProj H s := by
  rw [synProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext z
  by_cases h : H z = s <;> simp [h]

omit [AddCommGroup β] in
theorem ancProj_mul_self (s : β) : ancProj (α := α) s * ancProj s = ancProj s := by
  rw [ancProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases h : p.2 = s <;> simp [h]

omit [Fintype β] [AddCommGroup β] in
theorem synProj_mul_self (H : α → β) (s : β) : synProj H s * synProj H s = synProj H s := by
  rw [synProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext z
  by_cases h : H z = s <;> simp [h]

omit [Fintype α] [AddCommGroup β] in
theorem sum_ancProj : ∑ s : β, ancProj (α := α) s = 1 := by
  ext p q
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [ancProj, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    simp
  · simp [h]

omit [Fintype α] [AddCommGroup β] in
theorem sum_synProj (H : α → β) : ∑ s : β, synProj H s = 1 := by
  ext z w
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [synProj, Matrix.diagonal_apply]
  by_cases h : z = w
  · subst h
    simp
  · simp [h]

/-! ### What the gadget computes -/

/-- ★★ **Extraction tags the data with its syndrome.** The circuit takes the basis state `z` with a
fresh ancilla to `(z, H z)`: one matrix entry, and the whole content of the gadget. -/
theorem extractMat_mul_ancInit_apply {H : α → β} (hH : ∀ z, H z + H z = 0) (p : α × β) (z : α) :
    (extractMat H * (ancInit : Matrix (α × β) α ℂ)) p z = if p = (z, H z) then 1 else 0 := by
  rw [extractMat, permMat_mul_apply (extractPerm_involutive hH), ancInit_apply]
  by_cases h : p = (z, H z)
  · subst h
    rw [if_pos rfl, if_pos]
    refine Prod.ext rfl ?_
    simp only [extractPerm]
    rw [hH]
  · rw [if_neg h, if_neg]
    intro hc
    have h1 : p.1 = z := by simpa using congrArg Prod.fst hc
    have h2 : p.2 + H p.1 = 0 := by simpa using congrArg Prod.snd hc
    have h3 : p.2 + H z = 0 := by rw [← h1]; exact h2
    refine h (Prod.ext h1 ?_)
    show p.2 = H z
    calc p.2 = p.2 + (H z + H z) := by rw [hH z, add_zero]
      _ = p.2 + H z + H z := by rw [add_assoc]
      _ = H z := by rw [h3, zero_add]

/-- ★★★ **Extraction returns the syndrome.** Reading the ancilla block as `s` after extraction is the
same operator as projecting the **data** onto the syndrome-`s` subspace: the circuit implements the
projective measurement that the corpus's `SyndromeRecovery.lean` form of the syndrome assumes. -/
theorem ancProj_mul_extractMat_mul_ancInit {H : α → β} (hH : ∀ z, H z + H z = 0) (s : β) :
    ancProj (α := α) s * (extractMat H * (ancInit : Matrix (α × β) α ℂ))
      = (extractMat H * (ancInit : Matrix (α × β) α ℂ)) * synProj H s := by
  ext p z
  rw [ancProj, Matrix.diagonal_mul, synProj, Matrix.mul_diagonal,
    extractMat_mul_ancInit_apply hH]
  by_cases hz : H z = s
  · subst hz
    by_cases h : p = (z, H z)
    · subst h; simp
    · simp [h]
  · rw [if_neg hz, mul_zero]
    by_cases h : p = (z, H z)
    · subst h
      rw [if_neg hz, zero_mul]
    · rw [if_neg h, mul_zero]

/-- ★ **A syndrome the data does not carry gets zero amplitude.** The measurement is exhaustive, not
merely consistent. -/
theorem ancProj_mul_extractMat_mul_ancInit_of_ne {H : α → β} (hH : ∀ z, H z + H z = 0) {s : β}
    (p : α × β) (z : α) (hz : H z ≠ s) :
    (ancProj (α := α) s * (extractMat H * (ancInit : Matrix (α × β) α ℂ))) p z = 0 := by
  rw [ancProj_mul_extractMat_mul_ancInit hH, synProj, Matrix.mul_diagonal, if_neg hz, mul_zero]

/-- The prepared ancilla is already in the `0` branch. -/
theorem ancProj_zero_mul_ancInit :
    ancProj (α := α) (0 : β) * ancInit = ancInit := by
  ext p z
  rw [ancProj, Matrix.diagonal_mul, ancInit_apply]
  by_cases h : p = (z, 0)
  · subst h; simp
  · simp [h]

/-- ★★★ **On the code, extraction does nothing.** Restricted to the syndrome-`0` subspace the circuit
acts as the identity — the ancilla comes back to `0` and the data is untouched — so "extraction leaves
a code state alone" is an operator identity, not a statement about a particular state. -/
theorem extractMat_mul_ancInit_mul_synProj_zero {H : α → β} (hH : ∀ z, H z + H z = 0) :
    extractMat H * (ancInit : Matrix (α × β) α ℂ) * synProj H (0 : β)
      = (ancInit : Matrix (α × β) α ℂ) * synProj H (0 : β) := by
  ext p z
  rw [synProj, Matrix.mul_diagonal, Matrix.mul_diagonal, extractMat_mul_ancInit_apply hH,
    ancInit_apply]
  by_cases hz : H z = 0
  · rw [hz]
  · rw [if_neg hz, mul_zero, mul_zero]

/-- ★★★ **A code state is returned unchanged, ancilla included.** For any operator supported on the
syndrome-`0` subspace, extraction conjugates it to itself with a fresh ancilla. -/
theorem extractMat_conj_codeState {H : α → β} (hH : ∀ z, H z + H z = 0)
    {ρ : Matrix α α ℂ} (hρ : synProj H (0 : β) * ρ * synProj H (0 : β) = ρ) :
    extractMat H * ((ancInit : Matrix (α × β) α ℂ) * ρ * ancInitᴴ) * (extractMat H)ᴴ
      = (ancInit : Matrix (α × β) α ℂ) * ρ * ancInitᴴ := by
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (α × β) α ℂ,
      A = (ancInit : Matrix (α × β) α ℂ) * synProj H (0 : β) := ⟨_, rfl⟩
  have hEA : extractMat H * A = A := by
    rw [hAdef, ← Matrix.mul_assoc]
    exact extractMat_mul_ancInit_mul_synProj_zero hH
  have hAH : Aᴴ * extractMat H = Aᴴ := by
    rw [← extractMat_conjTranspose hH, ← Matrix.conjTranspose_mul, hEA]
  have hX : A * ρ * Aᴴ = (ancInit : Matrix (α × β) α ℂ) * ρ * ancInitᴴ := by
    rw [hAdef, Matrix.conjTranspose_mul, synProj_conjTranspose]
    calc (ancInit : Matrix (α × β) α ℂ) * synProj H (0 : β) * ρ
            * (synProj H (0 : β) * ancInitᴴ)
        = (ancInit : Matrix (α × β) α ℂ)
            * (synProj H (0 : β) * ρ * synProj H (0 : β)) * ancInitᴴ := by
          simp only [Matrix.mul_assoc]
      _ = (ancInit : Matrix (α × β) α ℂ) * ρ * ancInitᴴ := by rw [hρ]
  rw [← hX, extractMat_conjTranspose hH]
  calc extractMat H * (A * ρ * Aᴴ) * extractMat H
      = extractMat H * A * ρ * (Aᴴ * extractMat H) := by simp only [Matrix.mul_assoc]
    _ = A * ρ * Aᴴ := by rw [hEA, hAH]

/-- ★★ **And the syndrome-`0` outcome is certain on the code.** -/
theorem ancProj_zero_mul_extractMat_conj_codeState {H : α → β} (hH : ∀ z, H z + H z = 0)
    {ρ : Matrix α α ℂ} (hρ : synProj H (0 : β) * ρ * synProj H (0 : β) = ρ) :
    ancProj (α := α) (0 : β) * (extractMat H * ((ancInit : Matrix (α × β) α ℂ) * ρ * ancInitᴴ)
        * (extractMat H)ᴴ)
      = extractMat H * ((ancInit : Matrix (α × β) α ℂ) * ρ * ancInitᴴ) * (extractMat H)ᴴ := by
  rw [extractMat_conj_codeState hH hρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ancProj_zero_mul_ancInit]

end QuantumInfo

end

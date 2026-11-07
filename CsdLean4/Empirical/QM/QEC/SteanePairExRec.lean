/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneInjection

/-!
# The `CNOT̄` extended rectangle

**Category:** 3-Local (Empirical, QM twin). BACKLOG #302 (QC chain, link 12; on the path to #315).

`SteanePairMachine.lean` (#226) runs the two-block machine on `isCorrectedStep_rect` with an ideal
recovery. #96's extended rectangle with a faulty **leading** recovery
(`isCorrectedStep_exRec_leading`) also needs the gadget to be transversal for the correctable set,
and #226 proved that for the single-block gadgets only. The transversal `CNOT̄` copies an `X` on
the control block's qubit `q` onto the target block's qubit `q` (and a `Z` the other way), so it
does not keep the set "weight one in each block" — a target error already on another qubit would
become weight two. This module supplies the two-set form instead.

* `cnotT_mul_pairPauli_mul_cnotT` — **the transversal `CNOT̄` on Paulis**: conjugation
  sends `X^{a₀}Z^{b₀} ⊗ X^{a₁}Z^{b₁}` to `X^{a₀}Z^{b₀+b₁} ⊗ X^{a₀+a₁}Z^{b₁}`, exactly, no sign
  (#304's `cnotT_mul_blockKron_pauliMat_mul_cnotT` is the case `a₀ = b₀ = 0`);
* `bitOn`, `errAt` — the Pauli labels at one qubit; `cnotT_mul_pairFam_errAt_mul_cnotT` — a Pauli
  on qubit `q` of each block goes to a Pauli on qubit `q` of each block;
  ★★ `cnotT_mul_blockFault_mul_cnotT_mem` — **a fault at one location of `CNOT̄`, conjugated by the
  gate, is in the span of the pair's error family** (not a product in general);
* `pairLocWeightOne` — **the input set `D₁`**: a unitary fault on qubit `q` of each block, the same
  `q` (one block's factor may be `1`, so a fault on one qubit of one block is the special case);
  **the output set `D₂`** is #304's `pairMix` (`SteaneInjection.lean`: mixtures of conjugations by
  unitary combinations of the pair's error family, corrected by `exists_isRecovery_pairMix`);
  `pairLocWeightOne_subset`, `conj_mem_pairMix`, ★★ `cnotT_mul_blockFault_mul_cnotT_mem_pairSpan`;
* ★★ `PairGadget.propagatesInto_cnot` — **`CNOT̄` carries `D₁` into `D₂`**;
  ★★ `PairGadget.propagatesInto_pairMix` — every gadget of the set does;
* ★★★ `steane_pair_exRec` — **#96's extended rectangle on the two-block register, `CNOT̄`
  included**: one recovery `R` such that a faulty leading recovery (any map leaving a `D₁`
  deviation) before an ideal gadget and `R` is a corrected step, a faulty gadget with a good pattern
  between two copies of `R` is a corrected step, and a faulty trailing recovery hands on a
  weight-one-per-block deviation.

## Honest scope

⚠️ **The leading recovery's deviation is a hypothesis**,
`DeviatesBy pairProj pairLocWeightOne id R₁`, as in `steane_exRec` (#207): one fault inside the
leading recovery is assumed to leave an error on one location's qubits. That Steane's method on
two blocks, built as a circuit, satisfies it is not proved here (on one block it is
`SteaneFaultyRecovery.lean`, #232).

⚠️ **`D₂` is larger than "weight one per block".** After `CNOT̄` the error on the pair of qubits `q`
can be entangled; `D₂` is #304's `pairMix`, which the Knill–Laflamme recovery corrects.
That the one-set `PropagatesD pairProj pairWeightOne` fails for `CNOT̄` is not proved; the two-set
form makes it unnecessary.

⚠️ **As in #226:** level one, unitary faults, ideal gadgets as maps, the recovery the two-block
Knill–Laflamme channel. Counting the recovery's own locations at every level is #312–#315.

References: P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97;
D. Gottesman, arXiv:quant-ph/9705052 (transversal `CNOT` on Paulis); `specs/BACKLOG.md` #302, #226,
#96, #315; `Mathlib/QuantumInfo/ExtendedRectangle.lean`
(`isCorrectedStep_exRec_leading_of_propagatesInto`), `Empirical/QM/QEC/SteanePairMachine.lean`,
`Empirical/QM/QEC/SteaneTransversalCNOT.lean`,
`Empirical/QM/QEC/SteaneMachine.lean` (`steane_exRec`);
`docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12; `specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The transversal `CNOT̄` on Paulis -/

/-- **The transversal `CNOT̄` on Paulis**: conjugation sends `X^{a₀}Z^{b₀} ⊗ X^{a₁}Z^{b₁}` to
`X^{a₀}Z^{b₀+b₁} ⊗ X^{a₀+a₁}Z^{b₁}` — the `X` part of the control copied onto the target, the `Z`
part of the target onto the control — with no sign. -/
theorem cnotT_mul_pairPauli_mul_cnotT (a b : Fin 2 → Fin 7 → Fin 2) :
    cnotT * blockKron (fun j => pauliMat (a j) (b j)) * cnotT
      = blockKron (fun j => pauliMat (![a 0, a 0 + a 1] j) (![b 0 + b 1, b 1] j)) := by
  ext z w
  rw [cnotT, mul_permMat_apply, permMat_mul_apply cnotPerm_involutive, blockKron_apply,
    blockKron_apply, Fin.prod_univ_two, Fin.prod_univ_two]
  rw [show cnotPerm w 0 = w 0 from rfl, show cnotPerm z 0 = z 0 from rfl,
    show cnotPerm w 1 = w 0 + w 1 from rfl, show cnotPerm z 1 = z 0 + z 1 from rfl,
    show (![a 0, a 0 + a 1] : Fin 2 → Fin 7 → Fin 2) 0 = a 0 from rfl,
    show (![a 0, a 0 + a 1] : Fin 2 → Fin 7 → Fin 2) 1 = a 0 + a 1 from rfl,
    show (![b 0 + b 1, b 1] : Fin 2 → Fin 7 → Fin 2) 0 = b 0 + b 1 from rfl,
    show (![b 0 + b 1, b 1] : Fin 2 → Fin 7 → Fin 2) 1 = b 1 from rfl]
  unfold pauliMat
  by_cases h0 : w 0 = z 0 + a 0
  · have hkey : z 0 + z 1 + a 1 = (z 0 + a 0) + (z 1 + (a 0 + a 1)) := by
      funext i
      simp only [Pi.add_apply]
      exact (by decide : ∀ x y p r : Fin 2, x + y + r = x + p + (y + (p + r))) _ _ _ _
    have h1 : w 0 + w 1 = z 0 + z 1 + a 1 ↔ w 1 = z 1 + (a 0 + a 1) := by
      rw [hkey, ← h0]
      exact add_right_inj _
    rw [ite_eq_left h0, ite_eq_left h0]
    by_cases h2 : w 1 = z 1 + (a 0 + a 1)
    · rw [ite_eq_left (h1.2 h2), ite_eq_left h2, pauliSign_add_right, pauliSign_add_left]
      ring
    · rw [ite_eq_right (mt h1.1 h2), ite_eq_right h2, mul_zero, mul_zero]
  · rw [ite_eq_right h0, ite_eq_right h0, zero_mul, zero_mul]

/-- The bit `x` on qubit `q`, zero elsewhere. -/
def bitOn (q : Fin 7) (x : Fin 2) : Fin 7 → Fin 2 := fun i => if i = q then x else 0

theorem bitOn_add (q : Fin 7) (x y : Fin 2) : bitOn q x + bitOn q y = bitOn q (x + y) := by
  funext i
  by_cases h : i = q <;> simp [bitOn, h]

/-- **The Pauli `X^x Z^y` on qubit `q`** as an error label. -/
def errAt (q : Fin 7) (x y : Fin 2) : SingleErr :=
  if x = 0 ∧ y = 0 then none else some (q, if y = 0 then 0 else if x = 0 then 1 else 2)

theorem errA_errAt (q : Fin 7) (x y : Fin 2) : errA (errAt q x y) = bitOn q x := by
  funext i
  fin_cases x <;> fin_cases y <;> by_cases h : i = q <;> simp [errAt, errA, bitOn, unitErr, h]

theorem errB_errAt (q : Fin 7) (x y : Fin 2) : errB (errAt q x y) = bitOn q y := by
  funext i
  fin_cases x <;> fin_cases y <;> by_cases h : i = q <;> simp [errAt, errB, bitOn, unitErr, h]

/-- A label that is no Pauli on qubit `q` has no coefficient in an operator on qubit `q`. -/
theorem singleCoeff_eq_zero_of_forall_ne {q : Fin 7} {i : SingleErr}
    (M : Matrix (Fin 2) (Fin 2) ℂ) (h : ∀ x y, i ≠ errAt q x y) : singleCoeff q M i = 0 := by
  rcases i with _ | ⟨j, t⟩
  · exact absurd (by simp [errAt]) (h 0 0)
  · by_cases hj : j = q
    · subst hj
      exfalso
      fin_cases t
      · exact h 1 0 (by simp [errAt])
      · exact h 0 1 (by simp [errAt])
      · exact h 1 1 (by simp [errAt])
    · simp [singleCoeff, hj]

/-- A Pauli on qubit `q` of each block goes, under `CNOT̄`, to a Pauli on qubit `q` of each
block. -/
theorem cnotT_mul_pairFam_errAt_mul_cnotT (q : Fin 7) (x y : Fin 2 → Fin 2) :
    cnotT * pairFam (fun j => errAt q (x j) (y j)) * cnotT
      = pairFam (fun j => errAt q (![x 0, x 0 + x 1] j) (![y 0 + y 1, y 1] j)) := by
  rw [pairFam, pairFam]
  simp only [errA_errAt, errB_errAt]
  refine (cnotT_mul_pairPauli_mul_cnotT (fun j => bitOn q (x j))
    (fun j => bitOn q (y j))).trans (congrArg blockKron (funext fun j => ?_))
  fin_cases j <;> simp [bitOn_add]

/-- ★★ **A fault at one location of `CNOT̄`, conjugated by the gate, is in the span of the pair's
error family.** The fault is a combination of Paulis on qubit `q` of each block (the others have
coefficient zero), and `CNOT̄` keeps each of those at qubit `q`. -/
theorem cnotT_mul_blockFault_mul_cnotT_mem (q : Fin 7) (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    cnotT * blockFault (fun _ => q) A * cnotT ∈ Submodule.span ℂ (Set.range pairFam) := by
  rw [blockFault_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Submodule.sum_mem _ fun g _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  by_cases hg : ∀ b, ∃ x y, g b = errAt q x y
  · choose x y hxy using hg
    obtain rfl : g = fun j => errAt q (x j) (y j) := funext hxy
    rw [cnotT_mul_pairFam_errAt_mul_cnotT]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · push Not at hg
    obtain ⟨b, hb⟩ := hg
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (singleCoeff_eq_zero_of_forall_ne (A b) hb),
      zero_smul]
    exact Submodule.zero_mem _

/-! ### The two correctable sets -/

/-- **The input set `D₁`**: a unitary fault on qubit `q` of each block, the same `q` — one location
of `CNOT̄`. A fault on one qubit of one block is the case where the other factor is `1`. -/
def pairLocWeightOne : Set (Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ) :=
  {f | ∃ (q : Fin 7) (A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ b, A b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
      ∧ f = fun ρ => blockFault (fun _ => q) A * ρ * (blockFault (fun _ => q) A)ᴴ}

theorem pairLocWeightOne_subset : pairLocWeightOne ⊆ pairWeightOne := by
  rintro _ ⟨q, A, hA, rfl⟩
  exact ⟨fun _ => q, A, hA, rfl⟩

/-- A conjugation by a member of `pairSpan` is a mixture of one: it lies in `pairMix`, the
injection's correctable set (#304), which is the output set `D₂` here. -/
theorem conj_mem_pairMix {F : Matrix PairReg PairReg ℂ} (hF : F ∈ pairSpan) :
    (fun ρ => F * ρ * Fᴴ) ∈ pairMix := by
  refine ⟨1, fun _ => 1, fun _ => F, fun _ => zero_le_one, by simp, fun _ => hF, ?_⟩
  funext ρ
  simp

/-- ★★ **The conjugated fault is a unitary combination of the pair's error family**: a member of
#304's `pairSpan`. -/
theorem cnotT_mul_blockFault_mul_cnotT_mem_pairSpan (q : Fin 7)
    {A : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ} (hA : ∀ b, A b ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    cnotT * blockFault (fun _ => q) A * cnotT ∈ pairSpan := by
  have e : ∀ M : Matrix PairReg PairReg ℂ, cnotT * (cnotT * M) = M := fun M => by
    rw [← Matrix.mul_assoc, cnotT_mul_self, Matrix.one_mul]
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (cnotT_mul_blockFault_mul_cnotT_mem q A)
  refine ⟨?_, a, ha.symm⟩
  rw [conjTranspose_mul, conjTranspose_mul, cnotT_conjTranspose]
  simp only [Matrix.mul_assoc, e]
  rw [← Matrix.mul_assoc (blockFault (fun _ => q) A)ᴴ, blockFault_conjTranspose_mul hA,
    Matrix.one_mul, cnotT_mul_self]

/-! ### Transversality into the second set -/

namespace PairGadget

/-- ★★ **`CNOT̄` carries `D₁` into `D₂`**: a fault at one of its locations, pushed through the gate,
is conjugation by `CNOT̄ · F · CNOT̄`, a member of `pairSpan`. -/
theorem propagatesInto_cnot :
    PropagatesInto pairProj pairLocWeightOne pairMix cnot.ideal := by
  rintro _ ⟨q, A, hA, rfl⟩ ρ _
  set B := blockFault (fun _ => q) A
  have e : ∀ M : Matrix PairReg PairReg ℂ, cnotT * (cnotT * M) = M := fun M => by
    rw [← Matrix.mul_assoc, cnotT_mul_self, Matrix.one_mul]
  refine ⟨fun σ => (cnotT * B * cnotT) * σ * (cnotT * B * cnotT)ᴴ,
    conj_mem_pairMix (cnotT_mul_blockFault_mul_cnotT_mem_pairSpan q hA), ?_⟩
  · show cnotT * (B * ρ * Bᴴ) * cnotTᴴ
      = (cnotT * B * cnotT) * (cnotT * ρ * cnotTᴴ) * (cnotT * B * cnotT)ᴴ
    rw [conjTranspose_mul, conjTranspose_mul, cnotT_conjTranspose]
    simp only [Matrix.mul_assoc, e]

/-- ★★ **Every gadget of the set carries `D₁` into `D₂`**: the single-block gadgets through #226's
one-set transversality, `CNOT̄` through `propagatesInto_cnot`. -/
theorem propagatesInto_pairMix (G : PairGadget) :
    PropagatesInto pairProj pairLocWeightOne pairMix G.ideal := by
  cases G with
  | single b G =>
    exact (propagatesD_single b G).propagatesInto pairLocWeightOne_subset
      pairWeightOne_subset_pairMix
  | phase b =>
    exact (propagatesD_phase b).propagatesInto pairLocWeightOne_subset
      pairWeightOne_subset_pairMix
  | cnot => exact propagatesInto_cnot

end PairGadget

/-! ### The extended rectangle -/

/-- ★★★ **#96's extended rectangle on the two-block register, `CNOT̄` included.** One recovery
channel `R`, correcting #304's `pairMix` (mixtures of unitary combinations of the pair's error
family), such that for every
gadget `G` of the set (`H̄`, `X̄`, `Z̄`, `S̄` on either block, and `CNOT̄`):

* **a faulty leading recovery** — any map leaving a fault on one location's qubits (`D₁`) — then
  the ideal gadget, then `R`, is a corrected step (`isCorrectedStep_exRec_leading_of_propagatesInto`
  with `PairGadget.propagatesInto_pairMix`);
* **a faulty gadget** with a good pattern between two copies of `R` is a corrected step;
* **a faulty trailing recovery** hands on a weight-one-per-block deviation of the ideal output. -/
theorem steane_pair_exRec :
    ∃ R : Channel PairReg PairReg (Option (Fin 2 → SingleErr)),
      IsRecovery pairProj R.apply pairMix
      ∧ (∀ (G : PairGadget) (R₁ : Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ),
          DeviatesBy pairProj pairLocWeightOne id R₁ →
          IsCorrectedStep pairProj G.ideal (exRec R₁ G.ideal R.apply))
      ∧ (∀ (G : PairGadget) (U : Fin 7 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
          (∀ q b, U q b ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
          ∀ ω : ConcatPat 7 1, isBad 7 1 ω = false →
            IsCorrectedStep pairProj G.ideal (exRec R.apply (G.faulty U (locPat ω)) R.apply))
      ∧ (∀ (G : PairGadget) (R₂ : Matrix PairReg PairReg ℂ → Matrix PairReg PairReg ℂ),
          DeviatesBy pairProj pairWeightOne id R₂ →
          DeviatesBy pairProj pairWeightOne G.ideal (exRec R.apply G.ideal R₂)) := by
  obtain ⟨R, hR⟩ := exists_isRecovery_pairMix
  have hW := hR.mono pairWeightOne_subset_pairMix
  refine ⟨R, hR, fun G R₁ hR₁ => ?_, fun G U hU ω hω => ?_, fun G R₂ hR₂ => ?_⟩
  · exact isCorrectedStep_exRec_leading_of_propagatesInto hR₁ G.propagatesInto_pairMix hR
      fun _ hρ => G.isCodeState_ideal hρ
  · exact isCorrectedStep_exRec_gadget id_mem_pairWeightOne hW
      (G.deviatesBy_faulty hU (card_le_one_of_isBad_eq_false hω)) hW
      fun _ hρ => G.isCodeState_ideal hρ
  · exact deviatesBy_exRec_trailing id_mem_pairWeightOne hW hR₂ fun _ hρ => G.isCodeState_ideal hρ

end Steane
end QEC
end QM
end Empirical
end CSD

end

end

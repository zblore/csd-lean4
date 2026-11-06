/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneMachineConcat

/-!
# The recursive simulation at the Steane code

**Category:** 3-Local (Empirical, QM twin). BACKLOG #231, first brick (the recursion with its
interleaved recoveries; the recoveries' own faults are the row's remainder).

`SteaneMachineConcat.lean` (#227) builds its level-`k` gadget as the transversal gate on all `7^k`
qubits followed by **one** level-`k` recovery. The threshold argument's simulation is recursive: a
level-`(k+1)` gadget is a layer of seven level-`k` gadgets, one per block, **each ending in its
own level-`k` recovery**, followed by the level-`(k+1)` recovery. Here that tower is built and shown
exact on every good fault pattern, with one recovery channel per level shared by every gate of the
set.

## The gadget, Kraus operator by Kraus operator

* `simFam`, `SimTower` — the Kraus index of the recursive gadget, and a recovery for every level
  `k + 1`; `simKraus` — **the recursive gadget's Kraus operators**: at level `0` the faulty gate, at
  level `k + 1` a recovery Kraus operator after the tensor of the seven blocks' level-`k` Kraus
  operators; `simApply` — the gadget as a map on states;
* `cTrans_conjTranspose_mul`, ★ `simKraus_tp` — **the gadget is trace preserving** (a channel) when
  the gate and the faults are unitary;
* `exists_simTower` — **a tower of recoveries acting Kraus operator by Kraus operator**: for every
  error in the span of the level-`(k+1)` family each recovery Kraus operator acts on the code as a
  scalar (#86's recovery, through `exists_kraus_mul_mul_eq_smul`);
* ★★★ `simKraus_mul_cEnc` — **on a good pattern every Kraus operator acts on the code as a scalar
  times the ideal gate**, `K_j E_k = c_j · (g^{⊗7^k} E_k)`. By induction: the good blocks are
  scalars by hypothesis, the one bad block is arbitrary, and a tensor of scalars and one arbitrary
  block lies in the span of the family (`blockKron_mem_span_cErr`), which the next recovery undoes;
* ★★★ `simApply_eq` — **the recursive gadget is exactly the ideal gate on every code state** for
  every good pattern: the scalars' weights sum to one by trace preservation.

## The machine

* `ConcatGadget.gate_conjTranspose_mul`; `machineCircuitSim`, `idealRun_machineCircuitSim`; ★★★
  `steane_machine_recursive` — **the Steane machine run as the recursive simulation**: one tower of
  recoveries such that at every level `k`, for every circuit of `N` gates of the set (`H̄`, `X̄`,
  `Z̄`, and `S̄` as `S` or `S†`), every unitary fault at the `7^k` leaves of each gate and every
  encoded input, a pattern that makes no gadget bad gives exactly the ideal output, and under
  independent leaf faults of rate at most `p` the output is ideal with probability at least
  `1 − N (21 p)^{2^k}/21`.

## Honest scope

⚠️ **The recoveries are ideal channels.** Each level's recovery is #86's Knill–Laflamme channel on
the level-`(k+1)` code, applied without faults; it is not itself built as a level-`k` circuit of
gadgets (syndrome extraction with level-`k` ancillas), and its locations are not counted. The bound
is the gate-fault bound of #227; counting the recoveries' locations at every level is the remainder
of BACKLOG #231.

⚠️ **Faults at the leaves, after the gate, unitary and independent**, as in #227.

⚠️ **The recursion's good set is #227's.** A pattern is good when at most one sub-block is bad at
every level of the tree (`isBad`); what is new is that the gadget realising it is the recursive one,
with a recovery after every block at every level.

References: D. Aharonov, M. Ben-Or, SIAM J. Comput. 38 (2008) 1207; P. Aliferis, D. Gottesman,
J. Preskill, Quantum Inf. Comput. 6 (2006) 97; E. Knill, R. Laflamme, W. Zurek, *Science* 279 (1998)
342; `specs/BACKLOG.md` #231, #227, #97, #86; `Empirical/QM/QEC/SteaneMachineConcat.lean`,
`Empirical/QM/QEC/SteaneConcat.lean`, `Mathlib/QuantumInfo/KnillLaflamme.lean`,
`Mathlib/QuantumInfo/LevelReduction.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12;
`specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory
open scoped ENNReal ComplexOrder

noncomputable section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The recursive gadget -/

/-- The Kraus index of the recursive level-`k` gadget: one operator at level `0`, and at level
`k + 1` an index for each block's level-`k` gadget and one for the level-`(k + 1)` recovery. -/
def simFam : ℕ → Type
  | 0 => Unit
  | k + 1 => (Fin 7 → simFam k) × Option (cFam (k + 1))

instance instFintypeSimFam : ∀ k, Fintype (simFam k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 =>
      have : Fintype (simFam k) := instFintypeSimFam k
      inferInstanceAs (Fintype ((Fin 7 → simFam k) × Option (cFam (k + 1))))

/-- A recovery for every level `k + 1`. -/
abbrev SimTower : Type :=
  ∀ k, Channel (cLabel (k + 1)) (cLabel (k + 1)) (Option (cFam (k + 1)))

/-- A level-`(k + 1)` operator read on the seven blocks: the identity, at the block type. -/
abbrev blockView {k : ℕ} (M : Matrix (cLabel (k + 1)) (cLabel (k + 1)) ℂ) :
    Matrix (Fin 7 → cLabel k) (Fin 7 → cLabel k) ℂ :=
  M

/-- **The recursive gadget's Kraus operators.** At level `0` the gate under its leaf's fault; at
level `k + 1` a Kraus operator of the level-`(k + 1)` recovery after the tensor of the seven blocks'
level-`k` gadgets, each of which ends in its own level-`k` recovery. -/
def simKraus (g : Matrix (Fin 2) (Fin 2) ℂ) (R : SimTower) :
    ∀ k, ConcatPat 7 k → ((Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ) → simFam k →
      Matrix (cLabel k) (cLabel k) ℂ
  | 0, x, U, _ => cFaulty g 0 x U
  | k + 1, x, U, j =>
      blockView ((R k).kraus j.2) *
        blockKron fun b : Fin 7 => simKraus g R k (x b) (fun a => U (Fin.cons b a)) (j.1 b)

/-- The recursive gadget as a map on states. -/
def simApply (g : Matrix (Fin 2) (Fin 2) ℂ) (R : SimTower) (k : ℕ) (x : ConcatPat 7 k)
    (U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ) (ρ : Matrix (cLabel k) (cLabel k) ℂ) :
    Matrix (cLabel k) (cLabel k) ℂ :=
  ∑ j, simKraus g R k x U j * ρ * (simKraus g R k x U j)ᴴ

/-- The transversal gate is unitary when the gate is. -/
theorem cTrans_conjTranspose_mul {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : gᴴ * g = 1) :
    ∀ k, (cTrans g k)ᴴ * cTrans g k = 1
  | 0 => hg
  | k + 1 => by
      show (blockKron fun _ : Fin 7 => cTrans g k)ᴴ * blockKron (fun _ : Fin 7 => cTrans g k) = 1
      rw [blockKron_conjTranspose, blockKron_mul]
      simp only [cTrans_conjTranspose_mul hg k]
      exact blockKron_one

/-- ★ **The recursive gadget is trace preserving** when the gate and the faults are unitary. -/
theorem simKraus_tp {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : gᴴ * g = 1) (R : SimTower) :
    ∀ k (x : ConcatPat 7 k) (U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ a, (U a)ᴴ * U a = 1) → ∑ j, (simKraus g R k x U j)ᴴ * simKraus g R k x U j = 1
  | 0, x, U, hU => by
      show ∑ _j : Unit, (cFaulty g 0 x U)ᴴ * cFaulty g 0 x U = 1
      rw [Fintype.sum_unique, cFaulty_eq, conjTranspose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (cFaultErr 0 x U)ᴴ,
        cFaultErr_unitary (U' := fun M => Mᴴ * M = 1) (fun _ h => h) 0 x U hU, Matrix.one_mul]
      exact cTrans_conjTranspose_mul hg 0
  | k + 1, x, U, hU => by
      set K : Fin 7 → simFam k → Matrix (cLabel k) (cLabel k) ℂ :=
        fun b => simKraus g R k (x b) (fun a => U (Fin.cons b a)) with hK
      set R7 : Option (cFam (k + 1)) → Matrix (Fin 7 → cLabel k) (Fin 7 → cLabel k) ℂ :=
        fun o => blockView ((R k).kraus o) with hR7
      have htp7 : ∑ o, (R7 o)ᴴ * R7 o = 1 := (R k).tp
      have hIH : ∀ b, ∑ i, (K b i)ᴴ * K b i = 1 := fun b =>
        simKraus_tp hg R k (x b) _ fun a => hU _
      have hin : ∀ (j : Fin 7 → simFam k),
          ∑ o, (R7 o * blockKron (fun b => K b (j b)))ᴴ * (R7 o * blockKron (fun b => K b (j b)))
            = blockKron (fun b => (K b (j b))ᴴ * K b (j b)) := by
        intro j
        calc ∑ o, (R7 o * blockKron (fun b => K b (j b)))ᴴ
              * (R7 o * blockKron (fun b => K b (j b)))
            = (blockKron (fun b => K b (j b)))ᴴ * (∑ o, (R7 o)ᴴ * R7 o)
                * blockKron (fun b => K b (j b)) := by
              simp only [conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
          _ = blockKron (fun b => (K b (j b))ᴴ * K b (j b)) := by
              rw [htp7, Matrix.mul_one, blockKron_conjTranspose, blockKron_mul]
      show ∑ j : (Fin 7 → simFam k) × Option (cFam (k + 1)),
          (R7 j.2 * blockKron (fun b => K b (j.1 b)))ᴴ * (R7 j.2 * blockKron (fun b => K b (j.1 b)))
        = (1 : Matrix (Fin 7 → cLabel k) (Fin 7 → cLabel k) ℂ)
      rw [Fintype.sum_prod_type]
      simp only [hin]
      rw [← blockKron_sum fun b i => (K b i)ᴴ * K b i]
      simp only [hIH]
      exact blockKron_one

/-! ### The tower of recoveries -/

/-- **A tower of recoveries acting Kraus operator by Kraus operator**: at every level `k + 1`, for
every error in the span of the level-`(k + 1)` family, each Kraus operator of the recovery acts on
the code as a scalar. #86's recoveries, through `exists_kraus_mul_mul_eq_smul`. -/
theorem exists_simTower :
    ∃ R : SimTower, ∀ k (E : Matrix (cLabel (k + 1)) (cLabel (k + 1)) ℂ),
      E ∈ Submodule.span ℂ (Set.range (cErr (k + 1))) →
        ∀ o, ∃ μ : ℂ, (R k).kraus o * E * cProj (k + 1) = μ • cProj (k + 1) := by
  have h : ∀ k, ∃ R : Channel (cLabel (k + 1)) (cLabel (k + 1)) (Option (cFam (k + 1))),
      ∀ E : Matrix (cLabel (k + 1)) (cLabel (k + 1)) ℂ,
        E ∈ Submodule.span ℂ (Set.range (cErr (k + 1))) →
          ∀ o, ∃ μ : ℂ, R.kraus o * E * cProj (k + 1) = μ • cProj (k + 1) := by
    intro k
    obtain ⟨c, R, hR⟩ := exists_cErr_recovery (k + 1)
    refine ⟨R, fun E hE o => ?_⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hE
    obtain ⟨γ, hγ⟩ := exists_smul_recovery_apply_of_eq_lin_comb hR ha.symm
    exact exists_kraus_mul_mul_eq_smul (isCodeProjector_cProj (k + 1)) R hγ o
  choose R hR using h
  exact ⟨R, hR⟩

/-! ### Exactness on good patterns -/

/-- ★★★ **On a good pattern every Kraus operator of the recursive gadget acts on the code as a
scalar times the ideal gate**: `K_j E_k = c_j · (g^{⊗7^k} E_k)`. At level `k + 1` the good blocks
are scalars times the ideal block gate by induction and the one bad block is arbitrary; factoring
the ideal gate out leaves a tensor of scalars and one arbitrary block, in the span of the
level-`(k + 1)` family, which each recovery Kraus operator turns into a scalar on the code. -/
theorem simKraus_mul_cEnc {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : gᴴ * g = 1)
    (hW : ∀ k, ∃ W : Matrix (Fin 2) (Fin 2) ℂ, cTrans g k * cEnc k = cEnc k * W)
    {R : SimTower}
    (hR : ∀ k (E : Matrix (cLabel (k + 1)) (cLabel (k + 1)) ℂ),
      E ∈ Submodule.span ℂ (Set.range (cErr (k + 1))) →
        ∀ o, ∃ μ : ℂ, (R k).kraus o * E * cProj (k + 1) = μ • cProj (k + 1)) :
    ∀ k (x : ConcatPat 7 k) (U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ),
      isBad 7 k x = false →
        ∀ j, ∃ c : ℂ, simKraus g R k x U j * cEnc k = c • (cTrans g k * cEnc k)
  | 0, x, U, hx, _ => ⟨1, by
      have hx' : patBit x = false := hx
      rw [one_smul]
      show (if patBit x then U Fin.elim0 * g else g) * (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = g * (1 : Matrix (Fin 2) (Fin 2) ℂ)
      rw [hx']
      rfl⟩
  | k + 1, x, U, hx, j => by
      classical
      obtain ⟨b₀, hgood⟩ := exists_forall_ne_isBad_eq_false hx
      set V := cTrans g k * cEnc k with hVdef
      have hVV : Vᴴ * V = 1 := by
        rw [hVdef, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cTrans g k)ᴴ,
          cTrans_conjTranspose_mul hg k, Matrix.one_mul, cEnc_conjTranspose_mul]
      set K : Fin 7 → Matrix (cLabel k) (cLabel k) ℂ :=
        fun b => simKraus g R k (x b) (fun a => U (Fin.cons b a)) (j.1 b) with hK
      have hc : ∀ b, ∃ c : ℂ, b ≠ b₀ → K b * cEnc k = c • V := by
        intro b
        by_cases hb : b = b₀
        · exact ⟨0, fun h => absurd hb h⟩
        · obtain ⟨c, hc⟩ := simKraus_mul_cEnc hg hW hR k (x b) (fun a => U (Fin.cons b a))
            (hgood b hb) (j.1 b)
          exact ⟨c, fun _ => hc⟩
      choose c hc using hc
      set N : Fin 7 → Matrix (cLabel k) (cLabel k) ℂ :=
        fun b => if b = b₀ then K b₀ * cEnc k * Vᴴ else c b • 1 with hN
      have hKN : ∀ b, K b * cEnc k = N b * V := by
        intro b
        by_cases hb : b = b₀
        · rw [hb]
          show K b₀ * cEnc k = (if b₀ = b₀ then K b₀ * cEnc k * Vᴴ else c b₀ • 1) * V
          rw [ite_eq_left rfl, Matrix.mul_assoc (K b₀ * cEnc k) Vᴴ V, hVV, Matrix.mul_one]
        · show K b * cEnc k = (if b = b₀ then K b₀ * cEnc k * Vᴴ else c b • 1) * V
          rw [ite_eq_right hb, hc b hb, Matrix.smul_mul, Matrix.one_mul]
      have hspan : (blockKron N : Matrix (cLabel (k + 1)) (cLabel (k + 1)) ℂ)
          ∈ Submodule.span ℂ (Set.range (cErr (k + 1))) := by
        refine blockKron_mem_span_cErr b₀ N (fun b hb => ?_) rfl
        show (if b = b₀ then K b₀ * cEnc k * Vᴴ else c b • 1)
          ∈ Submodule.span ℂ (Set.range (cErr k))
        rw [ite_eq_right hb, ← cErr_cIdOne k]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      obtain ⟨μ, hμ⟩ := hR k _ hspan j.2
      obtain ⟨W, hWk⟩ := hW (k + 1)
      set R7 : Matrix (Fin 7 → cLabel k) (Fin 7 → cLabel k) ℂ :=
        blockView ((R k).kraus j.2) with hR7
      set E7 : Matrix (Fin 7 → cLabel k) (Fin 2) ℂ :=
        blockKron (fun _ : Fin 7 => cEnc k) * steaneEnc with hE7
      set T7 : Matrix (Fin 7 → cLabel k) (Fin 7 → cLabel k) ℂ :=
        blockKron (fun _ : Fin 7 => cTrans g k) with hT7
      have hEE : E7ᴴ * E7 = 1 := cEnc_conjTranspose_mul (k + 1)
      have hW7 : T7 * E7 = E7 * W := hWk
      have hμ7 : R7 * blockKron N * (E7 * E7ᴴ) = μ • (E7 * E7ᴴ) := hμ
      have hPE : E7 * E7ᴴ * (E7 * W) = E7 * W := by
        rw [← Matrix.mul_assoc, Matrix.mul_assoc E7, hEE, Matrix.mul_one]
      have hBK : blockKron K * E7 = blockKron N * (T7 * E7) := by
        rw [hE7, hT7, ← Matrix.mul_assoc, blockKron_mul,
          ← Matrix.mul_assoc (blockKron fun _ => cTrans g k), blockKron_mul, ← Matrix.mul_assoc,
          blockKron_mul]
        congr 2
        funext b
        exact hKN b
      refine ⟨μ, ?_⟩
      show R7 * blockKron K * E7 = μ • (T7 * E7)
      calc R7 * blockKron K * E7 = R7 * (blockKron N * (E7 * W)) := by
            rw [Matrix.mul_assoc, hBK, hW7]
        _ = R7 * blockKron N * (E7 * E7ᴴ) * (E7 * W) := by
            rw [Matrix.mul_assoc (R7 * blockKron N) (E7 * E7ᴴ), hPE, Matrix.mul_assoc R7]
        _ = μ • (T7 * E7) := by
            rw [hμ7, Matrix.smul_mul, hPE, hW7]

/-- ★★★ **The recursive gadget is exactly the ideal gate on every code state**, for every good
pattern of unitary faults: each Kraus operator contributes its scalar's weight times the ideal
output, and the weights sum to one because the gadget is trace preserving. -/
theorem simApply_eq {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : gᴴ * g = 1)
    (hW : ∀ k, ∃ W : Matrix (Fin 2) (Fin 2) ℂ, cTrans g k * cEnc k = cEnc k * W)
    {R : SimTower}
    (hR : ∀ k (E : Matrix (cLabel (k + 1)) (cLabel (k + 1)) ℂ),
      E ∈ Submodule.span ℂ (Set.range (cErr (k + 1))) →
        ∀ o, ∃ μ : ℂ, (R k).kraus o * E * cProj (k + 1) = μ • cProj (k + 1))
    {k : ℕ} {x : ConcatPat 7 k} {U : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ}
    (hx : isBad 7 k x = false) (hU : ∀ a, (U a)ᴴ * U a = 1)
    {ρ : Matrix (cLabel k) (cLabel k) ℂ} (hρ : IsCodeState (cProj k) ρ) :
    simApply g R k x U ρ = cTrans g k * ρ * (cTrans g k)ᴴ := by
  choose c hc using simKraus_mul_cEnc hg hW hR k x U hx
  have hTT : (cTrans g k * cEnc k)ᴴ * (cTrans g k * cEnc k) = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cTrans g k)ᴴ,
      cTrans_conjTranspose_mul hg k, Matrix.one_mul, cEnc_conjTranspose_mul]
  set σ := (cEnc k)ᴴ * ρ * cEnc k with hσ
  have hρσ : ρ = cEnc k * σ * (cEnc k)ᴴ := by
    calc ρ = cProj k * ρ * cProj k := hρ
      _ = cEnc k * σ * (cEnc k)ᴴ := by simp only [cProj, hσ, Matrix.mul_assoc]
  have hterm : ∀ j, simKraus g R k x U j * ρ * (simKraus g R k x U j)ᴴ
      = (c j * star (c j)) • (cTrans g k * ρ * (cTrans g k)ᴴ) := by
    intro j
    have h2 : (cEnc k)ᴴ * (simKraus g R k x U j)ᴴ = star (c j) • (cTrans g k * cEnc k)ᴴ := by
      have h := congrArg conjTranspose (hc j)
      rwa [conjTranspose_mul, conjTranspose_smul] at h
    calc simKraus g R k x U j * ρ * (simKraus g R k x U j)ᴴ
        = (simKraus g R k x U j * cEnc k) * σ * ((cEnc k)ᴴ * (simKraus g R k x U j)ᴴ) := by
          conv_lhs => rw [hρσ]
          simp only [Matrix.mul_assoc]
      _ = (c j • (cTrans g k * cEnc k)) * σ * (star (c j) • (cTrans g k * cEnc k)ᴴ) := by
          rw [hc j, h2]
      _ = (c j * star (c j)) • (cTrans g k * (cEnc k * σ * (cEnc k)ᴴ) * (cTrans g k)ᴴ) := by
          rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (c j * star (c j)) • (cTrans g k * ρ * (cTrans g k)ᴴ) := by rw [← hρσ]
  have hs : ∑ j, c j * star (c j) = 1 := by
    have htp := simKraus_tp hg R k x U hU
    have h3 : (cEnc k)ᴴ * (∑ j, (simKraus g R k x U j)ᴴ * simKraus g R k x U j) * cEnc k
        = ∑ j, (c j * star (c j)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      calc (cEnc k)ᴴ * ((simKraus g R k x U j)ᴴ * simKraus g R k x U j) * cEnc k
          = (simKraus g R k x U j * cEnc k)ᴴ * (simKraus g R k x U j * cEnc k) := by
            rw [conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = (c j * star (c j)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
            rw [hc j, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hTT,
              mul_comm]
    rw [htp, Matrix.mul_one, cEnc_conjTranspose_mul, ← Finset.sum_smul] at h3
    have h00 := congrFun (congrFun h3 0) 0
    simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at h00
    exact h00.symm
  rw [simApply]
  simp only [hterm]
  rw [← Finset.sum_smul, hs, one_smul]

/-! ### The machine -/

/-- Every gate of the set is unitary. -/
theorem ConcatGadget.gate_conjTranspose_mul (G : ConcatGadget) : G.gateᴴ * G.gate = 1 := by
  cases G with
  | of G => exact G.gate_conjTranspose_mul
  | s => exact sGateM_conjTranspose_mul
  | sDag =>
    show sDagMᴴ * sDagM = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sDagM, Matrix.mul_apply, Fin.sum_univ_two]

/-- The machine's circuit at level `k`, each gate run as the recursive simulation. -/
def machineCircuitSim (k : ℕ) (R : SimTower) {N : ℕ} (gs : Fin N → ConcatGadget)
    (U : Fin N → (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ) (ω : CircuitPat N 7 k) :
    Circuit (cLabel k) :=
  List.ofFn fun j => ((gs j).idealK k, simApply (gs j).gate R k (ω j) (U j))

theorem idealRun_machineCircuitSim (k : ℕ) (R : SimTower) {N : ℕ} (gs : Fin N → ConcatGadget)
    (U : Fin N → (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ) (ω : CircuitPat N 7 k)
    (ρ : Matrix (cLabel k) (cLabel k) ℂ) :
    idealRun (machineCircuitSim k R gs U ω) ρ = machineIdealK k gs ρ := by
  rw [idealRun, machineCircuitSim, machineIdealK, List.map_ofFn]
  rfl

/-- ★★★ **The Steane machine run as the recursive simulation.** One tower of recoveries, a recovery
for every level, such that at every level `k`, for every circuit of `N` gates of the set (`H̄`,
`X̄`, `Z̄`, and `S̄` as `S` or `S†`) on the level-`k` code — each gate a layer of seven
level-`(k−1)` gadgets, each ending in its own recovery, then the level-`k` recovery — every
assignment of unitary faults to the gates' `7^k` leaves and every encoded input, a pattern that makes no gadget bad gives
exactly the ideal output, and under independent leaf faults of rate at most `p` the output is ideal
with probability at least `1 − N (21 p)^{2^k}/21`. -/
theorem steane_machine_recursive :
    ∃ R : SimTower, ∀ (k N : ℕ) (gs : Fin N → ConcatGadget)
      (U : Fin N → (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ),
        (∀ j a, U j a ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
        ∀ ρ : Matrix (cLabel k) (cLabel k) ℂ, IsCodeState (cProj k) ρ →
          (∀ ω : CircuitPat N 7 k, (∀ j, isBad 7 k (ω j) = false) →
              correctedRun (machineCircuitSim k R gs U ω) ρ = machineIdealK k gs ρ)
          ∧ ∀ (ν : MeasureTheory.Measure Bool) [MeasureTheory.IsProbabilityMeasure ν] {p : ℝ},
              0 ≤ p → ν {c | c = true} ≤ ENNReal.ofReal p →
              1 - (N : ℝ≥0∞) * ENNReal.ofReal (codeCapacityBound 21 p k)
                ≤ QuantumInfo.circuitMeasure N 7 ν k
                    {ω | correctedRun (machineCircuitSim k R gs U ω) ρ = machineIdealK k gs ρ} := by
  obtain ⟨R, hR⟩ := exists_simTower
  refine ⟨R, fun k N gs U hU ρ hρ => ?_⟩
  have hU' : ∀ j a, (U j a)ᴴ * U j a = 1 := fun j a => by
    have := Matrix.mem_unitaryGroup_iff'.1 (hU j a)
    rwa [Matrix.star_eq_conjTranspose] at this
  have hstep : ∀ (G : ConcatGadget) (x : ConcatPat 7 k)
      (V : (Fin k → Fin 7) → Matrix (Fin 2) (Fin 2) ℂ), (∀ a, (V a)ᴴ * V a = 1) →
        isBad 7 k x = false → IsCorrectedStep (cProj k) (G.idealK k) (simApply G.gate R k x V) :=
    fun G x V hV hx =>
      ⟨fun σ hσ => simApply_eq G.gate_conjTranspose_mul
          (fun k => by obtain ⟨μ, h⟩ := G.exists_cTrans_mul_cEnc k; exact ⟨_, h⟩) hR hx hV hσ,
        fun σ hσ => G.isCodeState_idealK k hσ⟩
  have hgood : ∀ ω : CircuitPat N 7 k, (∀ j, isBad 7 k (ω j) = false) →
      correctedRun (machineCircuitSim k R gs U ω) ρ = machineIdealK k gs ρ := by
    intro ω hω
    rw [← idealRun_machineCircuitSim k R gs U ω ρ]
    refine correctedRun_eq_idealRun_of_level (k := 0) (fun g hg => ?_) hρ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact hstep (gs j) (ω j) (U j) (hU' j) (hω j)
  refine ⟨hgood, fun ν _ p hp hν => ?_⟩
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by norm_num [Nat.choose]
  have h := one_sub_le_measure_output_eq_concat (N := N) (n := 7) (k := k) ν hp hν
    (out := fun ω => correctedRun (machineCircuitSim k R gs U ω) ρ)
    (ideal := machineIdealK k gs ρ) hgood
  rwa [h21] at h

end Steane
end QEC
end QM
end Empirical
end CSD

end

end

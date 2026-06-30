import CsdLean4.Empirical.CSD.Einselection
import CsdLean4.Mathlib.QuantumInfo.Entropy

/-!
# Empirical/CSD: channel capacities of the de-isolation / dephasing channel (Build 15e)

**Category:** 6-Local (the open-system / decoherence stratum of D1; the K1
von-Neumann-entropy reading of the de-isolation channel of 15a-d).

A dephasing (de-isolation) channel transmits CLASSICAL information but destroys
QUANTUM coherence. This file gives the entropy-based, single-shot contrast on the
completely-dephasing channel `Φ_deph = decohereReducedN` (15a, `Einselection.lean`),
reusing the K1-A von Neumann entropy `QuantumInfo.vonNeumannEntropy`.

## Part A: the information quantity (single-letter Holevo χ)

`holevoChi2 h0 h1 havg := S(½ρ0 + ½ρ1) − (½ S(ρ0) + ½ S(ρ1))`, the Holevo χ of the
equal-weight two-element ensemble `{(½,ρ0),(½,ρ1)}`. This is the **single-letter /
single-shot** Holevo quantity, NOT the regularized classical capacity (a limit over
many channel uses with additivity, which is not formalised here).

**Honest scope on the general bound.** `holevoChi2 ≥ 0` in general is concavity of the
von Neumann entropy `S(∑pᵢρᵢ) ≥ ∑pᵢS(ρᵢ)`. Entropy concavity is NOT in the K1 API
(`Subadditivity.lean` proves `S(ρAB) ≤ S(ρA)+S(ρB)`, a different statement; the SSA
fork is open). So no general `holevo_nonneg` is asserted here; instead the headline
value `χ = log 2 > 0` is obtained by DIRECT computation on the concrete channel.

## Part B: the classical-yes / quantum-no contrast (direct computation)

- **Classical info survives.** The computational-basis states `|i⟩⟨i|` are FIXED POINTS
  of `Φ_deph` (`dephasing_fixes_basis_state`, general `N`). For the qubit ensemble
  `{(½,|0⟩⟨0|),(½,|1⟩⟨1|)}` the Holevo χ through the channel is `log 2`, a full
  classical bit (`holevo_classical_eq_log_two`): `S(½I) − ½·0 − ½·0 = log 2`.
- **Quantum coherence destroyed.** The same channel maps the coherent `|+⟩⟨+|` to the
  maximally mixed `½I` (`dephasing_plus_eq_half_one`), so a pure (zero-entropy) input
  becomes entropy `log 2` (`dephasing_destroys_coherence`): the entropy jump `0 → log 2`,
  the decoherence witness.
- `dephasing_classical_vs_quantum` (capstone): fixed points on the classical basis +
  `|+⟩ → ½I` + entropy jump + Holevo `χ = log 2`.

The entropy values are DERIVED (not gated): `S(|i⟩⟨i|) = S(|+⟩⟨+|) = 0` from
`vonNeumannEntropy_eq_zero_of_pure`; `S(½I) = log 2` from the maximally-mixed value
`vonNeumannEntropy_const_smul_one` (charpoly route, `spectral_sum_eq_of_charpoly_prod`).

## Part C: the CSD reading and D1 gating

Channel capacity = how much Σ-volume distinguishability survives the de-isolation
channel: the dephasing channel preserves the classical (pointer-basis) volume
partition (fixed points) but collapses the coherent (off-diagonal) Σ-structure (the
`|+⟩ → ½I` entropy increase). This is the operational / volume reading. The genuine
ontic Σ-volume capacity (the de-isolation flow's information throughput as a property
of `Φ ≠ id`) is D1-gated to the entangled tier (LF6); `Φ = id` in every concrete
`SectorData`. No volume-capacity theorem is claimed here.

All exports are foundational-triple-only (off `busch_effect_gleason`): concrete
`Matrix` spectral arithmetic on the 15a dephasing channel and the K1-A entropy.
-/

open Matrix Polynomial QuantumInfo
open CSD.LF2 CSD.LF5
open CSD.Empirical.CSDBridge.Einselection

namespace CSD
namespace Empirical
namespace CSDBridge
namespace ChannelCapacity

/-! ### Entropy of a scalar (maximally-mixed) state

The Cat-1 entropy facts `const_smul_one_isHermitian`, `vonNeumannEntropy_const_smul_one`
(`S((↑c)·I) = N·negMulLog c`), and `vonNeumannEntropy_maximally_mixed` (`S((1/N)·I) = log N`,
the saturating case of `vonNeumannEntropy_le_log_card`) live in the K1 staging tree
`Mathlib/QuantumInfo/Entropy.lean` under `namespace QuantumInfo` (they are CSD-free); they
are in scope here via `open QuantumInfo`. -/

/-- Entropy is a function of the matrix only (proof-irrelevant in the Hermitian
witness): `A = B ⟹ S(hA) = S(hB)`. -/
lemma vonNeumannEntropy_congr {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A = B) :
    vonNeumannEntropy hA = vonNeumannEntropy hB := by
  subst hAB; rfl

/-! ### The Holevo χ of a two-element equal-weight ensemble -/

/-- **The single-letter Holevo χ** of the equal-weight ensemble `{(½,ρ0),(½,ρ1)}`:
`χ = S(½ρ0 + ½ρ1) − (½ S(ρ0) + ½ S(ρ1))`. This is the single-shot quantity, NOT the
regularized classical capacity. -/
noncomputable def holevoChi2 {N : ℕ} {ρ0 ρ1 : Matrix (Fin N) (Fin N) ℂ}
    (h0 : ρ0.IsHermitian) (h1 : ρ1.IsHermitian)
    (havg : ((↑((1 : ℝ) / 2) : ℂ) • ρ0 + (↑((1 : ℝ) / 2) : ℂ) • ρ1).IsHermitian) : ℝ :=
  vonNeumannEntropy havg
    - ((1 / 2 : ℝ) * vonNeumannEntropy h0 + (1 / 2 : ℝ) * vonNeumannEntropy h1)

/-! ### Computational-basis facts (the classical ensemble) -/

/-- A computational basis vector has unit norm. -/
lemma compBasis_norm {N : ℕ} (i : Fin N) :
    ‖(EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin N))‖ = 1 := by
  rw [PiLp.norm_single]; exact norm_one

/-- `S(|i⟩⟨i|) = 0`: a computational-basis pure state has zero entropy. -/
lemma compBasis_entropy_zero {N : ℕ} (i : Fin N) :
    vonNeumannEntropy (outerProduct_isHermitian (EuclideanSpace.single i (1 : ℂ))) = 0 :=
  vonNeumannEntropy_eq_zero_of_pure _
    (outerProduct_mul_self_of_unit_norm _ (compBasis_norm i))
    (outerProduct_trace_of_unit_norm _ (compBasis_norm i))

/-! ### Part B (classical-yes): the dephasing channel fixes the pointer basis -/

/-- **Classical info survives: `|i⟩⟨i|` is a fixed point of the dephasing channel.**
`Φ_deph(|i⟩⟨i|) = |i⟩⟨i|`, every `N`. The computational-basis density is already
diagonal (`outerProduct_single`), so the off-diagonal-killing channel leaves it
unchanged. The classical (pointer-basis) states are transmitted perfectly. -/
theorem dephasing_fixes_basis_state {N : ℕ} (i : Fin N) :
    decohereReducedN (outerProduct (EuclideanSpace.single i (1 : ℂ)))
      = outerProduct (EuclideanSpace.single i (1 : ℂ)) := by
  rw [outerProduct_single, decohereReducedN]
  ext a b
  rw [Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]
  · rw [if_neg hab, Matrix.single_apply, if_neg (fun h => hab (h.1.symm.trans h.2))]

/-- The classical-ensemble average of the channel outputs is the maximally mixed
`½I`: `½|0⟩⟨0| + ½|1⟩⟨1| = ½I`. The two computational-basis projectors sum to `I`. -/
theorem classical_avg_eq_half_one :
    ((↑((1 : ℝ) / 2) : ℂ) • outerProduct (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
      + (↑((1 : ℝ) / 2) : ℂ) • outerProduct (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)))
      = (↑((1 : ℝ) / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← smul_add]
  congr 1
  rw [outerProduct_single, outerProduct_single,
    ← Fin.sum_univ_two (f := fun i : Fin 2 => Matrix.single i i (1 : ℂ))]
  exact Matrix.sum_single_one

/-- The classical-ensemble average is Hermitian (it is `½I`). -/
theorem classical_avg_isHermitian :
    ((↑((1 : ℝ) / 2) : ℂ) • outerProduct (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
      + (↑((1 : ℝ) / 2) : ℂ)
          • outerProduct (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))).IsHermitian := by
  rw [classical_avg_eq_half_one]; exact const_smul_one_isHermitian _

/-- **The classical Holevo χ is a full bit: `χ = log 2`.** For the computational-basis
ensemble `{(½,|0⟩⟨0|),(½,|1⟩⟨1|)}`, which the dephasing channel transmits as fixed
points (`dephasing_fixes_basis_state`), the single-letter Holevo quantity is
`S(½I) − ½·0 − ½·0 = log 2`. The full classical bit survives the de-isolation. -/
theorem holevo_classical_eq_log_two :
    holevoChi2 (outerProduct_isHermitian (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)))
        (outerProduct_isHermitian (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)))
        classical_avg_isHermitian = Real.log 2 := by
  unfold holevoChi2
  rw [compBasis_entropy_zero (0 : Fin 2), compBasis_entropy_zero (1 : Fin 2),
    vonNeumannEntropy_congr classical_avg_isHermitian
      (const_smul_one_isHermitian (N := 2) ((1 : ℝ) / 2)) classical_avg_eq_half_one,
    vonNeumannEntropy_const_smul_one, Real.negMulLog,
    show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ from by norm_num, Real.log_inv]
  push_cast; ring

/-! ### Part B (quantum-no): the dephasing channel destroys coherence -/

/-- The coherent state `|+⟩ = degenerateWitness` has unit norm. -/
lemma degenerateWitness_norm : ‖degenerateWitness‖ = 1 := by
  have h := CSD.LF4.euclidean_norm_sq_eq_sum degenerateWitness
  rw [Fin.sum_univ_two, degenerateWitness_apply_zero, degenerateWitness_apply_one] at h
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [abs_of_pos (inv_pos.mpr hpos)] at h
  have hsq : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [hsq] at h
  have h1 : ‖degenerateWitness‖ ^ 2 = 1 := by linarith
  have hfac : (‖degenerateWitness‖ - 1) * (‖degenerateWitness‖ + 1) = 0 := by
    have hexp : (‖degenerateWitness‖ - 1) * (‖degenerateWitness‖ + 1)
        = ‖degenerateWitness‖ ^ 2 - 1 := by ring
    rw [hexp, h1]; ring
  have hpos2 : (0 : ℝ) < ‖degenerateWitness‖ + 1 := by positivity
  have := (mul_eq_zero.mp hfac).resolve_right (by linarith)
  linarith

/-- `S(|+⟩⟨+|) = 0`: the coherent input is a pure (zero-entropy) state. -/
theorem plus_entropy_zero :
    vonNeumannEntropy (outerProduct_isHermitian degenerateWitness) = 0 :=
  vonNeumannEntropy_eq_zero_of_pure _
    (outerProduct_mul_self_of_unit_norm _ degenerateWitness_norm)
    (outerProduct_trace_of_unit_norm _ degenerateWitness_norm)

/-- **Quantum-no: the dephasing channel maps the coherent `|+⟩⟨+|` to `½I`.**
`Φ_deph(|+⟩⟨+|) = ½I` (the maximally mixed qubit): the off-diagonal coherences of the
equal-population superposition are killed, sending the pure input to the fully mixed
state. Reuses `decohereReducedN_outerProduct` (the channel on a pure density) +
`degenerateWitness_decohere_half` (15a, the qubit dephasing computation). -/
theorem dephasing_plus_eq_half_one :
    decohereReducedN (outerProduct degenerateWitness)
      = (↑((1 : ℝ) / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [decohereReducedN_outerProduct, degenerateWitness_decohere_half]
  congr 1
  push_cast; ring

/-- The dephased coherent output `Φ_deph(|+⟩⟨+|) = ½I` is Hermitian. -/
theorem dephasing_plus_output_isHermitian :
    (decohereReducedN (outerProduct degenerateWitness)).IsHermitian := by
  rw [dephasing_plus_eq_half_one]; exact const_smul_one_isHermitian _

/-- **The dephased coherent output has entropy `log 2`.** `S(Φ_deph(|+⟩⟨+|)) = S(½I) =
log 2`: the maximally mixed qubit's maximal entropy. -/
theorem dephasing_plus_output_entropy :
    vonNeumannEntropy dephasing_plus_output_isHermitian = Real.log 2 := by
  rw [vonNeumannEntropy_congr dephasing_plus_output_isHermitian
      (const_smul_one_isHermitian (N := 2) ((1 : ℝ) / 2)) dephasing_plus_eq_half_one,
    vonNeumannEntropy_const_smul_one, Real.negMulLog,
    show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ from by norm_num, Real.log_inv]
  push_cast; ring

/-- **THE decoherence witness: coherence destroyed, entropy jumps `0 → log 2`.**
The pure coherent input `|+⟩⟨+|` (entropy `0`) is sent by the dephasing channel to the
maximally mixed `½I` (entropy `log 2`): the strict entropy increase
`S(|+⟩⟨+|) = 0 < log 2 = S(Φ_deph(|+⟩⟨+|))`. The channel cannot preserve the
superposition: quantum coherence is destroyed. Connects to 15a
(`decohere_not_diagonal_in_rotated_basis`, the off-diagonal-killing) and the LF6-B.2
purity drop. -/
theorem dephasing_destroys_coherence :
    vonNeumannEntropy (outerProduct_isHermitian degenerateWitness) = 0
    ∧ vonNeumannEntropy dephasing_plus_output_isHermitian = Real.log 2
    ∧ vonNeumannEntropy (outerProduct_isHermitian degenerateWitness)
        < vonNeumannEntropy dephasing_plus_output_isHermitian := by
  refine ⟨plus_entropy_zero, dephasing_plus_output_entropy, ?_⟩
  rw [plus_entropy_zero, dephasing_plus_output_entropy]
  exact Real.log_pos (by norm_num)

/-! ### Capstone -/

/-- **Build 15e capstone: classical information survives, quantum coherence destroyed.**
For the completely-dephasing (de-isolation) channel `Φ_deph = decohereReducedN`:

1. **classical-yes** — the computational-basis states are FIXED POINTS,
   `Φ_deph(|i⟩⟨i|) = |i⟩⟨i|` for every `i` (`dephasing_fixes_basis_state`);
2. **quantum-no** — the coherent `|+⟩⟨+|` is mapped to the maximally mixed `½I`
   (`dephasing_plus_eq_half_one`);
3. the coherent input is pure, `S(|+⟩⟨+|) = 0` (`plus_entropy_zero`);
4. its dephased output is maximally mixed, `S(½I) = log 2`
   (`dephasing_plus_output_entropy`): the entropy jump `0 → log 2`;
5. the single-letter Holevo χ of the classical basis ensemble is a full bit,
   `χ = log 2` (`holevo_classical_eq_log_two`).

The contrast is single-shot Holevo / coherent-information, NOT the regularized
capacity. The CSD reading: the de-isolation channel preserves the classical
(pointer-basis) Σ-volume partition but collapses the coherent off-diagonal
Σ-structure; the ontic Σ-volume capacity (throughput of `Φ ≠ id`) is D1-gated to the
entangled tier (LF6). Foundational-triple-only. -/
theorem dephasing_classical_vs_quantum :
    (∀ i : Fin 2, decohereReducedN (outerProduct (EuclideanSpace.single i (1 : ℂ)))
        = outerProduct (EuclideanSpace.single i (1 : ℂ)))
    ∧ decohereReducedN (outerProduct degenerateWitness)
        = (↑((1 : ℝ) / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    ∧ vonNeumannEntropy (outerProduct_isHermitian degenerateWitness) = 0
    ∧ vonNeumannEntropy dephasing_plus_output_isHermitian = Real.log 2
    ∧ holevoChi2 (outerProduct_isHermitian (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)))
        (outerProduct_isHermitian (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)))
        classical_avg_isHermitian = Real.log 2 :=
  ⟨fun i => dephasing_fixes_basis_state i, dephasing_plus_eq_half_one,
   plus_entropy_zero, dephasing_plus_output_entropy, holevo_classical_eq_log_two⟩

end ChannelCapacity
end CSDBridge
end Empirical
end CSD

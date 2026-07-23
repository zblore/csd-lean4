/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF5.FlowBornFrequency
public import CsdLean4.LF6.ForcedContextuality
public import CsdLean4.LF3.Singlet.Expectations

/-!
# LF6-D: the general d x d maximally-entangled de-isolation flow

**Category:** 6-Local (the first genuinely DIMENSION-GENERAL instance of CSD's D1
entangled frontier; the general-`d` analogue of the singlet's LF6-A.2 and the
GHZ's LF6-C.2).

Before this file the entangled de-isolation tier had exactly two hand-built
instances: the 2x2 singlet (LF6-A) and the three-qubit GHZ (LF6-C). This module
makes "general-N" actually general: it instantiates the LF5 general-`N`
de-isolation engine at `N = d * d` for the bipartite maximally-entangled state
`Ψ_d = (1/√d) ∑_i |i⟩|i⟩` on `EuclideanSpace ℂ (Fin d × Fin d)`, for **every**
`d ≥ 2`, and lands the pointer-block Fubini-Study volumes on the maximally-mixed
Born weights `1/d`, with a.s. block frequencies converging to them.

## The construction (reusing LF5 @ N = d·d)

The bipartite system `ℂ^{d²} ≅ ℂ^d ⊗ ℂ^d` is measured by the LF5 von Neumann
de-isolation flow `measurementFlow (d*d) e` on the dilated projective ontic space
`Σ' = ℂℙ^{d²·d²−1}`. The flow is inherited wholesale from LF5-B at `N = d*d`; it
is genuinely `Φ ≠ id` (`1 < d*d`, i.e. `d ≥ 2`) and Fubini-Study
measure-preserving. The prepared state is `Ψ_d` reindexed to the computational
`Fin (d*d)` basis (`nudgedMaxEntangled d`). Then the headline:

```
pointer-block w FS volume  =  ‖⟨e_{medIdx w}, nudgedMaxEntangled d⟩‖²   -- LF5 @ N=d·d
                           =  ‖(maxEntangled d) w‖²                       -- reindex identity
                           =  medWeight d w                               -- 1/d on the diagonal, 0 off
```

So the reproduction is LF5@N=d·d + a coordinate (reindex-isometry) step + the
computed maximally-entangled Born weights `medWeight`.

## Honest scope (the D ledger)

- **Dimension-general, exhibited.** A genuine deterministic FS-measure-preserving
  de-isolation flow `Φ ≠ id` for every `d ≥ 2` (`maxEntangledDeisolation_*`),
  whose context-fixed `BornRegion` pointer-block volumes equal the Born weights
  `medWeight` (`maxEntangledDeisolation_pointer_volume`) and whose a.s. block
  frequencies converge to them (`maxEntangledDeisolation_frequency`). This is the
  load-bearing content: the LF6 de-isolation dynamics + Born-from-volume is now
  GENUINELY DIMENSION-GENERAL, not tied to 2x2 / GHZ.
- **Imported, not re-derived.** Born = FS-volume is the DH/moment-map cluster's
  (`fs_born_volume_ratio_N`, Gleason-free, no Born put in), imported through
  `vnDilation_pointer_volume`; this file does not re-derive it. What is exercised
  is the measurement **dynamics** (`Φ ≠ id`).
- **Realisation, not derivation.** The flow **realises** the measurement
  dynamically; it does not derive the weights from independent dynamics. The
  carve is the joint moment subdivision, never a setting-local product region.
- **Forced non-factorisation, derived and maxEntangled-specific.** `Ψ_d`'s
  `{0,1}×{0,1}` Schmidt sector is *derived* (full state, coherences included) to
  be the Bell `Φ⁺` state up to the positive scalar `√2/√d`
  (`maxEntangledSector_eq_phiPlus`). `Φ⁺`'s two-qubit Pauli correlation is
  *computed here from the Hilbert space* (`phiPlus_pauli_correlation`:
  `⟨Φ⁺|σ·a ⊗ σ·b|Φ⁺⟩ = a_x b_x − a_y b_y + a_z b_z`), and no product
  (setting-local, non-contextual) partition reproduces it
  (`no_product_partition_realises_phiPlus`). The CHSH violation is genuinely
  `Φ⁺`'s: the orthogonal `xz`-reflection of Bob's axis (`reflectXZ`) carries
  `E_{Φ⁺}` to the singlet's `−a·b` (`phiPlusCorrelation_reflectXZ`), so `Φ⁺`
  reaches the same `2√2 > 2`, contradicting the LHV cap `|S| ≤ 2`
  (`lhvCHSH_abs_le_two`). So `no_product_partition_realises_maxEntangled` is
  Bell-forced *and* maxEntangled-specific (the `Φ⁺` correlation is derived and
  identified with the sector, not the singlet's `−a·b` imported by prose). Scope:
  non-factorisation forced by the CHSH-violating 2x2 `Φ⁺` sector. This is now
  superseded for **every** `d ≥ 2` by the genuinely `d`-intrinsic CGLMP violation of
  `Ψ_d` (`CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d`,
  `CGLMPQudit.cglmp_maxEntangled_qudit_gt_two`: `cglmp d pQM > 2` for all `d ≥ 2`,
  computed from `Ψ_d`'s actual Born probabilities via the Dirichlet-kernel closed
  form), with `d = 3` (`cglmp 3 pQM = (12+8√3)/9`) the concrete qutrit anchor. The
  general-`d` CGLMP result is now closed.
- **Residue: A5.** The entangled sector / preparation region is posited, not
  derived (SO-1: the sector origin, distinct from Paper C Axiom A5); the typicality law on `Σ'` is the Fubini-Study
  measure (A5).

All exports are foundational-triple-only (Gleason-free; the LF5 pointer engine is
off Busch, A.1 is measure-theoretic Bell content).

Reference: `specs/lf6-plan.md` (LF6-D).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal BigOperators LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF3 CSD.LF5 CSD.LF4 CSD.LF2 CSD.Empirical.QM.E91

/-- `d * d` is nonzero whenever `d` is (targeted local instance so the LF5 engine
at `N = d * d` synthesises `[NeZero (d * d)]` from `[NeZero d]`). -/
instance neZero_mul_self (d : ℕ) [NeZero d] : NeZero (d * d) :=
  ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩

/-! ### The maximally-entangled Born weights -/

/-- **The maximally-entangled Born weights.** `Ψ_d = (1/√d) ∑_i |i⟩|i⟩` has
support exactly on the diagonal `{(i, i)}`, each computational cell carrying
weight `1/d`; every off-diagonal cell has weight `0`. This is the maximally-mixed
(Schmidt-rank-`d`) weight vector. Not a stub: `maxEntangled_normSq_eq_weight`
proves it equals `‖(maxEntangled d) w‖²`. -/
noncomputable def medWeight (d : ℕ) (w : Fin d × Fin d) : ℝ :=
  if w.1 = w.2 then (d : ℝ)⁻¹ else 0

/-! ### The maximally-entangled state -/

/-- **The bipartite maximally-entangled state** `Ψ_d = (1/√d) ∑_i |i⟩|i⟩` on
`EuclideanSpace ℂ (Fin d × Fin d)`: the computational amplitude is `(√d)⁻¹` on
the diagonal and `0` off it. Schmidt rank `d`; unit-norm for `d ≥ 1`. -/
noncomputable def maxEntangled (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun w => if w.1 = w.2 then ((Real.sqrt d : ℂ))⁻¹ else 0)

/-- The computational amplitude of `Ψ_d` at cell `w`. -/
lemma maxEntangled_apply (d : ℕ) (w : Fin d × Fin d) :
    (maxEntangled d) w = if w.1 = w.2 then ((Real.sqrt d : ℂ))⁻¹ else 0 := rfl

/-- **The Born weights are the squared computational amplitudes.** For every
computational cell `w`, `‖(maxEntangled d) w‖² = medWeight d w` — genuinely
computed from the diagonal amplitude `(√d)⁻¹` (`‖·‖² = 1/d`) and the off-diagonal
zeros. -/
lemma maxEntangled_normSq_eq_weight (d : ℕ) (w : Fin d × Fin d) :
    ‖(maxEntangled d) w‖ ^ 2 = medWeight d w := by
  rw [maxEntangled_apply]
  unfold medWeight
  by_cases h : w.1 = w.2
  · rw [if_pos h, if_pos h, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ))]
  · rw [if_neg h, if_neg h, norm_zero]; norm_num

/-- The maximally-entangled Born weights sum to `1` (the `d` diagonal cells, each
`1/d`; the off-diagonal cells `0`). The prepared state is normalised. -/
lemma sum_medWeight (d : ℕ) (hd : 0 < d) : ∑ w : Fin d × Fin d, medWeight d w = 1 := by
  unfold medWeight
  rw [Fintype.sum_prod_type]
  have hinner : ∀ i : Fin d,
      (∑ j : Fin d, if (i, j).1 = (i, j).2 then (d : ℝ)⁻¹ else 0) = (d : ℝ)⁻¹ := by
    intro i
    simp only
    rw [Finset.sum_ite_eq Finset.univ i (fun _ => (d : ℝ)⁻¹)]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd.ne')

/-! ### The diagonal Born-weight marginal is uniform (`1/d`) -/

/-- **The diagonal Born-weight marginal is uniform (`1/d`).** For every system
index `i`, the marginal Born weight `∑_j medWeight d (i, j) = 1/d` (one diagonal
cell contributes `1/d`, the rest `0`). This is the *diagonal* (computational-basis
Born-weight) marginal only; it is the maximal-entanglement signature at that level
(a uniform diagonal marginal is necessary for `ρ_A = I/d`), but it does NOT by
itself establish `ρ_A = I/d` (the off-diagonal vanishing of the reduced state is a
separate fact, not proved here). Holds for every `d ≥ 1` (the sole `i` diagonal
cell contributes `1/d`). -/
lemma maxEntangled_marginal_uniform (d : ℕ) (i : Fin d) :
    ∑ j : Fin d, medWeight d (i, j) = (d : ℝ)⁻¹ := by
  unfold medWeight
  simp only
  rw [Finset.sum_ite_eq Finset.univ i (fun _ => (d : ℝ)⁻¹)]
  simp

/-! ### The CHSH-violating 2x2 maximally-entangled sector -/

/-- The Schmidt-block embedding `Fin 2 ↪ Fin d` (indices `0, 1`), available for
`d ≥ 2`. Picks out two Schmidt vectors per side. -/
def sectorEmbed (d : ℕ) (hd : 2 ≤ d) : Fin 2 → Fin d :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt hd⟩

lemma sectorEmbed_injective (d : ℕ) (hd : 2 ≤ d) :
    Function.Injective (sectorEmbed d hd) := by
  intro i j h
  exact Fin.ext (Fin.mk.injEq _ _ _ _ ▸ h)

/-- **The 2x2 sector Born weight in closed form.** On the `{0,1}×{0,1}` Schmidt
block the Born weight is `1/d` on the diagonal (the two Schmidt vectors are the
`Φ⁺` support) and `0` off it — the embedding is injective, so `sectorEmbed i =
sectorEmbed j ↔ i = j`. -/
lemma medWeight_sector (d : ℕ) (hd : 2 ≤ d) (i j : Fin 2) :
    medWeight d (sectorEmbed d hd i, sectorEmbed d hd j)
      = if i = j then (d : ℝ)⁻¹ else 0 := by
  unfold medWeight
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hh => h (sectorEmbed_injective d hd hh))]

/-- **The 2x2 sector diagonal weight.** On the `{0,1}×{0,1}` Schmidt block the
diagonal Born weight is `1/d` (the two Schmidt vectors `(0,0)`, `(1,1)` are the
`Φ⁺` support). -/
lemma maxEntangled_sector_diagonal (d : ℕ) (hd : 2 ≤ d) (i : Fin 2) :
    medWeight d (sectorEmbed d hd i, sectorEmbed d hd i) = (d : ℝ)⁻¹ := by
  rw [medWeight_sector d hd i i, if_pos rfl]

/-- **The 2x2 sector off-diagonal weight.** Off the diagonal the sector Born
weight is `0`; the embedding is injective, so distinct sector indices map to
distinct system indices. -/
lemma maxEntangled_sector_offdiagonal (d : ℕ) (hd : 2 ≤ d) (i j : Fin 2)
    (hij : i ≠ j) :
    medWeight d (sectorEmbed d hd i, sectorEmbed d hd j) = 0 := by
  rw [medWeight_sector d hd i j, if_neg hij]

/-- **The 2x2 sector diagonal Born-weight marginal is uniform (`1/d`).** The
sector diagonal marginal `∑_j medWeight d (sectorEmbed i, sectorEmbed j) = 1/d` is
uniform over the two Schmidt vectors. This is the *diagonal* Born-weight signature
that the `{0,1}×{0,1}` block is (up to the `d`-factor) the two-qubit
maximally-entangled Bell state `Φ⁺`; the full state-level identification of the
sector with `Φ⁺` (coherences included) is `maxEntangledSector_eq_phiPlus`, and the
sector's CHSH violation is `no_product_partition_realises_phiPlus`. -/
lemma maxEntangled_sector_marginal_uniform (d : ℕ) (hd : 2 ≤ d) (i : Fin 2) :
    ∑ j : Fin 2, medWeight d (sectorEmbed d hd i, sectorEmbed d hd j) = (d : ℝ)⁻¹ := by
  simp_rw [medWeight_sector d hd i]
  rw [Finset.sum_ite_eq Finset.univ i (fun _ => (d : ℝ)⁻¹)]
  simp

/-! ### The Bell `Φ⁺` state and the derived sector correlation

The genuine content that makes the non-factorisation `maxEntangled`-specific
(not a verbatim re-export of the singlet no-go): the `{0,1}×{0,1}` Schmidt sector
of `Ψ_d` is *derived* to be the Bell state `Φ⁺ = (|00⟩+|11⟩)/√2`
(`maxEntangledSector_eq_phiPlus`), whose two-qubit Pauli correlation
`⟨Φ⁺|σ·a ⊗ σ·b|Φ⁺⟩ = a_x b_x − a_y b_y + a_z b_z` is computed here from the
Hilbert space (`phiPlus_pauli_correlation`), and whose CHSH violation forces
non-factorisation (`no_product_partition_realises_phiPlus`). -/

/-- **The Bell `Φ⁺` state** `Φ⁺ = (1/√2)(|00⟩ + |11⟩)` on
`EuclideanSpace ℂ (Fin 2 × Fin 2)`, unit-norm, the maximally-entangled symmetric
Bell state. This is the two-qubit sector of `Ψ_d`. -/
noncomputable def phiPlus : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ)
       + EuclideanSpace.single ((1, 1) : Fin 2 × Fin 2) (1 : ℂ))

lemma phiPlus_apply_00 : phiPlus (0, 0) = ((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [phiPlus, EuclideanSpace.single]
lemma phiPlus_apply_01 : phiPlus (0, 1) = 0 := by
  simp [phiPlus, EuclideanSpace.single]
lemma phiPlus_apply_10 : phiPlus (1, 0) = 0 := by
  simp [phiPlus, EuclideanSpace.single]
lemma phiPlus_apply_11 : phiPlus (1, 1) = ((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [phiPlus, EuclideanSpace.single]

/-- `Φ⁺` amplitude in `if i = j` form on the `Fin 2 × Fin 2` sector: `(√2)⁻¹` on
the diagonal (the `(0,0)`, `(1,1)` support), `0` off it. -/
lemma phiPlus_apply_sector (i j : Fin 2) :
    phiPlus (i, j) = if i = j then ((Real.sqrt 2 : ℂ)⁻¹) else 0 := by
  fin_cases i <;> fin_cases j
  · rw [if_pos rfl]; exact phiPlus_apply_00
  · rw [if_neg (by decide)]; exact phiPlus_apply_01
  · rw [if_neg (by decide)]; exact phiPlus_apply_10
  · rw [if_pos rfl]; exact phiPlus_apply_11

/-- Expectation `⟨Φ⁺ | M | Φ⁺⟩` for a `(Fin 2 × Fin 2)`-indexed matrix `M`. -/
noncomputable def phiPlusExpectation (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℂ :=
  inner ℂ phiPlus ((Matrix.toEuclideanLin M) phiPlus)

/-- **`Φ⁺` expectation formula.** On the Bell `Φ⁺` state the expectation of an
arbitrary `(Fin 2 × Fin 2)`-indexed matrix reduces to a half-sum over the four
diagonal-support entries. The 12 of 16 double-sum terms vanish (each has a
`Φ⁺(0,1) = 0` or `Φ⁺(1,0) = 0` factor); the surviving 4 factor through
`((√2)⁻¹)² = 1/2`. Mirrors `LF3.expectation_formula` for `Φ⁺`'s `(0,0)`/`(1,1)`
support. -/
theorem phiPlus_expectation_formula (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    phiPlusExpectation M
      = (1/2 : ℂ) *
          (M (0,0) (0,0) + M (0,0) (1,1) + M (1,1) (0,0) + M (1,1) (1,1)) := by
  unfold phiPlusExpectation
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin,
      dotProduct, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct,
             Fintype.sum_prod_type, Pi.star_apply]
  simp only [show phiPlus.ofLp (0, 0) = ((Real.sqrt 2 : ℂ)⁻¹) from phiPlus_apply_00,
             show phiPlus.ofLp (0, 1) = (0 : ℂ) from phiPlus_apply_01,
             show phiPlus.ofLp (1, 0) = (0 : ℂ) from phiPlus_apply_10,
             show phiPlus.ofLp (1, 1) = ((Real.sqrt 2 : ℂ)⁻¹) from phiPlus_apply_11,
             star_zero,
             show star ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) by
               rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]]
  linear_combination
    (M (0,0) (0,0) + M (0,0) (1,1) + M (1,1) (0,0) + M (1,1) (1,1))
      * CSD.LF3.inv_sqrt_two_sq

/-- **The `Φ⁺` correlation function** in closed form,
`E_{Φ⁺}(a, b) = a_x b_x − a_y b_y + a_z b_z`. `Φ⁺` correlates `σ_x`/`σ_z` and
anti-correlates `σ_y`; this is the derived Pauli expectation
(`phiPlus_pauli_correlation`). -/
noncomputable def phiPlusCorrelation (a b : DetectorSetting) : ℝ :=
  a.vec 0 * b.vec 0 - a.vec 1 * b.vec 1 + a.vec 2 * b.vec 2

/-- **The derived `Φ⁺` two-qubit Pauli correlation** (the load-bearing genuine
computation): `⟨Φ⁺ | σ·a ⊗ σ·b | Φ⁺⟩ = a_x b_x − a_y b_y + a_z b_z`, computed
from the Hilbert space via `phiPlus_expectation_formula` and the `pauliDot`
entries. This is `Φ⁺`'s own correlation, DERIVED — not the singlet's `−a·b`
imported. -/
theorem phiPlus_pauli_correlation (a b : DetectorSetting) :
    phiPlusExpectation (sigmaDotJoint a b) = (phiPlusCorrelation a b : ℂ) := by
  rw [phiPlus_expectation_formula]
  show (1/2 : ℂ) *
      (sigmaDotJoint a b (0,0) (0,0) + sigmaDotJoint a b (0,0) (1,1)
        + sigmaDotJoint a b (1,1) (0,0) + sigmaDotJoint a b (1,1) (1,1)) = _
  simp only [sigmaDotJoint, Matrix.kroneckerMap_apply,
             pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11]
  unfold phiPlusCorrelation
  push_cast
  ring_nf
  rw [show (Complex.I^2 : ℂ) = -1 from Complex.I_sq]
  ring

/-! ### The 2x2 Schmidt sector is the Bell `Φ⁺` state (derived) -/

/-- The `{0,1}×{0,1}` Schmidt sector of `Ψ_d` as a two-qubit vector: the
restriction of `maxEntangled d` to the sector-embedded indices. -/
noncomputable def maxEntangledSector (d : ℕ) (hd : 2 ≤ d) :
    EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun w => (maxEntangled d) (sectorEmbed d hd w.1, sectorEmbed d hd w.2))

/-- Sector amplitude in `if i = j` form: `(√d)⁻¹` on the diagonal, `0` off it (via
the injectivity of `sectorEmbed`). -/
lemma maxEntangled_sector_apply (d : ℕ) (hd : 2 ≤ d) (i j : Fin 2) :
    (maxEntangled d) (sectorEmbed d hd i, sectorEmbed d hd j)
      = if i = j then ((Real.sqrt d : ℂ))⁻¹ else 0 := by
  rw [maxEntangled_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hh => h (sectorEmbed_injective d hd hh))]

/-- **The 2x2 Schmidt sector IS the Bell `Φ⁺` state** (up to the positive real
scalar `√2/√d`): `maxEntangledSector d = (√2/√d) • Φ⁺`. This is the derived,
`d`-dependent, full-state (coherences included) identification of `Ψ_d`'s
`{0,1}×{0,1}` sector with the maximally-entangled `Φ⁺` — the honest link making
the sector's `Φ⁺` correlation genuinely `Ψ_d`'s sector correlation, for every
`d ≥ 2`. -/
theorem maxEntangledSector_eq_phiPlus (d : ℕ) (hd : 2 ≤ d) :
    maxEntangledSector d hd = ((Real.sqrt 2 / Real.sqrt d : ℝ) : ℂ) • phiPlus := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hsqrtd : (Real.sqrt d : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd0)
    exact_mod_cast (ne_of_gt this)
  have hsqrt2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast (ne_of_gt this)
  -- The scalar identity `(√2/√d)·(√2)⁻¹ = (√d)⁻¹` on the diagonal support.
  have hscalar : ((Real.sqrt 2 / Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ)⁻¹)
      = ((Real.sqrt d : ℂ))⁻¹ := by
    rw [Complex.ofReal_div]
    field_simp
  ext w
  obtain ⟨i, j⟩ := w
  show (maxEntangled d) (sectorEmbed d hd i, sectorEmbed d hd j)
      = (((Real.sqrt 2 / Real.sqrt d : ℝ) : ℂ) • phiPlus) (i, j)
  rw [maxEntangled_sector_apply d hd i j, PiLp.smul_apply, phiPlus_apply_sector,
      smul_eq_mul]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, hscalar]
  · rw [if_neg h, if_neg h, mul_zero]

/-! ### The reindexed (nudged) maximally-entangled state -/

/-- The pointer-index identification `(i, j) ↦ Fin (d*d)` tying the LF5 pointer
outcome at `N = d*d` to the bipartite computational basis. -/
def medIdx (d : ℕ) : Fin d × Fin d ≃ Fin (d * d) := finProdFinEquiv

/-- **The prepared state.** `Ψ_d` reindexed to the computational `Fin (d*d)`
basis, `nudgedMaxEntangled d k = (maxEntangled d) (medIdx d |>.symm k)`. For the
minimal computational-basis carve the "nudge" is the identity context; the name
mirrors A.2's `nudgedSinglet` / C.2's `nudgedGHZ`. -/
noncomputable def nudgedMaxEntangled (d : ℕ) : EuclideanSpace ℂ (Fin (d * d)) :=
  WithLp.toLp 2 (fun k => (maxEntangled d) ((medIdx d).symm k))

/-- The pointer-cell coordinate of the nudged state is the `Ψ_d` amplitude. -/
lemma nudgedMaxEntangled_coord (d : ℕ) (w : Fin d × Fin d) :
    (nudgedMaxEntangled d) (medIdx d w) = (maxEntangled d) w := by
  have h : (medIdx d).symm (medIdx d w) = w := Equiv.symm_apply_apply (medIdx d) w
  show (maxEntangled d) ((medIdx d).symm (medIdx d w)) = (maxEntangled d) w
  rw [h]

/-- **The nudge coordinate-Born identity.** The squared computational amplitude of
the nudged state at pointer cell `w` equals the Born weight `medWeight d w` —
composing the reindex-coordinate identity with the computed weights. -/
lemma nudgedMaxEntangled_born (d : ℕ) (w : Fin d × Fin d) :
    ‖inner ℂ (EuclideanSpace.single (medIdx d w) (1 : ℂ)) (nudgedMaxEntangled d)‖ ^ 2
      = medWeight d w := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, nudgedMaxEntangled_coord]
  exact maxEntangled_normSq_eq_weight d w

/-- The pointer-cell squared coordinate as a function of the outcome pair. -/
lemma nudgedMaxEntangled_coord_normSq (d : ℕ) (w : Fin d × Fin d) :
    ‖(nudgedMaxEntangled d) (medIdx d w)‖ ^ 2 = medWeight d w := by
  rw [nudgedMaxEntangled_coord]; exact maxEntangled_normSq_eq_weight d w

/-- **The nudged state is a unit preparation.** `‖φ‖² = ∑_w medWeight d w = 1`.
Discharges the `hψ` hypothesis of the LF5 pointer-volume / frequency theorems. -/
theorem nudgedMaxEntangled_norm (d : ℕ) (hd : 0 < d) : ‖nudgedMaxEntangled d‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ k : Fin (d * d), ‖(nudgedMaxEntangled d) k‖ ^ 2 = 1 := by
    calc ∑ k : Fin (d * d), ‖(nudgedMaxEntangled d) k‖ ^ 2
        = ∑ w : Fin d × Fin d, ‖(nudgedMaxEntangled d) (medIdx d w)‖ ^ 2 :=
          (Equiv.sum_comp (medIdx d) (fun k => ‖(nudgedMaxEntangled d) k‖ ^ 2)).symm
      _ = ∑ w : Fin d × Fin d, medWeight d w :=
          Finset.sum_congr rfl (fun w _ => nudgedMaxEntangled_coord_normSq d w)
      _ = 1 := sum_medWeight d hd
  rw [hsum, Real.sqrt_one]

/-- The nudged state is nonzero. -/
theorem nudgedMaxEntangled_ne_zero (d : ℕ) (hd : 0 < d) : nudgedMaxEntangled d ≠ 0 := by
  intro h
  have := nudgedMaxEntangled_norm d hd
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-! ### Deliverable 1: the flow -/

/-- **The maximally-entangled de-isolation flow** `Φ = measurementFlow (d*d)
finProdFinEquiv` on the dilated projective ontic space `Σ' = ℂℙ^{d²·d²−1}`. This
is the LF5-B von Neumann de-isolation flow instantiated at the bipartite system
`N = d*d`. -/
noncomputable def maxEntangledDeisolationFlow (d : ℕ) [NeZero d] :
    ℙ ℂ (EuclideanSpace ℂ (Fin ((d * d) * (d * d))))
      → ℙ ℂ (EuclideanSpace ℂ (Fin ((d * d) * (d * d)))) :=
  measurementFlow (d * d) finProdFinEquiv

/-- The maximally-entangled de-isolation flow is Fubini-Study measure-preserving
(the Liouville / `hΦ_pres` content), inherited from
`measurementFlow_measurePreserving`. -/
theorem maxEntangledDeisolation_measurePreserving (d : ℕ) [NeZero d]
    (p₀ : CPN ((d * d) * (d * d))) :
    MeasurePreserving (maxEntangledDeisolationFlow d)
      (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  measurementFlow_measurePreserving finProdFinEquiv p₀

/-- The maximally-entangled de-isolation flow is genuinely not the identity for
`d ≥ 2` (`1 < d*d`), inherited from `measurementFlow_ne_id`. -/
theorem maxEntangledDeisolation_ne_id (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    maxEntangledDeisolationFlow d ≠ id := by
  have h : 1 < d * d := by
    have := Nat.mul_le_mul hd hd; omega
  exact measurementFlow_ne_id h finProdFinEquiv

/-! ### Deliverable 2: pointer-block FS volume = Born weight (the headline) -/

/-- **The reproduction (the D headline).** The context-fixed `BornRegion`
pointer-block `w` Fubini-Study volume of the maximally-entangled de-isolation flow
equals the Born weight `medWeight d w`, for the prepared state
`φ = nudgedMaxEntangled d`, for every `d ≥ 1`.

The proof **composes** LF5 `vnDilation_pointer_volume` at `N = d*d` (pointer-block
volume = `‖⟨e_i, φ⟩‖²`, Gleason-free, Born = FS-volume imported from the DH engine)
with the nudge coordinate-Born identity `nudgedMaxEntangled_born` (the
reindex-isometry step + the computed maximally-entangled weights). Dimension-general:
the weights are the real maximally-mixed diagonal `(1/d, …, 1/d)`. -/
theorem maxEntangledDeisolation_pointer_volume (d : ℕ) [NeZero d] {M : ℕ}
    (e : Fin (d * d) × Fin (d * d) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV (d * d)) (nudgedMaxEntangled d)))
    (hψ'0 : ψ' ≠ 0) (w : Fin d × Fin d) :
    ∑ n : Fin (d * d),
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, medIdx d w)))).toReal
      = medWeight d w := by
  rw [← vnDilation_pointer_volume (nudgedMaxEntangled d)
      (nudgedMaxEntangled_norm d (NeZero.pos d)) e p₀ ψ' hψ'eq hψ'0 (medIdx d w)]
  exact nudgedMaxEntangled_born d w

/-! ### Deliverable 3: a.s. pointer-block frequencies → Born weight -/

/-- **The empirical capstone.** For i.i.d. Fubini-Study-typical trials on the
dilated `Σ' = ℂℙ^{d²·d²−1}` (the sector-typicality posit (SO-1) on the enlarged entangled
sector), almost surely every pointer-block `w` empirical frequency converges to
the Born weight `medWeight d w`. Instantiates LF5 `vnDilation_pointer_frequency` at
`N = d*d`, `φ = nudgedMaxEntangled d`, landing the limit on `medWeight` via
`nudgedMaxEntangled_born`. -/
theorem maxEntangledDeisolation_frequency (d : ℕ) [NeZero d] {M : ℕ}
    (e : Fin (d * d) × Fin (d * d) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV (d * d)) (nudgedMaxEntangled d)))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ w : Fin d × Fin d,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin (d * d),
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, medIdx d w)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (medWeight d w)) := by
  filter_upwards [vnDilation_pointer_frequency (nudgedMaxEntangled d)
      (nudgedMaxEntangled_norm d (NeZero.pos d)) e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep]
    with ω hω w
  have h := hω (medIdx d w)
  rwa [nudgedMaxEntangled_born d w] at h

/-! ### Deliverable 4: forced non-factorisation (Bell-forced via the derived Φ⁺ CHSH) -/

/-- The orthogonal `xz`-reflection on detector settings, `reflectXZ (b_x, b_y, b_z)
= (−b_x, b_y, −b_z)`. It is a norm-preserving involution mapping settings to
settings; it carries the `Φ⁺` correlation to the singlet's `−a·b`
(`phiPlusCorrelation_reflectXZ`). -/
def reflectXZ (b : DetectorSetting) : DetectorSetting where
  vec := WithLp.toLp 2 (![-(b.vec 0), b.vec 1, -(b.vec 2)] : Fin 3 → ℝ)
  unit := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [show (-(b.vec 0)) ^ 2 + (b.vec 1) ^ 2 + (-(b.vec 2)) ^ 2
          = b.vec 0 ^ 2 + b.vec 1 ^ 2 + b.vec 2 ^ 2 from by ring,
      b.sum_sq_components_eq_one, Real.sqrt_one]

@[simp] lemma reflectXZ_vec_0 (b : DetectorSetting) : (reflectXZ b).vec 0 = -(b.vec 0) := rfl
@[simp] lemma reflectXZ_vec_1 (b : DetectorSetting) : (reflectXZ b).vec 1 = b.vec 1 := rfl
@[simp] lemma reflectXZ_vec_2 (b : DetectorSetting) : (reflectXZ b).vec 2 = -(b.vec 2) := rfl

/-- **`Φ⁺`'s correlation = the singlet's under the `xz`-reflection of Bob's axis.**
`E_{Φ⁺}(a, b) = −a·(reflectXZ b) = singletCorrelation a (reflectXZ b)`. This is the
`Φ⁺ ↔ ψ⁻` local-unitary transport at the correlation level (an orthogonal
relabeling of Bob's setting), reducing `Φ⁺`'s CHSH to the singlet's. -/
lemma phiPlusCorrelation_reflectXZ (a b : DetectorSetting) :
    phiPlusCorrelation a (reflectXZ b) = singletCorrelation a b := by
  rw [singletCorrelation_eq_neg_dot]
  unfold phiPlusCorrelation dotR
  simp only [reflectXZ_vec_0, reflectXZ_vec_1, reflectXZ_vec_2]
  ring

/-! ### LF6-7: the symmetric-sector `Φ⁺ ↔ ψ⁻` transport recompute

The two Bell correlations were derived by two *independent* Hilbert-space
computations — `Φ⁺`'s here in LF6-D (`phiPlus_pauli_correlation`) and `ψ⁻`'s
separately in LF3 (`LF3.singlet_pauli_correlation`). Here the `xz`-reflection
transport (`phiPlusCorrelation_reflectXZ`, so far only at the correlation-function
level) is lifted to the HILBERT-SPACE expectation level: the singlet's `−a·b` is
recomputed directly from `Φ⁺`'s own expectation, and the two independent
derivations are proved to agree. This consolidates the antisymmetric (`ψ⁻`) sector
as the `reflectXZ`-image of the symmetric (`Φ⁺`) sector — the `Φ⁺ ↔ ψ⁻` transport
recompute that was not yet done in LF6-D. -/

/-- **Transport recompute (Hilbert-space level).** Feeding Bob's `xz`-reflected
setting into `Φ⁺`'s *derived* Pauli expectation recomputes the singlet
correlation: `⟨Φ⁺ | σ·a ⊗ σ·(reflectXZ b) | Φ⁺⟩ = singletCorrelation a b = −a·b`.
The `ψ⁻` value is obtained as a corollary of the `Φ⁺` computation via the
local-unitary (`xz`-reflection) transport, not as a separate derivation. -/
theorem phiPlus_pauli_correlation_reflectXZ (a b : DetectorSetting) :
    phiPlusExpectation (sigmaDotJoint a (reflectXZ b)) = (singletCorrelation a b : ℂ) := by
  rw [phiPlus_pauli_correlation, phiPlusCorrelation_reflectXZ]

/-- **The two independent Bell derivations agree (the LF6-7 consolidation).** The
singlet correlation recomputed from `Φ⁺` via the `xz`-reflection transport equals
the singlet's own Hilbert-space expectation derived separately in LF3
(`LF3.singlet_pauli_correlation`):
`⟨Φ⁺ | σ·a ⊗ σ·(reflectXZ b) | Φ⁺⟩ = ⟨ψ⁻ | σ·a ⊗ σ·b | ψ⁻⟩`. So the
symmetric-sector (`Φ⁺`) computation and the antisymmetric-sector (`ψ⁻`)
computation are the SAME result under `reflectXZ` — the two independently-derived
correlations are one, closing the `Φ⁺ ↔ ψ⁻` sector consolidation. -/
theorem phiPlus_transport_eq_singlet_expectation (a b : DetectorSetting) :
    phiPlusExpectation (sigmaDotJoint a (reflectXZ b))
      = CSD.LF3.expectation (sigmaDotJoint a b) := by
  rw [phiPlus_pauli_correlation_reflectXZ, singletCorrelation_eq_neg_dot,
      CSD.LF3.singlet_pauli_correlation]
  simp only [dotR]
  push_cast
  ring

/-- A product partition **reproduces the `Φ⁺` (sector) correlations** if its
factorisable LHV correlation matches `Φ⁺`'s derived correlation
`E_{Φ⁺}(a, b) = a_x b_x − a_y b_y + a_z b_z` at every pair of settings. -/
def ReproducesPhiPlus {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (RA RB : DetectorSetting → Λ → ℝ) : Prop :=
  ∀ a b, lhvCorrelation μ RA RB a b = phiPlusCorrelation a b

/-- **`no_product_partition_realises_phiPlus` (the sector CHSH violation, derived).**
There is NO product (setting-local, non-contextual) partition of any shared
probability space `(Λ, μ)` whose factorisable correlations reproduce the Bell
`Φ⁺` correlation function `E_{Φ⁺}(a, b) = a_x b_x − a_y b_y + a_z b_z` — the
correlation of `Ψ_d`'s `{0,1}×{0,1}` Schmidt sector (`maxEntangledSector_eq_phiPlus`
+ the derived Pauli expectation `phiPlus_pauli_correlation`).

**Genuinely the sector's own violation, not the singlet's imported.** A product
partition `(RA, RB)` reproducing `Φ⁺` gives, under Bob's `xz`-axis relabeling
`RB' := RB ∘ reflectXZ`, a product partition reproducing the *singlet*
(`phiPlusCorrelation_reflectXZ`: `E_{Φ⁺}(a, reflectXZ b) = −a·b`), contradicting
`no_product_partition_realises_singlet`. The `Φ⁺` correlation is a genuine
orthogonal relabeling of the singlet's `−a·b`, so it violates CHSH at the same
`2√2 > 2`; the violation is derived for `Φ⁺`, not posited. -/
theorem no_product_partition_realises_phiPlus {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (RA RB : DetectorSetting → Λ → ℝ)
    (hPP : IsProductPartition RA RB) (hRep : ReproducesPhiPlus μ RA RB) : False := by
  obtain ⟨hA, hB, hApm, hBpm⟩ := hPP
  -- Relabel Bob's axis by the `xz`-reflection; the relabeled partition reproduces
  -- the singlet, so `no_product_partition_realises_singlet` fires.
  refine no_product_partition_realises_singlet μ RA (fun b => RB (reflectXZ b))
    ⟨hA, fun b => hB (reflectXZ b), hApm, fun b => hBpm (reflectXZ b)⟩ ?_
  intro a b
  have hstep : lhvCorrelation μ RA (fun b => RB (reflectXZ b)) a b
      = lhvCorrelation μ RA RB a (reflectXZ b) := rfl
  rw [hstep, hRep a (reflectXZ b), phiPlusCorrelation_reflectXZ]

/-- **`no_product_partition_realises_maxEntangled` (LF6-D, the thesis-load-bearing
non-factorisation, all `d ≥ 2`).** For every `d ≥ 2`, `Ψ_d`'s `{0,1}×{0,1}`
Schmidt sector IS the Bell `Φ⁺` state (coherences included), and NO product
(setting-local, non-contextual) partition of any shared probability space `(Λ, μ)`
reproduces that sector's correlation function.

**Bell-forced and maxEntangled-specific (derived, not imported).** Conjuncts:
- (a) the sector's diagonal Born-weight marginal is uniform `1/d`
  (`maxEntangled_sector_marginal_uniform`, derived, general `d`);
- (b) the sector IS `Φ⁺` up to the positive scalar `√2/√d`
  (`maxEntangledSector_eq_phiPlus`, full-state identity, coherences included,
  `d`-dependent);
- (c) no product partition reproduces the sector's own `Φ⁺` correlation function
  `E_{Φ⁺}(a, b) = a_x b_x − a_y b_y + a_z b_z` (`no_product_partition_realises_phiPlus`).

Unlike the earlier revision (which re-exported `no_product_partition_realises_singlet`
verbatim on the singlet's `−a·b`, an unused `d`), conjunct (c) is about `Φ⁺`'s own
correlation, which is (i) *derived* from the Hilbert space
(`phiPlus_pauli_correlation`: `⟨Φ⁺|σ·a ⊗ σ·b|Φ⁺⟩ = a_x b_x − a_y b_y + a_z b_z`)
and (ii) *identified* with `Ψ_d`'s sector by (b). The CHSH violation is genuinely
`Φ⁺`'s: an orthogonal relabeling of Bob's axis (`reflectXZ`) carries `E_{Φ⁺}` to
the singlet's `−a·b` (`phiPlusCorrelation_reflectXZ`), so `Φ⁺` violates CHSH at the
same `2√2 > 2`. The non-factorisation is thus Bell-forced *and* maxEntangled-specific.

Scope: non-factorisation forced by the CHSH-violating 2x2 `Φ⁺` sector. This is
superseded for **every** `d ≥ 2` by the genuinely `d`-intrinsic CGLMP violation
(`CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d`,
`CGLMPQudit.cglmp_maxEntangled_qudit_gt_two`), with `d = 3`
(`CGLMPQutrit.cglmp_maxEntangled_qutrit_gt_two`) the concrete qutrit anchor; the
general-`d` CGLMP result is now closed. Residue: A5 (the entangled sector posited). -/
theorem no_product_partition_realises_maxEntangled (d : ℕ) (hd : 2 ≤ d) :
    -- (a) the sector diagonal Born-weight marginal is uniform (derived, general d)
    (∀ i : Fin 2, ∑ j : Fin 2,
        medWeight d (sectorEmbed d hd i, sectorEmbed d hd j) = (d : ℝ)⁻¹)
    -- (b) the sector IS the Bell Φ⁺ state, up to √2/√d (derived, d-dependent)
    ∧ (maxEntangledSector d hd = ((Real.sqrt 2 / Real.sqrt d : ℝ) : ℂ) • phiPlus)
    -- (c) no product partition reproduces the sector's own Φ⁺ correlation (derived)
    ∧ (∀ (_Λ : Type) [MeasurableSpace _Λ] (μ : Measure _Λ) [IsProbabilityMeasure μ]
        (RA RB : DetectorSetting → _Λ → ℝ), IsProductPartition RA RB →
        ReproducesPhiPlus μ RA RB → False) :=
  ⟨fun i => maxEntangled_sector_marginal_uniform d hd i,
   maxEntangledSector_eq_phiPlus d hd,
   fun _Λ _ μ _ RA RB hPP hRep => no_product_partition_realises_phiPlus μ RA RB hPP hRep⟩

/-! ### Deliverable 5: the capstone -/

/-- **The LF6-D capstone: the general d x d maximally-entangled de-isolation
flow.** A deterministic, Fubini-Study-measure-preserving de-isolation flow
`Φ ≠ id` on the dilated `Σ' = ℂℙ^{d²·d²−1}`, for **every** `d ≥ 2`, whose
context-fixed `BornRegion` pointer-block volumes are the maximally-entangled Born
weights `medWeight`, with a.s. block frequencies → the weights, plus the derived
CHSH-violating 2x2 maximally-entangled sector witness and the Bell-forced
non-factorisation. Conjuncts:

1. genuine dynamics, `Φ ≠ id` (`measurementFlow_ne_id`, `1 < d*d`);
2. physically admissible: FS measure-preserving (`measurementFlow_measurePreserving`);
3. pointer-block FS volume = the Born weight, every outcome
   (`maxEntangledDeisolation_pointer_volume`);
4. a.s. block frequencies → the Born weight (`maxEntangledDeisolation_frequency`);
5. the 2x2 Schmidt sector's diagonal Born-weight marginal is uniform `1/d`
   (`maxEntangled_sector_marginal_uniform`, derived, general `d`);
6. the sector IS the Bell `Φ⁺` state up to `√2/√d` (coherences included,
   `maxEntangledSector_eq_phiPlus`, derived, `d`-dependent);
7. the non-factorisation is Bell-forced and maxEntangled-specific: no
   setting-local ±1 product partition reproduces the sector's own derived `Φ⁺`
   correlation `a_x b_x − a_y b_y + a_z b_z` (`no_product_partition_realises_phiPlus`).

For the strictly stronger, **`d`-intrinsic** form of conjunct 7 — non-factorisation
forced directly in dimension `d` by the CGLMP violation `cglmp d (pQM d) > 2`, with
no 2×2 `Φ⁺` sector reduction — see `maxEntangledDeisolation_flow_capstone_cglmp`
(`LF6/MaxEntangledCGLMPCapstone.lean`, fix LF6-1), which inherits conjuncts 1–6
here and swaps only conjunct 7.

Dimension-general (all `d ≥ 2`): the load-bearing "general-N is now general"
content is the de-isolation dynamics + Born-from-volume (conjuncts 1-4). Born =
FS-volume is imported from the DH/FS-volume engine, not re-derived; the flow
realises (not derives) the measurement. Non-factorisation is Bell-forced via the
CHSH-violating 2x2 `Φ⁺` sector (conjuncts 5-7): the sector is *derived* to be `Φ⁺`
(6), whose two-qubit Pauli correlation is *computed* (`phiPlus_pauli_correlation`)
and violates CHSH at `2√2 > 2` (7, via the `reflectXZ` reduction to the singlet).
Residue: A5 (the entangled sector posited). Honest ledger: module docstring. -/
theorem maxEntangledDeisolation_flow_capstone (d : ℕ) [NeZero d] (hd : 2 ≤ d) {M : ℕ}
    (e : Fin (d * d) × Fin (d * d) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV (d * d)) (nudgedMaxEntangled d)))
    (hψ'0 : ψ' ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    -- (1) genuine dynamics
    measurementFlow (d * d) e ≠ id
    -- (2) FS measure-preserving
    ∧ MeasurePreserving (measurementFlow (d * d) e)
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀)
    -- (3) pointer-block FS volume = the Born weight
    ∧ (∀ w : Fin d × Fin d,
        ∑ n : Fin (d * d),
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, medIdx d w)))).toReal
          = medWeight d w)
    -- (4) a.s. block frequencies → the Born weight
    ∧ (∀ᵐ ω ∂ Pr, ∀ w : Fin d × Fin d,
        Tendsto
          (fun m : ℕ =>
            ∑ n : Fin (d * d),
              (∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, medIdx d w)))
                    (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
          atTop
          (nhds (medWeight d w)))
    -- (5) the sector diagonal Born-weight marginal is uniform (derived, general d)
    ∧ (∀ i : Fin 2, ∑ j : Fin 2,
        medWeight d (sectorEmbed d hd i, sectorEmbed d hd j) = (d : ℝ)⁻¹)
    -- (6) the sector IS the Bell Φ⁺ state, up to √2/√d (derived, d-dependent)
    ∧ (maxEntangledSector d hd = ((Real.sqrt 2 / Real.sqrt d : ℝ) : ℂ) • phiPlus)
    -- (7) the non-factorisation is Bell-forced via the sector's own Φ⁺ correlation
    ∧ (∀ (_Λ : Type) [MeasurableSpace _Λ] (μ : Measure _Λ) [IsProbabilityMeasure μ]
        (RA RB : DetectorSetting → _Λ → ℝ), IsProductPartition RA RB →
        ReproducesPhiPlus μ RA RB → False) :=
  ⟨by have h : 1 < d * d := by have := Nat.mul_le_mul hd hd; omega
      exact measurementFlow_ne_id h e,
   measurementFlow_measurePreserving e p₀,
   fun w => maxEntangledDeisolation_pointer_volume d e p₀ ψ' hψ'eq hψ'0 w,
   maxEntangledDeisolation_frequency d e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep,
   fun i => maxEntangled_sector_marginal_uniform d hd i,
   maxEntangledSector_eq_phiPlus d hd,
   fun _Λ _ μ _ RA RB hPP hRep => no_product_partition_realises_phiPlus μ RA RB hPP hRep⟩

end LF6
end CSD


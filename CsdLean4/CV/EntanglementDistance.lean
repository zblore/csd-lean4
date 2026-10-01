/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity
public import CsdLean4.CV.EntangledWeights

/-!
# ST-2: the entanglement distance on the composite arena

**Category:** 3-Local (CV; entanglement geometry at finite dimension). BACKLOG #38, brick `ST-2` of
[`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md).

`ST-1` ([`RecordInfluence.lean`](RecordInfluence.lean)) gave the composite arena a **causal** shape
from the coupling graph. This file gives it a **correlational** one: the mutual information of two
sectors, and the separation functional `d = −log I` that reads it as a distance. The scoping note
prices this as research rather than as something the record layer needs, and says so; it is here
because the author asked for entanglement geometry as a direction.

## Mutual information

* `mutualInfo hpsd = S(ρ_A) + S(ρ_B) − S(ρ_AB)` for a bipartite density, off the two partial traces,
  with `mutualInfo_congr_matrix` (it depends only on the matrix) and
  `vonNeumannEntropy_congr_matrix` underneath;
* ★★ `mutualInfo_nonneg` — **non-negative**, which is subadditivity of the von Neumann entropy
  (`vonNeumannEntropy_subadditive`), with the standard positive-definite support condition on the
  marginals;
* ★★★ `mutualInfo_kronecker` — **a product state carries none**: `I(ρ ⊗ σ) = 0` exactly, because the
  marginals of a product are the factors and the entropy is additive over `⊗`;
* ★★★ `mutualInfo_pureDensity` — **on a pure state the mutual information is twice the entanglement
  entropy**: the joint entropy vanishes (`pureDensity_mul_self`, new) and the two marginals have
  equal entropy (`pure_marginal_entropy_eq`), so `I(A:B) = 2 S(ρ_A)`.

## The distance, and the arena

* `entDist I = −log I` with `I ≤ 0` sent to `⊤`: ★ `entDist_zero` (no correlation, infinitely far),
  ★ `entDist_antitone` (**more correlation is less distance**), ★ `entDist_eq_zero_of_one_le` (a nat
  or more of mutual information puts the sectors at distance zero);
* `compositeDM` — the composite arena point in product coordinates, whose right partial trace is
  the corpus's `reducedDM` (`reducedDM_eq_partialTraceRight`);
* ★★★ `mutualInfo_compositeDM_join` and ★★ `entDist_mutualInfo_join` — **a product point of the
  composite arena carries no mutual information, and its two sectors are infinitely far apart**;
* ★★ `mutualInfoTri_mono` — **enlarging a sector cannot decrease the mutual information**, hence
  cannot increase the distance: `I(A:B) ≤ I(A:BC)`, which is strong subadditivity rearranged.

## Honest scope

⚠️ **`entDist` is a separation functional, not a proved metric.** No triangle inequality is proved
or claimed, here or anywhere in the corpus. Calling `−log I` a "distance" is the physics convention
this file adopts; the properties proved are the three the scoping note asked for — the sign, the
product-point value, and monotonicity — and nothing beyond them.

⚠️ **Monotonicity carries the corpus's SSA hypothesis.** `mutualInfoTri_mono` is
`QuantumInfo.strong_subadditivity_of_relEntropy_monotone` rearranged, so it inherits that theorem's
explicit data-processing bound `hDPI` rather than assuming it silently: the corpus does not prove
SSA unconditionally at this pin, and this file does not pretend otherwise.

⚠️ **This is not geometry from records, and not a step toward emergent spacetime.** It is a
correlation functional on a finite-dimensional composite arena. The scoping note's finding is
unchanged: what is missing for emergence proper is which coarse-graining projection defines the
macroscopic coordinates, and that is the author's decision rather than a lemma. Nothing here feeds
the record layer; `ST-1` is the brick that does.

⚠️ Finite cutoff throughout (`FieldConfig K N`), and the arena statements are about the **join**
(product) points; the entangled case is covered only through `mutualInfo_pureDensity`, as twice a
marginal entropy, with no numerical value computed for any particular entangled ray.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-2`;
`Mathlib/QuantumInfo/{Entropy, Subadditivity, StrongSubadditivity}.lean`;
`CV/{CompositeArena, EntangledWeights}.lean`; `specs/BACKLOG.md` #38.
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ENNReal ComplexOrder Kronecker LinearAlgebra.Projectivization

noncomputable section

namespace CSD.CV

/-! ### Mutual information of a bipartite density -/

section MutualInfo

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Entropy depends only on the matrix, not on the Hermitian witness or on how the matrix is
written. -/
theorem vonNeumannEntropy_congr_matrix {ρ σ : Matrix n n ℂ} (h : ρ = σ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    vonNeumannEntropy hρ = vonNeumannEntropy hσ := by
  subst h
  exact vonNeumannEntropy_congr _ _

/-- **The mutual information** `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)` of a bipartite density, read
off the two partial traces. -/
def mutualInfo {ρ : Matrix (n × m) (n × m) ℂ} (hpsd : ρ.PosSemidef) : ℝ :=
  vonNeumannEntropy (partialTraceRight_isHermitian hpsd.1)
    + vonNeumannEntropy (partialTraceLeft_isHermitian hpsd.1)
    - vonNeumannEntropy hpsd.1

/-- Mutual information depends only on the matrix. -/
theorem mutualInfo_congr_matrix {ρ σ : Matrix (n × m) (n × m) ℂ} (h : ρ = σ)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : mutualInfo hρ = mutualInfo hσ := by
  rw [mutualInfo, mutualInfo,
    vonNeumannEntropy_congr_matrix (congrArg partialTraceRight h)
      (partialTraceRight_isHermitian hρ.1) (partialTraceRight_isHermitian hσ.1),
    vonNeumannEntropy_congr_matrix (congrArg partialTraceLeft h)
      (partialTraceLeft_isHermitian hρ.1) (partialTraceLeft_isHermitian hσ.1),
    vonNeumannEntropy_congr_matrix h hρ.1 hσ.1]

/-- ★★ **Mutual information is non-negative** — subadditivity of the von Neumann entropy, with the
standard positive-definite support condition on the two marginals. -/
theorem mutualInfo_nonneg {ρ : Matrix (n × m) (n × m) ℂ} (hpsd : ρ.PosSemidef)
    (htr : ρ.trace = 1) (hpdA : (partialTraceRight ρ).PosDef)
    (hpdB : (partialTraceLeft ρ).PosDef) :
    0 ≤ mutualInfo hpsd := by
  have h := vonNeumannEntropy_subadditive hpsd htr hpdA hpdB
  rw [vonNeumannEntropy_congr_matrix rfl hpdA.1 (partialTraceRight_isHermitian hpsd.1),
    vonNeumannEntropy_congr_matrix rfl hpdB.1 (partialTraceLeft_isHermitian hpsd.1)] at h
  rw [mutualInfo]
  linarith

/-- ★★★ **A product state carries no mutual information.** The marginals of `ρ ⊗ σ` are `ρ` and `σ`
and the entropy is additive over the tensor product, so `I = 0` exactly. -/
theorem mutualInfo_kronecker {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ}
    (hpsdρ : ρ.PosSemidef) (hpsdσ : σ.PosSemidef) (htrρ : ρ.trace = 1) (htrσ : σ.trace = 1) :
    mutualInfo (hpsdρ.kronecker hpsdσ) = 0 := by
  have hA : partialTraceRight (ρ ⊗ₖ σ) = ρ := by
    rw [partialTraceRight_kronecker, htrσ, one_smul]
  have hB : partialTraceLeft (ρ ⊗ₖ σ) = σ := by
    rw [partialTraceLeft_kronecker, htrρ, one_smul]
  rw [mutualInfo,
    vonNeumannEntropy_congr_matrix hA
      (partialTraceRight_isHermitian (hpsdρ.kronecker hpsdσ).1) hpsdρ.1,
    vonNeumannEntropy_congr_matrix hB
      (partialTraceLeft_isHermitian (hpsdρ.kronecker hpsdσ).1) hpsdσ.1,
    vonNeumannEntropy_congr_matrix rfl (hpsdρ.kronecker hpsdσ).1
      (isHermitian_kronecker hpsdρ.1 hpsdσ.1),
    vonNeumannEntropy_kronecker hpsdρ hpsdσ htrρ htrσ]
  ring

omit [DecidableEq n] [DecidableEq m] in
/-- A unit vector's pure density is a projection. -/
theorem pureDensity_mul_self {ψ : (n × m) → ℂ} (hψ : ∑ p, ‖ψ p‖ ^ 2 = (1 : ℝ)) :
    pureDensity ψ * pureDensity ψ = pureDensity ψ := by
  have hsum : ∑ p, star (ψ p) * ψ p = (1 : ℂ) := by
    have h : ∀ p, star (ψ p) * ψ p = ((‖ψ p‖ ^ 2 : ℝ) : ℂ) := by
      intro p
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    rw [Finset.sum_congr rfl fun p _ => h p, ← Complex.ofReal_sum, hψ, Complex.ofReal_one]
  ext i j
  simp only [pureDensity, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  calc ∑ k, ψ i * star (ψ k) * (ψ k * star (ψ j))
      = (∑ k, star (ψ k) * ψ k) * (ψ i * star (ψ j)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ψ i * star (ψ j) := by rw [hsum, one_mul]

/-- ★★★ **For a pure bipartite state the mutual information is twice the marginal entropy.** The
joint entropy vanishes and the two marginals have equal entropy, so `I(A:B) = 2 S(ρ_A)`: on a pure
state the mutual information *is* the entanglement entropy, doubled. -/
theorem mutualInfo_pureDensity {ψ : (n × m) → ℂ} (hψ : ∑ p, ‖ψ p‖ ^ 2 = (1 : ℝ))
    (hpsd : (pureDensity ψ).PosSemidef) :
    mutualInfo hpsd
      = 2 * vonNeumannEntropy (partialTraceRight_isHermitian hpsd.1) := by
  have htr : (pureDensity ψ).trace = 1 := by
    rw [pureDensity_trace, hψ, Complex.ofReal_one]
  have hzero : vonNeumannEntropy hpsd.1 = 0 :=
    vonNeumannEntropy_eq_zero_of_pure hpsd.1 (pureDensity_mul_self hψ) htr
  have hmarg : vonNeumannEntropy (partialTraceLeft_isHermitian hpsd.1)
      = vonNeumannEntropy (partialTraceRight_isHermitian hpsd.1) := by
    rw [vonNeumannEntropy_congr_matrix rfl (partialTraceLeft_isHermitian hpsd.1)
        (partialTraceLeft_isHermitian (pureDensity_isHermitian ψ)),
      vonNeumannEntropy_congr_matrix rfl (partialTraceRight_isHermitian hpsd.1)
        (partialTraceRight_isHermitian (pureDensity_isHermitian ψ))]
    exact (pure_marginal_entropy_eq ψ).symm
  rw [mutualInfo, hmarg, hzero]
  ring

end MutualInfo

/-! ### The entanglement distance -/

/-- **The entanglement distance** of a mutual information: `d = −log I`, with the vanishing case
sent to `⊤`. Unentangled sectors are infinitely far apart; a mutual information of at least `1`
nat puts them at distance zero. ⚠️ This is a *separation functional*, not a proved metric: no
triangle inequality is claimed anywhere in this file. -/
def entDist (I : ℝ) : ℝ≥0∞ := if I ≤ 0 then ⊤ else ENNReal.ofReal (-Real.log I)

@[simp]
theorem entDist_of_nonpos {I : ℝ} (h : I ≤ 0) : entDist I = ⊤ := by
  rw [entDist, if_pos h]

theorem entDist_zero : entDist 0 = ⊤ := entDist_of_nonpos le_rfl

theorem entDist_of_pos {I : ℝ} (h : 0 < I) : entDist I = ENNReal.ofReal (-Real.log I) := by
  rw [entDist, if_neg (not_le.mpr h)]

/-- ★ **More correlation is less distance**: the distance is antitone in the mutual information. -/
theorem entDist_antitone {I J : ℝ} (hI : 0 < I) (hIJ : I ≤ J) : entDist J ≤ entDist I := by
  rw [entDist_of_pos hI, entDist_of_pos (lt_of_lt_of_le hI hIJ)]
  exact ENNReal.ofReal_le_ofReal (by
    have := Real.log_le_log hI hIJ
    linarith)

/-- ★ A mutual information of a nat or more sits at distance zero. -/
theorem entDist_eq_zero_of_one_le {I : ℝ} (h : 1 ≤ I) : entDist I = 0 := by
  rw [entDist_of_pos (lt_of_lt_of_le zero_lt_one h), ENNReal.ofReal_eq_zero]
  have := Real.log_nonneg h
  linarith

/-! ### On the composite arena -/

variable {K₁ K₂ N : ℕ}

/-- The composite arena density in product coordinates: the matrix whose partial traces are the two
sectors' reduced states. -/
def compositeDM (x : FieldArena (K₁ + K₂) N) :
    Matrix (FieldConfig K₁ N × FieldConfig K₂ N) (FieldConfig K₁ N × FieldConfig K₂ N) ℂ :=
  compositeReindex.symm (arenaDM x)

theorem reducedDM_eq_partialTraceRight (x : FieldArena (K₁ + K₂) N) :
    reducedDM x = partialTraceRight (compositeDM x) := rfl

/-- ★★★ **A product point of the composite arena carries no mutual information.** The join of two
single-sector points has `I = 0`: on the arena, zero mutual information is exactly the
product-point case this theorem names, and the entanglement distance there is infinite. -/
theorem mutualInfo_compositeDM_join (p : FieldArena K₁ N) (q : FieldArena K₂ N)
    (hpsd : (compositeDM (arenaJoin p q)).PosSemidef) :
    mutualInfo hpsd = 0 := by
  have hDM : compositeDM (arenaJoin p q) = arenaDM p ⊗ₖ arenaDM q := by
    rw [compositeDM, arenaDM_join, AlgEquiv.symm_apply_apply]
  refine (mutualInfo_congr_matrix hDM hpsd
    ((arenaDM_posSemidef p).kronecker (arenaDM_posSemidef q))).trans ?_
  exact mutualInfo_kronecker (arenaDM_posSemidef p) (arenaDM_posSemidef q)
    (arenaDM_trace p) (arenaDM_trace q)

/-- ★★ **The two sectors of a product point are infinitely far apart.** -/
theorem entDist_mutualInfo_join (p : FieldArena K₁ N) (q : FieldArena K₂ N)
    (hpsd : (compositeDM (arenaJoin p q)).PosSemidef) :
    entDist (mutualInfo hpsd) = ⊤ := by
  rw [mutualInfo_compositeDM_join p q hpsd, entDist_zero]

/-! ### Monotonicity under sector enlargement -/

/-- ★★ **Enlarging a sector cannot decrease the mutual information**, hence cannot increase the
entanglement distance: `I(A:B) ≤ I(A:BC)`. This is strong subadditivity rearranged, and it carries
the same hypothesis the corpus's SSA carries — the data-processing bound `hDPI`, left explicit
rather than assumed (`QuantumInfo.strong_subadditivity_of_relEntropy_monotone`). -/
theorem mutualInfoTri_mono {a b c : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] {ρ : Matrix (a × b × c) (a × b × c) ℂ}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hpdA : (rhoA ρ).PosDef) (hpdB : (rhoB ρ).PosDef) (hpdBC : (rhoBC ρ).PosDef)
    (hDPI :
      ∀ (hpdA' : (partialTraceRight (rhoAB ρ)).PosDef),
        relEntropy (rhoAB_posSemidef hpsd).1
            (Matrix.PosDef.kronecker hpdA' hpdB).1
          ≤ relEntropy hpsd.1
            (Matrix.PosDef.kronecker hpdA hpdBC).1) :
    vonNeumannEntropy hpdA.1 + vonNeumannEntropy hpdB.1
          - vonNeumannEntropy (rhoAB_posSemidef hpsd).1
      ≤ vonNeumannEntropy hpdA.1 + vonNeumannEntropy hpdBC.1 - vonNeumannEntropy hpsd.1 := by
  have h := strong_subadditivity_of_relEntropy_monotone hpsd htr hpdA hpdB hpdBC hDPI
  linarith

end CSD.CV

end

end

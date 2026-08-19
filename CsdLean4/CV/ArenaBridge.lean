/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.LiebRobinson
public import CsdLean4.Mathlib.QuantumInfo.UnitaryPerturbation
public import CsdLean4.Mathlib.Analysis.Matrix.TrotterProduct
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# P1: the arena bridge — operator locality carried onto the record arena

**Category:** CV (continuous variables — the bridge from mode-local operators to
the projective record arena).

The CV chain states locality as an **operator** notion: `SupportedOn S A`,
commutators, the Lieb-Robinson cone. The record layer's arenas are projective
spaces, where locality is a **measure-and-set** notion. Nothing translated
between the two categories, and on 2026-08-10 that gap made a Lieb-Robinson
bound on record redundancy unstatable (`specs/eft-pillars-plan.md`, P1 — the
twice-observed bottleneck). This module is the translation.

* `FieldArena K N` — `ℙ ℂ (EuclideanSpace ℂ (FieldConfig K N))`, the epistemic
  base over the `K`-mode field.
* `arenaDM p` — the rank-one density of a ray: positive semidefinite
  (`arenaDM_posSemidef`), trace one (`arenaDM_trace`).
* `arenaObs A p = re tr(ρ_p A)` — a matrix observable read as a **function on
  the arena**. `arenaObs_sub_le`: arena observables are 1-Lipschitz in the
  operator norm — this is CR-1's Hölder-lite bound
  (`QuantumInfo.abs_re_trace_mul_le`) doing the category translation.
* `arenaKick U p` — a unitary as an arena self-map, constructed directly
  through `Projectivization.mk` (no `MulAction` instance needed at this index).
* `arenaObs_kick` — **the bridge identity**: `arenaObs A (kick U p)
  = arenaObs (heisenberg U A) p`. Schrödinger on the arena IS Heisenberg on the
  operator, so every operator-norm estimate about Heisenberg evolution becomes a
  sup-norm estimate about functions on the arena.
* ★ `arenaObs_kick_of_disjointSupport` — **statics**: an arena observable of
  mode set `S` is *exactly* invariant under any kick supported on disjoint `T`.
  Haag–Kastler locality (CV-8), restated as a fact about functions on the arena.
* ★★ `arena_lightcone` — **the previously unstatable theorem**: under a
  graph-local skew generator, a kick supported outside the graph `d`-ball of `R`
  changes any region-`R` arena observable after time `t` by at most
  `2·(2‖S‖t)^d/d! · ‖A‖`. The Lieb-Robinson cone (CV-20), now a statement at the
  record-arena level: far-away interventions cannot reach the epistemic regions
  faster than the cone.

⚠️ Honest scope: the **base** arena only — the fibred arenas (`ℂℙ^{N-1} × T²`)
inherit these statements for functions that factor through the base, and the
fibre-active extension is the recorded follow-up. P1's definitional half (a
*field-structured flow* as a structure with a locally-decomposed generator) is
not claimed here; this arc supplies the transport any such definition will be
stated against. `euclidean_norm_map_of_isom` restates LF5's
`toEuclideanLin_norm_map_of_isom` (same proof) to keep CV free of an LF5 import
— rule-of-two note: unify in Mathlib staging when next touched.

## References

`specs/arena-bridge-plan.md` (the feasibility record this executes);
`specs/eft-pillars-plan.md` (P1); `CV/ModeLocality.lean`
(`commute_of_disjointSupport`); `CV/LiebRobinson.lean` (`heisenbergFlow`,
`norm_commutator_spatial_factorial_le`);
`Mathlib/QuantumInfo/UnitaryPerturbation.lean` (CR-1);
`Mathlib/Analysis/Matrix/TrotterProduct.lean` (`exp_mem_unitaryGroup_of_skew`);
`LF2/BornWrapper.lean` (the `outerProduct` pattern this generalises).
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
open scoped LinearAlgebra.Projectivization
open scoped ComplexOrder

namespace CSD.CV

variable {K N : ℕ}

/-! ### The arena -/

/-- **The field arena**: the projective space of the `K`-mode field Hilbert
space — the epistemic base on which records are read. -/
abbrev FieldArena (K N : ℕ) : Type :=
  ℙ ℂ (EuclideanSpace ℂ (FieldConfig K N))

/-- Norm preservation for isometric matrices through `toEuclideanLin`. Same
proof as LF5's `toEuclideanLin_norm_map_of_isom`; restated to keep CV free of an
LF5 import (rule-of-two note in the module docstring). -/
lemma euclidean_norm_map_of_isom {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix κ ι ℂ} (hA : Aᴴ * A = 1)
    (ψ : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin A ψ‖ = ‖ψ‖ := by
  have hinner : inner ℂ (Matrix.toEuclideanLin A ψ) (Matrix.toEuclideanLin A ψ)
      = inner ℂ ψ ψ := by
    rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A),
      show (Matrix.toEuclideanLin A).adjoint = Matrix.toEuclideanLin Aᴴ from
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm,
      show Matrix.toEuclideanLin Aᴴ (Matrix.toEuclideanLin A ψ)
          = Matrix.toEuclideanLin (Aᴴ * A) ψ from by
        simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply],
      hA,
      show Matrix.toEuclideanLin (1 : Matrix ι ι ℂ) = LinearMap.id from
        Matrix.toLpLin_one 2,
      LinearMap.id_apply]
  have hsq : ‖Matrix.toEuclideanLin A ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    exact_mod_cast hinner
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Coordinate sum of squared norms is the squared Euclidean norm. -/
lemma euclid_sum_norm_sq {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) : ∑ i, ‖x i‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  positivity

/-! ### The rank-one density of a ray -/

/-- The **unit representative** of a vector, as a plain function: `v/‖v‖`. -/
noncomputable def unitVec (v : EuclideanSpace ℂ (FieldConfig K N)) :
    FieldConfig K N → ℂ :=
  fun i => ((‖v‖ : ℝ) : ℂ)⁻¹ * v i

/-- The **rank-one density** of a vector: `|v/‖v‖⟩⟨v/‖v‖|`. -/
noncomputable def dmVec (v : EuclideanSpace ℂ (FieldConfig K N)) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  Matrix.vecMulVec (unitVec v) (star (unitVec v))

lemma dmVec_apply (v : EuclideanSpace ℂ (FieldConfig K N))
    (i j : FieldConfig K N) :
    dmVec v i j = unitVec v i * star (unitVec v j) := by
  rw [dmVec, Matrix.vecMulVec_apply, Pi.star_apply]

/-- The rank-one density is positive semidefinite. -/
lemma dmVec_posSemidef (v : EuclideanSpace ℂ (FieldConfig K N)) :
    (dmVec v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (unitVec v)

/-- A complex number times its own star is its squared norm. -/
lemma mul_star_self_eq_norm_sq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The canonical entry form of the density: normalisation outside, raw
coordinates inside. -/
lemma dmVec_apply' {v : EuclideanSpace ℂ (FieldConfig K N)}
    (i j : FieldConfig K N) :
    dmVec v i j = (((‖v‖ ^ 2 : ℝ)) : ℂ)⁻¹ * (v i * star (v j)) := by
  rw [dmVec_apply, unitVec, unitVec]
  simp only [star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [show ((‖v‖ : ℝ) : ℂ)⁻¹ * v i
        * ((((‖v‖ : ℝ) : ℂ))⁻¹ * (starRingEnd ℂ) (v j))
      = (((‖v‖ : ℝ) : ℂ)⁻¹ * ((‖v‖ : ℝ) : ℂ)⁻¹) * (v i * (starRingEnd ℂ) (v j))
      from by ring, ← mul_inv, ← Complex.ofReal_mul, ← sq]

/-- The rank-one density of a nonzero vector has trace one. -/
lemma dmVec_trace {v : EuclideanSpace ℂ (FieldConfig K N)} (hv : v ≠ 0) :
    (dmVec v).trace = 1 := by
  classical
  have hterm : ∀ i, dmVec v i i
      = (((‖v‖ ^ 2 : ℝ)) : ℂ)⁻¹ * ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [dmVec_apply', mul_star_self_eq_norm_sq]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hterm]
  rw [← Finset.mul_sum, show (∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ))
      = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) from by push_cast; rfl,
    euclid_sum_norm_sq]
  rw [inv_mul_cancel₀]
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))

/-- Scale invariance: the density depends only on the ray. -/
lemma dmVec_smul {c : ℂ} (hc : c ≠ 0)
    {v : EuclideanSpace ℂ (FieldConfig K N)} (hv : v ≠ 0) :
    dmVec (c • v) = dmVec v := by
  ext i j
  rw [dmVec_apply', dmVec_apply']
  have hcv : ∀ k, (c • v : EuclideanSpace ℂ (FieldConfig K N)) k = c * v k :=
    fun k => by rw [PiLp.smul_apply, smul_eq_mul]
  have hnc : ‖(c • v : EuclideanSpace ℂ (FieldConfig K N))‖ = ‖c‖ * ‖v‖ :=
    norm_smul c v
  rw [hcv i, hcv j, hnc, star_mul']
  have hcc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := mul_star_self_eq_norm_sq c
  have hcne : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
  have hvne : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
  rw [show ((((‖c‖ * ‖v‖) ^ 2 : ℝ)) : ℂ)
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) from by push_cast; ring,
    mul_inv]
  rw [show c * v i * (star c * star (v j))
      = (c * star c) * (v i * star (v j)) from by ring, hcc]
  rw [show ((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹
        * (((‖c‖ ^ 2 : ℝ) : ℂ) * (v i * star (v j)))
      = (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ((‖c‖ ^ 2 : ℝ) : ℂ))
        * (((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ * (v i * star (v j))) from by ring,
    inv_mul_cancel₀ hcne, one_mul]

/-- **The density of a ray**: `arenaDM p = |p⟩⟨p|` through the canonical
representative — well-defined on the arena by `dmVec_smul`. -/
noncomputable def arenaDM (p : FieldArena K N) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  dmVec p.rep

lemma arenaDM_posSemidef (p : FieldArena K N) : (arenaDM p).PosSemidef :=
  dmVec_posSemidef p.rep

lemma arenaDM_trace (p : FieldArena K N) : (arenaDM p).trace = 1 :=
  dmVec_trace (Projectivization.rep_nonzero p)

/-- The density of `mk v` is the density of `v`: the `rep` choice washes out. -/
lemma arenaDM_mk {v : EuclideanSpace ℂ (FieldConfig K N)} (hv : v ≠ 0) :
    arenaDM (Projectivization.mk ℂ v hv) = dmVec v := by
  have hmk : Projectivization.mk ℂ
        (Projectivization.mk ℂ v hv).rep
        (Projectivization.rep_nonzero _)
      = Projectivization.mk ℂ v hv :=
    Projectivization.mk_rep _
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hmk
  have hane : a ≠ 0 := by
    intro h0
    apply Projectivization.rep_nonzero (Projectivization.mk ℂ v hv)
    rw [← ha, h0, zero_smul]
  rw [arenaDM, ← ha, dmVec_smul hane hv]

/-! ### Arena observables -/

/-- **An operator read as a function on the arena**: `arenaObs A p = re tr(ρ_p A)`
— the expectation of `A` in the ray `p`. This is the object that lives on the
record layer's side of the category divide. -/
noncomputable def arenaObs (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (p : FieldArena K N) : ℝ :=
  RCLike.re ((arenaDM p * A).trace)

/-- ★ **The Lipschitz transport** (CR-1 as the category bridge): arena
observables are 1-Lipschitz in the operator norm. Every operator-norm estimate
becomes a uniform estimate on arena functions through this single inequality. -/
theorem arenaObs_sub_le [NeZero N]
    (A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (p : FieldArena K N) :
    |arenaObs A p - arenaObs B p| ≤ ‖A - B‖ := by
  have hne : Nonempty (FieldConfig K N) := ⟨fun _ => 0⟩
  have hsplit : arenaObs A p - arenaObs B p
      = RCLike.re ((arenaDM p * (A - B)).trace) := by
    rw [arenaObs, arenaObs, Matrix.mul_sub, Matrix.trace_sub, map_sub]
  rw [hsplit]
  have h := QuantumInfo.abs_re_trace_mul_le (arenaDM_posSemidef p) (A - B)
  rwa [arenaDM_trace, show RCLike.re (1 : ℂ) = 1 from by norm_num, mul_one]
    at h

/-! ### Unitary kicks on the arena -/

/-- A unitary sends nonzero vectors to nonzero vectors. -/
lemma toEuclideanLin_ne_zero (U : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    {v : EuclideanSpace ℂ (FieldConfig K N)} (hv : v ≠ 0) :
    Matrix.toEuclideanLin U.val v ≠ 0 := by
  intro h0
  apply hv
  have hU : (U.val)ᴴ * U.val = 1 := by
    have hmem := U.property
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
  have hnorm := euclidean_norm_map_of_isom hU v
  rw [h0, norm_zero] at hnorm
  exact norm_eq_zero.mp hnorm.symm

/-- **A unitary as an arena self-map**, constructed directly through
`Projectivization.mk`. -/
noncomputable def arenaKick (U : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (p : FieldArena K N) : FieldArena K N :=
  Projectivization.mk ℂ (Matrix.toEuclideanLin U.val p.rep)
    (toEuclideanLin_ne_zero U (Projectivization.rep_nonzero p))

/-- Coordinates of the kicked representative: matrix-vector multiplication. -/
lemma toEuclideanLin_coord (M : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (v : EuclideanSpace ℂ (FieldConfig K N)) (i : FieldConfig K N) :
    (Matrix.toEuclideanLin M v) i = (M *ᵥ (fun j => v j)) i := rfl

/-- The kicked density is the conjugated density: `ρ_{U•p} = U ρ_p Uᴴ`. -/
lemma arenaDM_kick (U : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (p : FieldArena K N) :
    arenaDM (arenaKick U p) = U.val * arenaDM p * (U.val)ᴴ := by
  classical
  set v := p.rep with hvdef
  have hv : v ≠ 0 := Projectivization.rep_nonzero p
  have hU : (U.val)ᴴ * U.val = 1 := by
    have hmem := U.property
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
  have hnormeq : ‖Matrix.toEuclideanLin U.val v‖ = ‖v‖ :=
    euclidean_norm_map_of_isom hU v
  rw [arenaKick, arenaDM_mk (toEuclideanLin_ne_zero U hv)]
  ext i j
  -- LHS in canonical form, with the kicked coordinates as mulVec
  have hcoord : ∀ m, (Matrix.toEuclideanLin U.val v) m
      = (U.val *ᵥ (fun k => v k)) m := fun m => rfl
  rw [dmVec_apply', hnormeq, hcoord i, hcoord j]
  -- RHS: expand the double matrix product entrywise
  rw [Matrix.mul_apply]
  have hRHS : ∀ l, (U.val * arenaDM p) i l * (U.val)ᴴ l j
      = (((‖v‖ ^ 2 : ℝ)) : ℂ)⁻¹
        * (((U.val *ᵥ (fun k => v k)) i * star (v l)) * star (U.val j l)) := by
    intro l
    rw [Matrix.conjTranspose_apply, Matrix.mul_apply, arenaDM, ← hvdef]
    rw [Finset.sum_congr rfl fun k _ => by rw [dmVec_apply']]
    rw [show (∑ k, U.val i k
            * ((((‖v‖ ^ 2 : ℝ)) : ℂ)⁻¹ * (v k * star (v l))))
        = (((‖v‖ ^ 2 : ℝ)) : ℂ)⁻¹ * ((U.val *ᵥ (fun k => v k)) i * star (v l))
        from by
      rw [show ((U.val *ᵥ (fun k => v k)) i : ℂ) = ∑ k, U.val i k * v k
          from rfl,
        Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring]
    ring
  rw [Finset.sum_congr rfl fun l _ => hRHS l, ← Finset.mul_sum]
  congr 1
  -- Σ_l (Uv)_i * star(v l) * star(U j l)  =  (Uv)_i * star((Uv)_j)
  rw [show (∑ l, ((U.val *ᵥ (fun k => v k)) i * star (v l)) * star (U.val j l))
      = (U.val *ᵥ (fun k => v k)) i
        * star (∑ l, U.val j l * v l) from by
    rw [star_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [star_mul']; ring]
  rfl

/-- ★ **The bridge identity**: Schrödinger on the arena IS Heisenberg on the
operator. `arenaObs A (U • p) = arenaObs (U† A U) p`, with `heisenberg` the CV
chain's own Heisenberg map — so the entire CV estimate stack applies verbatim to
functions on the arena. -/
theorem arenaObs_kick (U : Matrix.unitaryGroup (FieldConfig K N) ℂ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (p : FieldArena K N) :
    arenaObs A (arenaKick U p) = arenaObs (heisenberg U A) p := by
  rw [arenaObs, arenaObs, arenaDM_kick, heisenberg,
    Matrix.star_eq_conjTranspose]
  congr 1
  rw [Matrix.mul_assoc (U.val * arenaDM p) ((U.val)ᴴ) A,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc (arenaDM p), Matrix.mul_assoc]

/-! ### Statics: exact locality on the arena -/

/-- ★★ **Haag–Kastler locality on the arena** (statics): an arena observable of
mode set `S` is *exactly* invariant under any unitary kick supported on a
disjoint mode set `T`. Not approximately — exactly: the record layer cannot see
disjointly supported interventions at all. -/
theorem arenaObs_kick_of_disjointSupport [NeZero N]
    {S T : Finset (Fin K)} (hST : Disjoint S T)
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn S A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn T W.val)
    (p : FieldArena K N) :
    arenaObs A (arenaKick W p) = arenaObs A p := by
  rw [arenaObs_kick]
  congr 2
  rw [heisenberg]
  have hcomm : A * W.val = W.val * A := commute_of_disjointSupport hST hA hW
  have hWW : star W.val * W.val = 1 := by
    have hmem := W.property
    rwa [Matrix.mem_unitaryGroup_iff'] at hmem
  rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hWW, Matrix.one_mul]

/-! ### Dynamics: the record-arena light cone -/

/-- **The flow as an arena kick**: `exp(t•S)` for skew-Hermitian `S`, packaged
as a unitary. -/
noncomputable def flowU {m : Type*} [Fintype m] [DecidableEq m]
    {S : Matrix m m ℂ} (hS : Sᴴ = -S) (t : ℝ) :
    Matrix.unitaryGroup m ℂ :=
  ⟨exp (t • S), Matrix.exp_mem_unitaryGroup_of_skew
    (Matrix.conjTranspose_real_smul_skew hS t)⟩

/-- The Heisenberg map of the flow kick is the CV chain's `heisenbergFlow`. -/
lemma heisenberg_flowU
    {S : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hS : Sᴴ = -S) (t : ℝ)
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) :
    heisenberg (flowU hS t) A = heisenbergFlow S t A := by
  have hstar : star (exp (t • S)) = exp ((-t) • S) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_real_smul_skew hS t, neg_smul]
  rw [heisenberg, heisenbergFlow, flowU]
  rw [show ((⟨exp (t • S), Matrix.exp_mem_unitaryGroup_of_skew
      (Matrix.conjTranspose_real_smul_skew hS t)⟩ :
        Matrix.unitaryGroup (FieldConfig K N) ℂ)).val = exp (t • S) from rfl,
    hstar]

/-- ★★ **The record-arena light cone** — the theorem that was unstatable before
the bridge. Under a graph-local skew generator, a unitary kick supported outside
the graph `d`-ball of region `R` changes any region-`R` arena observable, after
time `t`, by at most the Lieb-Robinson factorial tail:

  `|arenaObs A (flow t (kick W p)) − arenaObs A (flow t p)| ≤ 2·(2‖S‖t)^d/d!·‖A‖`.

Far-away interventions cannot reach the epistemic regions faster than the cone.
The proof is the bridge run end to end: both sides become Heisenberg statements
(`arenaObs_kick`), the difference becomes a commutator through unitarity, the
commutator is priced by CV-20 (`norm_commutator_spatial_factorial_le`), and the
price crosses back to the arena through CR-1 (`arenaObs_sub_le`). -/
theorem arena_lightcone [NeZero N]
    {E : Finset (Fin K × Fin K)}
    {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    (hS : (∑ e ∈ E, G e)ᴴ = -(∑ e ∈ E, G e))
    {R Y : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn Y W.val)
    {d : ℕ} (hcone : Disjoint (graphBall E R d) Y) {t : ℝ} (ht : 0 ≤ t)
    (p : FieldArena K N) :
    |arenaObs A (arenaKick (flowU hS t) (arenaKick W p))
        - arenaObs A (arenaKick (flowU hS t) p)|
      ≤ 2 * ((2 * ‖∑ e ∈ E, G e‖ * t) ^ d / d.factorial) * ‖A‖ := by
  have hne : Nonempty (FieldConfig K N) := ⟨fun _ => 0⟩
  -- both sides through the bridge (explicit instantiations: `rw` would otherwise
  -- rewrite only the first unifiable occurrence, twice, and miss the second term)
  rw [arenaObs_kick (flowU hS t) A (arenaKick W p),
    arenaObs_kick W (heisenberg (flowU hS t) A) p,
    arenaObs_kick (flowU hS t) A p,
    heisenberg_flowU hS t A]
  -- the difference is Lipschitz-bounded by the conjugation defect
  refine le_trans (arenaObs_sub_le _ _ p) ?_
  set X := heisenbergFlow (∑ e ∈ E, G e) t A with hXdef
  -- the defect is the commutator, through unitarity of W
  have hWW : star W.val * W.val = 1 := by
    have hmem := W.property
    rwa [Matrix.mem_unitaryGroup_iff'] at hmem
  have hdefect : heisenberg W X - X
      = star W.val * (X * W.val - W.val * X) := by
    rw [Matrix.mul_sub, heisenberg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hWW, Matrix.one_mul]
  rw [hdefect]
  have hWs : ‖star W.val‖ = 1 := by
    rw [norm_star]
    exact CStarRing.norm_of_mem_unitary W.property
  calc ‖star W.val * (X * W.val - W.val * X)‖
      ≤ ‖star W.val‖ * ‖X * W.val - W.val * X‖ := norm_mul_le _ _
    _ = ‖X * W.val - W.val * X‖ := by rw [hWs, one_mul]
    _ ≤ 2 * ((2 * ‖∑ e ∈ E, G e‖ * t) ^ d / d.factorial) * ‖A‖ * ‖W.val‖ :=
        norm_commutator_spatial_factorial_le hG hS hA hW hcone ht
    _ = 2 * ((2 * ‖∑ e ∈ E, G e‖ * t) ^ d / d.factorial) * ‖A‖ := by
        rw [CStarRing.norm_of_mem_unitary W.property, mul_one]

end CSD.CV

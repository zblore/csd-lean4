/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TransponderReading

/-!
# The place of what is launched: a transponder without hopping keeps it

**Category:** 7-SigmaLayer. BACKLOG #437 (obligation UO-26, item (2), the place of the
launched part; and what item (3) needs before a receiver at a distance can record).

In every statement of the caused return so far (UD-251 to UD-263) the transponder's
Hamiltonian has one block for each level and each block is a multiple of the identity: the
transponder does not hop. The contact term changes its level and not its site. So the site
of the transponder is conserved by the whole energy, contact term included.

* `diagonal_mul_of_site_preserving`, `siteSetProj_mul_of_site_preserving` — a function of
  the site commutes with every operator that does not move between sites;
* `blockDiagonal_smul_one_apply_of_site_ne` — level energies with no hopping do not;
* `one_kronecker_diagonal`, `one_kronecker_siteSetProj_mul_coincProj`;
* ★★ `one_kronecker_siteSetProj_mul_transponderH` — **the projector on a set of transponder
  sites commutes with the carriers' energy, contact term included**;
* ★★★ `transponder_site_conserved` — **a state with no weight on the transponder sites `B`
  has none at any flow time**: exact, for every strength `g`;
* `mul_neg_I_smul_add_smul_comm`, `levelProj_mul_siteSetProj`, `diagonal_ite_isHermitian`,
  `diagonal_ite_mul_self`, `one_kronecker_siteSetProj_mulVec_prod`;
* ★★★ `transponder_distant_reading_idle` — **a pointer coupled to the transponder's second
  level on sites `B` where the transponder was not prepared counts `0`, on every fibre, with
  the contact term present.**

## What this decides

The record of UD-260 and UD-261 is written where the transponder rests, and by this file it
could not be written anywhere else: with the transponder of UD-251 to UD-263 no receiver at
a distance records the meeting. For a return to travel, the second level has to hop. UA-19
(a) leaves the two levels' masses and the window of momenta open and UA-19 (d) says the
speed is to come from the band of the second level. That band is not in any statement yet,
and with it the level swap no longer commutes with the transponder's Hamiltonian, so the
lower bounds of UD-253 to UD-263 do not carry over as they stand.

## Honest scope

⚠️ **An obstruction for the transponder as built, not for UA-19.** It says the present
Lean objects cannot carry a return to a distance. It says nothing against a second level
with a band.

⚠️ **"Does not move between sites" is a hypothesis on the transponder's Hamiltonian and on
the operator of the contact term**; level energies with no hopping and the level swap meet
it.

⚠️ **The messenger is not constrained**: it moves as before, and the statement is about
the transponder's factor only.

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-19, UO-26,
UD-260, UD-261, UD-263, UD-264); `specs/unified-records-spacetime-task-plans.md` (§9, item
3); `RecordLayer/TransponderReading.lean` (`graphDetector_idle`,
`mul_exp_smul_mulVec_eq_zero`, `arenaObs_proj_kick_toLp`);
`RecordLayer/UnifiedCoincidence.lean` (`coincProj`, `gateOp`,
`coincProj_mul_one_kronecker`); `RecordLayer/GraphDetector.lean` (`siteSetProj`);
`RecordLayer/UnifiedTransponder.lean` (`one_kronecker_mul_compositeH`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix NormedSpace Set MeasureTheory
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator Kronecker

namespace CSD.RecordLayer

/-! ### Functions of the site -/

section Site

variable {m S : Type*} [Fintype m] [DecidableEq m]

/-- A diagonal matrix whose entries depend only on the site commutes with every matrix that
has no entry between different sites. -/
theorem diagonal_mul_of_site_preserving (τ : m → S) {d : m → ℂ}
    (hd : ∀ i j, τ i = τ j → d i = d j) {Y : Matrix m m ℂ}
    (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) : Matrix.diagonal d * Y = Y * Matrix.diagonal d := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : τ i = τ j
  · rw [hd i j h, mul_comm]
  · rw [hY i j h, mul_zero, zero_mul]

/-- The projector on a set of sites commutes with every matrix that has no entry between
different sites. -/
theorem siteSetProj_mul_of_site_preserving (τ : m → S) (B : Set S) [DecidablePred (· ∈ B)]
    {Y : Matrix m m ℂ} (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) :
    siteSetProj τ B * Y = Y * siteSetProj τ B :=
  diagonal_mul_of_site_preserving τ (fun i j h => by simp only [h]) hY

omit [Fintype m] in
/-- A diagonal matrix of zeros and ones is Hermitian. -/
theorem diagonal_ite_isHermitian (p : m → Prop) [DecidablePred p] :
    (Matrix.diagonal fun x => if p x then (1 : ℂ) else 0).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  by_cases hx : p x <;> simp [hx]

/-- A diagonal matrix of zeros and ones is idempotent. -/
theorem diagonal_ite_mul_self (p : m → Prop) [DecidablePred p] :
    (Matrix.diagonal fun x => if p x then (1 : ℂ) else 0)
        * (Matrix.diagonal fun x => if p x then (1 : ℂ) else 0)
      = Matrix.diagonal fun x => if p x then (1 : ℂ) else 0 := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hx : p x <;> simp [hx]

/-- `Π` commuting with `A` and with `Q` commutes with `−i (A + c Q)`. -/
theorem mul_neg_I_smul_add_smul_comm {P A Q : Matrix m m ℂ} (hA : P * A = A * P)
    (hQ : P * Q = Q * P) (c : ℂ) :
    P * ((-Complex.I) • (A + c • Q)) = ((-Complex.I) • (A + c • Q)) * P := by
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, hA, mul_smul_comm, smul_mul_assoc, hQ]

end Site

section Levels

variable {n S : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- Level energies with no hopping have no entry between different sites. -/
theorem blockDiagonal_smul_one_apply_of_site_ne (τ : n × Fin 2 → S) (E : Fin 2 → ℝ) :
    ∀ i j, τ i ≠ τ j →
      Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ)) i j = 0 := by
  intro i j hij
  have hne : i ≠ j := fun h => hij (by rw [h])
  have hd : Matrix.blockDiagonal (fun l : Fin 2 => ((E l : ℝ) : ℂ) • (1 : Matrix n n ℂ))
      = Matrix.diagonal fun x : n × Fin 2 => ((E x.2 : ℝ) : ℂ) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.blockDiagonal_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
    split_ifs <;> simp_all
  rw [hd, Matrix.diagonal_apply_ne _ hne]

/-- A level projector times the projector on a set of sites, as one diagonal matrix. -/
theorem levelProj_mul_siteSetProj (τ : n × Fin 2 → S) (B : Set S) [DecidablePred (· ∈ B)]
    (l : Fin 2) :
    levelProj n l * siteSetProj τ B
      = Matrix.diagonal fun q : n × Fin 2 => if q.2 = l ∧ τ q ∈ B then (1 : ℂ) else 0 := by
  rw [levelProj, siteSetProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext q
  by_cases h1 : q.2 = l <;> by_cases h2 : τ q ∈ B <;> simp [h1, h2]

end Levels

/-! ### The transponder's site is conserved -/

section Conserved

variable {ι n S : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

omit [Fintype ι] [Fintype n] in
/-- The identity on the messenger times a diagonal matrix on the transponder is diagonal. -/
theorem one_kronecker_diagonal (d : n × Fin 2 → ℂ) :
    (1 : Matrix ι ι ℂ) ⊗ₖ Matrix.diagonal d
      = Matrix.diagonal fun p : ι × (n × Fin 2) => d p.2 := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext p
  exact one_mul _

/-- The projector on a set of transponder sites commutes with every coincidence projector. -/
theorem one_kronecker_siteSetProj_mul_coincProj (σ : ι → S) (τ : n × Fin 2 → S)
    (r : S → S → Prop) [DecidableRel r] (B : Set S) [DecidablePred (· ∈ B)] :
    ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) * coincProj σ τ r
      = coincProj σ τ r * ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) := by
  rw [siteSetProj, one_kronecker_diagonal, coincProj, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  exact mul_comm _ _

/-- ★★ **The projector on a set of transponder sites commutes with the carriers' energy,
contact term included.** The transponder's Hamiltonian `C` and the operator `Y` of the
contact term have no entry between different sites; the messenger's Hamiltonian is any. -/
theorem one_kronecker_siteSetProj_mul_transponderH (σ : ι → S) (τ : n × Fin 2 → S)
    (r : S → S → Prop) [DecidableRel r] (B : Set S) [DecidablePred (· ∈ B)]
    (M₀ : Matrix ι ι ℂ) {C Y : Matrix (n × Fin 2) (n × Fin 2) ℂ}
    (hC : ∀ i j, τ i ≠ τ j → C i j = 0) (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (g : ℂ) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) * (compositeH M₀ C + g • gateOp σ τ r Y)
      = (compositeH M₀ C + g • gateOp σ τ r Y) * ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) := by
  have h2 : ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) * ((1 : Matrix ι ι ℂ) ⊗ₖ Y)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ Y) * ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul,
      siteSetProj_mul_of_site_preserving τ B hY]
  have h3 : ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) * gateOp σ τ r Y
      = gateOp σ τ r Y * ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) := by
    rw [gateOp, ← mul_assoc, one_kronecker_siteSetProj_mul_coincProj, mul_assoc, h2,
      ← mul_assoc]
  rw [mul_add, add_mul,
    one_kronecker_mul_compositeH M₀ (siteSetProj_mul_of_site_preserving τ B hC),
    mul_smul_comm, smul_mul_assoc, h3]

/-- ★★★ **The transponder's site is conserved.** The transponder's Hamiltonian and the
operator of the contact term have no entry between different sites. A state with no weight
on the transponder sites `B` has none at any flow time, for every strength `g`. -/
theorem transponder_site_conserved (σ : ι → S) (τ : n × Fin 2 → S)
    (r : S → S → Prop) [DecidableRel r] (B : Set S) [DecidablePred (· ∈ B)]
    (M₀ : Matrix ι ι ℂ) {C Y : Matrix (n × Fin 2) (n × Fin 2) ℂ}
    (hC : ∀ i j, τ i ≠ τ j → C i j = 0) (hY : ∀ i j, τ i ≠ τ j → Y i j = 0) (g : ℂ)
    {Ψ : ι × (n × Fin 2) → ℂ} (hΨ : ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) *ᵥ Ψ = 0)
    (t : ℝ) :
    (((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B)
      * exp (t • ((-Complex.I) • (compositeH M₀ C + g • gateOp σ τ r Y)))) *ᵥ Ψ = 0 := by
  refine mul_exp_smul_mulVec_eq_zero ?_ hΨ t
  rw [mul_smul_comm, smul_mul_assoc,
    one_kronecker_siteSetProj_mul_transponderH σ τ r B M₀ hC hY g]

/-- A product state whose transponder factor vanishes on the sites `B` has no weight
there. -/
theorem one_kronecker_siteSetProj_mulVec_prod (τ : n × Fin 2 → S)
    (B : Set S) [DecidablePred (· ∈ B)] (ψ : ι → ℂ) {φ : n × Fin 2 → ℂ}
    (hφ : ∀ q, τ q ∈ B → φ q = 0) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) *ᵥ (fun y : ι × (n × Fin 2) => ψ y.1 * φ y.2)
      = 0 := by
  rw [siteSetProj, one_kronecker_diagonal]
  funext y
  rw [Matrix.mulVec_diagonal]
  by_cases hy : τ y.2 ∈ B
  · simp [hφ y.2 hy]
  · simp [hy]

variable {f : ℝ → ℝ} {N : ℕ}

/-- ★★★ **No record at a distance from a transponder that does not hop.** A pointer is
coupled to the transponder's second level on the sites `B`. The carriers' energy has any
Hermitian `M₀` for the messenger, a Hermitian transponder Hamiltonian `C` with no entry
between different sites, and the contact term of UA-19 with any strength `g`. From a ready
pointer and the ray of a state with no weight on the transponder sites `B`, on every fibre
of the pointer's conserved angle: the pointer is not displayed at any flow time up to
`t ≥ 0`, and "the pointer has counted `0` at `t`" is a recorded fact of the run's start. -/
theorem transponder_distant_reading_idle (e : ι × (n × Fin 2) ≃ Fin (N + 1)) (σ : ι → S)
    (τ : n × Fin 2 → S) (r : S → S → Prop) [DecidableRel r]
    (hτ : ∀ i j, τ i ≠ τ j → levelSwap n i j = 0) (B : Set S) [DecidablePred (· ∈ B)]
    {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian) {C : Matrix (n × Fin 2) (n × Fin 2) ℂ}
    (hCh : C.IsHermitian) (hC : ∀ i j, τ i ≠ τ j → C i j = 0) (g : ℝ)
    (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f) (p₀ : CPN (N + 1))
    {Ψ : ι × (n × Fin 2) → ℂ} (hΨ : ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) *ᵥ Ψ = 0)
    (hp : (WithLp.toLp 2 Ψ : EuclideanSpace ℂ (ι × (n × Fin 2))) ≠ 0) {θ : KTorus}
    (hθ : θ ∈ readyArc 2) {t : ℝ} (ht : 0 ≤ t) :
    (∀ u, 0 ≤ u → u ≤ t →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy
          (Matrix.reindex e e (compositeH M₀ C + (g : ℂ) • gateOp σ τ r (levelSwap n)))
          (Matrix.reindex e e
            ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B))) hf hc) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∉ displayArc)
      ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e (compositeH M₀ C + (g : ℂ) • gateOp σ τ r (levelSwap n)))
            (Matrix.reindex e e
              ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B))) hf hc)
            p₀).semantics
          [TickReadout.startFact () t 0] := by
  have hV : ((g : ℂ) • gateOp σ τ r (levelSwap n)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul,
      (gateOp_isHermitian σ τ r (levelSwap_isHermitian n) hτ).eq, Complex.star_def,
      Complex.conj_ofReal]
  have hA := (compositeH_isHermitian hM hCh).add hV
  have hQd : (1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B)
      = Matrix.diagonal fun p : ι × (n × Fin 2) =>
        if p.2.2 = 1 ∧ τ p.2 ∈ B then (1 : ℂ) else 0 := by
    rw [levelProj_mul_siteSetProj, one_kronecker_diagonal]
  have hQh : ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B)).IsHermitian := by
    rw [hQd]
    exact diagonal_ite_isHermitian _
  have hQQ : ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B))
      * ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B))
      = (1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B) := by
    rw [hQd]
    exact diagonal_ite_mul_self _
  have hQfac : (1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B)
      = ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) := by
    rw [← Matrix.mul_kronecker_mul, one_mul]
  have hPA := one_kronecker_siteSetProj_mul_transponderH (ι := ι) σ τ r B M₀ hC hτ (g : ℂ)
  have hPQ : ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B)
        * ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B))
      = ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B))
        * ((1 : Matrix ι ι ℂ) ⊗ₖ siteSetProj τ B) := by
    rw [hQd, siteSetProj, one_kronecker_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    exact mul_comm _ _
  refine graphDetector_idle e hA hQh hf hc p₀ hθ ht fun s _ _ => ?_
  have h0 := mul_exp_smul_mulVec_eq_zero
    (mul_neg_I_smul_add_smul_comm hPA hPQ ((hf.lift θ.2 : ℝ) : ℂ)) hΨ s
  rw [arenaObs_proj_kick_toLp hQh hQQ, idxCarrierU_val]
  have hz : (((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B))
      * exp (s • ((-Complex.I) • idxCoupledH
        (compositeH M₀ C + (g : ℂ) • gateOp σ τ r (levelSwap n))
        ((1 : Matrix ι ι ℂ) ⊗ₖ (levelProj n 1 * siteSetProj τ B)) hf θ.2))) *ᵥ Ψ = 0 := by
    rw [hQfac, mul_assoc, ← Matrix.mulVec_mulVec]
    rw [← hQfac]
    exact (congrArg _ h0).trans (Matrix.mulVec_zero _)
  rw [hz]
  simp

end Conserved

end CSD.RecordLayer

end

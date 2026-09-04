/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Uncertainty
public import CsdLean4.Empirical.QM.Contextuality.MerminPeres
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# Empirical/QM: Ozawa's universally valid error–disturbance relation

**Category:** 3-Local (promotion-ready to 2-Framework on demand). QM-generic: no CSD ontology,
pure operator geometry on one inner-product space.

Robertson (`Uncertainty.lean`) bounds the **preparation** spread of two observables in one state.
It says nothing about a measurement's **error** or the **disturbance** it inflicts. The
Heisenberg-microscope reading

  `ε(A)·η(B) ≥ ½ |⟪ψ, [A,B] ψ⟫|`

is quoted constantly and is **not universally valid**: it holds under restrictive extra hypotheses
(unbiased measurements) and fails in general, as Erhart et al. 2012 and Rozema et al. 2012
measured. Ozawa 2003's universally valid replacement is what this module proves:

  ★★ `ozawa_error_disturbance`:  `ε(A)·η(B) + ε(A)·σ(B) + σ(A)·η(B) ≥ ½ |⟪Ψ, [A_in,B_in] Ψ⟫|`

with `σ` the **standard deviations** (`Uncertainty.stdDev`), not variances.

## The shape: four operators on one space, two of which commute

Ozawa's `ε` and `η` are usually introduced through a measurement model `(K, σ_probe, U, M)` on a
tensor product, with `A_in = A ⊗ 1`, `A_out = U†(1 ⊗ M)U`, `B_in = B ⊗ 1`, `B_out = U†(B ⊗ 1)U`.
But the tensor structure plays **no part in the inequality**. What the proof uses is:

* four symmetric operators `A_in, B_in, A_out, B_out` on one space, and
* `Commute A_out B_out` — which in the measurement model holds because `A_out` and `B_out` are
  conjugates *by the same `U`* of `1 ⊗ M` and `B ⊗ 1`, and those commute.

So the theorem is stated at that level (`OzawaData`), and a measurement model is one way to
produce the data. This is deliberate: `Empirical/QM/WignerArakiYanase.lean` states its theorems
over an abstract tensor (`arakiYanase_identity` takes `tensor` with `h_tensor_inner` as a
hypothesis rather than using Mathlib's `⊗[ℂ]`), and `specs/way-theorem-scoping.md` records that
WAY brick 2 shares these definitions. Fixing a concrete tensor here would strand that brick.

## Why the commutation is the whole content

Expanding `[A_out, B_out] = [A_in + N, B_in + D]` with `N = A_out − A_in`, `D = B_out − B_in`
gives four summands, and **the left-hand side is zero**. Hence

  `[A_in, B_in] = −[A_in, D] − [N, B_in] − [N, D]`  (`ozawa_commutator_identity`)

and the three remaining terms are bounded by `2σ(A)η(B)`, `2ε(A)σ(B)`, `2ε(A)η(B)` through one
application each of `Uncertainty.commutator_le_two_mul_norm` — the unsquared Cauchy–Schwarz core,
which exists in that file precisely because Robertson's squared form cannot be summed across three
products. Centring `A_in` and `B_in` does not move the commutator (`commutator_shift`).

## ⚠️ Honest scope

* `ε` and `η` are defined here as **norms** `‖(A_out − A_in) Ψ‖`, `‖(B_out − B_in) Ψ‖`. For
  symmetric operators this is Ozawa's `⟪Ψ, (A_out − A_in)² Ψ⟫^{1/2}` (`error_sq_eq`), so the
  definitions agree; the norm form is what the proof consumes.
* The **naive Heisenberg form is not proved false here**, and no Lean claim is made about it. That
  needs `ε` and `η` computed inside a measurement model. `ozawa_two_term_false` refutes only the
  **two-term** variant `ε·η + ε·σ(B) ≥ ½|⟪[A,B]⟫|`, i.e. it shows the third term is load-bearing.
* The witness inhabits `OzawaData`; a measurement model deriving `A_out = U†(1 ⊗ M)U` from a probe
  is **not** built here (`specs/ozawa-scoping.md` §3a).
* Nothing here is a CSD result. The record-layer stroke is not a measurement model in this sense —
  see `Empirical/CSD/Ozawa.lean`, which states that as a theorem rather than leaving it implied.

## References

`specs/ozawa-scoping.md` (the scoping note, `csd-foundations`-checked; §3a is the vocabulary
decision above, §5 the CSD side); `specs/BACKLOG.md` row B; `Empirical/QM/Uncertainty.lean`
(`commutator_le_two_mul_norm`, `commutator_shift`, `stdDev`, `expectation`, `robertson_uncertainty`);
`Empirical/QM/WignerArakiYanase.lean` (the abstract-tensor interface WAY brick 2 shares, and
`way_hypotheses_satisfiable`, the non-vacuity pattern followed here); `specs/future-work.md` (MT-1);
`specs/qm-empirical-tests.md` (the twins board). Sources: Ozawa 2003, *Phys. Rev. A* **67**, 042105;
Erhart et al. 2012, *Nature Physics* **8**, 185; Rozema et al. 2012, *Phys. Rev. Lett.* **109**,
100404; Branciard 2013, *PNAS* **110**, 6742 (the tight form, not proved here).
-/

@[expose] public section

open ComplexConjugate

namespace CSD
namespace Empirical
namespace Ozawa

open CSD.Empirical.Uncertainty

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### The data the inequality needs -/

/-- **The data of an error–disturbance situation**: the two observables as they enter
(`aIn`, `bIn`) and as the interaction leaves them (`aOut` the meter read-back, `bOut` the
disturbed observable), all symmetric, with `aOut` and `bOut` **commuting**.

In a measurement model `(K, σ_probe, U, M)` this is `A ⊗ 1`, `B ⊗ 1`, `U†(1 ⊗ M)U`, `U†(B ⊗ 1)U`,
and `commute_out` holds because conjugation by one `U` preserves the commutation of `1 ⊗ M` with
`B ⊗ 1`. The tensor structure is not needed anywhere else, so it is not assumed here. -/
structure OzawaData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The measured observable as it enters. -/
  aIn : Module.End ℂ H
  /-- The second observable as it enters. -/
  bIn : Module.End ℂ H
  /-- The meter read-back: what the apparatus reports for `aIn`. -/
  aOut : Module.End ℂ H
  /-- The second observable after the interaction. -/
  bOut : Module.End ℂ H
  /-- Observables are symmetric. -/
  aIn_symm : aIn.IsSymmetric
  /-- Observables are symmetric. -/
  bIn_symm : bIn.IsSymmetric
  /-- The read-back is symmetric. -/
  aOut_symm : aOut.IsSymmetric
  /-- The disturbed observable is symmetric. -/
  bOut_symm : bOut.IsSymmetric
  /-- ★ **The load-bearing hypothesis.** The read-back and the disturbed observable commute —
  in a measurement model, because they are conjugates by the same unitary of the commuting
  `1 ⊗ M` and `B ⊗ 1`. Everything else in this file is formal; this is where the physics is. -/
  commute_out : aOut * bOut = bOut * aOut

namespace OzawaData

variable (d : OzawaData H) (Ψ : H)

/-- The **noise operator** `N = A_out − A_in`. -/
noncomputable def noiseOp : Module.End ℂ H := d.aOut - d.aIn

/-- The **disturbance operator** `D = B_out − B_in`. -/
noncomputable def disturbOp : Module.End ℂ H := d.bOut - d.bIn

/-- **Ozawa's error** `ε(A) = ‖(A_out − A_in) Ψ‖`. -/
noncomputable def error : ℝ := ‖d.noiseOp Ψ‖

/-- **Ozawa's disturbance** `η(B) = ‖(B_out − B_in) Ψ‖`. -/
noncomputable def disturbance : ℝ := ‖d.disturbOp Ψ‖

lemma error_nonneg : 0 ≤ d.error Ψ := norm_nonneg _

lemma disturbance_nonneg : 0 ≤ d.disturbance Ψ := norm_nonneg _

lemma noiseOp_symm : (d.noiseOp).IsSymmetric := fun x y => by
  simp only [noiseOp, LinearMap.sub_apply, inner_sub_left, inner_sub_right,
    d.aOut_symm x y, d.aIn_symm x y]

lemma disturbOp_symm : (d.disturbOp).IsSymmetric := fun x y => by
  simp only [disturbOp, LinearMap.sub_apply, inner_sub_left, inner_sub_right,
    d.bOut_symm x y, d.bIn_symm x y]

/-- The norm definition agrees with Ozawa's quadratic one: `ε(A)² = ⟪Ψ, (A_out − A_in)² Ψ⟫`.
(Real part taken because the inner product is `ℂ`-valued; symmetry makes it real.) -/
lemma error_sq_eq : (d.error Ψ) ^ 2 = (inner ℂ Ψ ((d.noiseOp * d.noiseOp) Ψ)).re := by
  rw [Module.End.mul_apply, ← d.noiseOp_symm Ψ (d.noiseOp Ψ)]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- Likewise for the disturbance: `η(B)² = ⟪Ψ, (B_out − B_in)² Ψ⟫`. -/
lemma disturbance_sq_eq :
    (d.disturbance Ψ) ^ 2 = (inner ℂ Ψ ((d.disturbOp * d.disturbOp) Ψ)).re := by
  rw [Module.End.mul_apply, ← d.disturbOp_symm Ψ (d.disturbOp Ψ)]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

end OzawaData

/-! ### The algebraic identity: the fourth term vanishes -/

/-- ★ **The identity the theorem rests on.** With `N = A_out − A_in` and `D = B_out − B_in`,
expanding `[A_out, B_out]` gives four summands — and the left-hand side is **zero** by
`commute_out`, so

  `[A_in, B_in] = −[A_in, D] − [N, B_in] − [N, D]`.

Each remaining commutator pairs a *measurement* quantity with a *preparation* quantity, which is
exactly the shape of Ozawa's three terms. Without the commutation the residue is `[A_out, B_out]`,
a term containing neither `ε` nor `η`, and no bound in those quantities can follow. -/
theorem ozawa_commutator_identity (d : OzawaData H) :
    d.aIn * d.bIn - d.bIn * d.aIn
      = -(d.aIn * d.disturbOp - d.disturbOp * d.aIn)
        - (d.noiseOp * d.bIn - d.bIn * d.noiseOp)
        - (d.noiseOp * d.disturbOp - d.disturbOp * d.noiseOp) := by
  have h := d.commute_out
  simp only [OzawaData.noiseOp, OzawaData.disturbOp, mul_sub, sub_mul]
  -- everything is linear; the `aOut * bOut` terms cancel through `commute_out`
  abel_nf
  rw [h]
  abel

/-! ### The relation -/

/-- ★★ **Ozawa's universally valid error–disturbance relation** (Ozawa 2003).

  `ε(A)·η(B) + ε(A)·σ(B) + σ(A)·η(B) ≥ ½ |⟪Ψ, [A_in, B_in] Ψ⟫|`

Three Cauchy–Schwarz bounds on the three terms of `ozawa_commutator_identity`, after centring
`A_in` and `B_in` (which does not move the commutator). Each term pairs a measurement quantity
with a preparation quantity; the pure-preparation product `σ(A)·σ(B)` appears in **none** of them,
which is why this neither implies nor follows from Robertson. -/
theorem ozawa_error_disturbance (d : OzawaData H) (Ψ : H) :
    d.error Ψ * d.disturbance Ψ
        + d.error Ψ * stdDev d.bIn Ψ
        + stdDev d.aIn Ψ * d.disturbance Ψ
      ≥ (1 / 2) * ‖inner ℂ Ψ ((d.aIn * d.bIn - d.bIn * d.aIn) Ψ)‖ := by
  classical
  -- centred input observables; the commutator is unchanged by the shift
  set a := d.aIn - (expectation d.aIn Ψ) • (1 : Module.End ℂ H) with ha_def
  set b := d.bIn - (expectation d.bIn Ψ) • (1 : Module.End ℂ H) with hb_def
  have ha_symm : a.IsSymmetric :=
    isSymmetric_sub_smul_one d.aIn_symm (expectation_conj d.aIn d.aIn_symm Ψ)
  have hb_symm : b.IsSymmetric :=
    isSymmetric_sub_smul_one d.bIn_symm (expectation_conj d.bIn d.bIn_symm Ψ)
  have ha_norm : ‖a Ψ‖ = stdDev d.aIn Ψ := by
    rw [ha_def, stdDev, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hb_norm : ‖b Ψ‖ = stdDev d.bIn Ψ := by
    rw [hb_def, stdDev, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  -- the three bounds
  have h1 : ‖inner ℂ Ψ ((d.aIn * d.disturbOp - d.disturbOp * d.aIn) Ψ)‖
      ≤ 2 * (stdDev d.aIn Ψ * d.disturbance Ψ) := by
    have hshift : d.aIn * d.disturbOp - d.disturbOp * d.aIn = a * d.disturbOp - d.disturbOp * a := by
      rw [ha_def]
      have := commutator_shift d.aIn d.disturbOp (expectation d.aIn Ψ) 0
      simpa using this.symm
    rw [hshift, ← ha_norm]
    simpa [OzawaData.disturbance] using
      commutator_le_two_mul_norm a d.disturbOp ha_symm d.disturbOp_symm Ψ
  have h2 : ‖inner ℂ Ψ ((d.noiseOp * d.bIn - d.bIn * d.noiseOp) Ψ)‖
      ≤ 2 * (d.error Ψ * stdDev d.bIn Ψ) := by
    have hshift : d.noiseOp * d.bIn - d.bIn * d.noiseOp = d.noiseOp * b - b * d.noiseOp := by
      rw [hb_def]
      have := commutator_shift d.noiseOp d.bIn 0 (expectation d.bIn Ψ)
      simpa using this.symm
    rw [hshift, ← hb_norm]
    simpa [OzawaData.error] using
      commutator_le_two_mul_norm d.noiseOp b d.noiseOp_symm hb_symm Ψ
  have h3 : ‖inner ℂ Ψ ((d.noiseOp * d.disturbOp - d.disturbOp * d.noiseOp) Ψ)‖
      ≤ 2 * (d.error Ψ * d.disturbance Ψ) := by
    simpa [OzawaData.error, OzawaData.disturbance] using
      commutator_le_two_mul_norm d.noiseOp d.disturbOp d.noiseOp_symm d.disturbOp_symm Ψ
  -- collect through the identity
  have hid := ozawa_commutator_identity d
  have hval : inner ℂ Ψ ((d.aIn * d.bIn - d.bIn * d.aIn) Ψ)
      = -(inner ℂ Ψ ((d.aIn * d.disturbOp - d.disturbOp * d.aIn) Ψ)
          + inner ℂ Ψ ((d.noiseOp * d.bIn - d.bIn * d.noiseOp) Ψ)
          + inner ℂ Ψ ((d.noiseOp * d.disturbOp - d.disturbOp * d.noiseOp) Ψ)) := by
    rw [hid]
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, inner_sub_right, inner_neg_right]
    ring
  rw [ge_iff_le, hval, norm_neg]
  have htri := norm_add₃_le (a := inner ℂ Ψ ((d.aIn * d.disturbOp - d.disturbOp * d.aIn) Ψ))
    (b := inner ℂ Ψ ((d.noiseOp * d.bIn - d.bIn * d.noiseOp) Ψ))
    (c := inner ℂ Ψ ((d.noiseOp * d.disturbOp - d.disturbOp * d.noiseOp) Ψ))
  linarith

/-! ### Non-vacuity, and the two-term variant

`way_hypotheses_satisfiable` is the pattern followed here: exhibit the data, and exhibit it
where the statement has content. What would make the relation vacuous is a **vanishing
right-hand side** — `⟪Ψ,[A_in,B_in]Ψ⟫ = 0` leaves `0 ≤ (nonneg)`. It is NOT `ε = 0`: that is the
sharpest case, an exact measurement forcing disturbance, and it is exactly the case exhibited
below.

⚠️ This inhabits `OzawaData`, which is what the theorem quantifies over. A full measurement-model
instantiation — probe space, `U`, and `A_out = U†(1 ⊗ M)U` derived rather than posited — is **not
built here**; `specs/ozawa-scoping.md` §3a records why the module is stated at the `OzawaData`
level in the first place. -/

open CSD.Empirical.MerminPeres (sigmaZ sigmaX)

/-- The `+1` eigenvector of `σ_y`, unnormalised: `(1, i)`. -/
noncomputable def yPlus : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, Complex.I]

lemma sigmaZ_isHermitian : sigmaZ.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaZ, Matrix.conjTranspose]

lemma sigmaX_isHermitian : sigmaX.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaX, Matrix.conjTranspose]

/-- **The witness**: `A_in = σ_z` measured *exactly* (`A_out = σ_z`, so `ε = 0`), with
`B_in = σ_x` disturbed to `B_out = σ_z`. `commute_out` is immediate because `A_out` and `B_out`
are the same operator. -/
noncomputable def zxWitness : OzawaData (EuclideanSpace ℂ (Fin 2)) where
  aIn := Matrix.toEuclideanLin sigmaZ
  bIn := Matrix.toEuclideanLin sigmaX
  aOut := Matrix.toEuclideanLin sigmaZ
  bOut := Matrix.toEuclideanLin sigmaZ
  aIn_symm := Matrix.isSymmetric_toEuclideanLin_iff.symm.mp sigmaZ_isHermitian
  bIn_symm := Matrix.isSymmetric_toEuclideanLin_iff.symm.mp sigmaX_isHermitian
  aOut_symm := Matrix.isSymmetric_toEuclideanLin_iff.symm.mp sigmaZ_isHermitian
  bOut_symm := Matrix.isSymmetric_toEuclideanLin_iff.symm.mp sigmaZ_isHermitian
  commute_out := rfl

/-- The measurement is exact: `ε(σ_z) = 0`. -/
@[simp] lemma zxWitness_error (Ψ : EuclideanSpace ℂ (Fin 2)) : zxWitness.error Ψ = 0 := by
  show ‖(zxWitness.aOut - zxWitness.aIn) Ψ‖ = 0
  simp [zxWitness]

/-- ★ **Non-vacuity: the right-hand side is nonzero.** `⟪y₊, [σ_z, σ_x] y₊⟫ = 4i`, so the bound
`ozawa_error_disturbance` asserts at this datum is a strictly positive lower bound, not `0 ≤ 0`. -/
theorem zxWitness_commutator_ne_zero :
    inner ℂ yPlus ((zxWitness.aIn * zxWitness.bIn - zxWitness.bIn * zxWitness.aIn) yPlus)
      = (4 : ℂ) * Complex.I := by
  have hop : (zxWitness.aIn * zxWitness.bIn - zxWitness.bIn * zxWitness.aIn)
      = Matrix.toEuclideanLin (sigmaZ * sigmaX - sigmaX * sigmaZ) := by
    simp [zxWitness, map_sub]
    rfl
  rw [hop]
  simp [yPlus, sigmaZ, sigmaX, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
  ring

/-- ★ **The two-term variant is false.** Dropping `σ(A)·η(B)` from Ozawa's relation leaves
`ε(A)·η(B) + ε(A)·σ(B) ≥ ½|⟪Ψ,[A_in,B_in]Ψ⟫|`, which the witness refutes: its left-hand side is
`0` (the measurement is exact) while the right-hand side is `2`.

This is **not** a refutation of the naive Heisenberg form `ε·η ≥ ½|⟪[A,B]⟫|` — that needs `ε` and
`η` computed inside a measurement model, and is deliberately out of scope
(`specs/ozawa-scoping.md` §2). It does show that the third term is load-bearing. -/
theorem ozawa_two_term_false :
    ¬ ∀ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (d : OzawaData H) (Ψ : H),
        d.error Ψ * d.disturbance Ψ + d.error Ψ * stdDev d.bIn Ψ
          ≥ (1 / 2) * ‖inner ℂ Ψ ((d.aIn * d.bIn - d.bIn * d.aIn) Ψ)‖ := by
  intro h
  have hw := h (EuclideanSpace ℂ (Fin 2)) inferInstance inferInstance zxWitness yPlus
  rw [zxWitness_error, zxWitness_commutator_ne_zero] at hw
  have : ‖(4 : ℂ) * Complex.I‖ = 4 := by
    rw [norm_mul, Complex.norm_I, mul_one]; norm_num
  rw [this] at hw
  norm_num at hw

end Ozawa
end Empirical
end CSD

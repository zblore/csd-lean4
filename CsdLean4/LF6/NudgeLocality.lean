/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Spinor
public import CsdLean4.LF3.Singlet.JointProjector

/-!
# LF6/NudgeLocality: the setting-dependent nudge, done locally

**Category:** 6-Entanglement (the local half of the setting-dependent chain).

## Why this exists

`SingletDeisolationFlow.nudgedSinglet` is documented as the singlet "transformed
by local basis rotations". **That is false.** Inside `singletJointEig_born`,

    inner ℂ singlet (singletJointEig s t a b) = (Real.sqrt (P_st a b s t) : ℂ)

so `nudgedSinglet a b` is the vector `(√P_st)_{s,t}` — all real, all
non-negative, **every phase stripped**. Local unitaries preserve Schmidt spectra
and `ψ⁻` is maximally entangled; but at `a ⊥ b` all four `P_st = ¼`, so
`nudgedSinglet = ½(1,1,1,1)`, a **product state**. No local unitary carries a
maximally entangled state to a product state, so `nudgedSinglet` is a
local-unitary image of `ψ⁻` only at `a·b = ±1` — exactly the endpoint set the
`hgen` hypothesis excludes.

The defect is in `singletJointEig := (√P_st)⁻¹ • (Πˢ(a) ⊗ Πᵗ(b)) ψ⁻`, which fixes
each basis vector's phase by projecting `ψ⁻` itself: four independent phases,
where a product unitary supplies only separable ones (`αₛ + βₜ`).

## What this module does

`localNudge` is the object `nudgedSinglet` was described as being. It is
**defined** as the action of a product unitary on the singlet, so locality is
definitional rather than asserted, and there is no phase to get wrong:

    localNudge a b := (U_A(a) ⊗ U_B(b))ᴴ ψ⁻

with `U_A(a) = wingBasisUnitary a` proved unitary in `LF3/Spinor.lean`.

* `localNudge_coord` — its `(k,l)` coordinate is `⟨u ⊗ w, ψ⁻⟩`.
* ★★ `localNudge_born` — `‖coordinate‖² = P_st`, with **no genericity
  hypothesis**. So `localNudge` reproduces exactly the Born statistics
  `nudgedSinglet` was used for, while genuinely being a local-unitary image of
  the singlet.

## References

`LF3/Spinor.lean` (`spinor`, `wingBasisUnitary`, `spinProj_eq_outer`,
`jointSpinProj_eq_outer`); `LF3/Singlet/JointProjector.lean`
(`singlet_jointSpinProj_expectation`); `LF6/SingletDeisolationFlow.lean` (the
object this replaces); `specs/c1-correction-plan.md` §3b.
-/

@[expose] public section

open Matrix Complex
open CSD.LF3

namespace CSD.LF6

/-- **The product unitary** `U_A(a) ⊗ U_B(b)` implementing the setting change. -/
noncomputable def wingPairUnitary (a b : DetectorSetting) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (wingBasisUnitary a) (wingBasisUnitary b)

/-- ★ **The nudge, done locally.** The singlet rotated into the `(a,b)`
eigenbasis by a **product** unitary. Locality is definitional. -/
noncomputable def localNudge (a b : DetectorSetting) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  Matrix.toEuclideanLin (wingPairUnitary a b)ᴴ singlet

/-- The `(k,l)` coordinate of the local nudge is the overlap of the singlet with
the product eigenvector `u ⊗ w`. -/
lemma localNudge_coord (a b : DetectorSetting) (k l : Fin 2) :
    localNudge a b (k, l)
      = inner ℂ (WithLp.toLp 2 (spinorPair (signOfFin k) (signOfFin l) a b)
          : EuclideanSpace ℂ (Fin 2 × Fin 2)) singlet := by
  rw [localNudge, PiLp.inner_apply]
  show ((wingPairUnitary a b)ᴴ *ᵥ singlet) (k, l) = _
  rw [Matrix.mulVec]
  simp only [dotProduct, Matrix.conjTranspose_apply, wingPairUnitary,
    Matrix.kroneckerMap_apply, wingBasisUnitary, Matrix.of_apply, spinorPair,
    RCLike.inner_apply, map_mul]
  exact Finset.sum_congr rfl (fun i _ => by rw [RCLike.star_def, map_mul]; ring)

/-! ### The Born identity on the local object -/

/-- For a rank-one `M = v vᴴ`, the singlet expectation is `|⟨v, ψ⁻⟩|²`. -/
lemma expectation_of_outer (v : Fin 2 × Fin 2 → ℂ)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hM : ∀ I J, M I J = v I * star (v J)) :
    expectation M
      = (starRingEnd ℂ) (inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 2 × Fin 2)) singlet)
        * inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 2 × Fin 2)) singlet := by
  set c := inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 2 × Fin 2)) singlet with hc
  have hrow : ∀ I : Fin 2 × Fin 2, ((Matrix.toEuclideanLin M) singlet) I = v I * c := by
    intro I
    show (M *ᵥ singlet) I = _
    rw [Matrix.mulVec, dotProduct, hc, PiLp.inner_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun J _ => by
      rw [hM I J, RCLike.inner_apply, RCLike.star_def]; ring)
  rw [expectation, PiLp.inner_apply]
  simp only [hrow, RCLike.inner_apply]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    show v x * c * (starRingEnd ℂ) (singlet x)
      = c * (v x * (starRingEnd ℂ) (singlet x)) from by ring), ← Finset.mul_sum, mul_comm]
  congr 1
  rw [hc, PiLp.inner_apply, map_sum]
  exact Finset.sum_congr rfl (fun I _ => by
    rw [RCLike.inner_apply, map_mul, Complex.conj_conj]; ring)

/-- ★★ **The Born identity for the local nudge**, with **no genericity
hypothesis**: the squared modulus of the `(k,l)` coordinate is the singlet kernel
`P_st`.

So `localNudge` reproduces exactly the statistics `nudgedSinglet` was used for,
while — unlike `nudgedSinglet` — genuinely being the image of `ψ⁻` under a
product unitary. -/
theorem localNudge_born (a b : DetectorSetting) (k l : Fin 2) :
    ‖localNudge a b (k, l)‖ ^ 2 = P_st a b (signOfFin k) (signOfFin l) := by
  have hexp := singlet_jointSpinProj_expectation (signOfFin k) (signOfFin l) a b
  have houter := expectation_of_outer (spinorPair (signOfFin k) (signOfFin l) a b)
    (jointSpinProj (signOfFin k) (signOfFin l) a b)
    (jointSpinProj_eq_outer (signOfFin k) (signOfFin l) a b)
  rw [hexp] at houter
  rw [localNudge_coord]
  set c := inner ℂ (WithLp.toLp 2 (spinorPair (signOfFin k) (signOfFin l) a b)
    : EuclideanSpace ℂ (Fin 2 × Fin 2)) singlet with hcdef
  have h1 : ((P_st a b (signOfFin k) (signOfFin l) : ℝ) : ℂ) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [houter, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  exact (Complex.ofReal_inj.mp h1).symm

end CSD.LF6


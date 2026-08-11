/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Spinor
public import CsdLean4.LF3.Singlet.JointProjector
public import CsdLean4.LF6.SingletDeisolationFlow
public import CsdLean4.LF6.LocalDeisolationFlow
public import CsdLean4.LF3.OperationalNoSignalling

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

open Matrix Complex MeasureTheory Matrix.UnitaryGroup
open scoped ENNReal Kronecker LinearAlgebra.Projectivization
open CSD.LF3

namespace CSD.LF6

open CSD.LF2 CSD.LF4 CSD.LF5

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

/-! ### Transport to the `Fin 4` pointer indexing

The downstream volume machinery indexes pointer cells by `Fin 4` through
`stIdx`. This carries `localNudge` across, so it is a drop-in replacement for
`nudgedSinglet` — with the genericity hypothesis gone. -/

lemma signOfFin_signEquiv (s : Sign) : signOfFin (signEquiv s) = s := by
  cases s <;> rfl

/-- The local nudge in the `Fin 4` pointer indexing. -/
noncomputable def localNudgeVec (a b : DetectorSetting) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun k =>
    localNudge a b (signEquiv (stIdx.symm k).1, signEquiv (stIdx.symm k).2))

/-- ★ **The pointer-cell Born identity, with no genericity hypothesis.**
Compare `nudgedSinglet_coord_normSq`, which needs `hgen`. -/
lemma localNudgeVec_coord_normSq (a b : DetectorSetting) (st : Sign × Sign) :
    ‖localNudgeVec a b (stIdx st)‖ ^ 2 = P_st a b st.1 st.2 := by
  obtain ⟨s, t⟩ := st
  show ‖localNudge a b (signEquiv (stIdx.symm (stIdx (s, t))).1,
    signEquiv (stIdx.symm (stIdx (s, t))).2)‖ ^ 2 = _
  rw [Equiv.symm_apply_apply, localNudge_born, signOfFin_signEquiv, signOfFin_signEquiv]

/-- ★ **Unit norm, with no genericity hypothesis.** Compare
`nudgedSinglet_norm`, which needs `hgen`. -/
theorem localNudgeVec_norm (a b : DetectorSetting) : ‖localNudgeVec a b‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ k : Fin 4, ‖(localNudgeVec a b) k‖ ^ 2 = 1 := by
    calc ∑ k : Fin 4, ‖(localNudgeVec a b) k‖ ^ 2
        = ∑ st : Sign × Sign, ‖(localNudgeVec a b) (stIdx st)‖ ^ 2 :=
          (Equiv.sum_comp stIdx (fun k => ‖(localNudgeVec a b) k‖ ^ 2)).symm
      _ = ∑ st : Sign × Sign, P_st a b st.1 st.2 :=
          Finset.sum_congr rfl (fun st _ => localNudgeVec_coord_normSq a b st)
      _ = 1 := sum_P_st_eq_one a b
  rw [hsum, Real.sqrt_one]

/-- ★ **The pointer-cell Born identity in single-basis form**, matching
`basisPOVM_weight`. No genericity hypothesis. -/
lemma localNudgeVec_born (a b : DetectorSetting) (s t : Sign) :
    ‖inner ℂ (EuclideanSpace.single (stIdx (s, t)) (1 : ℂ)) (localNudgeVec a b)‖ ^ 2
      = P_st a b s t := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  exact localNudgeVec_coord_normSq a b (s, t)

/-- The local nudge is nonzero, with no genericity hypothesis. -/
theorem localNudgeVec_ne_zero (a b : DetectorSetting) : localNudgeVec a b ≠ 0 := by
  intro h
  have := localNudgeVec_norm a b
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm


/-! ### The pointer-volume theorem, re-routed and genericity-free -/

/-- ★★ **The local de-isolation reproduces the singlet, at EVERY setting pair.**

This is `localDeisolation_pointer_volume` with `nudgedSinglet` replaced by
`localNudgeVec`, and **without `hgen`**. The genericity restriction was never
intrinsic to the volume machinery — `povm_born_eq_dilated_volume_uncond` is
already hpos-free — it entered only through `singletJointEig`'s division by
`√P_st`. Routing through the local object removes it, so the perfectly
(anti)correlated endpoints `a·b = ±1` are now covered. -/
theorem localDeisolation_pointer_volume_local {M : ℕ}
    (a b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ'0 : ψ' ≠ 0) (s t : Sign) :
    ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
      = P_st a b s t := by
  have hnorm : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b))‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, localDeisolation_norm_map, localNudgeVec_norm a b]
  have h := povm_born_eq_dilated_volume_uncond (basisPOVM 4) localNaimark
      (localNudgeVec a b) (stIdx (s, t)) e p₀ hnorm
  rw [basisPOVM_weight, localNudgeVec_born a b s t] at h
  subst hψ'eq
  exact h.symm


/-! ### The complete finite measurement chain factorises

⚠️ **Scope.** This is a statement about the **finite dilated construction** — the
wing de-isolation isometries and the wing basis unitaries — not about arbitrary
ontic `Σ`. No canonical subsystem decomposition of `Σ` is used or implied. -/

/-- ★★ **The whole setting-dependent chain is a product of wing-local maps.**

Composing the context-setting nudge with the apparatus coupling gives

    (V_A ⊗ V_B) · (U_A(a) ⊗ U_B(b))ᴴ  =  (V_A · U_A(a)ᴴ) ⊗ (V_B · U_B(b)ᴴ)

so each wing's operation depends only on that wing's setting. This is work-order
item 8, and it is available only because `localNudge` replaced `nudgedSinglet`:
the old object is not a product-unitary image of the singlet at all, so no such
factorisation existed for it.

⚠️ This is **dynamical** locality of the chain. It is emphatically **not** Bell
factorisation of outcomes, which `no_product_partition_realises_singlet` proves
impossible for the singlet. -/
theorem localMeasurementChain_factorises (a b : DetectorSetting) :
    (wingDeisolationV ⊗ₖ wingDeisolationV) * (wingPairUnitary a b)ᴴ
      = (wingDeisolationV * (wingBasisUnitary a)ᴴ)
        ⊗ₖ (wingDeisolationV * (wingBasisUnitary b)ᴴ) := by
  rw [wingPairUnitary, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]


/-! ### Operational no-signalling of the explicit construction (item 15)

The pointer-block volumes reproduce `P_st`, so summing out one wing gives that
wing's marginal. Because the singlet marginals are `1/2` at *every* context,
the A-marginal volume does not move when B's setting changes.

⚠️ These are equalities of **marginal volumes**, never of the underlying
outcome partitions. The microscopic regions differ between contexts; only their
measures agree. And the whole statement sits under **measurement independence**,
as `LF3.OperationalNoSignalling` records. -/

/-- ★ **The A-wing marginal volume is `1/2`.** Summing the pointer-block volumes
over the B outcome recovers the A marginal, which the singlet fixes at one half.
No genericity hypothesis. -/
theorem localDeisolation_A_marginal_volume_eq_half {M : ℕ}
    (a b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ'0 : ψ' ≠ 0) (s : Sign) :
    ∑ t : Sign, ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
      = 1 / 2 := by
  have hcell : ∀ t : Sign, ∑ n : Fin 4,
      (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
        = P_st a b s t :=
    fun t => localDeisolation_pointer_volume_local a b e p₀ ψ' hψ'eq hψ'0 s t
  rw [Finset.sum_congr rfl (fun t _ => hcell t)]
  exact marginal_a_eq_half a b s

/-- ★ **The B-wing marginal volume is `1/2`**, symmetrically. -/
theorem localDeisolation_B_marginal_volume_eq_half {M : ℕ}
    (a b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ'0 : ψ' ≠ 0) (t : Sign) :
    ∑ s : Sign, ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
      = 1 / 2 := by
  have hcell : ∀ s : Sign, ∑ n : Fin 4,
      (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
        = P_st a b s t :=
    fun s => localDeisolation_pointer_volume_local a b e p₀ ψ' hψ'eq hψ'0 s t
  rw [Finset.sum_congr rfl (fun s _ => hcell s)]
  exact marginal_b_eq_half a b t

/-- ★★ **A-wing operational no-signalling for the explicit construction.**
Changing B's setting from `b` to `b'` leaves the A-marginal volume unchanged.

The two sides are built from *different* prepared states, so the underlying
pointer regions differ; what agrees is their measure. -/
theorem localDeisolation_no_signalling_A {M : ℕ}
    (a b b' : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' ψ'' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ''eq : ψ'' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b')))
    (hψ'0 : ψ' ≠ 0) (hψ''0 : ψ'' ≠ 0) (s : Sign) :
    ∑ t : Sign, ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
      = ∑ t : Sign, ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ'' hψ''0 (e (n, stIdx (s, t))))).toReal := by
  rw [localDeisolation_A_marginal_volume_eq_half a b e p₀ ψ' hψ'eq hψ'0 s,
    localDeisolation_A_marginal_volume_eq_half a b' e p₀ ψ'' hψ''eq hψ''0 s]

/-- ★★ **B-wing operational no-signalling for the explicit construction.** -/
theorem localDeisolation_no_signalling_B {M : ℕ}
    (a a' b : DetectorSetting)
    (e : Fin 4 × Fin 4 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' ψ'' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a b)))
    (hψ''eq : ψ'' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin localDeisolationV (localNudgeVec a' b)))
    (hψ'0 : ψ' ≠ 0) (hψ''0 : ψ'' ≠ 0) (t : Sign) :
    ∑ s : Sign, ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, stIdx (s, t))))).toReal
      = ∑ s : Sign, ∑ n : Fin 4,
        (fubiniStudyMeasure p₀ (bornRegion ψ'' hψ''0 (e (n, stIdx (s, t))))).toReal := by
  rw [localDeisolation_B_marginal_volume_eq_half a b e p₀ ψ' hψ'eq hψ'0 t,
    localDeisolation_B_marginal_volume_eq_half a' b e p₀ ψ'' hψ''eq hψ''0 t]


end CSD.LF6


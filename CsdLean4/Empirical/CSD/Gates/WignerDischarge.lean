/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Gates.Framework
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
public import CsdLean4.LF4.Instance

/-!
# Empirical/CSD/Gates: Wigner discharge of `CSDUnitaryBundle.U_isometry` (LF4-todo §13.2)

**Category:** 3-Local (CSD-side discharge of the §13.2 obligation).

## What this file provides

The `CSDUnitaryBundle.U_isometry` field (`∀ x y, ⟪U x, U y⟫ = ⟪x, y⟫`) is
discharged **through Wigner** from the intrinsic transition-probability-preserving
condition on a projective self-map, rather than posited as a Hilbert isometry.

* `Projectivization.transProbPreserving_isometry_dichotomy` — the honest Wigner
  dichotomy at the Hilbert level: a `TransProbPreserving` self-map of `ℂℙ^{N-1}`
  is realised by a genuine `≃ₗᵢ[ℂ]` `e` with `⟪e x, e y⟫ = ⟪x, y⟫` (**unitary**,
  giving `U_isometry`), OR by an antiunitary `e ∘ conjVec` with
  `⟪e (conjVec x), e (conjVec y)⟫ = conj ⟪x, y⟫` (**time-reversal / anti-isometry**;
  it does *not* satisfy `U_isometry` as stated). The antiunitary branch is not
  dropped: it is exposed with its conjugated inner-product law.
* `CSDBridge.Gates.u_isometry_of_transProbPreserving` — the constructor headline:
  from `TransProbPreserving f` **plus** a no-time-reversal selection
  (`f` is not the antiunitary branch), Wigner *produces* a `≃ₗᵢ[ℂ]` `e` realising
  `f` and satisfying `⟪e x, e y⟫ = ⟪x, y⟫`. Unitarity (hence `U_isometry`) is the
  OUTPUT of Wigner, not an input.
* `CSDBridge.Gates.CSDUnitaryBundle.ofTransProbPreserving` — the same content
  packaged as a `CSDUnitaryBundle`: `U_isometry` is a THEOREM.
* `Projectivization.conjProj_ne_projMap` / `smul_action_not_antiunitary` — the
  non-vacuity core: coordinatewise conjugation is not a unitary projective map
  (`N ≥ 2`), so the sector action `g • ·` (a `Matrix.unitaryGroup` element, the A5
  datum) satisfies the no-time-reversal selection.
* `cpSectorActionBundle` — a concrete `CSDUnitaryBundle` on `cpSectorData p₀`
  whose `U_isometry` is DERIVED (via the constructor, from the sector action's
  transition-probability preservation), not posited. Non-vacuous.
  **Honest scope of this witness.** Here `f = g • ·` already carries isometry
  structure (that is exactly why `transProbPreserving_unitary g` and
  `smul_action_not_antiunitary` are provable), so for this concrete instance the
  Wigner step adds no content: an isometry realising `f` was in hand a priori.
  Read this as "`U_isometry` derived from the A5 sector action (which already
  carries the isometry)", NOT as "isometry derived from blind deterministic
  dynamics". The content-adding case — Wigner manufacturing an isometry from a
  map NOT presented as one — is the general constructor
  `u_isometry_of_transProbPreserving`; the general `μL`-flow ⟹ transProb lift is
  the open D1 gap.

## Honest status of §13.2

**Discharged MODULO the sector symmetry (A5).** For projective dynamics that
preserve the transition-probability structure, `U_isometry` is a theorem via
Wigner, non-vacuously realised by the sector action on the concrete Kähler
instance. The primitive moves from "posit the Hilbert unitary `U` with
`U_isometry`" to "posit the projective dynamics preserves transition
probabilities and is not time-reversal".

**True residue (D1).** The transition-probability preservation is FORCED by the
sector symmetry — the sector group `G` acting by Fubini–Study isometries, which
is the A5 datum (`SectorData.(π, G)`) — **not** by `μL`-measure-preservation.
Measure-preservation is strictly weaker than metric preservation: a
`μFS`-measure-preserving self-map of `ℂℙ^{N-1}` need **not** preserve the
Fubini–Study metric / transition probability, so no lemma
"measure-preserving `f_Φ` ⟹ `TransProbPreserving f_Φ`" is proved here (it is
false). Deriving `TransProbPreserving f_Φ` from a *general* `μL`-flow for a
non-symmetry flow is the open D1 gap. So §13.2 discharges exactly modulo the
posited sector symmetry, correcting the earlier (false) "measure-preserving
π-equivariant flow ⟹ isometry" reading of the obligation.

Foundational-triple only; no `busch`.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization ComplexOrder

namespace Projectivization

variable {N : ℕ}

/-- **Coordinatewise conjugation is not a unitary projective map (`N ≥ 2`).**
For any `≃ₗᵢ[ℂ]` `h`, `conjProj ≠ projMap h`. Probe rays: the real rays fix the
diagonal scalars `h uᵢ = dᵢ • uᵢ`, the real sum ray forces `d₀ = d₁`, and the
complex ray `mk (u₀ + I • u₁)` — which `conjProj` sends to `mk (u₀ − I • u₁)` and
`projMap h` to `mk (u₀ + I • u₁)` — forces `I = −I`, absurd. This is the
crisp statement that the antiunitary class is genuinely distinct from the unitary
class, and the non-vacuity core of the no-time-reversal selection below. -/
theorem conjProj_ne_projMap (hN : 2 ≤ N)
    (h : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    ¬ (∀ p, conjProj p = projMap h p) := by
  intro hall
  set i0 : Fin N := ⟨0, by omega⟩ with hi0
  set i1 : Fin N := ⟨1, by omega⟩ with hi1
  have hne01 : i0 ≠ i1 := by
    rw [hi0, hi1]; intro hc; exact absurd (Fin.mk.injEq .. ▸ hc) (by norm_num)
  set u0 : EuclideanSpace ℂ (Fin N) := EuclideanSpace.single i0 (1:ℂ) with hu0def
  set u1 : EuclideanSpace ℂ (Fin N) := EuclideanSpace.single i1 (1:ℂ) with hu1def
  have hu0 : u0 ≠ 0 := by
    rw [hu0def]
    simpa using (EuclideanSpace.single_ne_zero_iff (i := i0) (a := (1:ℂ))).mpr one_ne_zero
  have hu1 : u1 ≠ 0 := by
    rw [hu1def]
    simpa using (EuclideanSpace.single_ne_zero_iff (i := i1) (a := (1:ℂ))).mpr one_ne_zero
  -- coordinates of the two probe basis vectors
  have c00 : u0.ofLp i0 = 1 := by simp [hu0def]
  have c01 : u0.ofLp i1 = 0 := by simp [hu0def, hne01.symm]
  have c10 : u1.ofLp i0 = 0 := by simp [hu1def, hne01]
  have c11 : u1.ofLp i1 = 1 := by simp [hu1def]
  -- conjugation identities on the probes
  have cv0 : conjVec u0 = u0 := by
    ext j; simp [conjVec_ofLp, hu0def, apply_ite (starRingEnd ℂ)]
  have cv1 : conjVec u1 = u1 := by
    ext j; simp [conjVec_ofLp, hu1def, apply_ite (starRingEnd ℂ)]
  have cvsum : conjVec (u0 + u1) = u0 + u1 := by
    ext j; simp [conjVec_ofLp, hu0def, hu1def, apply_ite (starRingEnd ℂ)]
  have cvcpx : conjVec (u0 + Complex.I • u1) = u0 + (-Complex.I) • u1 := by
    ext j
    simp only [conjVec_ofLp, hu0def, hu1def, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      map_add, map_mul, Complex.conj_I, PiLp.single_apply, apply_ite (starRingEnd ℂ),
      map_one, map_zero, neg_mul]
  -- the three combination rays are nonzero
  have hsum : u0 + u1 ≠ 0 := by
    intro hc; have := congrArg (fun v => v.ofLp i0) hc; simp [c00, c10] at this
  have hcpx : u0 + Complex.I • u1 ≠ 0 := by
    intro hc; have := congrArg (fun v => v.ofLp i0) hc; simp [c00, c10] at this
  have hcpx' : u0 + (-Complex.I) • u1 ≠ 0 := by
    intro hc; have := congrArg (fun v => v.ofLp i0) hc; simp [c00, c10] at this
  -- `conjProj` fixings, as clean projective equalities (no dependent rewrite in `mk`)
  have hcp0 : conjProj (Projectivization.mk ℂ u0 hu0) = Projectivization.mk ℂ u0 hu0 := by
    rw [conjProj_mk hu0]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by rw [one_smul]; exact cv0.symm⟩
  have hcp1 : conjProj (Projectivization.mk ℂ u1 hu1) = Projectivization.mk ℂ u1 hu1 := by
    rw [conjProj_mk hu1]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by rw [one_smul]; exact cv1.symm⟩
  have hcpsum : conjProj (Projectivization.mk ℂ (u0 + u1) hsum)
      = Projectivization.mk ℂ (u0 + u1) hsum := by
    rw [conjProj_mk hsum]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by rw [one_smul]; exact cvsum.symm⟩
  have hcpcpx : conjProj (Projectivization.mk ℂ (u0 + Complex.I • u1) hcpx)
      = Projectivization.mk ℂ (u0 + (-Complex.I) • u1) hcpx' := by
    rw [conjProj_mk hcpx]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by rw [one_smul]; exact cvcpx.symm⟩
  -- diagonal scalars `h uᵢ = dᵢ • uᵢ`
  have e0 : ∃ d : ℂ, d • u0 = h u0 := by
    have hP := hall (Projectivization.mk ℂ u0 hu0)
    rw [hcp0, projMap_mk h u0 hu0] at hP
    exact (Projectivization.mk_eq_mk_iff' ℂ (h u0) u0 _ hu0).mp hP.symm
  have e1 : ∃ d : ℂ, d • u1 = h u1 := by
    have hP := hall (Projectivization.mk ℂ u1 hu1)
    rw [hcp1, projMap_mk h u1 hu1] at hP
    exact (Projectivization.mk_eq_mk_iff' ℂ (h u1) u1 _ hu1).mp hP.symm
  obtain ⟨d0, hd0⟩ := e0
  obtain ⟨d1, hd1⟩ := e1
  have hd0ne : d0 ≠ 0 := by
    intro hc; rw [hc, zero_smul] at hd0
    exact (h.toLinearEquiv.map_ne_zero_iff.mpr hu0) hd0.symm
  -- real sum ray ⟹ `d₀ = d₁`
  have hsumeq : ∃ e : ℂ, e • (u0 + u1) = h (u0 + u1) := by
    have hP := hall (Projectivization.mk ℂ (u0 + u1) hsum)
    rw [hcpsum, projMap_mk h (u0 + u1) hsum] at hP
    exact (Projectivization.mk_eq_mk_iff' ℂ (h (u0 + u1)) (u0 + u1) _ hsum).mp hP.symm
  obtain ⟨e, he⟩ := hsumeq
  have hvalsum : h (u0 + u1) = d0 • u0 + d1 • u1 := by
    simp only [map_add, ← hd0, ← hd1]
  rw [hvalsum] at he
  have hei0 := congrArg (fun v => v.ofLp i0) he
  have hei1 := congrArg (fun v => v.ofLp i1) he
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, c00, c01, c10, c11] at hei0 hei1
  have hd01 : d0 = d1 := by
    have h1 : e = d0 := by linear_combination hei0
    have h2 : e = d1 := by linear_combination hei1
    rw [← h1, h2]
  -- complex ray ⟹ `I = −I`, contradiction
  have hcpxeq : ∃ f : ℂ, f • (u0 + (-Complex.I) • u1) = h (u0 + Complex.I • u1) := by
    have hP := hall (Projectivization.mk ℂ (u0 + Complex.I • u1) hcpx)
    rw [hcpcpx, projMap_mk h (u0 + Complex.I • u1) hcpx] at hP
    exact (Projectivization.mk_eq_mk_iff' ℂ (h (u0 + Complex.I • u1))
      (u0 + (-Complex.I) • u1) _ hcpx').mp hP.symm
  obtain ⟨fcx, hf⟩ := hcpxeq
  have hvalcpx : h (u0 + Complex.I • u1) = d0 • u0 + Complex.I • d1 • u1 := by
    simp only [map_add, map_smul, ← hd0, ← hd1]
  rw [hvalcpx] at hf
  have hfi0 := congrArg (fun v => v.ofLp i0) hf
  have hfi1 := congrArg (fun v => v.ofLp i1) hf
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, c00, c01, c10, c11] at hfi0 hfi1
  have hf_d0 : fcx = d0 := by linear_combination hfi0
  have hrel : (-Complex.I) * fcx = Complex.I * d1 := by linear_combination hfi1
  rw [hf_d0, ← hd01] at hrel
  have hId0 : Complex.I * d0 = 0 := by
    have h2 : (2 : ℂ) * (Complex.I * d0) = 0 := by linear_combination -hrel
    rcases mul_eq_zero.mp h2 with hh | hh
    · exact absurd hh (by norm_num)
    · exact hh
  rcases mul_eq_zero.mp hId0 with hh | hh
  · exact Complex.I_ne_zero hh
  · exact hd0ne hh

variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-- **Honest Wigner dichotomy at the Hilbert level.** A `TransProbPreserving`
self-map of `ℂℙ^{N-1}` is realised either by a genuine `≃ₗᵢ[ℂ]` `e` satisfying the
isometry law `⟪e x, e y⟫ = ⟪x, y⟫` (the **unitary** branch, which discharges
`CSDUnitaryBundle.U_isometry`), or by the antiunitary map `e ∘ conjVec` satisfying
the conjugated law `⟪e (conjVec x), e (conjVec y)⟫ = conj ⟪x, y⟫` (the
**time-reversal** branch, which does *not* satisfy `U_isometry` as stated). The
antiunitary branch is not silently dropped: it is exposed with its anti-isometry
law. ℂ-linearity of `e` is an OUTPUT of `wigner_rigidity`, not assumed. -/
theorem transProbPreserving_isometry_dichotomy (hf : TransProbPreserving f) :
    (∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        (∀ p, f p = projMap e p)
        ∧ (∀ x y : EuclideanSpace ℂ (Fin N), (inner ℂ (e x) (e y) : ℂ) = inner ℂ x y))
    ∨ (∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        (∀ p, f p = projMap e (conjProj p))
        ∧ (∀ x y : EuclideanSpace ℂ (Fin N),
            (inner ℂ (e (conjVec x)) (e (conjVec y)) : ℂ) = (starRingEnd ℂ) (inner ℂ x y))) := by
  rcases wigner_rigidity hf with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨e, he, fun x y => e.inner_map_map x y⟩
  · refine Or.inr ⟨e, he, fun x y => ?_⟩
    rw [e.inner_map_map, conjVec_inner]

/-- **The sector action `g • ·` is not time-reversal (`N ≥ 2`).** No `≃ₗᵢ[ℂ]` `e`
realises the unitary projective action `g • ·` as the antiunitary `e ∘ conjProj`.
Reduces to `conjProj_ne_projMap`: writing `g • · = projMap eg` with
`eg := (toEuclideanLinearEquiv g).isometryOfInner _` (isometry via
`inner_toEuclideanLin_unitary`), an antiunitary factorisation would make
`conjProj = projMap (eg.trans e.symm)`, contradicting `conjProj_ne_projMap`. -/
theorem smul_action_not_antiunitary (hN : 2 ≤ N) (g : Matrix.unitaryGroup (Fin N) ℂ) :
    ¬ ∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        ∀ p, (g • p) = projMap e (conjProj p) := by
  rintro ⟨e, he⟩
  set eg := (Matrix.UnitaryGroup.toEuclideanLinearEquiv g).isometryOfInner
    (inner_toEuclideanLin_unitary g) with hegdef
  have hgeq : ∀ p, g • p = projMap eg p := by
    intro p
    conv_lhs => rw [← p.mk_rep]
    conv_rhs => rw [← p.mk_rep]
    rw [smul_mk_eq_mk_toEuclideanLin g p.rep_nonzero, projMap_mk eg p.rep p.rep_nonzero]
    congr 1
  refine conjProj_ne_projMap hN (eg.trans e.symm) ?_
  intro p
  have heq : projMap eg p = projMap e (conjProj p) := by rw [← hgeq p]; exact he p
  have hstrip : projMap e.symm (projMap e (conjProj p)) = conjProj p := by
    have := projMap_symm_projMap e.symm (conjProj p)
    simpa using this
  calc conjProj p = projMap e.symm (projMap e (conjProj p)) := hstrip.symm
    _ = projMap e.symm (projMap eg p) := by rw [heq]
    _ = projMap (eg.trans e.symm) p := projMap_comp e.symm eg p

end Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Gates

open Projectivization

/-- **Constructor headline: `U_isometry` derived via Wigner.** From
`TransProbPreserving f` (the intrinsic transition-probability condition on a
projective self-map) **plus** a no-time-reversal selection (`f` is not the
antiunitary branch), Wigner *produces* a `≃ₗᵢ[ℂ]` `e` realising `f` and satisfying
the isometry law `⟪e x, e y⟫ = ⟪x, y⟫`. Unitarity — hence
`CSDUnitaryBundle.U_isometry` — is the OUTPUT of `wigner_rigidity`, never assumed.
The primitive is thereby weakened from "posit the Hilbert isometry" to "posit the
projective dynamics preserves transition probabilities and is not time-reversal".
The no-time-reversal selection is a discrete `ℤ/2` datum (the Kähler / ℂ-linearity
orientation), not the isometry data. -/
theorem u_isometry_of_transProbPreserving {N : ℕ}
    {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hf : TransProbPreserving f)
    (hsel : ¬ ∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        ∀ p, f p = projMap e (conjProj p)) :
    ∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
      (∀ p, f p = projMap e p)
      ∧ (∀ x y : EuclideanSpace ℂ (Fin N), (inner ℂ (e x) (e y) : ℂ) = inner ℂ x y) := by
  rcases wigner_rigidity hf with h | h
  · exact ⟨h.choose, h.choose_spec, fun x y => h.choose.inner_map_map x y⟩
  · exact absurd h hsel

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **`CSDUnitaryBundle` with `U_isometry` discharged through Wigner.** Given a
bridge context, a `TransProbPreserving` projective self-map `f`, and the
no-time-reversal selection, produces a `CSDUnitaryBundle` whose carried `U` is the
Wigner-output isometry and whose `U_isometry` field is a THEOREM
(`e.inner_map_map`), not a posit. This is the §13.2 discharge on the Hilbert space
`EuclideanSpace ℂ (Fin N)`. -/
noncomputable def CSDUnitaryBundle.ofTransProbPreserving {N : ℕ}
    {D : CSD.LF2.SectorData SigmaSpace P G}
    (ctx : CSD.Empirical.CSDBridge.Context D)
    (f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N)))
    (hf : TransProbPreserving f)
    (hsel : ¬ ∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        ∀ p, f p = projMap e (conjProj p)) :
    CSDUnitaryBundle D N (EuclideanSpace ℂ (Fin N)) :=
  let hunit := u_isometry_of_transProbPreserving hf hsel
  { toContext := ctx
    U := ⇑hunit.choose
    U_isometry := fun x y => hunit.choose_spec.2 x y }

end Gates
end CSDBridge
end Empirical
end CSD

namespace CSD
namespace LF4

open Projectivization CSD.Empirical.CSDBridge Matrix.UnitaryGroup

variable {N : ℕ} [NeZero N]

/-- Measure-bridge data for `cpSectorData` (`c = 1`, `π = id`), built axiom-free
from `fubiniStudyMeasure_smul_invariant` and `Measure.map_id`. -/
noncomputable def cpBridgeData (p₀ : CPN N) :
    CSD.LF2.MeasureBridgeData (cpSectorData p₀) (fubiniStudyMeasure p₀) where
  is_inv := fun U =>
    ⟨(continuous_const_smul U).measurable, fubiniStudyMeasure_smul_invariant U p₀⟩
  c := 1
  bridge_eq := by
    show Measure.map (cpSectorData p₀).π ((cpSectorData p₀).μL : Measure (CPN N))
        = (1 : ENNReal) • fubiniStudyMeasure p₀
    rw [one_smul]
    show Measure.map id (fubiniStudyMeasure p₀) = fubiniStudyMeasure p₀
    rw [Measure.map_id]

/-- The bridge context for the concrete `ℂℙ^{N-1}` / `U(N)` instance. -/
noncomputable def cpContext (p₀ : CPN N) :
    CSD.Empirical.CSDBridge.Context (cpSectorData p₀) where
  μFS := fubiniStudyMeasure p₀
  hμFS_prob := inferInstance
  bridge := cpBridgeData p₀

/-- **Non-vacuous §13.2 discharge on the concrete Kähler instance.** A concrete
`CSDUnitaryBundle` on `cpSectorData p₀` whose `U_isometry` is DERIVED (via
`CSDUnitaryBundle.ofTransProbPreserving`, from the sector action's
transition-probability preservation `transProbPreserving_unitary g`) rather than
posited. The no-time-reversal selection is supplied by
`smul_action_not_antiunitary` (`N ≥ 2`): the sector action `g • ·` is a
`Matrix.unitaryGroup` element acting — the A5 sector-symmetry datum — hence not
time-reversal. Unitarity is the OUTPUT of Wigner. -/
noncomputable def cpSectorActionBundle (hN : 2 ≤ N) (p₀ : CPN N)
    (g : Matrix.unitaryGroup (Fin N) ℂ) :
    CSD.Empirical.CSDBridge.Gates.CSDUnitaryBundle (cpSectorData p₀) N
      (EuclideanSpace ℂ (Fin N)) :=
  CSD.Empirical.CSDBridge.Gates.CSDUnitaryBundle.ofTransProbPreserving (cpContext p₀)
    (fun p => g • p)
    (transProbPreserving_unitary g)
    (smul_action_not_antiunitary hN g)

end LF4
end CSD

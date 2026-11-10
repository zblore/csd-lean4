/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.EchoCoupledFlow
public import CsdLean4.LF4.ArenaVolume

/-!
# The flow of a ray coupled to two tori: its two one-torus slices and its preserved measure

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #359.

`EchoCoupledFlow.lean` (#202) put a symplectic form on `ℂℙᴺ × T² × T²` and gave the flow of

  `𝓗(x, θ, ψ) = −2⟨A⟩(x) − 2⟨B_A⟩(x) f(θ₂) − 2⟨B_B⟩(x) g(ψ₂)`

in closed form (`hamiltonianFlow_twoCoupledEnergy`). Two facts about that flow were not stated
there, for general `N` and general matrices. This module proves them from the closed form.

**The slices.** Both second angles are conserved. With `ψ₂` held, the ray and the first torus move
by the one-torus flow of `ArenaCoupledFlow.lean` for the matrices `(A + g(ψ₂) B_B, B_A)` and the
profile `f` (`twoCoupledFlow_fst`). With `θ₂` held, the ray and the second torus move by the
one-torus flow for `(A + f(θ₂) B_A, B_B)` and the profile `g` (`twoCoupledFlow_snd`). Neither
torus is singled out. On a fibre where the other profile vanishes the slice is the one-torus flow
of `(A, B_A)`, or of `(A, B_B)`, with nothing added (`twoCoupledFlow_fst_of_lift_eq_zero`,
`twoCoupledFlow_snd_of_lift_eq_zero`).

**The measure.** The flow preserves `μ_FS ⊗ vol_{T²} ⊗ vol_{T²}` (`echoMuL_map_twoCoupledFlow`).
The proof is a skew product: over each `ψ₂` the first slice preserves `kMuL` by
`kMuL_map_hamiltonianFlow`, and `ψ₁` is translated by an amount that does not depend on `ψ₁`.

* `twoCoupledFlow`, `twoCoupledFlow_apply`, `continuous_twoCoupledFlow`,
  `measurable_twoCoupledFlow`, `twoCoupledFlow_zero`, `twoCoupledFlow_add`;
* `schrodingerUnitary_congr`, `twoCoupledMatrix_eq_coupledMatrix_fst`,
  `twoCoupledMatrix_eq_coupledMatrix_snd`, `twoAccumA_eq_coupledAccum`,
  `twoAccumB_eq_coupledAccum`;
* ★★ `twoCoupledFlow_fst`, ★★ `twoCoupledFlow_snd` — the two one-torus slices;
* ★ `twoCoupledFlow_fst_of_lift_eq_zero`, ★ `twoCoupledFlow_snd_of_lift_eq_zero`;
* ★ `measurePreserving_addShear` — a shear of one circle coordinate by a measurable amount that
  does not depend on it preserves the product measure;
* `echoMuL`, ★★★ `echoMuL_map_twoCoupledFlow`.

## Honest scope

* **Two tori.** `EchoSigma` has two pointer tori. A third needs one more product form, as
  `CrossCoupledFlow.lean` (#225) did for a second ray. No family of pointers is built.
* **The measure statement is read off the closed form.** It is not the top-form theorem
  `map_hamiltonianFlow_topFormMeasure_wedgePow` applied to `echoForm`. The top-form measure of
  `echoForm` is not identified with `echoMuL` here.
* **The matrices are Hermitian by hypothesis.** The flow is defined for any matrices. The closed
  form, the slices and the measure statement are for Hermitian ones.
* `measurePreserving_addShear` has the special case `measurePreserving_cshift_mid`
  (`RecordLayer/EchoArena.lean`, #199), where the amount is the class of a real number.

References: `specs/BACKLOG.md` #359, #202, #199, #195; `specs/future-work.md`;
`specs/unified-record-spacetime-plan.md` (UD-66, UD-67); `LF4/EchoCoupledFlow.lean`
(`hamiltonianFlow_twoCoupledEnergy`), `LF4/ArenaCoupledFlow.lean`
(`hamiltonianFlow_coupledEnergy`), `LF4/ArenaVolume.lean` (`kMuL_map_hamiltonianFlow`).
-/

@[expose] public section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### The flow -/

section Flow

variable {f g : ℝ → ℝ} (A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- **The flow of the two-torus energy** on `ℂℙᴺ × T² × T²`: the Hamiltonian flow of
`twoCoupledEnergy` for the form `echoForm`. -/
noncomputable def twoCoupledFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (t : ℝ) : EchoSigma N → EchoSigma N :=
  (echoForm_isSymplectic N).hamiltonianFlow (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg) t

theorem continuous_twoCoupledFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (t : ℝ) :
    Continuous (twoCoupledFlow A BA BB hf hg hc hcg t) :=
  (echoForm_isSymplectic N).continuous_hamiltonianFlow _ t

set_option synthInstance.maxSize 512 in
theorem measurable_twoCoupledFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (t : ℝ) :
    Measurable (twoCoupledFlow A BA BB hf hg hc hcg t) :=
  (continuous_twoCoupledFlow A BA BB hf hg hc hcg t).measurable

theorem twoCoupledFlow_zero (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (x : EchoSigma N) :
    twoCoupledFlow A BA BB hf hg hc hcg 0 x = x :=
  integralFlow_zero ((echoForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
    (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg)) x

/-- The flow is a one-parameter group. -/
theorem twoCoupledFlow_add (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (s t : ℝ) (x : EchoSigma N) :
    twoCoupledFlow A BA BB hf hg hc hcg (s + t) x
      = twoCoupledFlow A BA BB hf hg hc hcg s (twoCoupledFlow A BA BB hf hg hc hcg t x) :=
  integralFlow_add ((echoForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
    (contMDiff_twoCoupledEnergy A BA BB hf hg hc hcg)) s t x

variable {A BA BB}

/-- The closed form of #202, for the named flow. -/
theorem twoCoupledFlow_apply (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (t : ℝ) (x : CPN (N + 1)) (θ ψ : KTorus) :
    twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)
      = ((Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2) t • x,
          (θ.1 + ((hf.deriv_periodic.lift θ.2 * twoAccumA hA hBA hBB hf hg θ.2 ψ.2 x t : ℝ) :
            AddCircle (1 : ℝ)), θ.2)),
         (ψ.1 + ((hg.deriv_periodic.lift ψ.2 * twoAccumB hA hBA hBB hf hg θ.2 ψ.2 x t : ℝ) :
            AddCircle (1 : ℝ)), ψ.2)) :=
  hamiltonianFlow_twoCoupledEnergy hA hBA hBB hf hg hc hcg t x θ ψ

/-! ### The two one-torus slices -/

/-- The Schrödinger unitary depends on the matrix only. -/
theorem schrodingerUnitary_congr {H H' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (h : H = H')
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) :
    Matrix.schrodingerUnitary hH = Matrix.schrodingerUnitary hH' := by
  subst h
  rfl

variable (A BA BB) in
/-- With `ψ` held, the two-angle matrix is the one-angle matrix of `(A + g(ψ) B_B, B_A)`. -/
theorem twoCoupledMatrix_eq_coupledMatrix_fst (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ)) :
    twoCoupledMatrix A BA BB hf hg φ ψ
      = coupledMatrix (A + ((hg.lift ψ : ℝ) : ℂ) • BB) BA hf φ := by
  unfold twoCoupledMatrix coupledMatrix
  exact add_right_comm _ _ _

variable (A BA BB) in
/-- With `φ` held, the two-angle matrix is the one-angle matrix of `(A + f(φ) B_A, B_B)`. -/
theorem twoCoupledMatrix_eq_coupledMatrix_snd (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (φ ψ : AddCircle (1 : ℝ)) :
    twoCoupledMatrix A BA BB hf hg φ ψ
      = coupledMatrix (A + ((hf.lift φ : ℝ) : ℂ) • BA) BB hg ψ := rfl

/-- The first accumulated amount is the one-torus amount of `(A + g(ψ) B_B, B_A)`. -/
theorem twoAccumA_eq_coupledAccum (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (φ ψ : AddCircle (1 : ℝ)) (x : CPN (N + 1)) (t : ℝ) :
    twoAccumA hA hBA hBB hf hg φ ψ x t
      = coupledAccum (isHermitian_add_real_smul hA hBB (hg.lift ψ)) hBA hf φ x t := by
  unfold twoAccumA coupledAccum
  rw [schrodingerUnitary_congr (twoCoupledMatrix_eq_coupledMatrix_fst A BA BB hf hg φ ψ)
    (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ)
    (coupledMatrix_isHermitian (isHermitian_add_real_smul hA hBB (hg.lift ψ)) hBA hf φ)]

/-- The second accumulated amount is the one-torus amount of `(A + f(φ) B_A, B_B)`. -/
theorem twoAccumB_eq_coupledAccum (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (φ ψ : AddCircle (1 : ℝ)) (x : CPN (N + 1)) (t : ℝ) :
    twoAccumB hA hBA hBB hf hg φ ψ x t
      = coupledAccum (isHermitian_add_real_smul hA hBA (hf.lift φ)) hBB hg ψ x t := by
  unfold twoAccumB coupledAccum
  rw [schrodingerUnitary_congr (twoCoupledMatrix_eq_coupledMatrix_snd A BA BB hf hg φ ψ)
    (twoCoupledMatrix_isHermitian hA hBA hBB hf hg φ ψ)
    (coupledMatrix_isHermitian (isHermitian_add_real_smul hA hBA (hf.lift φ)) hBB hg ψ)]

/-- ★★ **The first slice.** With the second torus's angle `ψ₂` held, the ray and the first torus
move by the one-torus flow of `(A + g(ψ₂) B_B, B_A)` with the profile `f`. -/
theorem twoCoupledFlow_fst (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (t : ℝ) (x : CPN (N + 1)) (θ ψ : KTorus) :
    (twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)).1
      = (arenaForm_isSymplectic N).hamiltonianFlow
          (contMDiff_coupledEnergy (A + ((hg.lift ψ.2 : ℝ) : ℂ) • BB) BA hf hc) t (x, θ) := by
  rw [twoCoupledFlow_apply hA hBA hBB hf hg hc hcg,
    hamiltonianFlow_coupledEnergy (isHermitian_add_real_smul hA hBB (hg.lift ψ.2)) hBA hf hc,
    twoAccumA_eq_coupledAccum,
    schrodingerUnitary_congr (twoCoupledMatrix_eq_coupledMatrix_fst A BA BB hf hg θ.2 ψ.2)
      (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2)
      (coupledMatrix_isHermitian (isHermitian_add_real_smul hA hBB (hg.lift ψ.2)) hBA hf θ.2)]

/-- ★★ **The second slice.** With the first torus's angle `θ₂` held, the ray and the second torus
move by the one-torus flow of `(A + f(θ₂) B_A, B_B)` with the profile `g`. -/
theorem twoCoupledFlow_snd (hA : A.IsHermitian) (hBA : BA.IsHermitian) (hBB : BB.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (t : ℝ) (x : CPN (N + 1)) (θ ψ : KTorus) :
    ((twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)).1.1,
        (twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)).2)
      = (arenaForm_isSymplectic N).hamiltonianFlow
          (contMDiff_coupledEnergy (A + ((hf.lift θ.2 : ℝ) : ℂ) • BA) BB hg hcg) t (x, ψ) := by
  rw [twoCoupledFlow_apply hA hBA hBB hf hg hc hcg,
    hamiltonianFlow_coupledEnergy (isHermitian_add_real_smul hA hBA (hf.lift θ.2)) hBB hg hcg,
    twoAccumB_eq_coupledAccum,
    schrodingerUnitary_congr (twoCoupledMatrix_eq_coupledMatrix_snd A BA BB hf hg θ.2 ψ.2)
      (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2)
      (coupledMatrix_isHermitian (isHermitian_add_real_smul hA hBA (hf.lift θ.2)) hBB hg ψ.2)]

/-- ★ **Where the second profile vanishes, the first slice is the one-torus flow of `(A, B_A)`.**
Nothing is added to the generator the ray and the first torus see. -/
theorem twoCoupledFlow_fst_of_lift_eq_zero (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (t : ℝ) (x : CPN (N + 1)) (θ : KTorus)
    {ψ : KTorus} (h : hg.lift ψ.2 = 0) :
    (twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)).1
      = (arenaForm_isSymplectic N).hamiltonianFlow (contMDiff_coupledEnergy A BA hf hc) t
          (x, θ) := by
  have hz : A + ((hg.lift ψ.2 : ℝ) : ℂ) • BB = A := by
    rw [h, Complex.ofReal_zero, zero_smul, add_zero]
  rw [twoCoupledFlow_fst hA hBA hBB hf hg hc hcg]
  simp only [hz]

/-- ★ **Where the first profile vanishes, the second slice is the one-torus flow of `(A, B_B)`.** -/
theorem twoCoupledFlow_snd_of_lift_eq_zero (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (t : ℝ) (x : CPN (N + 1)) {θ : KTorus}
    (ψ : KTorus) (h : hf.lift θ.2 = 0) :
    ((twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)).1.1,
        (twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)).2)
      = (arenaForm_isSymplectic N).hamiltonianFlow (contMDiff_coupledEnergy A BB hg hcg) t
          (x, ψ) := by
  have hz : A + ((hf.lift θ.2 : ℝ) : ℂ) • BA = A := by
    rw [h, Complex.ofReal_zero, zero_smul, add_zero]
  rw [twoCoupledFlow_snd hA hBA hBB hf hg hc hcg]
  simp only [hz]

end Flow

/-! ### The preserved measure -/

/-- ★ **A shear of one circle coordinate preserves the product measure**: on `α × (S¹ × β)`, add
to the circle coordinate an amount that depends measurably on the other two coordinates. The
fibre map over `x` is a swap, a skew product of the identity with a translation, and a swap. -/
theorem measurePreserving_addShear {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] {d : α → β → AddCircle (1 : ℝ)}
    (hd : Measurable (Function.uncurry d)) :
    MeasurePreserving
      (fun z : α × (AddCircle (1 : ℝ) × β) => (z.1, (z.2.1 + d z.1 z.2.2, z.2.2)))
      (μ.prod (volume.prod ν)) (μ.prod (volume.prod ν)) := by
  have hfib : ∀ x : α, MeasurePreserving
      (fun w : AddCircle (1 : ℝ) × β => (w.1 + d x w.2, w.2))
      (volume.prod ν) (volume.prod ν) := by
    intro x
    have h1 : MeasurePreserving (fun w : β × AddCircle (1 : ℝ) => (w.1, w.2 + d x w.1))
        (ν.prod volume) (ν.prod volume) := by
      refine (MeasurePreserving.id ν).skew_product ?_
        (ae_of_all _ fun y => (measurePreserving_add_right volume (d x y)).map_eq)
      show Measurable fun w : β × AddCircle (1 : ℝ) => w.2 + d x w.1
      exact measurable_snd.add (hd.comp (measurable_const.prodMk measurable_fst))
    have heq : (fun w : AddCircle (1 : ℝ) × β => (w.1 + d x w.2, w.2))
        = Prod.swap ∘ (fun w : β × AddCircle (1 : ℝ) => (w.1, w.2 + d x w.1)) ∘ Prod.swap := by
      funext w
      rfl
    rw [heq]
    exact Measure.measurePreserving_swap.comp (h1.comp Measure.measurePreserving_swap)
  refine (MeasurePreserving.id μ).skew_product ?_ (ae_of_all _ fun x => (hfib x).map_eq)
  show Measurable fun z : α × (AddCircle (1 : ℝ) × β) => (z.2.1 + d z.1 z.2.2, z.2.2)
  exact (measurable_snd.fst.add (hd.comp (measurable_fst.prodMk measurable_snd.snd))).prodMk
    measurable_snd.snd

/-- **The measure of the two-torus arena**: `μ_FS ⊗ vol_{T²} ⊗ vol_{T²}`. -/
noncomputable def echoMuL (p₀ : CPN (N + 1)) : Measure (EchoSigma N) :=
  (kMuL p₀).prod (volume : Measure KTorus)

section Volume

variable {f g : ℝ → ℝ} {A BA BB : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}

set_option synthInstance.maxSize 512 in
/-- ★★★ **The flow of the two-torus energy preserves `μ_FS ⊗ vol_{T²} ⊗ vol_{T²}`**, for every
`N` and all Hermitian matrices. Over each conserved `ψ₂` the first slice is a one-torus flow,
which preserves `kMuL`. The coordinate `ψ₁` is then translated by an amount that does not depend
on it. -/
theorem echoMuL_map_twoCoupledFlow (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (p₀ : CPN (N + 1)) (t : ℝ) :
    Measure.map (twoCoupledFlow A BA BB hf hg hc hcg t) (echoMuL p₀) = echoMuL p₀ := by
  have hΦm := measurable_twoCoupledFlow A BA BB hf hg hc hcg t
  -- the amount by which `ψ₁` is translated
  have hd : Measurable (Function.uncurry fun (σ : KSigma (N + 1)) (b : AddCircle (1 : ℝ)) =>
      (twoCoupledFlow A BA BB hf hg hc hcg t (σ, ((0 : AddCircle (1 : ℝ)), b))).2.1) :=
    (measurable_fst.comp (measurable_snd.comp hΦm)).comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hT := measurePreserving_addShear (kMuL p₀) (volume : Measure (AddCircle (1 : ℝ))) hd
  -- the first slice, over each `ψ`
  have h1 : MeasurePreserving (fun w : KTorus × KSigma (N + 1) =>
        (w.1, (twoCoupledFlow A BA BB hf hg hc hcg t (w.2, w.1)).1))
      ((volume : Measure KTorus).prod (kMuL p₀)) ((volume : Measure KTorus).prod (kMuL p₀)) := by
    refine MeasurePreserving.skew_product (μc := kMuL p₀) (μd := kMuL p₀)
      (g := fun (ψ : KTorus) (σ : KSigma (N + 1)) =>
        (twoCoupledFlow A BA BB hf hg hc hcg t (σ, ψ)).1)
      (MeasurePreserving.id (volume : Measure KTorus)) ?_ (ae_of_all _ fun ψ => ?_)
    · exact (measurable_fst.comp hΦm).comp (measurable_snd.prodMk measurable_fst)
    · have hs : (fun σ : KSigma (N + 1) => (twoCoupledFlow A BA BB hf hg hc hcg t (σ, ψ)).1)
          = (arenaForm_isSymplectic N).hamiltonianFlow
              (contMDiff_coupledEnergy (A + ((hg.lift ψ.2 : ℝ) : ℂ) • BB) BA hf hc) t := by
        funext σ
        exact twoCoupledFlow_fst hA hBA hBB hf hg hc hcg t σ.1 σ.2 ψ
      rw [hs]
      exact kMuL_map_hamiltonianFlow N p₀ _ t
  have hG : MeasurePreserving (fun z : EchoSigma N =>
        ((twoCoupledFlow A BA BB hf hg hc hcg t z).1, z.2)) (echoMuL p₀) (echoMuL p₀) :=
    Measure.measurePreserving_swap.comp (h1.comp Measure.measurePreserving_swap)
  have hcomp : twoCoupledFlow A BA BB hf hg hc hcg t
      = (fun z : EchoSigma N => ((twoCoupledFlow A BA BB hf hg hc hcg t z).1, z.2))
        ∘ (fun z : KSigma (N + 1) × (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) =>
          (z.1, (z.2.1 + (twoCoupledFlow A BA BB hf hg hc hcg t
            (z.1, ((0 : AddCircle (1 : ℝ)), z.2.2))).2.1, z.2.2))) := by
    funext z
    obtain ⟨⟨x, θ⟩, ψ₁, ψ₂⟩ := z
    simp only [Function.comp_apply, twoCoupledFlow_apply hA hBA hBB hf hg hc hcg, zero_add]
  rw [hcomp]
  exact (hG.comp hT).map_eq

end Volume

end LF4
end CSD

end

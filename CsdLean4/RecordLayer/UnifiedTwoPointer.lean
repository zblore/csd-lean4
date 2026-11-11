/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.EchoVolume
public import CsdLean4.RecordLayer.UnifiedDiracClock

/-!
# Two pointers on one arena: two site detectors, and the clock's pointer beside a site detector

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #359 — the author's programme "From `Σ` to
physical spacetime", between milestones M4 and M5. The shared arena `Σ_*` of #349 has one pointer
torus, coupled to one site. The clock extension of #357 has one pointer torus, coupled to the
level swap. M4's acceptance asks for clock readings and measurement records from the same
dynamics, and M5 for influence between recorded events. Both need two pointers in one joint
energy. This module builds that energy and solves its flow. It reads no record.

**The arena was already in the corpus.** `ℂℙᴺ × T² × T²`, its symplectic form and the closed-form
flow of an energy with two product terms are `LF4/EchoCoupledFlow.lean` (#202), for every `N` and
every Hermitian triple. The programme's contract had not adopted it. `LF4/EchoVolume.lean` adds
the two one-torus slices of that flow and its preserved measure. This module reads the flow on a
carrier with any finite index type and gives two instances.

**One carrier, one propagator, two displacements.** For Hermitian `A₀`, `B₀`, `C₀` the flow of

  `−2⟨A₀⟩ − 2 f(θ₂)⟨B₀⟩ − 2 h(ψ₂)⟨C₀⟩`

moves the carrier by `exp (−i t (A₀ + f(θ₂) B₀ + h(ψ₂) C₀))`, advances `θ₁` by
`−2 f'(θ₂) ∫₀ᵗ ⟨B₀⟩` and `ψ₁` by `−2 h'(ψ₂) ∫₀ᵗ ⟨C₀⟩`, both integrals along that one orbit, and
fixes `θ₂` and `ψ₂` (`twoCoupledFlow_reindex`). The energy has no term between the pointers. Each
acts on the other through the carrier only, as a static term in the carrier's generator.

**Cross-talk.** On a fibre where the second profile vanishes, the carrier and the first pointer
move exactly as they do with the first pointer alone (`idxTwoCarrierU_of_snd_lift_eq_zero`,
`idxTwoShiftFst_of_lift_eq_zero`). On every fibre the first pointer's displacement is within

  `2 |f'(θ₂)| ‖B₀‖ |h(ψ₂)| ‖C₀‖ t²`

of its displacement alone (`abs_idxTwoShiftFst_sub_le`). The same holds with the two pointers
exchanged (`abs_idxTwoShiftSnd_sub_le`).

**Two instances.**

1. The Dirac ring with a pointer on site `j` and a pointer on site `k`, on `ℂℙ^{2M+1} × T² × T²`.
   The flow is `diracTwoPointerFlow` and the carrier's generator is
   `H_D + g₁ f(θ₂) P_j + g₂ h(ψ₂) P_k` (`diracTwoH`, `hasDerivAt_diracTwoCarrierU`).
2. The two-level device of #357 with the clock's pointer and a pointer on site `k`, on
   `ℂℙ^{4M+3} × T² × T²`. The flow is `clockSiteFlow` and the generator is
   `H_dev + g₁ f(θ₂) X + g₂ h(ψ₂) Q_k` (`clockSiteH`, `hasDerivAt_clockSiteCarrierU`), with
   `Q_k = deviceSiteProj k` the site projector on both levels.

Each restricts exactly to the one-pointer flow of #349 or of #357 on the fibres where the other
profile vanishes, and each preserves `μ_FS ⊗ vol_{T²} ⊗ vol_{T²}`.

## The two-pointer flow in the coordinates of a carrier

For any finite index type and any Hermitian triple.

* `idxTwoH`, `idxCoupledH_idxCoupledH_fst`, `idxCoupledH_idxCoupledH_snd`, `idxTwoH_isHermitian`,
  `idxCoupledH_of_lift_eq_zero`, `idxCarrierU_congr`, `idxPointerShift_congr`;
* `idxTwoCarrierU`, `idxTwoCarrierU_val`, `idxCarrierU_snd_eq_idxTwoCarrierU`,
  ★★ `hasDerivAt_idxTwoCarrierU` — the carrier's equation, `continuous_idxTwoCarrierU`;
* `idxTwoCarrierU_of_snd_lift_eq_zero`, `idxTwoCarrierU_of_fst_lift_eq_zero`;
* `idxTwoShiftFst`, `idxTwoShiftSnd`, `idxTwoShiftFst_eq`, ★ `idxTwoShiftSnd_eq` — both
  displacements along the one orbit;
* `idxTwoShiftFst_of_lift_eq_zero`, `idxTwoShiftSnd_of_lift_eq_zero`;
* `twoCoupledEnergy_reindex`, ★★★ `twoCoupledFlow_reindex` — **the flow, solved**.

## Cross-talk between the two pointers

* `norm_idxCarrierU_sub_idxCarrierU_le`, `abs_integral_arenaObs_idxCarrierU_sub_idxCarrierU_le`,
  `abs_idxPointerShift_sub_idxPointerShift_le`, `norm_idxCoupledH_sub` — two carriers with
  different free parts;
* ★ `norm_idxTwoCarrierU_sub_fst_le`, ★ `norm_idxTwoCarrierU_sub_snd_le`;
* ★★ `abs_idxTwoShiftFst_sub_le`, ★★ `abs_idxTwoShiftSnd_sub_le`.

## Real coupling strengths

* `isHermitian_ofReal_smul`, `norm_ofReal_smul_le`, `idxTwoH_ofReal_smul`,
  `idxPointerShift_ofReal_smul`, `idxTwoShiftFst_ofReal_smul`, `idxTwoShiftSnd_ofReal_smul`;
* `norm_idxTwoCarrierU_sub_fst_le_of_norm_le`, `norm_idxTwoCarrierU_sub_snd_le_of_norm_le`,
  ★★ `abs_idxTwoShiftFst_sub_le_of_norm_le`, ★★ `abs_idxTwoShiftSnd_sub_le_of_norm_le`.

## Two site detectors on the Dirac ring

* `siteProj_smul_isHermitian`, `idxCarrierU_dirac`, `idxPointerShift_dirac` — the objects of #349
  as instances of the generic one-pointer layer;
* `diracTwoPointerEnergy`, `diracTwoPointerEnergy_eq`, `diracTwoH`, `diracTwoCarrierU`,
  `diracTwoCarrierU_val`, ★★ `hasDerivAt_diracTwoCarrierU`;
* `diracTwoShiftFst`, `diracTwoShiftSnd`, `idxTwoShiftFst_diracTwo`, `idxTwoShiftSnd_diracTwo`;
* `diracTwoPointerFlow`, `diracTwoPointerFlow_zero`, `diracTwoPointerFlow_add`,
  ★★★ `diracTwoPointerFlow_apply`, `diracTwoPointerFlow_angles`;
* ★★ `diracTwoPointerFlow_fst_of_lift_eq_zero`, ★★ `diracTwoPointerFlow_snd_of_lift_eq_zero` — each
  detector alone, exactly;
* ★★ `echoMuL_map_diracTwoPointerFlow`;
* ★ `norm_diracTwoCarrierU_sub_le`, ★★ `abs_diracTwoShiftFst_sub_le`,
  ★★ `abs_diracTwoShiftSnd_sub_le`.

## The clock's pointer and a site detector on one device

* `deviceSiteProj`, `deviceSiteProj_eq_diagonal`, `deviceSiteProj_isHermitian`,
  `deviceSiteProj_mul_self`, `norm_deviceSiteProj_le`, `deviceSiteProj_smul_isHermitian`;
* `clockSiteEnergy`, `clockSiteEnergy_eq`, `clockSiteH`, `clockSiteCarrierU`,
  `clockSiteCarrierU_val`, ★★ `hasDerivAt_clockSiteCarrierU`;
* `clockSiteShiftFst`, `clockSiteShiftSnd`, `idxTwoShiftFst_clockSite`,
  `idxTwoShiftSnd_clockSite`;
* `clockSiteFlow`, `clockSiteFlow_zero`, `clockSiteFlow_add`, ★★★ `clockSiteFlow_apply`,
  `clockSiteFlow_angles`;
* ★★ `clockSiteFlow_fst_of_lift_eq_zero` — the clock alone, exactly;
  ★ `clockSiteFlow_snd_of_lift_eq_zero`;
* ★★ `echoMuL_map_clockSiteFlow`;
* ★★ `norm_clockSiteCarrierU_sub_le`, ★★ `abs_clockSiteShiftFst_sub_le`,
  ★★ `abs_clockSiteShiftSnd_sub_le`.

## Honest scope

* **No record is read.** There is no readout region, no ready state, no threshold and no
  `ActualOccurrence` on either arena. The flows are solved and nothing is read off them. In
  particular no theorem here has a tick record and a position record in one run. M4's acceptance
  sentence is met no further than #358 met it. What this module supplies is the one dynamics those
  two records would both have to come from. Both are read off `clockSiteFlow` in
  `RecordLayer/UnifiedClockSiteRecords.lean` (#360). The arena of two site detectors gets a
  readout on each torus in `RecordLayer/UnifiedTwoSiteRecords.lean` (#364).
* **No propagation bound.** The cross-talk bounds do not depend on the distance between the two
  sites. They are not a cone bound, and they say nothing about when the second detector's
  influence can reach the first. M5's bound is for the generators `diracTwoH` and `clockSiteH`,
  and it is not proved here. It is in `RecordLayer/UnifiedCausalOrder.lean` (#361).
* **What is exact and what is bounded.** The closed forms, the two reductions and the measure
  statement are exact. The cross-talk statements are upper bounds that grow as `t²`. They are not
  shown to be attained.
* **The exact reduction holds on a null set of fibres.** For a generic profile the fibres on
  which it vanishes have measure zero. The theorems of #349 to #358 transfer to these arenas
  verbatim on those fibres, and elsewhere only up to the cross-talk bound. None of them is proved
  again here on the two-pointer arenas.
* **A pointer the carrier does not see can still move.** On a fibre with `h(ψ₂) = 0` and
  `h'(ψ₂) ≠ 0` the second pointer is displaced by the occupancy while the carrier's generator has
  no term from it.
* **Two tori, not a family.** A third pointer needs one more product form. A radar exchange with
  an emission record, a reception record and a clock is likely to need more than two.
* **The product measure is an assumption.** `echoMuL` makes the two pointers' fibre coordinates
  independent and uniform at the start. That is UA-13. Its invariance is read off the closed form
  (`echoMuL_map_twoCoupledFlow`), and the top-form measure of `echoForm` is not identified with it.
* **`deviceSiteProj` is a definition.** It is the site projector of the ring on each level, so it
  is diagonal, a projector, and of norm at most one. That its expectation is the occupancy of the
  site is the definition.
* **The site pointer alone on the device has no module.** `clockSiteFlow_snd_of_lift_eq_zero` and
  `abs_clockSiteShiftSnd_sub_le` are stated against the generic one-pointer flow and displacement
  of the pair `(H_dev, g₂ Q_k)`.
* **The generic layer is not about detectors.** The first three sections hold for every Hermitian
  triple.
* **What is assumed** (`specs/unified-record-spacetime-plan.md`, Register 1): the two-pointer
  arena, its product measure and the additive energy with no term between the pointers (UA-13);
  the couplings (UA-5, UA-12); the propagation law (UA-8). The profiles and the coupling strengths
  are apparatus input (UA-4). Every time is the flow parameter (UA-7). No probability is stated,
  and UA-6 is not used.

References: `specs/BACKLOG.md` #359, #358, #357, #349, #225, #202; `specs/future-work.md`;
`specs/unified-record-spacetime-plan.md` (UA-13; UO-10, UO-13, UO-14, UO-15; UD-66 to UD-71);
`LF4/EchoVolume.lean` (`twoCoupledFlow_fst`, `twoCoupledFlow_snd`, `echoMuL_map_twoCoupledFlow`);
`LF4/EchoCoupledFlow.lean` (`hamiltonianFlow_twoCoupledEnergy`);
`RecordLayer/UnifiedDiracClock.lean` (`idxCarrierU`, `idxPointerShift`,
`hamiltonianFlow_coupledEnergy_reindex`, `clockPointerFlow`, `idxPointerShift_clock`);
`RecordLayer/DiracPointerHamiltonian.lean` (`diracPointerFlow`, `diracCarrierU`,
`diracPointerShift`); `RecordLayer/DiracPointerWrite.lean` (`norm_siteProj_le`,
`abs_arenaObs_arenaKick_sub_le`); `Mathlib/Analysis/Matrix/DuhamelBound.lean`
(`Matrix.norm_exp_smul_neg_I_sub_le`); `CV/DiracDevice.lean` (`deviceHam`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The two-pointer flow in the coordinates of a carrier -/

section Indexed

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} (e : ι ≃ Fin (N + 1))
  {f h : ℝ → ℝ} {A₀ B₀ C₀ : Matrix ι ι ℂ}

/-- **The carrier's Hamiltonian at the pointer angles `φ = θ₂`, `χ = ψ₂`**, in the carrier's own
index: `A₀ + f(φ) B₀ + h(χ) C₀`. -/
noncomputable def idxTwoH (A₀ B₀ C₀ : Matrix ι ι ℂ) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) : Matrix ι ι ℂ :=
  A₀ + ((hf.lift φ : ℝ) : ℂ) • B₀ + ((hh.lift χ : ℝ) : ℂ) • C₀

omit [Fintype ι] [DecidableEq ι] in
/-- The first pointer's one-pointer Hamiltonian over `A₀ + h(χ) C₀` is the two-pointer one. -/
theorem idxCoupledH_idxCoupledH_fst (A₀ B₀ C₀ : Matrix ι ι ℂ) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) :
    idxCoupledH (idxCoupledH A₀ C₀ hh χ) B₀ hf φ = idxTwoH A₀ B₀ C₀ hf hh φ χ := by
  unfold idxCoupledH idxTwoH
  exact add_right_comm _ _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The second pointer's one-pointer Hamiltonian over `A₀ + f(φ) B₀` is the two-pointer one. -/
theorem idxCoupledH_idxCoupledH_snd (A₀ B₀ C₀ : Matrix ι ι ℂ) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) :
    idxCoupledH (idxCoupledH A₀ B₀ hf φ) C₀ hh χ = idxTwoH A₀ B₀ C₀ hf hh φ χ :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The two-pointer Hamiltonian of the carrier is Hermitian. -/
theorem idxTwoH_isHermitian (hA : A₀.IsHermitian) (hB : B₀.IsHermitian) (hC : C₀.IsHermitian)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) :
    (idxTwoH A₀ B₀ C₀ hf hh φ χ).IsHermitian :=
  idxCoupledH_isHermitian (idxCoupledH_isHermitian hA hB hf φ) hC hh χ

omit [Fintype ι] [DecidableEq ι] in
/-- On a fibre where the profile vanishes the one-pointer Hamiltonian is the uncoupled one. -/
theorem idxCoupledH_of_lift_eq_zero (A₀ B₀ : Matrix ι ι ℂ) (hf : Function.Periodic f 1)
    {φ : AddCircle (1 : ℝ)} (hz : hf.lift φ = 0) : idxCoupledH A₀ B₀ hf φ = A₀ := by
  rw [idxCoupledH, hz, Complex.ofReal_zero, zero_smul, add_zero]

/-- The one-pointer propagator depends on the uncoupled matrix only. -/
theorem idxCarrierU_congr {A₁ A₂ : Matrix ι ι ℂ} (hA : A₁ = A₂) (h₁ : A₁.IsHermitian)
    (h₂ : A₂.IsHermitian) (hB : B₀.IsHermitian) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    idxCarrierU h₁ hB hf φ t = idxCarrierU h₂ hB hf φ t := by
  subst hA
  rfl

/-- The one-pointer displacement depends on the uncoupled matrix only. -/
theorem idxPointerShift_congr {A₁ A₂ : Matrix ι ι ℂ} (hA : A₁ = A₂) (h₁ : A₁.IsHermitian)
    (h₂ : A₂.IsHermitian) (hB : B₀.IsHermitian) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) (p : GenArena ι) (t : ℝ) :
    idxPointerShift h₁ hB hf φ p t = idxPointerShift h₂ hB hf φ p t := by
  subst hA
  rfl

/-- **The carrier's propagator with two pointers** `exp (−i t (A₀ + f(φ) B₀ + h(χ) C₀))` on the
fibre `θ₂ = φ`, `ψ₂ = χ`. It is the one-pointer propagator of the first pointer over the matrix
`A₀ + h(χ) C₀`. -/
noncomputable def idxTwoCarrierU (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (t : ℝ) : Matrix.unitaryGroup ι ℂ :=
  idxCarrierU (idxCoupledH_isHermitian hA hC hh χ) hB hf φ t

/-- The two-pointer propagator as a matrix exponential. -/
theorem idxTwoCarrierU_val (hA : A₀.IsHermitian) (hB : B₀.IsHermitian) (hC : C₀.IsHermitian)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    (idxTwoCarrierU hA hB hC hf hh φ χ t).val
      = exp (t • ((-Complex.I) • idxTwoH A₀ B₀ C₀ hf hh φ χ)) := by
  rw [idxTwoCarrierU, idxCarrierU_val, idxCoupledH_idxCoupledH_fst]

/-- **Neither pointer is singled out**: the one-pointer propagator of the second pointer over
`A₀ + f(φ) B₀` is the same unitary. -/
theorem idxCarrierU_snd_eq_idxTwoCarrierU (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    idxCarrierU (idxCoupledH_isHermitian hA hB hf φ) hC hh χ t
      = idxTwoCarrierU hA hB hC hf hh φ χ t := by
  apply Subtype.ext
  rw [idxTwoCarrierU_val, idxCarrierU_val, idxCoupledH_idxCoupledH_snd]

/-- ★★ **The carrier's equation with two pointers**:
`U̇(t) = −i (A₀ + f(θ₂) B₀ + h(ψ₂) C₀) U(t)`. -/
theorem hasDerivAt_idxTwoCarrierU (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (idxTwoCarrierU hA hB hC hf hh φ χ s).val)
      (((-Complex.I) • idxTwoH A₀ B₀ C₀ hf hh φ χ) * (idxTwoCarrierU hA hB hC hf hh φ χ t).val)
      t := by
  rw [← idxCoupledH_idxCoupledH_fst]
  exact hasDerivAt_idxCarrierU (idxCoupledH_isHermitian hA hC hh χ) hB hf φ t

/-- The two-pointer propagator is continuous in the flow parameter. -/
theorem continuous_idxTwoCarrierU (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) :
    Continuous fun t : ℝ => idxTwoCarrierU hA hB hC hf hh φ χ t :=
  continuous_idxCarrierU (idxCoupledH_isHermitian hA hC hh χ) hB hf φ

/-- On a fibre where the second profile vanishes the carrier sees the first pointer only. -/
theorem idxTwoCarrierU_of_snd_lift_eq_zero (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ : AddCircle (1 : ℝ)) {χ : AddCircle (1 : ℝ)} (hz : hh.lift χ = 0) (t : ℝ) :
    idxTwoCarrierU hA hB hC hf hh φ χ t = idxCarrierU hA hB hf φ t :=
  idxCarrierU_congr (idxCoupledH_of_lift_eq_zero A₀ C₀ hh hz) _ hA hB hf φ t

/-- On a fibre where the first profile vanishes the carrier sees the second pointer only. -/
theorem idxTwoCarrierU_of_fst_lift_eq_zero (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    {φ : AddCircle (1 : ℝ)} (χ : AddCircle (1 : ℝ)) (hz : hf.lift φ = 0) (t : ℝ) :
    idxTwoCarrierU hA hB hC hf hh φ χ t = idxCarrierU hA hC hh χ t := by
  rw [← idxCarrierU_snd_eq_idxTwoCarrierU]
  exact idxCarrierU_congr (idxCoupledH_of_lift_eq_zero A₀ B₀ hf hz) _ hA hC hh χ t

/-- **The first pointer's lifted displacement** on the shared carrier: the one-pointer
displacement over the matrix `A₀ + h(χ) C₀`. -/
noncomputable def idxTwoShiftFst (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) (t : ℝ) : ℝ :=
  idxPointerShift (idxCoupledH_isHermitian hA hC hh χ) hB hf φ p t

/-- **The second pointer's lifted displacement** on the shared carrier: the one-pointer
displacement over the matrix `A₀ + f(φ) B₀`. -/
noncomputable def idxTwoShiftSnd (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) (t : ℝ) : ℝ :=
  idxPointerShift (idxCoupledH_isHermitian hA hB hf φ) hC hh χ p t

/-- The first pointer integrates `⟨B₀⟩` along the common orbit. -/
theorem idxTwoShiftFst_eq (hA : A₀.IsHermitian) (hB : B₀.IsHermitian) (hC : C₀.IsHermitian)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ι) (t : ℝ) :
    idxTwoShiftFst hA hB hC hf hh φ χ p t
      = -2 * hf.deriv_periodic.lift φ
        * ∫ s in (0 : ℝ)..t, arenaObs B₀ (arenaKick (idxTwoCarrierU hA hB hC hf hh φ χ s) p) :=
  rfl

/-- ★ The second pointer integrates `⟨C₀⟩` along the same orbit. -/
theorem idxTwoShiftSnd_eq (hA : A₀.IsHermitian) (hB : B₀.IsHermitian) (hC : C₀.IsHermitian)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ι) (t : ℝ) :
    idxTwoShiftSnd hA hB hC hf hh φ χ p t
      = -2 * hh.deriv_periodic.lift χ
        * ∫ s in (0 : ℝ)..t, arenaObs C₀ (arenaKick (idxTwoCarrierU hA hB hC hf hh φ χ s) p) := by
  rw [idxTwoShiftSnd, idxPointerShift]
  simp only [idxCarrierU_snd_eq_idxTwoCarrierU hA hB hC hf hh φ χ]

/-- On a fibre where the second profile vanishes the first pointer moves as if alone. -/
theorem idxTwoShiftFst_of_lift_eq_zero (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ : AddCircle (1 : ℝ)) {χ : AddCircle (1 : ℝ)} (hz : hh.lift χ = 0) (p : GenArena ι)
    (t : ℝ) :
    idxTwoShiftFst hA hB hC hf hh φ χ p t = idxPointerShift hA hB hf φ p t :=
  idxPointerShift_congr (idxCoupledH_of_lift_eq_zero A₀ C₀ hh hz) _ hA hB hf φ p t

/-- On a fibre where the first profile vanishes the second pointer moves as if alone. -/
theorem idxTwoShiftSnd_of_lift_eq_zero (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    {φ : AddCircle (1 : ℝ)} (χ : AddCircle (1 : ℝ)) (hz : hf.lift φ = 0) (p : GenArena ι)
    (t : ℝ) :
    idxTwoShiftSnd hA hB hC hf hh φ χ p t = idxPointerShift hA hC hh χ p t :=
  idxPointerShift_congr (idxCoupledH_of_lift_eq_zero A₀ B₀ hf hz) _ hA hC hh χ p t

omit [DecidableEq ι] in
/-- **The two-pointer energy of a reindexed triple**, read on the carrier:
`−2⟨A₀⟩_p − 2 f(θ₂) ⟨B₀⟩_p − 2 h(ψ₂) ⟨C₀⟩_p`. -/
theorem twoCoupledEnergy_reindex (A₀ B₀ C₀ : Matrix ι ι ℂ) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (p : GenArena ι) (θ ψ : KTorus) :
    twoCoupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) (Matrix.reindex e e C₀)
        hf hh ((idxArenaEquiv e p, θ), ψ)
      = -2 * arenaObs A₀ p - 2 * hf.lift θ.2 * arenaObs B₀ p
        - 2 * hh.lift ψ.2 * arenaObs C₀ p := by
  show coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf (idxArenaEquiv e p, θ)
      + schrodingerHamiltonian (Matrix.reindex e e C₀) (idxArenaEquiv e p) * hh.lift ψ.2 = _
  rw [coupledEnergy_reindex, schrodingerHamiltonian_reindex]
  ring

/-- ★★★ **The two-pointer flow, solved on the carrier.** The flow of
`−2⟨A₀⟩ − 2 f(θ₂)⟨B₀⟩ − 2 h(ψ₂)⟨C₀⟩` moves the carrier by
`exp (−i t (A₀ + f(θ₂) B₀ + h(ψ₂) C₀))`, advances `θ₁` by `−2 f'(θ₂) ∫₀ᵗ ⟨B₀⟩` and `ψ₁` by
`−2 h'(ψ₂) ∫₀ᵗ ⟨C₀⟩` along that one orbit, and fixes `θ₂` and `ψ₂`. -/
theorem twoCoupledFlow_reindex (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) (p : GenArena ι) (θ ψ : KTorus) :
    twoCoupledFlow (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) (Matrix.reindex e e C₀)
        hf hh hc hch t ((idxArenaEquiv e p, θ), ψ)
      = ((idxArenaEquiv e (arenaKick (idxTwoCarrierU hA hB hC hf hh θ.2 ψ.2 t) p),
          (θ.1 + ((idxTwoShiftFst hA hB hC hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)), θ.2)),
         (ψ.1 + ((idxTwoShiftSnd hA hB hC hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)),
          ψ.2)) := by
  have h1 := twoCoupledFlow_fst (hA.reindex e) (hB.reindex e) (hC.reindex e) hf hh hc hch t
    (idxArenaEquiv e p) θ ψ
  have h1' : (arenaForm_isSymplectic N).hamiltonianFlow
      (contMDiff_coupledEnergy (Matrix.reindex e e A₀ + ((hh.lift ψ.2 : ℝ) : ℂ)
        • Matrix.reindex e e C₀) (Matrix.reindex e e B₀) hf hc) t (idxArenaEquiv e p, θ) = _ :=
    hamiltonianFlow_coupledEnergy_reindex e (idxCoupledH_isHermitian hA hC hh ψ.2) hB hf hc t p θ
  have h2 := twoCoupledFlow_snd (hA.reindex e) (hB.reindex e) (hC.reindex e) hf hh hc hch t
    (idxArenaEquiv e p) θ ψ
  have h2' : (arenaForm_isSymplectic N).hamiltonianFlow
      (contMDiff_coupledEnergy (Matrix.reindex e e A₀ + ((hf.lift θ.2 : ℝ) : ℂ)
        • Matrix.reindex e e B₀) (Matrix.reindex e e C₀) hh hch) t (idxArenaEquiv e p, ψ) = _ :=
    hamiltonianFlow_coupledEnergy_reindex e (idxCoupledH_isHermitian hA hB hf θ.2) hC hh hch t p ψ
  have h3 : _ = _ := congrArg Prod.snd (h2.trans h2')
  exact Prod.ext (h1.trans h1') h3

/-! ### Cross-talk between the two pointers -/

section Bound

variable [Nonempty ι]

/-- Two one-pointer propagators over different uncoupled matrices differ by at most `|t|` times
the norm of the difference of the matrices. -/
theorem norm_idxCarrierU_sub_idxCarrierU_le {A₁ A₂ : Matrix ι ι ℂ} (h₁ : A₁.IsHermitian)
    (h₂ : A₂.IsHermitian) (hB : B₀.IsHermitian) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(idxCarrierU h₁ hB hf φ t).val - (idxCarrierU h₂ hB hf φ t).val‖ ≤ |t| * ‖A₁ - A₂‖ := by
  rw [idxCarrierU_val, idxCarrierU_val]
  refine (Matrix.norm_exp_smul_neg_I_sub_le _ _ (idxCoupledH_isHermitian h₁ hB hf φ)
    (idxCoupledH_isHermitian h₂ hB hf φ) t).trans_eq ?_
  rw [idxCoupledH, idxCoupledH, add_sub_add_right_eq_sub]

/-- The integrated expectation along two such orbits differs by at most
`‖D‖ ‖A₁ − A₂‖ t²`. -/
theorem abs_integral_arenaObs_idxCarrierU_sub_idxCarrierU_le {A₁ A₂ : Matrix ι ι ℂ}
    (h₁ : A₁.IsHermitian) (h₂ : A₂.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (D : Matrix ι ι ℂ) (p : GenArena ι)
    {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (idxCarrierU h₁ hB hf φ s) p))
        - ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (idxCarrierU h₂ hB hf φ s) p)|
      ≤ ‖D‖ * ‖A₁ - A₂‖ * t ^ 2 := by
  have hU : Continuous fun s => arenaObs D (arenaKick (idxCarrierU h₁ hB hf φ s) p) :=
    (continuous_arenaObs D).comp ((continuous_idxCarrierU h₁ hB hf φ).arenaKick continuous_const)
  have hV : Continuous fun s => arenaObs D (arenaKick (idxCarrierU h₂ hB hf φ s) p) :=
    (continuous_arenaObs D).comp ((continuous_idxCarrierU h₂ hB hf φ).arenaKick continuous_const)
  rw [← intervalIntegral.integral_sub (hU.intervalIntegrable 0 t) (hV.intervalIntegrable 0 t)]
  have hc : Continuous fun s : ℝ => 2 * ‖D‖ * (s * ‖A₁ - A₂‖) := by fun_prop
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  refine (intervalIntegral.integral_mono_on ht ((hU.sub hV).abs.intervalIntegrable 0 t)
    (hc.intervalIntegrable 0 t) fun s hs => ?_).trans_eq ?_
  · have h := (abs_arenaObs_arenaKick_sub_le (idxCarrierU h₁ hB hf φ s)
      (idxCarrierU h₂ hB hf φ s) D p).trans (mul_le_mul_of_nonneg_left
        (norm_idxCarrierU_sub_idxCarrierU_le h₁ h₂ hB hf φ s) (by positivity))
    rwa [abs_of_nonneg hs.1] at h
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, integral_id]
    ring

/-- The one-pointer displacements over two uncoupled matrices differ by at most
`2 |f'(φ)| ‖B₀‖ ‖A₁ − A₂‖ t²`. -/
theorem abs_idxPointerShift_sub_idxPointerShift_le {A₁ A₂ : Matrix ι ι ℂ}
    (h₁ : A₁.IsHermitian) (h₂ : A₂.IsHermitian) (hB : B₀.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (p : GenArena ι) {t : ℝ}
    (ht : 0 ≤ t) :
    |idxPointerShift h₁ hB hf φ p t - idxPointerShift h₂ hB hf φ p t|
      ≤ 2 * |hf.deriv_periodic.lift φ| * (‖B₀‖ * ‖A₁ - A₂‖ * t ^ 2) := by
  rw [idxPointerShift, idxPointerShift, ← mul_sub, abs_mul, abs_mul, abs_neg, abs_two]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_arenaObs_idxCarrierU_sub_idxCarrierU_le h₁ h₂ hB hf φ B₀ p ht) (by positivity)

omit [Nonempty ι] in
/-- The coupling term of the one-pointer Hamiltonian has norm `|f(φ)| ‖B₀‖`. -/
theorem norm_idxCoupledH_sub (A₀ B₀ : Matrix ι ι ℂ) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) : ‖idxCoupledH A₀ B₀ hf φ - A₀‖ = |hf.lift φ| * ‖B₀‖ := by
  rw [idxCoupledH, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- ★ The carrier with both pointers stays within `|t| |h(χ)| ‖C₀‖` of the carrier with the first
pointer alone. -/
theorem norm_idxTwoCarrierU_sub_fst_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(idxTwoCarrierU hA hB hC hf hh φ χ t).val - (idxCarrierU hA hB hf φ t).val‖
      ≤ |t| * (|hh.lift χ| * ‖C₀‖) := by
  have key := norm_idxCarrierU_sub_idxCarrierU_le (idxCoupledH_isHermitian hA hC hh χ) hA hB hf
    φ t
  rwa [norm_idxCoupledH_sub] at key

/-- ★ The carrier with both pointers stays within `|t| |f(φ)| ‖B₀‖` of the carrier with the second
pointer alone. -/
theorem norm_idxTwoCarrierU_sub_snd_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(idxTwoCarrierU hA hB hC hf hh φ χ t).val - (idxCarrierU hA hC hh χ t).val‖
      ≤ |t| * (|hf.lift φ| * ‖B₀‖) := by
  have key := norm_idxCarrierU_sub_idxCarrierU_le (idxCoupledH_isHermitian hA hB hf φ) hA hC hh
    χ t
  rwa [norm_idxCoupledH_sub, idxCarrierU_snd_eq_idxTwoCarrierU] at key

/-- ★★ **Cross-talk on the first pointer.** With the second pointer coupled, the first pointer's
displacement is within `2 |f'(φ)| ‖B₀‖ |h(χ)| ‖C₀‖ t²` of its displacement alone. -/
theorem abs_idxTwoShiftFst_sub_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) {t : ℝ} (ht : 0 ≤ t) :
    |idxTwoShiftFst hA hB hC hf hh φ χ p t - idxPointerShift hA hB hf φ p t|
      ≤ 2 * |hf.deriv_periodic.lift φ| * (‖B₀‖ * (|hh.lift χ| * ‖C₀‖) * t ^ 2) := by
  have key := abs_idxPointerShift_sub_idxPointerShift_le (idxCoupledH_isHermitian hA hC hh χ) hA
    hB hf φ p ht
  rwa [norm_idxCoupledH_sub] at key

/-- ★★ **Cross-talk on the second pointer.** With the first pointer coupled, the second pointer's
displacement is within `2 |h'(χ)| ‖C₀‖ |f(φ)| ‖B₀‖ t²` of its displacement alone. -/
theorem abs_idxTwoShiftSnd_sub_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) {t : ℝ} (ht : 0 ≤ t) :
    |idxTwoShiftSnd hA hB hC hf hh φ χ p t - idxPointerShift hA hC hh χ p t|
      ≤ 2 * |hh.deriv_periodic.lift χ| * (‖C₀‖ * (|hf.lift φ| * ‖B₀‖) * t ^ 2) := by
  have key := abs_idxPointerShift_sub_idxPointerShift_le (idxCoupledH_isHermitian hA hB hf φ) hA
    hC hh χ p ht
  rwa [norm_idxCoupledH_sub] at key

end Bound

/-! ### Real coupling strengths -/

section Scaled

variable {P Q : Matrix ι ι ℂ}

omit [Fintype ι] [DecidableEq ι] in
/-- A real multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_ofReal_smul (g : ℝ) (hP : P.IsHermitian) : ((g : ℂ) • P).IsHermitian :=
  hP.smul (isSelfAdjoint_iff.2 (by rw [Complex.star_def, Complex.conj_ofReal]))

/-- A real multiple of a matrix of norm at most one has norm at most the multiplier's size. -/
theorem norm_ofReal_smul_le (g : ℝ) (hP : ‖P‖ ≤ 1) : ‖(g : ℂ) • P‖ ≤ |g| := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) hP

omit [Fintype ι] [DecidableEq ι] in
/-- The two-pointer Hamiltonian with coupling strengths `g₁`, `g₂`:
`A₀ + g₁ f(φ) P + g₂ h(χ) Q`. -/
theorem idxTwoH_ofReal_smul (A₀ P Q : Matrix ι ι ℂ) (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) :
    idxTwoH A₀ ((g₁ : ℂ) • P) ((g₂ : ℂ) • Q) hf hh φ χ
      = A₀ + ((g₁ * hf.lift φ : ℝ) : ℂ) • P + ((g₂ * hh.lift χ : ℝ) : ℂ) • Q := by
  rw [idxTwoH, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    mul_comm (hf.lift φ) g₁, mul_comm (hh.lift χ) g₂]

/-- The one-pointer displacement with a coupling strength `g`: `−2 g f'(φ) ∫₀ᵗ ⟨P⟩`. -/
theorem idxPointerShift_ofReal_smul (g : ℝ) (hA : A₀.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (p : GenArena ι) (t : ℝ) :
    idxPointerShift hA (isHermitian_ofReal_smul g hP) hf φ p t
      = -(2 * g) * hf.deriv_periodic.lift φ
        * ∫ s in (0 : ℝ)..t,
            arenaObs P (arenaKick (idxCarrierU hA (isHermitian_ofReal_smul g hP) hf φ s) p) := by
  rw [idxPointerShift]
  simp only [arenaObs_real_smul]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The first pointer's displacement with a coupling strength `g₁`. -/
theorem idxTwoShiftFst_ofReal_smul (g₁ : ℝ) (hA : A₀.IsHermitian) (hP : P.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) (t : ℝ) :
    idxTwoShiftFst hA (isHermitian_ofReal_smul g₁ hP) hC hf hh φ χ p t
      = -(2 * g₁) * hf.deriv_periodic.lift φ
        * ∫ s in (0 : ℝ)..t, arenaObs P
            (arenaKick (idxTwoCarrierU hA (isHermitian_ofReal_smul g₁ hP) hC hf hh φ χ s) p) :=
  idxPointerShift_ofReal_smul g₁ (idxCoupledH_isHermitian hA hC hh χ) hP hf φ p t

/-- The second pointer's displacement with a coupling strength `g₂`. -/
theorem idxTwoShiftSnd_ofReal_smul (g₂ : ℝ) (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hQ : Q.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) (t : ℝ) :
    idxTwoShiftSnd hA hB (isHermitian_ofReal_smul g₂ hQ) hf hh φ χ p t
      = -(2 * g₂) * hh.deriv_periodic.lift χ
        * ∫ s in (0 : ℝ)..t, arenaObs Q
            (arenaKick (idxTwoCarrierU hA hB (isHermitian_ofReal_smul g₂ hQ) hf hh φ χ s) p) := by
  rw [idxTwoShiftSnd_eq]
  simp only [arenaObs_real_smul]
  rw [intervalIntegral.integral_const_mul]
  ring

variable [Nonempty ι]

/-- The carrier with both pointers against the carrier with the first alone, for a second
coupling `g₂ Q` with `‖Q‖ ≤ 1`: within `|t| |h(χ)| |g₂|`. -/
theorem norm_idxTwoCarrierU_sub_fst_le_of_norm_le (g₂ : ℝ) (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (hQ : Q.IsHermitian) (hQn : ‖Q‖ ≤ 1) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(idxTwoCarrierU hA hB (isHermitian_ofReal_smul g₂ hQ) hf hh φ χ t).val
        - (idxCarrierU hA hB hf φ t).val‖ ≤ |t| * (|hh.lift χ| * |g₂|) := by
  refine (norm_idxTwoCarrierU_sub_fst_le hA hB _ hf hh φ χ t).trans ?_
  gcongr
  exact norm_ofReal_smul_le g₂ hQn

/-- The carrier with both pointers against the carrier with the second alone, for a first
coupling `g₁ P` with `‖P‖ ≤ 1`: within `|t| |f(φ)| |g₁|`. -/
theorem norm_idxTwoCarrierU_sub_snd_le_of_norm_le (g₁ : ℝ) (hA : A₀.IsHermitian)
    (hP : P.IsHermitian) (hC : C₀.IsHermitian) (hPn : ‖P‖ ≤ 1) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(idxTwoCarrierU hA (isHermitian_ofReal_smul g₁ hP) hC hf hh φ χ t).val
        - (idxCarrierU hA hC hh χ t).val‖ ≤ |t| * (|hf.lift φ| * |g₁|) := by
  refine (norm_idxTwoCarrierU_sub_snd_le hA _ hC hf hh φ χ t).trans ?_
  gcongr
  exact norm_ofReal_smul_le g₁ hPn

/-- ★★ **Cross-talk on the first pointer, in the coupling strengths**: for couplings `g₁ P` and
`g₂ Q` with `‖P‖, ‖Q‖ ≤ 1`, within `2 |f'(φ)| |g₁| |h(χ)| |g₂| t²`. -/
theorem abs_idxTwoShiftFst_sub_le_of_norm_le (g₁ g₂ : ℝ) (hA : A₀.IsHermitian)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hPn : ‖P‖ ≤ 1) (hQn : ‖Q‖ ≤ 1)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ι) {t : ℝ} (ht : 0 ≤ t) :
    |idxTwoShiftFst hA (isHermitian_ofReal_smul g₁ hP) (isHermitian_ofReal_smul g₂ hQ) hf hh φ χ
          p t - idxPointerShift hA (isHermitian_ofReal_smul g₁ hP) hf φ p t|
      ≤ 2 * |hf.deriv_periodic.lift φ| * (|g₁| * (|hh.lift χ| * |g₂|) * t ^ 2) := by
  refine (abs_idxTwoShiftFst_sub_le hA _ _ hf hh φ χ p ht).trans ?_
  gcongr
  · exact norm_ofReal_smul_le g₁ hPn
  · exact norm_ofReal_smul_le g₂ hQn

/-- ★★ **Cross-talk on the second pointer, in the coupling strengths**: within
`2 |h'(χ)| |g₂| |f(φ)| |g₁| t²`. -/
theorem abs_idxTwoShiftSnd_sub_le_of_norm_le (g₁ g₂ : ℝ) (hA : A₀.IsHermitian)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hPn : ‖P‖ ≤ 1) (hQn : ‖Q‖ ≤ 1)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ι) {t : ℝ} (ht : 0 ≤ t) :
    |idxTwoShiftSnd hA (isHermitian_ofReal_smul g₁ hP) (isHermitian_ofReal_smul g₂ hQ) hf hh φ χ
          p t - idxPointerShift hA (isHermitian_ofReal_smul g₂ hQ) hh χ p t|
      ≤ 2 * |hh.deriv_periodic.lift χ| * (|g₂| * (|hf.lift φ| * |g₁|) * t ^ 2) := by
  refine (abs_idxTwoShiftSnd_sub_le hA _ _ hf hh φ χ p ht).trans ?_
  gcongr
  · exact norm_ofReal_smul_le g₂ hQn
  · exact norm_ofReal_smul_le g₁ hPn

end Scaled

end Indexed

/-! ### Two site detectors on the Dirac ring -/

section DiracTwo

variable {M : ℕ} {f h : ℝ → ℝ}

/-- A real multiple of a site projector is Hermitian. -/
theorem siteProj_smul_isHermitian (g : ℝ) (j : ZMod (M + 1)) :
    ((g : ℂ) • siteProj j).IsHermitian :=
  isHermitian_ofReal_smul g (siteProj_isHermitian j)

/-- The carrier's propagator of #349 is the one-pointer propagator of the pair
`(H_D, g P_j)`. -/
theorem idxCarrierU_dirac (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    idxCarrierU (diracHam_isHermitian J μ) (siteProj_smul_isHermitian g j) hf φ t
      = diracCarrierU J μ g j hf φ t := by
  apply Subtype.ext
  rw [idxCarrierU_val, diracCarrierU_val, idxCoupledH, diracPointerH, smul_smul,
    ← Complex.ofReal_mul, mul_comm (hf.lift φ) g]

/-- The pointer's displacement of #349 is the one-pointer displacement of the pair
`(H_D, g P_j)`. -/
theorem idxPointerShift_dirac (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)
    (φ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    idxPointerShift (diracHam_isHermitian J μ) (siteProj_smul_isHermitian g j) hf φ p t
      = diracPointerShift J μ g j hf φ p t := by
  have key := idxPointerShift_ofReal_smul g (diracHam_isHermitian J μ) (siteProj_isHermitian j)
    hf φ p t
  simp only [idxCarrierU_dirac J μ g j hf φ] at key
  exact key

variable (J μ g₁ g₂ : ℝ) (j k : ZMod (M + 1)) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1)

/-- **The joint energy of the Dirac carrier and two pointers**, one coupled to the occupancy of
site `j` and one to the occupancy of site `k`, a function on `ℂℙ^{2M+1} × T² × T²`. -/
noncomputable def diracTwoPointerEnergy : EchoSigma (2 * M + 1) → ℝ :=
  twoCoupledEnergy (diracA M J μ) (diracB g₁ j) (diracB g₂ k) hf hh

/-- The joint energy read on the carrier:
`−2⟨H_D⟩ − 2 g₁ f(θ₂) ⟨P_j⟩ − 2 g₂ h(ψ₂) ⟨P_k⟩`. -/
theorem diracTwoPointerEnergy_eq (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) :
    diracTwoPointerEnergy J μ g₁ g₂ j k hf hh ((diracArenaEquiv M p, θ), ψ)
      = -2 * arenaObs (diracHam J μ) p - 2 * g₁ * hf.lift θ.2 * arenaObs (siteProj j) p
        - 2 * g₂ * hh.lift ψ.2 * arenaObs (siteProj k) p := by
  refine (twoCoupledEnergy_reindex (diracIdx M) (diracHam J μ) ((g₁ : ℂ) • siteProj j)
    ((g₂ : ℂ) • siteProj k) hf hh p θ ψ).trans ?_
  rw [arenaObs_real_smul, arenaObs_real_smul]
  ring

/-- **The carrier's Hamiltonian with two site pointers** at the angles `φ = θ₂`, `χ = ψ₂`:
`H_D + g₁ f(φ) P_j + g₂ h(χ) P_k`. -/
noncomputable def diracTwoH (φ χ : AddCircle (1 : ℝ)) :
    Matrix (ZMod (M + 1) × Fin 2) (ZMod (M + 1) × Fin 2) ℂ :=
  diracHam J μ + ((g₁ * hf.lift φ : ℝ) : ℂ) • siteProj j
    + ((g₂ * hh.lift χ : ℝ) : ℂ) • siteProj k

/-- **The carrier's propagator with two site pointers**
`exp (−i t (H_D + g₁ f(φ) P_j + g₂ h(χ) P_k))`. -/
noncomputable def diracTwoCarrierU (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    Matrix.unitaryGroup (ZMod (M + 1) × Fin 2) ℂ :=
  idxTwoCarrierU (diracHam_isHermitian J μ) (siteProj_smul_isHermitian g₁ j)
    (siteProj_smul_isHermitian g₂ k) hf hh φ χ t

theorem diracTwoCarrierU_val (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    (diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ t).val
      = exp (t • ((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ)) := by
  rw [diracTwoCarrierU, idxTwoCarrierU_val, idxTwoH_ofReal_smul, diracTwoH]

/-- ★★ **The carrier's equation with two detectors**:
`U̇(t) = −i (H_D + g₁ f(θ₂) P_j + g₂ h(ψ₂) P_k) U(t)`, the lattice Dirac equation with two static
site potentials. This is the coupled generator of the shared arena. -/
theorem hasDerivAt_diracTwoCarrierU (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s).val)
      (((-Complex.I) • diracTwoH J μ g₁ g₂ j k hf hh φ χ)
        * (diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ t).val) t := by
  have key := hasDerivAt_idxTwoCarrierU (diracHam_isHermitian J μ)
    (siteProj_smul_isHermitian g₁ j) (siteProj_smul_isHermitian g₂ k) hf hh φ χ t
  rw [idxTwoH_ofReal_smul] at key
  exact key

/-- **The first pointer's lifted displacement**: `−2 g₁ f'(φ) ∫₀ᵗ ⟨P_j⟩` along the common
orbit. -/
noncomputable def diracTwoShiftFst (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) : ℝ :=
  -(2 * g₁) * hf.deriv_periodic.lift φ
    * ∫ s in (0 : ℝ)..t,
        arenaObs (siteProj j) (arenaKick (diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s) p)

/-- **The second pointer's lifted displacement**: `−2 g₂ h'(χ) ∫₀ᵗ ⟨P_k⟩` along the same
orbit. -/
noncomputable def diracTwoShiftSnd (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) : ℝ :=
  -(2 * g₂) * hh.deriv_periodic.lift χ
    * ∫ s in (0 : ℝ)..t,
        arenaObs (siteProj k) (arenaKick (diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ s) p)

theorem idxTwoShiftFst_diracTwo (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    idxTwoShiftFst (diracHam_isHermitian J μ) (siteProj_smul_isHermitian g₁ j)
        (siteProj_smul_isHermitian g₂ k) hf hh φ χ p t
      = diracTwoShiftFst J μ g₁ g₂ j k hf hh φ χ p t :=
  idxTwoShiftFst_ofReal_smul g₁ (diracHam_isHermitian J μ) (siteProj_isHermitian j)
    (siteProj_smul_isHermitian g₂ k) hf hh φ χ p t

theorem idxTwoShiftSnd_diracTwo (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (t : ℝ) :
    idxTwoShiftSnd (diracHam_isHermitian J μ) (siteProj_smul_isHermitian g₁ j)
        (siteProj_smul_isHermitian g₂ k) hf hh φ χ p t
      = diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ p t :=
  idxTwoShiftSnd_ofReal_smul g₂ (diracHam_isHermitian J μ) (siteProj_smul_isHermitian g₁ j)
    (siteProj_isHermitian k) hf hh φ χ p t

/-- **The joint flow of the Dirac carrier and two pointers**: the flow of
`diracTwoPointerEnergy` for the form `echoForm`. -/
noncomputable def diracTwoPointerFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) :
    EchoSigma (2 * M + 1) → EchoSigma (2 * M + 1) :=
  twoCoupledFlow (diracA M J μ) (diracB g₁ j) (diracB g₂ k) hf hh hc hch t

theorem diracTwoPointerFlow_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (x : EchoSigma (2 * M + 1)) : diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch 0 x = x :=
  twoCoupledFlow_zero _ _ _ hf hh hc hch x

/-- The flow is a one-parameter group. -/
theorem diracTwoPointerFlow_add (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (s t : ℝ)
    (x : EchoSigma (2 * M + 1)) :
    diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch (s + t) x
      = diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch s
          (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t x) :=
  twoCoupledFlow_add _ _ _ hf hh hc hch s t x

/-- ★★★ **The Dirac carrier and two detectors, solved.** The flow of
`−2⟨H_D⟩ − 2 g₁ f(θ₂)⟨P_j⟩ − 2 g₂ h(ψ₂)⟨P_k⟩` moves the carrier by
`exp (−i t (H_D + g₁ f(θ₂) P_j + g₂ h(ψ₂) P_k))`, advances `θ₁` by `−2 g₁ f'(θ₂) ∫₀ᵗ ⟨P_j⟩` and
`ψ₁` by `−2 g₂ h'(ψ₂) ∫₀ᵗ ⟨P_k⟩` along that one orbit, and fixes `θ₂` and `ψ₂`. -/
theorem diracTwoPointerFlow_apply (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) :
    diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((diracArenaEquiv M p, θ), ψ)
      = ((diracArenaEquiv M (arenaKick (diracTwoCarrierU J μ g₁ g₂ j k hf hh θ.2 ψ.2 t) p),
          (θ.1 + ((diracTwoShiftFst J μ g₁ g₂ j k hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)),
            θ.2)),
         (ψ.1 + ((diracTwoShiftSnd J μ g₁ g₂ j k hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)),
          ψ.2)) := by
  rw [← idxTwoShiftFst_diracTwo, ← idxTwoShiftSnd_diracTwo]
  exact twoCoupledFlow_reindex (diracIdx M) (diracHam_isHermitian J μ)
    (siteProj_smul_isHermitian g₁ j) (siteProj_smul_isHermitian g₂ k) hf hh hc hch t p θ ψ

/-- Both hidden angles `θ₂` and `ψ₂` are conserved. -/
theorem diracTwoPointerFlow_angles (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (x : EchoSigma (2 * M + 1)) :
    (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t x).1.2.2 = x.1.2.2
      ∧ (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t x).2.2 = x.2.2 := by
  obtain ⟨⟨y, θ⟩, ψ⟩ := x
  obtain ⟨p, rfl⟩ := (diracArenaEquiv M).surjective y
  rw [diracTwoPointerFlow_apply]
  exact ⟨rfl, rfl⟩

/-- ★★ **The first detector alone, exactly.** On a fibre where the second profile vanishes, the
carrier and the first pointer move by the one-pointer flow `diracPointerFlow` of #349. -/
theorem diracTwoPointerFlow_fst_of_lift_eq_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (t : ℝ) (x : CPN (2 * M + 1 + 1)) (θ : KTorus) {ψ : KTorus} (hz : hh.lift ψ.2 = 0) :
    (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((x, θ), ψ)).1
      = diracPointerFlow J μ g₁ j hf hc t (x, θ) :=
  twoCoupledFlow_fst_of_lift_eq_zero (diracA_isHermitian M J μ) (diracB_isHermitian g₁ j)
    (diracB_isHermitian g₂ k) hf hh hc hch t x θ hz

/-- ★★ **The second detector alone, exactly.** On a fibre where the first profile vanishes, the
carrier and the second pointer move by the one-pointer flow `diracPointerFlow` at site `k`. -/
theorem diracTwoPointerFlow_snd_of_lift_eq_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (t : ℝ) (x : CPN (2 * M + 1 + 1)) {θ : KTorus} (ψ : KTorus) (hz : hf.lift θ.2 = 0) :
    ((diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((x, θ), ψ)).1.1,
        (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t ((x, θ), ψ)).2)
      = diracPointerFlow J μ g₂ k hh hch t (x, ψ) :=
  twoCoupledFlow_snd_of_lift_eq_zero (diracA_isHermitian M J μ) (diracB_isHermitian g₁ j)
    (diracB_isHermitian g₂ k) hf hh hc hch t x ψ hz

/-- ★★ **The joint flow preserves `μ_FS ⊗ vol_{T²} ⊗ vol_{T²}`.** -/
theorem echoMuL_map_diracTwoPointerFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (p₀ : CPN (2 * M + 1 + 1)) (t : ℝ) :
    Measure.map (diracTwoPointerFlow J μ g₁ g₂ j k hf hh hc hch t) (echoMuL p₀) = echoMuL p₀ :=
  echoMuL_map_twoCoupledFlow (diracA_isHermitian M J μ) (diracB_isHermitian g₁ j)
    (diracB_isHermitian g₂ k) hf hh hc hch p₀ t

/-- ★ The carrier with both detectors is within `|t| |h(ψ₂)| |g₂|` of the carrier of #349 with
the first detector alone. -/
theorem norm_diracTwoCarrierU_sub_le (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(diracTwoCarrierU J μ g₁ g₂ j k hf hh φ χ t).val - (diracCarrierU J μ g₁ j hf φ t).val‖
      ≤ |t| * (|hh.lift χ| * |g₂|) := by
  rw [← idxCarrierU_dirac]
  exact norm_idxTwoCarrierU_sub_fst_le_of_norm_le g₂ (diracHam_isHermitian J μ)
    (siteProj_smul_isHermitian g₁ j) (siteProj_isHermitian k) (norm_siteProj_le k) hf hh φ χ t

/-- ★★ **Cross-talk on the first detector.** Its displacement is within
`2 |f'(θ₂)| |g₁| |h(ψ₂)| |g₂| t²` of the displacement `diracPointerShift` of #349. -/
theorem abs_diracTwoShiftFst_sub_le (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracTwoShiftFst J μ g₁ g₂ j k hf hh φ χ p t - diracPointerShift J μ g₁ j hf φ p t|
      ≤ 2 * |hf.deriv_periodic.lift φ| * (|g₁| * (|hh.lift χ| * |g₂|) * t ^ 2) := by
  rw [← idxTwoShiftFst_diracTwo, ← idxPointerShift_dirac]
  exact abs_idxTwoShiftFst_sub_le_of_norm_le g₁ g₂ (diracHam_isHermitian J μ)
    (siteProj_isHermitian j) (siteProj_isHermitian k) (norm_siteProj_le j) (norm_siteProj_le k)
    hf hh φ χ p ht

/-- ★★ **Cross-talk on the second detector.** Its displacement is within
`2 |h'(ψ₂)| |g₂| |f(θ₂)| |g₁| t²` of the displacement `diracPointerShift` at site `k`. -/
theorem abs_diracTwoShiftSnd_sub_le (φ χ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracTwoShiftSnd J μ g₁ g₂ j k hf hh φ χ p t - diracPointerShift J μ g₂ k hh χ p t|
      ≤ 2 * |hh.deriv_periodic.lift χ| * (|g₂| * (|hf.lift φ| * |g₁|) * t ^ 2) := by
  rw [← idxTwoShiftSnd_diracTwo, ← idxPointerShift_dirac]
  exact abs_idxTwoShiftSnd_sub_le_of_norm_le g₁ g₂ (diracHam_isHermitian J μ)
    (siteProj_isHermitian j) (siteProj_isHermitian k) (norm_siteProj_le j) (norm_siteProj_le k)
    hf hh φ χ p ht

end DiracTwo

/-! ### The clock's pointer and a site detector on one device -/

section ClockSite

variable {M : ℕ}

/-- **The site projector of the two-level device**: the site projector `P_k` of the Dirac ring on
each of the two levels. -/
noncomputable def deviceSiteProj (k : ZMod (M + 1)) :
    Matrix ((ZMod (M + 1) × Fin 2) × Fin 2) ((ZMod (M + 1) × Fin 2) × Fin 2) ℂ :=
  Matrix.blockDiagonal fun _ : Fin 2 => siteProj k

/-- The device's site projector is diagonal: `1` on the entries at site `k`, `0` elsewhere. -/
theorem deviceSiteProj_eq_diagonal (k : ZMod (M + 1)) :
    deviceSiteProj k
      = Matrix.diagonal fun x : (ZMod (M + 1) × Fin 2) × Fin 2 =>
          if x.1.1 = k then (1 : ℂ) else 0 := by
  unfold deviceSiteProj siteProj
  exact Matrix.blockDiagonal_diagonal _

theorem deviceSiteProj_isHermitian (k : ZMod (M + 1)) : (deviceSiteProj k).IsHermitian := by
  rw [Matrix.IsHermitian, deviceSiteProj, Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext i
  exact siteProj_isHermitian k

/-- The device's site projector is a projector. -/
theorem deviceSiteProj_mul_self (k : ZMod (M + 1)) :
    deviceSiteProj k * deviceSiteProj k = deviceSiteProj k := by
  rw [deviceSiteProj_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

theorem norm_deviceSiteProj_le (k : ZMod (M + 1)) : ‖deviceSiteProj k‖ ≤ 1 := by
  rw [deviceSiteProj_eq_diagonal]
  exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun x => by split_ifs <;> simp

/-- A real multiple of the device's site projector is Hermitian. -/
theorem deviceSiteProj_smul_isHermitian (g : ℝ) (k : ZMod (M + 1)) :
    ((g : ℂ) • deviceSiteProj k).IsHermitian :=
  isHermitian_ofReal_smul g (deviceSiteProj_isHermitian k)

variable {f h : ℝ → ℝ} (J μ₀ μ₁ g₁ g₂ : ℝ) (k : ZMod (M + 1)) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1)

/-- **The joint energy of the two-level device, the clock's pointer and a site pointer**, a
function on `ℂℙ^{4M+3} × T² × T²`. The first torus is coupled to the level swap `X` (#357), the
second to the occupancy of site `k`. -/
noncomputable def clockSiteEnergy : EchoSigma (4 * M + 3) → ℝ :=
  twoCoupledEnergy (Matrix.reindex (clockIdx M) (clockIdx M) (deviceHam J μ₀ μ₁))
    (Matrix.reindex (clockIdx M) (clockIdx M) (clockB M g₁))
    (Matrix.reindex (clockIdx M) (clockIdx M) ((g₂ : ℂ) • deviceSiteProj k)) hf hh

/-- The joint energy read on the device:
`−2⟨H_dev⟩ − 2 g₁ f(θ₂) ⟨X⟩ − 2 g₂ h(ψ₂) ⟨Q_k⟩`. -/
theorem clockSiteEnergy_eq (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) :
    clockSiteEnergy J μ₀ μ₁ g₁ g₂ k hf hh ((clockArenaEquiv M p, θ), ψ)
      = -2 * arenaObs (deviceHam J μ₀ μ₁) p
        - 2 * g₁ * hf.lift θ.2 * arenaObs (levelSwap (ZMod (M + 1) × Fin 2)) p
        - 2 * g₂ * hh.lift ψ.2 * arenaObs (deviceSiteProj k) p := by
  refine (twoCoupledEnergy_reindex (clockIdx M) (deviceHam J μ₀ μ₁) (clockB M g₁)
    ((g₂ : ℂ) • deviceSiteProj k) hf hh p θ ψ).trans ?_
  rw [clockB, arenaObs_real_smul, arenaObs_real_smul]
  ring

/-- **The device's Hamiltonian with the clock's pointer and the site pointer** at the angles
`φ = θ₂`, `χ = ψ₂`: `H_dev + g₁ f(φ) X + g₂ h(χ) Q_k`. -/
noncomputable def clockSiteH (φ χ : AddCircle (1 : ℝ)) :
    Matrix ((ZMod (M + 1) × Fin 2) × Fin 2) ((ZMod (M + 1) × Fin 2) × Fin 2) ℂ :=
  deviceHam J μ₀ μ₁ + ((g₁ * hf.lift φ : ℝ) : ℂ) • levelSwap (ZMod (M + 1) × Fin 2)
    + ((g₂ * hh.lift χ : ℝ) : ℂ) • deviceSiteProj k

/-- **The device's propagator with both pointers**
`exp (−i t (H_dev + g₁ f(φ) X + g₂ h(χ) Q_k))`. -/
noncomputable def clockSiteCarrierU (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    Matrix.unitaryGroup ((ZMod (M + 1) × Fin 2) × Fin 2) ℂ :=
  idxTwoCarrierU (deviceHam_isHermitian J μ₀ μ₁) (clockB_isHermitian g₁)
    (deviceSiteProj_smul_isHermitian g₂ k) hf hh φ χ t

theorem clockSiteCarrierU_val (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ t).val
      = exp (t • ((-Complex.I) • clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ)) := by
  rw [clockSiteCarrierU, idxTwoCarrierU_val, clockB, idxTwoH_ofReal_smul, clockSiteH]

/-- ★★ **The device's equation with the clock's pointer and a site detector**:
`U̇(t) = −i (H_dev + g₁ f(θ₂) X + g₂ h(ψ₂) Q_k) U(t)`. -/
theorem hasDerivAt_clockSiteCarrierU (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s).val)
      (((-Complex.I) • clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ)
        * (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ t).val) t := by
  have key := hasDerivAt_idxTwoCarrierU (deviceHam_isHermitian J μ₀ μ₁)
    (clockB_isHermitian (M := M) g₁) (deviceSiteProj_smul_isHermitian g₂ k) hf hh φ χ t
  have e : idxTwoH (deviceHam J μ₀ μ₁) (clockB M g₁) ((g₂ : ℂ) • deviceSiteProj k) hf hh φ χ
      = clockSiteH J μ₀ μ₁ g₁ g₂ k hf hh φ χ :=
    idxTwoH_ofReal_smul (deviceHam J μ₀ μ₁) (levelSwap (ZMod (M + 1) × Fin 2))
      (deviceSiteProj k) g₁ g₂ hf hh φ χ
  rw [e] at key
  exact key

/-- **The clock pointer's lifted displacement**: `−2 g₁ f'(φ) ∫₀ᵗ ⟨X⟩` along the common orbit. -/
noncomputable def clockSiteShiftFst (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (t : ℝ) : ℝ :=
  -(2 * g₁) * hf.deriv_periodic.lift φ
    * ∫ s in (0 : ℝ)..t, arenaObs (levelSwap (ZMod (M + 1) × Fin 2))
        (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s) p)

/-- **The site pointer's lifted displacement**: `−2 g₂ h'(χ) ∫₀ᵗ ⟨Q_k⟩` along the same orbit. -/
noncomputable def clockSiteShiftSnd (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (t : ℝ) : ℝ :=
  -(2 * g₂) * hh.deriv_periodic.lift χ
    * ∫ s in (0 : ℝ)..t, arenaObs (deviceSiteProj k)
        (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ s) p)

theorem idxTwoShiftFst_clockSite (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (t : ℝ) :
    idxTwoShiftFst (deviceHam_isHermitian J μ₀ μ₁) (clockB_isHermitian g₁)
        (deviceSiteProj_smul_isHermitian g₂ k) hf hh φ χ p t
      = clockSiteShiftFst J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t :=
  idxTwoShiftFst_ofReal_smul g₁ (deviceHam_isHermitian J μ₀ μ₁) (levelSwap_isHermitian _)
    (deviceSiteProj_smul_isHermitian g₂ k) hf hh φ χ p t

theorem idxTwoShiftSnd_clockSite (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (t : ℝ) :
    idxTwoShiftSnd (deviceHam_isHermitian J μ₀ μ₁) (clockB_isHermitian g₁)
        (deviceSiteProj_smul_isHermitian g₂ k) hf hh φ χ p t
      = clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t :=
  idxTwoShiftSnd_ofReal_smul g₂ (deviceHam_isHermitian J μ₀ μ₁) (clockB_isHermitian g₁)
    (deviceSiteProj_isHermitian k) hf hh φ χ p t

/-- **The joint flow of the device, the clock's pointer and a site pointer**: the flow of
`clockSiteEnergy` for the form `echoForm`. -/
noncomputable def clockSiteFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) :
    EchoSigma (4 * M + 3) → EchoSigma (4 * M + 3) :=
  twoCoupledFlow (Matrix.reindex (clockIdx M) (clockIdx M) (deviceHam J μ₀ μ₁))
    (Matrix.reindex (clockIdx M) (clockIdx M) (clockB M g₁))
    (Matrix.reindex (clockIdx M) (clockIdx M) ((g₂ : ℂ) • deviceSiteProj k)) hf hh hc hch t

theorem clockSiteFlow_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (x : EchoSigma (4 * M + 3)) : clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch 0 x = x :=
  twoCoupledFlow_zero _ _ _ hf hh hc hch x

/-- The flow is a one-parameter group. -/
theorem clockSiteFlow_add (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (s t : ℝ)
    (x : EchoSigma (4 * M + 3)) :
    clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch (s + t) x
      = clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch s
          (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x) :=
  twoCoupledFlow_add _ _ _ hf hh hc hch s t x

/-- ★★★ **The device, the clock's pointer and a site detector, solved.** The flow of
`−2⟨H_dev⟩ − 2 g₁ f(θ₂)⟨X⟩ − 2 g₂ h(ψ₂)⟨Q_k⟩` moves the device by
`exp (−i t (H_dev + g₁ f(θ₂) X + g₂ h(ψ₂) Q_k))`, advances the clock's pointer `θ₁` by
`−2 g₁ f'(θ₂) ∫₀ᵗ ⟨X⟩` and the site pointer `ψ₁` by `−2 g₂ h'(ψ₂) ∫₀ᵗ ⟨Q_k⟩` along that one orbit,
and fixes `θ₂` and `ψ₂`. -/
theorem clockSiteFlow_apply (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) :
    clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((clockArenaEquiv M p, θ), ψ)
      = ((clockArenaEquiv M (arenaKick (clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 t) p),
          (θ.1 + ((clockSiteShiftFst J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)),
            θ.2)),
         (ψ.1 + ((clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)),
          ψ.2)) := by
  rw [← idxTwoShiftFst_clockSite, ← idxTwoShiftSnd_clockSite]
  exact twoCoupledFlow_reindex (clockIdx M) (deviceHam_isHermitian J μ₀ μ₁)
    (clockB_isHermitian g₁) (deviceSiteProj_smul_isHermitian g₂ k) hf hh hc hch t p θ ψ

/-- Both hidden angles `θ₂` and `ψ₂` are conserved. -/
theorem clockSiteFlow_angles (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (x : EchoSigma (4 * M + 3)) :
    (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x).1.2.2 = x.1.2.2
      ∧ (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t x).2.2 = x.2.2 := by
  obtain ⟨⟨y, θ⟩, ψ⟩ := x
  obtain ⟨p, rfl⟩ := (clockArenaEquiv M).surjective y
  rw [clockSiteFlow_apply]
  exact ⟨rfl, rfl⟩

/-- ★★ **The clock alone, exactly.** On a fibre where the site pointer's profile vanishes, the
device and the clock's pointer move by the flow `clockPointerFlow` of #357. -/
theorem clockSiteFlow_fst_of_lift_eq_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (t : ℝ) (x : CPN (4 * M + 3 + 1)) (θ : KTorus) {ψ : KTorus} (hz : hh.lift ψ.2 = 0) :
    (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((x, θ), ψ)).1
      = clockPointerFlow M J μ₀ μ₁ g₁ hf hc t (x, θ) :=
  twoCoupledFlow_fst_of_lift_eq_zero ((deviceHam_isHermitian J μ₀ μ₁).reindex (clockIdx M))
    ((clockB_isHermitian g₁).reindex (clockIdx M))
    ((deviceSiteProj_smul_isHermitian g₂ k).reindex (clockIdx M)) hf hh hc hch t x θ hz

/-- ★ **The site detector alone, exactly.** On a fibre where the clock pointer's profile
vanishes, the device and the site pointer move by the one-pointer flow of the pair
`(H_dev, g₂ Q_k)`. -/
theorem clockSiteFlow_snd_of_lift_eq_zero (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (t : ℝ) (x : CPN (4 * M + 3 + 1)) {θ : KTorus} (ψ : KTorus) (hz : hf.lift θ.2 = 0) :
    ((clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((x, θ), ψ)).1.1,
        (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t ((x, θ), ψ)).2)
      = (arenaForm_isSymplectic (4 * M + 3)).hamiltonianFlow
          (contMDiff_coupledEnergy (Matrix.reindex (clockIdx M) (clockIdx M) (deviceHam J μ₀ μ₁))
            (Matrix.reindex (clockIdx M) (clockIdx M) ((g₂ : ℂ) • deviceSiteProj k)) hh hch)
          t (x, ψ) :=
  twoCoupledFlow_snd_of_lift_eq_zero ((deviceHam_isHermitian J μ₀ μ₁).reindex (clockIdx M))
    ((clockB_isHermitian g₁).reindex (clockIdx M))
    ((deviceSiteProj_smul_isHermitian g₂ k).reindex (clockIdx M)) hf hh hc hch t x ψ hz

/-- ★★ **The joint flow preserves `μ_FS ⊗ vol_{T²} ⊗ vol_{T²}`.** -/
theorem echoMuL_map_clockSiteFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (p₀ : CPN (4 * M + 3 + 1)) (t : ℝ) :
    Measure.map (clockSiteFlow J μ₀ μ₁ g₁ g₂ k hf hh hc hch t) (echoMuL p₀) = echoMuL p₀ :=
  echoMuL_map_twoCoupledFlow ((deviceHam_isHermitian J μ₀ μ₁).reindex (clockIdx M))
    ((clockB_isHermitian g₁).reindex (clockIdx M))
    ((deviceSiteProj_smul_isHermitian g₂ k).reindex (clockIdx M)) hf hh hc hch p₀ t

/-- ★★ **The site detector's effect on the device.** The device with both pointers is within
`|t| |h(ψ₂)| |g₂|` of the device of #357 with the clock's pointer alone. -/
theorem norm_clockSiteCarrierU_sub_le (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    ‖(clockSiteCarrierU J μ₀ μ₁ g₁ g₂ k hf hh φ χ t).val
        - (clockCarrierU M J μ₀ μ₁ g₁ hf φ t).val‖ ≤ |t| * (|hh.lift χ| * |g₂|) :=
  norm_idxTwoCarrierU_sub_fst_le_of_norm_le g₂ (deviceHam_isHermitian J μ₀ μ₁)
    (clockB_isHermitian g₁) (deviceSiteProj_isHermitian k) (norm_deviceSiteProj_le k) hf hh φ χ t

/-- ★★ **Cross-talk on the clock's pointer.** With the site detector coupled, the clock pointer's
displacement is within `2 |f'(θ₂)| |g₁| |h(ψ₂)| |g₂| t²` of the displacement `clockPointerShift`
of #357. -/
theorem abs_clockSiteShiftFst_sub_le (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |clockSiteShiftFst J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t - clockPointerShift J μ₀ μ₁ g₁ hf φ p t|
      ≤ 2 * |hf.deriv_periodic.lift φ| * (|g₁| * (|hh.lift χ| * |g₂|) * t ^ 2) := by
  rw [← idxTwoShiftFst_clockSite, ← idxPointerShift_clock]
  exact abs_idxTwoShiftFst_sub_le_of_norm_le g₁ g₂ (deviceHam_isHermitian J μ₀ μ₁)
    (levelSwap_isHermitian _) (deviceSiteProj_isHermitian k) norm_levelSwap_le
    (norm_deviceSiteProj_le k) hf hh φ χ p ht

/-- ★★ **Cross-talk on the site pointer.** With the clock's pointer coupled, the site pointer's
displacement is within `2 |h'(ψ₂)| |g₂| |f(θ₂)| |g₁| t²` of its displacement on the device
alone. -/
theorem abs_clockSiteShiftSnd_sub_le (φ χ : AddCircle (1 : ℝ))
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |clockSiteShiftSnd J μ₀ μ₁ g₁ g₂ k hf hh φ χ p t
        - idxPointerShift (deviceHam_isHermitian J μ₀ μ₁) (deviceSiteProj_smul_isHermitian g₂ k)
            hh χ p t|
      ≤ 2 * |hh.deriv_periodic.lift χ| * (|g₂| * (|hf.lift φ| * |g₁|) * t ^ 2) := by
  rw [← idxTwoShiftSnd_clockSite]
  exact abs_idxTwoShiftSnd_sub_le_of_norm_le g₁ g₂ (deviceHam_isHermitian J μ₀ μ₁)
    (levelSwap_isHermitian _) (deviceSiteProj_isHermitian k) norm_levelSwap_le
    (norm_deviceSiteProj_le k) hf hh φ χ p ht

end ClockSite

end CSD.RecordLayer

end

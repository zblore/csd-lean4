/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Thermo.ReducedSecondMoment
public import CsdLean4.Mathlib.MeasureTheory.MapProbability

/-!
# E2: the microcanonical energy window

**Category:** conceptually 1-Mathlib (CSD-free quantum statistical mechanics), kept under
`CSD.Thermo`.

The equilibration arc's second item (`specs/equilibration-arc-plan.md` E2), **re-scoped by E3's
verdict**. E2 was originally "E1 on the unit sphere of a spectral sector `H_R`". That
formulation is refuted: `Thermo/SectorRestriction.lean` proves an exact spectral sector is
Fubini–Study-**null**, so restricting to one gives the zero measure and there is nothing to
condition on. The surviving route — route 1 of E3's two — is a **positive-measure energy
window**, and this module builds it.

## The setting: a diagonal Hamiltonian

For `H = diag(λ)` in the moment-map basis, the energy expectation of a ray is the *linear*
statistic `⟨H⟩_p = Σ_k λ_k x_k` (`rayEnergy`). That is exactly the shape Q24's linear moments and
Chebyshev bound speak about, so the window's measure is controlled by landed results with no
new integral.

## What is proved

* `rayEnergy`, `energyMean`, `energyVar` — the energy expectation and its first two Fubini–Study
  moments (`fs_energy_mean` is `fs_linear_expectation`; the variance is Q24's).
* `energyWindow` — the microcanonical window `{p : |⟨H⟩_p − ⟨H⟩| < ε}` around the mean, and its
  measurability.
* ★★ `energyWindow_ne_zero` — **the window has positive measure** once it is wider than the
  fluctuation scale (`ε² > Var`), by Chebyshev. This is the hypothesis E3's verdict makes
  load-bearing, and it is *quantitative*: the width condition is explicit in `d`, `λ`, `N`,
  not assumed.
* `microMeasure` — the microcanonical law: `μ_FS` conditioned on the window, a probability
  measure exactly when the window is non-null.

## ⚠️ Honest scope — what conditioning does and does not preserve

Conditioning on an energy window **breaks the `U(N)` invariance** that Q24's twirl argument
uses, so the moment *values* do not transfer. The situation is not uniform, and the split is
sharp:

* the **sign flips survive** — `momentMap_signFlip` says a sign flip fixes every moment
  coordinate, hence fixes `rayEnergy` and preserves the window setwise;
* the **permutations and the Hadamard rotation do not** — `momentMap_permU` permutes the
  coordinates and the Hadamard mixes them, either of which changes `rayEnergy` unless `λ` is
  constant.

So the *vanishing* results (which use only sign flips) survive conditioning, while the moment
*values* `E[x_i²] = 2/(N(N+1))` etc. do not. Computing conditional moments is a genuinely
different problem (a microcanonical density-of-states computation) and is **not** attempted
here.

## References

`specs/equilibration-arc-plan.md` (E2, and E3's verdict that forced this re-scope);
`Thermo/SectorRestriction.lean` (the refutation of the exact-sector formulation);
`Thermo/CanonicalTypicality.lean` (Q24's linear moments and `fs_chebyshev_concentration`).
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization BigOperators ENNReal

namespace CSD.Thermo

open CSD.LF4

variable {N : ℕ} [NeZero N]

/-! ### The energy expectation of a ray -/

/-- **The energy expectation** of a ray, for a Hamiltonian `diag lam` in the moment-map basis:
the linear statistic `⟨H⟩_p = Σ_k λ_k x_k`. -/
noncomputable def rayEnergy (lam : Fin N → ℝ) (p : CPN N) : ℝ :=
  ∑ k : Fin N, lam k * momentMap p k

omit [NeZero N] in
lemma rayEnergy_measurable (lam : Fin N → ℝ) : Measurable (rayEnergy lam) :=
  Finset.measurable_sum _ (fun k _ => (momentMap_measurable k).const_mul (lam k))

/-- The mean energy over Fubini–Study: the equal-weight average of the spectrum. -/
noncomputable def energyMean (lam : Fin N → ℝ) : ℝ := (∑ k : Fin N, lam k) / N

/-- The Fubini–Study variance of the energy (Q24's closed form). -/
noncomputable def energyVar (lam : Fin N → ℝ) : ℝ :=
  ((N : ℝ) * ∑ k : Fin N, lam k ^ 2 - (∑ k : Fin N, lam k) ^ 2)
    / ((N : ℝ) ^ 2 * ((N : ℝ) + 1))

/-- The mean energy is `fs_linear_expectation`, restated. -/
theorem fs_energy_mean (p₀ : CPN N) (lam : Fin N → ℝ) :
    ∫ p, rayEnergy lam p ∂(fubiniStudyMeasure p₀) = energyMean lam :=
  fs_linear_expectation p₀ lam

/-! ### The window -/

/-- **The microcanonical energy window** of half-width `ε` about the mean energy. -/
def energyWindow (lam : Fin N → ℝ) (ε : ℝ) : Set (CPN N) :=
  {p | |rayEnergy lam p - energyMean lam| < ε}

omit [NeZero N] in
lemma measurableSet_energyWindow (lam : Fin N → ℝ) (ε : ℝ) :
    MeasurableSet (energyWindow lam ε) := by
  have hset : energyWindow lam ε
      = {p : CPN N | energyMean lam - ε < rayEnergy lam p}
        ∩ {p : CPN N | rayEnergy lam p < energyMean lam + ε} := by
    ext p
    simp only [energyWindow, Set.mem_ofPred_eq, Set.mem_inter_iff, abs_lt]
    constructor
    · intro h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · intro h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hset]
  exact (measurableSet_lt measurable_const (rayEnergy_measurable lam)).inter
    (measurableSet_lt (rayEnergy_measurable lam) measurable_const)

omit [NeZero N] in
/-- The window's complement is the Chebyshev tail event. -/
lemma compl_energyWindow (lam : Fin N → ℝ) (ε : ℝ) :
    (energyWindow lam ε)ᶜ = {p : CPN N | ε ≤ |rayEnergy lam p - energyMean lam|} := by
  ext p
  simp [energyWindow, not_lt]

/-- ★★ **The energy window has positive measure once it exceeds the fluctuation scale.**

This is the hypothesis E3's verdict makes load-bearing — an exact spectral sector is
Fubini–Study-null, so a microcanonical statement needs a window that provably carries weight.
The condition is quantitative: the Chebyshev tail `Var/ε²` must be `< 1`, i.e. the window must
be wider than the standard deviation. -/
theorem energyWindow_ne_zero (p₀ : CPN N) (lam : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hwidth : ENNReal.ofReal (energyVar lam / ε ^ 2) < 1) :
    fubiniStudyMeasure p₀ (energyWindow lam ε) ≠ 0 := by
  intro h0
  have htail : fubiniStudyMeasure p₀ {p : CPN N | ε ≤ |rayEnergy lam p - energyMean lam|}
      ≤ ENNReal.ofReal (energyVar lam / ε ^ 2) := by
    have h := fs_chebyshev_concentration p₀ lam hε
    exact h
  have hone : fubiniStudyMeasure p₀ {p : CPN N | ε ≤ |rayEnergy lam p - energyMean lam|} = 1 := by
    rw [← compl_energyWindow lam ε,
      prob_compl_eq_one_sub (measurableSet_energyWindow lam ε), h0, tsub_zero]
  rw [hone] at htail
  exact absurd (lt_of_le_of_lt htail hwidth) (lt_irrefl 1)

/-- **The microcanonical law**: Fubini–Study conditioned on the energy window. -/
noncomputable def microMeasure (p₀ : CPN N) (lam : Fin N → ℝ) (ε : ℝ) :
    Measure (CPN N) :=
  ProbabilityTheory.cond (fubiniStudyMeasure p₀) (energyWindow lam ε)

omit [NeZero N] in
/-- The microcanonical law is a probability measure exactly when the window carries weight —
which `energyWindow_ne_zero` supplies. -/
lemma microMeasure_isProbability (p₀ : CPN N) (lam : Fin N → ℝ) {ε : ℝ}
    (hne : fubiniStudyMeasure p₀ (energyWindow lam ε) ≠ 0) :
    IsProbabilityMeasure (microMeasure p₀ lam ε) :=
  ProbabilityTheory.cond_isProbabilityMeasure hne

/-! ### ★★ What survives conditioning: the sign flips

The point of this section is a **sharp split**. Conditioning on an energy window destroys the
`U(N)` invariance Q24's twirl argument runs on — but not uniformly. A sign flip fixes every
moment coordinate (`momentMap_signFlip`), hence fixes the energy, hence maps the window to
itself; so the whole sign-flip half of the twirl toolkit survives conditioning intact. The
permutations and the Hadamard rotation move moment coordinates and therefore change the energy,
so they do not. -/

/-- The energy is invariant under a sign flip: the flip fixes every moment coordinate. -/
lemma rayEnergy_signFlip (lam : Fin N → ℝ) (k : Fin N) (p : CPN N) :
    rayEnergy lam ((signFlip k) • p) = rayEnergy lam p :=
  Finset.sum_congr rfl (fun j _ => by rw [momentMap_signFlip])

/-- Hence the sign flip preserves the energy window. -/
lemma energyWindow_signFlip_preimage (lam : Fin N → ℝ) (ε : ℝ) (k : Fin N) :
    (fun p : CPN N => (signFlip k) • p) ⁻¹' (energyWindow lam ε) = energyWindow lam ε := by
  ext p
  show |rayEnergy lam ((signFlip k) • p) - energyMean lam| < ε ↔ _
  rw [rayEnergy_signFlip]
  rfl

/-- ★ **The microcanonical law is sign-flip invariant.** The window is preserved and `μ_FS` is
unitarily invariant, so conditioning commutes with the flip. -/
lemma map_signFlip_microMeasure (p₀ : CPN N) (lam : Fin N → ℝ) (ε : ℝ) (k : Fin N) :
    Measure.map (fun p : CPN N => (signFlip k) • p) (microMeasure p₀ lam ε)
      = microMeasure p₀ lam ε := by
  have hT : Measurable (fun p : CPN N => (signFlip k) • p) :=
    (continuous_const_smul _).measurable
  have hinv : Measure.map (fun p : CPN N => (signFlip k) • p) (fubiniStudyMeasure p₀)
      = fubiniStudyMeasure p₀ := fubiniStudyMeasure_smul_invariant _ p₀
  have key : Measure.map (fun p : CPN N => (signFlip k) • p)
        ((fubiniStudyMeasure p₀).restrict (energyWindow lam ε))
      = (fubiniStudyMeasure p₀).restrict (energyWindow lam ε) := by
    calc Measure.map (fun p : CPN N => (signFlip k) • p)
          ((fubiniStudyMeasure p₀).restrict (energyWindow lam ε))
        = Measure.map (fun p : CPN N => (signFlip k) • p)
            ((fubiniStudyMeasure p₀).restrict
              ((fun p : CPN N => (signFlip k) • p) ⁻¹' (energyWindow lam ε))) := by
          rw [energyWindow_signFlip_preimage]
      _ = (Measure.map (fun p : CPN N => (signFlip k) • p)
            (fubiniStudyMeasure p₀)).restrict (energyWindow lam ε) :=
          (Measure.restrict_map hT (measurableSet_energyWindow lam ε)).symm
      _ = (fubiniStudyMeasure p₀).restrict (energyWindow lam ε) := by rw [hinv]
  show Measure.map (fun p : CPN N => (signFlip k) • p)
      ((fubiniStudyMeasure p₀ (energyWindow lam ε))⁻¹
        • (fubiniStudyMeasure p₀).restrict (energyWindow lam ε))
    = (fubiniStudyMeasure p₀ (energyWindow lam ε))⁻¹
        • (fubiniStudyMeasure p₀).restrict (energyWindow lam ε)
  rw [Measure.map_smul' _ _ (continuous_const_smul (signFlip k)).measurable, key]

/-- The change-of-variables engine, conditioned: integrals against the microcanonical law are
unchanged by a sign flip. The conditioned analogue of `fs_integral_unitary`, available for the
sign flips only. -/
lemma micro_integral_signFlip (p₀ : CPN N) (lam : Fin N → ℝ) (ε : ℝ) (k : Fin N)
    {f : CPN N → ℝ} (hf : Measurable f) :
    ∫ p, f p ∂(microMeasure p₀ lam ε)
      = ∫ p, f ((signFlip k) • p) ∂(microMeasure p₀ lam ε) := by
  have hT : Measurable (fun p : CPN N => (signFlip k) • p) :=
    (continuous_const_smul _).measurable
  conv_lhs => rw [← map_signFlip_microMeasure p₀ lam ε k]
  exact integral_map hT.aemeasurable hf.aestronglyMeasurable

/-! ### ★★ The four-index vanishing survives conditioning -/

variable {dA dB : ℕ}

/-- ★★ **The four-index expectations vanish microcanonically too.** The proof of
`fs_redOff_cross_vanish` used only a sign flip, and sign flips preserve the energy window, so
the argument transfers verbatim to the conditioned law. This is the part of E1's machinery that
survives E2's conditioning — in contrast to the moment *values*, which do not (see the module
header). -/
theorem micro_redOff_cross_vanish (p₀ : CPN N) (lam : Fin N → ℝ) (ε : ℝ)
    (e : Fin N ≃ Fin dA × Fin dB)
    {a a' : Fin dA} (haa : a ≠ a') {b b' : Fin dB} (hbb : b ≠ b') :
    ∫ p, ((rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
          + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im)
      ∂(microMeasure p₀ lam ε) = 0 := by
  have hjk : e.symm (a', b) ≠ e.symm (a, b) :=
    fun h => haa (congrArg Prod.fst (e.symm.injective h)).symm
  have hi'k : e.symm (a, b') ≠ e.symm (a, b) :=
    fun h => hbb (congrArg Prod.snd (e.symm.injective h)).symm
  have hj'k : e.symm (a', b') ≠ e.symm (a, b) :=
    fun h => haa (congrArg Prod.fst (e.symm.injective h)).symm
  have hmeas : Measurable (fun p : CPN N =>
      (rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
          * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
        + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
          * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im) := by
    refine Measurable.add ?_ ?_
    · exact ((Complex.measurable_re.comp (rayDensity_measurable _ _)).mul
        (Complex.measurable_re.comp (rayDensity_measurable _ _)))
    · exact ((Complex.measurable_im.comp (rayDensity_measurable _ _)).mul
        (Complex.measurable_im.comp (rayDensity_measurable _ _)))
  have h := micro_integral_signFlip p₀ lam ε (e.symm (a, b)) hmeas
  rw [integral_congr_ae (ae_of_all _ (fun p : CPN N => by
      rw [signFlip_smul_offdiag _ _ hjk,
        signFlip_smul_rayDensity_ne _ _ _ hi'k hj'k,
        Complex.neg_re, Complex.neg_im]
      ring :
    ∀ p : CPN N,
      (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b)) (e.symm (a', b))).re
          * (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b')) (e.symm (a', b'))).re
        + (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b)) (e.symm (a', b))).im
          * (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b')) (e.symm (a', b'))).im
      = -((rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
          + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im))),
    integral_neg] at h
  linarith

end CSD.Thermo

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracArrival
public import CsdLean4.RecordLayer.ArcAffine
public import CsdLean4.RecordLayer.CircleRecord
public import CsdLean4.CV.DiracPacketLimit
public import Mathlib.Probability.Distributions.Exponential

/-!
# One click: the site record selected by the ontic point

**Category:** 7-SigmaLayer (the record layer). BACKLOG #266.

## The problem

#252's detectors (`DiracDetector.lean`) integrate the packet's site weight on every site, so every
register rises. The threshold fixes *when* a register is written, not that only *one* is. A detector
array on a single trajectory must write exactly one site, and the corpus's selections pick an
outcome of a *fixed* measurement, while here the weights move with the packet.

⚠️ **The row's acceptance, as worded, is ill-posed, and is corrected here.** It asked for the
measure of the ontic states writing site `k` by `t` to equal "the weight delivered to `k` by `t`
over the norm", `∫₀ᵗ w_k / N`. Summed over the sites that is `t`, because the norm is conserved
(`Σ_k w_k(s) = N` at every `s`), so it is not a probability once `t > 1`. #252's registers do not
absorb the weight they read. The law below is the normalised one. Its first-order term at small
`κ t` is `κ ∫₀ᵗ w_k / N`, the row's expression with the click rate `κ`.

## The construction

The ontic fibre is `ℝ × T¹`, carrying `clickLaw κ = expMeasure κ ⊗ Haar`. An ontic point `(τ, η)`
clicks at time `τ`, at the site whose arc at that moment contains `η`:
`clickSite r (τ, η) = circleOutcome (r τ) η`, with `r τ k = w_k(τ)/N`. **The detail sets the
outcome**: the point fixes both when and where. The selection is non-anticipating. The site depends
only on the weights at the click time, never on later ones.

## What is proved

* `clickCell r k t` (the ontic points that write site `k` by time `t`),
  `measurableSet_clickCell`, `mem_clickCell_iff` (**`x` writes site `k` by `t` exactly when it
  clicks by `t` and its site is `k`**);
* ★★★ `existsUnique_clickSite` (**every ontic point clicks at exactly one site**), ★★
  `clickCell_disjoint` (**no ontic point writes two sites, at any pair of times**);
* ★★★ `clickLaw_clickCell` (**the probability of site `k` by `t` is `∫_{s ≤ t} w_k(s)/N` against
  the click-time law**: given a click at `s`, the site frequency over preparations is the packet's
  site weights at `s`);
* ★★★ `clickLaw_clicked_by` (**the probability of a click by `t ≥ 0` is `1 − e^{−κt}`**, whatever
  the packet);
* `clickTime` (`τ(ξ) = −log(rep ξ)/κ`), ★★ `map_clickTime` (**the uniform circle carries the
  exponential click-time law**), `torusClick`, ★★★ `measurePreserving_torusClick` (**the torus `T²`
  with its Haar measure carries the click law**), ★★★ `volume_torusClick_clickCell` (the law on
  `T²`);
* `siteRate`, `siteRate_nonneg`, `sum_siteRate`, `measurable_siteRate` (the site weights of a
  norm-conserving chain trajectory); ★★★ `chain_one_click` (**for any continuous trajectory of
  the chain with conserved norm, one click, its law and its total**);
  ★★★ `dirac_packet_one_click` (**the Dirac packet of `dirac_detector`, and every packet of the
  chain**, through `chainInner_packet_self`).

## What is the record, and where QM enters

The record is a **definite fact of the one trajectory**: the ontic point `(τ, η)` writes one site at
one time, with no probability in it. QM's statistics enter only as the packet's site weights
`‖ψ_k‖²/N`, which size the arcs; they are **input, not derived**, and the measures above say that
the frequency of records over preparations reproduces them. Nothing here constructs the Born rule.

## Honest scope

* **The click clock is a stated detector law**: exponential at rate `κ`, a parameter, as #252's
  gain `g` is. Nothing generates it from a coupling Hamiltonian (#251), and the packet is not
  depleted by the click (no back-reaction).
* **The fibre is the corpus's compact `T²` with Haar measure** (`measurePreserving_torusClick`):
  the first circle coordinate is read as the click time through `clickTime κ`. `ℝ × T¹` with
  `expMeasure κ ⊗ Haar` is the working chart.
* The site arcs are the corpus's arc cells (`circleCell`, `circleOutcome`), read at the weights of
  the click time. The click-time law does not depend on the packet, because the norm is conserved.

## References

`DiracDetector.lean` (`siteWeight`, `re_chainInner_self`, `continuous_siteWeight_packet`,
`dirac_detector`); `CV/DiracPacketLimit.lean` (`chainInner_packet_self`); `DiracArrival.lean`
(`sum_siteWeight`); `CircleRecord.lean` (`circleOutcome`, `circleOutcome_eq_some_iff`);
`ArcAffine.lean` (`existsUnique_mem_circleCell`);
`CircleFibre.lean` (`circleCell`, `volume_circleCell`); `Mathlib/Probability/Distributions/
Exponential.lean` (`expMeasure`, `cdf_expMeasure_eq`); `specs/BACKLOG.md` #266, #252, #251, #265;
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory CSD.CV

noncomputable section

namespace CSD.RecordLayer

variable {n : ℕ}

/-! ### The click arena -/

/-- **The click fibre**: a click time and a point of the record circle. -/
abbrev ClickFibre : Type := ℝ × CircleFibre

/-- **The click law**: the click time exponential at rate `κ`, the circle point uniform. -/
def clickLaw (κ : ℝ) : Measure ClickFibre := (expMeasure κ).prod volume

/-- **The site an ontic point writes**: the arc, sized by the site weights at its click time, that
contains its circle point. -/
def clickSite (r : ℝ → Fin n → ℝ) (x : ClickFibre) : Option (Fin n) := circleOutcome (r x.1) x.2

/-- **The ontic points that write site `k` by time `t`.** -/
def clickCell (r : ℝ → Fin n → ℝ) (k : Fin n) (t : ℝ) : Set ClickFibre :=
  {x | x.1 ≤ t ∧ x.2 ∈ circleCell (r x.1) k}

variable {r : ℝ → Fin n → ℝ}

theorem measurableSet_clickCell (hr : ∀ k, Measurable fun s => r s k) (k : Fin n) (t : ℝ) :
    MeasurableSet (clickCell r k t) := by
  have hlo' : Measurable fun s => loSum (r s) k := by
    unfold loSum
    exact Finset.measurable_sum _ fun j _ => hr j
  have hlo : Measurable fun x : ClickFibre => loSum (r x.1) k := hlo'.comp measurable_fst
  have hk : Measurable fun x : ClickFibre => r x.1 k := (hr k).comp measurable_fst
  have hrep : Measurable fun x : ClickFibre => rep x.2 := measurable_rep.comp measurable_snd
  have he : clickCell r k t = {x : ClickFibre | x.1 ≤ t}
      ∩ ({x | loSum (r x.1) k < rep x.2} ∩ {x | rep x.2 ≤ loSum (r x.1) k + r x.1 k}) := by
    ext x
    exact Iff.rfl
  rw [he]
  exact (measurableSet_le measurable_fst measurable_const).inter
    ((measurableSet_lt hlo hrep).inter (measurableSet_le hrep (hlo.add hk)))

/-! ### One click -/

/-- **Writing site `k` by `t` is clicking by `t` at site `k`.** -/
theorem mem_clickCell_iff (hnn : ∀ s k, 0 ≤ r s k) (k : Fin n) (t : ℝ) (x : ClickFibre) :
    x ∈ clickCell r k t ↔ x.1 ≤ t ∧ clickSite r x = some k := by
  rw [clickSite, circleOutcome_eq_some_iff _ (hnn x.1)]
  exact Iff.rfl

/-- ★★★ **Every ontic point clicks at exactly one site.** -/
theorem existsUnique_clickSite (hnn : ∀ s k, 0 ≤ r s k) (hsum : ∀ s, ∑ k, r s k = 1)
    (x : ClickFibre) : ∃! k, clickSite r x = some k := by
  obtain ⟨k, hk, huniq⟩ := existsUnique_mem_circleCell (r x.1) (hnn x.1) (hsum x.1) x.2
  refine ⟨k, (circleOutcome_eq_some_iff _ (hnn x.1) _ _).2 hk, fun k' hk' => huniq k' ?_⟩
  exact (circleOutcome_eq_some_iff _ (hnn x.1) _ _).1 hk'

/-- ★★ **No ontic point writes two sites**, whatever the two times. -/
theorem clickCell_disjoint (hnn : ∀ s k, 0 ≤ r s k) {k k' : Fin n} (h : k ≠ k') (t t' : ℝ) :
    Disjoint (clickCell r k t) (clickCell r k' t') :=
  Set.disjoint_left.2 fun x hx hx' =>
    Set.disjoint_left.1 (circleCell_pairwiseDisjoint _ (hnn x.1) h) hx.2 hx'.2

/-! ### The law of the click -/

/-- ★★★ **The probability of site `k` by `t`.** It is the site weight of `k` at the click time,
integrated against the click-time law up to `t`: given a click at `s`, the site is distributed by
the weights at `s`. -/
theorem clickLaw_clickCell (κ : ℝ) (hr : ∀ k, Measurable fun s => r s k)
    (hnn : ∀ s k, 0 ≤ r s k) (hsum : ∀ s, ∑ k, r s k = 1) (k : Fin n) (t : ℝ) :
    clickLaw κ (clickCell r k t) = ∫⁻ s in Iic t, ENNReal.ofReal (r s k) ∂(expMeasure κ) := by
  rw [clickLaw, Measure.prod_apply (measurableSet_clickCell hr k t),
    ← lintegral_indicator measurableSet_Iic]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ≤ t
  · rw [indicator_of_mem (show s ∈ Iic t from hs)]
    have he : Prod.mk s ⁻¹' clickCell r k t = circleCell (r s) k := by
      ext η
      simp [clickCell, hs]
    rw [he, volume_circleCell _ (hnn s) (loSum_add_self_le_one _ (hnn s) (hsum s)) k]
  · rw [indicator_of_notMem (show s ∉ Iic t from hs)]
    have he : Prod.mk s ⁻¹' clickCell r k t = ∅ := by
      ext η
      simp [clickCell, hs]
    rw [he, measure_empty]

/-- ★★★ **The probability of a click by `t ≥ 0` is `1 − e^{−κt}`**, whatever the weights. -/
theorem clickLaw_clicked_by {κ : ℝ} (hκ : 0 < κ) (hr : ∀ k, Measurable fun s => r s k)
    (hnn : ∀ s k, 0 ≤ r s k) (hsum : ∀ s, ∑ k, r s k = 1) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k, clickLaw κ (clickCell r k t) = ENNReal.ofReal (1 - Real.exp (-(κ * t))) := by
  have := isProbabilityMeasure_expMeasure hκ
  simp_rw [clickLaw_clickCell κ hr hnn hsum]
  rw [← lintegral_finsetSum _ fun k _ => (hr k).ennreal_ofReal]
  have h1 : ∀ s, ∑ k, ENNReal.ofReal (r s k) = 1 := fun s => by
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn s k, hsum s, ENNReal.ofReal_one]
  simp_rw [h1]
  rw [setLIntegral_const, one_mul, ← ofReal_cdf, cdf_expMeasure_eq hκ]
  simp only [ht, ↓reduceIte]

/-! ### The click fibre on the torus -/

/-- **The click time read off a circle point**: `τ(ξ) = −log(rep ξ)/κ`. -/
def clickTime (κ : ℝ) (ξ : CircleFibre) : ℝ := -Real.log (rep ξ) / κ

theorem measurable_clickTime (κ : ℝ) : Measurable (clickTime κ) :=
  (Real.measurable_log.comp measurable_rep).neg.div_const κ

/-- ★★ **The uniform circle carries the exponential click-time law** under `clickTime κ`. -/
theorem map_clickTime {κ : ℝ} (hκ : 0 < κ) :
    (volume : Measure CircleFibre).map (clickTime κ) = expMeasure κ := by
  have := isProbabilityMeasure_expMeasure hκ
  refine (Measure.ext_of_Iic _ _ fun t => ?_)
  rw [Measure.map_apply (measurable_clickTime κ) measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq hκ]
  have hpre : clickTime κ ⁻¹' Iic t = rep ⁻¹' Ici (Real.exp (-(κ * t))) := by
    ext ξ
    simp only [mem_preimage, mem_Iic, mem_Ici, clickTime]
    rw [div_le_iff₀ hκ, ← Real.log_le_log_iff (Real.exp_pos _) (rep_pos ξ), Real.log_exp]
    constructor <;> intro h <;> linarith
  rw [hpre, volume_rep_preimage measurableSet_Ici]
  by_cases ht : 0 ≤ t
  · have hc1 : Real.exp (-(κ * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have he : Ici (Real.exp (-(κ * t))) ∩ Ioc (0 : ℝ) 1 = Icc (Real.exp (-(κ * t))) 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, lt_of_lt_of_le (Real.exp_pos _) h1, h3⟩
    rw [he, Real.volume_Icc]
    simp only [ht, ↓reduceIte]
  · have hc1 : 1 < Real.exp (-(κ * t)) := Real.one_lt_exp_iff.2 (by nlinarith)
    have he : Ici (Real.exp (-(κ * t))) ∩ Ioc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_empty_iff_false, iff_false]
      rintro ⟨h1, -, h3⟩
      linarith
    rw [he, measure_empty]
    simp only [ht, ↓reduceIte, ENNReal.ofReal_zero]

/-- **The torus point's click**: its first coordinate read as the click time, its second as the
circle point. -/
def torusClick (κ : ℝ) (x : LF4.KTorus) : ClickFibre := (clickTime κ x.1, x.2)

/-- ★★★ **The torus with its Haar measure carries the click law.** So every statement about
`clickLaw κ` holds on the corpus's compact fibre `T²`, through `torusClick κ`. -/
theorem measurePreserving_torusClick {κ : ℝ} (hκ : 0 < κ) :
    MeasurePreserving (torusClick κ) (volume : Measure LF4.KTorus) (clickLaw κ) := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.prod ⟨measurable_clickTime κ, map_clickTime hκ⟩
    (MeasurePreserving.id (volume : Measure CircleFibre)) : _)

/-- ★★★ **On the torus: the probability of site `k` by `t`**, the same as on `ℝ × T¹`. -/
theorem volume_torusClick_clickCell {κ : ℝ} (hκ : 0 < κ) (hr : ∀ k, Measurable fun s => r s k)
    (hnn : ∀ s k, 0 ≤ r s k) (hsum : ∀ s, ∑ k, r s k = 1) (k : Fin n) (t : ℝ) :
    (volume : Measure LF4.KTorus) (torusClick κ ⁻¹' clickCell r k t)
      = ∫⁻ s in Iic t, ENNReal.ofReal (r s k) ∂(expMeasure κ) := by
  rw [(measurePreserving_torusClick hκ).measure_preimage
    (measurableSet_clickCell hr k t).nullMeasurableSet, clickLaw_clickCell κ hr hnn hsum]

/-! ### The chain's site weights -/

/-- **The site weights of a chain trajectory**: the weight `‖ψ_k‖²` on each site over the norm. -/
def siteRate (ψ : ℝ → ZMod (n + 1) × Fin 2 → ℂ) (N : ℝ) (s : ℝ) (k : Fin (n + 1)) : ℝ :=
  siteWeight (ψ s) k / N

theorem siteRate_nonneg (ψ : ℝ → ZMod (n + 1) × Fin 2 → ℂ) {N : ℝ} (hN : 0 < N) (s : ℝ)
    (k : Fin (n + 1)) : 0 ≤ siteRate ψ N s k :=
  div_nonneg (siteWeight_nonneg _ _) hN.le

theorem sum_siteRate (ψ : ℝ → ZMod (n + 1) × Fin 2 → ℂ) {N : ℝ} (hN : 0 < N)
    (hnorm : ∀ s, (chainInner (ψ s) (ψ s)).re = N) (s : ℝ) : ∑ k, siteRate ψ N s k = 1 := by
  have h := sum_siteWeight (ψ s)
  rw [hnorm s] at h
  calc ∑ k, siteRate ψ N s k = (∑ k : Fin (n + 1), siteWeight (ψ s) k) / N :=
        (Finset.sum_div _ _ _).symm
    _ = 1 := by rw [div_eq_one_iff_eq hN.ne']; exact h

theorem measurable_siteRate {ψ : ℝ → ZMod (n + 1) × Fin 2 → ℂ} (hψ : Continuous ψ) (N : ℝ)
    (k : Fin (n + 1)) : Measurable fun s => siteRate ψ N s k :=
  ((continuous_siteWeight (L := n + 1) k).comp hψ).measurable.div_const N

/-- ★★★ **One click for any norm-conserving chain trajectory.** Every ontic point clicks at
exactly one site; no ontic point writes two sites; the probability of site `k` by `t` is the site
weight `w_k(s)/N` integrated against the click-time law; and a click has occurred by `t ≥ 0` with
probability `1 − e^{−κt}`. -/
theorem chain_one_click {ψ : ℝ → ZMod (n + 1) × Fin 2 → ℂ} (hψ : Continuous ψ) {N : ℝ}
    (hN : 0 < N) (hnorm : ∀ s, (chainInner (ψ s) (ψ s)).re = N) {κ : ℝ} (hκ : 0 < κ) :
    (∀ x, ∃! k, clickSite (siteRate ψ N) x = some k) ∧
    (∀ k k', k ≠ k' → ∀ t t',
      Disjoint (clickCell (siteRate ψ N) k t) (clickCell (siteRate ψ N) k' t')) ∧
    (∀ k t, clickLaw κ (clickCell (siteRate ψ N) k t)
      = ∫⁻ s in Iic t, ENNReal.ofReal (siteWeight (ψ s) k / N) ∂(expMeasure κ)) ∧
    (∀ t, 0 ≤ t → ∑ k, clickLaw κ (clickCell (siteRate ψ N) k t)
      = ENNReal.ofReal (1 - Real.exp (-(κ * t)))) ∧
    (∀ k t, (volume : Measure LF4.KTorus) (torusClick κ ⁻¹' clickCell (siteRate ψ N) k t)
      = ∫⁻ s in Iic t, ENNReal.ofReal (siteWeight (ψ s) k / N) ∂(expMeasure κ)) :=
  ⟨existsUnique_clickSite (siteRate_nonneg ψ hN) (sum_siteRate ψ hN hnorm),
    fun _ _ h t t' => clickCell_disjoint (siteRate_nonneg ψ hN) h t t',
    clickLaw_clickCell κ (measurable_siteRate hψ N) (siteRate_nonneg ψ hN)
      (sum_siteRate ψ hN hnorm),
    fun _ ht => clickLaw_clicked_by hκ (measurable_siteRate hψ N) (siteRate_nonneg ψ hN)
      (sum_siteRate ψ hN hnorm) ht,
    volume_torusClick_clickCell hκ (measurable_siteRate hψ N) (siteRate_nonneg ψ hN)
      (sum_siteRate ψ hN hnorm)⟩

/-- ★★★ **One click for every Dirac packet of the chain** — the packet of `dirac_detector`
included (`twoMode` is `packet 4 3 {0, 1} 1` on `12 = 11 + 1` sites). The norm is the packet's
`Σ_m (‖a_m‖ ‖mode_m‖)²` (`chainInner_packet_self`), conserved in time. -/
theorem dirac_packet_one_click (J μ : ℝ) {W : Finset ℤ} (hD : Distinct (n + 1) W) (a : ℤ → ℂ)
    (hN : 0 < ∑ m ∈ W, (‖a m‖ * modeNorm (n + 1) J μ m) ^ 2) {κ : ℝ} (hκ : 0 < κ) :
    let ψ := fun s => packet (L := n + 1) J μ W a s
    let N := ∑ m ∈ W, (‖a m‖ * modeNorm (n + 1) J μ m) ^ 2
    (∀ x, ∃! k, clickSite (siteRate ψ N) x = some k) ∧
    (∀ k k', k ≠ k' → ∀ t t',
      Disjoint (clickCell (siteRate ψ N) k t) (clickCell (siteRate ψ N) k' t')) ∧
    (∀ k t, clickLaw κ (clickCell (siteRate ψ N) k t)
      = ∫⁻ s in Iic t, ENNReal.ofReal (siteWeight (ψ s) k / N) ∂(expMeasure κ)) ∧
    (∀ t, 0 ≤ t → ∑ k, clickLaw κ (clickCell (siteRate ψ N) k t)
      = ENNReal.ofReal (1 - Real.exp (-(κ * t)))) ∧
    (∀ k t, (volume : Measure LF4.KTorus) (torusClick κ ⁻¹' clickCell (siteRate ψ N) k t)
      = ∫⁻ s in Iic t, ENNReal.ofReal (siteWeight (ψ s) k / N) ∂(expMeasure κ)) := by
  intro ψ N
  refine chain_one_click ((continuous_packet J μ W).comp
    (continuous_const.prodMk continuous_id)) hN (fun s => ?_) hκ
  show (chainInner (packet J μ W a s) (packet J μ W a s)).re = _
  rw [chainInner_packet_self J μ hD a s, Complex.ofReal_re]

end CSD.RecordLayer

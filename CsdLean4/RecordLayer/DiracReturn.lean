/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracTwin

/-!
# A return leg on the Dirac chain, by reflection

**Category:** 7-SigmaLayer (the record layer). BACKLOG #270 (split from #256).

The free ring sends nothing back. Here the messenger is **reflected**, exactly, by the method of
images. Parity — `x ↦ −x` with `σ_z` — is a symmetry of the lattice Dirac Hamiltonian, so its even
sector evolves on its own: it is the chain on the segment from `A` (site `0`) to the antipode `B`, with
**reflecting ends** at both. A messenger leaving `A` together with its parity image is such a state.
It runs to `B`, is reflected there, and comes back to `A`: the emission, the reception at `B` and the
return to `A` are three ordered actual occurrences of one evolution, and the round trip is
`2 ℓ_AB / v` to within `0.3·1.25·10¹³`.

## Parity

* `chainParity`, `chainParity_chainParity`, `chainParity_add`, `chainParity_smul`, `chainParity_sum`;
  ★★ `diracHam_mulVec_chainParity` — **parity commutes with the Dirac Hamiltonian**;
* `angleZ_neg`, `dispE_neg`, `bandE_angleZ_neg`, `modeS_neg_intCast`, ★ `chainParity_diracMode` (a
  mode goes to the opposite momentum), `spinNorm_neg`, `unitAmp_neg`; ★★ `chainParity_packet`,
  ★★ `chainParity_ringPacket` — **the image of a packet is the mirror packet**;
* ★ `chainInner_packet_packet` — **packets with no common momentum are orthogonal**.

## A packet and its image

* `regionWeight_smul_add` (the pair's weight is the average plus the interference),
  ★ `abs_re_interference_le` (**the interference is at most the geometric mean**),
  `interference_compl`; ★ `le_regionWeight_pair` (**where both are, the pair is**),
  ★ `regionWeight_pair_le` (**where neither is, it is not**), `chainInner_pair`.

## The messenger between reflecting ends

* `chordArc_subset`, `chordArc_subset_compl`, `regionWeight_mono`, `norm_exp_sub_exp_eq`,
  `exp_I_mul_two_pi_mul`, `exp_I_mul_pi_add`, `near_one`, `near_neg_one`, `quarter_lt_two_sin`,
  `far_one`, `far_neg_one`; `integral_le_three`, `le_integral_two`;
* `imageWin`, `mem_imageWin`, `outPacket` (`2·10⁶` modes about momentum `4`, velocity `4/5`),
  `imagePacket`, ★★ `wallState` (the messenger with its image); `chainParity_outPacket`,
  `chainParity_imagePacket`, ★★ `chainParity_wallState` — **the state stays parity-even**;
  `image_spread`, `vRel_image`, `omega_image`, `image_win`, `outPacket_norm`, `imagePacket_norm`,
  `chainInner_out_image`, `wallState_norm`;
* `out_tail`, `image_tail` (each within chord `1/20` of its prediction but for `10⁻³`);
  ★ `wall_near`, ★ `wall_far`, `wall_le_one`; `wallA_start`, `wallA_end`, `wallA_away`, `wallB_near`,
  `wallB_before`.

## The records

* `chainProp_wallState`, `continuous_wallWeight`; `emission_before`, `emission_after`,
  `reception_before`, `reception_after`, `wall_return_before`, `wall_return_after`;
  ★★★ `wallEmission`, ★★★ `wallReception`, ★★★ `wallReturn`; `wallEmission_evolve`,
  `wallReception_evolve`, `wallReturn_evolve`, `wallEmission_prep`, `wallReception_prep`,
  `wallReturn_prep`;
* ★★★ `dirac_return` — **parity commutes with the Hamiltonian and the state stays parity-even;
  emission at `A`, reception at `B` and return at `A` are actual occurrences of one evolution from one
  preparation, ordered; and the round trip from the emission's write to the return's lies within
  `0.3·1.25·10¹³` below `2 ℓ_AB / v`**, `ℓ_AB = ℓ/2`, `v = 4/5` both ways.

## The finding

**A Dirac messenger comes back, reflected, and the round trip is read off the records.** The
reflection is exact, and nothing about the lattice is approximated: the reflecting ends are those of
the parity-even sector.

## Honest scope

⚠️ **The reflector is a symmetry wall, at rest.** The even sector is invariant, and is the segment
with reflecting ends; the segment Hamiltonian is not written out (#275). A moving reflector — or a
relay at a moving observer — is what #256's Doppler factor needs, and images do not give it (#274).

⚠️ **`A` sits at one end and `B` at the other**, each with a region detector of a stated law
(#251, #266). The emission and the return are read off the same register at two thresholds, the return's
threshold set between the half lobe of the departure and the full lobe of the return.

References: `specs/BACKLOG.md` #270, #256, #269, #253, #274, #275, #251, #266, #39;
`CV/DiracClockChain.lean` (`diracHam`, `diracMode`, `modeS`); `CV/DiracPacket.lean` (`packet`,
`chainInner_planeWave`); `CV/DiracPacketLimit.lean` (`ringPacket`, `unitAmp`, `dirac_packet_limit`);
`RecordLayer/DiracArrival.lean` (`regionDetector`, `chainProp_packet`); `RecordLayer/DiracTiming.lean`
(`diracHam_mulVec_apply`); `RecordLayer/DiracObservers.lean` (chords,
`regionWeight_compl_chordArc_le`); `RecordLayer/DiracTwin.lean` (`twin_budget`, `moving_spread`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {L : ℕ} [NeZero L]

/-! ### Parity -/

/-- **Parity on the chain**: `(Pφ)(j, a) = ±φ(−j, a)`, `+` on the upper component, `−` on the lower
(`x ↦ −x` with `σ_z`). -/
def chainParity (φ : ZMod L × Fin 2 → ℂ) : ZMod L × Fin 2 → ℂ := fun p =>
  (if p.2 = 0 then 1 else -1) * φ (-p.1, p.2)

omit [NeZero L] in
theorem chainParity_chainParity (φ : ZMod L × Fin 2 → ℂ) : chainParity (chainParity φ) = φ := by
  funext ⟨j, a⟩
  simp only [chainParity, neg_neg]
  fin_cases a <;> simp

/-- ★★ **Parity is a symmetry of the Dirac chain**: `H P = P H`. Its even sector is a chain on the
segment `[0, L/2]` with reflecting ends at `0` and at the antipode. -/
theorem diracHam_mulVec_chainParity (J μ : ℝ) (φ : ZMod L × Fin 2 → ℂ) :
    diracHam J μ *ᵥ chainParity φ = chainParity (diracHam J μ *ᵥ φ) := by
  funext ⟨j, a⟩
  rw [diracHam_mulVec_apply]
  simp only [chainParity]
  rw [diracHam_mulVec_apply]
  have e1 : -(j + 1) = -j - 1 := by ring
  have e2 : -(j - 1) = -j + 1 := by ring
  rw [e1, e2]
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, show (1 : Fin 2) - 0 = 1 from rfl,
      one_ne_zero]
    ring
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, show (1 : Fin 2) - 1 = 0 from rfl]
    ring

omit [NeZero L] in
theorem chainParity_add (φ ψ : ZMod L × Fin 2 → ℂ) :
    chainParity (φ + ψ) = chainParity φ + chainParity ψ := by
  funext p
  simp only [chainParity, Pi.add_apply]
  ring

omit [NeZero L] in
theorem chainParity_smul (c : ℂ) (φ : ZMod L × Fin 2 → ℂ) :
    chainParity (c • φ) = c • chainParity φ := by
  funext p
  simp only [chainParity, Pi.smul_apply, smul_eq_mul]
  ring

omit [NeZero L] in
theorem chainParity_sum {ι : Type*} (s : Finset ι) (v : ι → ZMod L × Fin 2 → ℂ) :
    chainParity (∑ i ∈ s, v i) = ∑ i ∈ s, chainParity (v i) := by
  funext p
  simp only [chainParity, Finset.sum_apply, Finset.mul_sum]

omit [NeZero L] in
theorem angleZ_neg (m : ℤ) : angleZ L (-m) = -angleZ L m := by
  simp only [angleZ]
  push_cast
  ring

theorem dispE_neg (μ s : ℝ) : dispE μ (-s) = dispE μ s := by
  rw [dispE, dispE, neg_sq]

omit [NeZero L] in
theorem bandE_angleZ_neg (J μ : ℝ) (m : ℤ) :
    bandE J μ (angleZ L (-m)) = bandE J μ (angleZ L m) := by
  rw [bandE, bandE, angleZ_neg, Real.sin_neg, show 2 * J * -Real.sin (angleZ L m)
    = -(2 * J * Real.sin (angleZ L m)) by ring, dispE_neg]

theorem modeS_neg_intCast (J : ℝ) (m : ℤ) :
    modeS J (((-m : ℤ)) : ZMod L) = -modeS J (m : ZMod L) := by
  rw [modeS, modeS, latticeAngle_intCast_sin, latticeAngle_intCast_sin, angleZ_neg, Real.sin_neg]
  ring

/-- **Parity sends a mode to the opposite momentum.** -/
theorem chainParity_diracMode (J μ : ℝ) (m : ℤ) :
    chainParity (diracMode J μ (m : ZMod L)) = diracMode J μ (((-m : ℤ)) : ZMod L) := by
  funext ⟨j, a⟩
  simp only [chainParity, diracMode, modeS_neg_intCast, dispE_neg]
  have hpw : planeWave (m : ZMod L) (-j) = planeWave (((-m : ℤ)) : ZMod L) j := by
    rw [planeWave, planeWave]
    congr 2
    push_cast
    ring
  rw [hpw]
  fin_cases a
  · simp
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    push_cast
    ring

theorem spinNorm_neg (J μ θ : ℝ) : spinNorm J μ (-θ) = spinNorm J μ θ := by
  rw [spinNorm, spinNorm, Real.sin_neg, bandE, bandE, Real.sin_neg,
    show 2 * J * -Real.sin θ = -(2 * J * Real.sin θ) by ring, dispE_neg, neg_sq]

omit [NeZero L] in
theorem unitAmp_neg (J μ : ℝ) (β : ℤ → ℂ) (m : ℤ) :
    unitAmp L J μ β (-m) = unitAmp L J μ (fun m => β (-m)) m := by
  rw [unitAmp, unitAmp, modeNorm, modeNorm, angleZ_neg, spinNorm_neg]

/-- ★★ **Parity sends a packet to its mirror image**: the window reflected through `0`, the
amplitudes with it. -/
theorem chainParity_packet (J μ : ℝ) {W W' : Finset ℤ} (hW : ∀ m, m ∈ W' ↔ -m ∈ W)
    (a : ℤ → ℂ) (t : ℝ) :
    chainParity (packet (L := L) J μ W a t) = packet J μ W' (fun m => a (-m)) t := by
  rw [packet, packet, chainParity_sum]
  simp only [chainParity_smul, chainParity_diracMode]
  refine Finset.sum_nbij' (fun m => -m) (fun m => -m) (fun m hm => (hW _).2 (by rwa [neg_neg]))
    (fun m hm => (hW m).1 hm) (fun m _ => neg_neg m) (fun m _ => neg_neg m) fun m _ => ?_
  rw [neg_neg, bandE_angleZ_neg]

/-- **The mirror image of a ring packet is a ring packet.** -/
theorem chainParity_ringPacket (c μ ℓ : ℝ) {W W' : Finset ℤ} (hW : ∀ m, m ∈ W' ↔ -m ∈ W)
    (β : ℤ → ℂ) (t : ℝ) :
    chainParity (ringPacket (L := L) c μ ℓ W β t) = ringPacket c μ ℓ W' (fun m => β (-m)) t := by
  rw [ringPacket, chainParity_packet _ _ hW, ringPacket]
  congr 1
  funext m
  exact unitAmp_neg _ _ β m

/-- **Packets on windows with no common momentum are orthogonal.** -/
theorem chainInner_packet_packet (J μ : ℝ) {W W' : Finset ℤ}
    (h : ∀ m ∈ W, ∀ m' ∈ W', (m : ZMod L) ≠ (m' : ZMod L)) (a b : ℤ → ℂ) (t : ℝ) :
    chainInner (packet (L := L) J μ W a t) (packet J μ W' b t) = 0 := by
  rw [packet, chainInner_sum_left]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [packet, chainInner_sum_right]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m' hm' => ?_)
  rw [diracMode_eq, diracMode_eq, chainInner_planeWave]
  simp [h m hm m' hm']

/-! ### A packet and its image -/

omit [NeZero L] in
/-- **The weight of a packet and its image**: for `ψ = (R + M)/√2`, the weight on `A` is the
average of `R`'s and `M`'s plus the interference `Re Σ_A R̄ M`. -/
theorem regionWeight_smul_add (R M : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    regionWeight (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (R + M)) A
      = (regionWeight R A + regionWeight M A) / 2
        + (∑ k ∈ A, ∑ c : Fin 2, star (R (k, c)) * M (k, c)).re := by
  simp only [regionWeight, siteWeight, Complex.re_sum]
  rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have h2 : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hs]
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, h2]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

omit [NeZero L] in
/-- **The interference on a region is at most the geometric mean of the weights there.** -/
theorem abs_re_interference_le (R M : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) {τ : ℝ}
    (hτ : 0 ≤ τ) (hR : regionWeight R A ≤ τ) (hM : regionWeight M A ≤ τ) :
    |(∑ k ∈ A, ∑ c : Fin 2, star (R (k, c)) * M (k, c)).re| ≤ τ := by
  set S := ∑ p ∈ A ×ˢ (Finset.univ : Finset (Fin 2)), ‖R p‖ * ‖M p‖
  have h1 : ‖∑ k ∈ A, ∑ c : Fin 2, star (R (k, c)) * M (k, c)‖ ≤ S := by
    rw [← Finset.sum_product' (f := fun k c => star (R (k, c)) * M (k, c))]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [norm_mul, Complex.star_def, Complex.norm_conj]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (A ×ˢ (Finset.univ : Finset (Fin 2)))
    (fun p => ‖R p‖) (fun p => ‖M p‖)
  have hRw : ∑ p ∈ A ×ˢ (Finset.univ : Finset (Fin 2)), ‖R p‖ ^ 2 = regionWeight R A := by
    rw [Finset.sum_product' (f := fun k c => ‖R (k, c)‖ ^ 2)]
    rfl
  have hMw : ∑ p ∈ A ×ˢ (Finset.univ : Finset (Fin 2)), ‖M p‖ ^ 2 = regionWeight M A := by
    rw [Finset.sum_product' (f := fun k c => ‖M (k, c)‖ ^ 2)]
    rfl
  rw [hRw, hMw] at hcs
  have hR0 : 0 ≤ regionWeight R A := regionWeight_nonneg R A
  have hM0 : 0 ≤ regionWeight M A := regionWeight_nonneg M A
  have hsq : S ^ 2 ≤ τ ^ 2 := hcs.trans (by nlinarith)
  have hSτ : S ≤ τ := by nlinarith
  exact (Complex.abs_re_le_norm _).trans (h1.trans hSτ)

/-- **Orthogonality moves the interference to the complement.** -/
theorem interference_compl {R M : ZMod L × Fin 2 → ℂ} (h : chainInner R M = 0)
    (A : Finset (ZMod L)) :
    ∑ k ∈ A, ∑ c : Fin 2, star (R (k, c)) * M (k, c)
      = -∑ k ∈ Aᶜ, ∑ c : Fin 2, star (R (k, c)) * M (k, c) := by
  have e : chainInner R M = ∑ k ∈ A, ∑ c : Fin 2, star (R (k, c)) * M (k, c)
      + ∑ k ∈ Aᶜ, ∑ c : Fin 2, star (R (k, c)) * M (k, c) := by
    rw [Finset.sum_add_sum_compl, chainInner, Fintype.sum_prod_type]
  rw [h] at e
  linear_combination -e

/-- ★ **Where both are, the pair is**: if `R` and `M` are orthogonal, normalised and each has at most
`τ` off `A`, the pair `(R + M)/√2` has at least `1 − 2τ` on `A`. -/
theorem le_regionWeight_pair {R M : ZMod L × Fin 2 → ℂ} (hRM : chainInner R M = 0)
    (hR1 : chainInner R R = 1) (hM1 : chainInner M M = 1) (A : Finset (ZMod L)) {τ : ℝ}
    (hτ : 0 ≤ τ) (hR : regionWeight R Aᶜ ≤ τ) (hM : regionWeight M Aᶜ ≤ τ) :
    1 - 2 * τ ≤ regionWeight (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (R + M)) A := by
  rw [regionWeight_smul_add, interference_compl hRM, Complex.neg_re]
  have hi := abs_re_interference_le R M Aᶜ hτ hR hM
  have eR := regionWeight_add_compl R A
  have eM := regionWeight_add_compl M A
  rw [hR1, Complex.one_re] at eR
  rw [hM1, Complex.one_re] at eM
  have := neg_abs_le (∑ k ∈ Aᶜ, ∑ c : Fin 2, star (R (k, c)) * M (k, c)).re
  linarith [abs_le.1 hi]

omit [NeZero L] in
/-- ★ **Where neither is, the pair is not**: if `R` and `M` each have at most `τ` on `A`, the pair
has at most `2τ` there. -/
theorem regionWeight_pair_le {R M : ZMod L × Fin 2 → ℂ} (A : Finset (ZMod L)) {τ : ℝ}
    (hτ : 0 ≤ τ) (hR : regionWeight R A ≤ τ) (hM : regionWeight M A ≤ τ) :
    regionWeight (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (R + M)) A ≤ 2 * τ := by
  rw [regionWeight_smul_add]
  have hi := abs_re_interference_le R M A hτ hR hM
  linarith [abs_le.1 hi]

/-- **The pair is normalised.** -/
theorem chainInner_pair {R M : ZMod L × Fin 2 → ℂ} (hRM : chainInner R M = 0)
    (hR1 : chainInner R R = 1) (hM1 : chainInner M M = 1) :
    chainInner (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (R + M)) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (R + M)) = 1 := by
  have hMR : chainInner M R = 0 := by
    have : chainInner M R = star (chainInner R M) := by
      simp only [chainInner, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    rw [this, hRM, star_zero]
  have hlin : ∀ (c : ℂ) (u v w : ZMod L × Fin 2 → ℂ),
      chainInner (c • (u + v)) (c • w) = star c * c * (chainInner u w + chainInner v w) := by
    intro c u v w
    simp only [chainInner, Pi.smul_apply, Pi.add_apply, smul_eq_mul, star_mul', star_add,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hsplit : ∀ u v : ZMod L × Fin 2 → ℂ, chainInner u (R + M) = chainInner u R + chainInner u M :=
    fun u v => by simp only [chainInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hlin, hsplit R R, hsplit M M, hRM, hMR, hR1, hM1, star_sqrt_two_inv]
  norm_num

/-! ### Arcs and phases -/

theorem chordArc_subset {z w : ℂ} {ρ σ : ℝ} (h : ‖z - w‖ + ρ ≤ σ) :
    (chordArc (L := L) z ρ) ⊆ chordArc w σ := fun k hk => by
  rw [mem_chordArc] at hk ⊢
  have := norm_sub_le_norm_sub_add_norm_sub (ZMod.toCircle k : ℂ) z w
  linarith

theorem chordArc_subset_compl {z w : ℂ} {ρ σ : ℝ} (h : σ + ρ < ‖z - w‖) :
    (chordArc (L := L) w σ) ⊆ (chordArc z ρ)ᶜ := fun k hk => by
  rw [mem_chordArc] at hk
  rw [Finset.mem_compl, mem_chordArc, not_le]
  have := norm_sub_le_norm_sub_add_norm_sub z (ZMod.toCircle k : ℂ) w
  rw [norm_sub_rev z (ZMod.toCircle k : ℂ)] at this
  linarith

omit [NeZero L] in
theorem regionWeight_mono (ψ : ZMod L × Fin 2 → ℂ) {A B : Finset (ZMod L)} (h : A ⊆ B) :
    regionWeight ψ A ≤ regionWeight ψ B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun k _ _ => siteWeight_nonneg ψ k

theorem norm_exp_sub_exp_eq (x y : ℝ) :
    ‖exp (I * (x : ℂ)) - exp (I * (y : ℂ))‖ = ‖exp (I * ((x - y : ℝ) : ℂ)) - 1‖ := by
  rw [show exp (I * (x : ℂ)) - exp (I * (y : ℂ))
      = exp (I * (y : ℂ)) * (exp (I * ((x - y : ℝ) : ℂ)) - 1) by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring, norm_mul, norm_exp_I_mul_ofReal_eq_one, one_mul]

theorem exp_I_mul_two_pi_mul (k : ℤ) : exp (I * ((2 * Real.pi * k : ℝ) : ℂ)) = 1 := by
  rw [show I * ((2 * Real.pi * k : ℝ) : ℂ) = k * (2 * Real.pi * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I]

theorem exp_I_mul_pi_add (k : ℤ) : exp (I * ((Real.pi + 2 * Real.pi * k : ℝ) : ℂ)) = -1 := by
  rw [show I * ((Real.pi + 2 * Real.pi * k : ℝ) : ℂ) = Real.pi * I + k * (2 * Real.pi * I) by
    push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I]
  ring

/-- **Near `1`**: within `3/20` of a multiple of `2π`, the point `e^{ix}` is within `3/20` of `1`. -/
theorem near_one {x : ℝ} (k : ℤ) (h : |x - 2 * Real.pi * k| ≤ 3 / 20) :
    ‖exp (I * (x : ℂ)) - 1‖ ≤ 3 / 20 := by
  have e := norm_exp_sub_exp_le x (2 * Real.pi * k)
  rw [exp_I_mul_two_pi_mul] at e
  exact e.trans h

/-- **Near `−1`**: within `3/20` of `π` modulo `2π`. -/
theorem near_neg_one {x : ℝ} (k : ℤ) (h : |x - (Real.pi + 2 * Real.pi * k)| ≤ 3 / 20) :
    ‖exp (I * (x : ℂ)) - (-1)‖ ≤ 3 / 20 := by
  have e := norm_exp_sub_exp_le x (Real.pi + 2 * Real.pi * k)
  rw [exp_I_mul_pi_add] at e
  exact e.trans h

theorem quarter_lt_two_sin : (1 / 4 : ℝ) < 2 * Real.sin (13 / 50 / 2) := by
  have h := Real.sin_gt_sub_cube (x := 13 / 50 / 2) (by norm_num)
  have : (1 / 4 : ℝ) < 2 * (13 / 50 / 2 - (13 / 50 / 2) ^ 3 / 6) := by norm_num
  linarith

/-- **Far from `1`**: at least `13/50` from every multiple of `2π` (`13/50 ≤ |x| ≤ 2π − 13/50`). -/
theorem far_one {x : ℝ} (h1 : 13 / 50 ≤ |x|) (h2 : |x| ≤ 2 * Real.pi - 13 / 50) :
    1 / 4 < ‖exp (I * (x : ℂ)) - 1‖ :=
  quarter_lt_two_sin.trans_le (two_sin_le_norm_exp_sub_one (by norm_num) h1 h2)

/-- **Far from `−1`**: `13/50 ≤ |x − π| ≤ 2π − 13/50`. -/
theorem far_neg_one {x : ℝ} (h1 : 13 / 50 ≤ |x - Real.pi|)
    (h2 : |x - Real.pi| ≤ 2 * Real.pi - 13 / 50) :
    1 / 4 < ‖exp (I * (x : ℂ)) - (-1)‖ := by
  have e := norm_exp_sub_exp_eq x Real.pi
  rw [show exp (I * (Real.pi : ℂ)) = -1 by
    rw [show I * (Real.pi : ℂ) = Real.pi * I by ring, Complex.exp_pi_mul_I]] at e
  rw [e]
  exact far_one h1 h2

/-! ### Integrals over three phases -/

/-- An integrand at most `1`, and at most `ε ≥ 0` on `[a, b]`, integrates by `t ≥ 0` to at most
`a + ε (b − a) + max(0, t − b)`, and to at most `t` while `t ≤ a`. -/
theorem integral_le_three {F : ℝ → ℝ} (hF : Continuous F) (h1 : ∀ s, F s ≤ 1) {ε a b t : ℝ}
    (hε : 0 ≤ ε) (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t)
    (hmid : ∀ s, a ≤ s → s ≤ b → F s ≤ ε) :
    ∫ s in (0 : ℝ)..t, F s ≤ a + ε * (b - a) + max 0 (t - b) := by
  have hi : ∀ x y : ℝ, IntervalIntegrable F volume x y := fun x y => hF.intervalIntegrable x y
  have one : ∀ x y : ℝ, x ≤ y → ∫ s in x..y, F s ≤ y - x := fun x y hxy => by
    have := intervalIntegral.integral_mono_on hxy (hi x y)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun s _ => h1 s
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  have eps : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b → ∫ s in x..y, F s ≤ ε * (y - x) :=
    fun x y hx hxy hy => by
      have := intervalIntegral.integral_mono_on hxy (hi x y)
        (intervalIntegrable_const (μ := volume) (c := ε)) fun s hs =>
          hmid s (hx.trans hs.1) (hs.2.trans hy)
      rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this
  have hm0 := le_max_left 0 (t - b)
  have hm1 := le_max_right 0 (t - b)
  rcases le_total t a with h | h
  · have := one 0 t ht
    nlinarith
  rcases le_total t b with h' | h'
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a t)]
    have e1 := one 0 a ha
    have e2 := eps a t le_rfl h h'
    nlinarith
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a t),
      ← intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b t)]
    have e1 := one 0 a ha
    have e2 := eps a b le_rfl hab le_rfl
    have e3 := one b t h'
    linarith

/-- A nonnegative integrand at least `κ` on `[0, a]` and on `[c, t]` integrates to at least
`κ a + κ (t − c)`. -/
theorem le_integral_two {F : ℝ → ℝ} (hF : Continuous F) (hpos : ∀ s, 0 ≤ s → 0 ≤ F s)
    {κ a c t : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hct : c ≤ t) (h1 : ∀ s, 0 ≤ s → s ≤ a → κ ≤ F s)
    (h2 : ∀ s, c ≤ s → s ≤ t → κ ≤ F s) :
    κ * a + κ * (t - c) ≤ ∫ s in (0 : ℝ)..t, F s := by
  have hi : ∀ x y : ℝ, IntervalIntegrable F volume x y := fun x y => hF.intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a t),
    ← intervalIntegral.integral_add_adjacent_intervals (hi a c) (hi c t)]
  have e1 := intervalIntegral.integral_mono_on ha (intervalIntegrable_const (μ := volume) (c := κ))
    (hi 0 a) fun s hs => h1 s hs.1 hs.2
  have e2 := intervalIntegral.integral_nonneg (μ := volume) hac fun s hs => hpos s (ha.trans hs.1)
  have e3 := intervalIntegral.integral_mono_on hct (intervalIntegrable_const (μ := volume) (c := κ))
    (hi c t) fun s hs => h2 s hs.1 hs.2
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm] at e1
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at e3
  linarith

/-! ### The messenger and its image -/

/-- **The image window**: the messenger's window reflected through `0`. -/
def imageWin : Finset ℤ :=
  Finset.Ico (-(4 * 10 ^ 13) - 1999999 : ℤ) (-(4 * 10 ^ 13) - 1999999 + (2000000 : ℕ))

theorem mem_imageWin (m : ℤ) :
    m ∈ imageWin ↔ -m ∈ Finset.Ico (4 * 10 ^ 13 : ℤ) (4 * 10 ^ 13 + (2000000 : ℕ)) := by
  simp only [imageWin, Finset.mem_Ico]
  push_cast
  omega

/-- **The messenger**: a packet of `2·10⁶` modes about momentum `4` (velocity `4/5`), from `A`. -/
noncomputable def outPacket (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ringPacket (L := L) 1 3 (2 * Real.pi * 10 ^ 13)
    (Finset.Ico (4 * 10 ^ 13 : ℤ) (4 * 10 ^ 13 + (2000000 : ℕ))) twinAmp t

/-- **Its image**: the parity image, about momentum `−4`. -/
noncomputable def imagePacket (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ringPacket (L := L) 1 3 (2 * Real.pi * 10 ^ 13) imageWin twinAmp t

/-- ★★ **The messenger between reflecting ends**: the messenger and its image, the parity-even
state of the ring — a state of the segment from `A` to the antipode with reflecting ends. -/
noncomputable def wallState (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (outPacket (L := L) t + imagePacket (L := L) t)

theorem chainParity_outPacket (t : ℝ) : chainParity (outPacket (L := L) t) = imagePacket t := by
  rw [outPacket, chainParity_ringPacket _ _ _ mem_imageWin]
  rfl

theorem chainParity_imagePacket (t : ℝ) : chainParity (imagePacket (L := L) t) = outPacket t := by
  rw [← chainParity_outPacket, chainParity_chainParity]

/-- ★★ **The state stays parity-even**: the messenger is reflected at the ends. -/
theorem chainParity_wallState (t : ℝ) : chainParity (wallState (L := L) t) = wallState t := by
  rw [wallState, chainParity_smul, chainParity_add, chainParity_outPacket, chainParity_imagePacket,
    add_comm]

omit [NeZero L] in
theorem image_spread : ∀ m ∈ imageWin,
    |2 * Real.pi * m / (2 * Real.pi * 10 ^ 13) - -4| ≤ 2 / 10 ^ 7 := by
  intro m hm
  rw [imageWin, Finset.mem_Ico] at hm
  have hm' : (-(4 * 10 ^ 13) - 1999999 : ℝ) ≤ m ∧ (m : ℝ) ≤ -(4 * 10 ^ 13) := by
    constructor <;> exact_mod_cast (by push_cast at hm; omega)
  rw [show 2 * Real.pi * m / (2 * Real.pi * 10 ^ 13) = m / 10 ^ 13 by field_simp, abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    nlinarith [hm'.1]
  · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]
    nlinarith [hm'.2]

omit [NeZero L] in
theorem vRel_image : vRel 1 3 (1 * -4) = -(4 / 5) := by
  rw [vRel, dispE, show (3 : ℝ) ^ 2 + (1 * -4) ^ 2 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

omit [NeZero L] in
theorem omega_image : 2 * Real.pi / (2 * Real.pi * 10 ^ 13) * vRel 1 3 (1 * -4) = -(8 / 10 ^ 14) := by
  rw [vRel_image]
  field_simp
  norm_num

section Wall

variable (hL : 10 ^ 19 ≤ L)
include hL

omit [NeZero L] in
theorem image_win : ∀ m ∈ imageWin,
    -(4 * 10 ^ 13) - 1999999 ≤ m ∧ m + 1 < -(4 * 10 ^ 13) - 1999999 + L := by
  intro m hm
  rw [imageWin, Finset.mem_Ico] at hm
  push_cast at hm
  constructor <;> omega

theorem outPacket_norm (t : ℝ) : chainInner (outPacket (L := L) t) (outPacket t) = 1 :=
  (dirac_packet_limit (L := L) (c := 1) (μ := 3) (P := 4) (D := 2 / 10 ^ 7) (p₀ := 4) one_pos
    (by norm_num) (by positivity) (by norm_num) (by positivity) (moving_win hL) moving_spread
    twinAmp (twin_norm hL _)).1 t

theorem imagePacket_norm (t : ℝ) : chainInner (imagePacket (L := L) t) (imagePacket t) = 1 :=
  (dirac_packet_limit (L := L) (c := 1) (μ := 3) (P := 4) (D := 2 / 10 ^ 7) (p₀ := -4) one_pos
    (by norm_num) (by positivity) (by norm_num) (by positivity) (image_win hL) image_spread
    twinAmp (twin_norm hL _)).1 t

/-- **The messenger and its image are orthogonal**: their momenta are opposite. -/
theorem chainInner_out_image (t : ℝ) :
    chainInner (outPacket (L := L) t) (imagePacket (L := L) t) = 0 := by
  rw [outPacket, imagePacket, ringPacket, ringPacket]
  refine chainInner_packet_packet _ _ (fun m hm m' hm' heq => ?_) _ _ t
  rw [Finset.mem_Ico] at hm
  rw [imageWin, Finset.mem_Ico] at hm'
  push_cast at hm hm'
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at heq
  obtain ⟨k, hk⟩ := heq
  have hLz : (10 ^ 19 : ℤ) ≤ L := by exact_mod_cast hL
  rcases lt_or_ge k 0 with h | h
  · nlinarith
  · nlinarith

theorem wallState_norm (t : ℝ) : chainInner (wallState (L := L) t) (wallState t) = 1 :=
  chainInner_pair (chainInner_out_image hL t) (outPacket_norm hL t) (imagePacket_norm hL t)

/-- **The messenger is within chord `1/20` of `e^{iΩt}`** but for `10⁻³` of its weight. -/
theorem out_tail {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    regionWeight (outPacket (L := L) t) (chordArc (exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (1 / 20))ᶜ
      ≤ 1 / 1000 := by
  have h := regionWeight_compl_chordArc_le (L := L) (c := 1) (μ := 3) (P := 4) (D := 2 / 10 ^ 7)
    (p₀ := 4) one_pos (by norm_num) (by positivity) (by norm_num) (by positivity) (moving_win hL)
    moving_spread twinAmp (twin_norm hL _) (z := exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)))
    (ρ := 1 / 20) (η := 0) (by norm_num) t (by rw [omega_twin, sub_self, norm_zero])
  have b := twin_budget (L := L) hL (μ := 3) le_rfl (4 * 10 ^ 13) (D := 2 / 10 ^ 7) (P := 4)
    (by positivity) le_rfl (by norm_num) le_rfl ht0 ht
  have hnn := regionWeight_nonneg (outPacket (L := L) t)
    (chordArc (exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (1 / 20))ᶜ
  unfold outPacket at hnn ⊢
  rw [sub_zero] at h
  nlinarith

/-- **The image is within chord `1/20` of `e^{−iΩt}`** but for `10⁻³` of its weight. -/
theorem image_tail {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    regionWeight (imagePacket (L := L) t)
      (chordArc (exp (I * ((-(8 / 10 ^ 14 * t) : ℝ) : ℂ))) (1 / 20))ᶜ ≤ 1 / 1000 := by
  have h := regionWeight_compl_chordArc_le (L := L) (c := 1) (μ := 3) (P := 4) (D := 2 / 10 ^ 7)
    (p₀ := -4) one_pos (by norm_num) (by positivity) (by norm_num) (by positivity) (image_win hL)
    image_spread twinAmp (twin_norm hL _) (z := exp (I * ((-(8 / 10 ^ 14 * t) : ℝ) : ℂ)))
    (ρ := 1 / 20) (η := 0) (by norm_num) t (by rw [omega_image, neg_mul, sub_self, norm_zero])
  have b := twin_budget (L := L) hL (μ := 3) le_rfl (-(4 * 10 ^ 13) - 1999999) (D := 2 / 10 ^ 7)
    (P := 4) (by positivity) le_rfl (by norm_num) le_rfl ht0 ht
  have hnn := regionWeight_nonneg (imagePacket (L := L) t)
    (chordArc (exp (I * ((-(8 / 10 ^ 14 * t) : ℝ) : ℂ))) (1 / 20))ᶜ
  unfold imagePacket imageWin at hnn ⊢
  unfold imageWin at h
  rw [sub_zero] at h
  nlinarith

/-- ★ **At a region the pair reaches, it has nearly all its weight**: if both predicted points are
within `3/20` of `w`, the pair has at least `1 − 2·10⁻³` on the chord-`1/5` arc around `w`. -/
theorem wall_near (w : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13)
    (h1 : ‖exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)) - w‖ ≤ 3 / 20)
    (h2 : ‖exp (I * ((-(8 / 10 ^ 14 * t) : ℝ) : ℂ)) - w‖ ≤ 3 / 20) :
    1 - 2 * (1 / 1000) ≤ regionWeight (wallState (L := L) t) (chordArc w (1 / 5)) := by
  refine le_regionWeight_pair (chainInner_out_image hL t) (outPacket_norm hL t)
    (imagePacket_norm hL t) _ (by norm_num) ?_ ?_
  · exact (regionWeight_mono _ (Finset.compl_subset_compl.2
      (chordArc_subset (z := exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (w := w) (ρ := 1 / 20)
        (σ := 1 / 5) (by linarith)))).trans (out_tail hL ht0 ht)
  · exact (regionWeight_mono _ (Finset.compl_subset_compl.2
      (chordArc_subset (z := exp (I * ((-(8 / 10 ^ 14 * t) : ℝ) : ℂ))) (w := w) (ρ := 1 / 20)
        (σ := 1 / 5) (by linarith)))).trans (image_tail hL ht0 ht)

/-- ★ **At a region the pair is far from, it has almost none**: if both predicted points are more
than `1/4` from `w`, the pair has at most `2·10⁻³` on the chord-`1/5` arc around `w`. -/
theorem wall_far (w : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13)
    (h1 : 1 / 4 < ‖exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)) - w‖)
    (h2 : 1 / 4 < ‖exp (I * ((-(8 / 10 ^ 14 * t) : ℝ) : ℂ)) - w‖) :
    regionWeight (wallState (L := L) t) (chordArc w (1 / 5)) ≤ 2 * (1 / 1000) := by
  refine regionWeight_pair_le _ (by norm_num) ?_ ?_
  · exact (regionWeight_mono _ (chordArc_subset_compl
      (z := exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (w := w) (ρ := 1 / 20) (σ := 1 / 5)
      (by linarith))).trans (out_tail hL ht0 ht)
  · exact (regionWeight_mono _ (chordArc_subset_compl
      (z := exp (I * ((-(8 / 10 ^ 14 * t) : ℝ) : ℂ))) (w := w) (ρ := 1 / 20) (σ := 1 / 5)
      (by linarith))).trans (image_tail hL ht0 ht)

theorem wall_le_one (A : Finset (ZMod L)) (t : ℝ) : regionWeight (wallState (L := L) t) A ≤ 1 := by
  have h := regionWeight_add_compl (wallState (L := L) t) A
  rw [wallState_norm hL, Complex.one_re] at h
  linarith [regionWeight_nonneg (wallState (L := L) t) Aᶜ]

end Wall

/-! ### The phases -/

section Phases

variable (hL : 10 ^ 19 ≤ L)
include hL

/-- **At `A` at the start**: for `0 ≤ t ≤ (3/20)·1.25·10¹³`. -/
theorem wallA_start {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3 / 20 * (125 * 10 ^ 11)) :
    1 - 2 * (1 / 1000) ≤ regionWeight (wallState (L := L) t) (chordArc 1 (1 / 5)) := by
  refine wall_near hL 1 ht0 (by nlinarith) (near_one 0 ?_) (near_one 0 ?_) <;>
    rw [abs_le] <;> push_cast <;> constructor <;> nlinarith

/-- **At `A` again after the round trip**: for `(2π − 3/20)·1.25·10¹³ ≤ t ≤ (2π + 7/100)·1.25·10¹³`. -/
theorem wallA_end {t : ℝ} (ht1 : (2 * Real.pi - 3 / 20) * (125 * 10 ^ 11) ≤ t)
    (ht2 : t ≤ (2 * Real.pi + 7 / 100) * (125 * 10 ^ 11)) :
    1 - 2 * (1 / 1000) ≤ regionWeight (wallState (L := L) t) (chordArc 1 (1 / 5)) := by
  have hπ := Real.pi_pos
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  refine wall_near hL 1 (by nlinarith) (by nlinarith) (near_one 1 ?_) (near_one (-1) ?_) <;>
    rw [abs_le] <;> push_cast <;> constructor <;> nlinarith

/-- **Away from `A`**: for `(13/50)·1.25·10¹³ ≤ t ≤ (2π − 13/50)·1.25·10¹³`. -/
theorem wallA_away {t : ℝ} (ht1 : 13 / 50 * (125 * 10 ^ 11) ≤ t)
    (ht2 : t ≤ (2 * Real.pi - 13 / 50) * (125 * 10 ^ 11)) :
    regionWeight (wallState (L := L) t) (chordArc 1 (1 / 5)) ≤ 2 * (1 / 1000) := by
  have hπ := Real.pi_pos
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hφ : 0 ≤ 8 / 10 ^ 14 * t := by nlinarith
  refine wall_far hL 1 (by nlinarith) (by nlinarith) (far_one ?_ ?_) (far_one ?_ ?_)
  · rw [abs_of_nonneg hφ]; nlinarith
  · rw [abs_of_nonneg hφ]; nlinarith
  · rw [abs_neg, abs_of_nonneg hφ]; nlinarith
  · rw [abs_neg, abs_of_nonneg hφ]; nlinarith

/-- **At the far end `B`**: for `(π − 3/20)·1.25·10¹³ ≤ t ≤ (π + 3/20)·1.25·10¹³`. -/
theorem wallB_near {t : ℝ} (ht1 : (Real.pi - 3 / 20) * (125 * 10 ^ 11) ≤ t)
    (ht2 : t ≤ (Real.pi + 3 / 20) * (125 * 10 ^ 11)) :
    1 - 2 * (1 / 1000) ≤ regionWeight (wallState (L := L) t) (chordArc (-1) (1 / 5)) := by
  have hπ := Real.pi_pos
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  refine wall_near hL (-1) (by nlinarith) (by nlinarith) (near_neg_one 0 ?_) (near_neg_one (-1) ?_)
    <;> rw [abs_le] <;> push_cast <;> constructor <;> nlinarith

/-- **Before the far end `B`**: for `0 ≤ t ≤ (π − 13/50)·1.25·10¹³`. -/
theorem wallB_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Real.pi - 13 / 50) * (125 * 10 ^ 11)) :
    regionWeight (wallState (L := L) t) (chordArc (-1) (1 / 5)) ≤ 2 * (1 / 1000) := by
  have hπ := Real.pi_pos
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  refine wall_far hL (-1) ht0 (by nlinarith) (far_neg_one ?_ ?_) (far_neg_one ?_ ?_)
  · rw [abs_of_nonpos (by nlinarith)]; nlinarith
  · rw [abs_of_nonpos (by nlinarith)]; nlinarith
  · rw [abs_of_nonpos (by nlinarith)]; nlinarith
  · rw [abs_of_nonpos (by nlinarith)]; nlinarith

end Phases

/-! ### The records -/

theorem chainProp_wallState (s : ℝ) :
    chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 s *ᵥ wallState 0
      = wallState s := by
  rw [wallState, wallState, Matrix.mulVec_smul, Matrix.mulVec_add, outPacket, imagePacket,
    outPacket, imagePacket, ringPacket, ringPacket, ringPacket, ringPacket, chainProp_packet,
    chainProp_packet]

theorem continuous_wallWeight (A : Finset (ZMod L)) :
    Continuous fun s => regionWeight (chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L))
      3 s *ᵥ wallState 0) A :=
  continuous_regionWeight_chainProp _ _ _ A

section Records

variable (hL : 10 ^ 19 ≤ L)
include hL

theorem emission_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1 / 10 * (125 * 10 ^ 11)) :
    1 * ∫ s in (0 : ℝ)..t, regionWeight (chainProp (L := L)
      (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 s *ᵥ wallState 0) (chordArc 1 (1 / 5))
      < 1 / 10 * (125 * 10 ^ 11) := by
  have h := integral_le_of_le_on (continuous_wallWeight (L := L) (chordArc 1 (1 / 5))) (ε := 1)
    ht0 le_rfl fun s _ _ => by
      rw [chainProp_wallState]
      exact wall_le_one hL _ s
  linarith

theorem emission_after :
    1 / 10 * (125 * 10 ^ 11) ≤ 1 * ∫ s in (0 : ℝ)..11 / 100 * (125 * 10 ^ 11),
      regionWeight (chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 s
        *ᵥ wallState 0) (chordArc 1 (1 / 5)) := by
  have h := le_integral_of_ge_on (continuous_wallWeight (L := L) (chordArc 1 (1 / 5)))
    (κ := 1 - 2 * (1 / 1000)) (tn := 0) (te := 3 / 20 * (125 * 10 ^ 11))
    (t := 11 / 100 * (125 * 10 ^ 11)) le_rfl (by norm_num) (by norm_num)
    (fun s _ => regionWeight_nonneg _ _) fun s hs1 hs2 => by
      rw [chainProp_wallState]
      exact wallA_start hL hs1 hs2
  have : (1 / 10 * (125 * 10 ^ 11) : ℝ) ≤ (1 - 2 * (1 / 1000)) * (11 / 100 * (125 * 10 ^ 11) - 0) := by
    norm_num
  rw [one_mul]
  exact this.trans h

theorem reception_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t < (Real.pi - 17 / 100) * (125 * 10 ^ 11)) :
    1 * ∫ s in (0 : ℝ)..t, regionWeight (chainProp (L := L)
      (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 s *ᵥ wallState 0) (chordArc (-1) (1 / 5))
      < 1 / 10 * (125 * 10 ^ 11) := by
  have hπ := Real.pi_pos
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hF := continuous_wallWeight (L := L) (chordArc (-1) (1 / 5))
  have hfar : ∀ s, 0 ≤ s → s ≤ (Real.pi - 13 / 50) * (125 * 10 ^ 11) →
      regionWeight (chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 s
        *ᵥ wallState 0) (chordArc (-1) (1 / 5)) ≤ 2 * (1 / 1000) := fun s hs0 hs => by
    rw [chainProp_wallState]
    exact wallB_before hL hs0 hs
  rw [one_mul]
  rcases le_total t ((Real.pi - 13 / 50) * (125 * 10 ^ 11)) with h | h
  · have h1 := integral_le_of_le_on hF ht0 h hfar
    nlinarith
  · have h1 := integral_le_of_le_on_then_one hF (by nlinarith) h hfar fun s => by
      rw [chainProp_wallState]
      exact wall_le_one hL _ s
    nlinarith

theorem reception_after :
    1 / 10 * (125 * 10 ^ 11) ≤ 1 * ∫ s in (0 : ℝ)..(Real.pi - 4 / 100) * (125 * 10 ^ 11),
      regionWeight (chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 s
        *ᵥ wallState 0) (chordArc (-1) (1 / 5)) := by
  have hπ := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h := le_integral_of_ge_on (continuous_wallWeight (L := L) (chordArc (-1) (1 / 5)))
    (κ := 1 - 2 * (1 / 1000)) (tn := (Real.pi - 3 / 20) * (125 * 10 ^ 11))
    (te := (Real.pi + 3 / 20) * (125 * 10 ^ 11)) (t := (Real.pi - 4 / 100) * (125 * 10 ^ 11))
    (by nlinarith) (by nlinarith) (by nlinarith) (fun s _ => regionWeight_nonneg _ _)
    fun s hs1 hs2 => by
      rw [chainProp_wallState]
      exact wallB_near hL hs1 hs2
  rw [one_mul]
  have : (1 / 10 * (125 * 10 ^ 11) : ℝ) ≤ (1 - 2 * (1 / 1000))
      * ((Real.pi - 4 / 100) * (125 * 10 ^ 11) - (Real.pi - 3 / 20) * (125 * 10 ^ 11)) := by
    nlinarith
  exact this.trans h

theorem wall_return_before {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < (2 * Real.pi - 19 / 100) * (125 * 10 ^ 11)) :
    1 * ∫ s in (0 : ℝ)..t, regionWeight (chainProp (L := L)
      (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 s *ᵥ wallState 0) (chordArc 1 (1 / 5))
      < 35 / 100 * (125 * 10 ^ 11) := by
  have hπ := Real.pi_pos
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h := integral_le_three (continuous_wallWeight (L := L) (chordArc 1 (1 / 5)))
    (fun s => by rw [chainProp_wallState]; exact wall_le_one hL _ s) (ε := 2 * (1 / 1000))
    (a := 13 / 50 * (125 * 10 ^ 11)) (b := (2 * Real.pi - 13 / 50) * (125 * 10 ^ 11))
    (by norm_num) (by norm_num) (by nlinarith) ht0 fun s hs1 hs2 => by
      rw [chainProp_wallState]
      exact wallA_away hL hs1 hs2
  have hm : max 0 (t - (2 * Real.pi - 13 / 50) * (125 * 10 ^ 11)) ≤ 7 / 100 * (125 * 10 ^ 11) :=
    max_le (by norm_num) (by nlinarith)
  rw [one_mul]
  nlinarith

theorem wall_return_after :
    35 / 100 * (125 * 10 ^ 11) ≤ 1 * ∫ s in (0 : ℝ)..(2 * Real.pi + 7 / 100) * (125 * 10 ^ 11),
      regionWeight (chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 s
        *ᵥ wallState 0) (chordArc 1 (1 / 5)) := by
  have hπ := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h := le_integral_two (continuous_wallWeight (L := L) (chordArc 1 (1 / 5)))
    (fun s _ => regionWeight_nonneg _ _) (κ := 1 - 2 * (1 / 1000)) (a := 3 / 20 * (125 * 10 ^ 11))
    (c := (2 * Real.pi - 3 / 20) * (125 * 10 ^ 11)) (t := (2 * Real.pi + 7 / 100) * (125 * 10 ^ 11))
    (by norm_num) (by nlinarith) (by nlinarith)
    (fun s hs1 hs2 => by
      rw [chainProp_wallState]
      exact wallA_start hL hs1 hs2)
    fun s hs1 hs2 => by
      rw [chainProp_wallState]
      exact wallA_end hL hs1 hs2
  rw [one_mul]
  have : (35 / 100 * (125 * 10 ^ 11) : ℝ) ≤ (1 - 2 * (1 / 1000)) * (3 / 20 * (125 * 10 ^ 11))
      + (1 - 2 * (1 / 1000)) * ((2 * Real.pi + 7 / 100) * (125 * 10 ^ 11)
        - (2 * Real.pi - 3 / 20) * (125 * 10 ^ 11)) := by nlinarith
  exact this.trans h

/-- ★★★ **The emission, recorded at `A`**: the register of the arc at `A` reaches `1.25·10¹²` within
`[1.25·10¹², 1.375·10¹²]`. -/
noncomputable def wallEmission {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (WholeArena L) ℕ L :=
  regionDetector (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 1 (1 / 10 * (125 * 10 ^ 11))
    (chordArc 1 (1 / 5)) (wallState 0) 0 rfl (τ₀ := 1 / 10 * (125 * 10 ^ 11))
    (τ₁ := 11 / 100 * (125 * 10 ^ 11)) (by norm_num) (by norm_num) hw zero_le_one
    (fun _ ht0 ht => emission_before hL ht0 ht) (emission_after hL)

/-- ★★★ **The reception, recorded at the far end `B`**: the register of the arc at the antipode
reaches `1.25·10¹²` within `[(π − 0.17), (π − 0.04)]·1.25·10¹³`. -/
noncomputable def wallReception {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (WholeArena L) ℕ L :=
  regionDetector (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 1 (1 / 10 * (125 * 10 ^ 11))
    (chordArc (-1) (1 / 5)) (wallState 0) 0 rfl (τ₀ := (Real.pi - 17 / 100) * (125 * 10 ^ 11))
    (τ₁ := (Real.pi - 4 / 100) * (125 * 10 ^ 11)) (by nlinarith [Real.pi_gt_three])
    (by nlinarith [Real.pi_gt_three]) hw zero_le_one
    (fun _ ht0 ht => reception_before hL ht0 ht) (reception_after hL)

/-- ★★★ **The return, recorded at `A`**: the same register of the arc at `A` reaches `4.375·10¹²`
within `[(2π − 0.19), (2π + 0.07)]·1.25·10¹³` — after the reflection at `B`. -/
noncomputable def wallReturn {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (WholeArena L) ℕ L :=
  regionDetector (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 1 (35 / 100 * (125 * 10 ^ 11))
    (chordArc 1 (1 / 5)) (wallState 0) 0 rfl (τ₀ := (2 * Real.pi - 19 / 100) * (125 * 10 ^ 11))
    (τ₁ := (2 * Real.pi + 7 / 100) * (125 * 10 ^ 11)) (by nlinarith [Real.pi_gt_three])
    (by nlinarith [Real.pi_gt_three]) hw zero_le_one
    (fun _ ht0 ht => wall_return_before hL ht0 ht) (wall_return_after hL)

theorem wallEmission_evolve {w : ℝ} (hw : 0 ≤ w) :
    (wallEmission (L := L) hL hw).evolve = wholeEvolve (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 1 :=
  rfl

theorem wallReception_evolve {w : ℝ} (hw : 0 ≤ w) :
    (wallReception (L := L) hL hw).evolve
      = wholeEvolve (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 1 :=
  rfl

theorem wallReturn_evolve {w : ℝ} (hw : 0 ≤ w) :
    (wallReturn (L := L) hL hw).evolve = wholeEvolve (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 1 :=
  rfl

theorem wallEmission_prep {w : ℝ} (hw : 0 ≤ w) :
    (wallEmission (L := L) hL hw).prep = (wallState 0, 0) := rfl

theorem wallReception_prep {w : ℝ} (hw : 0 ≤ w) :
    (wallReception (L := L) hL hw).prep = (wallState 0, 0) := rfl

theorem wallReturn_prep {w : ℝ} (hw : 0 ≤ w) :
    (wallReturn (L := L) hL hw).prep = (wallState 0, 0) := rfl

/-- ★★★ **A return leg on the Dirac chain** (BACKLOG #270). On a ring of length `ℓ = 2π·10¹³`
(`c = 1`), a messenger of velocity `4/5` leaves `A` (site `0`) together with its parity image — the
**parity-even state**, a state of the segment from `A` to the antipode `B` with **reflecting ends**:

* **the reflector**: parity commutes with the Dirac Hamiltonian, and the state stays parity-even,
  the messenger's image being its mirror packet;
* **one evolution**: the emission at `A`, the reception at `B` and the return at `A` are actual
  occurrences of the chain's evolution from the same preparation;
* **ordered**: emission written by `1.375·10¹²`, reception within `[(π − 0.17), (π − 0.04)]·1.25·10¹³`,
  return within `[(2π − 0.19), (2π + 0.07)]·1.25·10¹³`;
* **the round trip** — from the emission's write to the return's — lies within `0.3·1.25·10¹³` below
  `2 ℓ_AB / v`, `ℓ_AB = ℓ/2` and `v = 4/5` both ways. -/
theorem dirac_return {w : ℝ} (hw : 0 ≤ w) :
    let em := wallEmission (L := L) hL hw
    let rcv := wallReception (L := L) hL hw
    let ret := wallReturn (L := L) hL hw
    (rcv.evolve = em.evolve ∧ rcv.prep = em.prep ∧ ret.evolve = em.evolve ∧ ret.prep = em.prep)
    ∧ (∀ φ : ZMod L × Fin 2 → ℂ,
        diracHam (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 *ᵥ chainParity φ
          = chainParity (diracHam (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 *ᵥ φ))
    ∧ (∀ t, (em.evolve 0 t em.prep).1 = wallState t ∧ chainParity (wallState (L := L) t) = wallState t
        ∧ chainParity (outPacket (L := L) t) = imagePacket t)
    ∧ (em.writeStart = 1 / 10 * (125 * 10 ^ 11) ∧ em.writeEnd = 11 / 100 * (125 * 10 ^ 11)
      ∧ rcv.writeStart = (Real.pi - 17 / 100) * (125 * 10 ^ 11)
      ∧ rcv.writeEnd = (Real.pi - 4 / 100) * (125 * 10 ^ 11)
      ∧ ret.writeStart = (2 * Real.pi - 19 / 100) * (125 * 10 ^ 11)
      ∧ ret.writeEnd = (2 * Real.pi + 7 / 100) * (125 * 10 ^ 11))
    ∧ em.writeEnd < rcv.writeStart ∧ rcv.writeEnd < ret.writeStart
    ∧ 2 * (Real.pi * 10 ^ 13) / (4 / 5) - 3 / 10 * (125 * 10 ^ 11) ≤ ret.writeStart - em.writeEnd
    ∧ ret.writeEnd - em.writeStart ≤ 2 * (Real.pi * 10 ^ 13) / (4 / 5) := by
  intro em rcv ret
  have hπ := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  refine ⟨⟨(wallReception_evolve hL hw).trans (wallEmission_evolve hL hw).symm,
    (wallReception_prep hL hw).trans (wallEmission_prep hL hw).symm,
    (wallReturn_evolve hL hw).trans (wallEmission_evolve hL hw).symm,
    (wallReturn_prep hL hw).trans (wallEmission_prep hL hw).symm⟩, fun φ => diracHam_mulVec_chainParity _ _ φ,
    fun t => ⟨?_, chainParity_wallState t, chainParity_outPacket t⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [wallEmission_evolve, wallEmission_prep]
    show chainProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (t - 0) *ᵥ wallState 0 = _
    rw [sub_zero, chainProp_wallState]
  · show 11 / 100 * (125 * 10 ^ 11) < (Real.pi - 17 / 100) * (125 * 10 ^ 11)
    nlinarith
  · show (Real.pi - 4 / 100) * (125 * 10 ^ 11) < (2 * Real.pi - 19 / 100) * (125 * 10 ^ 11)
    nlinarith
  · show 2 * (Real.pi * 10 ^ 13) / (4 / 5) - 3 / 10 * (125 * 10 ^ 11)
      ≤ (2 * Real.pi - 19 / 100) * (125 * 10 ^ 11) - 11 / 100 * (125 * 10 ^ 11)
    nlinarith
  · show (2 * Real.pi + 7 / 100) * (125 * 10 ^ 11) - 1 / 10 * (125 * 10 ^ 11)
      ≤ 2 * (Real.pi * 10 ^ 13) / (4 / 5)
    nlinarith

end Records

end CSD.RecordLayer

end

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Probability.FeynmanKac
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# The Schrödinger group on `L²(E)` and Nelson's product formula

**Category:** 1-Mathlib (CSD-free; staged for upstream).

The real-time rung of the Feynman path integral (BACKLOG #36 (c) FC-5). The interacting
Schrödinger propagator `U(t) = e^{−it(H₀ + V)}` on `L²(ℝ, ℂ)` is the limit of alternating free
flights and potential kicks,

  `(U₀(t/n) · e^{−i(t/n)V})ⁿ ψ → U(t) ψ`   (★★ `nelson`),

Nelson's operator form of Feynman's finite-slice formula (E. Nelson, *Feynman integrals and the
Schrödinger equation*, J. Math. Phys. 5 (1964) 332; for a bounded potential it is Trotter's product
formula, and the free flights are Fresnel kernels the theorem never has to write). This is the
real-time twin of Feynman–Kac (`Probability/FeynmanKac.lean`): there the time slices carry the heat
kernel and the Wiener measure, here the unitary free group and unimodular phases.

## Design

* **The phase group** `phaseGroup hκ t = M_{e^{−itκ}}` of a real measurable symbol `κ`: a unitary
  one-parameter group of multiplication operators on `L²`. Its strong continuity is obtained from
  its *weak* continuity `⟪M_t f, f⟫ → ⟪f, f⟫` — a scalar dominated convergence with dominator
  `|f|²` — through the polarisation `‖M_t f − f‖² = 2‖f‖² − 2 Re ⟪M_t f, f⟫`; no dominated
  convergence in `L²` is needed.
* **The unitary group with dispersion relation `κ`**, `fourierGroup hκ t = 𝓕⁻¹ M_{e^{−itκ}} 𝓕`:
  the phase group conjugated by Mathlib's `L²` Fourier isometry `Lp.fourierTransformₗᵢ`. It is
  the group `e^{−itκ(D)}`, `D = −i d/dx`; `freeSchrodinger` is the Schrödinger case
  `κ(ξ) = 2π²ξ²`, the symbol of `H₀ = −½ d²/dx²` in Mathlib's convention
  `𝓕 f (ξ) = ∫ e^{−2πiξx} f(x) dx` (units `ℏ = m = 1`). No generator is written: `e^{−itH₀}` is
  *defined* by its Fourier multiplier, as the spectral theorem would define it.
* **The interacting propagator** `schrodinger hκ VL t`: the Dyson series of
  `BoundedPerturbation.lean` around the free group with interaction `−i M_V`, `V ∈ L^∞`, for
  `t ≥ 0`; a semigroup, strongly continuous, satisfying Duhamel's equation, all inherited.
* ★ `exp_eq_potential` — the exponential of a multiplication operator is multiplication by the
  exponential, for a bounded complex multiplier (the real-time counterpart of
  `FeynmanKac.exp_smul_neg_potential`): `exp (h · (−i M_V)) = M_{e^{−ihV}}`, the potential kick.
* ★★ `nelson` — **Nelson's theorem**: `(U_κ(t/n) · M_{e^{−i(t/n)V}})ⁿ ψ → e^{−it(κ(D)+V)} ψ`,
  Trotter's formula of `BoundedPerturbation.lean` with the kick identified; `nelson_freeSchrodinger`
  is the Schrödinger case. Both factors are phase groups — the kinetic one in momentum space, the
  potential one in position space — which is exactly Feynman's alternation of free propagation and
  `e^{−iV Δt}`.
* ★ `norm_schrodinger_apply` — **probability is conserved**: the propagator of a real bounded
  potential is an isometry of `L²`, inherited from its unitary Trotter approximants through
  Nelson's limit.
* ★★ `exists_linearIsometryEquiv_schrodinger` — **the propagator is unitary**: the propagator of
  the reversed dynamics `e^{−it(−κ(D) − V)}` is a two-sided inverse
  (`schrodinger_mul_schrodinger_neg`, `schrodinger_neg_mul_schrodinger`). The inverse of the
  forward Trotter approximant `(U M)ⁿ` is `M⁻¹ (U⁻¹ M⁻¹)ⁿ M`, a conjugate of the reversed
  approximant (`mul_pow_conj`); both sides converge strongly by Nelson, and `χ = Xₙ Xₙ⁻¹ χ` passes
  to the limit. With the isometry, a linear isometric bijection of `L²`.

**The wider picture.** With `HeatSemigroup.lean` and `FeynmanKac.lean` the corpus now holds both
signatures of the same dynamics: in imaginary time `e^{−t(H₀+V)}` is the Trotter limit of heat
steps and is the Wiener functional; in real time `e^{−it(H₀+V)}` is the Trotter limit of unitary
free flights and phase kicks. The Schrödinger picture (the propagator as the solution of Duhamel's
equation), the Heisenberg picture (`DynamicalLocality.lean`, the flow on observables) and the
Feynman picture (the time-sliced product) are each theorems about one object.

## Honest scope

⚠️ **Bounded potentials, `t ≥ 0`.** The space is any finite-dimensional real inner product space
`E` — `ℝᵈ` in particular (BACKLOG #41, 2026-09-20); the Euclidean chain lives on
`EuclideanSpace ℝ ι`, so Feynman–Kac and Nelson meet on the same `L²(ℝᵈ)`. Nelson's original
theorem also covers a class of unbounded potentials through Trotter's formula for self-adjoint
generators; only the bounded case is stated. The kernel (Fresnel-integral) form of the finite-slice
formula is FC-5′ (XL). The explicit action of `freeSchrodinger` on Schwartz functions — the free
Gaussian packet spreading into a Gaussian of complex variance, through
`SchwartzMap.toLp_fourierInv_eq` — and its identification with the differential operator
`−½ d²/dx²` on Schwartz functions are not stated (FC-5″, S–M).

References: E. Nelson, J. Math. Phys. 5 (1964) 332; M. Reed, B. Simon, *Methods of Modern
Mathematical Physics* I §VIII.8 and II §X.11; `Analysis/Semigroup/BoundedPerturbation.lean` (FC-1);
`Probability/FeynmanKac.lean` (FC-4); `specs/feynman-continuum-scoping.md` (FC-5);
`specs/BACKLOG.md` #36(c); `specs/future-work.md` FP-1.
-/

@[expose] public section

open scoped ENNReal NNReal Topology Nat ComplexConjugate
open MeasureTheory Filter HeatSemigroup NormedSpace

namespace SchrodingerGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `L²(E, ℂ)` with Lebesgue measure, `E` a finite-dimensional inner product space. -/
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-! ### Multiplication operators -/

/-- The powers of a multiplication operator, pointwise. -/
theorem pow_apply_ae_eq {m : E → ℂ} {A : L2 →L[ℂ] L2}
    (hA : ∀ f : L2, (A f : E → ℂ) =ᵐ[volume] fun x => m x * f x) (f : L2) :
    ∀ n : ℕ, ((A ^ n) f : E → ℂ) =ᵐ[volume] fun x => m x ^ n * f x := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, one_apply_eq_self]
    exact Eventually.of_forall fun x => by simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [hA ((A ^ n) f), ih] with x h1 h2
    rw [h1, h2]
    ring

set_option maxHeartbeats 800000 in
/-- ★ **The exponential of a multiplication operator is multiplication by the exponential**,
complex form: if `A` acts on `L²` as multiplication by a bounded measurable `m`, then `exp A` acts
as multiplication by `e^{m}`. The operator series applied to `f` has partial sums equal almost
everywhere to the pointwise partial sums; the `L²` limit and the pointwise (dominated) limit are
identified on every finite-measure set. -/
theorem exp_eq_potential {m : E → ℂ} (hm : Measurable m) {C : ℝ} (hC : ∀ x, ‖m x‖ ≤ C)
    {A : L2 →L[ℂ] L2} (hA : ∀ f : L2, (A f : E → ℂ) =ᵐ[volume] fun x => m x * f x)
    {M : Lp ℂ ∞ (volume : Measure E)} (hM : (M : E → ℂ) =ᵐ[volume] fun x => Complex.exp (m x)) :
    exp A = potential M := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  -- the series in the operator algebra, applied to `f`
  have hsum := (ContinuousLinearMap.apply ℂ L2 f).hasSum (exp_series_hasSum_exp' (𝕂 := ℝ) A)
  have hlim := hsum.tendsto_sum_nat
  simp only [ContinuousLinearMap.apply_apply] at hlim
  -- the partial sums, pointwise
  have hpartial : ∀ N : ℕ,
      ((∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹ • A ^ n) f : L2) : E → ℂ)
        =ᵐ[volume] fun x => (∑ n ∈ Finset.range N, m x ^ n / n !) * f x := by
    intro N
    have hterm : ∀ n : ℕ, ((((n ! : ℝ)⁻¹ • A ^ n) f : L2) : E → ℂ)
        =ᵐ[volume] fun x => m x ^ n / n ! * f x := by
      intro n
      rw [smul_apply]
      filter_upwards [Lp.coeFn_smul ((n ! : ℝ)⁻¹) ((A ^ n) f), pow_apply_ae_eq hA f n] with x h1 h2
      rw [h1, Pi.smul_apply, h2]
      simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
      rw [div_eq_mul_inv]
      ring
    have hsumN := FeynmanKac.coeFn_sum_range (fun n => ((n ! : ℝ)⁻¹ • A ^ n) f) N
    filter_upwards [hsumN, ae_all_iff.mpr hterm] with x hx hx'
    rw [hx, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => hx' n
  -- identification on every finite-measure set
  have hbound : ∀ N x, ‖(∑ n ∈ Finset.range N, m x ^ n / n !) * f x‖ ≤ Real.exp C * ‖f x‖ := by
    intro N x
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact le_trans (FeynmanKac.norm_sum_pow_div_factorial_le _ N) (Real.exp_le_exp.mpr (hC x))
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hμs => ?_) (fun s _ hμs => ?_)
    (fun s hs hμs => ?_)
  · have : IsFiniteMeasure ((volume : Measure E).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    exact ((Lp.memLp (exp A f)).restrict s).integrable one_le_two
  · have : IsFiniteMeasure ((volume : Measure E).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    exact ((Lp.memLp (potential M f)).restrict s).integrable one_le_two
  · have : IsFiniteMeasure ((volume : Measure E).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    have hfint : Integrable (fun x => Real.exp C * ‖f x‖) ((volume : Measure E).restrict s) :=
      (((Lp.memLp f).restrict s).integrable one_le_two).norm.const_mul _
    -- the set integrals of the partial sums converge to both sides
    have h1 : Tendsto (fun N => ∫ x in s, ((∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹ • A ^ n) f : L2) x))
        atTop (𝓝 (∫ x in s, exp A f x)) := by
      have hcont : Continuous fun g : L2 => ∫ x in s, g x := by
        have : (fun g : L2 => ∫ x in s, g x)
            = fun g => inner ℂ (indicatorConstLp 2 hs hμs.ne (1 : ℂ)) g := by
          funext g
          rw [L2.inner_indicatorConstLp_one hs hμs.ne]
        rw [this]
        exact continuous_const.inner continuous_id
      exact (hcont.tendsto _).comp hlim
    have h2 : Tendsto (fun N => ∫ x in s, ((∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹ • A ^ n) f : L2) x))
        atTop (𝓝 (∫ x in s, Complex.exp (m x) * f x)) := by
      have hrw : ∀ N, ∫ x in s, ((∑ n ∈ Finset.range N, ((n ! : ℝ)⁻¹ • A ^ n) f : L2) x)
          = ∫ x in s, (∑ n ∈ Finset.range N, m x ^ n / n !) * f x :=
        fun N => integral_congr_ae (ae_restrict_of_ae (hpartial N))
      simp_rw [hrw]
      refine tendsto_integral_filter_of_dominated_convergence (fun x => Real.exp C * ‖f x‖)
        (Eventually.of_forall fun N => ?_)
        (Eventually.of_forall fun N => Eventually.of_forall fun x => hbound N x)
        hfint (Eventually.of_forall fun x => ?_)
      · have hsm : Measurable fun x : E => ∑ n ∈ Finset.range N, m x ^ n / (n ! : ℂ) :=
          Finset.measurable_sum _ fun n _ => (hm.pow_const n).div_const _
        exact hsm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).restrict
      · refine Tendsto.mul_const _ ?_
        rw [Complex.exp_eq_exp_ℂ]
        exact (expSeries_div_hasSum_exp (m x)).tendsto_sum_nat
    rw [tendsto_nhds_unique h1 h2]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [coeFn_potential M f, hM] with x hx hx'
    rw [hx, hx']

/-- A multiplier bounded by one is a contraction of `L²`. -/
theorem norm_potential_apply_le {V : Lp ℂ ∞ (volume : Measure E)}
    (hV : ∀ᵐ x ∂(volume : Measure E), ‖V x‖ ≤ 1) (f : L2) : ‖potential V f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_ae ?_)
  filter_upwards [coeFn_potential V f, hV] with x h1 h2
  rw [h1, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) h2

/-- A unimodular multiplier is an isometry of `L²`. -/
theorem norm_potential_apply_eq {V : Lp ℂ ∞ (volume : Measure E)}
    (hV : ∀ᵐ x ∂(volume : Measure E), ‖V x‖ = 1) (f : L2) : ‖potential V f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards [coeFn_potential V f, hV] with x h1 h2
  rw [h1, norm_mul, h2, one_mul]

/-- A power of an isometry is an isometry. -/
theorem norm_pow_apply_eq {T : L2 →L[ℂ] L2} (hT : ∀ ψ, ‖T ψ‖ = ‖ψ‖) (n : ℕ) (ψ : L2) :
    ‖(T ^ n) ψ‖ = ‖ψ‖ := by
  induction n with
  | zero => rw [pow_zero, one_apply_eq_self]
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, hT, ih]

/-! ### The phase group `e^{−itκ}` of a real symbol -/

/-- The phase `e^{−itκ(ξ)}`. -/
noncomputable def phaseFun (κ : E → ℝ) (t : ℝ) (ξ : E) : ℂ :=
  Complex.exp ((-(t * κ ξ) : ℝ) * Complex.I)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem norm_phaseFun (κ : E → ℝ) (t : ℝ) (ξ : E) : ‖phaseFun κ t ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem phaseFun_zero (κ : E → ℝ) (ξ : E) : phaseFun κ 0 ξ = 1 := by
  simp [phaseFun]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem phaseFun_add (κ : E → ℝ) (s t : ℝ) (ξ : E) :
    phaseFun κ (s + t) ξ = phaseFun κ s ξ * phaseFun κ t ξ := by
  rw [phaseFun, phaseFun, phaseFun, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem continuous_phaseFun (κ : E → ℝ) (ξ : E) : Continuous fun t => phaseFun κ t ξ := by
  unfold phaseFun
  fun_prop

/-- Mathlib's `L²` Fourier transform on `ℝ`, as a linear isometry equivalence of `L2`. -/
noncomputable def fourierL2 : L2 ≃ₗᵢ[ℂ] L2 := Lp.fourierTransformₗᵢ E ℂ

variable {κ : E → ℝ} (hκ : Measurable κ)
include hκ

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
theorem measurable_phaseFun (t : ℝ) : Measurable (phaseFun κ t) := by
  unfold phaseFun
  exact Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp (measurable_const.mul hκ).neg).mul measurable_const)

theorem memLp_phaseFun (t : ℝ) : MemLp (phaseFun κ t) ∞ volume :=
  memLp_top_of_bound (measurable_phaseFun hκ t).aestronglyMeasurable 1
    (Eventually.of_forall fun ξ => (norm_phaseFun κ t ξ).le)

/-- The `L^∞` class of the phase `e^{−itκ}`. -/
noncomputable def phase (t : ℝ) : Lp ℂ ∞ (volume : Measure E) := (memLp_phaseFun hκ t).toLp _

theorem coeFn_phase (t : ℝ) : (phase hκ t : E → ℂ) =ᵐ[volume] phaseFun κ t :=
  MemLp.coeFn_toLp _

/-- **The phase group** `M_t = M_{e^{−itκ}}` on `L²`, multiplication by the unimodular phase. -/
noncomputable def phaseGroup (t : ℝ) : L2 →L[ℂ] L2 := potential (phase hκ t)

theorem coeFn_phaseGroup (t : ℝ) (f : L2) :
    (phaseGroup hκ t f : E → ℂ) =ᵐ[volume] fun x => phaseFun κ t x * f x := by
  filter_upwards [coeFn_potential (phase hκ t) f, coeFn_phase hκ t] with x h1 h2
  rw [phaseGroup, h1, h2]

theorem phaseGroup_zero : phaseGroup hκ 0 = 1 :=
  ContinuousLinearMap.ext fun f => Lp.ext <| by
    filter_upwards [coeFn_phaseGroup hκ 0 f] with x hx
    rw [hx, phaseFun_zero, one_mul, one_apply_eq_self]

/-- The phase group is a group. -/
theorem phaseGroup_add (s t : ℝ) : phaseGroup hκ (s + t) = phaseGroup hκ s * phaseGroup hκ t :=
  ContinuousLinearMap.ext fun f => Lp.ext <| by
    rw [mul_apply_eq_comp]
    filter_upwards [coeFn_phaseGroup hκ (s + t) f, coeFn_phaseGroup hκ s (phaseGroup hκ t f),
      coeFn_phaseGroup hκ t f] with x h1 h2 h3
    rw [h1, h2, h3, phaseFun_add]
    ring

theorem phaseGroup_mul_neg (s : ℝ) : phaseGroup hκ s * phaseGroup hκ (-s) = 1 := by
  rw [← phaseGroup_add, add_neg_cancel, phaseGroup_zero]

theorem phaseGroup_neg_mul (s : ℝ) : phaseGroup hκ (-s) * phaseGroup hκ s = 1 := by
  rw [← phaseGroup_add, neg_add_cancel, phaseGroup_zero]

/-- The phase group is unitary: an isometry of `L²`. -/
theorem norm_phaseGroup_apply (t : ℝ) (f : L2) : ‖phaseGroup hκ t f‖ = ‖f‖ :=
  norm_potential_apply_eq
    (by filter_upwards [coeFn_phase hκ t] with x hx; rw [hx, norm_phaseFun]) f

theorem norm_phaseGroup_le (t : ℝ) : ‖phaseGroup hκ t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [norm_phaseGroup_apply, one_mul]

/-- `⟪M_t f, f⟫ = ∫ conj (e^{−itκ}) |f|²`. -/
theorem inner_phaseGroup_apply (t : ℝ) (f : L2) :
    inner ℂ (phaseGroup hκ t f) f = ∫ x, conj (phaseFun κ t x) * inner ℂ (f x) (f x) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_phaseGroup hκ t f] with x hx
  rw [hx, RCLike.inner_apply', RCLike.inner_apply', map_mul]
  ring

/-- **Weak continuity** of the phase group at `t = 0`: a scalar dominated convergence with the
integrable dominator `|f|²`. -/
theorem tendsto_inner_phaseGroup (f : L2) :
    Tendsto (fun t => inner ℂ (phaseGroup hκ t f) f) (𝓝 0) (𝓝 (inner ℂ f f)) := by
  simp_rw [inner_phaseGroup_apply hκ]
  rw [L2.inner_def]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖ ^ 2)
    (Eventually.of_forall fun t => ?_)
    (Eventually.of_forall fun t => Eventually.of_forall fun x => ?_) ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((Complex.continuous_conj.measurable.comp (measurable_phaseFun hκ t)).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable f))
  · rw [norm_mul, Complex.norm_conj, norm_phaseFun, one_mul, inner_self_eq_norm_sq_to_K, norm_pow,
      RCLike.norm_ofReal, abs_norm]
  · exact_mod_cast (Lp.memLp f).integrable_norm_pow (p := 2) two_ne_zero
  · have h1 : Tendsto (fun t => conj (phaseFun κ t x)) (𝓝 0) (𝓝 (conj (phaseFun κ 0 x))) :=
      (Complex.continuous_conj.tendsto _).comp ((continuous_phaseFun κ x).tendsto 0)
    rw [phaseFun_zero, map_one] at h1
    convert h1.mul_const (inner ℂ (f x) (f x)) using 2
    rw [one_mul]

/-- ★ **Strong continuity** of the phase group at `t = 0`, from weak continuity and the isometry:
`‖M_t f − f‖² = 2‖f‖² − 2 Re ⟪M_t f, f⟫ → 0`. -/
theorem tendsto_phaseGroup_apply_zero (f : L2) :
    Tendsto (fun t => phaseGroup hκ t f) (𝓝 0) (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun t => ‖phaseGroup hκ t f - f‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have h : ∀ t, ‖phaseGroup hκ t f - f‖ ^ 2
        = 2 * ‖f‖ ^ 2 - 2 * RCLike.re (inner ℂ (phaseGroup hκ t f) f) := by
      intro t
      rw [norm_sub_sq (𝕜 := ℂ), norm_phaseGroup_apply]
      ring
    simp_rw [h]
    have h2 : Tendsto (fun t => RCLike.re (inner ℂ (phaseGroup hκ t f) f)) (𝓝 0)
        (𝓝 (RCLike.re (inner ℂ f f))) :=
      (RCLike.continuous_re.tendsto _).comp (tendsto_inner_phaseGroup hκ f)
    have h3 := (tendsto_const_nhds (x := 2 * ‖f‖ ^ 2)).sub (h2.const_mul 2)
    rw [inner_self_eq_norm_sq, sub_self] at h3
    exact h3
  have := hsq.sqrt
  rw [Real.sqrt_zero] at this
  exact this.congr fun t => Real.sqrt_sq (norm_nonneg _)

/-- ★ The phase group is strongly continuous. -/
theorem continuous_phaseGroup_apply (f : L2) : Continuous fun t => phaseGroup hκ t f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hsub : Tendsto (fun t => t - t₀) (𝓝 t₀) (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr tendsto_id
  have h1 : Tendsto (fun t => phaseGroup hκ t₀ (phaseGroup hκ (t - t₀) f)) (𝓝 t₀)
      (𝓝 (phaseGroup hκ t₀ f)) :=
    ((phaseGroup hκ t₀).continuous.tendsto f).comp
      ((tendsto_phaseGroup_apply_zero hκ f).comp hsub)
  refine h1.congr fun t => ?_
  rw [← mul_apply_eq_comp, ← phaseGroup_add, add_sub_cancel]

/-! ### The unitary group of a dispersion relation -/

/-- **The unitary group with dispersion relation `κ`**, `U_κ(t) = 𝓕⁻¹ M_{e^{−itκ}} 𝓕 = e^{−itκ(D)}`:
the phase group conjugated by the `L²` Fourier isometry. -/
noncomputable def fourierGroup (t : ℝ) : L2 →L[ℂ] L2 :=
  ((fourierL2 (E := E)).symm.toContinuousLinearEquiv : L2 →L[ℂ] L2) ∘L phaseGroup hκ t
    ∘L ((fourierL2 (E := E)).toContinuousLinearEquiv : L2 →L[ℂ] L2)

theorem fourierGroup_apply (t : ℝ) (f : L2) :
    fourierGroup hκ t f = fourierL2.symm (phaseGroup hκ t (fourierL2 f)) := rfl

theorem fourierGroup_zero : fourierGroup hκ 0 = 1 :=
  ContinuousLinearMap.ext fun f => by
    rw [fourierGroup_apply, phaseGroup_zero, one_apply_eq_self, fourierL2.symm_apply_apply,
      one_apply_eq_self]

/-- The group law `U_κ(s + t) = U_κ(s) U_κ(t)`. -/
theorem fourierGroup_add (s t : ℝ) :
    fourierGroup hκ (s + t) = fourierGroup hκ s * fourierGroup hκ t :=
  ContinuousLinearMap.ext fun f => by
    rw [mul_apply_eq_comp, fourierGroup_apply, fourierGroup_apply, fourierGroup_apply,
      fourierL2.apply_symm_apply, phaseGroup_add, mul_apply_eq_comp]

theorem fourierGroup_mul_neg (s : ℝ) : fourierGroup hκ s * fourierGroup hκ (-s) = 1 := by
  rw [← fourierGroup_add, add_neg_cancel, fourierGroup_zero]

theorem fourierGroup_neg_mul (s : ℝ) : fourierGroup hκ (-s) * fourierGroup hκ s = 1 := by
  rw [← fourierGroup_add, neg_add_cancel, fourierGroup_zero]

/-- `U_κ(t)` is unitary: an isometry of `L²`. -/
theorem norm_fourierGroup_apply (t : ℝ) (f : L2) : ‖fourierGroup hκ t f‖ = ‖f‖ := by
  rw [fourierGroup_apply, LinearIsometryEquiv.norm_map, norm_phaseGroup_apply,
    LinearIsometryEquiv.norm_map]

theorem norm_fourierGroup_le (t : ℝ) : ‖fourierGroup hκ t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [norm_fourierGroup_apply, one_mul]

/-- ★ `U_κ` is strongly continuous. -/
theorem continuous_fourierGroup_apply (f : L2) : Continuous fun t => fourierGroup hκ t f := by
  simp_rw [fourierGroup_apply]
  exact fourierL2.symm.continuous.comp (continuous_phaseGroup_apply hκ (fourierL2 f))

/-- ★★ The unitary group `U_κ`, extended by the identity to `t < 0`, is a strongly continuous
contraction semigroup in the sense of `BoundedPerturbation.lean`: the Dyson series, the Duhamel
equation and the Trotter product formula apply to it. -/
theorem isContractionSemigroup_fourierGroup :
    IsContractionSemigroup fun t => if 0 ≤ t then fourierGroup hκ t else 1 :=
  IsContractionSemigroup.of_group _ (fourierGroup_zero hκ) (fourierGroup_add hκ)
    (norm_fourierGroup_le hκ) (continuous_fourierGroup_apply hκ)

/-! ### The interacting propagator and Nelson's formula -/

/-- **The interacting propagator** `U(t) = e^{−it(κ(D) + V)}` for a bounded potential `V ∈ L^∞`:
the Dyson series of `BoundedPerturbation.lean` around the free group `U_κ` with interaction
`−i M_V`, for `t ≥ 0` (the identity for `t < 0`). -/
noncomputable def schrodinger (VL : Lp ℂ ∞ (volume : Measure E)) (t : ℝ) : L2 →L[ℂ] L2 :=
  (isContractionSemigroup_fourierGroup hκ).perturbed (-(Complex.I • potential VL)) t

theorem schrodinger_apply (VL : Lp ℂ ∞ (volume : Measure E)) (t : ℝ) (ψ : L2) :
    schrodinger hκ VL t ψ = ContractionSemigroup.dysonSum
      (fun t => if 0 ≤ t then fourierGroup hκ t else 1) (-(Complex.I • potential VL)) t ψ :=
  rfl

theorem schrodinger_zero (VL : Lp ℂ ∞ (volume : Measure E)) : schrodinger hκ VL 0 = 1 :=
  ContractionSemigroup.perturbed_zero _ _

/-- The propagator is a semigroup: `U(t + s) = U(t) U(s)` for `s, t ≥ 0`. -/
theorem schrodinger_add (VL : Lp ℂ ∞ (volume : Measure E)) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    schrodinger hκ VL (t + s) = schrodinger hκ VL t * schrodinger hκ VL s :=
  ContractionSemigroup.perturbed_add _ _ hs ht

theorem continuous_schrodinger_apply (VL : Lp ℂ ∞ (volume : Measure E)) (ψ : L2) :
    Continuous fun t => schrodinger hκ VL t ψ :=
  ContractionSemigroup.continuous_perturbed_apply _ _ ψ

variable {V : E → ℝ} (hVm : Measurable V) {CV : ℝ} (hCV : ∀ x, |V x| ≤ CV)
  {VL : Lp ℂ ∞ (volume : Measure E)}
include hVm hCV

/-- ★ **The potential kick**: the Trotter step of the propagator is a free flight followed by the
phase `e^{−ihV}`, `U_κ(h) · exp (h · (−i M_V)) = U_κ(h) · M_{e^{−ihV}}` for `h ≥ 0`. -/
theorem trotterStep_eq (hVL : (VL : E → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {h : ℝ} (hh : 0 ≤ h) :
    ContractionSemigroup.trotterStep (fun t => if 0 ≤ t then fourierGroup hκ t else 1)
        (-(Complex.I • potential VL)) h
      = fourierGroup hκ h * phaseGroup hVm h := by
  rw [ContractionSemigroup.trotterStep, if_pos hh]
  congr 1
  refine exp_eq_potential (m := fun x => ((-(h * V x) : ℝ) : ℂ) * Complex.I) ?_ (C := |h| * CV)
    ?_ ?_ (coeFn_phase hVm h)
  · exact (Complex.measurable_ofReal.comp (measurable_const.mul hVm).neg).mul measurable_const
  · intro x
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul]
    gcongr
    exact hCV x
  · intro f
    rw [smul_apply, neg_apply, smul_apply]
    -- the real action on `L²` is the restriction of the complex one
    show (((h : ℂ) • -(Complex.I • potential VL f) : L2) : E → ℂ) =ᵐ[volume] _
    filter_upwards [Lp.coeFn_smul (h : ℂ) (-(Complex.I • potential VL f)),
      Lp.coeFn_neg (Complex.I • potential VL f), Lp.coeFn_smul Complex.I (potential VL f),
      coeFn_potential VL f, hVL] with x h1 h2 h3 h4 h5
    rw [h1, Pi.smul_apply, h2, Pi.neg_apply, h3, Pi.smul_apply, h4, h5]
    simp only [smul_eq_mul]
    push_cast
    ring

/-- ★★ **Nelson's theorem** — Trotter's product formula for the Schrödinger propagator. For a
bounded real potential `V`, the interacting propagator is the limit of alternating free flights and
potential kicks,

  `(U_κ(t/n) · M_{e^{−i(t/n)V}})ⁿ ψ → e^{−it(κ(D) + V)} ψ`  in `L²`, `t ≥ 0`.

With `U_κ(t/n) = 𝓕⁻¹ e^{−i(t/n)κ} 𝓕`, the left side is Feynman's finite-slice formula in operator
form: the momentum-space phase of the kinetic term alternating with the position-space phase of the
potential. -/
theorem nelson (hVL : (VL : E → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {t : ℝ} (ht : 0 ≤ t) (ψ : L2) :
    Tendsto (fun n : ℕ => ((fourierGroup hκ (t / n) * phaseGroup hVm (t / n)) ^ n) ψ) atTop
      (𝓝 (schrodinger hκ VL t ψ)) := by
  have h := ContractionSemigroup.tendsto_trotterStep_pow_apply (-(Complex.I • potential VL))
    (isContractionSemigroup_fourierGroup hκ) ht ψ
  rw [schrodinger_apply]
  refine h.congr' (Eventually.of_forall fun n => ?_)
  rw [trotterStep_eq hκ hVm hCV hVL (div_nonneg ht n.cast_nonneg)]

/-- ★ **Probability is conserved**: the propagator of a real bounded potential is an isometry of
`L²`, `‖U(t) ψ‖ = ‖ψ‖`, inherited from its unitary Trotter approximants through Nelson's limit. -/
theorem norm_schrodinger_apply (hVL : (VL : E → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {t : ℝ}
    (ht : 0 ≤ t) (ψ : L2) : ‖schrodinger hκ VL t ψ‖ = ‖ψ‖ := by
  refine tendsto_nhds_unique (nelson hκ hVm hCV hVL ht ψ).norm
    (tendsto_const_nhds.congr fun n => ?_)
  refine (norm_pow_apply_eq (fun g => ?_) n ψ).symm
  rw [mul_apply_eq_comp, norm_fourierGroup_apply, norm_phaseGroup_apply]

end SchrodingerGroup

namespace SchrodingerGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The free Schrödinger group -/

/-- `L²(E, ℂ)` with Lebesgue measure. -/
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The free symbol `2π²‖ξ‖²`: the Fourier symbol of `H₀ = −½ Δ` in Mathlib's convention
`𝓕 f (ξ) = ∫ e^{−2πi⟪ξ,x⟫} f(x) dx` (units `ℏ = m = 1`). -/
noncomputable def freeSymbol (ξ : E) : ℝ := 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_freeSymbol : Measurable (freeSymbol (E := E)) := by
  unfold freeSymbol
  fun_prop

/-- **The free Schrödinger group** `e^{−itH₀}`, `H₀ = −½ d²/dx²`, defined through its Fourier
multiplier `e^{−2π²itξ²}`: `fourierGroup` with the free symbol. -/
noncomputable def freeSchrodinger (t : ℝ) : L2 →L[ℂ] L2 :=
  fourierGroup (measurable_freeSymbol (E := E)) t

/-- ★★ **Nelson's theorem for the Schrödinger equation**: for a bounded real potential `V`,
`(e^{−i(t/n)H₀} · e^{−i(t/n)V})ⁿ ψ → e^{−it(H₀ + V)} ψ` in `L²(E)`, `H₀ = −½ Δ`. -/
theorem nelson_freeSchrodinger {V : E → ℝ} (hVm : Measurable V) {CV : ℝ} (hCV : ∀ x, |V x| ≤ CV)
    {VL : Lp ℂ ∞ (volume : Measure E)} (hVL : (VL : E → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {t : ℝ}
    (ht : 0 ≤ t) (ψ : L2) :
    Tendsto (fun n : ℕ => ((freeSchrodinger (E := E) (t / n) * phaseGroup hVm (t / n)) ^ n) ψ) atTop
      (𝓝 (schrodinger measurable_freeSymbol VL t ψ)) :=
  nelson measurable_freeSymbol hVm hCV hVL ht ψ


/-! ### Unitarity: the reversed dynamics is the inverse -/

/-- In a monoid, `(c a)ⁿ = c (a c)ⁿ d` when `c d = d c = 1`. -/
theorem mul_pow_conj {M : Type*} [Monoid M] {a c d : M} (hcd : c * d = 1) (hdc : d * c = 1)
    (n : ℕ) : (c * a) ^ n = c * (a * c) ^ n * d := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one, hcd]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc d c a, hdc, one_mul, hcd, mul_one]

/-- Negating the symbol reverses the phase group: `M^{−κ}_s = M^{κ}_{−s}`. -/
theorem phaseGroup_of_neg {κ₁ κ₂ : E → ℝ} (hκ₁ : Measurable κ₁) (hκ₂ : Measurable κ₂)
    (hκ : ∀ ξ, κ₂ ξ = -κ₁ ξ) (s : ℝ) : phaseGroup hκ₂ s = phaseGroup hκ₁ (-s) :=
  ContinuousLinearMap.ext fun f => Lp.ext <| by
    filter_upwards [coeFn_phaseGroup hκ₂ s f, coeFn_phaseGroup hκ₁ (-s) f] with x h1 h2
    rw [h1, h2, phaseFun, phaseFun, hκ]
    have : -(s * -κ₁ x) = -(-s * κ₁ x) := by ring
    rw [this]

/-- Negating the symbol reverses the group: `U_{−κ}(s) = U_κ(−s)`. -/
theorem fourierGroup_of_neg {κ₁ κ₂ : E → ℝ} (hκ₁ : Measurable κ₁) (hκ₂ : Measurable κ₂)
    (hκ : ∀ ξ, κ₂ ξ = -κ₁ ξ) (s : ℝ) : fourierGroup hκ₂ s = fourierGroup hκ₁ (-s) :=
  ContinuousLinearMap.ext fun f => by
    rw [fourierGroup_apply, fourierGroup_apply, phaseGroup_of_neg hκ₁ hκ₂ hκ]

/-- ★ **The propagator of the reversed dynamics is an inverse**: if `κ₂ = −κ₁` and `V₂ = −V₁`,
then `e^{−it(κ₁(D)+V₁)} · e^{−it(κ₂(D)+V₂)} = 1` for `t ≥ 0`. The forward Trotter approximants
`Xₙ = (U₁ M₁)ⁿ` are invertible with `Xₙ⁻¹ = M₂ (U₂ M₂)ⁿ M₁`, a conjugate of the reversed
approximants; both converge strongly (Nelson), and `χ = Xₙ Xₙ⁻¹ χ` passes to the limit. -/
theorem schrodinger_mul_schrodinger_of_neg {κ₁ κ₂ : E → ℝ} (hκ₁ : Measurable κ₁)
    (hκ₂ : Measurable κ₂) (hκ : ∀ ξ, κ₂ ξ = -κ₁ ξ) {V₁ V₂ : E → ℝ} (hV₁ : Measurable V₁)
    (hV₂ : Measurable V₂) (hV : ∀ x, V₂ x = -V₁ x) {CV : ℝ} (hCV₁ : ∀ x, |V₁ x| ≤ CV)
    (hCV₂ : ∀ x, |V₂ x| ≤ CV) {VL₁ VL₂ : Lp ℂ ∞ (volume : Measure E)}
    (hVL₁ : (VL₁ : E → ℂ) =ᵐ[volume] fun x => (V₁ x : ℂ))
    (hVL₂ : (VL₂ : E → ℂ) =ᵐ[volume] fun x => (V₂ x : ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    schrodinger hκ₁ VL₁ t * schrodinger hκ₂ VL₂ t = 1 := by
  refine ContinuousLinearMap.ext fun χ => ?_
  rw [mul_apply_eq_comp, one_apply_eq_self]
  set U₂χ := schrodinger hκ₂ VL₂ t χ with hU₂χ
  -- the forward and reversed Trotter steps, and the inverse of the forward step
  set X : ℕ → L2 →L[ℂ] L2 := fun n => fourierGroup hκ₁ (t / n) * phaseGroup hV₁ (t / n) with hX
  set Y : ℕ → L2 →L[ℂ] L2 := fun n => fourierGroup hκ₂ (t / n) * phaseGroup hV₂ (t / n) with hY
  set Z : ℕ → L2 →L[ℂ] L2 := fun n => phaseGroup hV₂ (t / n) * fourierGroup hκ₂ (t / n) with hZ
  have hM : ∀ s, phaseGroup hV₂ s = phaseGroup hV₁ (-s) := phaseGroup_of_neg hV₁ hV₂ hV
  have hU : ∀ s, fourierGroup hκ₂ s = fourierGroup hκ₁ (-s) := fourierGroup_of_neg hκ₁ hκ₂ hκ
  have hXZ : ∀ n, X n * Z n = 1 := by
    intro n
    simp only [hX, hZ]
    rw [mul_assoc, ← mul_assoc (phaseGroup hV₁ (t / n)), hM, phaseGroup_mul_neg, one_mul, hU,
      fourierGroup_mul_neg]
  have hZpow : ∀ n, Z n ^ n = phaseGroup hV₂ (t / n) * Y n ^ n * phaseGroup hV₁ (t / n) := by
    intro n
    simp only [hZ, hY]
    exact mul_pow_conj (by rw [hM, phaseGroup_neg_mul]) (by rw [hM, phaseGroup_mul_neg]) n
  have hYiso : ∀ n g, ‖Y n g‖ = ‖g‖ := fun n g => by
    simp only [hY]
    rw [mul_apply_eq_comp, norm_fourierGroup_apply, norm_phaseGroup_apply]
  have hXiso : ∀ n g, ‖X n g‖ = ‖g‖ := fun n g => by
    simp only [hX]
    rw [mul_apply_eq_comp, norm_fourierGroup_apply, norm_phaseGroup_apply]
  have hdiv : Tendsto (fun n : ℕ => t / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat t
  -- `Zₙⁿ χ → U₂ χ`
  have hZlim : Tendsto (fun n => (Z n ^ n) χ) atTop (𝓝 U₂χ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n : ℕ => ‖phaseGroup hV₁ (t / n) χ - χ‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp ((tendsto_phaseGroup_apply_zero hV₁ χ).comp hdiv)
    have h2 : Tendsto (fun n : ℕ => ‖(Y n ^ n) χ - U₂χ‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (nelson hκ₂ hV₂ hCV₂ hVL₂ ht χ)
    have h3 : Tendsto (fun n : ℕ => ‖phaseGroup hV₂ (t / n) U₂χ - U₂χ‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp ((tendsto_phaseGroup_apply_zero hV₂ U₂χ).comp hdiv)
    have hsum := (h1.add h2).add h3
    rw [add_zero, add_zero] at hsum
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
    rw [hZpow n, mul_apply_eq_comp, mul_apply_eq_comp]
    calc ‖phaseGroup hV₂ (t / n) ((Y n ^ n) (phaseGroup hV₁ (t / n) χ)) - U₂χ‖
        = ‖phaseGroup hV₂ (t / n) ((Y n ^ n) (phaseGroup hV₁ (t / n) χ - χ))
            + phaseGroup hV₂ (t / n) ((Y n ^ n) χ - U₂χ)
            + (phaseGroup hV₂ (t / n) U₂χ - U₂χ)‖ := by
          congr 1
          simp only [map_sub]
          abel
      _ ≤ ‖phaseGroup hV₂ (t / n) ((Y n ^ n) (phaseGroup hV₁ (t / n) χ - χ))‖
            + ‖phaseGroup hV₂ (t / n) ((Y n ^ n) χ - U₂χ)‖
            + ‖phaseGroup hV₂ (t / n) U₂χ - U₂χ‖ := norm_add₃_le
      _ = ‖phaseGroup hV₁ (t / n) χ - χ‖ + ‖(Y n ^ n) χ - U₂χ‖
            + ‖phaseGroup hV₂ (t / n) U₂χ - U₂χ‖ := by
          rw [norm_phaseGroup_apply, norm_phaseGroup_apply, norm_pow_apply_eq (hYiso n)]
  -- `Xₙⁿ (Zₙⁿ χ) = χ` and `Xₙⁿ (Zₙⁿ χ) → U₁ (U₂ χ)`
  have hconst : ∀ n, (X n ^ n) ((Z n ^ n) χ) = χ := fun n => by
    rw [← mul_apply_eq_comp, pow_mul_pow_eq_one n (hXZ n), one_apply_eq_self]
  have hlim : Tendsto (fun n => (X n ^ n) ((Z n ^ n) χ)) atTop
      (𝓝 (schrodinger hκ₁ VL₁ t U₂χ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n : ℕ => ‖(Z n ^ n) χ - U₂χ‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hZlim
    have h2 : Tendsto (fun n : ℕ => ‖(X n ^ n) U₂χ - schrodinger hκ₁ VL₁ t U₂χ‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (nelson hκ₁ hV₁ hCV₁ hVL₁ ht U₂χ)
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
    calc ‖(X n ^ n) ((Z n ^ n) χ) - schrodinger hκ₁ VL₁ t U₂χ‖
        = ‖(X n ^ n) ((Z n ^ n) χ - U₂χ) + ((X n ^ n) U₂χ - schrodinger hκ₁ VL₁ t U₂χ)‖ := by
          congr 1
          simp only [map_sub]
          abel
      _ ≤ ‖(X n ^ n) ((Z n ^ n) χ - U₂χ)‖ + ‖(X n ^ n) U₂χ - schrodinger hκ₁ VL₁ t U₂χ‖ :=
          norm_add_le _ _
      _ = ‖(Z n ^ n) χ - U₂χ‖ + ‖(X n ^ n) U₂χ - schrodinger hκ₁ VL₁ t U₂χ‖ := by
          rw [norm_pow_apply_eq (hXiso n)]
  exact (tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hconst n).symm) hlim).symm

theorem coeFn_neg_ae_eq {V : E → ℝ} {VL : Lp ℂ ∞ (volume : Measure E)}
    (hVL : (VL : E → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) :
    ((-VL : Lp ℂ ∞ (volume : Measure E)) : E → ℂ) =ᵐ[volume] fun x => ((-V x : ℝ) : ℂ) := by
  filter_upwards [Lp.coeFn_neg VL, hVL] with x h1 h2
  rw [h1, Pi.neg_apply, h2, Complex.ofReal_neg]

/-- ★ `U(t) · U⁻(t) = 1`: the propagator of the reversed dynamics `e^{−it(−κ(D) − V)}` is a right
inverse of `e^{−it(κ(D) + V)}`, `t ≥ 0`. -/
theorem schrodinger_mul_schrodinger_neg {κ : E → ℝ} (hκ : Measurable κ) {V : E → ℝ}
    (hVm : Measurable V) {CV : ℝ} (hCV : ∀ x, |V x| ≤ CV) {VL : Lp ℂ ∞ (volume : Measure E)}
    (hVL : (VL : E → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    schrodinger hκ VL t * schrodinger hκ.neg (-VL) t = 1 :=
  schrodinger_mul_schrodinger_of_neg hκ hκ.neg (fun _ => rfl) hVm hVm.neg (fun _ => rfl) hCV
    (fun x => by rw [Pi.neg_apply, abs_neg]; exact hCV x) hVL (coeFn_neg_ae_eq hVL) ht

/-- ★ `U⁻(t) · U(t) = 1`: the propagator of the reversed dynamics is a left inverse. -/
theorem schrodinger_neg_mul_schrodinger {κ : E → ℝ} (hκ : Measurable κ) {V : E → ℝ}
    (hVm : Measurable V) {CV : ℝ} (hCV : ∀ x, |V x| ≤ CV) {VL : Lp ℂ ∞ (volume : Measure E)}
    (hVL : (VL : E → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    schrodinger hκ.neg (-VL) t * schrodinger hκ VL t = 1 :=
  schrodinger_mul_schrodinger_of_neg hκ.neg hκ (fun ξ => (neg_neg (κ ξ)).symm) hVm.neg hVm
    (fun x => (neg_neg (V x)).symm) (fun x => by rw [Pi.neg_apply, abs_neg]; exact hCV x) hCV
    (coeFn_neg_ae_eq hVL) hVL ht

/-- ★★ **The Schrödinger propagator is unitary.** For a real bounded potential `V` and `t ≥ 0`,
`e^{−it(κ(D) + V)}` is a linear isometric bijection of `L²`: an isometry by
`norm_schrodinger_apply`, invertible with inverse the propagator of the reversed dynamics
(`schrodinger_mul_schrodinger_neg`, `schrodinger_neg_mul_schrodinger`). -/
theorem exists_linearIsometryEquiv_schrodinger {κ : E → ℝ} (hκ : Measurable κ) {V : E → ℝ}
    (hVm : Measurable V) {CV : ℝ} (hCV : ∀ x, |V x| ≤ CV) {VL : Lp ℂ ∞ (volume : Measure E)}
    (hVL : (VL : E → ℂ) =ᵐ[volume] fun x => (V x : ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ e : L2 ≃ₗᵢ[ℂ] L2, ⇑e = schrodinger hκ VL t :=
  ⟨{ toLinearEquiv := (ContinuousLinearEquiv.equivOfInverse (schrodinger hκ VL t)
        (schrodinger hκ.neg (-VL) t)
        (fun χ => by
          rw [← mul_apply_eq_comp, schrodinger_neg_mul_schrodinger hκ hVm hCV hVL ht,
            one_apply_eq_self])
        (fun χ => by
          rw [← mul_apply_eq_comp, schrodinger_mul_schrodinger_neg hκ hVm hCV hVL ht,
            one_apply_eq_self])).toLinearEquiv
     norm_map' := norm_schrodinger_apply hκ hVm hCV hVL ht }, rfl⟩

end SchrodingerGroup

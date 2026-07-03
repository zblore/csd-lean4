import CsdLean4.LF5.FlowBornFrequency
import CsdLean4.LF6.GHZContextuality

/-!
# LF6-C (GHZ_n): the n-party GHZ de-isolation flow and the general-n Mermin forcing

**Category:** 6-Local (the D1 entangled frontier at general party number; the
n-party generalisation of the three-party GHZ C-tier `GHZDeisolationFlow.lean` /
`GHZContextuality.lean`).

This module carries the deterministic (Mermin) all-or-nothing forcing axis to
**general party number `n`**, complementing the statistical (CGLMP) axis at
general dimension `d` (`MaxEntangledDeisolationFlow.lean` + `Mathlib/Probability/
CGLMP.lean`). Together the two give the symmetric both-axes statement: the
de-isolation account reproduces forced non-locality in both the statistical
(CGLMP, general `d`) and deterministic (Mermin/GHZ, general `n`) forms at
arbitrary size. Read this framing against the honest-scope ledger below: the
general-`n` deterministic FORCING (the ±1 combinatorial no-go) is formalised for
all `n`, but the QM link (that the four ±1 context targets are GHZ_n's own
tensor-Pauli Mermin correlations) is formalised only at `n = 3`, with the
essentially-4-party case witnessed at `n = 4`; the general-`n` QM link is a named
residual. So "forced non-locality at arbitrary size" is fully load-bearing at
`n = 3`/`n = 4` and combinatorial-only (QM link deferred) for general `n`.

## What lands

1. **`ghzN n`** — the n-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` on
   `EuclideanSpace ℂ (Fin (2^n))` (all-zeros `= 0`, all-ones `= topIdx n = 2^n−1`),
   `ghzNWeight n` (Born `1/2` on the two all-equal outcomes, `0` else), unit-norm
   and weights-sum-one for `n ≥ 1`. The direct `Fin (2^n)` generalisation of the
   three-party `ghzWeight`.

2. **The de-isolation flow + Born-from-volume at `N = 2^n` (the clean general-party
   core).** `ghzNDeisolationFlow n = measurementFlow (2^n) finProdFinEquiv` on the
   dilated `Σ' = ℂℙ^{2^n·2^n − 1}` (genuinely `Φ ≠ id` for `n ≥ 1`,
   FS-measure-preserving), `ghzNDeisolation_pointer_volume` (pointer-block FS volume
   = `ghzNWeight`, composing LF5 `vnDilation_pointer_volume` @ `N=2^n` with the Born
   identity `ghzN_born`), `_frequency` (a.s. block freq → Born), `_ne_id`,
   `_measurePreserving`. This is genuine **party-number**-general de-isolation
   dynamics, not tied to `n = 3`. Born = FS-volume is **imported** from the DH/
   moment-map engine (`vnDilation_pointer_volume`), not re-derived; the flow
   **realises** the measurement, it does not derive the weights.

3. **The n-party deterministic (Mermin) forcing (the load-bearing thesis part).**
   `no_lhvN_assignment_for_ghzN` (general `n`) and `no_product_partition_realises_ghzN`
   (general `n`) generalise C.1's `no_product_partition_realises_ghz` to `n` parties:
   no setting-local `±1` PRODUCT partition of a shared probability space reproduces
   the GHZ_n Mermin correlations. The mechanism is the **spectator embedding**: the
   three-party Mermin dance runs on parties `{0,1,2}`, parties `≥ 3` measure `X`; the
   full-`n` product parity contradiction (each party's `±1` value appears squared, so
   the four correlations multiply to `+1` while their product of QM values is `−1`)
   is a genuine `n`-party statement (product over `Fin n`, `n`-party contexts).
   `no_lhv_assignment_for_ghz4` is an essentially-**four**-party witness (all four
   parties measure `Y` at least twice; no spectator) via the same parity mechanism.

4. **Capstone** `ghzNDeisolation_flow_capstone` (five conjuncts, mirror C.2/LF6-D):
   `Φ ≠ id`, FS-measure-preserving, pointer volume = Born, a.s. freq → Born,
   n-party deterministic no-LHV forcing.

## Honest scope (the GHZ_n ledger)

- **Born imported, not derived.** Born = FS-volume is the DH/moment-map cluster's
  (`fs_born_volume_ratio_N`, Gleason-free, no Born put in), imported through
  `vnDilation_pointer_volume`. The GHZ_n Born weights are computed from the two
  amplitudes; this file does not re-derive Born = volume.
- **Realisation, not derivation.** The flow **realises** the GHZ_n measurement
  dynamically; the carve is the joint moment subdivision, never a setting-local
  product region.
- **The forcing is genuine, not posited, not a hollow re-export.** The theorem's
  type genuinely quantifies over `n` parties, `n`-party product partitions, and
  full-`n` context correlations; the proof is a genuine `n`-party parity argument.
  **Honest caveat on physical strength:** the general-`n` forcing routes the
  contradiction through the three-party Mermin paradox embedded via `n − 3`
  `X`-spectators; it is a valid GHZ_n all-or-nothing but does not exhibit
  essentially-`n`-party entanglement beyond three. `no_lhv_assignment_for_ghz4`
  is the essentially-four-party witness (all parties participate) demonstrating
  genuine beyond-`n=3` content. The physical regime is `n ≥ 3` (the targets
  `⟨XXX…⟩ = +1`, `⟨XYY…⟩ = −1`, … are GHZ_n's actual Mermin correlations only for
  `n ≥ 3`; for `n = 3` the tie is `Empirical.GHZ.ghz_expectation_*`).
- **Residue: A5.** The GHZ_n entangled sector / preparation region is posited, not
  derived (A5 reduces to D1); the typicality law on `Σ'` is the Fubini-Study
  measure (A5).

## Residual (named, honestly)

- The **uniform closed-form essentially-all-`n`-parties** general-`n` Mermin
  all-or-nothing (which uses every party non-trivially; the construction depends on
  `n mod 4` and is not delivered uniformly here — only the spectator-embedding
  general-`n` and the essentially-four-party `n = 4` witness are).
- The **general-`n` GHZ_n QM confirmation** that the `±1` targets are the actual
  `⟨σ_{a_1} ⊗ … ⊗ σ_{a_n}⟩` Mermin correlations (the general tensor-Pauli
  expectation; proved for `n = 3` in `Empirical.GHZ`, named residual for general
  `n`).

All exports are foundational-triple-only (Gleason-free; the LF5 pointer engine is
off Busch, the forcing is measure-theoretic Mermin content, `decide` only on the
finite `n = 4` witness, no `native_decide`).

Reference: `specs/lf6-plan.md` (GHZ_n tranche).
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal BigOperators LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF5 CSD.LF4 CSD.LF2 CSD.Empirical.GHZ

/-- `2 ^ n` is nonzero (targeted local instance so the LF5 engine at `N = 2^n`
synthesises `[NeZero (2^n)]`). -/
instance neZero_two_pow (n : ℕ) : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩

/-! ### The top computational index `2^n − 1` (all-ones) -/

/-- The all-ones computational index `2^n − 1` of `Fin (2^n)` (the `|1…1⟩`
support of GHZ_n). -/
def topIdx (n : ℕ) : Fin (2 ^ n) :=
  ⟨2 ^ n - 1, Nat.sub_lt (pow_pos (by norm_num) n) one_pos⟩

/-- For `n ≥ 1` the all-ones index is distinct from the all-zeros index `0`
(`2^n − 1 ≠ 0` since `2^n > 1`). -/
lemma topIdx_ne_zero (n : ℕ) (hn : n ≠ 0) : topIdx n ≠ 0 := by
  have h : (2 : ℕ) ^ n - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_two_pow_iff.mpr hn)
  intro hcontra
  have hv : (2 : ℕ) ^ n - 1 = 0 := by
    have := congrArg Fin.val hcontra
    simpa [topIdx] using this
  exact h hv

/-! ### The GHZ_n Born weights -/

/-- **The GHZ_n Born weights.** The n-qubit GHZ state has support exactly on the
two all-equal computational indices `0` (all zeros) and `topIdx n` (all ones),
each with weight `1/2`; every other outcome has weight `0`. Not a stub:
`ghzN_normSq_eq_weight` proves it equals `‖(ghzN n) i‖²`. -/
noncomputable def ghzNWeight (n : ℕ) (i : Fin (2 ^ n)) : ℝ :=
  if i = 0 ∨ i = topIdx n then (2 : ℝ)⁻¹ else 0

/-! ### The GHZ_n state -/

/-- **The n-qubit GHZ state** `(|0…0⟩ + |1…1⟩)/√2` on `EuclideanSpace ℂ (Fin (2^n))`:
computational amplitude `(√2)⁻¹` on the all-zeros index `0` and the all-ones index
`topIdx n`, `0` elsewhere. Unit-norm for `n ≥ 1`. The direct `Fin (2^n)`
generalisation of the three-party `ghzState`. -/
noncomputable def ghzN (n : ℕ) : EuclideanSpace ℂ (Fin (2 ^ n)) :=
  WithLp.toLp 2 (fun i => if i = 0 ∨ i = topIdx n then ((Real.sqrt 2 : ℂ))⁻¹ else 0)

/-- The computational amplitude of GHZ_n at index `i`. -/
lemma ghzN_apply (n : ℕ) (i : Fin (2 ^ n)) :
    (ghzN n) i = if i = 0 ∨ i = topIdx n then ((Real.sqrt 2 : ℂ))⁻¹ else 0 := rfl

/-- **The GHZ_n Born weights are the squared computational amplitudes.** For every
outcome `i`, `‖(ghzN n) i‖² = ghzNWeight n i` — computed from the amplitude `(√2)⁻¹`
(`‖·‖² = 1/2`) on the support and the zeros off it. -/
lemma ghzN_normSq_eq_weight (n : ℕ) (i : Fin (2 ^ n)) :
    ‖(ghzN n) i‖ ^ 2 = ghzNWeight n i := by
  rw [ghzN_apply]
  unfold ghzNWeight
  by_cases h : i = 0 ∨ i = topIdx n
  · rw [if_pos h, if_pos h, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · rw [if_neg h, if_neg h, norm_zero]; norm_num

/-- The GHZ_n Born weights sum to `1` (two support cells, each `1/2`), for `n ≥ 1`. -/
lemma sum_ghzNWeight (n : ℕ) (hn : 0 < n) :
    ∑ i : Fin (2 ^ n), ghzNWeight n i = 1 := by
  have hne : topIdx n ≠ 0 := topIdx_ne_zero n hn.ne'
  rw [show (∑ i : Fin (2 ^ n), ghzNWeight n i)
        = ∑ i : Fin (2 ^ n),
            ((if i = 0 then (2 : ℝ)⁻¹ else 0) + (if i = topIdx n then (2 : ℝ)⁻¹ else 0))
      from ?_]
  · rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (0 : Fin (2 ^ n)),
      Finset.sum_ite_eq' Finset.univ (topIdx n)]
    simp only [Finset.mem_univ, if_true]
    norm_num
  · apply Finset.sum_congr rfl
    intro i _
    unfold ghzNWeight
    by_cases h0 : i = 0
    · subst h0
      rw [if_pos (Or.inl rfl), if_pos rfl, if_neg (Ne.symm hne), add_zero]
    · by_cases ht : i = topIdx n
      · subst ht
        rw [if_pos (Or.inr rfl), if_neg hne, if_pos rfl, zero_add]
      · rw [if_neg (not_or.mpr ⟨h0, ht⟩), if_neg h0, if_neg ht, add_zero]

/-- **GHZ_n is a unit preparation** for `n ≥ 1`. `‖ghzN n‖² = ∑_i ghzNWeight n i = 1`.
Discharges the `hψ` hypothesis of the LF5 pointer-volume / frequency theorems. -/
theorem ghzN_norm (n : ℕ) (hn : 0 < n) : ‖ghzN n‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin (2 ^ n), ‖(ghzN n) i‖ ^ 2 = 1 := by
    calc ∑ i : Fin (2 ^ n), ‖(ghzN n) i‖ ^ 2
        = ∑ i : Fin (2 ^ n), ghzNWeight n i :=
          Finset.sum_congr rfl (fun i _ => ghzN_normSq_eq_weight n i)
      _ = 1 := sum_ghzNWeight n hn
  rw [hsum, Real.sqrt_one]

/-- **The GHZ_n coordinate-Born identity.** The squared computational amplitude of
GHZ_n at pointer cell `i` equals the Born weight `ghzNWeight n i`, in the
`inner ⟨e_i, ·⟩` form the LF5 pointer theorems consume. -/
lemma ghzN_born (n : ℕ) (i : Fin (2 ^ n)) :
    ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) (ghzN n)‖ ^ 2 = ghzNWeight n i := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  exact ghzN_normSq_eq_weight n i

/-! ### Deliverable 2: the de-isolation flow (the clean general-party core) -/

/-- **The GHZ_n de-isolation flow** `Φ = measurementFlow (2^n) finProdFinEquiv` on
the dilated projective ontic space `Σ' = ℂℙ^{2^n·2^n − 1}`. The LF5-B von Neumann
de-isolation flow instantiated at the joint n-qubit system `N = 2^n`. -/
noncomputable def ghzNDeisolationFlow (n : ℕ) :
    ℙ ℂ (EuclideanSpace ℂ (Fin ((2 ^ n) * (2 ^ n))))
      → ℙ ℂ (EuclideanSpace ℂ (Fin ((2 ^ n) * (2 ^ n)))) :=
  measurementFlow (2 ^ n) finProdFinEquiv

/-- The GHZ_n de-isolation flow is Fubini-Study measure-preserving (the Liouville /
`hΦ_pres` content), inherited from `measurementFlow_measurePreserving`. -/
theorem ghzNDeisolation_measurePreserving (n : ℕ) (p₀ : CPN ((2 ^ n) * (2 ^ n))) :
    MeasurePreserving (ghzNDeisolationFlow n)
      (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  measurementFlow_measurePreserving finProdFinEquiv p₀

/-- The GHZ_n de-isolation flow is genuinely not the identity for `n ≥ 1`
(`1 < 2^n`), inherited from `measurementFlow_ne_id`. -/
theorem ghzNDeisolation_ne_id (n : ℕ) (hn : 0 < n) : ghzNDeisolationFlow n ≠ id :=
  measurementFlow_ne_id (Nat.one_lt_two_pow_iff.mpr hn.ne') finProdFinEquiv

/-- **The reproduction (the GHZ_n headline).** The context-fixed `BornRegion`
pointer-block `i` Fubini-Study volume of the GHZ_n de-isolation flow equals the
GHZ_n Born weight `ghzNWeight n i`, for the prepared state `φ = ghzN n`, every
`n ≥ 1`.

The proof **composes** LF5 `vnDilation_pointer_volume` at `N = 2^n` (pointer-block
volume = `‖⟨e_i, φ⟩‖²`, Gleason-free, Born = FS-volume imported from the DH engine)
with the coordinate-Born identity `ghzN_born` (the computed GHZ_n weights). -/
theorem ghzNDeisolation_pointer_volume (n : ℕ) (hn : 0 < n) {M : ℕ}
    (e : Fin (2 ^ n) × Fin (2 ^ n) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV (2 ^ n)) (ghzN n)))
    (hψ'0 : ψ' ≠ 0) (i : Fin (2 ^ n)) :
    ∑ nn : Fin (2 ^ n),
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (nn, i)))).toReal
      = ghzNWeight n i := by
  rw [← vnDilation_pointer_volume (ghzN n) (ghzN_norm n hn) e p₀ ψ' hψ'eq hψ'0 i]
  exact ghzN_born n i

/-- **The empirical capstone.** For i.i.d. Fubini-Study-typical trials on the
dilated `Σ' = ℂℙ^{2^n·2^n − 1}` (the A5 typicality posit on the enlarged entangled
sector), almost surely every pointer-block `i` empirical frequency converges to the
GHZ_n Born weight `ghzNWeight n i`. Instantiates LF5 `vnDilation_pointer_frequency`
at `N = 2^n`, `φ = ghzN n`, landing the limit on `ghzNWeight` via `ghzN_born`. -/
theorem ghzNDeisolation_frequency (n : ℕ) (hn : 0 < n) {M : ℕ}
    (e : Fin (2 ^ n) × Fin (2 ^ n) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV (2 ^ n)) (ghzN n)))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (2 ^ n),
      Tendsto
        (fun m : ℕ =>
          ∑ nn : Fin (2 ^ n),
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (nn, i)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (ghzNWeight n i)) := by
  filter_upwards [vnDilation_pointer_frequency (ghzN n) (ghzN_norm n hn) e ψ'
      hψ'eq hψ'0 p₀ X hX hlaw hindep] with ω hω i
  have h := hω i
  rwa [ghzN_born n i] at h

/-! ### Deliverable 3: the n-party deterministic (Mermin) forcing

The n-party generalisation of C.1's forced-contextuality no-go
(`no_product_partition_realises_ghz`). The mechanism is the **spectator
embedding**: parties `{0,1,2}` run the three-party Mermin dance, parties `≥ 3`
measure `X`; the full-`n` product parity contradiction is a genuine `n`-party
statement. -/

/-- The n-party Mermin context `(a, b, c)`: party `0` measures Pauli axis `a`,
party `1` axis `b`, party `2` axis `c`, every party `≥ 3` (spectator) axis `X`. -/
def ghzNCtx (a b c : PauliAxis) (n : ℕ) (i : Fin n) : PauliAxis :=
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else PauliAxis.x

/-- **No `n`-party `±1` LHV assignment reproduces the GHZ_n Mermin product
constraints** (the combinatorial all-or-nothing, general `n`). The four full-`n`
context products must equal `+1` (all-`X`), `−1`, `−1`, `−1` (the twisted `XYY /
YXY / YYX` contexts, spectators `X`); multiplying them, each party's `±1` value
appears an even number of times so the product is `+1`, while the product of the
four target values is `−1`. Contradiction.

Genuinely `n`-party (product over `Fin n`, `n`-party contexts). Physical regime
`n ≥ 3`; the mechanism is the three-party Mermin paradox embedded via `n − 3`
`X`-spectators (see the module ledger). -/
theorem no_lhvN_assignment_for_ghzN (n : ℕ) :
    ¬ ∃ lam : Fin n → PauliAxis → ℤ,
      (∀ i ax, lam i ax = 1 ∨ lam i ax = -1) ∧
      (∏ i, lam i (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n i) = 1) ∧
      (∏ i, lam i (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n i) = -1) ∧
      (∏ i, lam i (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n i) = -1) ∧
      (∏ i, lam i (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n i) = -1) := by
  rintro ⟨lam, hpm, h1, h2, h3, h4⟩
  have hcell : ∀ i : Fin n,
      lam i (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n i)
        * lam i (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n i)
        * lam i (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n i)
        * lam i (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n i) = 1 := by
    intro i
    simp only [ghzNCtx]
    split_ifs with h0 h1 h2 <;>
      rcases hpm i PauliAxis.x with hx | hx <;>
      rcases hpm i PauliAxis.y with hy | hy <;>
      simp only [hx, hy] <;> norm_num
  have hkey :
      (∏ i, lam i (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n i))
        * (∏ i, lam i (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n i))
        * (∏ i, lam i (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n i))
        * (∏ i, lam i (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n i)) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => hcell i)
  rw [h1, h2, h3, h4] at hkey
  norm_num at hkey

/-! #### The measure-theoretic n-party forcing (generalising C.1) -/

/-- ±1-valued measurable function is integrable on a probability space (bounded by
`1`). Re-derivation of C.1's private helper. -/
private lemma pm_integrable {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    [IsProbabilityMeasure μ] {f : Λ → ℝ} (hf : Measurable f)
    (hpm : ∀ l, f l = 1 ∨ f l = -1) : Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun l => ?_)
  rcases hpm l with h | h <;> rw [h] <;> norm_num

/-- Perfect correlation forces pointwise determinism: a ±1-valued measurable
function whose integral over a probability measure equals `v ∈ {1, −1}` is
`μ`-a.e. equal to `v`. Re-derivation of C.1's private helper. -/
private lemma pm_ae_eq {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    [IsProbabilityMeasure μ] {f : Λ → ℝ} (hf : Measurable f)
    (hpm : ∀ l, f l = 1 ∨ f l = -1) {v : ℝ} (hv : v = 1 ∨ v = -1)
    (hint : ∫ l, f l ∂μ = v) : ∀ᵐ l ∂μ, f l = v := by
  have hfint : Integrable f μ := pm_integrable μ hf hpm
  rcases hv with rfl | rfl
  · have hg_nonneg : (0 : Λ → ℝ) ≤ fun l => (1 : ℝ) - f l := by
      intro l; show (0 : ℝ) ≤ 1 - f l
      rcases hpm l with h | h <;> rw [h] <;> norm_num
    have hgint : Integrable (fun l => (1 : ℝ) - f l) μ :=
      (integrable_const 1).sub hfint
    have hz : ∫ l, ((1 : ℝ) - f l) ∂μ = 0 := by
      rw [integral_sub (integrable_const 1) hfint, hint]
      simp [integral_const]
    have hae := (integral_eq_zero_iff_of_nonneg hg_nonneg hgint).mp hz
    filter_upwards [hae] with l hl
    have h2 : (1 : ℝ) - f l = 0 := by simpa using hl
    linarith
  · have hg_nonneg : (0 : Λ → ℝ) ≤ fun l => f l + 1 := by
      intro l; show (0 : ℝ) ≤ f l + 1
      rcases hpm l with h | h <;> rw [h] <;> norm_num
    have hgint : Integrable (fun l => f l + 1) μ :=
      hfint.add (integrable_const 1)
    have hz : ∫ l, (f l + 1) ∂μ = 0 := by
      rw [integral_add hfint (integrable_const 1), hint]
      simp [integral_const]
    have hae := (integral_eq_zero_iff_of_nonneg hg_nonneg hgint).mp hz
    filter_upwards [hae] with l hl
    have h2 : f l + 1 = 0 := by simpa using hl
    linarith

/-- The full-`n` context product of ±1-valued responses is ±1 (its square is `1`). -/
private lemma prod_pm_real {Λ : Type*} {n : ℕ} (R : Fin n → PauliAxis → Λ → ℝ)
    (c : Fin n → PauliAxis) (hpm : ∀ i ax l, R i ax l = 1 ∨ R i ax l = -1) (l : Λ) :
    (∏ i, R i (c i) l) = 1 ∨ (∏ i, R i (c i) l) = -1 := by
  have hsq : (∏ i, R i (c i) l) * (∏ i, R i (c i) l) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one
      (fun i _ => by rcases hpm i (c i) l with h | h <;> rw [h] <;> norm_num)
  exact mul_self_eq_one_iff.mp hsq

/-- The full-`n` context product is measurable (finite product of measurable
responses). -/
private lemma prod_meas {Λ : Type*} {n : ℕ} [MeasurableSpace Λ]
    (R : Fin n → PauliAxis → Λ → ℝ) (c : Fin n → PauliAxis)
    (hmeas : ∀ i ax, Measurable (R i ax)) :
    Measurable (fun l => ∏ i, R i (c i) l) :=
  Finset.measurable_prod Finset.univ (fun i _ => hmeas i (c i))

/-- `R` is a **product (non-contextual) partition** of the shared ontic space
`(Λ, μ)` for the `n`-party GHZ scenario: `R i ax` is the ±1 measurable response of
party `i ∈ Fin n` measuring Pauli axis `ax ∈ {x, y}`, a function of that party's own
axis and the shared microstate alone. The `n`-party analogue of C.1's
`IsProductPartitionGHZ`. -/
def IsProductPartitionGHZN {Λ : Type*} [MeasurableSpace Λ] (n : ℕ)
    (R : Fin n → PauliAxis → Λ → ℝ) : Prop :=
  (∀ i ax, Measurable (R i ax)) ∧ (∀ i ax l, R i ax l = 1 ∨ R i ax l = -1)

/-- A product partition **reproduces the GHZ_n Mermin correlations** if its four
factorisable full-`n` context-product expectations match the GHZ_n perfect
correlations `+1` (all-`X`), `−1`, `−1`, `−1` (the twisted contexts). These are
known to be GHZ_n's actual QM Mermin correlations for every `n ≥ 3` (X⊗ⁿ is a
+1 stabiliser; a two-`Y`-rest-`X` operator has eigenvalue `−1` independent of the
spectator count), but this QM link is FORMALISED only at `n = 3` (via
`Empirical.GHZ`) and witnessed essentially-4-party at `n = 4`; the general-`n`
QM confirmation is a named residual (see the module ledger). -/
def ReproducesGHZN {Λ : Type*} [MeasurableSpace Λ] (n : ℕ) (μ : Measure Λ)
    (R : Fin n → PauliAxis → Λ → ℝ) : Prop :=
  (∫ l, ∏ i, R i (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n i) l ∂μ = 1) ∧
  (∫ l, ∏ i, R i (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n i) l ∂μ = -1) ∧
  (∫ l, ∏ i, R i (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n i) l ∂μ = -1) ∧
  (∫ l, ∏ i, R i (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n i) l ∂μ = -1)

/-- **`no_product_partition_realises_ghzN` (the n-party generalisation of C.1, the
load-bearing forcing).** There is NO product (setting-local, non-contextual)
partition of any shared probability space `(Λ, μ)` whose factorisable full-`n`
context-product expectations reproduce the GHZ_n Mermin correlations.

Proof (deterministic all-or-nothing, generalising C.1): each of the four ±1-valued
full-`n` product integrands has expectation exactly ±1, so by `pm_ae_eq` it equals
that value `μ`-a.e.; the four full-measure sets intersect (probability measure),
giving a single microstate `l₀`. Reading off the ±1 value of every party-and-axis
response at `l₀` yields an `n`-party deterministic assignment satisfying all four
Mermin product constraints, which `no_lhvN_assignment_for_ghzN` forbids. Genuinely
`n`-party; physical regime `n ≥ 3` (see the module ledger). -/
theorem no_product_partition_realises_ghzN {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (n : ℕ)
    (R : Fin n → PauliAxis → Λ → ℝ)
    (hPP : IsProductPartitionGHZN n R) (hRep : ReproducesGHZN n μ R) : False := by
  obtain ⟨hmeas, hpm⟩ := hPP
  obtain ⟨h1, h2, h3, h4⟩ := hRep
  have hae1 : ∀ᵐ l ∂μ,
      (∏ i, R i (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n i) l) = 1 :=
    pm_ae_eq μ (prod_meas R _ hmeas) (fun l => prod_pm_real R _ hpm l) (Or.inl rfl) h1
  have hae2 : ∀ᵐ l ∂μ,
      (∏ i, R i (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n i) l) = -1 :=
    pm_ae_eq μ (prod_meas R _ hmeas) (fun l => prod_pm_real R _ hpm l) (Or.inr rfl) h2
  have hae3 : ∀ᵐ l ∂μ,
      (∏ i, R i (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n i) l) = -1 :=
    pm_ae_eq μ (prod_meas R _ hmeas) (fun l => prod_pm_real R _ hpm l) (Or.inr rfl) h3
  have hae4 : ∀ᵐ l ∂μ,
      (∏ i, R i (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n i) l) = -1 :=
    pm_ae_eq μ (prod_meas R _ hmeas) (fun l => prod_pm_real R _ hpm l) (Or.inr rfl) h4
  obtain ⟨l₀, e1, e2, e3, e4⟩ := (hae1.and (hae2.and (hae3.and hae4))).exists
  set lam : Fin n → PauliAxis → ℤ :=
    fun i ax => if R i ax l₀ = 1 then (1 : ℤ) else -1 with hlam
  have key : ∀ i ax, ((lam i ax : ℤ) : ℝ) = R i ax l₀ := by
    intro i ax
    rcases hpm i ax l₀ with h | h
    · have hval : lam i ax = 1 := by rw [hlam]; simp [h]
      rw [hval]; push_cast; rw [h]
    · have hne : R i ax l₀ ≠ 1 := by rw [h]; norm_num
      have hval : lam i ax = -1 := by rw [hlam]; simp [hne]
      rw [hval]; push_cast; rw [h]
  have hpmlam : ∀ i ax, lam i ax = 1 ∨ lam i ax = -1 := by
    intro i ax; rw [hlam]; by_cases h : R i ax l₀ = 1 <;> simp [h]
  have cast_prod : ∀ (c : Fin n → PauliAxis) (v : ℝ),
      (∏ i, R i (c i) l₀) = v → ((∏ i, lam i (c i) : ℤ) : ℝ) = v := by
    intro c v hv
    push_cast
    rw [Finset.prod_congr rfl (fun i _ => key i (c i))]
    exact hv
  have c1 : ∏ i, lam i (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n i) = 1 := by
    exact_mod_cast cast_prod _ 1 e1
  have c2 : ∏ i, lam i (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n i) = -1 := by
    exact_mod_cast cast_prod _ (-1) e2
  have c3 : ∏ i, lam i (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n i) = -1 := by
    exact_mod_cast cast_prod _ (-1) e3
  have c4 : ∏ i, lam i (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n i) = -1 := by
    exact_mod_cast cast_prod _ (-1) e4
  exact no_lhvN_assignment_for_ghzN n ⟨lam, hpmlam, c1, c2, c3, c4⟩

/-! #### The essentially-four-party witness (all parties participate)

`no_lhv_assignment_for_ghz4` is a genuine four-party all-or-nothing forcing where
NO party is a pure spectator: every party measures `Y` at least twice across the
four contexts (`YYYY`, `YXXY`, `XYXY`, `XXYY`). This is genuine essentially-`n`-party
content beyond the three-party paradox, via the same parity mechanism (the uniform
essentially-all-`n`-parties construction, `n mod 4`-dependent, is the residual). -/

/-- **No four-party `±1` LHV assignment reproduces the essentially-four-party GHZ_4
Mermin constraints.** Contexts `YYYY (+1)`, `YXXY (−1)`, `XYXY (−1)`, `XXYY (−1)`;
every party has an even (`4` or `2`) `Y`/`X` count, so multiplying the four
constraints gives `+1` while the product of target values is `−1`. All four parties
participate non-trivially (no spectator). -/
theorem no_lhv_assignment_for_ghz4 :
    ¬ ∃ lam : Fin 4 → PauliAxis → ℤ,
      (∀ i ax, lam i ax = 1 ∨ lam i ax = -1) ∧
      lam 0 PauliAxis.y * lam 1 PauliAxis.y * lam 2 PauliAxis.y * lam 3 PauliAxis.y = 1 ∧
      lam 0 PauliAxis.y * lam 1 PauliAxis.x * lam 2 PauliAxis.x * lam 3 PauliAxis.y = -1 ∧
      lam 0 PauliAxis.x * lam 1 PauliAxis.y * lam 2 PauliAxis.x * lam 3 PauliAxis.y = -1 ∧
      lam 0 PauliAxis.x * lam 1 PauliAxis.x * lam 2 PauliAxis.y * lam 3 PauliAxis.y = -1 := by
  rintro ⟨lam, hpm, c1, c2, c3, c4⟩
  have hsq : ∀ i ax, lam i ax * lam i ax = 1 := fun i ax => by
    rcases hpm i ax with h | h <;> rw [h] <;> ring
  have hprod :
      (lam 0 PauliAxis.y * lam 1 PauliAxis.y * lam 2 PauliAxis.y * lam 3 PauliAxis.y)
        * (lam 0 PauliAxis.y * lam 1 PauliAxis.x * lam 2 PauliAxis.x * lam 3 PauliAxis.y)
        * (lam 0 PauliAxis.x * lam 1 PauliAxis.y * lam 2 PauliAxis.x * lam 3 PauliAxis.y)
        * (lam 0 PauliAxis.x * lam 1 PauliAxis.x * lam 2 PauliAxis.y * lam 3 PauliAxis.y)
      = (lam 0 PauliAxis.x * lam 0 PauliAxis.x) * (lam 0 PauliAxis.y * lam 0 PauliAxis.y)
        * (lam 1 PauliAxis.x * lam 1 PauliAxis.x) * (lam 1 PauliAxis.y * lam 1 PauliAxis.y)
        * (lam 2 PauliAxis.x * lam 2 PauliAxis.x) * (lam 2 PauliAxis.y * lam 2 PauliAxis.y)
        * (lam 3 PauliAxis.y * lam 3 PauliAxis.y) * (lam 3 PauliAxis.y * lam 3 PauliAxis.y) := by
    ring
  rw [c1, c2, c3, c4] at hprod
  simp only [hsq] at hprod
  norm_num at hprod

/-! ### Deliverable 4: the capstone -/

/-- **The GHZ_n capstone: the n-party GHZ de-isolation flow.** A deterministic,
Fubini-Study-measure-preserving de-isolation flow `Φ ≠ id` on the dilated
`Σ' = ℂℙ^{2^n·2^n − 1}`, for every `n ≥ 3`, whose context-fixed `BornRegion`
pointer-block volumes are the GHZ_n Born weights `ghzNWeight`, with a.s. block
frequencies → the weights, plus the n-party deterministic (Mermin) forcing.
Conjuncts:

1. genuine dynamics, `Φ ≠ id` (`measurementFlow_ne_id`, `1 < 2^n`);
2. physically admissible: FS measure-preserving (`measurementFlow_measurePreserving`);
3. pointer-block FS volume = the GHZ_n Born weight, every outcome
   (`ghzNDeisolation_pointer_volume`);
4. a.s. block frequencies → the GHZ_n Born weight (`ghzNDeisolation_frequency`);
5. the n-party deterministic forcing: no setting-local `±1` product partition
   reproduces the GHZ_n Mermin correlations (`no_product_partition_realises_ghzN`).

Born = FS-volume is imported from the DH/FS-volume engine, not re-derived; the flow
realises (not derives) the GHZ_n measurement. The forcing is a genuine `n`-party
statement whose mechanism is the three-party Mermin paradox embedded via
`X`-spectators (`no_lhv_assignment_for_ghz4` is the essentially-four-party witness).
Residue: A5 (the GHZ_n entangled sector posited). Honest ledger: module docstring. -/
theorem ghzNDeisolation_flow_capstone (n : ℕ) (hn : 3 ≤ n) {M : ℕ}
    (e : Fin (2 ^ n) × Fin (2 ^ n) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV (2 ^ n)) (ghzN n)))
    (hψ'0 : ψ' ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    -- (1) genuine dynamics
    measurementFlow (2 ^ n) e ≠ id
    -- (2) FS measure-preserving
    ∧ MeasurePreserving (measurementFlow (2 ^ n) e)
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀)
    -- (3) pointer-block FS volume = the GHZ_n Born weight
    ∧ (∀ i : Fin (2 ^ n),
        ∑ nn : Fin (2 ^ n),
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (nn, i)))).toReal
          = ghzNWeight n i)
    -- (4) a.s. block frequencies → the GHZ_n Born weight
    ∧ (∀ᵐ ω ∂ Pr, ∀ i : Fin (2 ^ n),
        Tendsto
          (fun m : ℕ =>
            ∑ nn : Fin (2 ^ n),
              (∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (nn, i)))
                    (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
          atTop
          (nhds (ghzNWeight n i)))
    -- (5) the n-party deterministic (Mermin) forcing
    ∧ (∀ (Λ : Type) [MeasurableSpace Λ] (μ : Measure Λ) [IsProbabilityMeasure μ]
        (R : Fin n → PauliAxis → Λ → ℝ), IsProductPartitionGHZN n R →
        ReproducesGHZN n μ R → False) :=
  ⟨measurementFlow_ne_id (Nat.one_lt_two_pow_iff.mpr (by omega)) e,
   measurementFlow_measurePreserving e p₀,
   fun i => ghzNDeisolation_pointer_volume n (by omega) e p₀ ψ' hψ'eq hψ'0 i,
   ghzNDeisolation_frequency n (by omega) e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep,
   fun Λ _ μ _ R hPP hRep => no_product_partition_realises_ghzN μ n R hPP hRep⟩

end LF6
end CSD

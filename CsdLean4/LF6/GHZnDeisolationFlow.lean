/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF5.FlowBornFrequency
public import CsdLean4.LF6.GHZContextuality

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
all `n`, and (2026-07-03, deliverable 5) the QM link is now ALSO general-`n`: the
four ±1 context targets are DERIVED to be GHZ_n's own tensor-Pauli Mermin
correlations `⟨GHZ_n | σ_{a_1} ⊗ … ⊗ σ_{a_n} | GHZ_n⟩` for every `n ≥ 3`
(`ghzN_mermin_correlations`), through a genuine two-corner Hilbert reducer
(`ghzN_expectation_corner`), not `n = 3`-anchored. So "forced non-locality at
arbitrary size" is now fully load-bearing (dynamics + forcing + QM link) for
general `n ≥ 3`; the essentially-4-party case is additionally witnessed at `n = 4`.

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

5. **The general-`n` GHZ_n QM tensor-Pauli link (deliverable 5, residual closure).**
   `ghzN_expectation_corner` (the two-corner Hilbert reducer on `Fin (2^n)`),
   `tensorPauliFin` (the `n`-fold tensor Pauli via the product-of-factor-entries
   Kronecker formula on the bit-decomposition basis `finFunctionFinEquiv`),
   `ghzN_mermin_correlation` / `ghzN_mermin_correlations` (the four GHZ_n Mermin
   correlations `+1, −1, −1, −1` DERIVED for every `n ≥ 3`, the spectator `X`-factors
   contributing `+1` via `prod_ghzNCtx`), and `no_product_partition_realises_ghzN_qm`
   (the forcing routed through GHZ_n's ACTUAL QM correlations via
   `reproducesGHZN_QM_iff`). This closes the general-`n` QM-link residual.

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
  `⟨XXX…⟩ = +1`, `⟨XYY…⟩ = −1`, … are GHZ_n's actual Mermin correlations for every
  `n ≥ 3`, DERIVED here as `ghzN_mermin_correlations` — deliverable 5, general `n`;
  at `n = 3` this agrees with `Empirical.GHZ.ghz_expectation_*`).
- **Residue: A5.** The GHZ_n entangled sector / preparation region is posited, not
  derived (A5 reduces to D1); the typicality law on `Σ'` is the Fubini-Study
  measure (A5).

## Residual (named, honestly)

- The **uniform closed-form essentially-all-`n`-parties** general-`n` Mermin
  all-or-nothing (which uses every party non-trivially; the construction depends on
  `n mod 4` and is not delivered uniformly here — only the spectator-embedding
  general-`n` and the essentially-four-party `n = 4` witness are).
- **CLOSED (2026-07-03, deliverable 5): the general-`n` GHZ_n QM confirmation.** The
  four `±1` targets are DERIVED to be the actual `⟨σ_{a_1} ⊗ … ⊗ σ_{a_n}⟩` Mermin
  correlations for every `n ≥ 3` (`ghzN_mermin_correlations`, via the two-corner
  reducer `ghzN_expectation_corner` and the product-of-factor-entries tensor Pauli
  `tensorPauliFin`), no longer `n = 3`-anchored to `Empirical.GHZ`. The one residual
  sub-point: the fully-general arbitrary-Pauli-tensor reducer (any `Z` factors, any
  axis pattern) is not delivered; only the `X`/`Y` Mermin family relevant to the four
  `ghzNCtx` contexts is (which is exactly what the forcing consumes).

All exports are foundational-triple-only (Gleason-free; the LF5 pointer engine is
off Busch, the forcing is measure-theoretic Mermin content; `decide` is used only
on the two-element `PauliAxis` inequality `x ≠ y` (and the `n = 4` witness closes
by `norm_num`/`ring`), no `native_decide`).

Reference: `specs/lf6-plan.md` (GHZ_n tranche).
-/

@[expose] public section

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
lemma prod_pm_real {Λ : Type*} {n : ℕ} (R : Fin n → PauliAxis → Λ → ℝ)
    (c : Fin n → PauliAxis) (hpm : ∀ i ax l, R i ax l = 1 ∨ R i ax l = -1) (l : Λ) :
    (∏ i, R i (c i) l) = 1 ∨ (∏ i, R i (c i) l) = -1 := by
  have hsq : (∏ i, R i (c i) l) * (∏ i, R i (c i) l) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one
      (fun i _ => by rcases hpm i (c i) l with h | h <;> rw [h] <;> norm_num)
  exact mul_self_eq_one_iff.mp hsq

/-- The full-`n` context product is measurable (finite product of measurable
responses). -/
lemma prod_meas {Λ : Type*} {n : ℕ} [MeasurableSpace Λ]
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
correlations `+1` (all-`X`), `−1`, `−1`, `−1` (the twisted contexts). These
`±1` targets ARE GHZ_n's actual QM tensor-Pauli Mermin correlations for every
`n ≥ 3` — DERIVED as `ghzN_mermin_correlations` (deliverable 5, general `n`;
`X⊗ⁿ` is a `+1` stabiliser, a two-`Y`-rest-`X` operator has eigenvalue `−1`
independent of the spectator count). The forcing is routed through those actual QM
correlations by `no_product_partition_realises_ghzN_qm` (via `reproducesGHZN_QM_iff`
and `ReproducesGHZN_QM`); the general-`n` QM link is CLOSED (previously formalised
only at `n = 3` via `Empirical.GHZ`). -/
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

/-! ### Deliverable 5 (residual closure): the general-`n` GHZ_n QM tensor-Pauli link

Closes the LF6-E named residual "the general-`n` GHZ_n QM confirmation that the ±1
targets are the actual `⟨σ_{a_1} ⊗ … ⊗ σ_{a_n}⟩` Mermin correlations". The four ±1
targets of `ReproducesGHZN` / `no_lhvN_assignment_for_ghzN` (`+1` all-`X`, `−1` for
each twisted 2-`Y` context) are here DERIVED to be GHZ_n's own tensor-Pauli Mermin
correlations `⟨GHZ_n | σ_{a_1} ⊗ … ⊗ σ_{a_n} | GHZ_n⟩`, for every `n ≥ 3`, as a
genuine Hilbert computation (the two-corner reducer + the product-of-factor-entries
tensor Pauli on the bit-decomposition basis), not asserted and not `n = 3`-anchored.

The tensor-Pauli operator is `tensorPauliFin n f`, whose `(r, c)` entry is the
standard product-of-factor-entries formula `∏ i, (σ·f i)_{r_i, c_i}` under the bit
decomposition `Fin (2^n) ≃ (Fin n → Fin 2)` (`finFunctionFinEquiv`). This IS the
`n`-fold Kronecker product `σ·f₁ ⊗ … ⊗ σ·f_n` (the definition of the Kronecker
product on the tensor-basis indices); at `n = 3` it agrees, up to the
`Fin 8 ≃ Fin 2 × Fin 2 × Fin 2` reindexing, with `Empirical.GHZ.sigmaDotTriple`. -/

section QMLink

open CSD.LF3 CSD.Empirical.Bell

/-! #### The two-corner reducer for GHZ_n on `Fin (2^n)` -/

/-- `∑ i : Fin n, 2^i = 2^n − 1` (the all-ones binary expansion). -/
lemma sum_two_pow_fin (n : ℕ) : ∑ i : Fin n, (2 : ℕ) ^ (i : ℕ) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    have h1 : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    omega

/-- GHZ_n written as `(√2)⁻¹ • (|0…0⟩ + |1…1⟩)` in the two-support single-vector
form the corner reducer consumes. -/
lemma ghzN_eq_smul (n : ℕ) (hn : 0 < n) :
    ghzN n = ((Real.sqrt 2 : ℂ)⁻¹) •
      (EuclideanSpace.single (0 : Fin (2 ^ n)) (1 : ℂ)
        + EuclideanSpace.single (topIdx n) (1 : ℂ)) := by
  have hne : topIdx n ≠ (0 : Fin (2 ^ n)) := topIdx_ne_zero n hn.ne'
  ext i
  rw [ghzN_apply]
  simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, smul_eq_mul]
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos (Or.inl rfl), if_pos rfl, if_neg (Ne.symm hne)]
    ring
  · by_cases ht : i = topIdx n
    · subst ht
      rw [if_pos (Or.inr rfl), if_neg h0, if_pos rfl]
      ring
    · rw [if_neg (not_or.mpr ⟨h0, ht⟩), if_neg h0, if_neg ht]
      ring

/-- Coordinate readout of `toEuclideanLin`: `⟨e_i, (toEuclideanLin M) e_j⟩ = M i j`. -/
lemma toELin_single_coord {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    inner ℂ (EuclideanSpace.single i (1 : ℂ))
        (Matrix.toEuclideanLin M (EuclideanSpace.single j (1 : ℂ))) = M i j := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, Matrix.ofLp_toEuclideanLin]
  simp only [Matrix.mulVec, dotProduct, PiLp.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j (fun k => M i k)]
  simp

/-- **The two-corner reducer for GHZ_n.** For any `Fin (2^n)`-indexed matrix `M`,
`⟨GHZ_n | M | GHZ_n⟩` reduces to a half-sum over the four corner entries at the two
all-equal indices `0` (all zeros) and `topIdx n` (all ones). A genuine Hilbert
computation: GHZ_n is supported on exactly `{0, topIdx n}`, each with amplitude
`(√2)⁻¹`, so the double sum collapses to the four corner terms, each carrying
`((√2)⁻¹)² = 1/2`. The `Fin (2^n)` analogue of `Empirical.GHZ.ghz_expectation_formula`
and `phiPlus_expectation_formula`. -/
theorem ghzN_expectation_corner (n : ℕ) (hn : 0 < n)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    inner ℂ (ghzN n) (Matrix.toEuclideanLin M (ghzN n))
      = (1 / 2 : ℂ) *
          (M 0 0 + M 0 (topIdx n) + M (topIdx n) 0 + M (topIdx n) (topIdx n)) := by
  rw [ghzN_eq_smul n hn, map_smul, inner_smul_left, inner_smul_right]
  simp only [map_add, inner_add_left, inner_add_right, toELin_single_coord]
  rw [show (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) = ((Real.sqrt 2 : ℂ)⁻¹) from by
        rw [starRingEnd_apply, star_inv₀, Complex.star_def, Complex.conj_ofReal],
      ← mul_assoc, inv_sqrt_two_sq]
  ring

/-! #### The tensor-Pauli operator on the bit-decomposition basis -/

/-- The bit decomposition `Fin (2^n) → (Fin n → Fin 2)` (`finFunctionFinEquiv.symm`);
`bitDecomp n k i` is the `i`-th qubit value of the computational index `k`. -/
def bitDecomp (n : ℕ) (k : Fin (2 ^ n)) : Fin n → Fin 2 := finFunctionFinEquiv.symm k

lemma finFunctionFinEquiv_allZero (n : ℕ) :
    finFunctionFinEquiv (fun _ : Fin n => (0 : Fin 2)) = 0 := by
  apply Fin.ext
  rw [finFunctionFinEquiv_apply]
  simp

lemma finFunctionFinEquiv_allOne (n : ℕ) :
    finFunctionFinEquiv (fun _ : Fin n => (1 : Fin 2)) = topIdx n := by
  apply Fin.ext
  rw [finFunctionFinEquiv_apply]
  simp only [Fin.val_one, one_mul]
  rw [sum_two_pow_fin]
  rfl

/-- The all-zeros index bit-decomposes to the all-zeros qubit string. -/
lemma bitDecomp_zero_apply (n : ℕ) (i : Fin n) : bitDecomp n 0 i = 0 := by
  rw [bitDecomp, ← finFunctionFinEquiv_allZero n, Equiv.symm_apply_apply]

/-- The all-ones index `topIdx n` bit-decomposes to the all-ones qubit string. -/
lemma bitDecomp_top_apply (n : ℕ) (i : Fin n) : bitDecomp n (topIdx n) i = 1 := by
  rw [bitDecomp, ← finFunctionFinEquiv_allOne n, Equiv.symm_apply_apply]

/-- **The `n`-fold tensor-Pauli operator** `σ·f₁ ⊗ … ⊗ σ·f_n` on `Fin (2^n)`, via the
standard product-of-factor-entries Kronecker formula on the bit-decomposition basis:
its `(r, c)` entry is `∏ i, (σ·f i)_{bit r i, bit c i}`. -/
noncomputable def tensorPauliFin (n : ℕ) (f : Fin n → DetectorSetting) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.of fun r c => ∏ i : Fin n, (pauliDot (f i)) (bitDecomp n r i) (bitDecomp n c i)

lemma tensorPauliFin_apply (n : ℕ) (f : Fin n → DetectorSetting) (r c : Fin (2 ^ n)) :
    tensorPauliFin n f r c
      = ∏ i : Fin n, (pauliDot (f i)) (bitDecomp n r i) (bitDecomp n c i) := rfl

/-! #### The single-qubit axis assignment and its Pauli entries -/

/-- The measurement axis as a `DetectorSetting`: `x ↦ chshA = (1,0,0)` (`σ_x`),
`y ↦ chshA' = (0,1,0)` (`σ_y`). -/
noncomputable def axisVec : PauliAxis → DetectorSetting
  | PauliAxis.x => chshA
  | PauliAxis.y => chshA'

/-- `(σ·axisVec ax)_{0,0} = a_z = 0` (both `σ_x`, `σ_y` are traceless, `z`-free). -/
lemma pauliDot_axisVec_00 (ax : PauliAxis) : pauliDot (axisVec ax) 0 0 = 0 := by
  cases ax <;>
    simp only [axisVec, pauliDot_apply_00, chshA_vec_ofLp_2, chshA'_vec_ofLp_2,
      Complex.ofReal_zero]

/-- `(σ·axisVec ax)_{1,1} = −a_z = 0`. -/
lemma pauliDot_axisVec_11 (ax : PauliAxis) : pauliDot (axisVec ax) 1 1 = 0 := by
  cases ax <;>
    simp only [axisVec, pauliDot_apply_11, chshA_vec_ofLp_2, chshA'_vec_ofLp_2,
      Complex.ofReal_zero, neg_zero]

/-- The `(0,1)` corner entry: `1` for `X`, `−i` for `Y` (`a_x − i a_y`). -/
lemma pauliDot_axisVec_01 (ax : PauliAxis) :
    pauliDot (axisVec ax) 0 1 = if ax = PauliAxis.y then -Complex.I else 1 := by
  cases ax
  · rw [if_neg (by decide)]
    show pauliDot chshA 0 1 = 1
    rw [pauliDot_apply_01]
    simp only [chshA_vec_ofLp_0, chshA_vec_ofLp_1, Complex.ofReal_one, Complex.ofReal_zero,
      mul_zero, sub_zero]
  · rw [if_pos rfl]
    show pauliDot chshA' 0 1 = -Complex.I
    rw [pauliDot_apply_01]
    simp only [chshA'_vec_ofLp_0, chshA'_vec_ofLp_1, Complex.ofReal_one, Complex.ofReal_zero,
      mul_one, zero_sub]

/-- The `(1,0)` corner entry: `1` for `X`, `i` for `Y` (`a_x + i a_y`). -/
lemma pauliDot_axisVec_10 (ax : PauliAxis) :
    pauliDot (axisVec ax) 1 0 = if ax = PauliAxis.y then Complex.I else 1 := by
  cases ax
  · rw [if_neg (by decide)]
    show pauliDot chshA 1 0 = 1
    rw [pauliDot_apply_10]
    simp only [chshA_vec_ofLp_0, chshA_vec_ofLp_1, Complex.ofReal_one, Complex.ofReal_zero,
      mul_zero, add_zero]
  · rw [if_pos rfl]
    show pauliDot chshA' 1 0 = Complex.I
    rw [pauliDot_apply_10]
    simp only [chshA'_vec_ofLp_0, chshA'_vec_ofLp_1, Complex.ofReal_one, Complex.ofReal_zero,
      mul_one, zero_add]

/-! #### The GHZ_n tensor-Pauli expectation and the four Mermin correlations -/

/-- **The GHZ_n tensor-Pauli expectation** for a context `c : Fin n → PauliAxis`:
`⟨GHZ_n | σ·(axisVec (c 0)) ⊗ … ⊗ σ·(axisVec (c (n−1))) | GHZ_n⟩`. -/
noncomputable def ghzNPauliExpectation (n : ℕ) (c : Fin n → PauliAxis) : ℂ :=
  inner ℂ (ghzN n)
    (Matrix.toEuclideanLin (tensorPauliFin n (fun i => axisVec (c i))) (ghzN n))

/-- **The GHZ_n expectation reduces to the two off-diagonal corner products.** For
every context of `X`/`Y` axes and every `n ≥ 1`,
`⟨GHZ_n | ⊗σ | GHZ_n⟩ = (1/2)(∏_i (σ·axisVec (c i))_{0,1} + ∏_i (σ·axisVec (c i))_{1,0})`.
The `(0,0)` and `(1,1)` corner products vanish (each factor `= a_z = 0`); the
surviving two are the `(0,1)`/`(1,0)` products. Genuine Hilbert computation via
`ghzN_expectation_corner`. -/
theorem ghzNPauliExpectation_eq (n : ℕ) (hn : 0 < n) (c : Fin n → PauliAxis) :
    ghzNPauliExpectation n c
      = (1 / 2 : ℂ) *
          ((∏ i, pauliDot (axisVec (c i)) 0 1) + (∏ i, pauliDot (axisVec (c i)) 1 0)) := by
  unfold ghzNPauliExpectation
  rw [ghzN_expectation_corner n hn, tensorPauliFin_apply, tensorPauliFin_apply,
      tensorPauliFin_apply, tensorPauliFin_apply]
  simp only [bitDecomp_zero_apply, bitDecomp_top_apply]
  rw [show (∏ i, pauliDot (axisVec (c i)) 0 0) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n)) (pauliDot_axisVec_00 _),
      show (∏ i, pauliDot (axisVec (c i)) 1 1) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n)) (pauliDot_axisVec_11 _)]
  ring

/-- **Spectator collapse.** For a context `(a on party 0, b on party 1, c on party 2,
X on every spectator party ≥ 3)` and any factor function `F` with `F x = 1`, the
full-`n` product collapses to the three essential parties: `∏_i F(ghzNCtx a b c n i)
= F a · F b · F c`, for every `n ≥ 3`. This is what makes the `n − 3` `X`-spectators
contribute `+1` and the general-`n` correlation match the three-party Mermin value. -/
lemma prod_ghzNCtx {F : PauliAxis → ℂ} (hF : F PauliAxis.x = 1)
    (a b c : PauliAxis) (n : ℕ) (hn : 3 ≤ n) :
    ∏ i : Fin n, F (ghzNCtx a b c n i) = F a * F b * F c := by
  have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) ⊆
      Finset.univ := Finset.subset_univ _
  have hrest : ∀ x ∈ (Finset.univ : Finset (Fin n)),
      x ∉ ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) →
      F (ghzNCtx a b c n x) = 1 := by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨hx0, hx1, hx2⟩ := hx
    have hv0 : x.val ≠ 0 := fun h => hx0 (Fin.ext (by simpa using h))
    have hv1 : x.val ≠ 1 := fun h => hx1 (Fin.ext (by simpa using h))
    have hv2 : x.val ≠ 2 := fun h => hx2 (Fin.ext (by simpa using h))
    unfold ghzNCtx
    rw [if_neg hv0, if_neg hv1, if_neg hv2]
    exact hF
  rw [← Finset.prod_subset hsub hrest]
  rw [Finset.prod_insert (by simp [Fin.ext_iff]), Finset.prod_insert (by simp [Fin.ext_iff]),
    Finset.prod_singleton]
  have e0 : ghzNCtx a b c n ⟨0, by omega⟩ = a := by simp [ghzNCtx]
  have e1 : ghzNCtx a b c n ⟨1, by omega⟩ = b := by simp [ghzNCtx]
  have e2 : ghzNCtx a b c n ⟨2, by omega⟩ = c := by simp [ghzNCtx]
  rw [e0, e1, e2]; ring

/-- **The GHZ_n Mermin correlation (general `n`).** For a Mermin context `(a, b, c)`
with `X`-spectators, `⟨GHZ_n | ⊗σ | GHZ_n⟩ = (1/2)(g₀₁ a · g₀₁ b · g₀₁ c
+ g₁₀ a · g₁₀ b · g₁₀ c)`, where `g₀₁ = (1, −i)` on `(X, Y)` and `g₁₀ = (1, i)`.
Derived from `ghzNPauliExpectation_eq` + `prod_ghzNCtx`, every `n ≥ 3`. -/
theorem ghzN_mermin_correlation (n : ℕ) (hn : 3 ≤ n) (a b c : PauliAxis) :
    ghzNPauliExpectation n (ghzNCtx a b c n)
      = (1 / 2 : ℂ) *
          ((if a = PauliAxis.y then -Complex.I else 1) *
             (if b = PauliAxis.y then -Complex.I else 1) *
             (if c = PauliAxis.y then -Complex.I else 1)
           + (if a = PauliAxis.y then Complex.I else 1) *
             (if b = PauliAxis.y then Complex.I else 1) *
             (if c = PauliAxis.y then Complex.I else 1)) := by
  rw [ghzNPauliExpectation_eq n (by omega) (ghzNCtx a b c n)]
  congr 1
  congr 1
  · rw [Finset.prod_congr rfl (fun i _ => pauliDot_axisVec_01 (ghzNCtx a b c n i))]
    exact prod_ghzNCtx (F := fun ax => if ax = PauliAxis.y then -Complex.I else 1)
      (by simp) a b c n hn
  · rw [Finset.prod_congr rfl (fun i _ => pauliDot_axisVec_10 (ghzNCtx a b c n i))]
    exact prod_ghzNCtx (F := fun ax => if ax = PauliAxis.y then Complex.I else 1)
      (by simp) a b c n hn

/-- **GHZ_n `⟨XXX…X⟩ = +1`** (all-`X` context, general `n ≥ 3`). Mermin identity #1,
GHZ_n's own tensor-Pauli correlation. -/
theorem ghzN_correlation_allX (n : ℕ) (hn : 3 ≤ n) :
    ghzNPauliExpectation n (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n) = 1 := by
  rw [ghzN_mermin_correlation n hn]
  simp only [if_neg (show ¬ PauliAxis.x = PauliAxis.y by decide)]
  norm_num

/-- **GHZ_n `⟨XYY…⟩ = −1`** (twisted `X,Y,Y` context, `X`-spectators, general `n ≥ 3`).
Mermin identity #2; `n_y = 2`, `cos(π) = −1`. -/
theorem ghzN_correlation_xyy (n : ℕ) (hn : 3 ≤ n) :
    ghzNPauliExpectation n (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n) = -1 := by
  rw [ghzN_mermin_correlation n hn]
  simp only [reduceIte, if_neg (show ¬ PauliAxis.x = PauliAxis.y by decide)]
  linear_combination Complex.I_mul_I

/-- **GHZ_n `⟨YXY…⟩ = −1`** (twisted `Y,X,Y` context, general `n ≥ 3`). Mermin
identity #3. -/
theorem ghzN_correlation_yxy (n : ℕ) (hn : 3 ≤ n) :
    ghzNPauliExpectation n (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n) = -1 := by
  rw [ghzN_mermin_correlation n hn]
  simp only [reduceIte, if_neg (show ¬ PauliAxis.x = PauliAxis.y by decide)]
  linear_combination Complex.I_mul_I

/-- **GHZ_n `⟨YYX…⟩ = −1`** (twisted `Y,Y,X` context, general `n ≥ 3`). Mermin
identity #4. -/
theorem ghzN_correlation_yyx (n : ℕ) (hn : 3 ≤ n) :
    ghzNPauliExpectation n (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n) = -1 := by
  rw [ghzN_mermin_correlation n hn]
  simp only [reduceIte, if_neg (show ¬ PauliAxis.x = PauliAxis.y by decide)]
  linear_combination Complex.I_mul_I

/-- **The four GHZ_n Mermin correlations, general `n ≥ 3` (the residual-closing bundle).**
`⟨XXX…⟩ = +1`, `⟨XYY…⟩ = −1`, `⟨YXY…⟩ = −1`, `⟨YYX…⟩ = −1` are GHZ_n's OWN
tensor-Pauli correlations, for every `n ≥ 3` — the four ±1 targets of
`ReproducesGHZN` / `no_lhvN_assignment_for_ghzN`. Genuine derived Hilbert
computations, not `n = 3`-anchored. -/
theorem ghzN_mermin_correlations (n : ℕ) (hn : 3 ≤ n) :
    ghzNPauliExpectation n (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n) = 1 ∧
    ghzNPauliExpectation n (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n) = -1 ∧
    ghzNPauliExpectation n (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n) = -1 ∧
    ghzNPauliExpectation n (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n) = -1 :=
  ⟨ghzN_correlation_allX n hn, ghzN_correlation_xyy n hn,
   ghzN_correlation_yxy n hn, ghzN_correlation_yyx n hn⟩

/-! #### Routing the forcing through GHZ_n's actual QM correlations -/

/-- A product partition **reproduces GHZ_n's ACTUAL QM tensor-Pauli Mermin
correlations**: its four factorisable full-`n` context-product expectations match
`(ghzNPauliExpectation n …).re`, i.e. the genuine `⟨GHZ_n | ⊗σ | GHZ_n⟩`. Unlike
`ReproducesGHZN` (bare ±1 numerals), the targets here are GHZ_n's own derived Hilbert
correlations. -/
def ReproducesGHZN_QM {Λ : Type*} [MeasurableSpace Λ] (n : ℕ) (μ : Measure Λ)
    (R : Fin n → PauliAxis → Λ → ℝ) : Prop :=
  (∫ l, ∏ i, R i (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n i) l ∂μ
      = (ghzNPauliExpectation n (ghzNCtx PauliAxis.x PauliAxis.x PauliAxis.x n)).re) ∧
  (∫ l, ∏ i, R i (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n i) l ∂μ
      = (ghzNPauliExpectation n (ghzNCtx PauliAxis.x PauliAxis.y PauliAxis.y n)).re) ∧
  (∫ l, ∏ i, R i (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n i) l ∂μ
      = (ghzNPauliExpectation n (ghzNCtx PauliAxis.y PauliAxis.x PauliAxis.y n)).re) ∧
  (∫ l, ∏ i, R i (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n i) l ∂μ
      = (ghzNPauliExpectation n (ghzNCtx PauliAxis.y PauliAxis.y PauliAxis.x n)).re)

/-- **The QM link (general `n ≥ 3`): the ±1 targets ARE GHZ_n's QM correlations.**
`ReproducesGHZN_QM n μ R ↔ ReproducesGHZN n μ R`, because GHZ_n's four tensor-Pauli
Mermin correlations are exactly `+1, −1, −1, −1` (`ghzN_mermin_correlations`). This is
the residual closure: the abstract ±1 targets of the forcing are GHZ_n's OWN QM
correlations, for every `n ≥ 3`, not just `n = 3`. -/
theorem reproducesGHZN_QM_iff {Λ : Type*} [MeasurableSpace Λ] (n : ℕ) (hn : 3 ≤ n)
    (μ : Measure Λ) (R : Fin n → PauliAxis → Λ → ℝ) :
    ReproducesGHZN_QM n μ R ↔ ReproducesGHZN n μ R := by
  unfold ReproducesGHZN_QM ReproducesGHZN
  rw [ghzN_correlation_allX n hn, ghzN_correlation_xyy n hn, ghzN_correlation_yxy n hn,
      ghzN_correlation_yyx n hn]
  norm_num

/-- **`no_product_partition_realises_ghzN_qm` (the residual-closed forcing, general
`n ≥ 3`).** No product (setting-local, non-contextual) partition of any shared
probability space reproduces GHZ_n's ACTUAL QM tensor-Pauli Mermin correlations
`⟨GHZ_n | ⊗σ | GHZ_n⟩` (the `.re` values `+1, −1, −1, −1`). Routes the LF6-E forcing
`no_product_partition_realises_ghzN` through GHZ_n's own derived QM correlations
(`reproducesGHZN_QM_iff`), so the general-`n` GHZ_n non-locality is genuinely
GHZ_n-specific and not `n = 3`-anchored. -/
theorem no_product_partition_realises_ghzN_qm {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (n : ℕ) (hn : 3 ≤ n)
    (R : Fin n → PauliAxis → Λ → ℝ)
    (hPP : IsProductPartitionGHZN n R) (hRep : ReproducesGHZN_QM n μ R) : False :=
  no_product_partition_realises_ghzN μ n R hPP ((reproducesGHZN_QM_iff n hn μ R).mp hRep)

end QMLink

end LF6
end CSD

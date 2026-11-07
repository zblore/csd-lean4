/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.LocalStochastic
public import CsdLean4.Mathlib.QuantumInfo.OverlappingRectangles
public import CsdLean4.Mathlib.QuantumInfo.PartialTrace

/-!
# The decoder between rectangles, keeping the syndrome

**Category:** 1-Mathlib (CSD-free). BACKLOG #316 (split from #314).

A level reduction inserts an ideal decoder between rectangles. The decoder that throws the syndrome
away cannot be inserted exactly: a faulty recovery can read the syndrome (BACKLOG ~~#313~~). The one
that **keeps** it can. A unitary `W` from the physical register to a logical register and a syndrome
register, `W : n ≅ m × s`, decodes by `D(ρ) = Tr_s(W ρ W†)`, and conjugating a run of rectangles by
`W` is exact: the decoded run is the run of the maps `Φ̃ⱼ = W Rectⱼ W†` on logical ⊗ syndrome,
traced over the syndrome at the end. A rectangle is **good** when `D ∘ Rect = 𝒰 ∘ D` on every
input; that is exactly the statement that its `Φ̃` acts as `𝒰` on the logical register whatever
it does to the syndrome. A bad rectangle's `Φ̃` is an arbitrary map on the logical register
**and the syndrome as its environment** — the faulty location one level down.

## The decoder

* `synDecode W ρ = Tr_s(W ρ W†)`; `liftRect W R` — `Φ̃ = W R(W† · W) W†`;
* `liftRect_comp` — lifting respects composition; ★★ `conj_ovIdeal` — **the run conjugated by `W`
  is the run of the lifted maps, exactly**; ★★ `synDecode_ovIdeal` — **the decoded run is the lifted
  run traced over the syndrome**.

## Good rectangles

* `IsGoodRect W U R` — `D(R ρ) = U D(ρ) U†` for **every** input `ρ`; `IsLogicalIdeal U Φ` —
  `Tr_s(Φ X) = U Tr_s(X) U†` for every `X` on logical ⊗ syndrome;
* ★★ `isGoodRect_iff_isLogicalIdeal` — **a rectangle is good exactly when its lift is ideal on the
  logical register**, whatever it does to the syndrome;
* `IsLogicalIdeal.comp`, ★ `isLogicalIdeal_kron_one` — `U ⊗ 1` is one (the class is not empty);
* ★★ `partialTraceRight_ovIdeal_of_isLogicalIdeal` — a run of logical-ideal maps is the ideal
  logical run after the trace;
* ★★★ `synDecode_ovIdeal_of_good` — **if every rectangle is good, the decoded run is the ideal
  logical run, on every input**.

## The join with the noise

* ★★★ `one_sub_le_measure_synDecode_eq` — **under local stochastic noise of parameter `p` with at
  most `A` malignant pairs per rectangle, if every rectangle that is not bad (#318's sequential
  badness) is good, the decoded run of `N` rectangles is the ideal logical run on every input with
  probability at least `1 − N A p²`**.

## Honest scope

⚠️ **Maps, not channels**, as in #62 (d1), #96 and #233: nothing here imposes positivity or trace
preservation on the rectangles.

⚠️ **Goodness is a hypothesis.** That a rectangle with no faulty malignant pair satisfies
`D ∘ Rect = 𝒰 ∘ D` on **every** input is code-specific; at the Steane code it is #317 (with a faulty
leading recovery) — ~~#313~~'s `steane_rect_correct_clean` gives it with a fault-free leading
recovery.

⚠️ **One level.** A bad rectangle is a map on logical ⊗ syndrome; making the next level's rectangles
good for such environment-coupled faults, and the circuit model with several blocks and classical
feed-forward, is #319.

## References

P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf. Comput. 6 (2006) 97, § 4 (the `*`-decoder that
keeps the syndrome); `Mathlib/QuantumInfo/LocalStochastic.lean` (#318),
`Mathlib/QuantumInfo/OverlappingRectangles.lean` (#233), `Mathlib/QuantumInfo/LevelReduction.lean`
(#97), `Mathlib/QuantumInfo/PartialTrace.lean`; `specs/BACKLOG.md` #316, #317, #319, #314, #315;
`specs/future-work.md`.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Kronecker ENNReal

noncomputable section

namespace QuantumInfo

variable {n m s : Type*} [Fintype n] [Fintype m] [Fintype s] [DecidableEq n]

/-! ### The decoder -/

/-- **The decoder that discards the syndrome**: `D(ρ) = Tr_s(W ρ W†)`. -/
def synDecode (W : Matrix (m × s) n ℂ) (ρ : Matrix n n ℂ) : Matrix m m ℂ :=
  partialTraceRight (W * ρ * Wᴴ)

/-- **A rectangle read on logical ⊗ syndrome**: `Φ̃(X) = W R(W† X W) W†`. -/
def liftRect (W : Matrix (m × s) n ℂ) (R : Matrix n n ℂ → Matrix n n ℂ)
    (X : Matrix (m × s) (m × s) ℂ) : Matrix (m × s) (m × s) ℂ :=
  W * R (Wᴴ * X * W) * Wᴴ

/-- Lifting respects composition when `W` is an isometry. -/
theorem liftRect_comp {W : Matrix (m × s) n ℂ} (hW : Wᴴ * W = 1)
    (R₁ R₂ : Matrix n n ℂ → Matrix n n ℂ) (X : Matrix (m × s) (m × s) ℂ) :
    liftRect W (R₂ ∘ R₁) X = liftRect W R₂ (liftRect W R₁ X) := by
  simp only [liftRect, Function.comp]
  congr 3
  calc R₁ (Wᴴ * X * W) = (Wᴴ * W) * R₁ (Wᴴ * X * W) * (Wᴴ * W) := by
        rw [hW, Matrix.one_mul, Matrix.mul_one]
    _ = Wᴴ * (W * R₁ (Wᴴ * X * W) * Wᴴ) * W := by simp only [Matrix.mul_assoc]

/-- ★★ **The run conjugated by `W` is the run of the lifted maps, exactly.** -/
theorem conj_ovIdeal {W : Matrix (m × s) n ℂ} (hW : Wᴴ * W = 1)
    (R : ℕ → Matrix n n ℂ → Matrix n n ℂ) :
    ∀ (N : ℕ) (ρ : Matrix n n ℂ),
      W * ovIdeal R N ρ * Wᴴ = ovIdeal (fun j => liftRect W (R j)) N (W * ρ * Wᴴ)
  | 0, ρ => rfl
  | N + 1, ρ => by
    rw [ovIdeal_succ, ovIdeal_succ, ← conj_ovIdeal hW R N ρ, liftRect]
    congr 3
    calc ovIdeal R N ρ = (Wᴴ * W) * ovIdeal R N ρ * (Wᴴ * W) := by
          rw [hW, Matrix.one_mul, Matrix.mul_one]
      _ = Wᴴ * (W * ovIdeal R N ρ * Wᴴ) * W := by simp only [Matrix.mul_assoc]

/-- ★★ **The decoded run is the lifted run traced over the syndrome**: a run of rectangles, decoded,
is a run on logical ⊗ syndrome — the faults one level down, coupled to the syndrome. -/
theorem synDecode_ovIdeal {W : Matrix (m × s) n ℂ} (hW : Wᴴ * W = 1)
    (R : ℕ → Matrix n n ℂ → Matrix n n ℂ) (N : ℕ) (ρ : Matrix n n ℂ) :
    synDecode W (ovIdeal R N ρ)
      = partialTraceRight (ovIdeal (fun j => liftRect W (R j)) N (W * ρ * Wᴴ)) := by
  rw [synDecode, conj_ovIdeal hW]

/-! ### Good rectangles -/

/-- **A good rectangle**: `D(R ρ) = U D(ρ) U†` for every input `ρ`. -/
def IsGoodRect (W : Matrix (m × s) n ℂ) (U : Matrix m m ℂ) (R : Matrix n n ℂ → Matrix n n ℂ) :
    Prop :=
  ∀ ρ, synDecode W (R ρ) = U * synDecode W ρ * Uᴴ

/-- **A map on logical ⊗ syndrome that is ideal on the logical register**:
`Tr_s(Φ X) = U Tr_s(X) U†` for every `X`, whatever it does to the syndrome. -/
def IsLogicalIdeal (U : Matrix m m ℂ)
    (Φ : Matrix (m × s) (m × s) ℂ → Matrix (m × s) (m × s) ℂ) : Prop :=
  ∀ X, partialTraceRight (Φ X) = U * partialTraceRight X * Uᴴ

/-- ★★ **A rectangle is good exactly when its lift is ideal on the logical register.** -/
theorem isGoodRect_iff_isLogicalIdeal [DecidableEq m] [DecidableEq s] {W : Matrix (m × s) n ℂ}
    (hW : Wᴴ * W = 1)
    (hW' : W * Wᴴ = 1) (U : Matrix m m ℂ) (R : Matrix n n ℂ → Matrix n n ℂ) :
    IsGoodRect W U R ↔ IsLogicalIdeal U (liftRect W R) := by
  constructor
  · intro h X
    have hX : W * (Wᴴ * X * W) * Wᴴ = X := by
      calc W * (Wᴴ * X * W) * Wᴴ = (W * Wᴴ) * X * (W * Wᴴ) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hW', Matrix.one_mul, Matrix.mul_one]
    have := h (Wᴴ * X * W)
    rw [synDecode, synDecode, hX] at this
    exact this
  · intro h ρ
    have hρ : Wᴴ * (W * ρ * Wᴴ) * W = ρ := by
      calc Wᴴ * (W * ρ * Wᴴ) * W = (Wᴴ * W) * ρ * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
        _ = ρ := by rw [hW, Matrix.one_mul, Matrix.mul_one]
    have := h (W * ρ * Wᴴ)
    rw [liftRect, hρ] at this
    exact this

/-- Logical-ideal maps compose. -/
theorem IsLogicalIdeal.comp {U V : Matrix m m ℂ}
    {Φ Ψ : Matrix (m × s) (m × s) ℂ → Matrix (m × s) (m × s) ℂ} (hΦ : IsLogicalIdeal U Φ)
    (hΨ : IsLogicalIdeal V Ψ) : IsLogicalIdeal (V * U) (Ψ ∘ Φ) := by
  intro X
  simp only [Function.comp, hΨ (Φ X), hΦ X, conjTranspose_mul, Matrix.mul_assoc]

/-- ★ **`U ⊗ 1` is ideal on the logical register**: the class is not empty. -/
theorem isLogicalIdeal_kron_one [DecidableEq s] (U : Matrix m m ℂ) :
    IsLogicalIdeal U fun X => (U ⊗ₖ (1 : Matrix s s ℂ)) * X * (U ⊗ₖ (1 : Matrix s s ℂ))ᴴ := by
  intro X
  ext i j
  simp only [partialTraceRight_apply, Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite (star : ℂ → ℂ), star_zero, mul_ite,
    ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/-- ★★ **A run of logical-ideal maps is the ideal logical run after the trace.** -/
theorem partialTraceRight_ovIdeal_of_isLogicalIdeal {U : ℕ → Matrix m m ℂ}
    {Φ : ℕ → Matrix (m × s) (m × s) ℂ → Matrix (m × s) (m × s) ℂ} {N : ℕ}
    (h : ∀ j < N, IsLogicalIdeal (U j) (Φ j)) :
    ∀ k ≤ N, ∀ X, partialTraceRight (ovIdeal Φ k X)
      = ovIdeal (fun j Y => U j * Y * (U j)ᴴ) k (partialTraceRight X)
  | 0, _, X => rfl
  | k + 1, hk, X => by
    rw [ovIdeal_succ, ovIdeal_succ, h k (by omega),
      partialTraceRight_ovIdeal_of_isLogicalIdeal h k (by omega) X]

/-- ★★★ **If every rectangle is good, the decoded run is the ideal logical run, on every input.** -/
theorem synDecode_ovIdeal_of_good [DecidableEq m] [DecidableEq s] {W : Matrix (m × s) n ℂ}
    (hW : Wᴴ * W = 1)
    (hW' : W * Wᴴ = 1) {U : ℕ → Matrix m m ℂ} {R : ℕ → Matrix n n ℂ → Matrix n n ℂ} {N : ℕ}
    (h : ∀ j < N, IsGoodRect W (U j) (R j)) (ρ : Matrix n n ℂ) :
    synDecode W (ovIdeal R N ρ) = ovIdeal (fun j Y => U j * Y * (U j)ᴴ) N (synDecode W ρ) := by
  rw [synDecode_ovIdeal hW, partialTraceRight_ovIdeal_of_isLogicalIdeal
    (fun j hj => (isGoodRect_iff_isLogicalIdeal hW hW' (U j) (R j)).1 (h j hj)) N le_rfl]
  rfl

/-! ### The join with the noise -/

/-- ★★★ **The decoded run is ideal with probability at least `1 − N A p²`.** Under local stochastic
noise of parameter `p` on the locations `ι`, with the rectangles' sequential badness given by a
chain `C` of at most `A` malignant pairs each (#318): if every rectangle that is not bad is good,
the decoded run of `N` rectangles is the ideal logical run, on every input, with probability at
least `1 − N A p²`. -/
theorem one_sub_le_measure_synDecode_eq [DecidableEq m] [DecidableEq s] {ι : Type*} [DecidableEq ι]
    {W : Matrix (m × s) n ℂ} (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1) {U : ℕ → Matrix m m ℂ}
    (R : (ι → Bool) → ℕ → Matrix n n ℂ → Matrix n n ℂ) (C : RectChain ι)
    {μ : Measure (ι → Bool)} [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hμ : IsLocalStochastic μ p)
    {A : ℕ} (hA : ∀ j, (C.M j).card ≤ A) {N : ℕ}
    (hgood : ∀ ω, ∀ j < N, C.badSeq ω j = false → IsGoodRect W (U j) (R ω j)) :
    1 - (N : ℝ≥0∞) * ((A : ℝ≥0∞) * p ^ 2)
      ≤ μ {ω | (fun ρ => synDecode W (ovIdeal (R ω) N ρ))
          = fun ρ => ovIdeal (fun j Y => U j * Y * (U j)ᴴ) N (synDecode W ρ)} := by
  refine one_sub_le_measure_output_eq μ (fun j : Fin N => {ω | C.badSeq ω j = true})
    (fun ω hω => funext fun ρ => synDecode_ovIdeal_of_good hW hW' (fun j hj => ?_) ρ)
    (fun j => ?_)
  · refine hgood ω j hj ?_
    have := hω ⟨j, hj⟩
    simpa using this
  · have h := C.measure_forall_badSeq_le hμ hA {(j : ℕ)}
    rw [Finset.card_singleton, pow_one] at h
    refine (measure_mono fun ω hω => ?_).trans h
    intro j' hj'
    rw [Finset.mem_singleton.1 hj']
    exact hω

end QuantumInfo

end

import CsdLean4.LF3.Projectors.Core

/-!
# LF3 Projectors / SectorVolume: operator-form sector volume and bounds

**Category:** 3-Local (LF3 operator-form sector volume `Re ⟨Ψ, M_{st} Ψ⟩` and strong-readout / finite-leakage bounds).

Paper §5.10 / §9.7. (Renamed from `BranchWeight` in Phase 11, 2026-05-18,
to align with the volume-ratios reading: each `w_{st}(Ψ) = Re ⟨Ψ, M_{st} Ψ⟩`
is the volume of the post-measurement state on the `(s, t)` eigensector, a
volume in projective amplitude space — not an Everettian branch count.)

Defines the operator-form sector volume `w_{st}(Ψ) = Re ⟨Ψ, M_{st} Ψ⟩` and
proves two quantitative results against the squared amplitude `‖cAmp s t‖²`:

- `sectorVolume_strong_readout`: exact equality in the strong-readout limit
  (zero leakage); both sector states and pointer-sector projectors match
  cleanly through the `StrongReadoutCompat` structural compatibility data.
- `sectorVolume_finite_leakage`: an `εA + εB + εA·εB` bound parameterised by
  a `LeakageCompat` quantitative compatibility datum.

Both theorems take a structural-compatibility hypothesis linking the
projector algebra `P` to the sector states produced by `M`. In a future v2
with a concrete tensor decomposition of `H_SA`, the compatibility data would
be derivable from the decomposition; in v1.00 it is taken as data, mirroring
the design pattern used for `ProjectorAlgebra` and `MeasurementUnitary`.
-/

open scoped BigOperators ComplexConjugate

namespace CSD
namespace LF3

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
  {S : SystemApparatusSetup K_A K_B H_SA}

/-- Strong-readout structural compatibility (paper §5 / spec §9.7).

Connects the abstract pointer-sector projectors `mHat P s t` to the branch
states produced by the measurement unitary `M`. In a future v2 derived from
a concrete tensor decomposition; in v1.00 taken as data. -/
structure StrongReadoutCompat (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) where
  /-- Branch states are unit-norm. -/
  sectorNorm : ∀ s t, ‖sectorState M s t φA0 φB0‖ = 1
  /-- Distinct sector states are pairwise orthogonal under the inner product. -/
  sectorOrth : ∀ s t s' t', (s, t) ≠ (s', t') →
    inner ℂ (sectorState M s t φA0 φB0) (sectorState M s' t' φA0 φB0) = (0 : ℂ)
  /-- `mHat P s t` preserves the matching sector state. -/
  mHatDiag   : ∀ s t,
    mHat P s t (sectorState M s t φA0 φB0) = sectorState M s t φA0 φB0
  /-- `mHat P s t` annihilates sector states with mismatched labels. -/
  mHatOff    : ∀ s t s' t', (s', t') ≠ (s, t) →
    mHat P s t (sectorState M s' t' φA0 φB0) = 0

/-- Operator-form branch weight `w_{st}(Ψ) = Re ⟨Ψ, M_{st} Ψ⟩` (paper §5.6). -/
noncomputable def sectorVolume
    (P : ProjectorAlgebra S) (Ψ : H_SA) (s t : Sign) : ℝ :=
  RCLike.re (inner ℂ Ψ (mHat P s t Ψ))

/-! ### Strong-readout branch weight (paper §5.10) -/

/-- Applying `mHat P s t` to the four-term branch sum collapses to the single
    matching branch term, given strong-readout compatibility. -/
lemma mHat_finalState
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (cAmp : Sign → Sign → ℂ)
    (compat : StrongReadoutCompat P M φA0 φB0) (s t : Sign) :
    mHat P s t (finalState M cAmp φA0 φB0)
      = cAmp s t • sectorState M s t φA0 φB0 := by
  unfold finalState
  rw [map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single (s, t)]
  · show cAmp s t • mHat P s t (sectorState M s t φA0 φB0)
          = cAmp s t • sectorState M s t φA0 φB0
    rw [compat.mHatDiag s t]
  · intro st' _ hne
    show cAmp st'.1 st'.2 • mHat P s t (sectorState M st'.1 st'.2 φA0 φB0) = 0
    rw [compat.mHatOff s t st'.1 st'.2 hne, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Inner product of `finalState` with a single sector state collapses to the
    matching complex-conjugate amplitude, by orthogonality of sector states
    and unit-norm normalisation. -/
lemma inner_finalState_sectorState
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (cAmp : Sign → Sign → ℂ)
    (compat : StrongReadoutCompat P M φA0 φB0) (s t : Sign) :
    inner ℂ (finalState M cAmp φA0 φB0) (sectorState M s t φA0 φB0)
      = conj (cAmp s t) := by
  unfold finalState
  rw [sum_inner]
  rw [Finset.sum_eq_single (s, t)]
  · show inner ℂ (cAmp s t • sectorState M s t φA0 φB0)
                (sectorState M s t φA0 φB0)
          = conj (cAmp s t)
    rw [inner_smul_left]
    have h_ip : inner ℂ (sectorState M s t φA0 φB0)
                       (sectorState M s t φA0 φB0) = (1 : ℂ) := by
      rw [@inner_self_eq_norm_sq_to_K ℂ _ _ _, compat.sectorNorm s t]
      push_cast; ring
    rw [h_ip, mul_one]
  · intro st' _ hne
    show inner ℂ (cAmp st'.1 st'.2 • sectorState M st'.1 st'.2 φA0 φB0)
                (sectorState M s t φA0 φB0)
          = 0
    rw [inner_smul_left]
    rw [compat.sectorOrth st'.1 st'.2 s t hne]
    rw [mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Strong-readout limit (paper §5.10): the branch weight is exactly the
    Born probability of the singlet amplitude. Both compatibility data and
    the explicit `Ψ_T := finalState M cAmp φA0 φB0` substitution come in
    explicitly; the proof reduces to `‖cAmp s t‖² = z * conj z` via the
    branch-orthogonality and pointer-diagonality fields. -/
theorem sectorVolume_strong_readout
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (cAmp : Sign → Sign → ℂ)
    (compat : StrongReadoutCompat P M φA0 φB0) (s t : Sign) :
    sectorVolume P (finalState M cAmp φA0 φB0) s t = ‖cAmp s t‖ ^ 2 := by
  unfold sectorVolume
  rw [mHat_finalState P M φA0 φB0 cAmp compat s t]
  rw [inner_smul_right]
  rw [inner_finalState_sectorState P M φA0 φB0 cAmp compat s t]
  -- goal: re (cAmp s t * conj (cAmp s t)) = ‖cAmp s t‖^2
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact RCLike.ofReal_re _

/-! ### Finite-leakage branch weight (paper §5.11) -/

/-- Quantitative leakage compatibility (paper §5.11 / spec §9.7).

Bounds the deviation of the branch weight from `‖cAmp s t‖²` in absolute
terms by `εA + εB + εA·εB`. The per-side leakage parameters and the bound
itself enter as fields; the underlying Cauchy–Schwarz / per-sector overlap
argument is packaged here as a v1.00 structural-data interface (spec §9.7
/ §9.11), to be derived in v2 from a concrete tensor decomposition.

**V ≈ 1 − I disclosure.** `εA` and `εB` are stipulated stability parameters,
not derived from any physical isolation quantity `I`. The bound
`εA + εB + εA·εB` matches the V ≈ 1 − I phenomenology to leading order, but
the link from the per-side leakages to an underlying isolation parameter is
not formalised in this v1.00 module. Carries the V ≈ 1 − I structural debt
explicitly: the leakage Compat is honest as a stability statement (any caller
supplying `εA, εB` and discharging `sectorVolume_dev` obtains the bound), but
deriving `εA, εB` from first principles is open and not currently scheduled
in the Lean tree. -/
structure LeakageCompat (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) where
  /-- A-wing leakage parameter. -/
  εA : ℝ
  /-- B-wing leakage parameter. -/
  εB : ℝ
  /-- The A-wing leakage parameter is non-negative. -/
  εA_nn : 0 ≤ εA
  /-- The B-wing leakage parameter is non-negative. -/
  εB_nn : 0 ≤ εB
  /-- **Caller-supplied bound (data field, not a derivation).** The
      quantitative deviation of the branch weight from `‖cAmp s t‖²`,
      bounded by `εA + εB + εA·εB` for every `(s, t)`. This field
      *packages* the per-sector Cauchy-Schwarz / overlap argument as
      a v1.00 structural interface (spec §9.7 / §9.11); the bound is
      not derived inside this module. A v2 (and concretely a v2 with
      a Kähler-instantiated `SectorData`) will derive it from a
      concrete tensor decomposition and turn this field into a proved
      lemma. -/
  sectorVolume_dev :
    ∀ (cAmp : Sign → Sign → ℂ) (s t : Sign),
      |RCLike.re (inner ℂ (finalState M cAmp φA0 φB0)
                          (mHat P s t (finalState M cAmp φA0 φB0)))
       - ‖cAmp s t‖ ^ 2|
        ≤ εA + εB + εA * εB

/-- Finite-leakage bound (paper §5.11): the branch weight deviates from the
    Born probability by at most `εA + εB + εA·εB`. v1.00 packages the
    Cauchy–Schwarz / per-sector overlap argument as a field of `LeakageCompat`
    (spec §9.7 / §9.11 / §10.3); a future v2 derives it from a concrete tensor
    decomposition. -/
theorem sectorVolume_finite_leakage
    (P : ProjectorAlgebra S) (M : MeasurementUnitary S)
    (φA0 : K_A) (φB0 : K_B) (cAmp : Sign → Sign → ℂ)
    (L : LeakageCompat P M φA0 φB0) (s t : Sign) :
    |sectorVolume P (finalState M cAmp φA0 φB0) s t - ‖cAmp s t‖ ^ 2|
      ≤ L.εA + L.εB + L.εA * L.εB := by
  unfold sectorVolume
  exact L.sectorVolume_dev cAmp s t

end LF3
end CSD

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# A lattice Dirac chain carrying an internal clock

**Category:** 3-Local (CV). BACKLOG #249 (residue of ~~#241~~; the author's fourth operational-geometry
brief).

~~#241~~ built the control: a device moving by its own momentum, its clock decoupled from its motion,
and so Galilean by construction. This module builds the test candidate (B) of the fourth brief's
amendment: a **lattice Dirac chain**, whose dispersion is relativistic at small momenta, carrying a
device with **two internal levels** — an atomic clock, its ticks the beat between the levels.

**A correction to the row as opened.** #249 first named the oscillation *between the two bands* as
the clock. That beat runs at `2E/ħ`, which grows with momentum: it is the opposite of dilation. The
right clock is an internal two-level device of rest energies `μ₀ < μ₁` carried by the same mode, whose
beat `E_{μ₁}(k) − E_{μ₀}(k)` is slowed by `1/γ`. That is what is proved here.

## The dispersion and the clock (units `ħ = 1`, lattice spacing `1`)

* `dispE` (`E = √(μ² + s²)`), `vRel` (the relativistic velocity `c s / E`), `levelClockRate`
  (`E₁ − E₀`); `dispE_sq`, `dispE_pos`, `le_dispE`, `abs_le_dispE`, `clockRate_zero` (at rest the
  splitting of the rest energies), `vRel_div_eq`, `sq_vRel_div_le_one`;
* ★ `div_dispE_eq_sqrt` — **`μ / E = √(1 − (v/c)²)` exactly**; ★ `abs_vRel_lt` — `|v| < c`;
  `div_dispE_mono`;
* ★★ `clockRate_mem` — **the moving clock's rate lies between `(μ₁ − μ₀)` times its two levels'
  dilation factors**; ★★★ `abs_clockRate_div_sub_le` — **time dilation with its error**: the rate
  relative to the rest rate is `√(1 − (v/c)²)` within `(μ₁ − μ₀)/E₀`.

## The lattice

* ★ `hasDerivAt_dispE_lattice` — **the group velocity** of `s = 2J sin k` is the relativistic
  velocity times `cos k`; ★★ `lattice_dilation_defect` — **the preferred frame**: the squared dilation
  factors read from the group velocity and from the relativistic velocity differ by
  `(v/c)² sin² k ≤ sin² k`; `abs_groupVel_le` — no mode outruns `c = 2J`.

## The chain

* `diracSx`, `diracSz`, ★★ `diracHam` — **the Hamiltonian on a ring of `L` sites**,
  `−iJ (|j⟩⟨j+1| − |j⟩⟨j−1|) ⊗ σ_x + μ σ_z`, every term on one site or one edge;
  `diracHam_apply_eq_zero` (locality), ★ `diracHam_isHermitian`;
* `latticeAngle`, `planeWave`, `planeWave_add_one`, `planeWave_sub_one`, `hop_factor`, `modeS`,
  `diracMode` — the plane wave of momentum `n` times `(μ + E, s)`; ★★ `diracHam_mulVec_diracMode` —
  **the modes are exact eigenvectors**; ★ `hasDerivAt_diracMode` — **each solves Schrödinger's
  equation by its phase**; ★★ `clock_phase` — the two levels' relative phase advances at the clock's
  rate;
* ★★★ `dirac_clock_chain` — the package.

## The finding

On this lattice the internal clock's rate, normalised by its rest rate, lies within
`(μ₁ − μ₀)/E₀` of `√(1 − (v_rel/c)²)`, where `v_rel = cs/E` is the mode's **defined** relativistic
velocity — derived from the dispersion, not assumed, but not one exact dilation factor. Measured
against the **group velocity**, the velocity an observer would actually read, the squared factors
differ by `(v_rel/c)² sin² k ≤ sin² k`, a preferred-frame effect. At fixed `J` and `μ` it vanishes as
`k → 0` only together with the velocity; the controlled limit at nonzero physical momentum
(`J = c/(2a)`, `k = ap`, `a → 0`) is [`DiracContinuum.lean`](DiracContinuum.lean).

## Honest scope

⚠️ **Modes, not a localised device.** Plane waves are exact eigenvectors but spread over the ring; a
localised packet moving at the group velocity with a spreading bound, and its position read from
local records, are #250.

⚠️ **The internal levels are two copies of the chain** with rest energies `μ₀`, `μ₁` and the same `J`;
a clock whose levels couple to each other, or to the motion beyond the rest energy, is not treated.

⚠️ **The evolution is stated as Schrödinger's equation solved by the mode's phase**; its identity with
`exp (−itH)` is the uniqueness of that linear equation, not re-proved here.

⚠️ **No observer reads this clock yet**; #242's transported clock and #243's two observers on this
chain wait on #250.

References: P. Dirac (1928); R. P. Feynman, A. R. Hibbs (1965) §2-6 (the checkerboard); M. Zych,
F. Costa, I. Pikovski, Č. Brukner, Nat. Commun. 2 (2011) 505 (internal clocks under mass–energy
equivalence); `specs/BACKLOG.md` #249, #250, #241, #242, #243, #247, #213, #39;
`RecordLayer/MovingClock.lean`, `CV/LocalLiebRobinson.lean`.
-/

@[expose] public section

open Matrix Complex

noncomputable section

namespace CSD.CV

/-! ### The dispersion and the clock's rate -/

/-- **The band energy** `E = √(μ² + s²)` of a mode of rest energy `μ` and lattice momentum term `s`. -/
def dispE (μ s : ℝ) : ℝ := Real.sqrt (μ ^ 2 + s ^ 2)

/-- **The relativistic velocity of the mode**, `c s / E`: the velocity a continuum particle with the
same energy and momentum `s / c` would have. -/
def vRel (c μ s : ℝ) : ℝ := c * s / dispE μ s

/-- **The internal clock's rate** at a given momentum: the energy splitting of the two internal
levels of rest energies `μ₀`, `μ₁`. -/
def levelClockRate (μ₀ μ₁ s : ℝ) : ℝ := dispE μ₁ s - dispE μ₀ s

theorem dispE_sq (μ s : ℝ) : dispE μ s ^ 2 = μ ^ 2 + s ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem dispE_pos {μ : ℝ} (hμ : 0 < μ) (s : ℝ) : 0 < dispE μ s :=
  Real.sqrt_pos.2 (by nlinarith [pow_pos hμ 2, sq_nonneg s])

theorem le_dispE (μ s : ℝ) : μ ≤ dispE μ s :=
  Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])

theorem abs_le_dispE (μ s : ℝ) : |s| ≤ dispE μ s := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg μ])

/-- At rest the clock ticks at the splitting of the rest energies. -/
theorem clockRate_zero {μ₀ μ₁ : ℝ} (h0 : 0 ≤ μ₀) (h1 : 0 ≤ μ₁) : levelClockRate μ₀ μ₁ 0 = μ₁ - μ₀ := by
  simp [levelClockRate, dispE, Real.sqrt_sq h0, Real.sqrt_sq h1]

/-- ★ **The dilation factor is the relativistic one exactly**: `μ / E = √(1 − (v/c)²)`. -/
theorem div_dispE_eq_sqrt {c μ : ℝ} (hc : c ≠ 0) (hμ : 0 < μ) (s : ℝ) :
    μ / dispE μ s = Real.sqrt (1 - (vRel c μ s / c) ^ 2) := by
  have hE := dispE_pos hμ s
  have hv : vRel c μ s / c = s / dispE μ s := by
    rw [vRel]
    field_simp
  rw [hv, show 1 - (s / dispE μ s) ^ 2 = (μ / dispE μ s) ^ 2 by
    field_simp
    nlinarith [dispE_sq μ s], Real.sqrt_sq (div_nonneg hμ.le hE.le)]

theorem vRel_div_eq {c μ : ℝ} (hc : c ≠ 0) (hμ : 0 < μ) (s : ℝ) :
    vRel c μ s / c = s / dispE μ s := by
  have hE := dispE_pos hμ s
  rw [vRel]
  field_simp

theorem sq_vRel_div_le_one {c μ : ℝ} (hc : c ≠ 0) (hμ : 0 < μ) (s : ℝ) :
    (vRel c μ s / c) ^ 2 ≤ 1 := by
  have hE := dispE_pos hμ s
  rw [vRel_div_eq hc hμ, div_pow, div_le_one (by positivity), ← sq_abs s]
  have := abs_le_dispE μ s
  nlinarith [abs_nonneg s]

/-- **The relativistic velocity stays below `c`.** -/
theorem abs_vRel_lt {c μ : ℝ} (hc : 0 < c) (hμ : 0 < μ) (s : ℝ) : |vRel c μ s| < c := by
  have hE := dispE_pos hμ s
  have hs : |s| < dispE μ s := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  rw [vRel, abs_div, abs_mul, abs_of_pos hc, abs_of_pos hE, div_lt_iff₀ hE]
  nlinarith

/-- A heavier level has the larger factor `μ / E`. -/
theorem div_dispE_mono {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (s : ℝ) :
    μ₀ / dispE μ₀ s ≤ μ₁ / dispE μ₁ s := by
  have hE0 := dispE_pos h0 s
  have hE1 := dispE_pos (h0.trans_le h01) s
  rw [div_le_div_iff₀ hE0 hE1]
  have h := Real.sqrt_le_sqrt (show μ₀ ^ 2 * (μ₁ ^ 2 + s ^ 2) ≤ μ₁ ^ 2 * (μ₀ ^ 2 + s ^ 2) by
    nlinarith [sq_nonneg s, mul_le_mul h01 h01 h0.le (h0.le.trans h01)])
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h0.le,
    Real.sqrt_sq (h0.le.trans h01)] at h
  exact h

/-- ★★ **The moving clock is slowed by the relativistic factor, between its two levels' values**:
`(μ₁ − μ₀) μ₀/E₀ ≤ E₁ − E₀ ≤ (μ₁ − μ₀) μ₁/E₁`. -/
theorem clockRate_mem {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (s : ℝ) :
    (μ₁ - μ₀) * (μ₀ / dispE μ₀ s) ≤ levelClockRate μ₀ μ₁ s
      ∧ levelClockRate μ₀ μ₁ s ≤ (μ₁ - μ₀) * (μ₁ / dispE μ₁ s) := by
  have h1 : 0 < μ₁ := h0.trans_le h01
  have hE0 := dispE_pos h0 s
  have hE1 := dispE_pos h1 s
  have hdiff : levelClockRate μ₀ μ₁ s * (dispE μ₁ s + dispE μ₀ s) = (μ₁ - μ₀) * (μ₁ + μ₀) := by
    rw [levelClockRate]
    nlinarith [dispE_sq μ₀ s, dispE_sq μ₁ s]
  have hmono := div_dispE_mono h0 h01 s
  rw [div_le_div_iff₀ hE0 hE1] at hmono
  have hsum : 0 < dispE μ₁ s + dispE μ₀ s := by linarith
  have hd : 0 ≤ μ₁ - μ₀ := by linarith
  have hcr : levelClockRate μ₀ μ₁ s = (μ₁ - μ₀) * (μ₁ + μ₀) / (dispE μ₁ s + dispE μ₀ s) := by
    rw [eq_div_iff hsum.ne', hdiff]
  rw [hcr]
  constructor
  · rw [le_div_iff₀ hsum, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hd
    rw [div_mul_eq_mul_div, div_le_iff₀ hE0]
    nlinarith
  · rw [div_le_iff₀ hsum, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hd
    rw [div_mul_eq_mul_div, le_div_iff₀ hE1]
    nlinarith

/-- ★★★ **Time dilation of the internal clock, with its error**: the clock's rate relative to its
rest rate is `√(1 − (v/c)²)` at the lower level, within `(μ₁ − μ₀) / E₀`. -/
theorem abs_clockRate_div_sub_le {c μ₀ μ₁ : ℝ} (hc : c ≠ 0) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (s : ℝ) :
    |levelClockRate μ₀ μ₁ s / (μ₁ - μ₀) - Real.sqrt (1 - (vRel c μ₀ s / c) ^ 2)|
      ≤ (μ₁ - μ₀) / dispE μ₀ s := by
  have hd : 0 < μ₁ - μ₀ := by linarith
  have hE0 := dispE_pos h0 s
  have hE1 := dispE_pos (h0.trans h01) s
  obtain ⟨hlo, hhi⟩ := clockRate_mem h0 h01.le s
  rw [← div_dispE_eq_sqrt hc h0 s]
  have hlo' : μ₀ / dispE μ₀ s ≤ levelClockRate μ₀ μ₁ s / (μ₁ - μ₀) := by
    rw [le_div_iff₀ hd]; linarith
  have hhi' : levelClockRate μ₀ μ₁ s / (μ₁ - μ₀) ≤ μ₁ / dispE μ₁ s := by
    rw [div_le_iff₀ hd]; linarith
  have hE01 : dispE μ₀ s ≤ dispE μ₁ s :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h1 : μ₁ / dispE μ₁ s ≤ μ₁ / dispE μ₀ s :=
    div_le_div_of_nonneg_left (by linarith) hE0 hE01
  rw [abs_of_nonneg (by linarith)]
  calc levelClockRate μ₀ μ₁ s / (μ₁ - μ₀) - μ₀ / dispE μ₀ s ≤ μ₁ / dispE μ₀ s - μ₀ / dispE μ₀ s := by
        linarith
    _ = (μ₁ - μ₀) / dispE μ₀ s := by ring

/-! ### The lattice: group velocity and the preferred frame -/

/-- **The group velocity on the lattice** of hop amplitude `J`: `dE/dk` for `s = 2J sin k`. -/
theorem hasDerivAt_dispE_lattice {J μ : ℝ} (hμ : 0 < μ) (k : ℝ) :
    HasDerivAt (fun k => dispE μ (2 * J * Real.sin k))
      (vRel (2 * J) μ (2 * J * Real.sin k) * Real.cos k) k := by
  have hE := dispE_pos hμ (2 * J * Real.sin k)
  have hin : HasDerivAt (fun k => μ ^ 2 + (2 * J * Real.sin k) ^ 2)
      (2 * (2 * J * Real.sin k) * (2 * J * Real.cos k)) k := by
    have := ((Real.hasDerivAt_sin k).const_mul (2 * J)).pow 2
    simpa using this.const_add (μ ^ 2)
  have h := hin.sqrt (by positivity)
  unfold dispE vRel dispE
  convert h using 1
  rw [← dispE]
  field_simp

/-- ★★ **The lattice's preferred frame**: the measured group velocity is the relativistic velocity
times `cos k`, so the squared dilation factors read from the two differ by `(v/c)² sin² k ≤ sin² k`. -/
theorem lattice_dilation_defect {J μ : ℝ} (hJ : J ≠ 0) (hμ : 0 < μ) (k : ℝ) :
    (1 - (vRel (2 * J) μ (2 * J * Real.sin k) * Real.cos k / (2 * J)) ^ 2)
        - (1 - (vRel (2 * J) μ (2 * J * Real.sin k) / (2 * J)) ^ 2)
      = (vRel (2 * J) μ (2 * J * Real.sin k) / (2 * J)) ^ 2 * Real.sin k ^ 2
    ∧ (vRel (2 * J) μ (2 * J * Real.sin k) / (2 * J)) ^ 2 * Real.sin k ^ 2 ≤ Real.sin k ^ 2 := by
  have hc : (2 * J) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · have h := Real.sin_sq_add_cos_sq k
    have hw : vRel (2 * J) μ (2 * J * Real.sin k) * Real.cos k / (2 * J)
        = vRel (2 * J) μ (2 * J * Real.sin k) / (2 * J) * Real.cos k := by ring
    rw [hw]
    linear_combination (-(vRel (2 * J) μ (2 * J * Real.sin k) / (2 * J)) ^ 2) * h
  · have hv : (vRel (2 * J) μ (2 * J * Real.sin k) / (2 * J)) ^ 2 ≤ 1 :=
      sq_vRel_div_le_one hc hμ _
    nlinarith [sq_nonneg (Real.sin k)]

/-- **No mode outruns `c = 2J`**: the group velocity is at most `c` in size. -/
theorem abs_groupVel_le {J μ : ℝ} (hμ : 0 < μ) (k : ℝ) :
    |vRel (2 * J) μ (2 * J * Real.sin k) * Real.cos k| ≤ |2 * J| := by
  have hE := dispE_pos hμ (2 * J * Real.sin k)
  have hs := abs_le_dispE μ (2 * J * Real.sin k)
  rw [vRel, abs_mul, abs_div, abs_mul, abs_of_pos hE]
  have hcos := Real.abs_cos_le_one k
  calc |2 * J| * |2 * J * Real.sin k| / dispE μ (2 * J * Real.sin k) * |Real.cos k|
      ≤ |2 * J| * 1 * 1 := by
        refine mul_le_mul ?_ hcos (abs_nonneg _) (by positivity)
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left ((div_le_one hE).2 hs) (abs_nonneg _)
    _ = |2 * J| := by ring

/-! ### The chain and its modes -/

/-- `σ_x`, the hop between the two components. -/
def diracSx : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- `σ_z`, the mass term. -/
def diracSz : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

variable {L : ℕ} [NeZero L]

/-- ★★ **The lattice Dirac Hamiltonian** on a ring of `L` sites, two components per site: the hop
`−iJ (|j⟩⟨j+1| − |j⟩⟨j−1|) ⊗ σ_x` on each edge and the rest energy `μ σ_z` on each site. Every term
acts on one site or one edge. -/
def diracHam (J μ : ℝ) : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ := Matrix.of fun p q =>
  (J : ℂ) * (-I) * ((if q.1 = p.1 + 1 then 1 else 0) - (if q.1 = p.1 - 1 then 1 else 0))
      * diracSx p.2 q.2
    + (μ : ℂ) * (if q.1 = p.1 then 1 else 0) * diracSz p.2 q.2

omit [NeZero L] in
/-- **Locality**: the Hamiltonian couples a site only to itself and its two neighbours. -/
theorem diracHam_apply_eq_zero (J μ : ℝ) {p q : ZMod L × Fin 2}
    (h : q.1 ≠ p.1 + 1 ∧ q.1 ≠ p.1 - 1 ∧ q.1 ≠ p.1) : diracHam J μ p q = 0 := by
  simp [diracHam, h.1, h.2.1, h.2.2]

omit [NeZero L] in
/-- ★ **The Hamiltonian is Hermitian.** -/
theorem diracHam_isHermitian (J μ : ℝ) : Matrix.IsHermitian (diracHam (L := L) J μ) := by
  ext ⟨j, a⟩ ⟨j', b⟩
  simp only [Matrix.conjTranspose_apply, diracHam, Matrix.of_apply]
  have e1 : (j = j' + 1) = (j' = j - 1) :=
    propext ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩
  have e2 : (j = j' - 1) = (j' = j + 1) :=
    propext ⟨fun h => by rw [h]; ring, fun h => by rw [h]; ring⟩
  have e3 : (j = j') = (j' = j) := propext eq_comm
  simp only [e1, e2, e3]
  fin_cases a <;> fin_cases b <;> simp [diracSx, diracSz] <;> split_ifs <;> simp

/-- The site angle of momentum `n`: `θ_n = 2π n / L`. -/
def latticeAngle (n : ZMod L) : ℝ := 2 * Real.pi * n.val / L

/-- The plane wave of momentum `n`. -/
def planeWave (n j : ZMod L) : ℂ := (ZMod.toCircle (n * j) : ℂ)

theorem planeWave_add_one (n j : ZMod L) :
    planeWave n (j + 1) = planeWave n j * Complex.exp (latticeAngle n * I) := by
  rw [planeWave, planeWave, mul_add, mul_one, AddChar.map_add_eq_mul, Circle.coe_mul]
  congr 1
  rw [ZMod.toCircle_apply, latticeAngle]
  congr 1
  push_cast
  ring

theorem planeWave_sub_one (n j : ZMod L) :
    planeWave n (j - 1) = planeWave n j * Complex.exp ((-latticeAngle n : ℝ) * I) := by
  have h := planeWave_add_one n (j - 1)
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, ← Complex.exp_add,
    show (latticeAngle n : ℂ) * I + ((-latticeAngle n : ℝ) : ℂ) * I = 0 by push_cast; ring,
    Complex.exp_zero, mul_one]

theorem hop_factor (J θ : ℝ) :
    (J : ℂ) * (-I) * (Complex.exp (θ * I) - Complex.exp ((-θ : ℝ) * I))
      = ((2 * J * Real.sin θ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The lattice momentum term of mode `n`: `s_n = 2J sin θ_n`. -/
def modeS (J : ℝ) (n : ZMod L) : ℝ := 2 * J * Real.sin (latticeAngle n)

/-- **The mode of momentum `n` in the upper band**: the plane wave times `(μ + E, s)`. -/
def diracMode (J μ : ℝ) (n : ZMod L) : ZMod L × Fin 2 → ℂ := fun p =>
  planeWave n p.1 * (if p.2 = 0 then ((μ + dispE μ (modeS J n) : ℝ) : ℂ) else (modeS J n : ℂ))

/-- ★★ **The modes are exact eigenvectors**: `H ψ_n = E_n ψ_n` with `E_n = √(μ² + (2J sin θ_n)²)`. -/
theorem diracHam_mulVec_diracMode (J μ : ℝ) (n : ZMod L) :
    diracHam J μ *ᵥ diracMode J μ n = (dispE μ (modeS J n) : ℂ) • diracMode J μ n := by
  have hE2 : ((dispE μ (modeS J n) : ℝ) : ℂ) ^ 2 = (μ : ℂ) ^ 2 + (modeS J n : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, dispE_sq]
    push_cast
    ring
  have hhop : (J : ℂ) * (-I) * (Complex.exp (latticeAngle n * I)
      - Complex.exp ((-latticeAngle n : ℝ) * I)) = (modeS J n : ℂ) := by
    rw [modeS]
    exact hop_factor J (latticeAngle n)
  funext ⟨j, a⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, diracHam, diracMode, Matrix.of_apply,
    Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  simp only [mul_sub, sub_mul, add_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  fin_cases a
  · simp [diracSx, diracSz, planeWave_add_one, planeWave_sub_one]
    push_cast at hhop ⊢
    simp only [neg_mul] at hhop ⊢
    linear_combination (planeWave n j * (modeS J n : ℂ)) * hhop + (-planeWave n j) * hE2
  · simp [diracSx, diracSz, planeWave_add_one, planeWave_sub_one]
    push_cast at hhop ⊢
    simp only [neg_mul] at hhop ⊢
    linear_combination (planeWave n j * ((μ : ℂ) + (dispE μ (modeS J n) : ℂ))) * hhop

/-- ★ **The mode evolves by its phase**: `ψ(t) = e^{−iE t} ψ_n` solves `i ψ' = H ψ`. -/
theorem hasDerivAt_diracMode (J μ : ℝ) (n : ZMod L) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(I * dispE μ (modeS J n)) * t) • diracMode J μ n)
      ((-I) • (diracHam J μ *ᵥ (Complex.exp (-(I * dispE μ (modeS J n)) * t)
        • diracMode J μ n))) t := by
  set E : ℂ := (dispE μ (modeS J n) : ℂ)
  have h1 : HasDerivAt (fun t : ℝ => -(I * E) * (t : ℂ)) (-(I * E)) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(I * E))
  have h2 := (h1.cexp).smul_const (diracMode J μ n)
  convert h2 using 1
  rw [Matrix.mulVec_smul, diracHam_mulVec_diracMode, smul_smul, smul_smul]
  congr 1
  ring

/-- ★★ **The internal clock's phase**: carried by the mode `n` in two internal levels of rest energies
`μ₀`, `μ₁`, the relative phase after `t` is `e^{−i (E₁ − E₀) t}`, the clock's rate times `t`. -/
theorem clock_phase (μ₀ μ₁ s t : ℝ) :
    Complex.exp (-(I * dispE μ₁ s) * t) * (Complex.exp (-(I * dispE μ₀ s) * t))⁻¹
      = Complex.exp (-(I * levelClockRate μ₀ μ₁ s) * t) := by
  rw [← Complex.exp_neg, ← Complex.exp_add, levelClockRate]
  congr 1
  push_cast
  ring

/-- ★★★ **A moving clock on a lattice Dirac chain (#249).** On a ring of `L` sites with hop `J ≠ 0`, a
device with two internal levels of rest energies `0 < μ₀ < μ₁` in the upper-band mode of momentum
`n`: the Hamiltonian is Hermitian and local; the modes are exact eigenvectors in both levels; the
clock's phase advances at `E₁ − E₀`; that rate is slowed by the relativistic factor
`√(1 − (v/c)²)`, `c = 2J`, within `(μ₁ − μ₀)/E₀`, and lies between the two levels' factors; the
group velocity is the relativistic velocity times `cos θ`, never above `c`, and the squared dilation
factors read from the two velocities differ by `(v/c)² sin² θ` — the lattice's preferred frame. -/
theorem dirac_clock_chain {J μ₀ μ₁ : ℝ} (hJ : J ≠ 0) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (n : ZMod L) :
    Matrix.IsHermitian (diracHam (L := L) J μ₀)
    ∧ diracHam J μ₀ *ᵥ diracMode J μ₀ n = (dispE μ₀ (modeS J n) : ℂ) • diracMode J μ₀ n
    ∧ diracHam J μ₁ *ᵥ diracMode J μ₁ n = (dispE μ₁ (modeS J n) : ℂ) • diracMode J μ₁ n
    ∧ (∀ t : ℝ, Complex.exp (-(I * dispE μ₁ (modeS J n)) * t)
        * (Complex.exp (-(I * dispE μ₀ (modeS J n)) * t))⁻¹
          = Complex.exp (-(I * levelClockRate μ₀ μ₁ (modeS J n)) * t))
    ∧ ((μ₁ - μ₀) * (μ₀ / dispE μ₀ (modeS J n)) ≤ levelClockRate μ₀ μ₁ (modeS J n)
        ∧ levelClockRate μ₀ μ₁ (modeS J n) ≤ (μ₁ - μ₀) * (μ₁ / dispE μ₁ (modeS J n)))
    ∧ |levelClockRate μ₀ μ₁ (modeS J n) / (μ₁ - μ₀)
        - Real.sqrt (1 - (vRel (2 * J) μ₀ (modeS J n) / (2 * J)) ^ 2)|
        ≤ (μ₁ - μ₀) / dispE μ₀ (modeS J n)
    ∧ HasDerivAt (fun k => dispE μ₀ (2 * J * Real.sin k))
        (vRel (2 * J) μ₀ (modeS J n) * Real.cos (latticeAngle n)) (latticeAngle n)
    ∧ |vRel (2 * J) μ₀ (modeS J n) * Real.cos (latticeAngle n)| ≤ |2 * J|
    ∧ (1 - (vRel (2 * J) μ₀ (modeS J n) * Real.cos (latticeAngle n) / (2 * J)) ^ 2)
          - (1 - (vRel (2 * J) μ₀ (modeS J n) / (2 * J)) ^ 2)
        = (vRel (2 * J) μ₀ (modeS J n) / (2 * J)) ^ 2 * Real.sin (latticeAngle n) ^ 2 :=
  ⟨diracHam_isHermitian J μ₀, diracHam_mulVec_diracMode J μ₀ n, diracHam_mulVec_diracMode J μ₁ n,
    clock_phase μ₀ μ₁ (modeS J n), clockRate_mem h0 h01.le _,
    abs_clockRate_div_sub_le (by positivity) h0 h01 _, hasDerivAt_dispE_lattice h0 _,
    abs_groupVel_le h0 _, (lattice_dilation_defect hJ h0 _).1⟩

end CSD.CV

end

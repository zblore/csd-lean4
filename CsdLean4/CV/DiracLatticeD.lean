/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracClockChain
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The lattice Dirac Hamiltonian in `d` dimensions

**Category:** 3-Local (CV). BACKLOG #294 (split of #289; milestone M7 of the author's programme
"From `Σ` to physical spacetime", obligation UO-17; `specs/beyond-1p1-scoping.md` §3.3).

[`DiracClockChain.lean`](DiracClockChain.lean) (~~#249~~) is the chain in one space dimension:
sites `ZMod L`, two components, hop `σ_x`, mass term `σ_z`. This module is the same Hamiltonian
on the torus `ι → ZMod L` of any finite set `ι` of axes, with spinors in any finite type `S`,
for any **Clifford family**: Hermitian matrices `α_i` (`i : ι`) and `β` on `S`, each squaring to
one, any two of them anticommuting.

## The Clifford computation

* `IsCliffordFamily`, `cliffordSymbol` (`H(s) = Σ_i s_i α_i + μ β`);
* ★★ `cliffordSymbol_mul_self` — **`H(s)² = (μ² + Σ_i s_i²) · 1`**, from the relations alone;
  `mul_cliffordSymbol_add` (`β H(s) + H(s) β = 2μ`);
* `sNorm` (`|s| = √(Σ_i s_i²)`), `dispE_sNorm_sq` (`E² = μ² + Σ_i s_i²` for `E = dispE μ |s|`);
* ★ `cliffordSymbol_mulVec_mode` — **`(H(s) + E) e₀` is an eigenvector of `H(s)` at `E`**, for
  every spinor `e₀`; ★ `cliffordMode_ne_zero` — it is nonzero when `β e₀ = e₀ ≠ 0` and `μ > 0`.

## The lattice

* ★★ `latticeDiracHam` — **the Hamiltonian on `(ι → ZMod L) × S`**: on each edge along axis `i`
  the hop `−iJ (|x⟩⟨x + e_i| − |x⟩⟨x − e_i|) ⊗ α_i`, on each site `μ β`;
  `latticeDiracHam_apply_eq_zero` (locality: a site couples to itself and its `2 |ι|`
  neighbours), ★ `latticeDiracHam_isHermitian`;
* `planeWaveD`, `planeWaveD_add_single`, `planeWaveD_sub_single`, `planeWaveD_ne_zero`,
  `spinorWave`, `modeSD` (`s_i = 2J sin θ_{n_i}`);
* ★★ `latticeDiracHam_mulVec_spinorWave` — **on a plane wave the Hamiltonian acts on the spinor
  by its symbol**: `H (e^{i n·x} u) = e^{i n·x} (H(s) u)`;
* `diracModeD`, ★★★ `latticeDiracHam_mulVec_diracModeD` — **the modes are exact eigenvectors**
  with `E = √(μ² + Σ_i (2J sin θ_{n_i})²)`; `diracModeD_ne_zero`.

## Instances

* `diracSy`, `pauli`, `pauli_isHermitian`, `pauli_mul_self`, `pauli_anticomm`;
* `cliffordOne` (`d = 1`: `σ_x`; `σ_z`), ★ `cliffordTwo` (`d = 2`: `σ_x`, `σ_y`; `σ_z`, two
  components), ★★ `cliffordThree` (`d = 3`: `σ_x ⊗ σ_i`; `σ_z ⊗ 1`, four components);
* `latticeDiracHam_one` — at `d = 1` with `cliffordOne` the Hamiltonian is `diracHam`, entry by
  entry.

## The package

* ★★★ `lattice_dirac_d` — for a Clifford family, `0 < μ₀ < μ₁`, `J ≠ 0` and a momentum
  `n : ι → ZMod L`: Hermitian; the modes of both levels exact eigenvectors and nonzero; the
  energy `E` with `E² = μ² + Σ_i s_i²`; the clock's rate `E₁ − E₀` relative to its rest rate
  within `(μ₁ − μ₀)/E₀` of `√(1 − (v/c)²)`, `c = 2J`, `v = c |s|/E₀`
  (`abs_clockRate_div_sub_le` at `s := |s|`).

## Honest scope

⚠️ **Modes, not packets.** The plane waves are spread over the torus. Packets are #296.

⚠️ **`v = c |s| / E` is the defined relativistic speed**, a number. The group velocity as a
vector, its dependence on the direction at order `(a p)²` and the bound `|v_g| ≤ c` are #295.

⚠️ **Doublers.** `s_i = 2J sin θ` vanishes at `θ = π` as well as at `θ = 0`, on each axis. The
theorems here hold at every momentum and do not remove the `2^d − 1` doublers (#299, optional).

⚠️ **No record is read here**, and nothing is on the unified arena of UA-18. The detector and
record modules on this lattice are #297; the `d + 1` statement is #298.

⚠️ **The internal levels are two copies of the lattice** with rest energies `μ₀`, `μ₁`, as in
`DiracClockChain.lean`.

References: P. Dirac (1928); `specs/beyond-1p1-scoping.md`; `specs/BACKLOG.md` #294, #295, #296,
#297, #298, #299, ~~#249~~, ~~#292~~, ~~#293~~; `specs/unified-record-spacetime-plan.md` (UO-17,
UD-206); `CV/DiracClockChain.lean` (`diracHam`, `diracHam_mulVec_diracMode`, `dispE`,
`abs_clockRate_div_sub_le`); `RecordLayer/LorentzKinematics.lean`;
`RecordLayer/RadarTrilateration.lean`; `specs/future-work.md`.
-/

@[expose] public section

open Matrix Complex

open scoped Kronecker

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]

/-! ### The Clifford computation -/

/-- A **Clifford family**: Hermitian matrices `α_i` and `β`, each squaring to one, any two of
them anticommuting. -/
structure IsCliffordFamily (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ) : Prop where
  isHermitian_α : ∀ i, (α i).IsHermitian
  isHermitian_β : β.IsHermitian
  α_mul_self : ∀ i, α i * α i = 1
  β_mul_self : β * β = 1
  α_anticomm : ∀ i j, i ≠ j → α i * α j + α j * α i = 0
  α_β_anticomm : ∀ i, α i * β + β * α i = 0

/-- The symbol `H(s) = Σ_i s_i α_i + μ β`. -/
def cliffordSymbol (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ) (s : ι → ℝ) (μ : ℝ) :
    Matrix S S ℂ :=
  ∑ i, (s i : ℂ) • α i + (μ : ℂ) • β

/-- `|s| = √(Σ_i s_i²)`. -/
def sNorm (s : ι → ℝ) : ℝ := Real.sqrt (∑ i, s i ^ 2)

omit [DecidableEq ι] in
theorem dispE_sNorm_sq (μ : ℝ) (s : ι → ℝ) : dispE μ (sNorm s) ^ 2 = μ ^ 2 + ∑ i, s i ^ 2 := by
  rw [dispE_sq, sNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (s i))]

variable {α : ι → Matrix S S ℂ} {β : Matrix S S ℂ}

/-- ★★ **`H(s)² = (μ² + Σ_i s_i²) · 1`**, from the Clifford relations. -/
theorem cliffordSymbol_mul_self (h : IsCliffordFamily α β) (s : ι → ℝ) (μ : ℝ) :
    cliffordSymbol α β s μ * cliffordSymbol α β s μ
      = ((μ ^ 2 + ∑ i, s i ^ 2 : ℝ) : ℂ) • (1 : Matrix S S ℂ) := by
  have key : ∀ i j, ((s i : ℂ) • α i) * ((s j : ℂ) • α j) + ((s j : ℂ) • α j) * ((s i : ℂ) • α i)
      = if i = j then ((2 * s i ^ 2 : ℝ) : ℂ) • (1 : Matrix S S ℂ) else 0 := by
    intro i j
    rw [smul_mul_smul_comm, smul_mul_smul_comm]
    split_ifs with hij
    · subst hij
      rw [h.α_mul_self, ← add_smul]
      congr 1
      push_cast
      ring
    · rw [mul_comm (s j : ℂ), ← smul_add, h.α_anticomm i j hij, smul_zero]
  have hAA : (∑ i, (s i : ℂ) • α i) * (∑ i, (s i : ℂ) • α i)
      = ((∑ i, s i ^ 2 : ℝ) : ℂ) • (1 : Matrix S S ℂ) := by
    have e : (∑ i, (s i : ℂ) • α i) * (∑ i, (s i : ℂ) • α i)
        = ∑ i, ∑ j, ((s i : ℂ) • α i) * ((s j : ℂ) • α j) := Finset.sum_mul_sum _ _ _ _
    have c : ∑ i, ∑ j, ((s i : ℂ) • α i) * ((s j : ℂ) • α j)
        = ∑ i, ∑ j, ((s j : ℂ) • α j) * ((s i : ℂ) • α i) := Finset.sum_comm
    have two : (2 : ℂ) • ((∑ i, (s i : ℂ) • α i) * (∑ i, (s i : ℂ) • α i))
        = (2 : ℂ) • (((∑ i, s i ^ 2 : ℝ) : ℂ) • (1 : Matrix S S ℂ)) := by
      rw [two_smul]
      nth_rewrite 2 [e]
      rw [c, e, ← Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib, key, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← Finset.sum_smul, smul_smul]
      congr 1
      push_cast
      rw [Finset.mul_sum]
    exact smul_right_injective _ (two_ne_zero) two
  have hAB : (∑ i, (s i : ℂ) • α i) * ((μ : ℂ) • β) + ((μ : ℂ) • β) * (∑ i, (s i : ℂ) • α i)
      = 0 := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (μ : ℂ), ← smul_add, h.α_β_anticomm,
      smul_zero]
  have regroup : ∀ a b c d : Matrix S S ℂ, a + b + (c + d) = a + (b + c) + d := by
    intro a b c d
    abel
  unfold cliffordSymbol
  rw [add_mul, mul_add, mul_add, hAA, smul_mul_smul_comm, h.β_mul_self, regroup, hAB, add_zero,
    ← add_smul]
  congr 1
  push_cast
  ring

omit [DecidableEq ι] in
/-- `β H(s) + H(s) β = 2μ`. -/
theorem mul_cliffordSymbol_add (h : IsCliffordFamily α β) (s : ι → ℝ) (μ : ℝ) :
    β * cliffordSymbol α β s μ + cliffordSymbol α β s μ * β
      = ((2 * μ : ℝ) : ℂ) • (1 : Matrix S S ℂ) := by
  have hs : β * (∑ i, (s i : ℂ) • α i) + (∑ i, (s i : ℂ) • α i) * β = 0 := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, add_comm, h.α_β_anticomm, smul_zero]
  have regroup : ∀ a b c d : Matrix S S ℂ, a + b + (c + d) = (a + c) + (b + d) := by
    intro a b c d
    abel
  unfold cliffordSymbol
  rw [mul_add, add_mul, regroup, hs, zero_add, mul_smul_comm, smul_mul_assoc, h.β_mul_self,
    ← add_smul]
  congr 1
  push_cast
  ring

/-- ★ **`(H(s) + E) e₀` is an eigenvector of `H(s)` at `E = √(μ² + |s|²)`**, for every spinor
`e₀`. -/
theorem cliffordSymbol_mulVec_mode (h : IsCliffordFamily α β) (s : ι → ℝ) (μ : ℝ)
    (e₀ : S → ℂ) :
    cliffordSymbol α β s μ *ᵥ
        ((cliffordSymbol α β s μ + (dispE μ (sNorm s) : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀)
      = (dispE μ (sNorm s) : ℂ)
        • ((cliffordSymbol α β s μ + (dispE μ (sNorm s) : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀) := by
  have hE : ((μ ^ 2 + ∑ i, s i ^ 2 : ℝ) : ℂ)
      = (dispE μ (sNorm s) : ℂ) * (dispE μ (sNorm s) : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, dispE_sNorm_sq]
  rw [Matrix.mulVec_mulVec, mul_add, cliffordSymbol_mul_self h, mul_smul_comm, mul_one, hE,
    ← Matrix.smul_mulVec, smul_add, smul_smul, add_comm]

omit [DecidableEq ι] in
/-- ★ **The mode's spinor is nonzero** when `e₀` is a nonzero spinor of positive rest energy,
`β e₀ = e₀`, and `μ > 0`. -/
theorem cliffordMode_ne_zero (h : IsCliffordFamily α β) (s : ι → ℝ) {μ : ℝ} (hμ : 0 < μ)
    {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (h0 : e₀ ≠ 0) :
    (cliffordSymbol α β s μ + (dispE μ (sNorm s) : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀ ≠ 0 := by
  intro hz
  have hM : cliffordSymbol α β s μ *ᵥ e₀ = -((dispE μ (sNorm s) : ℂ) • e₀) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hz
    exact eq_neg_of_add_eq_zero_left hz
  have hanti := congrArg (fun A : Matrix S S ℂ => A *ᵥ e₀) (mul_cliffordSymbol_add h s μ)
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, he, hM, Matrix.mulVec_neg,
    Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.one_mulVec] at hanti
  have hsum : ((2 * (μ + dispE μ (sNorm s)) : ℝ) : ℂ) • e₀ = 0 := by
    have e : ((2 * (μ + dispE μ (sNorm s)) : ℝ) : ℂ) • e₀
        = ((2 * μ : ℝ) : ℂ) • e₀
          - (-((dispE μ (sNorm s) : ℂ) • e₀) + -((dispE μ (sNorm s) : ℂ) • e₀)) := by
      rw [← neg_add, sub_neg_eq_add, ← add_smul, ← add_smul]
      congr 1
      push_cast
      ring
    rw [e, hanti, sub_self]
  have hpos : (0 : ℝ) < 2 * (μ + dispE μ (sNorm s)) := by
    have := le_dispE μ (sNorm s)
    linarith
  exact h0 ((smul_eq_zero.1 hsum).resolve_left (Complex.ofReal_ne_zero.2 hpos.ne'))

/-! ### The lattice -/

variable {L : ℕ} [NeZero L]

/-- ★★ **The lattice Dirac Hamiltonian** on the torus `ι → ZMod L`, spinors in `S`: on each
edge along axis `i` the hop `−iJ (|x⟩⟨x + e_i| − |x⟩⟨x − e_i|) ⊗ α_i`, on each site `μ β`. -/
def latticeDiracHam (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ) (J μ : ℝ) :
    Matrix ((ι → ZMod L) × S) ((ι → ZMod L) × S) ℂ := Matrix.of fun p q =>
  ∑ i, (J : ℂ) * (-I)
      * ((if q.1 = p.1 + Pi.single i 1 then 1 else 0)
        - (if q.1 = p.1 - Pi.single i 1 then 1 else 0)) * α i p.2 q.2
    + (μ : ℂ) * (if q.1 = p.1 then 1 else 0) * β p.2 q.2

omit [NeZero L] [Fintype S] [DecidableEq S] in
/-- **Locality**: the Hamiltonian couples a site only to itself and its neighbours along the
axes. -/
theorem latticeDiracHam_apply_eq_zero (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ) (J μ : ℝ)
    {p q : (ι → ZMod L) × S}
    (h1 : ∀ i, q.1 ≠ p.1 + Pi.single i 1 ∧ q.1 ≠ p.1 - Pi.single i 1) (h0 : q.1 ≠ p.1) :
    latticeDiracHam α β J μ p q = 0 := by
  have a := fun i => (h1 i).1
  have b := fun i => (h1 i).2
  simp [latticeDiracHam, h0, a, b]

omit [NeZero L] in
/-- ★ **The Hamiltonian is Hermitian.** -/
theorem latticeDiracHam_isHermitian (h : IsCliffordFamily α β) (J μ : ℝ) :
    Matrix.IsHermitian (latticeDiracHam (L := L) α β J μ) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [Matrix.conjTranspose_apply, latticeDiracHam, Matrix.of_apply]
  have hβ : star (β b a) = β a b := by
    have := congrFun (congrFun h.isHermitian_β a) b
    simpa [Matrix.conjTranspose_apply] using this
  rw [star_add, star_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hα : star (α i b a) = α i a b := by
      have := congrFun (congrFun (h.isHermitian_α i) a) b
      simpa [Matrix.conjTranspose_apply] using this
    have e1 : (x = y + Pi.single i 1) = (y = x - Pi.single i 1) :=
      propext ⟨fun h => by rw [h]; abel, fun h => by rw [h]; abel⟩
    have e2 : (x = y - Pi.single i 1) = (y = x + Pi.single i 1) :=
      propext ⟨fun h => by rw [h]; abel, fun h => by rw [h]; abel⟩
    simp only [e1, e2]
    rw [star_mul', hα]
    congr 1
    split_ifs <;> simp
  · have e3 : (x = y) = (y = x) := propext eq_comm
    simp only [e3]
    rw [star_mul', hβ]
    congr 1
    split_ifs <;> simp

/-- The plane wave of momentum `n` on the torus: the product of the axes' plane waves. -/
def planeWaveD (n x : ι → ZMod L) : ℂ := ∏ i, planeWave (n i) (x i)

theorem planeWaveD_add_single (n x : ι → ZMod L) (i : ι) :
    planeWaveD n (x + Pi.single i 1)
      = planeWaveD n x * Complex.exp (latticeAngle (n i) * I) := by
  unfold planeWaveD
  have hj : ∀ j, planeWave (n j) ((x + Pi.single i 1 : ι → ZMod L) j)
      = planeWave (n j) (x j) * (if j = i then Complex.exp (latticeAngle (n i) * I) else 1) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [planeWave_add_one]
    · simp [hji]
  simp only [hj, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem planeWaveD_sub_single (n x : ι → ZMod L) (i : ι) :
    planeWaveD n (x - Pi.single i 1)
      = planeWaveD n x * Complex.exp ((-latticeAngle (n i) : ℝ) * I) := by
  unfold planeWaveD
  have hj : ∀ j, planeWave (n j) ((x - Pi.single i 1 : ι → ZMod L) j)
      = planeWave (n j) (x j)
        * (if j = i then Complex.exp ((-latticeAngle (n i) : ℝ) * I) else 1) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [planeWave_sub_one]
    · simp [hji]
  simp only [hj, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

omit [DecidableEq ι] in
theorem planeWaveD_ne_zero (n x : ι → ZMod L) : planeWaveD n x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => Circle.coe_ne_zero _

/-- A plane wave of momentum `n` carrying the spinor `u`. -/
def spinorWave (n : ι → ZMod L) (u : S → ℂ) : (ι → ZMod L) × S → ℂ := fun p =>
  planeWaveD n p.1 * u p.2

/-- The lattice momentum terms of the mode `n`: `s_i = 2J sin θ_{n_i}`. -/
def modeSD (J : ℝ) (n : ι → ZMod L) : ι → ℝ := fun i => modeS J (n i)

omit [DecidableEq S] in
/-- ★★ **On a plane wave the Hamiltonian acts on the spinor by its symbol.** -/
theorem latticeDiracHam_mulVec_spinorWave (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ)
    (J μ : ℝ) (n : ι → ZMod L) (u : S → ℂ) :
    latticeDiracHam α β J μ *ᵥ spinorWave n u
      = spinorWave n (cliffordSymbol α β (modeSD J n) μ *ᵥ u) := by
  funext ⟨x, a⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, latticeDiracHam, spinorWave,
    Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hterm : ∀ y : ι → ZMod L,
      (∑ i, (J : ℂ) * (-I)
          * ((if y = x + Pi.single i 1 then 1 else 0)
            - (if y = x - Pi.single i 1 then 1 else 0)) * α i a b
        + (μ : ℂ) * (if y = x then 1 else 0) * β a b) * (planeWaveD n y * u b)
      = ∑ i, ((J : ℂ) * (-I) * α i a b * u b)
          * ((if y = x + Pi.single i 1 then planeWaveD n y else 0)
            - (if y = x - Pi.single i 1 then planeWaveD n y else 0))
        + ((μ : ℂ) * β a b * u b) * (if y = x then planeWaveD n y else 0) := by
    intro y
    rw [add_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    · split_ifs <;> ring
  simp only [hterm, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, planeWaveD_add_single, planeWaveD_sub_single, cliffordSymbol, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, modeSD, modeS]
  rw [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (planeWaveD n x * α i a b * u b) * hop_factor J (latticeAngle (n i))
  · ring

/-- **The mode of momentum `n` in the upper band** built on the spinor `e₀`: the plane wave
times `(H(s) + E) e₀`. -/
def diracModeD (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ) (J μ : ℝ) (n : ι → ZMod L)
    (e₀ : S → ℂ) : (ι → ZMod L) × S → ℂ :=
  spinorWave n ((cliffordSymbol α β (modeSD J n) μ
    + (dispE μ (sNorm (modeSD J n)) : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀)

/-- ★★★ **The modes are exact eigenvectors**: `H ψ_n = E_n ψ_n` with
`E_n = √(μ² + Σ_i (2J sin θ_{n_i})²)`. -/
theorem latticeDiracHam_mulVec_diracModeD (h : IsCliffordFamily α β) (J μ : ℝ)
    (n : ι → ZMod L) (e₀ : S → ℂ) :
    latticeDiracHam α β J μ *ᵥ diracModeD α β J μ n e₀
      = (dispE μ (sNorm (modeSD J n)) : ℂ) • diracModeD α β J μ n e₀ := by
  unfold diracModeD
  rw [latticeDiracHam_mulVec_spinorWave, cliffordSymbol_mulVec_mode h]
  funext p
  simp only [spinorWave, Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq ι] in
/-- **The mode is a nonzero vector** when `β e₀ = e₀ ≠ 0` and `μ > 0`. -/
theorem diracModeD_ne_zero (h : IsCliffordFamily α β) (J : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (n : ι → ZMod L) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (h0 : e₀ ≠ 0) :
    diracModeD α β J μ n e₀ ≠ 0 := by
  intro hz
  refine cliffordMode_ne_zero h (modeSD J n) hμ he h0 (funext fun a => ?_)
  have := congrFun hz ((0 : ι → ZMod L), a)
  simp only [diracModeD, spinorWave, Pi.zero_apply, mul_eq_zero] at this
  exact this.resolve_left (planeWaveD_ne_zero n 0)

/-! ### Instances -/

/-- `σ_y`. -/
def diracSy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The three Pauli matrices. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![diracSx, diracSy, diracSz]

theorem pauli_isHermitian (i : Fin 3) : (pauli i).IsHermitian := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [pauli, diracSx, diracSy, diracSz, Matrix.conjTranspose_apply]

theorem pauli_mul_self (i : Fin 3) : pauli i * pauli i = 1 := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [pauli, diracSx, diracSy, diracSz, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_anticomm {i j : Fin 3} (hij : i ≠ j) : pauli i * pauli j + pauli j * pauli i = 0 := by
  ext a b
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | (fin_cases a <;> fin_cases b <;>
        simp [pauli, diracSx, diracSy, diracSz])

/-- **`d = 1`**: `σ_x` with `σ_z`, the family of `DiracClockChain.lean`. -/
theorem cliffordOne : IsCliffordFamily (fun _ : Fin 1 => pauli 0) (pauli 2) where
  isHermitian_α _ := pauli_isHermitian 0
  isHermitian_β := pauli_isHermitian 2
  α_mul_self _ := pauli_mul_self 0
  β_mul_self := pauli_mul_self 2
  α_anticomm i j hij := absurd (Subsingleton.elim i j) hij
  α_β_anticomm _ := pauli_anticomm (by decide)

/-- ★ **`d = 2`**: `σ_x`, `σ_y` with `σ_z`; two components. -/
theorem cliffordTwo : IsCliffordFamily (fun i : Fin 2 => pauli i.castSucc) (pauli 2) where
  isHermitian_α i := pauli_isHermitian _
  isHermitian_β := pauli_isHermitian 2
  α_mul_self i := pauli_mul_self _
  β_mul_self := pauli_mul_self 2
  α_anticomm i j hij := pauli_anticomm fun h => hij (Fin.castSucc_injective _ h)
  α_β_anticomm i := pauli_anticomm (by fin_cases i <;> decide)

/-- ★★ **`d = 3`**: `σ_x ⊗ σ_i` with `σ_z ⊗ 1`; four components. -/
theorem cliffordThree :
    IsCliffordFamily (fun i : Fin 3 => pauli 0 ⊗ₖ pauli i)
      (pauli 2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) where
  isHermitian_α i := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (pauli_isHermitian 0).eq,
      (pauli_isHermitian i).eq]
  isHermitian_β := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (pauli_isHermitian 2).eq,
      Matrix.conjTranspose_one]
  α_mul_self i := by
    rw [← Matrix.mul_kronecker_mul, pauli_mul_self, pauli_mul_self, Matrix.one_kronecker_one]
  β_mul_self := by
    rw [← Matrix.mul_kronecker_mul, pauli_mul_self, mul_one, Matrix.one_kronecker_one]
  α_anticomm i j hij := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.kronecker_add,
      pauli_anticomm hij, Matrix.kronecker_zero]
  α_β_anticomm i := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
      ← Matrix.add_kronecker, pauli_anticomm (by decide), Matrix.zero_kronecker]

omit [NeZero L] in
/-- **At `d = 1` the Hamiltonian is the chain's**, entry by entry. -/
theorem latticeDiracHam_one (J μ : ℝ) (x y : Fin 1 → ZMod L) (a b : Fin 2) :
    latticeDiracHam (fun _ : Fin 1 => pauli 0) (pauli 2) J μ (x, a) (y, b)
      = diracHam J μ (x 0, a) (y 0, b) := by
  have e1 : (y = x + Pi.single 0 1) = (y 0 = x 0 + 1) :=
    propext ⟨fun h => by rw [h]; simp, fun h => by
      funext i
      fin_cases i
      simpa using h⟩
  have e2 : (y = x - Pi.single 0 1) = (y 0 = x 0 - 1) :=
    propext ⟨fun h => by rw [h]; simp, fun h => by
      funext i
      fin_cases i
      simpa using h⟩
  have e3 : (y = x) = (y 0 = x 0) :=
    propext ⟨fun h => by rw [h], fun h => by
      funext i
      fin_cases i
      simpa using h⟩
  have p0 : pauli 0 = diracSx := rfl
  have p2 : pauli 2 = diracSz := rfl
  simp only [latticeDiracHam, diracHam, Matrix.of_apply, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, e1, e2, e3, p0, p2]

/-! ### The package -/

/-- ★★★ **The lattice Dirac Hamiltonian in `d` dimensions (#294).** For a Clifford family on
the torus `ι → ZMod L`, hop `J ≠ 0`, a device with two internal levels of rest energies
`0 < μ₀ < μ₁` in the upper-band mode of momentum `n` built on a spinor `β e₀ = e₀ ≠ 0`: the
Hamiltonian is Hermitian; the modes of both levels are exact eigenvectors and nonzero; the
energy squares to `μ² + Σ_i (2J sin θ_{n_i})²`; the clock's rate `E₁ − E₀` relative to its rest
rate is `√(1 − (v/c)²)` within `(μ₁ − μ₀)/E₀`, with `c = 2J` and `v = c |s|/E₀`. -/
theorem lattice_dirac_d (h : IsCliffordFamily α β) {J μ₀ μ₁ : ℝ} (hJ : J ≠ 0) (h0 : 0 < μ₀)
    (h01 : μ₀ < μ₁) (n : ι → ZMod L) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (hne : e₀ ≠ 0) :
    Matrix.IsHermitian (latticeDiracHam (L := L) α β J μ₀)
    ∧ latticeDiracHam α β J μ₀ *ᵥ diracModeD α β J μ₀ n e₀
        = (dispE μ₀ (sNorm (modeSD J n)) : ℂ) • diracModeD α β J μ₀ n e₀
    ∧ latticeDiracHam α β J μ₁ *ᵥ diracModeD α β J μ₁ n e₀
        = (dispE μ₁ (sNorm (modeSD J n)) : ℂ) • diracModeD α β J μ₁ n e₀
    ∧ diracModeD α β J μ₀ n e₀ ≠ 0 ∧ diracModeD α β J μ₁ n e₀ ≠ 0
    ∧ dispE μ₀ (sNorm (modeSD J n)) ^ 2
        = μ₀ ^ 2 + ∑ i, (2 * J * Real.sin (latticeAngle (n i))) ^ 2
    ∧ |levelClockRate μ₀ μ₁ (sNorm (modeSD J n)) / (μ₁ - μ₀)
        - Real.sqrt (1 - (vRel (2 * J) μ₀ (sNorm (modeSD J n)) / (2 * J)) ^ 2)|
        ≤ (μ₁ - μ₀) / dispE μ₀ (sNorm (modeSD J n)) :=
  ⟨latticeDiracHam_isHermitian h J μ₀, latticeDiracHam_mulVec_diracModeD h J μ₀ n e₀,
    latticeDiracHam_mulVec_diracModeD h J μ₁ n e₀, diracModeD_ne_zero h J h0 n he hne,
    diracModeD_ne_zero h J (h0.trans h01) n he hne, dispE_sNorm_sq μ₀ (modeSD J n),
    abs_clockRate_div_sub_le (mul_ne_zero two_ne_zero hJ) h0 h01 _⟩

end CSD.CV

end

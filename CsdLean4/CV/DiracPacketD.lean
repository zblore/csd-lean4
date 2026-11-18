/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracAnisotropy
public import CsdLean4.CV.DiracPacket

/-!
# Packets on the lattice in `d` dimensions

**Category:** 3-Local (CV). BACKLOG #296, first part (Task 8 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; milestone M7,
obligation UO-17).

`CV/DiracLatticeD.lean` has the modes of the lattice Dirac Hamiltonian on a torus of any number
of axes, and `CV/DiracAnisotropy.lean` their group velocity. A mode is spread over the whole
torus. Here the carrier is a **packet**: amplitudes on a finite window of integer momenta, each
mode advancing by its phase. Its place is read by one translation phase for each axis,
`T_i = ⟨ψ, e^{2πi x̂_i/L} ψ⟩`, as `CV/DiracPacket.lean` does on the ring.

## Integer momenta and orthogonality

* `castZ`, `angleZD`, `modeSD_castZ`, `dispE_modeSD_castZ`, `angleZD_add_single`;
* `sum_star_planeWave`, ★ `sum_star_planeWaveD` (**the plane waves of the torus are
  orthogonal**, weight `L^d`), `chainInnerD`, ★ `chainInnerD_spinorWave`, `chainInnerD_sum_left`,
  `chainInnerD_sum_right`.

## The translation phases and the packet

* `transMulD`, ★ `transPhaseD`, `transMulD_sum`, `transMulD_spinorWave` (the phase of the axis
  `i` raises that axis's momentum by one and leaves the spinor);
* `modeSpinD`, `diracModeD_eq`, `packetD`, ★★ `hasDerivAt_packetD` (**it solves Schrödinger's
  equation**, for any Clifford family and any `μ`);
* `NoWrapD`, `DistinctD`, ★ `noWrapD_distinctD_of_box` (a window inside a box shorter than the
  torus has neither wrap-around nor repeated momenta);
* `spinOverlapD`, `transWeightD`, ★★ `transPhaseD_packetD` (**the translation phase along an
  axis, exactly**: a sum over the pairs of the window that are neighbours along that axis, each
  turning at the energy step `E(m + e_i) − E(m)`);
* ★★ `chainInnerD_packetD_self` (**the packet's norm does not change**).

## The drift at the group velocity

* ★ `abs_groupVelD_sub_le` (each component of the group velocity is Lipschitz in the angles,
  for `μ > 0`), `stepErrD`, ★★ `abs_latticeED_step_sub_le` (the energy step along an axis is the
  step times that component of the group velocity, within the step times `stepErrD`);
* `driftErrorD`, ★★★ `transPhaseD_drift` (**the packet moves at the group velocity, one axis at
  a time**: `T_i(t)` rotates at `(2π/L) v_i(k₀)` within `|t|` times the drift error of the axis
  `i`), ★★ `norm_transPhaseD_ge` (**it stays localised along each axis**).

## Honest scope

⚠️ **`μ > 0` for the drift.** The Lipschitz bound carries `4J²/μ`, and both `transPhaseD_drift`
and `norm_transPhaseD_ge` assume `0 < μ`. Nothing here is claimed for a massless carrier. The
exact statements (`hasDerivAt_packetD`, `transPhaseD_packetD`, `chainInnerD_packetD_self`) hold
for any `μ`.

⚠️ **The Lipschitz constant is not sharp.** `abs_groupVelD_sub_le` has a term `2|J| |k_i − k'_i|`
without the factor `|sin|` that the derivative has. Under the scaling `J = c/(2a)`, `k = a p`
it stays bounded, as the `4J²/μ` term does.

⚠️ **Not yet a region of the torus.** The modulus of `T_i` measures localisation along the axis
`i`. The weight of the packet outside a box, the limits in physical units with errors free of
`L`, flat windows and the two-level clock are not here; they are the rest of #296.

⚠️ **No record is read**, and nothing is on the arena of UA-18.

References: `specs/BACKLOG.md` #296, ~~#294~~, ~~#295~~, ~~#250~~;
`specs/unified-record-spacetime-plan.md` (UO-17, UD-206, UD-207, UD-209);
`specs/beyond-1p1-scoping.md`; `specs/unified-m7-feasibility.md` (§3, §6);
`CV/DiracLatticeD.lean` (`latticeDiracHam`, `diracModeD`, `latticeDiracHam_mulVec_diracModeD`);
`CV/DiracAnisotropy.lean` (`latticeED`, `groupVelD`, `hasDerivAt_latticeED`,
`abs_div_dispE_sNorm_sub_le`); `CV/DiracPacket.lean` (`packet`, `transPhase_packet`,
`transPhase_drift`, `norm_sum_phase_sub_le`); R. Resta, PRL 80 (1998) 1800;
`specs/future-work.md`.
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
  {L : ℕ} [NeZero L]

/-! ### Integer momenta -/

/-- The integer momenta `m` read on the torus. -/
def castZ (L : ℕ) (m : ι → ℤ) : ι → ZMod L := fun i => (m i : ZMod L)

/-- The integer momenta `m` read as angles, `k_i = 2π m_i / L`. -/
def angleZD (L : ℕ) (m : ι → ℤ) : ι → ℝ := fun i => angleZ L (m i)

omit [Fintype ι] [DecidableEq ι] in
theorem modeSD_castZ (J : ℝ) (m : ι → ℤ) :
    modeSD J (castZ L m) = sinS J (angleZD L m) := by
  funext i
  simp only [modeSD, modeS, sinS, castZ, angleZD, latticeAngle_intCast_sin]

omit [DecidableEq ι] in
/-- **The mode of integer momenta `m` has the lattice energy at its angles.** -/
theorem dispE_modeSD_castZ (J μ : ℝ) (m : ι → ℤ) :
    dispE μ (sNorm (modeSD J (castZ L m))) = latticeED J μ (angleZD L m) := by
  rw [modeSD_castZ, latticeED]

omit [Fintype ι] [NeZero L] in
theorem angleZD_add_single (m : ι → ℤ) (i : ι) :
    angleZD L (m + Pi.single i 1)
      = Function.update (angleZD L m) i (angleZD L m i + 2 * Real.pi / L) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp only [angleZD, Pi.add_apply, Pi.single_eq_same, Function.update_self, angleZ_succ]
  · simp only [angleZD, Pi.add_apply, Pi.single_eq_of_ne hji, add_zero,
      Function.update_of_ne hji]

/-! ### Plane waves on the torus are orthogonal -/

theorem sum_star_planeWave (n' n : ZMod L) :
    ∑ j : ZMod L, star (planeWave n' j) * planeWave n j = if n' = n then (L : ℂ) else 0 := by
  have hpw : ∀ j : ZMod L, star (planeWave n' j) * planeWave n j
      = (ZMod.toCircle ((n - n') * j) : ℂ) := by
    intro j
    rw [planeWave, planeWave, Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul,
      ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp only [hpw]
  rw [sum_toCircle_mul]
  by_cases h : n' = n
  · rw [ite_eq_left (sub_eq_zero.2 h.symm), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (sub_eq_zero.1 h').symm), ite_eq_right h]

/-- ★ **The plane waves of the torus are orthogonal**, with weight `L^d`. -/
theorem sum_star_planeWaveD (n' n : ι → ZMod L) :
    ∑ x : ι → ZMod L, star (planeWaveD n' x) * planeWaveD n x
      = if n' = n then (L : ℂ) ^ Fintype.card ι else 0 := by
  have h1 : ∀ x : ι → ZMod L, star (planeWaveD n' x) * planeWaveD n x
      = ∏ i, star (planeWave (n' i) (x i)) * planeWave (n i) (x i) := by
    intro x
    rw [planeWaveD, planeWaveD, star_prod, ← Finset.prod_mul_distrib]
  have h2 := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (ZMod L)))
    (fun i j => star (planeWave (n' i) j) * planeWave (n i) j)
  rw [Fintype.piFinset_univ] at h2
  simp only [h1]
  rw [← h2]
  simp only [sum_star_planeWave]
  rw [Finset.prod_ite_zero]
  by_cases h : n' = n
  · rw [ite_eq_left fun i _ => congrFun h i, ite_eq_left h, Finset.prod_const, Finset.card_univ]
  · rw [ite_eq_right fun h2 => h (funext fun i => h2 i (Finset.mem_univ i)), ite_eq_right h]

/-- The inner product on the lattice. -/
def chainInnerD (u v : (ι → ZMod L) × S → ℂ) : ℂ := ∑ p, star (u p) * v p

omit [DecidableEq S] in
/-- ★ **Two plane waves with spinors overlap only at the same momentum**, with weight `L^d`. -/
theorem chainInnerD_spinorWave (n' n : ι → ZMod L) (u' u : S → ℂ) :
    chainInnerD (spinorWave n' u') (spinorWave n u)
      = (if n' = n then (L : ℂ) ^ Fintype.card ι else 0) * ∑ a, star (u' a) * u a := by
  rw [chainInnerD, Fintype.sum_prod_type]
  simp only [spinorWave, star_mul']
  calc ∑ x : ι → ZMod L, ∑ a, star (planeWaveD n' x) * star (u' a) * (planeWaveD n x * u a)
      = ∑ x : ι → ZMod L, (star (planeWaveD n' x) * planeWaveD n x) * ∑ a, star (u' a) * u a := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = _ := by rw [← Finset.sum_mul, sum_star_planeWaveD]

omit [DecidableEq S] in
theorem chainInnerD_sum_left {κ : Type*} (s : Finset κ) (c : κ → ℂ)
    (u : κ → (ι → ZMod L) × S → ℂ) (v : (ι → ZMod L) × S → ℂ) :
    chainInnerD (∑ i ∈ s, c i • u i) v = ∑ i ∈ s, star (c i) * chainInnerD (u i) v := by
  simp only [chainInnerD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul',
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

omit [DecidableEq S] in
theorem chainInnerD_sum_right {κ : Type*} (s : Finset κ) (c : κ → ℂ)
    (u : (ι → ZMod L) × S → ℂ) (v : κ → (ι → ZMod L) × S → ℂ) :
    chainInnerD u (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * chainInnerD u (v i) := by
  simp only [chainInnerD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

/-! ### The translation phase of each axis -/

/-- **Multiplication by `e^{2πi x_i/L}`**: the position along the axis `i` read as a phase. -/
def transMulD (i : ι) (v : (ι → ZMod L) × S → ℂ) : (ι → ZMod L) × S → ℂ := fun p =>
  (ZMod.toCircle (p.1 i) : ℂ) * v p

/-- ★ **The translation phase of the axis `i`**, `T_i = ⟨ψ, e^{2πi x̂_i/L} ψ⟩`: its argument
times `L/2π` is the circular position along the axis, its modulus the localisation. -/
def transPhaseD (i : ι) (ψ : (ι → ZMod L) × S → ℂ) : ℂ := chainInnerD ψ (transMulD i ψ)

omit [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S] in
theorem transMulD_sum {κ : Type*} (i : ι) (s : Finset κ) (c : κ → ℂ)
    (v : κ → (ι → ZMod L) × S → ℂ) :
    transMulD i (∑ j ∈ s, c j • v j) = ∑ j ∈ s, c j • transMulD i (v j) := by
  funext p
  simp only [transMulD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype S] [DecidableEq S] in
/-- **The phase of the axis `i` raises that axis's momentum by one** and leaves the spinor. -/
theorem transMulD_spinorWave (i : ι) (n : ι → ZMod L) (u : S → ℂ) :
    transMulD i (spinorWave n u) = spinorWave (n + Pi.single i 1) u := by
  funext p
  have hj : ∀ j, planeWave ((n + Pi.single i 1 : ι → ZMod L) j) (p.1 j)
      = planeWave (n j) (p.1 j) * (if j = i then (ZMod.toCircle (p.1 i) : ℂ) else 1) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [planeWave, add_mul, AddChar.map_add_eq_mul]
    · simp [hji]
  simp only [transMulD, spinorWave, planeWaveD, hj, Finset.prod_mul_distrib,
    Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  ring

/-! ### The packet -/

variable (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ)

/-- The spinor of the mode `n`: `(H(s) + E) e₀`. -/
def modeSpinD (J μ : ℝ) (n : ι → ZMod L) (e₀ : S → ℂ) : S → ℂ :=
  (cliffordSymbol α β (modeSD J n) μ
    + (dispE μ (sNorm (modeSD J n)) : ℂ) • (1 : Matrix S S ℂ)) *ᵥ e₀

omit [DecidableEq ι] in
theorem diracModeD_eq (J μ : ℝ) (n : ι → ZMod L) (e₀ : S → ℂ) :
    diracModeD α β J μ n e₀ = spinorWave n (modeSpinD α β J μ n e₀) := rfl

/-- **A packet of upper-band modes on the torus**: amplitudes `c m` on a finite window `W` of
integer momenta, each mode advancing by its phase. -/
def packetD (J μ : ℝ) (e₀ : S → ℂ) (W : Finset (ι → ℤ)) (c : (ι → ℤ) → ℂ) (t : ℝ) :
    (ι → ZMod L) × S → ℂ :=
  ∑ m ∈ W, (c m * exp (-(I * latticeED J μ (angleZD L m)) * t))
    • diracModeD α β J μ (castZ L m) e₀

variable {α β}

/-- ★★ **The packet solves Schrödinger's equation** `i ψ' = H ψ`, for any Clifford family. -/
theorem hasDerivAt_packetD (h : IsCliffordFamily α β) (J μ : ℝ) (e₀ : S → ℂ)
    (W : Finset (ι → ℤ)) (c : (ι → ℤ) → ℂ) (t : ℝ) :
    HasDerivAt (packetD (L := L) α β J μ e₀ W c)
      ((-I) • (latticeDiracHam α β J μ *ᵥ packetD (L := L) α β J μ e₀ W c t)) t := by
  unfold packetD
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  refine HasDerivAt.fun_sum fun m _ => ?_
  set E : ℂ := (latticeED J μ (angleZD L m) : ℂ) with hE
  have h1 : HasDerivAt (fun t : ℝ => -(I * E) * (t : ℂ)) (-(I * E)) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(I * E))
  have h2 := ((h1.cexp).const_mul (c m)).smul_const (diracModeD α β J μ (castZ L m) e₀)
  convert h2 using 1
  rw [Matrix.mulVec_smul, latticeDiracHam_mulVec_diracModeD h, dispE_modeSD_castZ, smul_smul,
    smul_smul]
  congr 1
  rw [← hE]
  ring

/-- **No wrap-around along the axis `i`**: in the window, raising the `i`-th momentum of an
element by one is congruent to a window element only as itself. -/
def NoWrapD (L : ℕ) (W : Finset (ι → ℤ)) (i : ι) : Prop :=
  ∀ m ∈ W, ∀ m' ∈ W, (castZ L m' = castZ L m + Pi.single i 1 ↔ m' = m + Pi.single i 1)

/-- **Distinct momenta**: the window's elements are distinct on the torus. -/
def DistinctD (L : ℕ) (W : Finset (ι → ℤ)) : Prop :=
  ∀ m ∈ W, ∀ m' ∈ W, (castZ L m' = castZ L m ↔ m' = m)

omit [Fintype ι] [NeZero L] in
/-- ★ **A window inside a box shorter than the torus has neither wrap-around nor repeated
momenta.** -/
theorem noWrapD_distinctD_of_box {W : Finset (ι → ℤ)} {lo : ι → ℤ}
    (hW : ∀ m ∈ W, ∀ j, lo j ≤ m j ∧ m j + 1 < lo j + L) :
    (∀ i, NoWrapD L W i) ∧ DistinctD L W := by
  have key : ∀ (l x y : ℤ), l ≤ x → x < l + L → l ≤ y → y < l + L →
      ((x : ZMod L) = (y : ZMod L) → x = y) := by
    intro l x y hx1 hx2 hy1 hy2 h
    have hd : (L : ℤ) ∣ x - y := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h, sub_self]
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith
  refine ⟨fun i m hm m' hm' => ⟨fun h => ?_, fun h => ?_⟩,
    fun m hm m' hm' => ⟨fun h => ?_, fun h => h ▸ rfl⟩⟩
  · funext j
    obtain ⟨h1, h2⟩ := hW m hm j
    obtain ⟨h1', h2'⟩ := hW m' hm' j
    have hj := congrFun h j
    by_cases hji : j = i
    · subst hji
      simp only [castZ, Pi.add_apply, Pi.single_eq_same] at hj ⊢
      refine key (lo j) (m' j) (m j + 1) h1' (by linarith) (by linarith) h2 ?_
      rw [hj]
      push_cast
      rfl
    · simp only [castZ, Pi.add_apply, Pi.single_eq_of_ne hji, add_zero] at hj ⊢
      exact key (lo j) (m' j) (m j) h1' (by linarith) h1 (by linarith) hj
  · rw [h]
    funext j
    by_cases hji : j = i
    · subst hji
      simp [castZ]
    · simp [castZ, Pi.single_eq_of_ne hji]
  · funext j
    obtain ⟨h1, h2⟩ := hW m hm j
    obtain ⟨h1', h2'⟩ := hW m' hm' j
    exact key (lo j) (m' j) (m j) h1' (by linarith) h1 (by linarith) (congrFun h j)

variable (α β)

/-- The spinor overlap of two modes of the packet. -/
def spinOverlapD (J μ : ℝ) (e₀ : S → ℂ) (m' m : ι → ℤ) : ℂ :=
  ∑ b, star (modeSpinD α β J μ (castZ L m') e₀ b) * modeSpinD α β J μ (castZ L m) e₀ b

/-- The weight of the pair `(m, m + e_i)` in the translation phase of the axis `i`. -/
def transWeightD (J μ : ℝ) (e₀ : S → ℂ) (c : (ι → ℤ) → ℂ) (i : ι) (m : ι → ℤ) : ℂ :=
  (L : ℂ) ^ Fintype.card ι * star (c (m + Pi.single i 1)) * c m
    * spinOverlapD (L := L) α β J μ e₀ (m + Pi.single i 1) m

/-- ★★ **The translation phase of a packet along the axis `i`, exactly**: a sum over the
pairs of the window that are neighbours along `i`, each a phase turning at the energy step
`E(m + e_i) − E(m)`. -/
theorem transPhaseD_packetD (J μ : ℝ) (e₀ : S → ℂ) {W : Finset (ι → ℤ)} {i : ι}
    (hW : NoWrapD L W i) (c : (ι → ℤ) → ℂ) (t : ℝ) :
    transPhaseD i (packetD (L := L) α β J μ e₀ W c t)
      = ∑ m ∈ W.filter (fun m => m + Pi.single i 1 ∈ W), transWeightD (L := L) α β J μ e₀ c i m
          * exp (I * (((latticeED J μ (angleZD L (m + Pi.single i 1))
              - latticeED J μ (angleZD L m) : ℝ) : ℂ) * t)) := by
  unfold transPhaseD packetD
  rw [transMulD_sum, chainInnerD_sum_left]
  simp only [chainInnerD_sum_right, diracModeD_eq, transMulD_spinorWave,
    chainInnerD_spinorWave]
  set d : (ι → ℤ) → ℂ := fun m => c m * exp (-(I * latticeED J μ (angleZD L m)) * t) with hd
  calc ∑ m' ∈ W, star (d m') * ∑ m ∈ W, d m
          * ((if castZ L m' = castZ L m + Pi.single i 1 then (L : ℂ) ^ Fintype.card ι else 0)
            * ∑ b, star (modeSpinD α β J μ (castZ L m') e₀ b)
                * modeSpinD α β J μ (castZ L m) e₀ b)
      = ∑ m' ∈ W, ∑ m ∈ W, if m' = m + Pi.single i 1 then star (d m') * (d m
            * ((L : ℂ) ^ Fintype.card ι * spinOverlapD (L := L) α β J μ e₀ m' m)) else 0 := by
        refine Finset.sum_congr rfl fun m' hm' => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        by_cases h : m' = m + Pi.single i 1
        · rw [ite_eq_left ((hW m hm m' hm').2 h), ite_eq_left h, spinOverlapD]
        · rw [ite_eq_right (fun h' => h ((hW m hm m' hm').1 h')), ite_eq_right h, zero_mul,
            mul_zero, mul_zero]
    _ = ∑ m ∈ W, if m + Pi.single i 1 ∈ W then star (d (m + Pi.single i 1)) * (d m
            * ((L : ℂ) ^ Fintype.card ι
              * spinOverlapD (L := L) α β J μ e₀ (m + Pi.single i 1) m)) else 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_ite_eq']
    _ = _ := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [hd]
        rw [star_mul', star_exp_neg_I_mul, transWeightD]
        have hexp : exp (I * (latticeED J μ (angleZD L (m + Pi.single i 1)) * t))
            * exp (-(I * latticeED J μ (angleZD L m)) * t)
            = exp (I * (((latticeED J μ (angleZD L (m + Pi.single i 1))
                - latticeED J μ (angleZD L m) : ℝ) : ℂ) * t)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [← hexp]
        ring

/-- ★★ **The packet's norm does not change**: for distinct momenta, `⟨ψ_t, ψ_t⟩` is
`L^d Σ_m |c_m|² ‖u_m‖²`, with no `t` in it. -/
theorem chainInnerD_packetD_self (J μ : ℝ) (e₀ : S → ℂ) {W : Finset (ι → ℤ)}
    (hD : DistinctD L W) (c : (ι → ℤ) → ℂ) (t : ℝ) :
    chainInnerD (packetD (L := L) α β J μ e₀ W c t) (packetD (L := L) α β J μ e₀ W c t)
      = (L : ℂ) ^ Fintype.card ι
        * ∑ m ∈ W, star (c m) * c m * spinOverlapD (L := L) α β J μ e₀ m m := by
  unfold packetD
  rw [chainInnerD_sum_left]
  simp only [chainInnerD_sum_right, diracModeD_eq, chainInnerD_spinorWave]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' hm' => ?_
  have hin : ∑ m ∈ W, (c m * exp (-(I * latticeED J μ (angleZD L m)) * t))
        * ((if castZ L m' = castZ L m then (L : ℂ) ^ Fintype.card ι else 0)
          * ∑ b, star (modeSpinD α β J μ (castZ L m') e₀ b)
              * modeSpinD α β J μ (castZ L m) e₀ b)
      = (c m' * exp (-(I * latticeED J μ (angleZD L m')) * t))
        * ((L : ℂ) ^ Fintype.card ι * spinOverlapD (L := L) α β J μ e₀ m' m') := by
    rw [Finset.sum_eq_single m']
    · simp only [↓reduceIte, spinOverlapD]
    · intro m hm hne
      rw [ite_eq_right (fun h => hne ((hD m' hm' m hm).1 h.symm)), zero_mul, mul_zero]
    · intro h
      exact absurd hm' h
  have he : star (exp (-(I * latticeED J μ (angleZD L m')) * t))
      * exp (-(I * latticeED J μ (angleZD L m')) * t) = 1 := by
    rw [star_exp_neg_I_mul, ← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  rw [hin, star_mul']
  linear_combination (star (c m') * c m' * (L : ℂ) ^ Fintype.card ι
    * spinOverlapD (L := L) α β J μ e₀ m' m') * he

variable {α β}

/-! ### The group velocity is Lipschitz, and the energy step -/

omit [DecidableEq ι] in
/-- ★ **Each component of the group velocity is Lipschitz in the angles**, for `μ > 0`:
`|v_i(k) − v_i(k')| ≤ 2|J| |k_i − k'_i| + (4J²/μ)(|k_i − k'_i| + Σ_j |k_j − k'_j|)`. -/
theorem abs_groupVelD_sub_le {J μ : ℝ} (hμ : 0 < μ) (k k' : ι → ℝ) (i : ι) :
    |groupVelD J μ k i - groupVelD J μ k' i|
      ≤ 2 * |J| * |k i - k' i| + 4 * J ^ 2 / μ * (|k i - k' i| + ∑ j, |k j - k' j|) := by
  have hsin : ∀ j, |sinS J k j - sinS J k' j| ≤ 2 * |J| * |k j - k' j| := by
    intro j
    have h := Real.lipschitzWith_sin.dist_le_mul (k j) (k' j)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
    rw [sinS, sinS, ← mul_sub, abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hcos : |Real.cos (k i) - Real.cos (k' i)| ≤ |k i - k' i| := by
    have h := Real.lipschitzWith_cos.dist_le_mul (k i) (k' i)
    rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  have hE : 0 < latticeED J μ k := dispE_pos hμ _
  set b := sinS J k i / latticeED J μ k with hb
  set b' := sinS J k' i / latticeED J μ k' with hb'
  have hbb : |b - b'| ≤ (|sinS J k i - sinS J k' i| + ∑ j, |sinS J k j - sinS J k' j|) / μ :=
    abs_div_dispE_sNorm_sub_le hμ (sinS J k) (sinS J k') i
  have hb1 : |b| ≤ 1 := by
    rw [hb, abs_div, abs_of_pos hE]
    exact (div_le_one hE).2 (abs_le_dispE_sNorm μ _ i)
  have key : groupVelD J μ k i - groupVelD J μ k' i
      = 2 * J * ((Real.cos (k i) - Real.cos (k' i)) * b + Real.cos (k' i) * (b - b')) := by
    simp only [groupVelD, hb, hb']
    ring
  set A := |k i - k' i| with hA
  set Sk := ∑ j, |k j - k' j| with hSk
  have h3 : |(Real.cos (k i) - Real.cos (k' i)) * b + Real.cos (k' i) * (b - b')|
      ≤ A + (2 * |J| * A + 2 * |J| * Sk) / μ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      calc |Real.cos (k i) - Real.cos (k' i)| * |b| ≤ A * 1 :=
            mul_le_mul hcos hb1 (abs_nonneg _) (abs_nonneg _)
        _ = A := mul_one _
    · rw [abs_mul]
      calc |Real.cos (k' i)| * |b - b'| ≤ 1 * |b - b'| :=
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |b - b'| := one_mul _
        _ ≤ _ := hbb.trans (div_le_div_of_nonneg_right (add_le_add (hsin i) (by
            rw [hSk, Finset.mul_sum]
            exact Finset.sum_le_sum fun j _ => hsin j)) hμ.le)
  have hJ : |J| * |J| = J ^ 2 := by rw [← sq, sq_abs]
  rw [key, abs_mul, abs_mul, abs_two]
  calc 2 * |J| * |(Real.cos (k i) - Real.cos (k' i)) * b + Real.cos (k' i) * (b - b')|
      ≤ 2 * |J| * (A + (2 * |J| * A + 2 * |J| * Sk) / μ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * |J| * A + 4 * (|J| * |J|) / μ * (A + Sk) := by
        field_simp
        ring
    _ = _ := by rw [hJ]

/-- **The error of one energy step**: for a step `h` along the axis `i` from the angles `k`,
against the group velocity at `k₀`. -/
def stepErrD (J μ : ℝ) (k k₀ : ι → ℝ) (i : ι) (h : ℝ) : ℝ :=
  2 * |J| * (|k i - k₀ i| + h)
    + 4 * J ^ 2 / μ * ((|k i - k₀ i| + h) + (∑ j, |k j - k₀ j| + h))

/-- ★★ **The energy step along an axis is the group velocity's component times the step**,
within the step times `stepErrD`: for `μ > 0`, `h > 0`,
`|E(k + h e_i) − E(k) − h v_i(k₀)| ≤ h · stepErrD`. -/
theorem abs_latticeED_step_sub_le {J μ : ℝ} (hμ : 0 < μ) {h : ℝ} (hh : 0 < h) (k k₀ : ι → ℝ)
    (i : ι) :
    |latticeED J μ (Function.update k i (k i + h)) - latticeED J μ k - h * groupVelD J μ k₀ i|
      ≤ h * stepErrD J μ k k₀ i h := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y => latticeED J μ (Function.update k i y))
      (groupVelD J μ (Function.update k i x) i) x := by
    intro x
    have := hasDerivAt_latticeED (J := J) (μ := μ) (k := Function.update k i x)
      (dispE_pos hμ _) i
    simpa only [Function.update_idem, Function.update_self] using this
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun y => latticeED J μ (Function.update k i y))
    (fun x => groupVelD J μ (Function.update k i x) i) (lt_add_of_pos_right (k i) hh)
    (continuous_iff_continuousAt.2 fun x => (hderiv x).continuousAt).continuousOn
    (fun x _ => hderiv x)
  have hΔ : latticeED J μ (Function.update k i (k i + h)) - latticeED J μ k
      = h * groupVelD J μ (Function.update k i ξ) i := by
    have h1 : groupVelD J μ (Function.update k i ξ) i
        = (latticeED J μ (Function.update k i (k i + h)) - latticeED J μ k) / h := by
      have h2 := hslope
      simp only [Function.update_eq_self, add_sub_cancel_left] at h2
      exact h2
    rw [h1]
    field_simp
  rw [hΔ, ← mul_sub, abs_mul, abs_of_pos hh]
  refine mul_le_mul_of_nonneg_left ?_ hh.le
  refine (abs_groupVelD_sub_le hμ _ _ i).trans ?_
  have hi : |Function.update k i ξ i - k₀ i| ≤ |k i - k₀ i| + h := by
    rw [Function.update_self]
    have e : ξ - k₀ i = (k i - k₀ i) + (ξ - k i) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have : |ξ - k i| ≤ h := by
      rw [abs_of_pos (sub_pos.2 hξ.1)]
      linarith [hξ.2]
    linarith
  have hsum : ∑ j, |Function.update k i ξ j - k₀ j| ≤ ∑ j, |k j - k₀ j| + h := by
    calc ∑ j, |Function.update k i ξ j - k₀ j|
        ≤ ∑ j, (|k j - k₀ j| + if j = i then h else 0) := Finset.sum_le_sum fun j _ => by
          by_cases hji : j = i
          · subst hji
            simpa using hi
          · simp [hji]
      _ = ∑ j, |k j - k₀ j| + h := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i]
          simp
  unfold stepErrD
  gcongr

/-! ### The packet moves at the group velocity -/

variable (α β)

/-- **The drift error along the axis `i`**: the weighted spread of the window's energy steps
about `(2π/L) v_i(k₀)`. -/
def driftErrorD (J μ : ℝ) (e₀ : S → ℂ) (W : Finset (ι → ℤ)) (c : (ι → ℤ) → ℂ) (i : ι)
    (k₀ : ι → ℝ) : ℝ :=
  ∑ m ∈ W.filter (fun m => m + Pi.single i 1 ∈ W), ‖transWeightD (L := L) α β J μ e₀ c i m‖
    * (2 * Real.pi / L * stepErrD J μ (angleZD L m) k₀ i (2 * Real.pi / L))

/-- ★★★ **The packet moves at the group velocity, one axis at a time**: for `μ > 0`, its
translation phase along the axis `i` rotates at `(2π/L) v_i(k₀)`, the circular position
advancing `v_i(k₀)` sites per unit time, within `|t|` times the drift error of that axis. -/
theorem transPhaseD_drift {J μ : ℝ} (hμ : 0 < μ) (e₀ : S → ℂ) {W : Finset (ι → ℤ)} {i : ι}
    (hW : NoWrapD L W i) (c : (ι → ℤ) → ℂ) (k₀ : ι → ℝ) (t : ℝ) :
    ‖transPhaseD i (packetD (L := L) α β J μ e₀ W c t)
        - exp (I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * t))
          * transPhaseD i (packetD (L := L) α β J μ e₀ W c 0)‖
      ≤ |t| * driftErrorD (L := L) α β J μ e₀ W c i k₀ := by
  have hL : (0 : ℝ) < 2 * Real.pi / L := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [transPhaseD_packetD α β J μ e₀ hW c t, transPhaseD_packetD α β J μ e₀ hW c 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  refine (norm_sum_phase_sub_le _ _ _ _ t).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (abs_nonneg t)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [angleZD_add_single]
  exact abs_latticeED_step_sub_le hμ hL (angleZD L m) k₀ i

/-- ★★ **The packet stays localised along each axis**: the modulus of its translation phase
along `i` drops by at most `|t|` times that axis's drift error. -/
theorem norm_transPhaseD_ge {J μ : ℝ} (hμ : 0 < μ) (e₀ : S → ℂ) {W : Finset (ι → ℤ)} {i : ι}
    (hW : NoWrapD L W i) (c : (ι → ℤ) → ℂ) (k₀ : ι → ℝ) (t : ℝ) :
    ‖transPhaseD i (packetD (L := L) α β J μ e₀ W c 0)‖
        - |t| * driftErrorD (L := L) α β J μ e₀ W c i k₀
      ≤ ‖transPhaseD i (packetD (L := L) α β J μ e₀ W c t)‖ := by
  have h := transPhaseD_drift (L := L) (J := J) α β hμ e₀ hW c k₀ t
  have hn : ‖exp (I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * t))‖ = 1 := by
    rw [show I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * t)
        = ((2 * Real.pi / L * groupVelD J μ k₀ i * t : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.norm_exp_ofReal_mul_I]
  have h2 := norm_sub_norm_le (exp (I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * t))
    * transPhaseD i (packetD (L := L) α β J μ e₀ W c 0))
    (transPhaseD i (packetD (L := L) α β J μ e₀ W c t))
  rw [norm_mul, hn, one_mul, norm_sub_rev] at h2
  linarith

end CSD.CV

end

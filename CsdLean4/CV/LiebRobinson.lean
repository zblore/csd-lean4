/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelBound
public import CsdLean4.CV.SupportSpreading
public import CsdLean4.CV.LocalAlgebraClosed
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# CV-17/CV-18: the Heisenberg flow and the linear Lieb-Robinson bound

**Category:** CV (continuous variables); the general lemmas are CSD-free
(`upstream-candidate(mathlib)`).

**Glossary:** https://glossary.constraintsurfacedynamics.com/lieb-robinson-bound/
Plain-language, CSD-role and formal statements of the Lieb-Robinson bound, with
this module as the Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

Stage 5's first two bricks. Everything is stated for a skew-Hermitian
generator `S`, which is `-i H` for Hermitian `H`, so that the propagators
are unitary and the L2 operator norm sees them as isometries.

* `heisenbergFlow S t A = exp (-t • S) * A * exp (t • S)` — the observable
  after time `t`; `norm_heisenbergFlow_le` (conjugation by unitaries does
  not grow the norm), `heisenbergFlow_zero`.
* ★ `hasDerivAt_heisenbergFlow` — `d/dt A(t) = [A(t), S]` (CV-17).
* `commutator_deriv_eq` — the interaction-picture split. Writing
  `S = S_X + T` with `S_X` the part of the generator that commutes with the
  probe `B`, the commutator `f(t) = [A(t), B]` obeys
  `f'(t) = [f(t), S_X] + [[A(t), T], B]`. The first term is a pure
  conjugation and carries no growth; all the growth is in `T`, the part of
  the generator that couples across the cut. Proved by the Jacobi
  cancellation `A·[S_X,B] - [S_X,B]·A = 0`.
* ★★ `norm_commutator_heisenbergFlow_le` — **the linear Lieb-Robinson
  bound**: if `[A, B] = 0` and `S_X` commutes with `B`, then
  `‖[A(t), B]‖ ≤ 4·|t|·‖T‖·‖A‖·‖B‖`. **Information cannot leave a region
  instantaneously**: the commutator grows at most linearly in time, at a
  rate set by the coupling across the cut alone, not by the total energy.
* `norm_commutator_field_le` — the CV instantiation: disjointly
  supported observables of the field, with `[A,B] = 0` supplied by CV-8's
  `commute_of_disjointSupport`.

* ★★ `norm_commutator_gronwall_le` (CV-19, partial) — the **Gronwall**
  bound: `‖[A(t),B]‖ ≤ gronwallBound 0 (2‖T‖) (2‖A‖‖[T,B]‖) t`, which for
  `‖T‖ ≠ 0` reads `(‖A‖‖[T,B]‖/‖T‖)(e^{2‖T‖t} − 1)`. Two things improve on
  the linear bound. The time dependence is exponential in `‖T‖t`, which is
  the correct shape. And the prefactor is `‖[T,B]‖`, the part of the
  coupling that actually *reaches* the probe, so
  `commutator_eq_zero_of_coupling_commutes`: a coupling commuting with `B`
  contributes exactly nothing, at any time.

* ★★ `adIter_supportedOn_graphBall` and `commutator_adIter_eq_zero` — the
  **combinatorial half of the spatial cone**. The Heisenberg flow is the
  exponential generating series of the nested commutators `ad_S^k(A)`, and
  for a generator that is a sum of edge-supported terms those iterates stay
  inside the coupling graph's `k`-ball: a term whose edge misses the current
  region commutes with the observable and drops out, so `k` steps reach at
  most `k` edges. Consequently `ad_S^k(A)` commutes with `B` **exactly**
  whenever the `k`-ball has not yet reached `B`'s region. That is what makes
  a Lieb-Robinson series start at the graph distance rather than at zero.

* ★★★ `norm_commutator_spatial_le` — **the spatial bound**:
  `‖[A(t), B]‖ ≤ 2‖A‖‖B‖·(2‖S‖|t|)^d` for every `d` whose graph ball
  around `A`'s region has not reached `B`'s. Whenever `2‖S‖|t| < 1` this
  decays geometrically in the graph distance, so an observable at distance
  `d` is disturbed only after a time of order `d/(2‖S‖)`: **the propagation
  speed is bounded by the coupling strength**. The two halves meet here.
  The Taylor remainder controls the flow to order `d`, and every discarded
  term commutes with `B` exactly, because `k` nested commutators reach at
  most `k` edges, so the whole commutator is carried by the remainder.

* ★★★ `norm_commutator_spatial_factorial_le` — **the Lieb-Robinson bound
  with its factorial**: `‖[A(t), B]‖ ≤ 2‖A‖‖B‖·(2‖S‖t)^d/d!`, obtained by
  replacing the mean-value step in the remainder estimate with an integral
  one (`norm_flowRemainder_le_factorial`). Because of the factorial this
  decays in the graph distance at **every** time rather than only below
  `2‖S‖t = 1`: at fixed `t` the bound falls faster than geometrically in
  `d`, which is the standard statement that the commutator is
  exponentially small outside an effective light cone.

⚠️ Honest scope. Both the geometric and factorial forms are proved; the
factorial one is the sharper and is the textbook shape. No velocity
constant is extracted or optimised: Lieb-Robinson velocities are famously
not tight, and none is asserted here, so "light cone" refers to the decay
in `d` at fixed `t` and not to an optimal speed. The interaction is a
finite sum of edge-supported terms on a finite mode graph; nothing is
claimed in the continuum (`ApproxCCR.no_exact_finite_ccr` stands).

## References

`Mathlib/Analysis/Matrix/DuhamelBound.lean` (the mean-value pattern and the
skew-generator lemmas); `CV/SupportSpreading.lean` (CV-8, the initial
condition); `specs/eft-stage5-plan.md` (rows CV-17, CV-18);
Lieb-Robinson (1972); Nachtergaele-Sims (2010).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix NormedSpace

namespace CSD.CV

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-! ### CV-17: the Heisenberg flow -/

/-- **The Heisenberg flow** generated by a skew-Hermitian `S = -iH`. -/
noncomputable def heisenbergFlow (S : Matrix m m ℂ) (t : ℝ)
    (A : Matrix m m ℂ) : Matrix m m ℂ :=
  exp ((-t) • S) * A * exp (t • S)

omit [Nonempty m] in
@[simp] lemma heisenbergFlow_zero (S A : Matrix m m ℂ) :
    heisenbergFlow S 0 A = A := by
  rw [heisenbergFlow]
  simp

/-- Conjugation by the unitary propagators does not grow the norm. -/
theorem norm_heisenbergFlow_le {S : Matrix m m ℂ} (hS : Sᴴ = -S) (t : ℝ)
    (A : Matrix m m ℂ) : ‖heisenbergFlow S t A‖ ≤ ‖A‖ := by
  have h1 : ‖exp ((-t) • S)‖ = 1 := Matrix.l2_opNorm_exp_smul_skew S hS (-t)
  have h2 : ‖exp (t • S)‖ = 1 := Matrix.l2_opNorm_exp_smul_skew S hS t
  calc ‖exp ((-t) • S) * A * exp (t • S)‖
      ≤ ‖exp ((-t) • S) * A‖ * ‖exp (t • S)‖ := norm_mul_le _ _
    _ ≤ ‖exp ((-t) • S)‖ * ‖A‖ * ‖exp (t • S)‖ := by
        gcongr
        exact norm_mul_le _ _
    _ = ‖A‖ := by rw [h1, h2, one_mul, mul_one]

omit [Nonempty m] in
/-- ★ **CV-17**: the Heisenberg flow solves `d/dt A(t) = [A(t), S]`. -/
theorem hasDerivAt_heisenbergFlow (S A : Matrix m m ℂ) (t : ℝ) :
    HasDerivAt (fun u => heisenbergFlow S u A)
      (heisenbergFlow S t A * S - S * heisenbergFlow S t A) t := by
  have hneg : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) t := hasDerivAt_neg t
  have hL : HasDerivAt (fun u : ℝ => exp ((-u) • S))
      ((-1 : ℝ) • (exp ((-t) • S) * S)) t :=
    (hasDerivAt_exp_smul_const S (-t)).scomp t hneg
  have hR : HasDerivAt (fun u : ℝ => exp (u • S)) (exp (t • S) * S) t :=
    hasDerivAt_exp_smul_const S t
  have hprod := (hL.mul_const A).mul hR
  have hcommL : exp ((-t) • S) * S = S * exp ((-t) • S) :=
    (((Commute.refl S).smul_left (-t)).exp_left).eq
  refine hprod.congr_deriv ?_
  rw [heisenbergFlow, neg_one_smul, neg_mul, neg_mul, hcommL]
  noncomm_ring

/-! ### The interaction-picture split -/

omit [Nonempty m] in
/-- **The split.** With `S = S_X + T` and `S_X` commuting with the probe
`B`, the commutator `[A(t), B]` obeys `f' = [f, S_X] + [[A(t), T], B]`:
the local part of the generator contributes only a conjugation, and all
growth comes from `T`, the part that couples across the cut. -/
theorem commutator_deriv_eq {S S_X T : Matrix m m ℂ} (A B : Matrix m m ℂ)
    (hsplit : S = S_X + T) (hcomm : S_X * B = B * S_X) (t : ℝ) :
    HasDerivAt (fun u => heisenbergFlow S u A * B - B * heisenbergFlow S u A)
      ((heisenbergFlow S t A * B - B * heisenbergFlow S t A) * S_X
        - S_X * (heisenbergFlow S t A * B - B * heisenbergFlow S t A)
        + ((heisenbergFlow S t A * T - T * heisenbergFlow S t A) * B
          - B * (heisenbergFlow S t A * T - T * heisenbergFlow S t A))) t := by
  set F := heisenbergFlow S t A with hF
  have hd := hasDerivAt_heisenbergFlow S A t
  have hprod := (hd.mul_const B).sub (hd.const_mul B)
  have hz : S_X * B - B * S_X = 0 := sub_eq_zero.mpr hcomm
  have hexpand : (F * S - S * F) * B - B * (F * S - S * F)
      - (((F * B - B * F) * S_X - S_X * (F * B - B * F))
        + ((F * T - T * F) * B - B * (F * T - T * F)))
      = F * (S_X * B - B * S_X) - (S_X * B - B * S_X) * F := by
    rw [hsplit]
    noncomm_ring
  have hkey : (F * S - S * F) * B - B * (F * S - S * F)
      = ((F * B - B * F) * S_X - S_X * (F * B - B * F))
        + ((F * T - T * F) * B - B * (F * T - T * F)) := by
    rw [← sub_eq_zero, hexpand, hz, mul_zero, zero_mul, sub_zero]
  exact hprod.congr_deriv hkey

/-! ### Conjugation invariance and the conjugated commutator -/

/-- Conjugation by the unitaries generated by a skew-Hermitian `S_X`
preserves the L2 operator norm. -/
theorem norm_conj_eq {S_X : Matrix m m ℂ} (hSX : S_Xᴴ = -S_X) (t : ℝ)
    (M : Matrix m m ℂ) :
    ‖exp (t • S_X) * M * exp ((-t) • S_X)‖ = ‖M‖ := by
  have hP : ‖exp (t • S_X)‖ = 1 := Matrix.l2_opNorm_exp_smul_skew S_X hSX t
  have hQ : ‖exp ((-t) • S_X)‖ = 1 :=
    Matrix.l2_opNorm_exp_smul_skew S_X hSX (-t)
  have hle : ∀ (u : ℝ) (X : Matrix m m ℂ),
      ‖exp (u • S_X) * X * exp ((-u) • S_X)‖ ≤ ‖X‖ := by
    intro u X
    have h1 : ‖exp (u • S_X)‖ = 1 := Matrix.l2_opNorm_exp_smul_skew S_X hSX u
    have h2 : ‖exp ((-u) • S_X)‖ = 1 :=
      Matrix.l2_opNorm_exp_smul_skew S_X hSX (-u)
    calc ‖exp (u • S_X) * X * exp ((-u) • S_X)‖
        ≤ ‖exp (u • S_X) * X‖ * ‖exp ((-u) • S_X)‖ := norm_mul_le _ _
      _ ≤ ‖exp (u • S_X)‖ * ‖X‖ * ‖exp ((-u) • S_X)‖ := by
          gcongr; exact norm_mul_le _ _
      _ = ‖X‖ := by rw [h1, h2, one_mul, mul_one]
  refine le_antisymm (hle t M) ?_
  have hinv : exp ((-t) • S_X) * exp (t • S_X) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _
        (((Commute.refl S_X).smul_left (-t)).smul_right t),
      neg_smul, neg_add_cancel, exp_zero]
  have hback : M = exp ((-t) • S_X)
      * (exp (t • S_X) * M * exp ((-t) • S_X)) * exp (t • S_X) := by
    rw [show exp ((-t) • S_X) * (exp (t • S_X) * M * exp ((-t) • S_X))
          * exp (t • S_X)
        = (exp ((-t) • S_X) * exp (t • S_X)) * M
          * (exp ((-t) • S_X) * exp (t • S_X)) from by noncomm_ring,
      hinv, one_mul, mul_one]
  calc ‖M‖ = ‖exp ((-t) • S_X)
        * (exp (t • S_X) * M * exp ((-t) • S_X)) * exp (t • S_X)‖ := by
        rw [← hback]
    _ ≤ ‖exp (t • S_X) * M * exp ((-t) • S_X)‖ := by
        have := hle (-t) (exp (t • S_X) * M * exp ((-t) • S_X))
        rwa [neg_neg] at this

/-- **The conjugated commutator**: the commutator viewed in the frame that
rotates with the local part of the generator. Its derivative has no
conjugation term, which is what makes the estimates work. -/
noncomputable def conjComm (S S_X A B : Matrix m m ℂ) (t : ℝ) :
    Matrix m m ℂ :=
  exp (t • S_X)
    * (heisenbergFlow S t A * B - B * heisenbergFlow S t A)
    * exp ((-t) • S_X)

/-- The conjugated commutator has the same norm as the commutator. -/
theorem norm_conjComm {S_X : Matrix m m ℂ} (hSX : S_Xᴴ = -S_X)
    (S A B : Matrix m m ℂ) (t : ℝ) :
    ‖conjComm S S_X A B t‖
      = ‖heisenbergFlow S t A * B - B * heisenbergFlow S t A‖ :=
  norm_conj_eq hSX t _

omit [Nonempty m] in
@[simp] lemma conjComm_zero (S S_X A B : Matrix m m ℂ) :
    conjComm S S_X A B 0 = A * B - B * A := by
  rw [conjComm]
  simp

omit [Nonempty m] in
/-- The derivative of the conjugated commutator is the leakage term, with
the local part of the generator gone. -/
theorem hasDerivAt_conjComm {S S_X T : Matrix m m ℂ} (A B : Matrix m m ℂ)
    (hsplit : S = S_X + T) (hcomm : S_X * B = B * S_X) (s : ℝ) :
    HasDerivAt (conjComm S S_X A B)
      (exp (s • S_X)
        * ((heisenbergFlow S s A * T - T * heisenbergFlow S s A) * B
          - B * (heisenbergFlow S s A * T - T * heisenbergFlow S s A))
        * exp ((-s) • S_X)) s := by
  set F := heisenbergFlow S s A with hFs
  set f := F * B - B * F with hfs
  set R := (F * T - T * F) * B - B * (F * T - T * F) with hRs
  have hP : HasDerivAt (fun u : ℝ => exp (u • S_X)) (exp (s • S_X) * S_X) s :=
    hasDerivAt_exp_smul_const S_X s
  have hnegs : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) s := hasDerivAt_neg s
  have hQ : HasDerivAt (fun u : ℝ => exp ((-u) • S_X))
      ((-1 : ℝ) • (exp ((-s) • S_X) * S_X)) s :=
    (hasDerivAt_exp_smul_const S_X (-s)).scomp s hnegs
  have hf := commutator_deriv_eq (S := S) (S_X := S_X) (T := T) A B
    hsplit hcomm s
  have hprod := ((hP.mul hf).mul hQ)
  simp only [Pi.mul_apply, neg_one_smul] at hprod
  have hcommQ : exp ((-s) • S_X) * S_X = S_X * exp ((-s) • S_X) :=
    (((Commute.refl S_X).smul_left (-s)).exp_left).eq
  refine hprod.congr_deriv ?_
  rw [mul_neg, hcommQ]
  simp only [hRs, neg_smul]
  noncomm_ring

/-- The leakage term, bounded crudely. -/
theorem norm_leak_le {S T : Matrix m m ℂ} {A B : Matrix m m ℂ}
    (hS : Sᴴ = -S) (s : ℝ) :
    ‖(heisenbergFlow S s A * T - T * heisenbergFlow S s A) * B
        - B * (heisenbergFlow S s A * T - T * heisenbergFlow S s A)‖
      ≤ 4 * ‖T‖ * ‖A‖ * ‖B‖ := by
  set F := heisenbergFlow S s A with hFs
  have hFn : ‖F‖ ≤ ‖A‖ := norm_heisenbergFlow_le hS s A
  have hFT : ‖F * T - T * F‖ ≤ 2 * ‖T‖ * ‖A‖ := by
    calc ‖F * T - T * F‖ ≤ ‖F * T‖ + ‖T * F‖ := norm_sub_le _ _
      _ ≤ ‖F‖ * ‖T‖ + ‖T‖ * ‖F‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖A‖ * ‖T‖ + ‖T‖ * ‖A‖ := by gcongr
      _ = 2 * ‖T‖ * ‖A‖ := by ring
  calc ‖(F * T - T * F) * B - B * (F * T - T * F)‖
      ≤ ‖(F * T - T * F) * B‖ + ‖B * (F * T - T * F)‖ := norm_sub_le _ _
    _ ≤ ‖F * T - T * F‖ * ‖B‖ + ‖B‖ * ‖F * T - T * F‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (2 * ‖T‖ * ‖A‖) * ‖B‖ + ‖B‖ * (2 * ‖T‖ * ‖A‖) := by gcongr
    _ = 4 * ‖T‖ * ‖A‖ * ‖B‖ := by ring

/-! ### CV-18: the linear bound -/

/-- ★★ **CV-18, the linear Lieb-Robinson bound.** If the observables
commute at time zero and the local part `S_X` of the generator commutes
with the probe `B`, then the commutator grows at most linearly in time, at
a rate set by `T` (the part of the generator coupling across the cut)
alone: `‖[A(t), B]‖ ≤ 4·|t|·‖T‖·‖A‖·‖B‖`. Information cannot leave a
region instantaneously. -/
theorem norm_commutator_heisenbergFlow_le {S S_X T : Matrix m m ℂ}
    {A B : Matrix m m ℂ} (hS : Sᴴ = -S) (hSX : S_Xᴴ = -S_X)
    (hsplit : S = S_X + T) (hcomm : S_X * B = B * S_X)
    (hAB : A * B = B * A) (t : ℝ) :
    ‖heisenbergFlow S t A * B - B * heisenbergFlow S t A‖
      ≤ 4 * |t| * ‖T‖ * ‖A‖ * ‖B‖ := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := conjComm S S_X A B)
    (f' := fun s => exp (s • S_X)
      * ((heisenbergFlow S s A * T - T * heisenbergFlow S s A) * B
        - B * (heisenbergFlow S s A * T - T * heisenbergFlow S s A))
      * exp ((-s) • S_X))
    (s := Set.uIcc (0 : ℝ) t) (C := 4 * ‖T‖ * ‖A‖ * ‖B‖)
    (fun s _ => (hasDerivAt_conjComm A B hsplit hcomm s).hasDerivWithinAt)
    (fun s _ => by
      rw [norm_conj_eq hSX s]
      exact norm_leak_le hS s)
    (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [conjComm_zero, sub_eq_zero.mpr hAB, sub_zero, norm_conjComm hSX] at hmvt
  calc ‖heisenbergFlow S t A * B - B * heisenbergFlow S t A‖
      ≤ 4 * ‖T‖ * ‖A‖ * ‖B‖ * |t - 0| := hmvt
    _ = 4 * |t| * ‖T‖ * ‖A‖ * ‖B‖ := by rw [sub_zero]; ring

/-! ### CV-19 (partial): the Gronwall bound -/

omit [Nonempty m] in
/-- The Jacobi re-split of the leakage term. The double commutator with the
coupling splits into a term proportional to the commutator being estimated
and a term proportional to `[T, B]`, the part of the coupling that actually
reaches the probe. -/
theorem leak_jacobi (F T B : Matrix m m ℂ) :
    (F * T - T * F) * B - B * (F * T - T * F)
      = ((F * B - B * F) * T - T * (F * B - B * F))
        + (F * (T * B - B * T) - (T * B - B * T) * F) := by
  noncomm_ring

/-- The leakage term, bounded in Gronwall shape: proportional to the
current commutator, plus a source proportional to `‖[T, B]‖`. -/
theorem norm_leak_gronwall_le {S T : Matrix m m ℂ} {A B : Matrix m m ℂ}
    (hS : Sᴴ = -S) (s : ℝ) :
    ‖(heisenbergFlow S s A * T - T * heisenbergFlow S s A) * B
        - B * (heisenbergFlow S s A * T - T * heisenbergFlow S s A)‖
      ≤ 2 * ‖T‖ * ‖heisenbergFlow S s A * B - B * heisenbergFlow S s A‖
        + 2 * ‖A‖ * ‖T * B - B * T‖ := by
  set F := heisenbergFlow S s A with hFs
  have hFn : ‖F‖ ≤ ‖A‖ := norm_heisenbergFlow_le hS s A
  have h1 : ‖(F * B - B * F) * T - T * (F * B - B * F)‖
      ≤ 2 * ‖T‖ * ‖F * B - B * F‖ := by
    calc ‖(F * B - B * F) * T - T * (F * B - B * F)‖
        ≤ ‖(F * B - B * F) * T‖ + ‖T * (F * B - B * F)‖ := norm_sub_le _ _
      _ ≤ ‖F * B - B * F‖ * ‖T‖ + ‖T‖ * ‖F * B - B * F‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * ‖T‖ * ‖F * B - B * F‖ := by ring
  have h2 : ‖F * (T * B - B * T) - (T * B - B * T) * F‖
      ≤ 2 * ‖A‖ * ‖T * B - B * T‖ := by
    calc ‖F * (T * B - B * T) - (T * B - B * T) * F‖
        ≤ ‖F * (T * B - B * T)‖ + ‖(T * B - B * T) * F‖ := norm_sub_le _ _
      _ ≤ ‖F‖ * ‖T * B - B * T‖ + ‖T * B - B * T‖ * ‖F‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖A‖ * ‖T * B - B * T‖ + ‖T * B - B * T‖ * ‖A‖ := by gcongr
      _ = 2 * ‖A‖ * ‖T * B - B * T‖ := by ring
  calc ‖(F * T - T * F) * B - B * (F * T - T * F)‖
      = ‖((F * B - B * F) * T - T * (F * B - B * F))
          + (F * (T * B - B * T) - (T * B - B * T) * F)‖ := by
        rw [leak_jacobi]
    _ ≤ ‖(F * B - B * F) * T - T * (F * B - B * F)‖
          + ‖F * (T * B - B * T) - (T * B - B * T) * F‖ := norm_add_le _ _
    _ ≤ 2 * ‖T‖ * ‖F * B - B * F‖ + 2 * ‖A‖ * ‖T * B - B * T‖ :=
        add_le_add h1 h2

/-- ★★ **The Gronwall (exponential-in-time) Lieb-Robinson bound.** The
commutator obeys `‖[A(t), B]‖ ≤ gronwallBound 0 (2‖T‖) (2‖A‖‖[T,B]‖) t`,
which for `‖T‖ ≠ 0` is `(‖A‖‖[T,B]‖/‖T‖)·(e^{2‖T‖t} − 1)`.

Two things are sharper here than in CV-18. The growth is exponential in
`‖T‖t` rather than linear, which is the correct time dependence. More
importantly the prefactor is `‖[T, B]‖`, the part of the coupling that
actually reaches the probe: if the coupling term commutes with `B`, the
bound is identically zero for all time. That vanishing is the seed of a
spatial light cone; converting it into one requires the iteration over
chains of interaction terms, which is not done here. -/
theorem norm_commutator_gronwall_le {S S_X T : Matrix m m ℂ}
    {A B : Matrix m m ℂ} (hS : Sᴴ = -S) (hSX : S_Xᴴ = -S_X)
    (hsplit : S = S_X + T) (hcomm : S_X * B = B * S_X)
    (hAB : A * B = B * A) {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow S t A * B - B * heisenbergFlow S t A‖
      ≤ gronwallBound 0 (2 * ‖T‖) (2 * ‖A‖ * ‖T * B - B * T‖) t := by
  have hderiv : ∀ s : ℝ, HasDerivAt (conjComm S S_X A B)
      (exp (s • S_X)
        * ((heisenbergFlow S s A * T - T * heisenbergFlow S s A) * B
          - B * (heisenbergFlow S s A * T - T * heisenbergFlow S s A))
        * exp ((-s) • S_X)) s :=
    fun s => hasDerivAt_conjComm A B hsplit hcomm s
  have hcont : ContinuousOn (conjComm S S_X A B) (Set.Icc 0 t) :=
    fun s _ => ((hderiv s).continuousAt).continuousWithinAt
  have hzero : ‖conjComm S S_X A B 0‖ ≤ 0 := by
    rw [conjComm_zero, sub_eq_zero.mpr hAB, norm_zero]
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖exp (s • S_X)
        * ((heisenbergFlow S s A * T - T * heisenbergFlow S s A) * B
          - B * (heisenbergFlow S s A * T - T * heisenbergFlow S s A))
        * exp ((-s) • S_X)‖
      ≤ 2 * ‖T‖ * ‖conjComm S S_X A B s‖ + 2 * ‖A‖ * ‖T * B - B * T‖ := by
    intro s _
    rw [norm_conj_eq hSX s, norm_conjComm hSX]
    exact norm_leak_gronwall_le hS s
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s _ => (hderiv s).hasDerivWithinAt) hzero hbound t
    (Set.right_mem_Icc.mpr ht)
  rw [sub_zero, norm_conjComm hSX] at hg
  exact hg

/-- The vanishing case, stated on its own: a coupling term that commutes
with the probe contributes nothing, at any time. -/
theorem commutator_eq_zero_of_coupling_commutes {S S_X T : Matrix m m ℂ}
    {A B : Matrix m m ℂ} (hS : Sᴴ = -S) (hSX : S_Xᴴ = -S_X)
    (hsplit : S = S_X + T) (hcomm : S_X * B = B * S_X)
    (hTB : T * B = B * T) (hAB : A * B = B * A) {t : ℝ} (ht : 0 ≤ t) :
    heisenbergFlow S t A * B - B * heisenbergFlow S t A = 0 := by
  have h := norm_commutator_gronwall_le hS hSX hsplit hcomm hAB ht
  rw [sub_eq_zero.mpr hTB, norm_zero, mul_zero, gronwallBound_ε0] at h
  simp only [zero_mul] at h
  exact norm_le_zero_iff.mp h

/-! ### The adjoint action -/

/-- One step of the adjoint action: `ad_G(A) = [G, A]`. -/
def adOne {n : Type*} [Fintype n] [DecidableEq n] (G A : Matrix n n ℂ) :
    Matrix n n ℂ := G * A - A * G

/-- The `k`-fold adjoint action `ad_S^k`. The Heisenberg flow is its
exponential generating series, which is why the support of these iterates
controls the spatial reach of the dynamics. -/
def adIter {n : Type*} [Fintype n] [DecidableEq n] (S : Matrix n n ℂ) :
    ℕ → Matrix n n ℂ → Matrix n n ℂ
  | 0, A => A
  | k + 1, A => adOne S (adIter S k A)

@[simp] lemma adIter_zero {n : Type*} [Fintype n] [DecidableEq n]
    (S A : Matrix n n ℂ) : adIter S 0 A = A := rfl

@[simp] lemma adIter_succ {n : Type*} [Fintype n] [DecidableEq n]
    (S A : Matrix n n ℂ) (k : ℕ) :
    adIter S (k + 1) A = adOne S (adIter S k A) := rfl

/-- The adjoint action is linear in the generator. -/
lemma adOne_sum {n ι : Type*} [Fintype n] [DecidableEq n] (E : Finset ι)
    (G : ι → Matrix n n ℂ) (A : Matrix n n ℂ) :
    adOne (∑ e ∈ E, G e) A = ∑ e ∈ E, adOne (G e) A := by
  simp only [adOne, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

/-! ### The Taylor remainder of the flow -/

/-- The Taylor coefficients of the Heisenberg flow, as real scalars. -/
noncomputable def flowCoef (t : ℝ) (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k / k.factorial) * t ^ k

@[simp] lemma flowCoef_zero (t : ℝ) : flowCoef t 0 = 1 := by
  rw [flowCoef]; simp

/-- The Taylor remainder of the flow after `k` terms of its adjoint
series. -/
noncomputable def flowRemainder (S A : Matrix m m ℂ) (k : ℕ) (t : ℝ) :
    Matrix m m ℂ :=
  heisenbergFlow S t A - ∑ j ∈ Finset.range k, flowCoef t j • adIter S j A

omit [Nonempty m] in
@[simp] lemma flowRemainder_zero_terms (S A : Matrix m m ℂ) (t : ℝ) :
    flowRemainder S A 0 t = heisenbergFlow S t A := by
  rw [flowRemainder]; simp

omit [Nonempty m] in
/-- The adjoint action commutes with real scalars in its second
argument. -/
lemma adOne_smul (S : Matrix m m ℂ) (c : ℝ) (A : Matrix m m ℂ) :
    adOne S (c • A) = c • adOne S A := by
  rw [adOne, adOne, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

omit [Nonempty m] in
lemma adOne_sub (S X Y : Matrix m m ℂ) :
    adOne S (X - Y) = adOne S X - adOne S Y := by
  rw [adOne, adOne, adOne]
  noncomm_ring

omit [Nonempty m] in
lemma adOne_sum_range (S : Matrix m m ℂ) (k : ℕ) (f : ℕ → Matrix m m ℂ) :
    adOne S (∑ j ∈ Finset.range k, f j)
      = ∑ j ∈ Finset.range k, adOne S (f j) := by
  simp only [adOne, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

omit [Nonempty m] in
/-- The norm of a nested commutator grows by at most `2‖S‖` per step. -/
theorem norm_adIter_le (S A : Matrix m m ℂ) (k : ℕ) :
    ‖adIter S k A‖ ≤ (2 * ‖S‖) ^ k * ‖A‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : (0 : ℝ) ≤ 2 * ‖S‖ := by positivity
    rw [adIter_succ]
    calc ‖adOne S (adIter S k A)‖
        ≤ ‖S * adIter S k A‖ + ‖adIter S k A * S‖ := norm_sub_le _ _
      _ ≤ ‖S‖ * ‖adIter S k A‖ + ‖adIter S k A‖ * ‖S‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * ‖S‖ * ‖adIter S k A‖ := by ring
      _ ≤ 2 * ‖S‖ * ((2 * ‖S‖) ^ k * ‖A‖) := mul_le_mul_of_nonneg_left ih h2
      _ = (2 * ‖S‖) ^ (k + 1) * ‖A‖ := by ring

/-- Each Taylor coefficient differentiates into its predecessor. -/
lemma hasDerivAt_flowCoef (t : ℝ) (j : ℕ) :
    HasDerivAt (fun u : ℝ => flowCoef u (j + 1)) (-flowCoef t j) t := by
  have hpow : HasDerivAt (fun u : ℝ => u ^ (j + 1))
      (((j : ℝ) + 1) * t ^ j) t := by
    simpa using hasDerivAt_pow (j + 1) t
  have hmul := hpow.const_mul ((-1 : ℝ) ^ (j + 1) / (j + 1).factorial)
  refine hmul.congr_deriv ?_
  rw [flowCoef, Nat.factorial_succ, pow_succ]
  have hj : ((j.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

omit [Nonempty m] in
/-- The remainder solves the same linear equation the flow does: the
Taylor terms differentiate into one another and cancel, leaving
`d/dt Rₖ₊₁(t) = -ad_S(Rₖ(t))`. -/
theorem hasDerivAt_flowRemainder (S A : Matrix m m ℂ) (k : ℕ) (t : ℝ) :
    HasDerivAt (flowRemainder S A (k + 1))
      (-adOne S (flowRemainder S A k t)) t := by
  have hF : HasDerivAt (fun u => heisenbergFlow S u A)
      (-adOne S (heisenbergFlow S t A)) t := by
    refine (hasDerivAt_heisenbergFlow S A t).congr_deriv ?_
    rw [adOne]; noncomm_ring
  have hfun : (fun u : ℝ => ∑ j ∈ Finset.range (k + 1),
        flowCoef u j • adIter S j A)
      = fun u : ℝ => (∑ j ∈ Finset.range k,
          flowCoef u (j + 1) • adIter S (j + 1) A) + A := by
    funext u
    rw [Finset.sum_range_succ']
    simp
  have hsum : HasDerivAt
      (fun u : ℝ => ∑ j ∈ Finset.range (k + 1), flowCoef u j • adIter S j A)
      (∑ j ∈ Finset.range k, (-flowCoef t j) • adIter S (j + 1) A) t := by
    rw [hfun]
    have hterms : ∀ j ∈ Finset.range k,
        HasDerivAt (fun u : ℝ => flowCoef u (j + 1) • adIter S (j + 1) A)
          ((-flowCoef t j) • adIter S (j + 1) A) t :=
      fun j _ => (hasDerivAt_flowCoef t j).smul_const _
    simpa using (HasDerivAt.sum hterms).add_const A
  refine ((hF.sub hsum)).congr_deriv ?_
  rw [flowRemainder, adOne_sub, adOne_sum_range]
  have hshift : ∀ j : ℕ, adOne S (flowCoef t j • adIter S j A)
      = flowCoef t j • adIter S (j + 1) A := by
    intro j
    rw [adOne_smul, adIter_succ]
  simp only [hshift, neg_smul, Finset.sum_neg_distrib]
  abel

/-- ★★ **The Taylor remainder is small**: `‖Rₖ(t)‖ ≤ (2‖S‖|t|)ᵏ‖A‖`, so
the flow is approximated by the first `k` terms of its adjoint series to
that order. -/
theorem norm_flowRemainder_le {S : Matrix m m ℂ} (hS : Sᴴ = -S)
    (A : Matrix m m ℂ) (k : ℕ) (t : ℝ) :
    ‖flowRemainder S A k t‖ ≤ (2 * ‖S‖ * |t|) ^ k * ‖A‖ := by
  induction k generalizing t with
  | zero =>
    rw [flowRemainder_zero_terms, pow_zero, one_mul]
    exact norm_heisenbergFlow_le hS t A
  | succ k ih =>
    have h2 : (0 : ℝ) ≤ 2 * ‖S‖ := by positivity
    have hzero : flowRemainder S A (k + 1) 0 = 0 := by
      rw [flowRemainder, Finset.sum_range_succ']
      simp [flowCoef, heisenbergFlow]
    have hbound : ∀ u ∈ Set.uIcc (0 : ℝ) t,
        ‖-adOne S (flowRemainder S A k u)‖
          ≤ 2 * ‖S‖ * ((2 * ‖S‖ * |t|) ^ k * ‖A‖) := by
      intro u hu
      have hut : |u| ≤ |t| := by
        rcases Set.mem_uIcc.mp hu with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
        · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2')]; exact h2'
        · rw [abs_of_nonpos h2', abs_of_nonpos (h1.trans h2')]; linarith
      have hstep : ‖adOne S (flowRemainder S A k u)‖
          ≤ 2 * ‖S‖ * ‖flowRemainder S A k u‖ := by
        calc ‖adOne S (flowRemainder S A k u)‖
            ≤ ‖S * flowRemainder S A k u‖ + ‖flowRemainder S A k u * S‖ :=
              norm_sub_le _ _
          _ ≤ ‖S‖ * ‖flowRemainder S A k u‖
              + ‖flowRemainder S A k u‖ * ‖S‖ :=
              add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ = 2 * ‖S‖ * ‖flowRemainder S A k u‖ := by ring
      have hmono : (2 * ‖S‖ * |u|) ^ k * ‖A‖ ≤ (2 * ‖S‖ * |t|) ^ k * ‖A‖ := by
        gcongr
      rw [norm_neg]
      exact hstep.trans ((mul_le_mul_of_nonneg_left (ih u) h2).trans
        (mul_le_mul_of_nonneg_left hmono h2))
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := flowRemainder S A (k + 1))
      (f' := fun u => -adOne S (flowRemainder S A k u))
      (s := Set.uIcc (0 : ℝ) t)
      (C := 2 * ‖S‖ * ((2 * ‖S‖ * |t|) ^ k * ‖A‖))
      (fun u _ => (hasDerivAt_flowRemainder S A k u).hasDerivWithinAt)
      hbound (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [hzero, sub_zero] at hmvt
    calc ‖flowRemainder S A (k + 1) t‖
        ≤ 2 * ‖S‖ * ((2 * ‖S‖ * |t|) ^ k * ‖A‖) * |t| := hmvt
      _ = (2 * ‖S‖ * |t|) ^ (k + 1) * ‖A‖ := by ring

/-! ### The factorial remainder bound -/

omit [Nonempty m] in
/-- The remainder is differentiable at every time, hence continuous. -/
lemma exists_hasDerivAt_flowRemainder (S A : Matrix m m ℂ) (k : ℕ) (t : ℝ) :
    ∃ v, HasDerivAt (flowRemainder S A k) v t := by
  cases k with
  | zero =>
    refine ⟨heisenbergFlow S t A * S - S * heisenbergFlow S t A, ?_⟩
    have h := hasDerivAt_heisenbergFlow S A t
    have hfun : (fun u => heisenbergFlow S u A) = flowRemainder S A 0 := by
      funext u; rw [flowRemainder_zero_terms]
    rwa [hfun] at h
  | succ k => exact ⟨_, hasDerivAt_flowRemainder S A k t⟩

omit [Nonempty m] in
lemma continuous_flowRemainder (S A : Matrix m m ℂ) (k : ℕ) :
    Continuous (flowRemainder S A k) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨v, hv⟩ := exists_hasDerivAt_flowRemainder S A k t
  exact hv.continuousAt

omit [Nonempty m] in
lemma continuous_adOne_flowRemainder (S A : Matrix m m ℂ) (k : ℕ) :
    Continuous (fun s => -adOne S (flowRemainder S A k s)) := by
  have hc := continuous_flowRemainder S A k
  simp only [adOne]
  exact ((continuous_const.mul hc).sub (hc.mul continuous_const)).neg

/-- ★★★ **The factorial remainder bound.** Replacing the mean-value step
by an integral estimate sharpens `norm_flowRemainder_le` to
`‖Rₖ(t)‖ ≤ (2‖S‖t)ᵏ/k!·‖A‖`. The factorial is what makes the spatial
bound decay at *every* time rather than only below `2‖S‖t = 1`. -/
theorem norm_flowRemainder_le_factorial {S : Matrix m m ℂ} (hS : Sᴴ = -S)
    (A : Matrix m m ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖flowRemainder S A k t‖ ≤ (2 * ‖S‖ * t) ^ k / k.factorial * ‖A‖ := by
  induction k generalizing t with
  | zero =>
    rw [flowRemainder_zero_terms, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul]
    exact norm_heisenbergFlow_le hS t A
  | succ k ih =>
    have h2 : (0 : ℝ) ≤ 2 * ‖S‖ := by positivity
    have hkfac : (0 : ℝ) < (k.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos k
    set c : ℝ := 2 * ‖S‖ * ((2 * ‖S‖) ^ k / k.factorial * ‖A‖) with hcdef
    have hzero : flowRemainder S A (k + 1) 0 = 0 := by
      rw [flowRemainder, Finset.sum_range_succ']
      simp [flowCoef, heisenbergFlow]
    have hcont := continuous_adOne_flowRemainder S A k
    have hint : IntervalIntegrable
        (fun s => -adOne S (flowRemainder S A k s))
        MeasureTheory.volume 0 t := hcont.intervalIntegrable 0 t
    have hftc : ∫ s in (0 : ℝ)..t, -adOne S (flowRemainder S A k s)
        = flowRemainder S A (k + 1) t := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hasDerivAt_flowRemainder S A k s) hint, hzero, sub_zero]
    have hintnorm : IntervalIntegrable
        (fun s => ‖-adOne S (flowRemainder S A k s)‖)
        MeasureTheory.volume 0 t := hcont.norm.intervalIntegrable 0 t
    have hintbound : IntervalIntegrable (fun s : ℝ => c * s ^ k)
        MeasureTheory.volume 0 t :=
      (continuous_const.mul (continuous_pow k)).intervalIntegrable 0 t
    have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖-adOne S (flowRemainder S A k s)‖ ≤ c * s ^ k := by
      intro s hs
      have hstep : ‖adOne S (flowRemainder S A k s)‖
          ≤ 2 * ‖S‖ * ‖flowRemainder S A k s‖ := by
        calc ‖adOne S (flowRemainder S A k s)‖
            ≤ ‖S * flowRemainder S A k s‖ + ‖flowRemainder S A k s * S‖ :=
              norm_sub_le _ _
          _ ≤ ‖S‖ * ‖flowRemainder S A k s‖
              + ‖flowRemainder S A k s‖ * ‖S‖ :=
              add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ = 2 * ‖S‖ * ‖flowRemainder S A k s‖ := by ring
      rw [norm_neg]
      refine hstep.trans ?_
      refine (mul_le_mul_of_nonneg_left (ih hs.1) h2).trans ?_
      rw [hcdef, mul_pow]
      ring_nf
      rfl
    calc ‖flowRemainder S A (k + 1) t‖
        = ‖∫ s in (0 : ℝ)..t, -adOne S (flowRemainder S A k s)‖ := by
          rw [hftc]
      _ ≤ ∫ s in (0 : ℝ)..t, ‖-adOne S (flowRemainder S A k s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ ∫ s in (0 : ℝ)..t, c * s ^ k :=
          intervalIntegral.integral_mono_on ht hintnorm hintbound hpt
      _ = c * (t ^ (k + 1) / (k + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_pow]
          simp
      _ = (2 * ‖S‖ * t) ^ (k + 1) / (k + 1).factorial * ‖A‖ := by
          rw [hcdef, Nat.factorial_succ, mul_pow]
          push_cast
          field_simp
          ring

/-! ### Toward the spatial cone: nested commutators stay in the ball -/

end CSD.CV

namespace CSD.CV

variable {K N : ℕ}

/-- **One adjoint step grows support by at most one graph edge.** A term
whose edge misses the current region commutes with the observable and
contributes nothing; a term whose edge touches it contributes inside the
one-step neighbourhood. -/
theorem adOne_supportedOn_graphNeighborhood
    {E : Finset (Fin K × Fin K)}
    {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) :
    SupportedOn (graphNeighborhood E R) (adOne (∑ e ∈ E, G e) A) := by
  classical
  rw [adOne_sum]
  refine Finset.sum_induction _ (SupportedOn (graphNeighborhood E R))
    (fun a b ha hb => ha.add hb) SupportedOn.zero ?_
  intro e he
  by_cases htouch : e.1 ∈ R ∨ e.2 ∈ R
  · -- the edge touches the region: stay inside the neighbourhood
    have hGe : SupportedOn (graphNeighborhood E R) (G e) := by
      refine (hG e he).mono ?_
      intro x hx
      rcases Finset.mem_insert.mp hx with h1 | h2
      · exact h1 ▸ mem_graphNeighborhood_fst he htouch
      · rw [Finset.mem_singleton.mp h2]
        exact mem_graphNeighborhood_snd he htouch
    have hAn : SupportedOn (graphNeighborhood E R) A :=
      hA.mono (subset_graphNeighborhood E R)
    exact (hGe.mul hAn).sub (hAn.mul hGe)
  · -- the edge misses the region: the term commutes, so it drops out
    have hdisj : Disjoint ({e.1, e.2} : Finset (Fin K)) R := by
      rw [Finset.disjoint_left]
      intro x hx hxR
      rcases Finset.mem_insert.mp hx with h1 | h2
      · exact htouch (Or.inl (h1 ▸ hxR))
      · exact htouch (Or.inr (Finset.mem_singleton.mp h2 ▸ hxR))
    have hcomm := commute_of_disjointSupport hdisj (hG e he) hA
    rw [show adOne (G e) A = 0 from by rw [adOne, hcomm, sub_self]]
    exact SupportedOn.zero

/-- ★★ **The iterated adjoint action stays inside the graph ball.** After
`n` nested commutators with a sum of edge-supported generators, the
observable is still supported within the coupling graph's `n`-ball. This
is the combinatorial heart of a spatial light cone: it is the statement
that `n` steps of the dynamics reach at most `n` edges. -/
theorem adIter_supportedOn_graphBall
    {E : Finset (Fin K × Fin K)}
    {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) (n : ℕ) :
    SupportedOn (graphBall E R n) (adIter (∑ e ∈ E, G e) n A) := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    rw [adIter_succ, graphBall_succ]
    exact adOne_supportedOn_graphNeighborhood hG ih

/-- ★★ **Exact vanishing below the light cone.** If the coupling graph's
`n`-ball around `A`'s region has not yet reached `B`'s region, the `n`-th
nested commutator commutes with `B` exactly. Since the Heisenberg flow is
the exponential generating series of these iterates, this is what makes a
Lieb-Robinson series start at the graph distance rather than at zero. -/
theorem commutator_adIter_eq_zero
    {E : Finset (Fin K × Fin K)}
    {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    {R Y : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) (hB : SupportedOn Y B) {n : ℕ}
    (hcone : Disjoint (graphBall E R n) Y) :
    adIter (∑ e ∈ E, G e) n A * B = B * adIter (∑ e ∈ E, G e) n A :=
  commute_of_disjointSupport hcone (adIter_supportedOn_graphBall hG hA n) hB

/-! ### The spatial Lieb-Robinson bound -/

/-- ★★★ **The spatial Lieb-Robinson bound.** For observables supported on
regions `R` and `Y` of the coupling graph, and a skew-Hermitian generator
that is a sum of edge-supported terms, the commutator after time `t` is
bounded by `2‖A‖‖B‖·(2‖S‖|t|)^d` for **every** `d` whose graph ball around
`R` has not yet reached `Y`.

This is a light cone. Whenever `2‖S‖|t| < 1`, the bound decays
geometrically in the graph distance, so an observable at distance `d`
feels a disturbance only after a time of order `d / (2‖S‖)`: the
propagation speed is bounded by the coupling strength.

The proof combines the two halves. The Taylor remainder controls the flow
to order `d` (`norm_flowRemainder_le`), and every discarded term commutes
with `B` exactly, because `k` nested commutators reach at most `k` graph
edges (`commutator_adIter_eq_zero`). So the entire commutator is carried
by the remainder alone. -/
theorem norm_commutator_spatial_le [NeZero N]
    {E : Finset (Fin K × Fin K)}
    {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    (hS : (∑ e ∈ E, G e)ᴴ = -(∑ e ∈ E, G e))
    {R Y : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) (hB : SupportedOn Y B) {d : ℕ}
    (hcone : Disjoint (graphBall E R d) Y) (t : ℝ) :
    ‖heisenbergFlow (∑ e ∈ E, G e) t A * B
        - B * heisenbergFlow (∑ e ∈ E, G e) t A‖
      ≤ 2 * (2 * ‖∑ e ∈ E, G e‖ * |t|) ^ d * ‖A‖ * ‖B‖ := by
  set S := ∑ e ∈ E, G e with hSdef
  -- every discarded Taylor term commutes with the probe
  have hvanish : ∀ j ∈ Finset.range d,
      adIter S j A * B = B * adIter S j A := by
    intro j hj
    exact commutator_adIter_eq_zero hG hA hB
      (Finset.disjoint_of_subset_left
        (graphBall_mono E R (le_of_lt (Finset.mem_range.mp hj))) hcone)
  have hsumcomm : (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) * B
      = B * (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hvanish j hj]
  -- so the commutator is carried entirely by the remainder
  have hkey : heisenbergFlow S t A * B - B * heisenbergFlow S t A
      = flowRemainder S A d t * B - B * flowRemainder S A d t := by
    rw [flowRemainder, sub_mul, mul_sub, hsumcomm]
    abel
  rw [hkey]
  calc ‖flowRemainder S A d t * B - B * flowRemainder S A d t‖
      ≤ ‖flowRemainder S A d t * B‖ + ‖B * flowRemainder S A d t‖ :=
        norm_sub_le _ _
    _ ≤ ‖flowRemainder S A d t‖ * ‖B‖ + ‖B‖ * ‖flowRemainder S A d t‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖flowRemainder S A d t‖ * ‖B‖ := by ring
    _ ≤ 2 * ((2 * ‖S‖ * |t|) ^ d * ‖A‖) * ‖B‖ := by
        gcongr
        exact norm_flowRemainder_le hS A d t
    _ = 2 * (2 * ‖S‖ * |t|) ^ d * ‖A‖ * ‖B‖ := by ring

/-- ★★★ **The Lieb-Robinson bound.** Sharpening the geometric bound with
the factorial remainder estimate:
`‖[A(t), B]‖ ≤ 2‖A‖‖B‖·(2‖S‖t)^d/d!` for every `d` whose graph ball around
`A`'s region has not reached `B`'s.

Because of the factorial this decays in the graph distance at **every**
time, not only for `2‖S‖t < 1`: at fixed `t` the bound falls faster than
geometrically in `d`, which is the standard Lieb-Robinson statement that
the commutator is exponentially small outside an effective light cone. -/
theorem norm_commutator_spatial_factorial_le [NeZero N]
    {E : Finset (Fin K × Fin K)}
    {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    (hS : (∑ e ∈ E, G e)ᴴ = -(∑ e ∈ E, G e))
    {R Y : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) (hB : SupportedOn Y B) {d : ℕ}
    (hcone : Disjoint (graphBall E R d) Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow (∑ e ∈ E, G e) t A * B
        - B * heisenbergFlow (∑ e ∈ E, G e) t A‖
      ≤ 2 * ((2 * ‖∑ e ∈ E, G e‖ * t) ^ d / d.factorial) * ‖A‖ * ‖B‖ := by
  set S := ∑ e ∈ E, G e with hSdef
  have hvanish : ∀ j ∈ Finset.range d,
      adIter S j A * B = B * adIter S j A := by
    intro j hj
    exact commutator_adIter_eq_zero hG hA hB
      (Finset.disjoint_of_subset_left
        (graphBall_mono E R (le_of_lt (Finset.mem_range.mp hj))) hcone)
  have hsumcomm : (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) * B
      = B * (∑ j ∈ Finset.range d, flowCoef t j • adIter S j A) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hvanish j hj]
  have hkey : heisenbergFlow S t A * B - B * heisenbergFlow S t A
      = flowRemainder S A d t * B - B * flowRemainder S A d t := by
    rw [flowRemainder, sub_mul, mul_sub, hsumcomm]
    abel
  rw [hkey]
  calc ‖flowRemainder S A d t * B - B * flowRemainder S A d t‖
      ≤ ‖flowRemainder S A d t * B‖ + ‖B * flowRemainder S A d t‖ :=
        norm_sub_le _ _
    _ ≤ ‖flowRemainder S A d t‖ * ‖B‖ + ‖B‖ * ‖flowRemainder S A d t‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖flowRemainder S A d t‖ * ‖B‖ := by ring
    _ ≤ 2 * ((2 * ‖S‖ * t) ^ d / d.factorial * ‖A‖) * ‖B‖ := by
        gcongr
        exact norm_flowRemainder_le_factorial hS A d ht
    _ = 2 * ((2 * ‖S‖ * t) ^ d / d.factorial) * ‖A‖ * ‖B‖ := by ring

/-! ### The CV instantiation -/

/-- ★ **On the field**: for observables supported on disjoint mode sets, the
commutator after time `t` is bounded by the cut coupling alone. The
zero-time commutation hypothesis is supplied by CV-8's
`commute_of_disjointSupport`, so only the generator split has to be
provided. -/
theorem norm_commutator_field_le {K N : ℕ} [NeZero N]
    {S S_X T : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    {R Y : Finset (Fin K)} {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hS : Sᴴ = -S) (hSX : S_Xᴴ = -S_X) (hsplit : S = S_X + T)
    (hcomm : S_X * B = B * S_X) (hRY : Disjoint R Y)
    (hA : SupportedOn R A) (hB : SupportedOn Y B) (t : ℝ) :
    ‖heisenbergFlow S t A * B - B * heisenbergFlow S t A‖
      ≤ 4 * |t| * ‖T‖ * ‖A‖ * ‖B‖ :=
  norm_commutator_heisenbergFlow_le hS hSX hsplit hcomm
    (commute_of_disjointSupport hRY hA hB) t

/-! ### CV-20 (Stage 6): the velocity, made explicit -/

/-- The exponential-series lower bound in the form the velocity extraction
needs: `d^d ≤ e^d · d!` (one term of the series for `exp d`). -/
lemma pow_pow_le_exp_mul_factorial (d : ℕ) :
    (d : ℝ) ^ d ≤ Real.exp d * d.factorial := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (d : ℝ)) (Nat.cast_nonneg d)
    (d + 1)
  have hterm : (d : ℝ) ^ d / d.factorial
      ≤ ∑ i ∈ Finset.range (d + 1), (d : ℝ) ^ i / i.factorial :=
    Finset.single_le_sum (f := fun i => (d : ℝ) ^ i / i.factorial)
      (fun i _ => by positivity) (Finset.self_mem_range_succ d)
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hle := hterm.trans hsum
  calc (d : ℝ) ^ d = ((d : ℝ) ^ d / d.factorial) * d.factorial := by
        field_simp
    _ ≤ Real.exp d * d.factorial := mul_le_mul_of_nonneg_right hle hfac.le

/-- Outside `x ≤ d/e²` the series term dies exponentially:
`x^d/d! ≤ e^{−d}`. The arithmetic engine of the velocity bound. -/
lemma pow_div_factorial_le_exp_neg {x : ℝ} (hx : 0 ≤ x) {d : ℕ}
    (h : Real.exp 1 ^ 2 * x ≤ d) :
    x ^ d / d.factorial ≤ Real.exp (-(d : ℝ)) := by
  have he2 : (0 : ℝ) < Real.exp 1 ^ 2 := by positivity
  have hfac : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast d.factorial_pos
  have hxd : x ≤ (d : ℝ) / Real.exp 1 ^ 2 := by
    rw [le_div_iff₀ he2]
    linarith
  have hpow : x ^ d ≤ ((d : ℝ) / Real.exp 1 ^ 2) ^ d :=
    pow_le_pow_left₀ hx hxd d
  have hepow : (Real.exp 1 ^ 2) ^ d = Real.exp (2 * d) := by
    rw [← pow_mul, Real.exp_one_pow]
    push_cast
    ring_nf
  have hkey : ((d : ℝ) / Real.exp 1 ^ 2) ^ d
      ≤ Real.exp (-(d : ℝ)) * d.factorial := by
    rw [div_pow, hepow, div_le_iff₀ (by positivity)]
    calc (d : ℝ) ^ d ≤ Real.exp d * d.factorial :=
          pow_pow_le_exp_mul_factorial d
      _ = Real.exp (-(d : ℝ)) * (d.factorial : ℝ) * Real.exp (2 * d) := by
          rw [mul_right_comm, ← Real.exp_add]
          ring_nf
  rw [div_le_iff₀ hfac]
  exact hpow.trans hkey

/-- ★★★ **The Lieb–Robinson velocity** (CV-20, Stage 6): outside the cone
`v·t ≤ d` with `v := 2e²·‖S‖`, the commutator is **exponentially small in
the graph distance** — `‖[A(t), B]‖ ≤ 2‖A‖‖B‖·e^{−d}`. The Stage-5
factorial bound with the velocity constant made explicit: information
propagates through the coupling graph no faster than `2e²‖S‖` edges per
unit time, up to exponentially small tails. No optimality of the constant
is claimed. -/
theorem norm_commutator_velocity_le {K N : ℕ} [NeZero N]
    {E : Finset (Fin K × Fin K)}
    {G : Fin K × Fin K → Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : ∀ e ∈ E, SupportedOn {e.1, e.2} (G e))
    (hS : (∑ e ∈ E, G e)ᴴ = -(∑ e ∈ E, G e))
    {R Y : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn R A) (hB : SupportedOn Y B) {d : ℕ}
    (hcone : Disjoint (graphBall E R d) Y) {t : ℝ} (ht : 0 ≤ t)
    (hv : Real.exp 1 ^ 2 * (2 * ‖∑ e ∈ E, G e‖ * t) ≤ d) :
    ‖heisenbergFlow (∑ e ∈ E, G e) t A * B
        - B * heisenbergFlow (∑ e ∈ E, G e) t A‖
      ≤ 2 * Real.exp (-(d : ℝ)) * ‖A‖ * ‖B‖ := by
  have hx : (0 : ℝ) ≤ 2 * ‖∑ e ∈ E, G e‖ * t := by positivity
  calc ‖heisenbergFlow (∑ e ∈ E, G e) t A * B
        - B * heisenbergFlow (∑ e ∈ E, G e) t A‖
      ≤ 2 * ((2 * ‖∑ e ∈ E, G e‖ * t) ^ d / d.factorial) * ‖A‖ * ‖B‖ :=
        norm_commutator_spatial_factorial_le hG hS hA hB hcone ht
    _ ≤ 2 * Real.exp (-(d : ℝ)) * ‖A‖ * ‖B‖ := by
        gcongr
        exact pow_div_factorial_le_exp_neg hx hv

end CSD.CV

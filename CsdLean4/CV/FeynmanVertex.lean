/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.DysonVertex
public import CsdLean4.CV.WickGeneral
public import CsdLean4.CV.LiebRobinson

/-!
# CV-27: Feynman diagrams at the cutoff — the Dyson vertices meet Wick

**Category:** 3-Local (CV; continuous variables — the multi-mode field).

The three pieces of the diagrammatic rung are landed separately: Wick's theorem for an arbitrary
equal-time word (`CV/WickGeneral.lean`) and at four points with the phases on (`CV/Wick.lean`),
the Dyson series (`Analysis/Matrix/DysonSeries.lean`), and the vertex bookkeeping
(`Analysis/Matrix/DysonVertex.lean`). This module joins them on the lattice field: the Dyson
expansion of the propagator `exp (−i t (H_field + lam·V))` of the free field perturbed by a
polynomial vertex `V`, its terms as vacuum diagrams, and the diagrams evaluated by Wick.

* `neg_I_smul_fieldHamiltonian` — the free generator `−i H_field` is diagonal with entries
  `−i E_c`, so the eigenbasis form of the bookkeeping applies verbatim;
* ★ `interactionPicture_neg_I_smul_fieldHamiltonian` — **the interaction-picture vertex is the
  free Heisenberg vertex**, `V_I(s) = U(s)† V U(s)` with `U(s) = freeFieldU K N s`: the same object
  whose products the time-separated Wick theorem evaluates
  (`heisenbergFlow_eq_interactionPicture` identifies it with CV-17's flow as well);
* ★★ `hasSum_dysonTerm_fieldHamiltonian` — **the lattice propagator is the sum of its vacuum
  diagrams' generating series**: for Hermitian `V` and `0 ≤ t`,
  `exp (−i t (H_field + lam·V)) = ∑ₙ Dₙ(t)`;
* ★ `dysonTerm_one_vac` — **the one-vertex vacuum amplitude for any vertex**:
  `D₁(t) vac vac = e^{−i t E₀} · t · (−i lam) · ⟨vac∣V∣vac⟩` — the vacuum phase cancels between the
  two legs of the vertex, which is inserted with the same weight at every time in `[0, t]`;
  ★★ `dysonTerm_one_vac_wordOp` — **the first-order vacuum diagram, by Wick**: for a monomial
  vertex `V = Q_{k₁} ⋯ Q_{kₘ}` below the threshold, `⟨vac∣V∣vac⟩ = ∏_k wickMoment (count k)` — the
  sum over pairings of the vertex's own legs (the figure-eight of `Q⁴`, value `3/4`; the tadpole
  of `Q²`, value `1/2`);
* ★ `dysonTerm_two_vac` — **the two-vertex vacuum amplitude for any vertex**: the double integral
  over the ordered times `0 ≤ s₁ ≤ s₂ ≤ t` of the two-time free correlator
  `⟨vac∣ V · U(s₁ − s₂)† V U(s₁ − s₂) ∣vac⟩` of the vertex with itself — only the time difference
  enters, the vacuum eigenphase having cancelled;
  `vertexPair_eq_timeFourPoint` — for the quadratic vertex `V = Q_a Q_b` that correlator IS
  CV-23b's `timeFourPoint τ 0 0 1 1 a b a b`, and
  ★★ `dysonTerm_two_vac_quadratic` — **the second-order vacuum diagrams, by Wick**
  (`2 < N`): the integrand is the three-pairing sum of stroboscopic kernels at the time
  difference; ★ `dysonTerm_two_vac_quadratic_of_ne` — distinct modes `a ≠ b`: only the
  **connected bubble** `K(0,1)²` survives, both propagators running between the two vertices;
  ★ `dysonTerm_two_vac_quadratic_self` — one mode `V = Q_a²`: the **disconnected double tadpole**
  `¼ = ⟨Q²⟩⟨Q²⟩` plus two bubbles `2 K(0,1)²`, the textbook `⟨Q²(s₂) Q²(s₁)⟩ = ⟨Q²⟩² + 2⟨Q(s₂)Q(s₁)⟩²`.

**Reading.** A term of the Dyson series at order `n` is a diagram with `n` vertices at ordered
times; the eigenbasis recursion `dysonTermI_succ_apply_diagonal` places a free propagation
between consecutive vertices; and at the vacuum the free correlator of the vertices is Wick's
pairing sum, each pairing a product of propagator lines `twoPointKernel`. First order needs Wick
at equal time (any vertex, any length — landed generally); second order needs Wick at two times
(landed at four points, so for quadratic vertices).

## Honest scope

⚠️ **Orders one and two by Wick; every order by bookkeeping.** The `n`-th order vacuum amplitude
is the ordered `n`-fold integral of an `(n − 1)`-time free correlator of vertices
(`dysonTermI_succ_apply_diagonal`, all `n`); evaluating it as a sum over pairings needs the
time-separated Wick theorem for words of length `n·deg V`, which the corpus has at four points
only. The general time-separated Wick theorem is priced separately (BACKLOG #36(b)(iv)).

⚠️ **Vacuum bubbles, not scattering amplitudes.** The objects are transition amplitudes
`⟨vac∣ exp (−i t (H₀ + lam V)) ∣vac⟩` at finite `t`; no adiabatic switching, no Gell-Mann–Low
formula, no cancellation of disconnected diagrams against a denominator. At the cutoff these
amplitudes are exact matrix elements, which is why the statements are theorems.

⚠️ **Finite cutoff.** The thresholds `count k / 2 < N`, `2 < N` are where Wick survives
truncation, as in CV-23; nothing continuum is claimed.

References: `Analysis/Matrix/DysonSeries.lean`, `Analysis/Matrix/DysonVertex.lean` (Category 1);
`CV/Wick.lean` (CV-23b, `timeFourPoint_wick`, `twoPointKernel`); `CV/WickGeneral.lean`
(`wordOp_vac_eq_prod_wickMoment`); `CV/ThermalPropagator.lean` (`heisenberg_freeFieldU_pow_apply`);
`CV/LiebRobinson.lean` (CV-17, `heisenbergFlow`); `CV/InteractionPrice.lean`
(`fieldHamiltonian_isHermitian`); `specs/BACKLOG.md` #36(b)(iii); `specs/future-work.md`
(row CV-27, FP-1).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix NormedSpace

namespace CSD.CV

variable {K N : ℕ}

/-! ### The free generator in its eigenbasis -/

/-- The free generator `−i H_field` is diagonal with entries `−i E_c`. -/
theorem neg_I_smul_fieldHamiltonian :
    (-Complex.I) • fieldHamiltonian K N
      = Matrix.diagonal fun c : FieldConfig K N =>
          -Complex.I * ((fieldEnergy c : ℝ) : ℂ) := by
  rw [fieldHamiltonian, ← Matrix.diagonal_smul]
  rfl

/-- ★ **The interaction-picture vertex is the free Heisenberg vertex**:
`exp (−s (−i H)) · V · exp (s (−i H)) = U(s)† V U(s)` with `U(s) = freeFieldU K N s`. -/
theorem interactionPicture_neg_I_smul_fieldHamiltonian
    (V : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (s : ℝ) :
    interactionPicture ((-Complex.I) • fieldHamiltonian K N) V s
      = heisenberg (freeFieldU K N s) V := by
  ext c d
  rw [neg_I_smul_fieldHamiltonian, interactionPicture_diagonal_apply,
    ← pow_one (freeFieldU K N s), heisenberg_freeFieldU_pow_apply]
  congr 2
  push_cast
  ring

/-- CV-17's Heisenberg flow is the interaction picture of `DysonVertex.lean`, argument order
aside. -/
theorem heisenbergFlow_eq_interactionPicture {m : Type*} [Fintype m] [DecidableEq m]
    (S A : Matrix m m ℂ) (t : ℝ) :
    heisenbergFlow S t A = interactionPicture S A t :=
  rfl

/-! ### The propagator as the sum of its diagrams -/

/-- ★★ **The lattice propagator is the sum of the Dyson series** in the coupling: for a Hermitian
vertex `V` and `0 ≤ t`, `exp (−i t (H_field + lam·V)) = ∑ₙ Dₙ(t)`. -/
theorem hasSum_dysonTerm_fieldHamiltonian [NeZero N] (lam : ℝ)
    {V : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hV : V.IsHermitian) {t : ℝ}
    (ht : 0 ≤ t) :
    HasSum (fun n => dysonTerm ((-Complex.I) • fieldHamiltonian K N)
        ((-Complex.I) • (lam • V)) n t)
      (exp (t • ((-Complex.I) • (fieldHamiltonian K N + lam • V)))) :=
  hasSum_dysonTerm_of_isHermitian (fieldHamiltonian_isHermitian K N)
    (isHermitian_real_smul hV lam) ht

/-! ### One vertex -/

/-- ★ **The one-vertex vacuum amplitude for any vertex**:
`D₁(t) vac vac = e^{−i t E₀} · t · (−i lam) · ⟨vac∣V∣vac⟩`. -/
theorem dysonTerm_one_vac [NeZero N] (lam : ℝ)
    (V : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (t : ℝ) :
    dysonTerm ((-Complex.I) • fieldHamiltonian K N) ((-Complex.I) • (lam • V)) 1 t
        (vacCfg K N) (vacCfg K N)
      = Complex.exp (t * (-Complex.I * ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)))
          * (t * (-Complex.I * (lam * V (vacCfg K N) (vacCfg K N)))) := by
  rw [neg_I_smul_fieldHamiltonian, dysonTerm_one_apply_diagonal_self, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.real_smul]

/-- ★★ **The first-order vacuum diagram, by Wick**: for a monomial vertex `Q_{k₁} ⋯ Q_{kₘ}` below
the threshold, `D₁(t) vac vac = e^{−i t E₀} · t · (−i lam) · ∏_k wickMoment (count k)` — the sum
over pairings of the vertex's own legs. -/
theorem dysonTerm_one_vac_wordOp [NeZero N] (lam : ℝ) (w : List (Fin K))
    (hw : ∀ k : Fin K, w.count k / 2 < N) (t : ℝ) :
    dysonTerm ((-Complex.I) • fieldHamiltonian K N) ((-Complex.I) • (lam • wordOp (N := N) w))
        1 t (vacCfg K N) (vacCfg K N)
      = Complex.exp (t * (-Complex.I * ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)))
          * (t * (-Complex.I * (lam * ∏ k : Fin K, wickMoment (w.count k)))) := by
  rw [dysonTerm_one_vac, wordOp_vac_eq_prod_wickMoment w hw]

/-! ### Two vertices -/

/-- ★ **The two-vertex vacuum amplitude for any vertex**: the double integral over the ordered
vertex times of the two-time free correlator `⟨vac∣ V · U(s₁ − s₂)† V U(s₁ − s₂) ∣vac⟩` — only
the time difference enters. -/
theorem dysonTerm_two_vac [NeZero N] (lam : ℝ)
    (V : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (t : ℝ) :
    dysonTerm ((-Complex.I) • fieldHamiltonian K N) ((-Complex.I) • (lam • V)) 2 t
        (vacCfg K N) (vacCfg K N)
      = Complex.exp (t * (-Complex.I * ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)))
          * ((-Complex.I * lam) ^ 2 * ∫ s₂ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s₂,
              (V * heisenberg (freeFieldU K N (s₁ - s₂)) V) (vacCfg K N) (vacCfg K N)) := by
  rw [dysonTerm_eq_exp_smul_mul_dysonTermI, neg_I_smul_fieldHamiltonian, exp_smul_diagonal,
    Matrix.diagonal_mul, dysonTermI_two_apply_diagonal_self]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s₂ _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s₁ _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← pow_one (freeFieldU K N (s₁ - s₂)), heisenberg_freeFieldU_pow_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Nat.cast_one, one_mul,
    Complex.ofReal_sub]
  rw [show ((s₂ : ℂ) - (s₁ : ℂ))
        * (-Complex.I * ((fieldEnergy k : ℝ) : ℂ)
          - -Complex.I * ((fieldEnergy (vacCfg K N) : ℝ) : ℂ))
      = Complex.I * ((s₁ : ℂ) - (s₂ : ℂ))
        * (((fieldEnergy k : ℝ) : ℂ) - ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)) by ring]
  ring

/-- For the quadratic vertex `V = Q_a Q_b`, the two-time vertex correlator is CV-23b's four-point
function at periods `(0, 0, 1, 1)` and step `τ`. -/
theorem vertexPair_eq_timeFourPoint [NeZero N] (τ : ℝ) (a b : Fin K) :
    (modeOp a (Q N) * modeOp b (Q N)
        * heisenberg (freeFieldU K N τ) (modeOp a (Q N) * modeOp b (Q N)))
        (vacCfg K N) (vacCfg K N)
      = timeFourPoint (N := N) τ 0 0 1 1 a b a b := by
  rw [heisenberg_mul_op, ← Matrix.mul_assoc, timeFourPoint, pow_zero, heisenberg_one,
    heisenberg_one, pow_one]

/-- ★★ **The second-order vacuum diagrams, by Wick.** For the quadratic vertex `Q_a Q_b` above the
threshold `2 < N`, the integrand of the two-vertex amplitude is the three-pairing sum of
stroboscopic kernels at the time difference `τ = s₁ − s₂`: the pairing within each vertex
(`K(0,0) K(1,1)`, the disconnected double tadpole, present only for `a = b`) and the two pairings
across the vertices (`K(0,1)²`, the bubbles — one for every mode pattern, one more for
`a = b`). -/
theorem dysonTerm_two_vac_quadratic [NeZero N] (hN2 : 2 < N) (lam : ℝ) (a b : Fin K) (t : ℝ) :
    dysonTerm ((-Complex.I) • fieldHamiltonian K N)
        ((-Complex.I) • (lam • (modeOp a (Q N) * modeOp b (Q N)))) 2 t
        (vacCfg K N) (vacCfg K N)
      = Complex.exp (t * (-Complex.I * ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)))
          * ((-Complex.I * lam) ^ 2 * ∫ s₂ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s₂,
              ((if a = b then twoPointKernel (s₁ - s₂) 0 0 else 0)
                  * (if a = b then twoPointKernel (s₁ - s₂) 1 1 else 0)
                + twoPointKernel (s₁ - s₂) 0 1 * twoPointKernel (s₁ - s₂) 0 1
                + (if a = b then twoPointKernel (s₁ - s₂) 0 1 else 0)
                  * (if b = a then twoPointKernel (s₁ - s₂) 0 1 else 0))) := by
  rw [dysonTerm_two_vac]
  congr 2
  refine intervalIntegral.integral_congr fun s₂ _ => ?_
  refine intervalIntegral.integral_congr fun s₁ _ => ?_
  rw [vertexPair_eq_timeFourPoint, timeFourPoint_wick hN2, if_pos (rfl : a = a),
    if_pos (rfl : b = b)]

/-- ★ **The connected bubble**: for distinct modes `a ≠ b` only the pairing across the vertices
survives, both propagator lines running from one vertex to the other. -/
theorem dysonTerm_two_vac_quadratic_of_ne [NeZero N] (hN2 : 2 < N) (lam : ℝ) {a b : Fin K}
    (hab : a ≠ b) (t : ℝ) :
    dysonTerm ((-Complex.I) • fieldHamiltonian K N)
        ((-Complex.I) • (lam • (modeOp a (Q N) * modeOp b (Q N)))) 2 t
        (vacCfg K N) (vacCfg K N)
      = Complex.exp (t * (-Complex.I * ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)))
          * ((-Complex.I * lam) ^ 2 * ∫ s₂ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s₂,
              twoPointKernel (s₁ - s₂) 0 1 ^ 2) := by
  rw [dysonTerm_two_vac_quadratic hN2]
  congr 2
  refine intervalIntegral.integral_congr fun s₂ _ => ?_
  refine intervalIntegral.integral_congr fun s₁ _ => ?_
  rw [if_neg hab, if_neg hab, if_neg hab, if_neg (Ne.symm hab)]
  ring

/-- ★ **The disconnected double tadpole and the two bubbles**: for the one-mode vertex `Q_a²` the
integrand is `¼ + 2 K(0,1)²` — `⟨Q²(s₂) Q²(s₁)⟩ = ⟨Q²⟩² + 2 ⟨Q(s₂) Q(s₁)⟩²`. -/
theorem dysonTerm_two_vac_quadratic_self [NeZero N] (hN2 : 2 < N) (lam : ℝ) (a : Fin K)
    (t : ℝ) :
    dysonTerm ((-Complex.I) • fieldHamiltonian K N)
        ((-Complex.I) • (lam • (modeOp a (Q N) * modeOp a (Q N)))) 2 t
        (vacCfg K N) (vacCfg K N)
      = Complex.exp (t * (-Complex.I * ((fieldEnergy (vacCfg K N) : ℝ) : ℂ)))
          * ((-Complex.I * lam) ^ 2 * ∫ s₂ in (0 : ℝ)..t, ∫ s₁ in (0 : ℝ)..s₂,
              ((2 : ℂ)⁻¹ * 2⁻¹ + 2 * twoPointKernel (s₁ - s₂) 0 1 ^ 2)) := by
  rw [dysonTerm_two_vac_quadratic hN2]
  congr 2
  refine intervalIntegral.integral_congr fun s₂ _ => ?_
  refine intervalIntegral.integral_congr fun s₁ _ => ?_
  rw [if_pos rfl, if_pos rfl, if_pos rfl, twoPointKernel_self, twoPointKernel_self]
  ring

end CSD.CV

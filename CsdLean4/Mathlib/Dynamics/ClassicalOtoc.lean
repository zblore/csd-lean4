/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.CatMapShears

/-!
# The classical out-of-time-order correlator of a linear map, and the cat map's

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #149 (out of ~~#101~~(b)); consumed by `SigmaLayer/FibreOtoc.lean`.

The quantum out-of-time-order correlator is the commutator norm `‖[A(n), B]‖` of a Heisenberg-evolved
observable against a probe (`QuantumChaos.otoc`, `Incubator/QuantumChaos/Otoc.lean`). Its classical
analogue replaces the commutator by the **Poisson bracket**: for a map `Φ` of the plane with
canonical coordinates `(x, p)`, the classical OTOC at step `n` is `{x ∘ Φⁿ, p}`, which by the chain
rule is the `(1,1)` entry `∂(Φⁿ)₁/∂x` of the derivative `DΦⁿ`. For a linear map `A` the derivative is
`A` itself and the bracket is constant in the phase point, so the classical OTOC is a number:
`classicalOtoc A n = ((Aⁿ) (1, 0)).1` (`classicalOtoc_eq`).

## The cat map

The powers of the cat matrix are Fibonacci matrices,
`catR ^ n = [[F_{2n+1}, F_{2n}], [F_{2n}, F_{2n−1}]]` (`catR_pow_apply`, with `F_{2n−1}` written
`F_{2n+1} − F_{2n}` so that `n = 0` is the identity), so

* ★ `classicalOtoc_catR`: the classical OTOC of the cat map at step `n` is **exactly** `F_{2n+1}`;
* ★★ `tendsto_log_classicalOtoc_catR`: it grows at the exponential rate `2 log φ`, **the Lyapunov
  exponent** — read off `hasLyapunovExponent_catR` for the direction `(1, 0)`, because the sup norm
  of `(F_{2n+1}, F_{2n})` is `F_{2n+1}`;
* ★ `tendsto_log_classicalOtoc_sq_catR`: the **squared** bracket, the textbook `C(t)`, grows at
  `4 log φ` — twice the Lyapunov exponent, as the textbook says;
* `classicalOtoc_catR_binet`: Binet's form `(φ^{2n+1} − ψ^{2n+1}) / √5`.

## The maps that do not scramble

* `classicalOtoc_id`: the identity (the derivative of every translation) has classical OTOC `1`
  at every step, rate `0` (`tendsto_log_classicalOtoc_id`).
* `classicalOtoc_shearXR`, `classicalOtoc_shearYR`: each of the two shears that compose to the cat
  map (`CatMapShears.lean`) has classical OTOC `1` at every step. The transverse bracket
  `{p ∘ shearYRⁿ, p}` of the vertical shear is `n` (`poissonBracket_snd_shearYR`): at most linear,
  never exponential. The exponential growth is produced by composing the two.

## Honest scope

* **Linear maps, and the Poisson bracket of linear coordinate functions.** `poissonBracket` is
  defined for any two differentiable functions of the plane, but the only brackets evaluated here
  are those of linear functions, where the bracket is a constant (`poissonBracket_clm_snd`). No
  averaging over a phase-space measure is performed, and none is needed: the integrand is constant.
* ⚠️ **The row that priced this file said the classical OTOC is the `(1,2)` entry `F_{2n}`.** The
  bracket `{x ∘ Φⁿ, p}` is the `(1,1)` entry `F_{2n+1}`; the `(1,2)` and `(2,1)` entries `F_{2n}` are
  the brackets `−{x ∘ Φⁿ, x}` and `{p ∘ Φⁿ, p}`. Every entry grows at the same rate `2 log φ`, so
  nothing the row concluded changes; the entry is corrected here. The row's "twice the Lyapunov
  exponent" is the rate of the *squared* bracket.
* **Not the quantum OTOC.** The exponential regime of `QuantumChaos.otoc` up to the Ehrenfest time
  needs a quantised cat map (Hannay–Berry), which the corpus does not have; see the row.

References: Maldacena–Shenker–Stanford, *A bound on chaos* (2016), §1 (the classical limit of the
OTOC as a Poisson bracket); Katok–Hasselblatt §1.8; `Mathlib/Dynamics/LyapunovExponent.lean`
(`catR`, `hasLyapunovExponent_catR`), `Mathlib/Dynamics/CatMapShears.lean` (`shearXR`, `shearYR`,
`shearXR_pow_apply`), `Incubator/QuantumChaos/Otoc.lean` (`QuantumChaos.otoc`),
`CV/ChaosBounds.lean` (`otoc_interactingU_le`, the corpus's at-most-linear quantum family);
`specs/BACKLOG.md` #149, ~~#148~~, ~~#153~~.
-/

@[expose] public section

open Filter Topology Real
open scoped goldenRatio

/-! ### The Poisson bracket, and the classical OTOC of a linear map -/

/-- The **Poisson bracket** `{f, g} = ∂ₓf ∂ₚg − ∂ₚf ∂ₓg` of two functions of the plane, with
canonical coordinates `(x, p) = (v.1, v.2)`. -/
noncomputable def poissonBracket (f g : ℝ × ℝ → ℝ) (v : ℝ × ℝ) : ℝ :=
  fderiv ℝ f v (1, 0) * fderiv ℝ g v (0, 1) - fderiv ℝ f v (0, 1) * fderiv ℝ g v (1, 0)

/-- The bracket of a linear function with the momentum coordinate is its `x`-coefficient, at every
phase point. -/
theorem poissonBracket_clm_snd (L : (ℝ × ℝ) →L[ℝ] ℝ) (v : ℝ × ℝ) :
    poissonBracket L Prod.snd v = L (1, 0) := by
  unfold poissonBracket
  rw [L.fderiv, fderiv_snd]
  simp

/-- The **classical OTOC** of a linear map `A` of the plane at step `n`: the Poisson bracket
`{x ∘ Aⁿ, p}` of the evolved position with the momentum. It is constant in the phase point
(`classicalOtoc_eq`), so it is evaluated at the origin. -/
noncomputable def classicalOtoc (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (n : ℕ) : ℝ :=
  poissonBracket (fun v => ((A ^ n) v).1) Prod.snd 0

/-- The classical OTOC is the `(1,1)` entry of `Aⁿ`. -/
theorem classicalOtoc_eq (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (n : ℕ) :
    classicalOtoc A n = ((A ^ n) (1, 0)).1 := by
  unfold classicalOtoc
  exact poissonBracket_clm_snd ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (A ^ n)) 0

/-- The bracket `{x ∘ Aⁿ, p}` does not depend on the phase point. -/
theorem poissonBracket_pow_fst_snd (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (n : ℕ) (v : ℝ × ℝ) :
    poissonBracket (fun v => ((A ^ n) v).1) Prod.snd v = classicalOtoc A n := by
  rw [classicalOtoc_eq]
  exact poissonBracket_clm_snd ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (A ^ n)) v

/-- The transverse bracket `{p ∘ Aⁿ, p}` is the `(2,1)` entry of `Aⁿ`. -/
theorem poissonBracket_pow_snd_snd (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (n : ℕ) (v : ℝ × ℝ) :
    poissonBracket (fun v => ((A ^ n) v).2) Prod.snd v = ((A ^ n) (1, 0)).2 :=
  poissonBracket_clm_snd ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (A ^ n)) v

/-! ### The maps that do not scramble -/

/-- The identity has classical OTOC `1` at every step. -/
theorem classicalOtoc_id (n : ℕ) : classicalOtoc (ContinuousLinearMap.id ℝ (ℝ × ℝ)) n = 1 := by
  rw [classicalOtoc_eq, ← ContinuousLinearMap.one_def, one_pow]
  rfl

/-- The identity's classical OTOC has growth rate `0`. -/
theorem tendsto_log_classicalOtoc_id :
    Tendsto (fun n : ℕ => Real.log (classicalOtoc (ContinuousLinearMap.id ℝ (ℝ × ℝ)) n) / n)
      atTop (𝓝 0) := by
  simp [classicalOtoc_id]

namespace MeasureTheory

/-- The horizontal shear has classical OTOC `1` at every step. -/
theorem classicalOtoc_shearXR (n : ℕ) : classicalOtoc shearXR n = 1 := by
  rw [classicalOtoc_eq, shearXR_pow_apply]
  simp

/-- The vertical shear has classical OTOC `1` at every step. -/
theorem classicalOtoc_shearYR (n : ℕ) : classicalOtoc shearYR n = 1 := by
  rw [classicalOtoc_eq, shearYR_pow_apply]

/-- The vertical shear's transverse bracket `{p ∘ shearYRⁿ, p}` is `n`: linear, not exponential. -/
theorem poissonBracket_snd_shearYR (n : ℕ) (v : ℝ × ℝ) :
    poissonBracket (fun v => ((shearYR ^ n) v).2) Prod.snd v = n := by
  rw [poissonBracket_pow_snd_snd, shearYR_pow_apply]
  simp

/-! ### The cat map's powers are Fibonacci matrices -/

/-- The first column of `catR ^ n` is `(F_{2n+1}, F_{2n})`. -/
theorem catR_pow_one_zero (n : ℕ) :
    (catR ^ n) (1, 0) = ((Nat.fib (2 * n + 1) : ℝ), (Nat.fib (2 * n) : ℝ)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ih, catR_apply]
      have e1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      have e2 : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [e1, e2, Nat.fib_add_two (n := 2 * k + 1), Nat.fib_add_two (n := 2 * k)]
      refine Prod.ext ?_ ?_
      · simp only; push_cast; ring
      · simp only; push_cast; ring

/-- The second column of `catR ^ n` is `(F_{2n}, F_{2n−1})`, with `F_{2n−1}` written
`F_{2n+1} − F_{2n}` so that `n = 0` gives the identity's column `(0, 1)`. -/
theorem catR_pow_zero_one (n : ℕ) :
    (catR ^ n) (0, 1)
      = ((Nat.fib (2 * n) : ℝ), (Nat.fib (2 * n + 1) : ℝ) - (Nat.fib (2 * n) : ℝ)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, ih, catR_apply]
      have e1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      have e2 : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [e1, e2, Nat.fib_add_two (n := 2 * k + 1), Nat.fib_add_two (n := 2 * k)]
      refine Prod.ext ?_ ?_
      · simp only; push_cast; ring
      · simp only; push_cast; ring

/-- ★ **The powers of the cat matrix are Fibonacci matrices:**
`catR ^ n = [[F_{2n+1}, F_{2n}], [F_{2n}, F_{2n+1} − F_{2n}]]`. -/
theorem catR_pow_apply (n : ℕ) (v : ℝ × ℝ) :
    (catR ^ n) v
      = ((Nat.fib (2 * n + 1) : ℝ) * v.1 + (Nat.fib (2 * n) : ℝ) * v.2,
          (Nat.fib (2 * n) : ℝ) * v.1 + ((Nat.fib (2 * n + 1) : ℝ) - (Nat.fib (2 * n) : ℝ)) * v.2) := by
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, catR_pow_one_zero, catR_pow_zero_one]
  ext <;> simp <;> ring

/-! ### ★ The cat map's classical OTOC -/

/-- ★ **The classical OTOC of the cat map at step `n` is exactly `F_{2n+1}`.** -/
theorem classicalOtoc_catR (n : ℕ) : classicalOtoc catR n = Nat.fib (2 * n + 1) := by
  rw [classicalOtoc_eq, catR_pow_one_zero]

/-- Binet's form of the cat map's classical OTOC: `(φ^{2n+1} − ψ^{2n+1}) / √5`. -/
theorem classicalOtoc_catR_binet (n : ℕ) :
    classicalOtoc catR n = (φ ^ (2 * n + 1) - ψ ^ (2 * n + 1)) / √5 := by
  rw [classicalOtoc_catR, Real.coe_fib_eq]

/-- The sup norm of the first column `(F_{2n+1}, F_{2n})` is `F_{2n+1}`. -/
theorem norm_catR_pow_one_zero (n : ℕ) : ‖(catR ^ n) (1, 0)‖ = Nat.fib (2 * n + 1) := by
  rw [catR_pow_one_zero, Prod.norm_def, Real.norm_natCast, Real.norm_natCast]
  exact max_eq_left (Nat.cast_le.2 Nat.fib_le_fib_succ)

/-- ★★ **The cat map's classical OTOC grows at the exponential rate `2 log φ`, the Lyapunov
exponent**: `log F_{2n+1} / n → 2 log φ`. Read off `hasLyapunovExponent_catR` in the direction
`(1, 0)`, whose iterates have sup norm exactly `F_{2n+1}`. -/
theorem tendsto_log_classicalOtoc_catR :
    Tendsto (fun n : ℕ => Real.log (classicalOtoc catR n) / n) atTop (𝓝 (2 * Real.log φ)) := by
  have h : HasLyapunovExponent catR ((1 : ℝ), (0 : ℝ)) (2 * Real.log φ) :=
    hasLyapunovExponent_catR (by simp [ellUR])
  unfold HasLyapunovExponent at h
  refine h.congr fun n => ?_
  rw [norm_catR_pow_one_zero, classicalOtoc_catR]

/-- ★ **The squared bracket, the textbook `C(t)`, grows at `4 log φ` — twice the Lyapunov
exponent.** -/
theorem tendsto_log_classicalOtoc_sq_catR :
    Tendsto (fun n : ℕ => Real.log ((classicalOtoc catR n) ^ 2) / n) atTop
      (𝓝 (4 * Real.log φ)) := by
  have h := tendsto_log_classicalOtoc_catR.const_mul 2
  have h4 : (2 : ℝ) * (2 * Real.log φ) = 4 * Real.log φ := by ring
  rw [h4] at h
  refine h.congr fun n => ?_
  rw [Real.log_pow]
  push_cast
  ring

/-- The cat map's classical OTOC is positive at every step: `F_{2n+1} ≥ 1`. -/
theorem classicalOtoc_catR_pos (n : ℕ) : 0 < classicalOtoc catR n := by
  rw [classicalOtoc_catR]
  exact_mod_cast Nat.fib_pos.2 (Nat.succ_pos _)

/-! ### ★★★ The package -/

/-- ★★★ **The classical OTOC separates the cat map from its shear factors and from the
identity.** The cat map's bracket is exactly `F_{2n+1}` and grows at rate `2 log φ`; the identity's
and each shear's bracket is `1` at every step, and the vertical shear's transverse bracket is `n`.
Exponential scrambling is the work of composing the two transverse shears. -/
theorem cat_classicalOtoc :
    (∀ n : ℕ, classicalOtoc catR n = Nat.fib (2 * n + 1))
      ∧ Tendsto (fun n : ℕ => Real.log (classicalOtoc catR n) / n) atTop (𝓝 (2 * Real.log φ))
      ∧ (∀ n : ℕ, classicalOtoc (ContinuousLinearMap.id ℝ (ℝ × ℝ)) n = 1)
      ∧ (∀ n : ℕ, classicalOtoc shearXR n = 1)
      ∧ (∀ n : ℕ, classicalOtoc shearYR n = 1)
      ∧ (∀ n : ℕ, ∀ v : ℝ × ℝ, poissonBracket (fun v => ((shearYR ^ n) v).2) Prod.snd v = n) :=
  ⟨classicalOtoc_catR, tendsto_log_classicalOtoc_catR, classicalOtoc_id, classicalOtoc_shearXR,
    classicalOtoc_shearYR, poissonBracket_snd_shearYR⟩

end MeasureTheory

end

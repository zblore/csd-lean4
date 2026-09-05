/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Boost
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# P4: the dispersion earned — covariance selects `ω = √(p² + m²)`

**Category:** CV (continuous variables — relativistic structure forced, not
defined; `eft-pillars-plan.md` P4). ⚠️ **Scope (CR-8):** "relativistic structure" here is boost
covariance of a *posited* `(E, p)`-plane cone. The plane, the cone and the boost family are set up;
what is earned is that covariance selects `ω = √(p² + m²)` among dispersions on them. No Lorentz
group, no four-dimensional spacetime, no signature is derived. "Forced" is earned here in the strong sense
CONVENTIONS §8.3a asks for: the converse is a theorem of this module
(`cone_preserving_is_boost` and the selection chain below), not a motivation.
Contrast the record layer's cell law, where "forced" holds only *given* torus
generation (`specs/POSITS.md` Posit 1) — the two uses are not the same strength,
and the governance wording keeps them apart.

`CV/Dispersion.lean` *defines* `omega m p := √(p² + m²)`; `CV/Boost.lean`
proves the forward direction (`boost_omega`: the definition is covariant).
`specs/necessity-audit.md` records the gap: the **converse** — that covariance
*selects* this dispersion — was proved nowhere. This module is the converse,
in two independent selections chained into a characterisation, with the mass
gap shown sharp. Scoped first in `specs/dispersion-earned-plan.md`.

* ★ `cone_preserving_is_boost` — **the light cone selects the boost group**:
  any linear map of the `(E, p)` plane preserving the two light rays forward,
  with unit determinant, IS `boostE χ`/`boostP χ` at some rapidity. The
  `cosh/sinh` form is derived, not posited: the rays are eigendirections, the
  eigenvalues are reciprocal and positive, and `χ = −arsinh b` does the rest.
* ★ `boost_covariance_selects_omega` — **the boosts select the dispersion**:
  if `ω 0 = m > 0` and the graph of `ω` is boost-covariant (the exact law
  `boost_omega` establishes for `omega m`), then `ω = omega m`. The single
  orbit through the rest point `(m, 0)` covers every momentum, and
  single-valuedness pins `ω` on it — no continuity, evenness, or
  measurability assumed.
* `omega_cone_covariant` — non-vacuity from the corpus's own theorem:
  `omega m` satisfies the full cone-symmetry covariance (via
  `cone_preserving_is_boost` + the existing `boost_omega`).
* ★★ `cone_symmetry_characterises_omega` — **P4's characterisation**: for
  `m > 0`, `ω = omega m` **iff** `ω` has rest energy `m` and its graph is
  covariant under every ray-preserving unimodular linear symmetry. Relativity
  at the shell level, forced rather than written down.
* `massless_covariance_not_selecting` — **the mass gap is sharp**: at `m = 0`
  selection fails — `ω = id` (the right-moving light ray) is boost-covariant
  with rest energy `0` yet differs from `omega 0 = |p|`. So `0 < m` above is
  necessary, not a convenience.

⚠️ Honest scope: kinematic level, inherited from `CV/Boost.lean`. No boost
action on the finite mode lattice is claimed (a lattice is not
boost-invariant; standard cutoff honesty), and the identification of the
`(E, p)` light rays with the dynamical Lieb-Robinson cone is not claimed here —
the LR cone is an upper bound with a model-dependent velocity, not an exact
invariant set.

## References

`specs/eft-pillars-plan.md` (P4); `specs/dispersion-earned-plan.md` (scoping);
`specs/necessity-audit.md` (the recorded overstatement this closes);
`specs/future-work.md`; `CV/Dispersion.lean` (`omega`, `omega_massless`);
`CV/Boost.lean` (`boostE`, `boostP`, `boost_omega`).
-/

@[expose] public section

namespace CSD.CV

/-! ### The rest-orbit helper -/

/-- The rest-point orbit parametrisation: `m · cosh (arsinh (p/m)) = ω(m, p)`.
This is the algebraic heart of the selection — the boost orbit through the
rest point `(m, 0)` traces out exactly the mass shell. -/
lemma mul_cosh_arsinh_div {m : ℝ} (hm : 0 < m) (p : ℝ) :
    m * Real.cosh (Real.arsinh (p / m)) = omega m p := by
  have hsq : (m * Real.cosh (Real.arsinh (p / m))) ^ 2 = p ^ 2 + m ^ 2 := by
    rw [mul_pow, Real.cosh_arsinh,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + (p / m) ^ 2)]
    field_simp
    ring
  have hpos : 0 ≤ m * Real.cosh (Real.arsinh (p / m)) :=
    mul_nonneg hm.le (Real.cosh_pos _).le
  rw [omega, ← hsq, Real.sqrt_sq hpos]

/-! ### The boosts select the dispersion -/

/-- ★ **Boost covariance selects the dispersion.** If `ω` has rest energy
`m > 0` and its graph is boost-covariant — the exact law `boost_omega` proves
for `omega m` — then `ω` IS `omega m`. The single orbit through the rest point
`(m, 0)` covers every momentum (`χ = −arsinh (p/m)`), and single-valuedness of
the graph pins `ω` on it. No continuity, evenness, or measurability is
assumed. -/
theorem boost_covariance_selects_omega {ω : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (h0 : ω 0 = m)
    (hcov : ∀ χ p, boostE χ (ω p) p = ω (boostP χ (ω p) p)) :
    ω = omega m := by
  funext p
  have h := hcov (-Real.arsinh (p / m)) 0
  rw [h0, boostE, boostP] at h
  rw [Real.cosh_neg, Real.sinh_neg] at h
  have harg : (0 : ℝ) * Real.cosh (Real.arsinh (p / m))
      - m * -Real.sinh (Real.arsinh (p / m)) = p := by
    rw [Real.sinh_arsinh]
    field_simp
    ring
  rw [harg] at h
  rw [← h, ← mul_cosh_arsinh_div hm p]
  ring

/-! ### The cone selects the boosts -/

/-- ★ **The light cone selects the boost group.** A linear map
`(E, p) ↦ (aE + bp, cE + dp)` that preserves the right light ray forward
(`a + b = c + d > 0`), preserves the left light ray forward
(`a − b = d − c > 0`), and is unimodular (`ad − bc = 1`) is the boost at
rapidity `χ = −arsinh b`. The `cosh/sinh` form is derived: the rays are
eigendirections with reciprocal positive eigenvalues. -/
theorem cone_preserving_is_boost {a b c d : ℝ}
    (hR : a + b = c + d) (hRpos : 0 < a + b)
    (hL : a - b = d - c) (hLpos : 0 < a - b)
    (hdet : a * d - b * c = 1) :
    ∃ χ : ℝ, ∀ E p : ℝ,
      a * E + b * p = boostE χ E p ∧ c * E + d * p = boostP χ E p := by
  have hd : d = a := by linarith
  have hc : c = b := by linarith
  have ha : 0 < a := by linarith
  rw [hd, hc] at hdet
  refine ⟨-Real.arsinh b, fun E p => ?_⟩
  have hcosh : Real.cosh (-Real.arsinh b) = a := by
    rw [Real.cosh_neg, Real.cosh_arsinh,
      show (1 : ℝ) + b ^ 2 = a ^ 2 by nlinarith [hdet]]
    exact Real.sqrt_sq ha.le
  have hsinh : Real.sinh (-Real.arsinh b) = -b := by
    rw [Real.sinh_neg, Real.sinh_arsinh]
  constructor
  · rw [boostE, hcosh, hsinh]
    ring
  · rw [boostP, hcosh, hsinh, hd, hc]
    ring

/-! ### Non-vacuity: the corpus's dispersion satisfies the full covariance -/

/-- `omega m` is covariant under EVERY ray-preserving unimodular linear
symmetry — non-vacuity of the characterisation below, assembled from
`cone_preserving_is_boost` and the corpus's own `boost_omega`. -/
theorem omega_cone_covariant (m : ℝ) {a b c d : ℝ}
    (hR : a + b = c + d) (hRpos : 0 < a + b)
    (hL : a - b = d - c) (hLpos : 0 < a - b)
    (hdet : a * d - b * c = 1) (p : ℝ) :
    a * omega m p + b * p = omega m (c * omega m p + d * p) := by
  obtain ⟨χ, hχ⟩ := cone_preserving_is_boost hR hRpos hL hLpos hdet
  obtain ⟨hE, hP⟩ := hχ (omega m p) p
  rw [hE, hP]
  exact boost_omega m p χ

/-! ### The characterisation -/

/-- ★★ **P4's characterisation: relativity at the shell level, forced.** For
`m > 0`: `ω = omega m` **iff** `ω` has rest energy `m` and its graph is
covariant under every linear symmetry of the `(E, p)` plane that preserves the
two light rays forward and is unimodular. The forward direction chains the two
selections (cone → boosts → dispersion); the backward direction is
`omega_cone_covariant`, i.e. the corpus's own `boost_omega`. -/
theorem cone_symmetry_characterises_omega {ω : ℝ → ℝ} {m : ℝ} (hm : 0 < m) :
    (ω 0 = m ∧ ∀ a b c d : ℝ, a + b = c + d → 0 < a + b → a - b = d - c →
        0 < a - b → a * d - b * c = 1 →
        ∀ p, a * ω p + b * p = ω (c * ω p + d * p))
      ↔ ω = omega m := by
  constructor
  · rintro ⟨h0, hcov⟩
    refine boost_covariance_selects_omega hm h0 (fun χ p => ?_)
    have hRpos : 0 < Real.cosh χ + -Real.sinh χ := by
      rw [show Real.cosh χ + -Real.sinh χ = Real.cosh χ - Real.sinh χ by ring,
        Real.cosh_sub_sinh]
      exact Real.exp_pos _
    have hLpos : 0 < Real.cosh χ - -Real.sinh χ := by
      rw [show Real.cosh χ - -Real.sinh χ = Real.cosh χ + Real.sinh χ by ring,
        Real.cosh_add_sinh]
      exact Real.exp_pos _
    have hdet : Real.cosh χ * Real.cosh χ - -Real.sinh χ * -Real.sinh χ = 1 := by
      have := Real.cosh_sq_sub_sinh_sq χ
      nlinarith
    have h := hcov (Real.cosh χ) (-Real.sinh χ) (-Real.sinh χ) (Real.cosh χ)
      (by ring) hRpos (by ring) hLpos hdet p
    rw [boostE, boostP,
      show p * Real.cosh χ - ω p * Real.sinh χ
        = -Real.sinh χ * ω p + Real.cosh χ * p by ring, ← h]
    ring
  · rintro rfl
    refine ⟨?_, fun a b c d hR hRpos hL hLpos hdet p =>
      omega_cone_covariant m hR hRpos hL hLpos hdet p⟩
    rw [omega_zero, abs_of_pos hm]

/-! ### Sharpness: the mass gap is necessary -/

/-- **The mass gap is sharp.** At `m = 0` the selection fails: `ω = id` — the
right-moving light ray as a graph — is boost-covariant with rest energy `0`,
yet is not `omega 0 = |p|`. So `0 < m` in the selection theorems is necessary,
not a convenience: the massless shell degenerates onto the cone, where
covariant graphs are unions of half-rays and no longer unique. -/
theorem massless_covariance_not_selecting :
    ∃ ω : ℝ → ℝ, ω 0 = 0
      ∧ (∀ χ p, boostE χ (ω p) p = ω (boostP χ (ω p) p))
      ∧ ω ≠ omega 0 := by
  refine ⟨id, rfl, fun χ p => rfl, fun h => ?_⟩
  have h1 := congrFun h (-1)
  rw [id_eq, omega_massless, abs_neg, abs_one] at h1
  linarith

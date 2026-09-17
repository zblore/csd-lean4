/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Complex.Basic

/-!
# The pointwise Fubini–Study / Kähler fundamental form (linear-algebra core)

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler"; the source
repository's terms register records what is backed and what is not.

**Category:** 1-Mathlib (CSD-free; the form-level analogue of `fsMeasure`).

Mathlib has no Kähler-geometry API (no manifold differential forms, no exterior derivative, no
almost-complex structure; MATHLIB-ABSENT(file:Mathlib/Geometry/Manifold/DifferentialForm)). When
this
module was written that meant the full closed 2-form `ω` on `ℂℙ^{N-1}` with `dω = 0` and
`ω^{∧(N-1)}/(N-1)! = μ_FS` could not be built; since 2026-09-07/11 the modules under
`Geometry/Manifold/` build that differential geometry themselves and both statements are
theorems (`Projectivization.fsForm_isKahler`, `fsVolume_eq_smul_fsMeasure`). What **is**
bounded — and is built here — is the
**pointwise** (linear-algebra) core of that form: on any complex inner-product space `E` (the
tangent
model of `ℂℙ^{N-1}` at a ray is `ψ^⊥ ⊆ E`), the flat Hermitian structure gives the Kähler triple

* the **complex structure** `J u = i • u` (with `J² = -1`);
* the **Riemannian metric** `g u v = re ⟪u, v⟫` (the real part of the Hermitian inner product);
* the **fundamental 2-form** `ω u v = im ⟪u, v⟫` (its imaginary part).

We prove the defining **almost-Kähler / Hermitian compatibility** relations, pointwise and
axiom-free:

* `J² = -1` (`complexStructure_involutive`);
* `ω` is an alternating `ℝ`-bilinear form (`fundamentalForm_self`, `fundamentalForm_antisymm`,
  `fundamentalForm_add_left`, `fundamentalForm_real_smul_left`);
* **J-compatibility** `ω u v = g (J u) v` (`fundamentalForm_eq_metric_complexStructure`) and the
  dual
  `g u v = ω u (J v)` (`metric_eq_fundamentalForm_complexStructure`) — the Kähler triple `g, ω, J`;
* `J` is a `g`-isometry and `ω` is `J`-invariant, i.e. `ω` is a **(1,1)-form**
  (`metric_complexStructure`, `fundamentalForm_complexStructure`, from `inner_complexStructure`);
* **positivity / taming** `ω u (J u) = ‖u‖²` (`fundamentalForm_complexStructure_self`), strictly
  positive off `0` (`fundamentalForm_complexStructure_self_pos`) — so `(u,v) ↦ ω u (J v) = g u v` is
  positive-definite.

The five statements are exported one by one; the bundle a consumer wants is built where it is
wanted (until 2026-09-16 three conjunction capstones lived here — Mathlib takes the conjuncts).

## Scope

This is the **pointwise (algebraic) core** of the Kähler form on the flat Hermitian model `E`: the
"compatible with the complex structure, positive" half of "Kähler", as theorems. The other half is
proved downstream, on the manifold:

* **closedness** `dω = 0` — flat, as a constant 2-form on `E`: `KahlerClosed.lean`
  (`extDeriv_fundamentalFormAlt_eq_zero`); on `ℂℙⁿ`: `Projectivization.fsForm_mextDeriv`
  (`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean`);
* the **global** identity between the top power of `ω` and the Fubini–Study measure:
  `Projectivization.fsVolume_eq_smul_fsMeasure`
  (`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyMass.lean`).

The `X_H = ω⁻¹dH` duality this triple supports is a theorem at the linear level in
`HamiltonianVectorField.lean` (same directory), together with the uniqueness non-degeneracy gives
(`eq_hamiltonianVectorFieldOf_of_forall`). The restriction of the triple to the tangent space
`ψ^⊥` of a ray is the Fubini–Study form pointwise (`complexStructure_mem_orthogonal`).
-/

@[expose] public section

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The complex structure `J`**: multiplication by `i`. Squares to `-1`
(`complexStructure_involutive`). -/
def complexStructure (u : E) : E := Complex.I • u

/-- **The Riemannian metric `g`**: the real part of the Hermitian inner product,
`g u v = re ⟪u, v⟫`.
This is the real inner product Mathlib's `InnerProductSpace.complexToReal` would install on `E`,
definitionally (`metric_eq_real_inner`); that structure is a `def`, not an instance (installing
`Inner ℝ E` on every complex space would create diamonds), so `re ⟪u, v⟫_ℂ` is Mathlib's own
spelling of the real inner product here and the name `g` is what the Kähler triple `g, ω, J` needs.
Symmetric (`metric_comm`) and positive-definite (`metric_self`, `= ‖u‖²`). -/
def metric (u v : E) : ℝ := (inner ℂ u v).re

/-- `metric`, unfolded: the definitional equation. -/
theorem metric_def (u v : E) : metric u v = (inner ℂ u v).re := rfl

/-- `g` is the real inner product of `InnerProductSpace.complexToReal`, `⟪u, v⟫_ℝ = re ⟪u, v⟫_ℂ`,
definitionally (the structure is installed locally; Mathlib provides it as a `def`). -/
theorem metric_eq_real_inner (u v : E) :
    letI := InnerProductSpace.complexToReal (G := E); metric u v = inner ℝ u v := rfl

/-- **The fundamental 2-form `ω`**: the imaginary part of the Hermitian inner product,
`ω u v = im ⟪u, v⟫`. Alternating `ℝ`-bilinear (the pointwise Kähler form). -/
def fundamentalForm (u v : E) : ℝ := (inner ℂ u v).im

/-- `fundamentalForm`, unfolded: the definitional equation. -/
theorem fundamentalForm_def (u v : E) : fundamentalForm u v = (inner ℂ u v).im := rfl

/-- `J u = i • u`, unfolded. **Not `@[simp]`**: as a head unfolder it rewrites `J` away before the
structural lemmas (`complexStructure_involutive`, `fundamentalForm_complexStructure_self`) can fire,
leaving them dead (`simpNF`). -/
theorem complexStructure_apply (u : E) : complexStructure u = Complex.I • u := rfl

/-- **`J² = -1`**: the fundamental relation of a complex structure. `J (J u) = i • (i • u) = -u`. -/
@[simp] theorem complexStructure_involutive (u : E) :
    complexStructure (complexStructure u) = -u := by
  simp only [complexStructure, smul_smul, Complex.I_mul_I, neg_smul, one_smul]

/-! ### `ω` is an alternating `ℝ`-bilinear form -/

/-- `ω u u = 0`: the fundamental form is alternating (`⟪u,u⟫` is real). -/
@[simp] theorem fundamentalForm_self (u : E) : fundamentalForm u u = 0 := by
  simp only [fundamentalForm, ← RCLike.im_to_complex, inner_self_im]

/-- `ω u v = -ω v u`: antisymmetry, from `⟪v,u⟫ = conj ⟪u,v⟫`. -/
theorem fundamentalForm_antisymm (u v : E) :
    fundamentalForm u v = - fundamentalForm v u := by
  simp only [fundamentalForm, ← RCLike.im_to_complex]
  exact inner_im_symm u v

/-- `ω` is additive in the left argument. -/
theorem fundamentalForm_add_left (u u' v : E) :
    fundamentalForm (u + u') v = fundamentalForm u v + fundamentalForm u' v := by
  simp only [fundamentalForm, inner_add_left, Complex.add_im]

/-- `ω` is `ℝ`-homogeneous in the left argument (`r : ℝ` acting through `ℂ`). With additivity and
antisymmetry this makes `ω` an alternating `ℝ`-bilinear form. -/
theorem fundamentalForm_real_smul_left (r : ℝ) (u v : E) :
    fundamentalForm ((r : ℂ) • u) v = r * fundamentalForm u v := by
  simp only [fundamentalForm, inner_smul_left, Complex.conj_ofReal, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-! ### The Kähler triple: `g`, `ω`, `J` compatibility -/

/-- **J-compatibility `ω u v = g (J u) v`.** The fundamental form is the metric precomposed with the
complex structure: `im ⟪u, v⟫ = re ⟪i • u, v⟫`. This is the defining relation tying `ω`, `g`, `J`.
-/
theorem fundamentalForm_eq_metric_complexStructure (u v : E) :
    fundamentalForm u v = metric (complexStructure u) v := by
  simp only [fundamentalForm, metric, complexStructure, inner_smul_left, Complex.conj_I,
    neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]

/-- **The metric is recovered from `ω` and `J`: `g u v = ω u (J v)`.** `re ⟪u, v⟫ = im ⟪u, i • v⟫`.
The dual Kähler-triple relation. -/
theorem metric_eq_fundamentalForm_complexStructure (u v : E) :
    metric u v = fundamentalForm u (complexStructure v) := by
  simp only [metric, fundamentalForm, complexStructure, inner_smul_right, Complex.I_mul_im]

/-! ### `J` is an isometry — `ω` is a `(1,1)`-form -/

/-- `J` preserves the Hermitian inner product: `⟪J u, J v⟫ = ⟪u, v⟫` (since `conj i · i = 1`). -/
theorem inner_complexStructure (u v : E) :
    inner ℂ (complexStructure u) (complexStructure v) = inner ℂ u v := by
  show inner ℂ (Complex.I • u) (Complex.I • v) = inner ℂ u v
  rw [inner_smul_left, inner_smul_right, Complex.conj_I, ← mul_assoc, neg_mul,
    Complex.I_mul_I, neg_neg, one_mul]

/-- `J` is a `g`-isometry: `g (J u) (J v) = g u v`. -/
theorem metric_complexStructure (u v : E) :
    metric (complexStructure u) (complexStructure v) = metric u v := by
  simp only [metric, inner_complexStructure]

/-- `ω` is `J`-invariant: `ω (J u) (J v) = ω u v`, i.e. `ω` is a `(1,1)`-form. -/
theorem fundamentalForm_complexStructure (u v : E) :
    fundamentalForm (complexStructure u) (complexStructure v) = fundamentalForm u v := by
  simp only [fundamentalForm, inner_complexStructure]

/-! ### Positivity / taming, and the metric's positive-definiteness -/

/-- `g u u = ‖u‖²`: the metric is positive-definite. -/
@[simp] theorem metric_self (u : E) : metric u u = ‖u‖ ^ 2 := by
  simp only [metric, ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq u

/-- `g` is symmetric. -/
theorem metric_comm (u v : E) : metric u v = metric v u := by
  simp only [metric, ← RCLike.re_to_complex]
  exact inner_re_symm u v

/-- **Positivity / taming `ω u (J u) = ‖u‖²`.** The fundamental form paired with the complex
structure
recovers the squared norm — so `(u, v) ↦ ω u (J v) = g u v` is positive-definite, the taming
condition
that makes `ω` a *positive* `(1,1)`-form (the compatible almost-Kähler structure). -/
@[simp] theorem fundamentalForm_complexStructure_self (u : E) :
    fundamentalForm u (complexStructure u) = ‖u‖ ^ 2 := by
  simp only [fundamentalForm, complexStructure, inner_smul_right, Complex.I_mul_im,
    ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq u

/-- `ω u (J u) > 0` for `u ≠ 0`: strict positivity of the taming form. -/
theorem fundamentalForm_complexStructure_self_pos {u : E} (hu : u ≠ 0) :
    0 < fundamentalForm u (complexStructure u) := by
  rw [fundamentalForm_complexStructure_self]
  exact pow_pos (norm_pos_iff.mpr hu) 2

/-! ### The projective tangent space `ψ^⊥` is `J`-invariant

At a ray `[ψ] ∈ ℂℙ^{N-1}` the (holomorphic) tangent space is modelled by the orthogonal complement
`(span ℂ {ψ})ᗮ = ψ^⊥`. The complex structure `J = i • ·` preserves it, so `ψ^⊥` is a complex
(`J`-invariant) subspace (`complexStructure_mem_orthogonal`, proved immediately below) — and since
the Kähler-triple identities above are universally quantified over `E`
(`fundamentalForm_eq_metric_complexStructure`, `fundamentalForm_complexStructure`), they
restrict to `ψ^⊥` with nothing to prove: the flat Hermitian structure on `E` **induces** the
Fubini–Study Kähler structure on
each tangent space. This ties the ambient pointwise form to the actual tangent model of `ℂℙ^{N-1}`
(still pointwise — no manifold structure needed). -/

/-- **`J` preserves the tangent space `ψ^⊥`.** If `v ⊥ ψ` then `J v = i • v ⊥ ψ` (since
`⟪ψ, i • v⟫ = i · ⟪ψ, v⟫ = 0`). -/
theorem complexStructure_mem_orthogonal {ψ v : E}
    (hv : v ∈ (Submodule.span ℂ {ψ})ᗮ) :
    complexStructure v ∈ (Submodule.span ℂ {ψ})ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  simp only [complexStructure, inner_smul_right, hv u hu, mul_zero]

/-! ### The Kähler structure is preserved by unitary symmetries

Any `ℂ`-linear isometry preserves the Hermitian inner product, hence both the metric `g` and the
fundamental form `ω`. So it is a **symplectic isometry** — a "Kähler transformation" of the
structure.
In particular the Schrödinger flow `exp(-itH)` (a one-parameter group of unitaries) preserves `g`
and
`ω`: QM evolution is a symplectomorphism of the Fubini–Study Kähler geometry (the Kibble /
Ashtekar–Schilling picture, at the pointwise/linear level). The flow corollary is drawn in the
source repository's Schrödinger–Kähler invariance module. -/

/-- A `ℂ`-linear isometry preserves the metric `g`. -/
theorem metric_linearIsometryEquiv (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    metric (f u) (f v) = metric u v := by
  simp only [metric, f.inner_map_map]

/-- A `ℂ`-linear isometry preserves the fundamental form `ω`. -/
theorem fundamentalForm_linearIsometryEquiv (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    fundamentalForm (f u) (f v) = fundamentalForm u v := by
  simp only [fundamentalForm, f.inner_map_map]

end Kahler



import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Complex.Basic

/-!
# The pointwise Fubini–Study / Kähler fundamental form (linear-algebra core)

**Category:** 1-Mathlib (CSD-free; the form-level analogue of `fubiniStudyMeasure`).

Mathlib has no Kähler-geometry API (no manifold differential forms, no exterior derivative, no
almost-complex structure — see `KahlerVolumeForced.lean` for the audit). So the full closed 2-form
`ω` on `ℂℙ^{N-1}` with `dω = 0` and `ω^{∧(N-1)}/(N-1)! = μ_FS` cannot be built without first
developing differential geometry in Lean. What **is** bounded — and is built here — is the
**pointwise** (linear-algebra) core of that form: on any complex inner-product space `E` (the tangent
model of `ℂℙ^{N-1}` at a ray is `ψ^⊥ ⊆ E`), the flat Hermitian structure gives the Kähler triple

* the **complex structure** `J u = i • u` (with `J² = -1`);
* the **Riemannian metric** `g u v = re ⟪u, v⟫` (the real part of the Hermitian inner product);
* the **fundamental 2-form** `ω u v = im ⟪u, v⟫` (its imaginary part).

We prove the defining **almost-Kähler / Hermitian compatibility** relations, pointwise and axiom-free:

* `J² = -1` (`complexStructure_involutive`);
* `ω` is an alternating `ℝ`-bilinear form (`fundamentalForm_self`, `fundamentalForm_antisymm`,
  `fundamentalForm_add_left`, `fundamentalForm_real_smul_left`);
* **J-compatibility** `ω u v = g (J u) v` (`fundamentalForm_eq_metric_complexStructure`) and the dual
  `g u v = ω u (J v)` (`metric_eq_fundamentalForm_complexStructure`) — the Kähler triple `g, ω, J`;
* `J` is a `g`-isometry and `ω` is `J`-invariant, i.e. `ω` is a **(1,1)-form**
  (`metric_complexStructure`, `fundamentalForm_complexStructure`, from `inner_complexStructure`);
* **positivity / taming** `ω u (J u) = ‖u‖²` (`fundamentalForm_complexStructure_self`), strictly
  positive off `0` (`fundamentalForm_complexStructure_self_pos`) — so `(u,v) ↦ ω u (J v) = g u v` is
  positive-definite.

The capstone `fubiniStudy_pointwise_kahler_compatibility` bundles the Kähler triple.

## Honest scope — what this is and is NOT

This is the **pointwise (algebraic) core** of the Kähler form, the exact analogue at the form level of
what `fubiniStudyMeasure` is at the measure level: it delivers the "compatible with the complex
structure, positive" half of "Kähler" as genuine theorems. It does **NOT** deliver:

* **closedness** `dω = 0` — the defining *Kähler* (vs merely almost-Hermitian) condition, which needs
  the exterior derivative on a manifold (absent from Mathlib);
* the **global** identity `ω^{∧(N-1)}/(N-1)! = μ_FS` — which needs differential forms on the
  projective *manifold* and the form→measure integration (absent from Mathlib).

Those remain the Mathlib-blocked residue (KG-1 / the `IsKahlerSector` posit). This module works on the
flat Hermitian model `E`; its restriction to the tangent space `ψ^⊥` is the Fubini–Study form
pointwise. The physically load-bearing datum — the volume — is already forced independently
(`KahlerVolumeForced.lean`).
-/

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The complex structure `J`**: multiplication by `i`. Squares to `-1`
(`complexStructure_involutive`). -/
def complexStructure (u : E) : E := Complex.I • u

/-- **The Riemannian metric `g`**: the real part of the Hermitian inner product, `g u v = re ⟪u, v⟫`.
Symmetric (`metric_comm`) and positive-definite (`metric_self`, `= ‖u‖²`). -/
def metric (u v : E) : ℝ := (inner ℂ u v).re

/-- **The fundamental 2-form `ω`**: the imaginary part of the Hermitian inner product,
`ω u v = im ⟪u, v⟫`. Alternating `ℝ`-bilinear (the pointwise Kähler form). -/
def fundamentalForm (u v : E) : ℝ := (inner ℂ u v).im

@[simp] theorem complexStructure_apply (u : E) : complexStructure u = Complex.I • u := rfl

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
complex structure: `im ⟪u, v⟫ = re ⟪i • u, v⟫`. This is the defining relation tying `ω`, `g`, `J`. -/
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

/-- **Positivity / taming `ω u (J u) = ‖u‖²`.** The fundamental form paired with the complex structure
recovers the squared norm — so `(u, v) ↦ ω u (J v) = g u v` is positive-definite, the taming condition
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

/-! ### The capstone -/

/-- **The pointwise Kähler compatibility of the Fubini–Study fundamental form.** On any complex
inner-product space `E` (the tangent model of `ℂℙ^{N-1}`), the triple `g = re ⟪·,·⟫`,
`ω = im ⟪·,·⟫`, `J = i • ·` satisfies the defining almost-Kähler relations:

* `J² = -1` (complex structure);
* `ω u v = g (J u) v` (the fundamental form is the metric twisted by `J`);
* `g u v = ω u (J v)` (the metric is recovered from `ω` and `J`);
* `ω (J u) (J v) = ω u v` (`ω` is a `(1,1)`-form);
* `ω u (J u) = ‖u‖²` (positivity / taming).

This is the linear-algebra core of the Kähler form — the "compatible with the complex structure and
positive" content, proved pointwise and axiom-free. Closedness `dω = 0` and the global identity
`ω^{∧(N-1)}/(N-1)! = μ_FS` need manifold exterior calculus (absent from Mathlib) and stay blocked. -/
theorem fubiniStudy_pointwise_kahler_compatibility (u v : E) :
    complexStructure (complexStructure u) = -u
    ∧ fundamentalForm u v = metric (complexStructure u) v
    ∧ metric u v = fundamentalForm u (complexStructure v)
    ∧ fundamentalForm (complexStructure u) (complexStructure v) = fundamentalForm u v
    ∧ fundamentalForm u (complexStructure u) = ‖u‖ ^ 2 :=
  ⟨complexStructure_involutive u, fundamentalForm_eq_metric_complexStructure u v,
    metric_eq_fundamentalForm_complexStructure u v,
    fundamentalForm_complexStructure u v, fundamentalForm_complexStructure_self u⟩

/-! ### The projective tangent space `ψ^⊥` is `J`-invariant

At a ray `[ψ] ∈ ℂℙ^{N-1}` the (holomorphic) tangent space is modelled by the orthogonal complement
`(span ℂ {ψ})ᗮ = ψ^⊥`. The complex structure `J = i • ·` preserves it, so `ψ^⊥` is a complex
(`J`-invariant) subspace — and since the Kähler-triple identities above hold on all of `E`, they
restrict to `ψ^⊥`: the flat Hermitian structure on `E` **induces** the Fubini–Study Kähler structure on
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

/-- **The tangent space at a ray is a complex (`J`-invariant) subspace.** `J` maps `ψ^⊥` into itself,
so the pointwise Kähler triple (`fubiniStudy_pointwise_kahler_compatibility`) restricts to the tangent
space of `ℂℙ^{N-1}` at `[ψ]` — the induced Fubini–Study Kähler structure on the tangent. -/
theorem tangent_complexStructure_invariant (ψ : E) :
    ∀ v ∈ (Submodule.span ℂ {ψ})ᗮ, complexStructure v ∈ (Submodule.span ℂ {ψ})ᗮ :=
  fun _ hv => complexStructure_mem_orthogonal hv

/-! ### The Kähler structure is preserved by unitary symmetries

Any `ℂ`-linear isometry preserves the Hermitian inner product, hence both the metric `g` and the
fundamental form `ω`. So it is a **symplectic isometry** — a "Kähler transformation" of the structure.
In particular the Schrödinger flow `exp(-itH)` (a one-parameter group of unitaries) preserves `g` and
`ω`: QM evolution is a symplectomorphism of the Fubini–Study Kähler geometry (the Kibble /
Ashtekar–Schilling picture, at the pointwise/linear level). See `LF4/SchrodingerKahlerInvariance.lean`
for the flow corollary. -/

/-- A `ℂ`-linear isometry preserves the metric `g`. -/
theorem metric_linearIsometryEquiv (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    metric (f u) (f v) = metric u v := by
  simp only [metric, f.inner_map_map]

/-- A `ℂ`-linear isometry preserves the fundamental form `ω`. -/
theorem fundamentalForm_linearIsometryEquiv (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    fundamentalForm (f u) (f v) = fundamentalForm u v := by
  simp only [fundamentalForm, f.inner_map_map]

/-- **The Kähler structure is preserved by any unitary symmetry.** A `ℂ`-linear isometry preserves
both the metric `g` and the fundamental form `ω`, so it is a symplectic isometry (a Kähler
transformation) of the Hermitian structure. This is the invariance that makes the Schrödinger flow a
symplectomorphism of the Fubini–Study geometry. -/
theorem kahler_structure_isometry_invariant (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    metric (f u) (f v) = metric u v ∧ fundamentalForm (f u) (f v) = fundamentalForm u v :=
  ⟨metric_linearIsometryEquiv f u v, fundamentalForm_linearIsometryEquiv f u v⟩

end Kahler



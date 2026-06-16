import CsdLean4.Mathlib.QuantumInfo.TraceDistance
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Spectral von Neumann entropy (K1-A)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **von Neumann entropy** of a density operator, defined spectrally as

  `S(ρ) = ∑ᵢ negMulLog (λᵢ) = − ∑ᵢ λᵢ log λᵢ`,

where `λᵢ` are the (real) eigenvalues of the Hermitian `ρ` and
`Real.negMulLog x = −x log x`. This is the K1-A tranche of `specs/k1-plan.md`; it reuses the
spectral machinery already staged in `TraceDistance.lean`
(`Matrix.IsHermitian.cfc`, `re_trace_cfc`, the `IsHermitian.cfc` algebra layer).

Delivered:

* `vonNeumannEntropy hρ := ∑ i, Real.negMulLog (hρ.eigenvalues i)`;
* the **operator-form headline** `S(ρ) = Re Tr(cfc negMulLog ρ) = − Re Tr(ρ log ρ)`
  (`vonNeumannEntropy_eq_re_trace_cfc`, `vonNeumannEntropy_eq_neg_re_trace_mul_log`),
  identifying the spectral sum with `−Tr(ρ log ρ)` via `re_trace_cfc`;
* **non-negativity** `0 ≤ S(ρ)` for a density operator (`vonNeumannEntropy_nonneg`),
  from `λᵢ ∈ [0,1]` (PSD ⟹ `λᵢ ≥ 0`; `∑ λᵢ = trace = 1` ⟹ `λᵢ ≤ 1`) and
  `Real.negMulLog_nonneg`;
* **pure-state vanishing** `S(ρ) = 0` for a rank-1 projection (`ρ * ρ = ρ`, `trace ρ = 1`)
  (`vonNeumannEntropy_eq_zero_of_pure`), since the spectrum is `{0,1}` and `negMulLog`
  vanishes there;
* **unitary invariance** `S(U ρ Uᴴ) = S(ρ)` (`vonNeumannEntropy_conj_unitary`), via charpoly
  conjugation-invariance + `eigenvalues_eq_eigenvalues_iff`;
* **additivity on tensor products** `S(ρ ⊗ σ) = S(ρ) + S(σ)` under an explicit
  eigenvalue-product hypothesis (`vonNeumannEntropy_kronecker_of_eigenvalues`); see the
  honesty note below.

## Honesty note on additivity

Mathlib has **no** lemma identifying the eigenvalues of a Kronecker product `ρ ⊗ₖ σ` with the
products `λᵢ μⱼ` of the factor eigenvalues (no Kronecker spectral theorem). Deriving it from
scratch is a multi-hour development (it is its own clean upstream contribution). So additivity is
stated under the explicit hypothesis that the `ρ ⊗ₖ σ` eigenvalues are reindexed products; the
`negMulLog`-product algebra and the `∑ λ = ∑ μ = 1` collapse are then proved. The hypothesis is
non-vacuous — it holds for the genuine Kronecker spectrum — and discharging it is the deferred
K1-A.2 item. See `specs/k1-plan.md`.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **von Neumann entropy** `S(ρ) = ∑ᵢ negMulLog(λᵢ) = −∑ᵢ λᵢ log λᵢ` of a Hermitian
operator, defined spectrally from its real eigenvalues. -/
noncomputable def vonNeumannEntropy {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : ℝ :=
  ∑ i, Real.negMulLog (hρ.eigenvalues i)

/-! ## Operator-form identity: `S(ρ) = −Tr(ρ log ρ)` -/

/-- **Operator-form headline (the `negMulLog`-trace identity):**
`S(ρ) = Re Tr(cfc negMulLog ρ)`, directly from `re_trace_cfc` at `f = Real.negMulLog`. -/
theorem vonNeumannEntropy_eq_re_trace_cfc {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = RCLike.re (hρ.cfc Real.negMulLog).trace := by
  rw [vonNeumannEntropy, ← hρ.cfc_eq Real.negMulLog, re_trace_cfc hρ Real.negMulLog]

/-- **The `−Tr(ρ log ρ)` form:** `S(ρ) = − Re Tr(cfc (x ↦ x log x) ρ)`. Here
`cfc (x ↦ x log x) ρ` is the operator `ρ log ρ` (`log ρ` being `cfc log ρ`), so this is the
standard `S(ρ) = −Tr(ρ log ρ)`. -/
theorem vonNeumannEntropy_eq_neg_re_trace_mul_log {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = - RCLike.re (hρ.cfc (fun x => x * Real.log x)).trace := by
  rw [vonNeumannEntropy, ← hρ.cfc_eq (fun x => x * Real.log x),
    re_trace_cfc hρ (fun x => x * Real.log x), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.negMulLog]; ring

/-- The cfc operator `ρ log ρ` equals the multiplicative cfc `cfc (x ↦ x log x) ρ`. The product
`ρ · log ρ` of the spectral identity `ρ = hρ.cfc id` and `log ρ = hρ.cfc log` is, by
`cfc_mul`, the cfc of the pointwise product. So `hρ.cfc (x ↦ x log x)` is genuinely `ρ log ρ`
and the headline above reads `S(ρ) = −Re Tr(ρ log ρ)`. -/
theorem cfc_id_mul_log {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    ρ * hρ.cfc Real.log = hρ.cfc (fun x => x * Real.log x) := by
  nth_rewrite 1 [show ρ = hρ.cfc id from (cfc_id hρ).symm]
  rw [cfc_mul]
  rfl

/-! ## Non-negativity -/

/-- Helper: a density operator's eigenvalues lie in `[0,1]`. PSD gives `λᵢ ≥ 0`; unit trace
gives `∑ λᵢ = 1`, hence each `λᵢ ≤ 1` (a single term bounded by a sum of non-negatives). -/
theorem eigenvalues_mem_Icc_of_density {ρ : Matrix n n ℂ} (hpsd : ρ.PosSemidef)
    (htr : ρ.trace = 1) (i : n) :
    0 ≤ hpsd.1.eigenvalues i ∧ hpsd.1.eigenvalues i ≤ 1 := by
  refine ⟨hpsd.eigenvalues_nonneg i, ?_⟩
  have hsum : ∑ j, hpsd.1.eigenvalues j = 1 := by
    have h := hpsd.1.trace_eq_sum_eigenvalues
    rw [htr] at h
    have hre := congrArg Complex.re h
    rw [Complex.one_re, Complex.re_sum] at hre
    simpa using hre.symm
  have hle := Finset.single_le_sum (f := hpsd.1.eigenvalues)
    (fun j _ => hpsd.eigenvalues_nonneg j) (Finset.mem_univ i)
  rwa [hsum] at hle

/-- **`S(ρ) ≥ 0`** for a density operator (PSD, unit trace). Each eigenvalue lies in `[0,1]`,
where `Real.negMulLog` is non-negative. -/
theorem vonNeumannEntropy_nonneg {ρ : Matrix n n ℂ} (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    0 ≤ vonNeumannEntropy hpsd.1 := by
  refine Finset.sum_nonneg fun i _ => ?_
  obtain ⟨h0, h1⟩ := eigenvalues_mem_Icc_of_density hpsd htr i
  exact Real.negMulLog_nonneg h0 h1

/-! ## cfc injectivity on the spectrum -/

/-- **`IsHermitian.cfc` injectivity on eigenvalues:** if `hρ.cfc f = hρ.cfc g` then `f` and `g`
agree on every eigenvalue. Conjugating `U · diag(↑∘f∘λ) · Uᴴ = U · diag(↑∘g∘λ) · Uᴴ` by `Uᴴ … U`
collapses (via `UᴴU = 1`) to the diagonals, whose entries are `f(λᵢ)` and `g(λᵢ)`. -/
theorem cfc_eq_iff_on_eigenvalues {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) {f g : ℝ → ℝ}
    (h : hρ.cfc f = hρ.cfc g) (i : n) :
    f (hρ.eigenvalues i) = g (hρ.eigenvalues i) := by
  unfold Matrix.IsHermitian.cfc at h
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply] at h
  have hUU : star (hρ.eigenvectorUnitary : Matrix n n ℂ) * (hρ.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self hρ.eigenvectorUnitary
  have collapse : ∀ (D : Matrix n n ℂ),
      star (hρ.eigenvectorUnitary : Matrix n n ℂ)
        * ((hρ.eigenvectorUnitary : Matrix n n ℂ) * D
          * star (hρ.eigenvectorUnitary : Matrix n n ℂ)) * (hρ.eigenvectorUnitary : Matrix n n ℂ)
      = D := by
    intro D
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.mul_assoc, hUU,
      Matrix.mul_one]
  have key : (diagonal (RCLike.ofReal ∘ f ∘ hρ.eigenvalues) : Matrix n n ℂ)
      = diagonal (RCLike.ofReal ∘ g ∘ hρ.eigenvalues) := by
    have h2 := congrArg (fun M => star (hρ.eigenvectorUnitary : Matrix n n ℂ) * M
      * (hρ.eigenvectorUnitary : Matrix n n ℂ)) h
    simp only at h2
    rw [collapse, collapse] at h2
    exact h2
  have hd := congrFun (congrFun key i) i
  simp only [diagonal_apply_eq, Function.comp_apply] at hd
  exact RCLike.ofReal_injective hd

/-! ## Pure-state vanishing -/

/-- **`S(ρ) = 0` for a projection** (`ρ` Hermitian, idempotent `ρ·ρ = ρ`). The idempotency
forces `λᵢ² = λᵢ`, so the spectrum is `{0,1}`, where `negMulLog` vanishes. The **pure-state**
case is the rank-1 instance `ρ = |ψ⟩⟨ψ|` (a projection with `trace ρ = 1`); see
`vonNeumannEntropy_eq_zero_of_pure` for that named form. Unit trace is not needed for `S = 0`
itself (every projection, including `0` and `I`, has spectrum in `{0,1}`). -/
theorem vonNeumannEntropy_eq_zero_of_projection {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hidem : ρ * ρ = ρ) :
    vonNeumannEntropy hρ = 0 := by
  -- eigenvalues are idempotent: λᵢ² = λᵢ.
  have hsq : ∀ i, hρ.eigenvalues i * hρ.eigenvalues i = hρ.eigenvalues i := by
    intro i
    have hcfc : hρ.cfc (fun x => x * x) = hρ.cfc id := by
      have h1 : hρ.cfc (fun x => x * x) = ρ * ρ := by
        rw [show (fun x : ℝ => x * x) = (fun x => id x * id x) from rfl, ← cfc_mul hρ id id,
          cfc_id hρ]
      rw [h1, hidem, cfc_id hρ]
    have := cfc_eq_iff_on_eigenvalues hρ hcfc i
    simpa using this
  -- so each eigenvalue is 0 or 1, where negMulLog = 0.
  refine Finset.sum_eq_zero fun i _ => ?_
  have hsplit : hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = 1 := by
    have hz : hρ.eigenvalues i * (hρ.eigenvalues i - 1) = 0 := by
      have := hsq i; ring_nf; linarith [this]
    rcases mul_eq_zero.mp hz with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  rcases hsplit with h0 | h1
  · rw [h0]; simp [Real.negMulLog]
  · rw [h1]; simp [Real.negMulLog]

/-- **`S(ρ) = 0` for a pure state** — a rank-1 density projection (`ρ` Hermitian, idempotent
`ρ·ρ = ρ`, unit trace `trace ρ = 1`). Direct corollary of
`vonNeumannEntropy_eq_zero_of_projection`. The unit-trace hypothesis is non-vacuous and
non-degenerate: it forces `∑ λᵢ = 1` with `λᵢ ∈ {0,1}`, i.e. **exactly one** eigenvalue equal
to `1`, so `ρ ≠ 0`; this is the genuine rank-1 pure state `|ψ⟩⟨ψ|`, not the trivial `ρ = 0`. -/
theorem vonNeumannEntropy_eq_zero_of_pure {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hidem : ρ * ρ = ρ) (_htr : ρ.trace = 1) :
    vonNeumannEntropy hρ = 0 :=
  vonNeumannEntropy_eq_zero_of_projection hρ hidem

/-! ## Unitary invariance -/

/-- **Charpoly conjugation-invariance:** `(U ρ Uᴴ).charpoly = ρ.charpoly` for `U` unitary
(`Uᴴ U = 1`). Two applications of `charpoly_mul_comm` plus `Uᴴ U = 1`. -/
theorem charpoly_conj_unitary {ρ U : Matrix n n ℂ} (hU : star U * U = 1) :
    (U * ρ * star U).charpoly = ρ.charpoly := by
  rw [Matrix.charpoly_mul_comm (U * ρ) (star U), ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- **Unitary invariance** `S(U ρ Uᴴ) = S(ρ)`. Conjugation by a unitary preserves the
characteristic polynomial, hence (by `eigenvalues_eq_eigenvalues_iff`) the eigenvalue
function, hence the spectral entropy sum. -/
theorem vonNeumannEntropy_conj_unitary {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    {U : Matrix n n ℂ} (hU : star U * U = 1)
    (hUρU : (U * ρ * star U).IsHermitian) :
    vonNeumannEntropy hUρU = vonNeumannEntropy hρ := by
  have heig : hUρU.eigenvalues = hρ.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hUρU hρ).mpr (charpoly_conj_unitary hU)
  rw [vonNeumannEntropy, vonNeumannEntropy, heig]

/-! ## Tensor additivity -/

omit [Fintype n] [DecidableEq n] in
/-- The Kronecker product of two Hermitian matrices is Hermitian. -/
theorem isHermitian_kronecker {m : Type*} [Fintype m] [DecidableEq m] {ρ : Matrix n n ℂ}
    {σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ ⊗ₖ σ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hρ.eq, hσ.eq]

/-- `negMulLog` of a product factorises: `negMulLog(a·b) = b·negMulLog a + a·negMulLog b` for
`a, b ≥ 0`. (At `a = 0` or `b = 0` both sides vanish; otherwise `log(ab) = log a + log b`.) -/
theorem negMulLog_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a * b) = b * Real.negMulLog a + a * Real.negMulLog b := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp [Real.negMulLog]
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simp [Real.negMulLog]
  simp only [Real.negMulLog]
  rw [Real.log_mul (ne_of_gt ha') (ne_of_gt hb')]
  ring

/-- **Additivity on tensor products** `S(ρ ⊗ σ) = S(ρ) + S(σ)`, under the explicit hypothesis
that the eigenvalues of `ρ ⊗ₖ σ` are the products `λ(e c).1 · μ(e c).2` of factor eigenvalues
along a reindexing `e : (n × m) ≃ k` of the Kronecker index.

This is the **honest weakened form of (6)**: Mathlib has no Kronecker spectral theorem, so the
eigenvalue-product fact is taken as a hypothesis (it holds for the genuine Kronecker spectrum;
discharging it is the deferred K1-A.2 item — see the module docstring and `specs/k1-plan.md`).
The `negMulLog`-product algebra and the `∑ λ = ∑ μ = 1` collapse are proved here.

`hsumρ`/`hsumσ` are the unit-trace conditions `∑ λᵢ = ∑ μⱼ = 1`; `hnnρ`/`hnnσ` the
PSD non-negativity of the factor eigenvalues. -/
theorem vonNeumannEntropy_kronecker_of_eigenvalues
    {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ} {τ : Matrix k k ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hτ : τ.IsHermitian)
    (e : (n × m) ≃ k)
    (heig : ∀ c, hτ.eigenvalues c
      = hρ.eigenvalues (e.symm c).1 * hσ.eigenvalues (e.symm c).2)
    (hnnρ : ∀ i, 0 ≤ hρ.eigenvalues i) (hnnσ : ∀ j, 0 ≤ hσ.eigenvalues j)
    (hsumρ : ∑ i, hρ.eigenvalues i = 1) (hsumσ : ∑ j, hσ.eigenvalues j = 1) :
    vonNeumannEntropy hτ = vonNeumannEntropy hρ + vonNeumannEntropy hσ := by
  rw [vonNeumannEntropy, vonNeumannEntropy, vonNeumannEntropy]
  -- reindex the τ-sum along e, then split negMulLog of the product.
  rw [← Equiv.sum_comp e (fun c => Real.negMulLog (hτ.eigenvalues c))]
  have hstep : ∀ p : n × m, Real.negMulLog (hτ.eigenvalues (e p))
      = hσ.eigenvalues p.2 * Real.negMulLog (hρ.eigenvalues p.1)
        + hρ.eigenvalues p.1 * Real.negMulLog (hσ.eigenvalues p.2) := by
    intro p
    rw [heig (e p), Equiv.symm_apply_apply]
    exact negMulLog_mul (hnnρ p.1) (hnnσ p.2)
  rw [Finset.sum_congr rfl (fun p _ => hstep p)]
  -- ∑_{i,j} [μⱼ·negMulLog λᵢ + λᵢ·negMulLog μⱼ] = (∑μ)(∑negMulLog λ) + (∑λ)(∑negMulLog μ).
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · -- ∑ᵢ ∑ⱼ μⱼ·negMulLog λᵢ = ∑ᵢ (∑ⱼ μⱼ)·negMulLog λᵢ = ∑ᵢ negMulLog λᵢ.
    rw [show (∑ x : n, ∑ y : m, hσ.eigenvalues y * Real.negMulLog (hρ.eigenvalues x))
        = ∑ x : n, (∑ y : m, hσ.eigenvalues y) * Real.negMulLog (hρ.eigenvalues x) from
          Finset.sum_congr rfl fun x _ => by rw [← Finset.sum_mul]]
    simp_rw [hsumσ, one_mul]
  · -- ∑ᵢ ∑ⱼ λᵢ·negMulLog μⱼ = ∑ᵢ λᵢ·(∑ⱼ negMulLog μⱼ) = ∑ⱼ negMulLog μⱼ.
    rw [show (∑ x : n, ∑ y : m, hρ.eigenvalues x * Real.negMulLog (hσ.eigenvalues y))
        = ∑ x : n, hρ.eigenvalues x * ∑ y : m, Real.negMulLog (hσ.eigenvalues y) from
          Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum]]
    rw [← Finset.sum_mul, hsumρ, one_mul]

end QuantumInfo

import CsdLean4.Mathlib.QuantumInfo.TraceDistance
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Jensen

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
* **unconditional additivity on tensor products** `S(ρ ⊗ σ) = S(ρ) + S(σ)` for density
  operators (PSD, unit trace) (`vonNeumannEntropy_kronecker`), via the **Kronecker spectrum**
  `spectral_sum_kronecker` (the eigenvalues of `ρ ⊗ₖ σ` are the products `λᵢ μⱼ`, in
  permutation-invariant spectral-sum form); the explicit-hypothesis form
  `vonNeumannEntropy_kronecker_of_eigenvalues` is retained for callers holding a sorted
  eigenvalue-product witness. See the note below.

## Note on the Kronecker spectrum (K1-A.2, done)

Mathlib has **no** lemma identifying the eigenvalues of a Kronecker product `ρ ⊗ₖ σ` with the
products `λᵢ μⱼ` of the factor eigenvalues (no Kronecker spectral theorem). We supply it here, in
the spectral-sum form that additivity needs (`spectral_sum_kronecker`):

  `∑_c g(λ(ρ⊗σ)_c) = ∑_{i,j} g(λρ(i)·λσ(j))`  for every `g : ℝ → ℝ`.

The route is **charpoly-based and permutation-invariant**, so it sidesteps the subtlety that
Mathlib's `eigenvalues` is the *sorted* spectrum (matching it pointwise to the products along an
ad-hoc reindexing is the easy-to-get-wrong step; the spectral *sum* avoids it). Concretely:
`ρ⊗σ = (U_ρ⊗U_σ) · diagonal(λρ·λσ) · (U_ρ⊗U_σ)ᴴ` (`kronecker_eq_conj_diagonal_eigenvalues`,
from the two spectral theorems + `mul_kronecker_mul` + `diagonal_kronecker_diagonal`), so its
charpoly is `∏_p (X − ↑(λρ(p.1)·λσ(p.2)))` (`charpoly_conj_unitary` + `charpoly_diagonal`); the
spectral sum is then read off the charpoly root multiset by `spectral_sum_eq_of_charpoly_prod`.
No external axiom is incurred (foundational triple only). This discharges the former K1-A.2 item;
the conditional `vonNeumannEntropy_kronecker_of_eigenvalues` is kept as a convenience.
-/

open Matrix Polynomial
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

/-! ## Maximum-entropy bound `S ≤ log d` -/

/-- **Maximum-entropy bound** `S(ρ) ≤ log d` for a density operator (PSD, unit trace) on a space
of dimension `d = Fintype.card n ≥ 1`. The maximally mixed state `ρ = I/d` saturates it.
Route: `negMulLog` is **concave** on `Ici 0` (`Real.concaveOn_negMulLog`); Finset Jensen
(`ConcaveOn.le_map_sum`) with uniform weights `wᵢ = 1/d` and `pᵢ = λᵢ ∈ [0,1] ⊂ Ici 0` gives
`∑ᵢ (1/d)·negMulLog(λᵢ) ≤ negMulLog(∑ᵢ (1/d)·λᵢ) = negMulLog(1/d)` (using `∑λᵢ = trace = 1`),
and `negMulLog(1/d) = (1/d)·log d`. Multiply through by `d`. -/
theorem vonNeumannEntropy_le_log_card {ρ : Matrix n n ℂ} (hpsd : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    vonNeumannEntropy hpsd.1 ≤ Real.log (Fintype.card n) := by
  set d : ℝ := (Fintype.card n : ℝ) with hd
  -- the index type is nonempty (its trace is 1 ≠ 0), so d ≥ 1 > 0.
  have hne : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Matrix.trace] at htr
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at htr
    exact zero_ne_one htr
  have hcard : 0 < Fintype.card n := Fintype.card_pos
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast hcard
  -- eigenvalue sum is 1.
  have hsum : ∑ i, hpsd.1.eigenvalues i = 1 := by
    have h := hpsd.1.trace_eq_sum_eigenvalues
    rw [htr] at h
    have hre := congrArg Complex.re h
    rw [Complex.one_re, Complex.re_sum] at hre
    simpa using hre.symm
  -- eigenvalues lie in Ici 0 (the concavity domain).
  have hmem : ∀ i ∈ Finset.univ, hpsd.1.eigenvalues i ∈ Set.Ici (0 : ℝ) :=
    fun i _ => (eigenvalues_mem_Icc_of_density hpsd htr i).1
  -- Jensen for the concave negMulLog with uniform weights 1/d.
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _ : n => 1 / d) (p := hpsd.1.eigenvalues)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hd]; field_simp)
    hmem
  -- ∑ (1/d) • λᵢ = (1/d) · ∑ λᵢ = 1/d.
  have hbary : ∑ i, (1 / d) • hpsd.1.eigenvalues i = 1 / d := by
    simp only [smul_eq_mul]
    rw [← Finset.mul_sum, hsum, mul_one]
  rw [hbary] at hjensen
  -- LHS of Jensen is (1/d) · S(ρ).
  have hLHS : ∑ i, (1 / d) • Real.negMulLog (hpsd.1.eigenvalues i)
      = (1 / d) * vonNeumannEntropy hpsd.1 := by
    rw [vonNeumannEntropy]
    simp only [smul_eq_mul]
    rw [Finset.mul_sum]
  rw [hLHS] at hjensen
  -- negMulLog(1/d) = (1/d) log d.
  have hval : Real.negMulLog (1 / d) = (1 / d) * Real.log d := by
    rw [Real.negMulLog, Real.log_div one_ne_zero (ne_of_gt hdpos), Real.log_one]
    ring
  rw [hval] at hjensen
  -- multiply both sides by d > 0.
  have := mul_le_mul_of_nonneg_left hjensen hdpos.le
  rw [show d * ((1 / d) * vonNeumannEntropy hpsd.1) = vonNeumannEntropy hpsd.1 by
        field_simp,
      show d * ((1 / d) * Real.log d) = Real.log d by field_simp] at this
  exact this

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

This is the **conditional form**: it takes the eigenvalue-product fact as a hypothesis. The
unconditional headline `vonNeumannEntropy_kronecker` discharges it via the Kronecker spectrum
`spectral_sum_kronecker` (K1-A.2, done); this form is retained for callers that already hold a
sorted eigenvalue-product witness along a specific reindexing `e`. The `negMulLog`-product
algebra and the `∑ λ = ∑ μ = 1` collapse are proved here.

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

/-! ## The Kronecker spectrum (discharging the K1-A.2 hypothesis) -/

/-- **Spectral-sum diagonalization invariance (charpoly form).** If a Hermitian `A` has
characteristic polynomial `∏ c, (X − ↑(d c))` for a real `d : k → ℝ` (i.e. its spectrum, with
multiplicity, is the multiset `{d c}`), then for every `g : ℝ → ℝ` the spectral sum
`∑ c, g(λᵢ(A))` equals `∑ c, g(d c)`.

The eigenvalue function `hA.eigenvalues` is Mathlib's *sorted* spectrum, so it is **not** equal to
`d` pointwise; only the *multiset* `{λᵢ}` equals `{d c}` (both are the charpoly root multiset, via
`roots_charpoly_eq_eigenvalues` and `roots_prod`). The spectral *sum* is permutation-invariant,
which is what lets us pass from the multiset equality to the sum equality (mapping by `g ∘ re` and
summing). This is the tool that sidesteps the eigenvalue-sorting subtlety. -/
theorem spectral_sum_eq_of_charpoly_prod
    {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix k k ℂ} (hA : A.IsHermitian)
    (d : k → ℝ) (g : ℝ → ℝ)
    (h : A.charpoly = ∏ c, (X - C ((RCLike.ofReal (d c)) : ℂ))) :
    ∑ c, g (hA.eigenvalues c) = ∑ c, g (d c) := by
  have hroots1 : A.charpoly.roots
      = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val :=
    hA.roots_charpoly_eq_eigenvalues
  have hroots2 : A.charpoly.roots
      = Multiset.map (fun c => (RCLike.ofReal (d c) : ℂ)) Finset.univ.val := by
    rw [h, Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp
  have hmap : Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val
      = Multiset.map (fun c => (RCLike.ofReal (d c) : ℂ)) Finset.univ.val := by
    rw [← hroots1, hroots2]
  have hcongr := congrArg (fun s => (Multiset.map (fun z : ℂ => g (RCLike.re z)) s).sum) hmap
  simp only [Multiset.map_map, Function.comp_apply, RCLike.ofReal_re] at hcongr
  rw [Finset.sum, Finset.sum]
  exact hcongr

/-- **The Kronecker product is unitarily similar to the diagonal of eigenvalue products.**
With `W := U_ρ ⊗ U_σ` (the Kronecker of the eigenvector unitaries),
`ρ ⊗ₖ σ = W · diagonal(λρ(p.1)·λσ(p.2)) · Wᴴ`. From the two spectral theorems
`ρ = U_ρ diag(λρ) U_ρᴴ`, `σ = U_σ diag(λσ) U_σᴴ`, `mul_kronecker_mul` (×2), and
`diagonal_kronecker_diagonal`. -/
theorem kronecker_eq_conj_diagonal_eigenvalues {m : Type*} [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ ⊗ₖ σ)
      = ((hρ.eigenvectorUnitary : Matrix n n ℂ) ⊗ₖ (hσ.eigenvectorUnitary : Matrix m m ℂ))
        * diagonal (fun p : n × m =>
            (RCLike.ofReal (hρ.eigenvalues p.1) : ℂ) * RCLike.ofReal (hσ.eigenvalues p.2))
        * star ((hρ.eigenvectorUnitary : Matrix n n ℂ)
            ⊗ₖ (hσ.eigenvectorUnitary : Matrix m m ℂ)) := by
  conv_lhs => rw [hρ.spectral_theorem, hσ.spectral_theorem,
    Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_kronecker]
  rw [← diagonal_kronecker_diagonal (fun i => (RCLike.ofReal (hρ.eigenvalues i) : ℂ))
        (fun j => (RCLike.ofReal (hσ.eigenvalues j) : ℂ)),
    mul_kronecker_mul, mul_kronecker_mul]
  rfl

/-- **The Kronecker eigenvector-unitary is unitary:** `(U_ρ ⊗ U_σ)ᴴ · (U_ρ ⊗ U_σ) = 1`. From
`conjTranspose_kronecker`, `mul_kronecker_mul`, `one_kronecker_one`. -/
theorem star_kronecker_eigenvectorUnitary_mul_self {m : Type*} [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    star ((hρ.eigenvectorUnitary : Matrix n n ℂ) ⊗ₖ (hσ.eigenvectorUnitary : Matrix m m ℂ))
      * ((hρ.eigenvectorUnitary : Matrix n n ℂ) ⊗ₖ (hσ.eigenvectorUnitary : Matrix m m ℂ))
      = 1 := by
  rw [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, ← Matrix.star_eq_conjTranspose,
    ← Matrix.star_eq_conjTranspose, ← mul_kronecker_mul,
    Unitary.coe_star_mul_self, Unitary.coe_star_mul_self, one_kronecker_one]

/-- **The Kronecker spectrum (eigenvalue-product fact).** The spectral sum of any `g : ℝ → ℝ`
over the eigenvalues of `ρ ⊗ₖ σ` equals the double sum over the products `λρ(i)·λσ(j)`:

  `∑_c g(λ(ρ⊗σ)_c) = ∑_{i,j} g(λρ(i)·λσ(j))`.

This is the load-bearing fact that discharges the `heig` hypothesis of
`vonNeumannEntropy_kronecker_of_eigenvalues`. Proof route: `ρ⊗σ` is unitarily similar to
`diagonal(λρ·λσ)` (`kronecker_eq_conj_diagonal_eigenvalues`), so its charpoly is
`∏ p, (X − ↑(λρ(p.1)·λσ(p.2)))` (`charpoly_conj_unitary` + `charpoly_diagonal`); the spectral sum
is then read off the charpoly root multiset by `spectral_sum_eq_of_charpoly_prod`, which is
permutation-invariant and so avoids matching Mathlib's *sorted* `eigenvalues` to the products
pointwise. No Kronecker spectral theorem is assumed; this **is** one (in spectral-sum form). -/
theorem spectral_sum_kronecker {m : Type*} [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (g : ℝ → ℝ) :
    ∑ c, g ((isHermitian_kronecker hρ hσ).eigenvalues c)
      = ∑ i, ∑ j, g (hρ.eigenvalues i * hσ.eigenvalues j) := by
  -- the charpoly of ρ⊗σ is the product of real linear factors X − ↑(λρ·λσ).
  have hchar : (ρ ⊗ₖ σ).charpoly
      = ∏ p : n × m, (X - C ((RCLike.ofReal (hρ.eigenvalues p.1 * hσ.eigenvalues p.2)) : ℂ)) := by
    rw [kronecker_eq_conj_diagonal_eigenvalues hρ hσ,
      charpoly_conj_unitary (star_kronecker_eigenvectorUnitary_mul_self hρ hσ),
      charpoly_diagonal]
    exact Finset.prod_congr rfl fun p _ => by rw [RCLike.ofReal_mul]
  -- read the spectral sum off the root multiset, then re-index the product over n × m.
  rw [spectral_sum_eq_of_charpoly_prod (isHermitian_kronecker hρ hσ)
    (fun p => hρ.eigenvalues p.1 * hσ.eigenvalues p.2) g hchar,
    ← Finset.univ_product_univ, Finset.sum_product]

/-- **Unconditional additivity of the von Neumann entropy on tensor products:**
`S(ρ ⊗ σ) = S(ρ) + S(σ)` for two density operators `ρ, σ` (PSD, unit trace). The
eigenvalue-product hypothesis of `vonNeumannEntropy_kronecker_of_eigenvalues` is discharged here
via the Kronecker spectrum `spectral_sum_kronecker`; the `negMulLog`-product algebra
(`negMulLog_mul`) and the `∑λ = ∑μ = 1` collapse close the argument.

This is **K1-A.2** of `specs/k1-plan.md`, now done: additivity holds with no spectral hypothesis,
only the density conditions. (The conditional form
`vonNeumannEntropy_kronecker_of_eigenvalues` is retained for callers that already hold a sorted
eigenvalue-product witness.) -/
theorem vonNeumannEntropy_kronecker {m : Type*} [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ}
    (hpsdρ : ρ.PosSemidef) (hpsdσ : σ.PosSemidef)
    (htrρ : ρ.trace = 1) (htrσ : σ.trace = 1) :
    vonNeumannEntropy (isHermitian_kronecker hpsdρ.1 hpsdσ.1)
      = vonNeumannEntropy hpsdρ.1 + vonNeumannEntropy hpsdσ.1 := by
  -- unit-trace ⟹ eigenvalue sums are 1.
  have hsumρ : ∑ i, hpsdρ.1.eigenvalues i = 1 := by
    have h := hpsdρ.1.trace_eq_sum_eigenvalues
    rw [htrρ] at h
    have hre := congrArg Complex.re h
    rw [Complex.one_re, Complex.re_sum] at hre
    simpa using hre.symm
  have hsumσ : ∑ j, hpsdσ.1.eigenvalues j = 1 := by
    have h := hpsdσ.1.trace_eq_sum_eigenvalues
    rw [htrσ] at h
    have hre := congrArg Complex.re h
    rw [Complex.one_re, Complex.re_sum] at hre
    simpa using hre.symm
  -- expand all three entropies; the τ-sum is the Kronecker spectral sum.
  rw [vonNeumannEntropy, vonNeumannEntropy, vonNeumannEntropy,
    spectral_sum_kronecker hpsdρ.1 hpsdσ.1 Real.negMulLog]
  -- split negMulLog of each product, then collapse via ∑λ = ∑μ = 1.
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    negMulLog_mul (hpsdρ.eigenvalues_nonneg i) (hpsdσ.eigenvalues_nonneg j)))]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ i : n, ∑ j : m, hpsdσ.1.eigenvalues j * Real.negMulLog (hpsdρ.1.eigenvalues i))
        = ∑ i : n, (∑ j : m, hpsdσ.1.eigenvalues j) * Real.negMulLog (hpsdρ.1.eigenvalues i) from
          Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul]]
    simp_rw [hsumσ, one_mul]
  · rw [show (∑ i : n, ∑ j : m, hpsdρ.1.eigenvalues i * Real.negMulLog (hpsdσ.1.eigenvalues j))
        = ∑ i : n, hpsdρ.1.eigenvalues i * ∑ j : m, Real.negMulLog (hpsdσ.1.eigenvalues j) from
          Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum]]
    rw [← Finset.sum_mul, hsumρ, one_mul]

end QuantumInfo

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Clifford
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Stabiliser families, the group projector, and the stabilised state (GK-3)

**Category:** 1-Mathlib (CSD-free).

The stabiliser layer over the Pauli algebra (plan `specs/gottesman-knill-plan.md`, GK-3),
in the corpus's hypothesis-driven concrete style: a **stabiliser family** is indexed by
`𝔽₂^m` directly — `𝔽₂`-linear label maps `A B : 𝔽₂^m → 𝔽₂ⁿ` and a sign function
`σ : 𝔽₂^m → 𝔽₂` subject to the one **coherence law**

  `σ(x+y) = σ(x) + σ(y) + B(x)·A(y)`,

which is exactly the condition that the signed Paulis `χ(σx)·X^{Ax}Z^{Bx}` form a genuine
group (the `𝔽₂` pairing on the right is the phase of `pauliOp_mul`) — the "`−I ∉ S`"
condition of the stabiliser formalism. Commutativity of the family is *implied*: coherence
at `(x,y)` and at `(y,x)` forces the symplectic form of any two members to vanish
(`stab_symp_zero`).

* ★ **Absorption** (`stabProjector_absorb`): every signed element of the family fixes the
  group average `P = 2^{−m} ∑_x χ(σx)·X^{Ax}Z^{Bx}` — one reindex `y ↦ x + y`.
* ★ **Idempotence** (`stabProjector_idem`): `P² = P`, three lines from absorption.
* ★ **The trace** (`stabProjector_trace`): with independent labels,
  `tr P = 2ⁿ/2^m` — the dimension count of the code space; `1` for a full stabiliser
  (`m = n`).
* ★★ **The stabilised state exists** (`stabState_exists`): a nonzero `ψ` with `Pψ = ψ` and
  `χ(σx)·X^{Ax}Z^{Bx} ψ = ψ` for **every** group element — the defining property of a
  stabiliser state, extracted from `tr P ≠ 0` plus idempotence, no spectral machinery.

Both residues named at the first landing are now discharged in this file:

* **Uniqueness/dimension** (`stabProjector_rank`, `stabState_unique`): the group average is a
  genuine linear projection (`stabProjectorL`, `IsProj` onto its range = the fixed space),
  so Mathlib's rank-equals-trace for projections (`LinearMap.IsProj.trace`) turns the trace
  count into `finrank (fixed space) = 2^{n−m}` — and for a full stabiliser (`m = n`) the
  stabilised state is **unique up to scalar**.
* **The measurement-update rule** (`measProj` section): measuring an involutive Pauli
  observable `g` on a stabilised state — ★ the outcome is **deterministic** when the signed
  `g` is in the group (`meas_deterministic`); ★ when `g` **anticommutes** with a group
  element the expectation vanishes (`meas_expectation_zero`) and both outcomes carry
  **probability exactly `1/2`** (`meas_prob_half`); and the post-measurement branch is
  stabilised by `±g` itself (`pauliOp_measProj`) and by every group element **commuting**
  with `g` (`meas_update_fixes`) — the standard stabiliser update, stated operator-free.

**Honest scope.** Measurement is Born-weight bookkeeping on the corpus's coordinate
operators; no measurement *dynamics* is claimed (that is the CSD layer's business
elsewhere). The `IsProj.trace` route uses Mathlib's linear algebra, not a spectral theorem.
-/

@[expose] public section

open scoped ComplexConjugate

namespace QuantumInfo

variable {n m : ℕ}

/-- The **stabiliser-group average**
`P = 2^{−m} ∑_{x ∈ 𝔽₂^m} χ(σx) · X^{Ax} Z^{Bx}`, applied to a state. -/
noncomputable def stabProjector (A B : (Fin m → Fin 2) → (Fin n → Fin 2))
    (σ : (Fin m → Fin 2) → Fin 2) (ψ : QReg n) : QReg n :=
  ((2 : ℂ) ^ m)⁻¹ • ∑ x : Fin m → Fin 2, signChar (σ x) • pauliOp (A x) (B x) ψ

section Coherent

variable {A B : (Fin m → Fin 2) → (Fin n → Fin 2)} {σ : (Fin m → Fin 2) → Fin 2}

/-- Linearity forces the zero label at `0`. -/
lemma stab_label_zero (hA : ∀ x y, A (x + y) = A x + A y) : A 0 = 0 := by
  have h := hA 0 0
  rw [add_zero] at h
  have h2 : A 0 + A 0 = 0 := by
    funext i
    rw [Pi.add_apply, Pi.zero_apply]
    exact fin2_add_self _
  exact h.trans h2

/-- Coherence forces the trivial sign at `0` — the group contains `+I`, not `−I`. -/
lemma stab_sigma_zero (hB : ∀ x y, B (x + y) = B x + B y)
    (hσ : ∀ x y, σ (x + y) = σ x + σ y + bdot (B x) (A y)) : σ 0 = 0 := by
  have h := hσ 0 0
  rw [add_zero, stab_label_zero hB, bdot_zero_left, add_zero] at h
  exact h.trans (fin2_add_self _)

/-- Coherence at `(x,y)` and `(y,x)` forces the symplectic form of any two members to
vanish: the family is automatically abelian. -/
lemma stab_symp_zero (hσ : ∀ x y, σ (x + y) = σ x + σ y + bdot (B x) (A y))
    (x y : Fin m → Fin 2) : bdot (A x) (B y) + bdot (B x) (A y) = 0 := by
  have h1 := hσ x y
  have h2 := hσ y x
  rw [add_comm y x] at h2
  have h3 : σ x + σ y + bdot (B x) (A y) = σ y + σ x + bdot (B y) (A x) :=
    h1.symm.trans h2
  have h4 : bdot (B x) (A y) = bdot (B y) (A x) := by
    have := h3
    generalize σ x = p at this
    generalize σ y = q at this
    generalize bdot (B x) (A y) = r at this
    generalize bdot (B y) (A x) = s at this
    revert this
    revert p q r s
    decide
  rw [bdot_comm (A x) (B y), ← h4]
  exact fin2_add_self _

variable (hA : ∀ x y, A (x + y) = A x + A y) (hB : ∀ x y, B (x + y) = B x + B y)
variable (hσ : ∀ x y, σ (x + y) = σ x + σ y + bdot (B x) (A y))

include hA hB hσ in
/-- ★ **Absorption:** every signed element of the family fixes the group average. -/
theorem stabProjector_absorb (x : Fin m → Fin 2) (ψ : QReg n) :
    signChar (σ x) • pauliOp (A x) (B x) (stabProjector A B σ ψ)
      = stabProjector A B σ ψ := by
  rw [stabProjector, pauliOp_smul, pauliOp_sum,
    Finset.sum_congr rfl fun y _ => by rw [pauliOp_smul, pauliOp_mul],
    smul_comm (signChar (σ x)) (((2 : ℂ) ^ m)⁻¹), Finset.smul_sum,
    Finset.sum_congr rfl fun y _ => by
      rw [smul_smul, smul_smul, pauliSign, ← signChar_add, ← signChar_add, ← hσ x y,
        ← hA x y, ← hB x y]]
  congr 1
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => rfl

include hA hB hσ in
/-- ★ **Idempotence**, three lines from absorption. -/
theorem stabProjector_idem (ψ : QReg n) :
    stabProjector A B σ (stabProjector A B σ ψ) = stabProjector A B σ ψ := by
  conv_lhs => rw [stabProjector]
  rw [Finset.sum_congr rfl fun x _ => stabProjector_absorb hA hB hσ x ψ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

include hA hB hσ in
/-- ★ **The trace of the group average is the code-space dimension count** `2ⁿ/2^m`
(`= 1` for a full stabiliser, `m = n`): only the identity label survives the Pauli trace,
and independence pins it to `x = 0`, where coherence forces the `+` sign. -/
theorem stabProjector_trace (hinj : ∀ x, A x = 0 → B x = 0 → x = 0) :
    ∑ z : Fin n → Fin 2, stabProjector A B σ (basisState z) z
      = (2 : ℂ) ^ n / (2 : ℂ) ^ m := by
  have hterm : ∀ z : Fin n → Fin 2,
      stabProjector A B σ (basisState z) z
        = ((2 : ℂ) ^ m)⁻¹ * ∑ x : Fin m → Fin 2,
            signChar (σ x) * pauliOp (A x) (B x) (basisState z) z := by
    intro z
    rw [stabProjector, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sum_coord]
    congr 1
  rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.mul_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun x _ => by rw [← Finset.mul_sum, pauliOp_trace],
    Finset.sum_eq_single 0
      (fun x _ hx => by rw [if_neg fun h => hx (hinj x h.1 h.2), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h),
    if_pos ⟨stab_label_zero hA, stab_label_zero hB⟩, stab_sigma_zero hB hσ,
    signChar_zero, one_mul, mul_comm, ← div_eq_mul_inv]

include hA hB hσ in
/-- ★★ **The stabilised state exists:** a nonzero `ψ` fixed by the group average and by
**every** signed element of the family — the defining property of a stabiliser state.
Extracted from `tr P ≠ 0` and idempotence; no spectral machinery. (That the fixed space has
dimension exactly `2^{n−m}` is the named uniqueness residue in the plan.) -/
theorem stabState_exists (hinj : ∀ x, A x = 0 → B x = 0 → x = 0) :
    ∃ ψ : QReg n, ψ ≠ 0 ∧ stabProjector A B σ ψ = ψ
      ∧ ∀ x, signChar (σ x) • pauliOp (A x) (B x) ψ = ψ := by
  have hne : ∃ φ : QReg n, stabProjector A B σ φ ≠ 0 := by
    by_contra hall
    rw [not_exists] at hall
    have h0 : ∀ φ : QReg n, stabProjector A B σ φ = 0 :=
      fun φ => not_not.mp (hall φ)
    have htr := stabProjector_trace hA hB hσ hinj
    rw [Finset.sum_congr rfl fun z _ => by rw [h0 (basisState z)]] at htr
    simp only [WithLp.ofLp_zero, Pi.zero_apply, Finset.sum_const_zero] at htr
    exact (div_ne_zero (pow_ne_zero n (two_ne_zero))
      (pow_ne_zero m (two_ne_zero))) htr.symm
  obtain ⟨φ, hφ⟩ := hne
  exact ⟨stabProjector A B σ φ, hφ, stabProjector_idem hA hB hσ φ,
    fun x => stabProjector_absorb hA hB hσ x φ⟩

end Coherent

/-! ## The group average as a linear projection, and rank = trace -/

lemma stabProjector_map_add (A B : (Fin m → Fin 2) → (Fin n → Fin 2))
    (σ : (Fin m → Fin 2) → Fin 2) (ψ χ : QReg n) :
    stabProjector A B σ (ψ + χ) = stabProjector A B σ ψ + stabProjector A B σ χ := by
  rw [stabProjector, stabProjector, stabProjector,
    Finset.sum_congr rfl fun x _ => by rw [pauliOp_add, smul_add],
    Finset.sum_add_distrib, smul_add]

lemma stabProjector_map_smul (A B : (Fin m → Fin 2) → (Fin n → Fin 2))
    (σ : (Fin m → Fin 2) → Fin 2) (c : ℂ) (ψ : QReg n) :
    stabProjector A B σ (c • ψ) = c • stabProjector A B σ ψ := by
  rw [stabProjector, stabProjector,
    Finset.sum_congr rfl fun x _ => by
      rw [pauliOp_smul, smul_comm (signChar (σ x)) c],
    ← Finset.smul_sum, smul_comm ((2 : ℂ) ^ m)⁻¹ c]

/-- The group average as a linear map. -/
noncomputable def stabProjectorL (A B : (Fin m → Fin 2) → (Fin n → Fin 2))
    (σ : (Fin m → Fin 2) → Fin 2) : QReg n →ₗ[ℂ] QReg n where
  toFun := stabProjector A B σ
  map_add' := stabProjector_map_add A B σ
  map_smul' := stabProjector_map_smul A B σ

@[simp] lemma stabProjectorL_apply (A B : (Fin m → Fin 2) → (Fin n → Fin 2))
    (σ : (Fin m → Fin 2) → Fin 2) (ψ : QReg n) :
    stabProjectorL A B σ ψ = stabProjector A B σ ψ := rfl

/-- The linear-map trace is the coordinate diagonal sum this file computes. -/
lemma stabProjectorL_trace (A B : (Fin m → Fin 2) → (Fin n → Fin 2))
    (σ : (Fin m → Fin 2) → Fin 2) :
    LinearMap.trace ℂ (QReg n) (stabProjectorL A B σ)
      = ∑ z : Fin n → Fin 2, stabProjector A B σ (basisState z) z := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin n → Fin 2)), Matrix.trace]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, PiLp.basisFun_repr,
    stabProjectorL_apply,
    show PiLp.basisFun 2 ℂ (Fin n → Fin 2) z = basisState z from by
      rw [PiLp.basisFun_apply]
      rfl]

section Coherent2

variable {A B : (Fin m → Fin 2) → (Fin n → Fin 2)} {σ : (Fin m → Fin 2) → Fin 2}
variable (hA : ∀ x y, A (x + y) = A x + A y) (hB : ∀ x y, B (x + y) = B x + B y)
variable (hσ : ∀ x y, σ (x + y) = σ x + σ y + bdot (B x) (A y))

include hA hB hσ in
/-- The group average is a genuine linear projection onto its range. -/
lemma stabProjectorL_isProj :
    LinearMap.IsProj (LinearMap.range (stabProjectorL A B σ)) (stabProjectorL A B σ) where
  map_mem ψ := LinearMap.mem_range_self _ ψ
  map_id ψ hψ := by
    obtain ⟨φ, hφ⟩ := hψ
    rw [← hφ, stabProjectorL_apply, stabProjectorL_apply,
      stabProjector_idem hA hB hσ φ]

include hA hB hσ in
/-- The range of the group average is exactly the fixed space. -/
lemma mem_range_stabProjectorL_iff (φ : QReg n) :
    φ ∈ LinearMap.range (stabProjectorL A B σ) ↔ stabProjector A B σ φ = φ := by
  constructor
  · rintro ⟨ψ, hψ⟩
    rw [← hψ, stabProjectorL_apply, stabProjector_idem hA hB hσ ψ]
  · intro h
    exact ⟨φ, h⟩

include hA hB hσ in
/-- ★★ **Rank equals trace — the uniqueness residue discharged:** the fixed space of a
stabiliser family with `m` independent generators on `n` qubits has dimension exactly
`2^{n−m}`. Via Mathlib's `LinearMap.IsProj.trace`; no spectral theorem. -/
theorem stabProjector_rank (hinj : ∀ x, A x = 0 → B x = 0 → x = 0) (hmn : m ≤ n) :
    Module.finrank ℂ ↥(LinearMap.range (stabProjectorL A B σ)) = 2 ^ (n - m) := by
  have htr := (stabProjectorL_isProj hA hB hσ).trace
  rw [stabProjectorL_trace, stabProjector_trace hA hB hσ hinj,
    show (2 : ℂ) ^ n / (2 : ℂ) ^ m = ((2 ^ (n - m) : ℕ) : ℂ) from by
      push_cast
      rw [pow_sub₀ _ (two_ne_zero) hmn, div_eq_mul_inv]] at htr
  exact_mod_cast htr.symm

omit hA hB hσ in
/-- ★★ **The full-stabiliser state is unique up to scalar** (`m = n`): any two stabilised
vectors are parallel. -/
theorem stabState_unique {A' B' : (Fin n → Fin 2) → (Fin n → Fin 2)}
    {σ' : (Fin n → Fin 2) → Fin 2}
    (hA' : ∀ x y, A' (x + y) = A' x + A' y) (hB' : ∀ x y, B' (x + y) = B' x + B' y)
    (hσ' : ∀ x y, σ' (x + y) = σ' x + σ' y + bdot (B' x) (A' y))
    (hinj : ∀ x, A' x = 0 → B' x = 0 → x = 0)
    (ψ φ : QReg n) (hψfix : stabProjector A' B' σ' ψ = ψ)
    (hφfix : stabProjector A' B' σ' φ = φ) (hψ0 : ψ ≠ 0) :
    ∃ c : ℂ, φ = c • ψ := by
  have hrank := stabProjector_rank hA' hB' hσ' hinj (le_refl n)
  rw [Nat.sub_self, pow_zero] at hrank
  have hψp : ψ ∈ LinearMap.range (stabProjectorL A' B' σ') :=
    (mem_range_stabProjectorL_iff hA' hB' hσ' ψ).mpr hψfix
  have hφp : φ ∈ LinearMap.range (stabProjectorL A' B' σ') :=
    (mem_range_stabProjectorL_iff hA' hB' hσ' φ).mpr hφfix
  obtain ⟨v, hv0, hvgen⟩ := (finrank_eq_one_iff'
    (V := ↥(LinearMap.range (stabProjectorL A' B' σ')))).mp hrank
  obtain ⟨cψ, hcψ⟩ := hvgen ⟨ψ, hψp⟩
  obtain ⟨cφ, hcφ⟩ := hvgen ⟨φ, hφp⟩
  have h1 : cψ • (v : QReg n) = ψ := congrArg Subtype.val hcψ
  have h2 : cφ • (v : QReg n) = φ := congrArg Subtype.val hcφ
  have hcψ0 : cψ ≠ 0 := by
    intro h
    apply hψ0
    rw [← h1, h, zero_smul]
  exact ⟨cφ / cψ, by rw [← h2, ← h1, smul_smul, div_mul_cancel₀ _ hcψ0]⟩

end Coherent2

/-! ## Measurement of an involutive Pauli observable -/

/-- The outcome-`s` measurement branch of the Pauli observable `X^a Z^b`:
`Π_s ψ = (ψ + χ(s)·gψ)/2`, the `χ(s)`-eigenspace projection. -/
noncomputable def measProj (a b : Fin n → Fin 2) (s : Fin 2) (ψ : QReg n) : QReg n :=
  (2 : ℂ)⁻¹ • (ψ + signChar s • pauliOp a b ψ)

variable {a b : Fin n → Fin 2}

/-- An `X`/`Z`-type Pauli (`b·a = 0`) is an involution. -/
lemma pauliOp_involutive (hba : bdot b a = 0) (ψ : QReg n) :
    pauliOp a b (pauliOp a b ψ) = ψ := by
  rw [pauliOp_mul, pauliSign, hba, signChar_zero, one_smul,
    show a + a = 0 from funext fun i => fin2_add_self _,
    show b + b = 0 from funext fun i => fin2_add_self _, pauliOp_zero]

/-- The two branches partition the state: `Π₀ψ + Π₁ψ = ψ`. -/
lemma measProj_add_compl (ψ : QReg n) :
    measProj a b 0 ψ + measProj a b 1 ψ = ψ := by
  rw [measProj, measProj, signChar_zero, one_smul,
    show signChar 1 = (-1 : ℂ) from rfl, neg_one_smul]
  module

/-- ★ **The branch is stabilised by the signed observable:** `g(Π_sψ) = χ(s)·Π_sψ` — half of
the measurement-update rule. -/
lemma pauliOp_measProj (hba : bdot b a = 0) (s : Fin 2) (ψ : QReg n) :
    pauliOp a b (measProj a b s ψ) = signChar s • measProj a b s ψ := by
  have hrhs : signChar s • measProj a b s ψ
      = (2 : ℂ)⁻¹ • (signChar s • ψ + pauliOp a b ψ) := by
    rw [measProj, smul_comm (signChar s) ((2 : ℂ)⁻¹)]
    congr 1
    rw [smul_add, smul_smul, signChar_mul_self, one_smul]
  rw [hrhs, measProj, pauliOp_smul, pauliOp_add, pauliOp_smul, pauliOp_involutive hba,
    add_comm (pauliOp a b ψ) (signChar s • ψ)]

/-- ★ **The deterministic case:** if the signed observable already stabilises `ψ`, the
matching outcome is certain and the other branch is empty. -/
theorem meas_deterministic (t : Fin 2) (ψ : QReg n)
    (hfix : signChar t • pauliOp a b ψ = ψ) :
    measProj a b t ψ = ψ ∧ measProj a b (t + 1) ψ = 0 := by
  have hg : pauliOp a b ψ = signChar t • ψ := by
    calc pauliOp a b ψ = (signChar t * signChar t) • pauliOp a b ψ := by
          rw [signChar_mul_self, one_smul]
      _ = signChar t • (signChar t • pauliOp a b ψ) := by rw [smul_smul]
      _ = signChar t • ψ := by rw [hfix]
  constructor
  · rw [measProj, hg, smul_smul, signChar_mul_self, one_smul]
    module
  · rw [measProj, hg, smul_smul, ← signChar_add,
      show t + 1 + t = 1 from by fin_cases t <;> rfl,
      show signChar 1 = (-1 : ℂ) from rfl, neg_one_smul, add_neg_cancel, smul_zero]

/-- Fixed states absorb their group elements inside an inner product. -/
lemma inner_fixed_pauliOp {a' b' : Fin n → Fin 2} {u : Fin 2} (ψ φ : QReg n)
    (hs : signChar u • pauliOp a' b' ψ = ψ) :
    inner ℂ ψ (pauliOp a' b' φ) = signChar u * inner ℂ ψ φ := by
  conv_lhs => rw [← hs]
  rw [inner_smul_left, conj_signChar, inner_pauliOp]

/-- ★ **The random case, expectation:** if some group element stabilising `ψ` anticommutes
with the observable, the expectation `⟨ψ, gψ⟩` vanishes. -/
theorem meas_expectation_zero {a' b' : Fin n → Fin 2} {u : Fin 2} (ψ : QReg n)
    (hs : signChar u • pauliOp a' b' ψ = ψ)
    (hanti : bdot a b' + bdot b a' = 1) :
    inner ℂ ψ (pauliOp a b ψ) = 0 := by
  have hanticomm : ∀ χ : QReg n,
      pauliOp a b (pauliOp a' b' χ) = -pauliOp a' b' (pauliOp a b χ) := by
    intro χ
    rw [pauliOp_comm, hanti, show signChar 1 = (-1 : ℂ) from rfl, neg_one_smul]
  have key : inner ℂ ψ (pauliOp a b ψ) = -inner ℂ ψ (pauliOp a b ψ) := by
    nth_rewrite 1 [show pauliOp a b ψ
        = signChar u • -pauliOp a' b' (pauliOp a b ψ) from by
      conv_lhs => rw [← hs]
      rw [pauliOp_smul, hanticomm]]
    rw [inner_smul_right, inner_neg_right,
      inner_fixed_pauliOp ψ (pauliOp a b ψ) hs, mul_neg, ← mul_assoc,
      signChar_mul_self, one_mul]
  linear_combination key / 2

/-- ★ **The random case, Born weights:** both outcomes carry probability exactly `1/2`. -/
theorem meas_prob_half {a' b' : Fin n → Fin 2} {u : Fin 2}
    (ψ : QReg n) (hψ : inner ℂ ψ ψ = 1)
    (hs : signChar u • pauliOp a' b' ψ = ψ)
    (hanti : bdot a b' + bdot b a' = 1) (s : Fin 2) :
    inner ℂ (measProj a b s ψ) (measProj a b s ψ) = 1 / 2 := by
  have hE := meas_expectation_zero ψ hs hanti
  have hE' : inner ℂ (pauliOp a b ψ) ψ = 0 := by
    rw [← inner_conj_symm, hE, map_zero]
  rw [measProj, inner_smul_left, inner_smul_right]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    conj_signChar, inner_pauliOp, hψ, hE, hE', map_inv₀, map_ofNat, mul_zero, add_zero,
    zero_add]
  have hss := signChar_mul_self s
  field_simp
  linear_combination hss

/-- ★ **The update rule:** every group element commuting with the observable still
stabilises the post-measurement branch. Together with `pauliOp_measProj` this is the
standard stabiliser update: the new group is generated by `χ(s)·g` and the commuting part
of the old one. -/
theorem meas_update_fixes {a' b' : Fin n → Fin 2} {u : Fin 2} (ψ : QReg n)
    (hs : signChar u • pauliOp a' b' ψ = ψ)
    (hcomm : bdot a' b + bdot b' a = 0) (s : Fin 2) :
    signChar u • pauliOp a' b' (measProj a b s ψ) = measProj a b s ψ := by
  rw [measProj, pauliOp_smul, pauliOp_add, pauliOp_smul,
    pauliOp_comm_of_symp a' b' a b hcomm ψ, smul_comm (signChar u) ((2 : ℂ)⁻¹), smul_add,
    hs, smul_smul, mul_comm (signChar u) (signChar s), ← smul_smul, ← pauliOp_smul, hs]

end QuantumInfo

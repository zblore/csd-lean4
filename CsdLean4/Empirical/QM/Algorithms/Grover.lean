import CsdLean4.Mathlib.QuantumInfo.Hadamard

/-!
# Grover's search algorithm (R5+)

**Category:** 3-Local (QM-validity).

Grover's algorithm (phase R5+ of `specs/nqubit-register-plan.md`): amplitude amplification of a
single marked item `w : Fin n → Fin 2` in an unstructured database of `N = 2ⁿ` items. The
search step is the composition of the **oracle** (phase flip on `w`, `I - 2|w⟩⟨w|`) and the
**diffusion** operator (inversion about the mean, `2|s⟩⟨s| - I`, where `|s⟩` is the uniform
superposition).

The whole evolution stays inside the two-dimensional subspace spanned by `|w⟩` and the uniform
state, where one Grover step is a **rotation by `2θ`** with `sin θ = 1/√N`. The symmetric-state
family `symState w a b` (amplitude `a` on the marked item, `b` on each of the others) carries
that 2D plane; the operator action lemmas (`oracle_symState`, `diffusion_symState`,
`groverStep_symState`) compute the step as a linear map of the `(a, b)` coefficients.

The headline (`grover_success`) is the closed form for the success probability after `k` steps:

  `prob ((groverStep w)^[k] uniformState) w = sin²((2k+1)·θ)`,

obtained by iterating the single-step rotation lemma (`groverStep_rotates`) from the starting
angle `θ` (`uniformState_eq_symState_theta`).

**Honest scope.** This is QM-validity breadth: the genuine reflection operators are built on the
`EuclideanSpace` inner-product structure (`oracle = I - 2|w⟩⟨w|`, `diffusion = 2|s⟩⟨s| - I`), so
the rotation is a real Hilbert-space computation. The amplitudes are real throughout; they are
carried as `ℂ`-coercions of `ℝ` so the operators stay genuinely complex / Hilbert. The optimal
iteration count and the success-probability bound are downstream arithmetic on this closed form;
they are not formalised here.
-/

open scoped ComplexConjugate
open QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace Grover

variable {n : ℕ}

/-- The database size `N = 2ⁿ` as a real number. -/
noncomputable def databaseSize (n : ℕ) : ℝ := 2 ^ n

/-- The all-ones vector `J = ∑ z |z⟩`: amplitude `1` on every basis state. -/
noncomputable def J (n : ℕ) : QReg n := ∑ z, basisState z

lemma J_coord (z : Fin n → Fin 2) : J n z = ∑ x, (basisState x z) := by
  have h : (J n).ofLp = ∑ x, (basisState x).ofLp := by
    rw [J]
    exact map_sum (WithLp.addEquiv 2 ((Fin n → Fin 2) → ℂ)) basisState Finset.univ
  calc J n z = (J n).ofLp z := rfl
    _ = (∑ x, (basisState x).ofLp) z := by rw [h]
    _ = ∑ x, (basisState x z) := by rw [Finset.sum_apply]

@[simp] lemma J_apply (z : Fin n → Fin 2) : J n z = 1 := by
  rw [J_coord, Finset.sum_eq_single z]
  · rw [basisState_apply, if_pos rfl]
  · intro b _ hb; rw [basisState_apply]; rw [if_neg (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The number of basis states summed as a complex constant: `∑ z, (1 : ℂ) = N`. -/
lemma sum_one_eq_N : (∑ _z : (Fin n → Fin 2), (1 : ℂ)) = ((2 : ℂ) ^ n) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]

/-- The **uniform superposition** `|s⟩ = (1/√N) ∑ z |z⟩`. -/
noncomputable def uniformState : QReg n := (Real.sqrt (databaseSize n))⁻¹ • J n

@[simp] lemma uniformState_apply (z : Fin n → Fin 2) :
    (uniformState : QReg n) z = (Real.sqrt (databaseSize n) : ℂ)⁻¹ := by
  rw [uniformState, WithLp.ofLp_smul, Pi.smul_apply, J_apply, Complex.real_smul, mul_one,
    Complex.ofReal_inv]

/-- The **oracle** `O_w = I - 2|w⟩⟨w|`: a phase flip on the marked item `w`. -/
noncomputable def oracle (w : Fin n → Fin 2) (ψ : QReg n) : QReg n :=
  ψ - (2 * ψ w) • basisState w

/-- The **diffusion** operator `2|s⟩⟨s| - I`: inversion about the mean. -/
noncomputable def diffusion (ψ : QReg n) : QReg n :=
  (2 * inner ℂ (uniformState) ψ) • uniformState - ψ

/-- One **Grover step**: oracle then diffusion. -/
noncomputable def groverStep (w : Fin n → Fin 2) (ψ : QReg n) : QReg n :=
  diffusion (oracle w ψ)

/-! ## The symmetric-state family -/

/-- The **symmetric state** with amplitude `a` on the marked item `w` and amplitude `b` on each
of the other `N - 1` items: `symState w a b = b·J + (a - b)·|w⟩`. -/
noncomputable def symState (w : Fin n → Fin 2) (a b : ℂ) : QReg n :=
  b • J n + (a - b) • basisState w

@[simp] lemma symState_apply (w : Fin n → Fin 2) (a b : ℂ) (z : Fin n → Fin 2) :
    symState w a b z = if z = w then a else b := by
  rw [symState, WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul, WithLp.ofLp_smul, Pi.smul_apply,
    Pi.smul_apply, J_apply, basisState_apply, smul_eq_mul, smul_eq_mul, mul_one]
  split
  · ring
  · ring

/-- The uniform state is the symmetric state with all coefficients `(√N)⁻¹`. -/
lemma uniformState_eq_symState (w : Fin n → Fin 2) :
    uniformState = symState w (Real.sqrt (databaseSize n) : ℂ)⁻¹
      (Real.sqrt (databaseSize n) : ℂ)⁻¹ := by
  ext z
  rw [uniformState_apply, symState_apply]
  split <;> rfl

/-! ## Operator actions on the symmetric family -/

/-- The oracle flips the sign of the marked-item amplitude: `O_w (symState a b) = symState (-a) b`. -/
lemma oracle_symState (w : Fin n → Fin 2) (a b : ℂ) :
    oracle w (symState w a b) = symState w (-a) b := by
  ext z
  rw [oracle, WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply, basisState_apply,
    smul_eq_mul]
  simp only [symState_apply]
  by_cases h : z = w
  · subst h; simp only [if_pos]; ring
  · simp only [if_neg h]; ring

/-- `∑ z, (if z = w then a else b) = a + (N - 1)·b` (split the `z = w` term off the constant `b`). -/
lemma sum_ite_eq_symState (w : Fin n → Fin 2) (a b : ℂ) :
    (∑ z : (Fin n → Fin 2), (if z = w then a else b)) = a + ((2 : ℂ) ^ n - 1) * b := by
  have hsplit : ∀ z : (Fin n → Fin 2),
      (if z = w then a else b) = b + (if z = w then a - b else 0) := by
    intro z; split <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq' Finset.univ w (fun _ => a - b),
    if_pos (Finset.mem_univ w)]
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- `inner ℂ (uniformState) (symState a b) = (√N)⁻¹ · (a + (N - 1)·b)`. -/
lemma inner_uniformState_symState (w : Fin n → Fin 2) (a b : ℂ) :
    inner ℂ (uniformState) (symState w a b)
      = (Real.sqrt (databaseSize n) : ℂ)⁻¹ * (a + ((2 : ℂ) ^ n - 1) * b) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', uniformState_apply, symState_apply]
  rw [Complex.conj_inv, Complex.conj_ofReal, ← Finset.mul_sum, sum_ite_eq_symState]

/-- `(√N)⁻¹ · (√N)⁻¹ = N⁻¹` over `ℂ`, with `N = 2ⁿ`. -/
lemma inv_sqrt_databaseSize_sq :
    (Real.sqrt (databaseSize n) : ℂ)⁻¹ * (Real.sqrt (databaseSize n) : ℂ)⁻¹
      = ((2 : ℂ) ^ n)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by rw [databaseSize]; positivity : (0 : ℝ) ≤ databaseSize n)]
  rw [databaseSize, Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- `2ⁿ ≠ 0` over `ℂ`. -/
lemma two_pow_ne_zero_C : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero

/-- The diffusion (inversion about the mean) acts on the symmetric family by sending both
coefficients to `mean - coefficient`, where `mean = 2·(a + (N-1)·b)/N`. -/
lemma diffusion_symState (w : Fin n → Fin 2) (a b : ℂ) :
    diffusion (symState w a b)
      = symState w (2 * (a + ((2 : ℂ) ^ n - 1) * b) / (2 : ℂ) ^ n - a)
          (2 * (a + ((2 : ℂ) ^ n - 1) * b) / (2 : ℂ) ^ n - b) := by
  have hN : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  ext z
  rw [diffusion, WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul, Pi.smul_apply,
    inner_uniformState_symState, uniformState_apply, smul_eq_mul]
  simp only [symState_apply]
  by_cases h : z = w
  · subst h
    simp only [if_pos]
    rw [show (2 * ((Real.sqrt (databaseSize n) : ℂ)⁻¹ * (a + ((2 : ℂ) ^ n - 1) * b)))
          * (Real.sqrt (databaseSize n) : ℂ)⁻¹
          = 2 * (a + ((2 : ℂ) ^ n - 1) * b)
            * ((Real.sqrt (databaseSize n) : ℂ)⁻¹ * (Real.sqrt (databaseSize n) : ℂ)⁻¹) from by
        ring, inv_sqrt_databaseSize_sq]
    field_simp
  · simp only [if_neg h]
    rw [show (2 * ((Real.sqrt (databaseSize n) : ℂ)⁻¹ * (a + ((2 : ℂ) ^ n - 1) * b)))
          * (Real.sqrt (databaseSize n) : ℂ)⁻¹
          = 2 * (a + ((2 : ℂ) ^ n - 1) * b)
            * ((Real.sqrt (databaseSize n) : ℂ)⁻¹ * (Real.sqrt (databaseSize n) : ℂ)⁻¹) from by
        ring, inv_sqrt_databaseSize_sq]
    field_simp

/-- **One Grover step on the symmetric family** is the linear coefficient map
`(a, b) ↦ ((N-2)/N·a + 2(N-1)/N·b, -2/N·a + (N-2)/N·b)` — a rotation in the `(|w⟩, rest)`
plane. -/
lemma groverStep_symState (w : Fin n → Fin 2) (a b : ℂ) :
    groverStep w (symState w a b)
      = symState w
          (((2 : ℂ) ^ n - 2) / (2 : ℂ) ^ n * a + 2 * ((2 : ℂ) ^ n - 1) / (2 : ℂ) ^ n * b)
          (-2 / (2 : ℂ) ^ n * a + ((2 : ℂ) ^ n - 2) / (2 : ℂ) ^ n * b) := by
  have hN : ((2 : ℂ) ^ n) ≠ 0 := two_pow_ne_zero_C
  rw [groverStep, oracle_symState, diffusion_symState]
  congr 1
  · field_simp; ring
  · field_simp; ring

/-! ## The rotation angle and the closed-form iterate

The Grover step is a rotation by `2θ` in the `(|w⟩, rest)` plane, with `sin θ = 1/√N`. We carry
the angle as a real parameter `θ` constrained by `sin θ = (√N)⁻¹` and `cos θ = √(N-1)/√N`, and
derive the double-angle values `cos 2θ = (N-2)/N`, `sin 2θ = 2√(N-1)/N`. -/

/-- `1 ≤ 2ⁿ` as a real, hence `0 ≤ 2ⁿ - 1`. -/
lemma one_le_two_pow : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
  calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
    _ ≤ (2 : ℝ) ^ n := by apply pow_le_pow_right₀ (by norm_num) (Nat.zero_le n)

/-- For `n ≥ 1`, `2 ≤ 2ⁿ` as a real, hence `1 ≤ 2ⁿ - 1`. -/
lemma two_le_two_pow (hn : 1 ≤ n) : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
  calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
    _ ≤ (2 : ℝ) ^ n := by apply pow_le_pow_right₀ (by norm_num) hn

/-- `√(N-1) · √(N-1) = N - 1` for `n ≥ 1` (so `N - 1 ≥ 0`). -/
lemma sqrt_sub_one_mul_self :
    Real.sqrt ((2 : ℝ) ^ n - 1) * Real.sqrt ((2 : ℝ) ^ n - 1) = (2 : ℝ) ^ n - 1 :=
  Real.mul_self_sqrt (by linarith [one_le_two_pow (n := n)])

/-- `√N · √N = N` (with `N = 2ⁿ ≥ 0`). -/
lemma sqrt_two_pow_mul_self :
    Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ n :=
  Real.mul_self_sqrt (by positivity)

/-- **Double-angle cosine:** `cos 2θ = (N-2)/N`, from `cos 2θ = 1 - 2 sin²θ` and `sin²θ = 1/N`. -/
lemma cos_two_theta {θ : ℝ} (hsin : Real.sin θ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹) :
    Real.cos (2 * θ) = ((2 : ℝ) ^ n - 2) / (2 : ℝ) ^ n := by
  have hN : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  rw [Real.cos_two_mul_eq_one_sub]
  rw [hsin]
  rw [show ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) ^ 2 = ((2 : ℝ) ^ n)⁻¹ from by
    rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]]
  field_simp

/-- **Double-angle sine:** `sin 2θ = 2√(N-1)/N`, from `sin 2θ = 2 sinθ cosθ` and the hypotheses. -/
lemma sin_two_theta {θ : ℝ}
    (hsin : Real.sin θ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n)) :
    Real.sin (2 * θ) = 2 * Real.sqrt ((2 : ℝ) ^ n - 1) / (2 : ℝ) ^ n := by
  have hN : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have hsN : Real.sqrt ((2 : ℝ) ^ n) ≠ 0 := by
    rw [Real.sqrt_ne_zero']; positivity
  rw [Real.sin_two_mul, hsin, hcos]
  have hkey : (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ = ((2 : ℝ) ^ n)⁻¹ := by
    rw [← mul_inv, sqrt_two_pow_mul_self]
  rw [show 2 * (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * (Real.sqrt ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n))
        = 2 * Real.sqrt ((2 : ℝ) ^ n - 1)
          * ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * (Real.sqrt ((2 : ℝ) ^ n))⁻¹)
      from by rw [div_eq_mul_inv]; ring]
  rw [hkey, ← div_eq_mul_inv, mul_div_assoc]

/-- `(N-1)/√(N-1) = √(N-1)`. -/
lemma sub_one_div_sqrt :
    ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n - 1) = Real.sqrt ((2 : ℝ) ^ n - 1) := by
  by_cases h : Real.sqrt ((2 : ℝ) ^ n - 1) = 0
  · rw [h, div_zero]
  · rw [eq_comm, eq_div_iff h, sqrt_sub_one_mul_self (n := n)]

/-- **Marked-amplitude rotation identity (real):**
`(N-2)/N·sin γ + 2(N-1)/N·(cos γ/√(N-1)) = sin(γ + 2θ)`. -/
lemma rot_a {θ : ℝ}
    (hsin : Real.sin θ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n)) (γ : ℝ) :
    ((2 : ℝ) ^ n - 2) / (2 : ℝ) ^ n * Real.sin γ
      + 2 * ((2 : ℝ) ^ n - 1) / (2 : ℝ) ^ n
        * (Real.cos γ / Real.sqrt ((2 : ℝ) ^ n - 1))
      = Real.sin (γ + 2 * θ) := by
  rw [Real.sin_add, cos_two_theta hsin, sin_two_theta hsin hcos]
  have hb : ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n - 1) = Real.sqrt ((2 : ℝ) ^ n - 1) :=
    sub_one_div_sqrt
  rw [show 2 * ((2 : ℝ) ^ n - 1) / (2 : ℝ) ^ n * (Real.cos γ / Real.sqrt ((2 : ℝ) ^ n - 1))
        = Real.cos γ * (2 * (((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n - 1)) / (2 : ℝ) ^ n)
      from by ring, hb]
  ring

/-- **Off-amplitude rotation identity (real):**
`-2/N·sin γ + (N-2)/N·(cos γ/√(N-1)) = cos(γ + 2θ)/√(N-1)`. -/
lemma rot_b (hn : 1 ≤ n) {θ : ℝ}
    (hsin : Real.sin θ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n)) (γ : ℝ) :
    (-2) / (2 : ℝ) ^ n * Real.sin γ
      + ((2 : ℝ) ^ n - 2) / (2 : ℝ) ^ n
        * (Real.cos γ / Real.sqrt ((2 : ℝ) ^ n - 1))
      = Real.cos (γ + 2 * θ) / Real.sqrt ((2 : ℝ) ^ n - 1) := by
  rw [Real.cos_add, cos_two_theta hsin, sin_two_theta hsin hcos]
  by_cases h : Real.sqrt ((2 : ℝ) ^ n - 1) = 0
  · -- then N - 1 = 0, impossible for n ≥ 1
    exfalso
    have : (2 : ℝ) ^ n - 1 = 0 := by
      have := sqrt_sub_one_mul_self (n := n); rw [h] at this; simpa using this.symm
    linarith [two_le_two_pow hn]
  · have hsq : Real.sqrt ((2 : ℝ) ^ n - 1) * Real.sqrt ((2 : ℝ) ^ n - 1) = (2 : ℝ) ^ n - 1 :=
      sqrt_sub_one_mul_self (n := n)
    have hN : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    field_simp
    nlinarith [hsq]

/-! ## The single-step rotation and the closed-form iterate -/

/-- `(2 : ℂ)^n = ↑((2 : ℝ)^n)`. -/
lemma two_pow_C_eq_ofReal : ((2 : ℂ) ^ n) = ((2 : ℝ) ^ n : ℝ) := by
  rw [Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- The angle-parametrized symmetric state `symState w (↑sin γ) (↑(cos γ / √(N-1)))`. -/
noncomputable def rotState (w : Fin n → Fin 2) (γ : ℝ) : QReg n :=
  symState w (Real.sin γ : ℂ) ((Real.cos γ / Real.sqrt ((2 : ℝ) ^ n - 1) : ℝ) : ℂ)

/-- **Single-step rotation lemma:** one Grover step advances the angle by `2θ`. -/
lemma groverStep_rotates (hn : 1 ≤ n) (w : Fin n → Fin 2) {θ : ℝ}
    (hsin : Real.sin θ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n)) (γ : ℝ) :
    groverStep w (rotState w γ) = rotState w (γ + 2 * θ) := by
  rw [rotState, groverStep_symState, rotState]
  have hN : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  congr 1
  · -- marked-item coordinate: matches `sin (γ + 2θ)`
    rw [← rot_a hsin hcos γ, two_pow_C_eq_ofReal]
    push_cast
    ring
  · -- off coordinate: matches `cos (γ + 2θ) / √(N-1)`
    rw [← rot_b hn hsin hcos γ, two_pow_C_eq_ofReal]
    push_cast
    ring

/-- The uniform state is the angle-`θ` rotation state: `uniformState = rotState w θ`. -/
lemma uniformState_eq_rotState (hn : 1 ≤ n) (w : Fin n → Fin 2) {θ : ℝ}
    (hsin : Real.sin θ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n)) :
    uniformState = rotState w θ := by
  rw [uniformState_eq_symState w, rotState]
  have hsN : Real.sqrt ((2 : ℝ) ^ n) ≠ 0 := by rw [Real.sqrt_ne_zero']; positivity
  have hsN1 : Real.sqrt ((2 : ℝ) ^ n - 1) ≠ 0 := by
    rw [Real.sqrt_ne_zero (by linarith [one_le_two_pow (n := n)])]
    linarith [two_le_two_pow hn]
  congr 1
  · rw [databaseSize, ← Complex.ofReal_inv, hsin]
  · -- (√N)⁻¹ = cos θ / √(N-1) = (√(N-1)/√N)/√(N-1) = 1/√N
    rw [databaseSize, ← Complex.ofReal_inv]
    congr 1
    rw [hcos, div_div, eq_div_iff (mul_ne_zero hsN hsN1)]
    rw [show (Real.sqrt ((2:ℝ)^n))⁻¹ * (Real.sqrt ((2:ℝ)^n) * Real.sqrt ((2:ℝ)^n - 1))
          = ((Real.sqrt ((2:ℝ)^n))⁻¹ * Real.sqrt ((2:ℝ)^n)) * Real.sqrt ((2:ℝ)^n - 1) from by ring,
      inv_mul_cancel₀ hsN, one_mul]

/-- **The closed-form iterate:** `k` Grover steps from the uniform state advance the angle to
`(2k+1)·θ`. -/
lemma groverStep_iterate (hn : 1 ≤ n) (w : Fin n → Fin 2) {θ : ℝ}
    (hsin : Real.sin θ = (Real.sqrt ((2 : ℝ) ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt ((2 : ℝ) ^ n - 1) / Real.sqrt ((2 : ℝ) ^ n)) (k : ℕ) :
    (groverStep w)^[k] (rotState w θ) = rotState w ((2 * k + 1) * θ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, groverStep_rotates hn w hsin hcos]
    congr 1
    push_cast
    ring

/-- **Grover success probability (headline):** after `k` Grover steps from the uniform
superposition, the probability of measuring the marked item `w` is `sin²((2k+1)·θ)`, where
`θ` is the Grover rotation half-angle (`sin θ = 1/√N`, `cos θ = √(N-1)/√N`). -/
theorem grover_success {n : ℕ} (hn : 1 ≤ n) (w : Fin n → Fin 2) (k : ℕ) (θ : ℝ)
    (hsin : Real.sin θ = (Real.sqrt (2 ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt (2 ^ n - 1) / Real.sqrt (2 ^ n)) :
    prob ((groverStep w)^[k] uniformState) w = Real.sin ((2 * k + 1) * θ) ^ 2 := by
  rw [uniformState_eq_rotState hn w hsin hcos, groverStep_iterate hn w hsin hcos, prob, rotState,
    symState_apply, if_pos rfl]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

import CsdLean4.Mathlib.QuantumInfo.Fourier
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Shor's algorithm — quantum core (M1: S1 + S2 + S3-core)

**Category:** 3-Local (QM-validity).

Milestone M1 of `specs/shor-plan.md`: the quantum heart of Shor's order-finding algorithm,
the part that needs no number-theory tail. Three pieces, all finite-dimensional QM:

* **S1 — the multiply-by-`a` oracle.** On the genuine work register `EuclideanSpace ℂ (ZMod N)`,
  the modular-exponentiation oracle is the permutation `|y⟩ ↦ |a·y⟩` induced by a unit
  `a : (ZMod N)ˣ` (`mulOracle`, `mulOracle_basisState`). A genuine permutation unitary, not a
  toy cyclic shift on `Fin r`.

* **S2 — eigenstructure of multiply-by-`a`.** With `r = orderOf a` and `ω = exp(2πi/r)`, the
  states `u_s = (1/√r) ∑_{j<r} conj(ω)^{s j} |a^j⟩` are eigenvectors with eigenvalue
  `ω^s = e^{2πi s/r}` (`mulOracle_eigU`), supported on the orbit `{a^j}`, and they reassemble
  `|1⟩ = (1/√r) ∑_{s<r} u_s` (`sum_eigU`). This is the hinge turning order-finding into phase
  estimation: the eigenphases are exactly the multiples of `1/r`.

* **S3 — phase-estimation exactness.** On the counting register `EuclideanSpace ℂ (Fin T)`, the
  inverse QFT inverts the QFT exactly (`applyQFTinv_phaseColumn`), so the phase state carrying
  eigenvalue `ω_T^{j₀}` is read out as `|j₀⟩` with certainty (`phase_estimation_exact`).

* **Bridge S2↔S3.** In the ideal case `r ∣ T`, the eigenphase `ω_r^s = ω_T^{s·(T/r)}`
  (`qftω_div`), so the counting-register phase state carrying eigenvalue `ω_r^s` is exactly the
  QFT column `s·(T/r)`. Inverse-QFT then reads the order's phase off a single eigenvalue branch
  with certainty: `prob = 1` at index `s·(T/r)` (`shor_order_readout`, the M1 headline).

## Honest scope

M1 delivers the genuine oracle (S1), its eigenstructure with eigenvalues `e^{2πi s/r}` and the
`|1⟩ = (1/√r) ∑_s |u_s⟩` decomposition (S2), and ideal-case phase-estimation exactness reading
the order's phase off **a single eigenvalue branch** (S3 + bridge). **Deferred (honest residue):**
the full two-register joint state `(1/√T) ∑_x |x⟩|a^x⟩` and its **uniform-`1/r`** measurement
marginal over `{s·T/r : s < r}`. That needs the product-index joint register
`EuclideanSpace ℂ (Fin T × ZMod N)` and is the next tranche; the uniform distribution over the
order's multiples is **not yet assembled** here. M1 reads a single eigenvalue branch exactly; it
does not yet exhibit the uniform spread that order recovery uses.
-/

open scoped ComplexConjugate
open scoped Matrix
open QuantumInfo

namespace CSD.Empirical.QM.Shor

/-! ## Generic register primitives over a finite index type

The R1 register (`QuantumInfo.basisState`/`prob`) is specialised to bitstrings `Fin n → Fin 2`.
Shor's registers are `ZMod N` (work) and `Fin T` (counting), so we use the same primitives over a
general finite index `ι`, mirroring the R1 API verbatim. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The computational basis state `|x⟩` indexed by an arbitrary finite type. -/
noncomputable def basisState (x : ι) : EuclideanSpace ℂ ι := EuclideanSpace.single x 1

omit [Fintype ι] in
@[simp] lemma basisState_apply (x y : ι) :
    basisState x y = if y = x then 1 else 0 := by
  rw [basisState, PiLp.single_apply]

/-- The Born probability of measuring outcome `z` in state `ψ`: `‖ψ z‖²`. -/
noncomputable def prob (ψ : EuclideanSpace ℂ ι) (z : ι) : ℝ := ‖ψ z‖ ^ 2

omit [Fintype ι] in
/-- A basis state is measured with certainty. -/
@[simp] lemma prob_basisState (x z : ι) :
    prob (basisState x) z = if z = x then 1 else 0 := by
  rw [prob, basisState_apply]
  split <;> simp

/-! ## S1 — the multiply-by-`a` oracle on `EuclideanSpace ℂ (ZMod N)` -/

variable {N : ℕ} [NeZero N]

/-- The **multiply-by-`a` oracle** `|y⟩ ↦ |a·y⟩`: the permutation operator reindexing a register
state by multiplication by the unit `a`. The coordinate at `y` is pulled back from `a⁻¹·y`, so a
basis state `|y⟩` maps to `|a·y⟩`. -/
noncomputable def mulOracle (a : (ZMod N)ˣ) (ψ : EuclideanSpace ℂ (ZMod N)) :
    EuclideanSpace ℂ (ZMod N) :=
  (WithLp.equiv 2 (ZMod N → ℂ)).symm (fun y => ψ (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * y))

omit [NeZero N] in
@[simp] lemma mulOracle_apply (a : (ZMod N)ˣ) (ψ : EuclideanSpace ℂ (ZMod N)) (y : ZMod N) :
    mulOracle a ψ y = ψ (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * y) := rfl

/-- Coordinatewise: a finite sum of register states evaluates as the sum of coordinates. -/
lemma sum_coord {ι : Type*} [Fintype ι] {κ : Type*} (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) (y : ι) :
    (∑ k ∈ s, f k) y = ∑ k ∈ s, (f k) y := by
  have h : (∑ k ∈ s, f k).ofLp = ∑ k ∈ s, (f k).ofLp :=
    map_sum (WithLp.addEquiv 2 (ι → ℂ)) f s
  calc (∑ k ∈ s, f k) y = (∑ k ∈ s, f k).ofLp y := rfl
    _ = (∑ k ∈ s, (f k).ofLp) y := by rw [h]
    _ = ∑ k ∈ s, (f k) y := by rw [Finset.sum_apply]

omit [NeZero N] in
/-- **The oracle is linear in the state.** -/
lemma mulOracle_smul (a : (ZMod N)ˣ) (c : ℂ) (ψ : EuclideanSpace ℂ (ZMod N)) :
    mulOracle a (c • ψ) = c • mulOracle a ψ := by
  ext y
  rw [mulOracle_apply, WithLp.ofLp_smul, Pi.smul_apply, WithLp.ofLp_smul, Pi.smul_apply,
    mulOracle_apply]

/-- **The oracle commutes with finite sums.** -/
lemma mulOracle_sum {κ : Type*} (a : (ZMod N)ˣ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ (ZMod N)) :
    mulOracle a (∑ k ∈ s, f k) = ∑ k ∈ s, mulOracle a (f k) := by
  ext y
  rw [mulOracle_apply, sum_coord, sum_coord]
  exact Finset.sum_congr rfl fun k _ => by rw [mulOracle_apply]

omit [NeZero N] in
/-- **S1 key fact:** the oracle sends the basis state `|y⟩` to `|a·y⟩`. -/
@[simp] lemma mulOracle_basisState (a : (ZMod N)ˣ) (y : ZMod N) :
    mulOracle a (basisState y) = basisState ((a : ZMod N) * y) := by
  ext z
  rw [mulOracle_apply, basisState_apply, basisState_apply]
  by_cases h : z = (a : ZMod N) * y
  · subst h
    rw [if_pos rfl, if_pos]
    rw [← mul_assoc, Units.inv_mul, one_mul]
  · rw [if_neg h, if_neg]
    intro hc
    apply h
    rw [← hc, ← mul_assoc, Units.mul_inv, one_mul]

/-! ## S2 — eigenstructure of the multiply-by-`a` oracle -/

variable (a : (ZMod N)ˣ)

/-- The order `r = orderOf a` of the unit `a` in `(ZMod N)ˣ`. -/
noncomputable def ord : ℕ := orderOf a

lemma ord_pos : 0 < ord a := orderOf_pos a

/-- The primitive `r`-th root `ω = exp(2πi/r)`, `r = orderOf a`. -/
noncomputable def omega : ℂ := qftω (ord a)

/-- The orbit map `j ↦ a^j` (as an element of `ZMod N`) along the cyclic orbit of `a`. -/
noncomputable def orbit (j : Fin (ord a)) : ZMod N := ((a ^ (j : ℕ) : (ZMod N)ˣ) : ZMod N)

/-- `Fin (ord a)` is nonempty as an additive group: `ord a > 0`. -/
instance instNeZeroOrd : NeZero (ord a) := ⟨(ord_pos a).ne'⟩

lemma orbit_zero : orbit a ⟨0, ord_pos a⟩ = (1 : ZMod N) := by
  simp [orbit]

/-- The cyclic shift `j ↦ j + 1` on `Fin (ord a)` as a self-equivalence. -/
noncomputable def cycShift : Fin (ord a) ≃ Fin (ord a) := Equiv.addRight (1 : Fin (ord a))

lemma cycShift_apply (j : Fin (ord a)) : cycShift a j = j + 1 := rfl

/-- The shifted index value, modulo the order. -/
lemma cycShift_val (j : Fin (ord a)) : ((cycShift a j : Fin (ord a)) : ℕ) = ((j : ℕ) + 1) % ord a := by
  rw [cycShift_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- A root-of-unity reduction: with `z^r = 1`, the power `z^{s·m}` depends only on `m mod r`. -/
private lemma pow_mul_mod_eq {z : ℂ} {r : ℕ} (hz : z ^ r = 1) (s m : ℕ) :
    z ^ (s * m) = z ^ (s * (m % r)) := by
  conv_lhs => rw [show m = r * (m / r) + m % r from (Nat.div_add_mod m r).symm]
  rw [Nat.mul_add, pow_add, Nat.mul_left_comm s r (m / r), pow_mul, hz, one_pow, one_mul]

omit [NeZero N] in
/-- A unit-power reduction: with `a^r = 1` (`r = ord a`), `a^m = a^{m mod r}`. -/
private lemma units_pow_mod (m : ℕ) : (a ^ m : (ZMod N)ˣ) = (a ^ (m % ord a) : (ZMod N)ˣ) := by
  conv_lhs => rw [show m = ord a * (m / ord a) + m % ord a from (Nat.div_add_mod m (ord a)).symm]
  rw [pow_add, pow_mul, show (a ^ ord a : (ZMod N)ˣ) = 1 from pow_orderOf_eq_one a,
    one_pow, one_mul]

/-- Multiplication by `a` shifts the orbit index by one (cyclically): `a · (a^j) = a^{j+1 mod r}`. -/
lemma mul_orbit (j : Fin (ord a)) :
    (a : ZMod N) * orbit a j = orbit a (cycShift a j) := by
  have key : (a : ZMod N) * orbit a j = ((a ^ ((j : ℕ) + 1) : (ZMod N)ˣ) : ZMod N) := by
    rw [orbit, ← Units.val_mul, pow_succ]
    congr 1
    rw [mul_comm]
  rw [key, orbit, cycShift_val, units_pow_mod a ((j : ℕ) + 1)]

/-- The **eigenvector** `u_s = (1/√r) ∑_{j<r} conj(ω)^{s j} |a^j⟩`, supported on the orbit. -/
noncomputable def eigU (s : Fin (ord a)) : EuclideanSpace ℂ (ZMod N) :=
  (Real.sqrt (ord a) : ℂ)⁻¹ •
    ∑ j : Fin (ord a), (conj (omega a) ^ ((s : ℕ) * (j : ℕ))) • basisState (orbit a j)

/-- **S2 eigenvector lemma:** `mulOracle a (u_s) = ω^s · u_s`, with `ω = exp(2πi/r)`. The oracle
shifts the orbit index by one; reindexing by the cyclic shift and using `conj ω = ω⁻¹`,
`ω^r = 1`, each summand picks up the common phase `ω^s`. -/
theorem mulOracle_eigU (s : Fin (ord a)) :
    mulOracle a (eigU a s) = omega a ^ (s : ℕ) • eigU a s := by
  have hωr : omega a ^ ord a = 1 := by rw [omega]; exact qftω_pow_N (ord a)
  have hcωr : conj (omega a) ^ ord a = 1 := by rw [← map_pow, hωr, map_one]
  have hcω : conj (omega a) = (omega a)⁻¹ := by rw [omega]; exact qftω_conj (ord a)
  have hωne : omega a ≠ 0 := by rw [omega]; exact qftω_ne_zero (ord a)
  -- the orbit-phase identity used per summand after the index shift:
  -- `conj ω^{s·j} = ω^s · conj ω^{s·(j+1 mod r)}`
  have hphase : ∀ j : Fin (ord a),
      conj (omega a) ^ ((s : ℕ) * (j : ℕ))
        = omega a ^ (s : ℕ) * conj (omega a) ^ ((s : ℕ) * ((cycShift a j : Fin (ord a)) : ℕ)) := by
    intro j
    -- the shifted exponent `s · (cycShift j).val` equals `s·j + s` modulo the order's period
    have hexp : conj (omega a) ^ ((s : ℕ) * ((cycShift a j : Fin (ord a)) : ℕ))
        = conj (omega a) ^ ((s : ℕ) * (j : ℕ)) * conj (omega a) ^ (s : ℕ) := by
      rw [cycShift_val, ← pow_mul_mod_eq hcωr s ((j : ℕ) + 1)]
      rw [show (s : ℕ) * ((j : ℕ) + 1) = (s : ℕ) * (j : ℕ) + (s : ℕ) from by ring, pow_add]
    -- `ω^s · conj ω^s = 1`
    have hcancel : omega a ^ (s : ℕ) * conj (omega a) ^ (s : ℕ) = 1 := by
      rw [← mul_pow, hcω, mul_inv_cancel₀ hωne, one_pow]
    rw [hexp, show omega a ^ (s : ℕ) * (conj (omega a) ^ ((s : ℕ) * (j : ℕ)) * conj (omega a) ^ (s : ℕ))
          = conj (omega a) ^ ((s : ℕ) * (j : ℕ)) * (omega a ^ (s : ℕ) * conj (omega a) ^ (s : ℕ))
        from by ring, hcancel, mul_one]
  -- push the oracle through the sum, reindex by the cyclic shift, apply the phase identity
  simp only [eigU]
  rw [mulOracle_smul, mulOracle_sum]
  rw [smul_comm (omega a ^ (s : ℕ)) (Real.sqrt (ord a) : ℂ)⁻¹]
  congr 1
  rw [Finset.smul_sum]
  -- LHS summand: oracle of `conj ω^{sj} • |a^j⟩` = `conj ω^{sj} • |orbit (cycShift j)⟩`
  have hLHS : ∀ j : Fin (ord a),
      mulOracle a (conj (omega a) ^ ((s : ℕ) * (j : ℕ)) • basisState (orbit a j))
        = conj (omega a) ^ ((s : ℕ) * (j : ℕ)) • basisState (orbit a (cycShift a j)) := by
    intro j
    rw [mulOracle_smul, mulOracle_basisState, mul_orbit]
  simp_rw [hLHS]
  -- reindex the sum by the bijection `cycShift`
  rw [← Equiv.sum_comp (cycShift a)
        (fun k => omega a ^ (s : ℕ) • conj (omega a) ^ ((s : ℕ) * (k : ℕ)) • basisState (orbit a k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← hphase j]

/-- A geometric-series collapse: for the primitive root `ω` and `j < r`,
`∑_{s<r} conj(ω)^{s·j} = r` if `j = 0` and `0` otherwise. (Roots-of-unity orthogonality, the
same collapse as in `Fourier.qft_unitary`.) -/
private lemma sum_pow_orbit_phase (j : Fin (ord a)) :
    (∑ s : Fin (ord a), conj (omega a) ^ ((s : ℕ) * (j : ℕ)))
      = if j = ⟨0, ord_pos a⟩ then (ord a : ℂ) else 0 := by
  have hr : 0 < ord a := ord_pos a
  set ζ : ℂ := conj (omega a) ^ (j : ℕ) with hζdef
  have hsum : (∑ s : Fin (ord a), conj (omega a) ^ ((s : ℕ) * (j : ℕ)))
      = ∑ i ∈ Finset.range (ord a), ζ ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ζ ^ i) (ord a)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hζdef, ← pow_mul, Nat.mul_comm]
  rw [hsum]
  by_cases hj : j = ⟨0, ord_pos a⟩
  · -- `j = 0`: `ζ = 1`, the sum is `r`
    have hζ1 : ζ = 1 := by rw [hζdef, hj]; simp
    rw [hζ1, if_pos hj]
    simp
  · -- `j ≠ 0`: `ζ ≠ 1` is an `r`-th root of unity, geometric sum vanishes
    have hζN : ζ ^ ord a = 1 := by
      rw [hζdef, ← pow_mul, mul_comm, pow_mul]
      rw [show conj (omega a) ^ ord a = 1 by rw [← map_pow, omega, qftω_pow_N, map_one]]
      rw [one_pow]
    have hζne : ζ ≠ 1 := by
      intro hζ1
      -- ζ = conj ω^{j} = ω⁻^{j}; ζ = 1 ⟹ ω^j = 1 ⟹ j = 0 by primitivity
      have hcω : conj (omega a) = (omega a)⁻¹ := by rw [omega]; exact qftω_conj (ord a)
      rw [hζdef, hcω, inv_pow] at hζ1
      have hω : omega a ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (by rw [omega]; exact qftω_ne_zero (ord a))
      have hωj : omega a ^ (j : ℕ) = 1 := by
        rw [inv_eq_one] at hζ1; exact hζ1
      have hprim : IsPrimitiveRoot (omega a) (ord a) := by rw [omega]; exact qftω_primitive (ord a)
      have := hprim.pow_inj j.isLt (ord_pos a) (by rw [hωj, pow_zero])
      exact hj (Fin.ext this)
    rw [geom_sum_eq hζne (ord a), hζN, sub_self, zero_div, if_neg hj]

/-- **S2 decomposition lemma:** `(1/√r) ∑_{s<r} u_s = |1⟩`. Summing the eigenvectors collapses the
phase sum by roots-of-unity orthogonality to the single orbit term `|a^0⟩ = |1⟩`. -/
theorem sum_eigU :
    (Real.sqrt (ord a) : ℂ)⁻¹ • ∑ s : Fin (ord a), eigU a s = basisState (1 : ZMod N) := by
  have hr : 0 < ord a := ord_pos a
  have hrne : (ord a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set c : ℂ := (Real.sqrt (ord a) : ℂ)⁻¹ with hc
  -- expand the double sum, swap order, collapse the inner phase sum
  have hexpand : c • ∑ s : Fin (ord a), eigU a s
      = (c * c) •
          ∑ j : Fin (ord a),
            (∑ s : Fin (ord a), conj (omega a) ^ ((s : ℕ) * (j : ℕ))) • basisState (orbit a j) := by
    -- factor `c` out of `∑_s eigU s`
    have hfac : (∑ s : Fin (ord a), eigU a s)
        = c • ∑ s : Fin (ord a),
            ∑ j : Fin (ord a), conj (omega a) ^ ((s : ℕ) * (j : ℕ)) • basisState (orbit a j) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun s _ => rfl
    rw [hfac, smul_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
  rw [hexpand]
  simp_rw [sum_pow_orbit_phase a, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (⟨0, ord_pos a⟩ : Fin (ord a))
        (fun j => (ord a : ℂ) • basisState (orbit a j)), if_pos (Finset.mem_univ _)]
  rw [orbit_zero, smul_smul, hc, inv_sqrtN_sq, inv_mul_cancel₀ hrne, one_smul]

/-! ## S3 — phase estimation exactness on the counting register `EuclideanSpace ℂ (Fin T)` -/

variable (T : ℕ) [NeZero T]

/-- The QFT action on the counting register. -/
noncomputable def applyQFT (ψ : EuclideanSpace ℂ (Fin T)) : EuclideanSpace ℂ (Fin T) :=
  Matrix.toEuclideanLin (qftMatrix T) ψ

/-- The inverse-QFT action on the counting register (`Fᴴ`). -/
noncomputable def applyQFTinv (ψ : EuclideanSpace ℂ (Fin T)) : EuclideanSpace ℂ (Fin T) :=
  Matrix.toEuclideanLin (qftMatrix T)ᴴ ψ

omit [NeZero T] in
lemma applyQFT_apply (ψ : EuclideanSpace ℂ (Fin T)) (y : Fin T) :
    applyQFT T ψ y = ∑ x, qftMatrix T y x * ψ x := by
  rw [applyQFT, Matrix.toLpLin_apply]
  rfl

/-- The QFT column `j₀`: the phase state `(1/√T) ∑_x ω_T^{x j₀} |x⟩`. -/
noncomputable def phaseColumn (j₀ : Fin T) : EuclideanSpace ℂ (Fin T) :=
  applyQFT T (basisState j₀)

omit [NeZero T] in
@[simp] lemma phaseColumn_apply (j₀ x : Fin T) :
    phaseColumn T j₀ x = (Real.sqrt T : ℂ)⁻¹ * qftω T ^ ((x : ℕ) * (j₀ : ℕ)) := by
  rw [phaseColumn, applyQFT_apply, Finset.sum_eq_single j₀]
  · rw [basisState_apply, if_pos rfl, mul_one, qftMatrix_apply]
  · intro b _ hb; rw [basisState_apply, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Phase-estimation exactness:** the inverse QFT inverts the QFT, so the QFT column `j₀` is
sent back to the basis state `|j₀⟩`. -/
theorem applyQFTinv_phaseColumn (j₀ : Fin T) :
    applyQFTinv T (phaseColumn T j₀) = basisState j₀ := by
  rw [phaseColumn, applyQFT, applyQFTinv]
  rw [show Matrix.toEuclideanLin (qftMatrix T)ᴴ (Matrix.toEuclideanLin (qftMatrix T) (basisState j₀))
        = Matrix.toEuclideanLin ((qftMatrix T)ᴴ * qftMatrix T) (basisState j₀) from by
      rw [Matrix.toLpLin_mul_same]; rfl]
  rw [qft_unitary, Matrix.toLpLin_one]
  rfl

/-- **S3 capstone:** phase estimation reads the QFT column `j₀` with certainty. -/
theorem phase_estimation_exact (j₀ : Fin T) :
    prob (applyQFTinv T (phaseColumn T j₀)) j₀ = 1 := by
  rw [applyQFTinv_phaseColumn, prob_basisState, if_pos rfl]

/-! ## Bridge S2 ↔ S3 — the eigenphase reads out the order

In the ideal case `r ∣ T` the eigenphase `ω_r^s` of `mulOracle a` is a `T`-th root: precisely
`ω_T^{s·(T/r)}`. So the counting-register phase state carrying eigenvalue `ω_r^s` is the QFT
column `s·(T/r)`, and inverse-QFT reads the order's phase off it with certainty. -/

/-- `ω_r = ω_T^{T/r}` when `r ∣ T` (`r, T > 0`): both equal `exp(2πi/r)`. -/
lemma qftω_div {r T : ℕ} (hr : 0 < r) (hT : 0 < T) (hdvd : r ∣ T) :
    qftω r = qftω T ^ (T / r) := by
  have hrne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hTne : (T : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hqpos : 0 < T / r := Nat.div_pos (Nat.le_of_dvd hT hdvd) hr
  have hqne : ((T / r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
  have hdvdC : (r : ℂ) * ((T / r : ℕ) : ℂ) = (T : ℂ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  rw [qftω, qftω, ← Complex.exp_nat_mul]
  congr 1
  -- `(T/r) · (2πi/T) = 2πi/r`, using `r · (T/r) = T`
  rw [← hdvdC]
  field_simp

/-- The bridge index `s·(T/r)`, valid `< T` when `s < r`, `r ∣ T`, and `T > 0`. -/
lemma bridgeIndex_lt {r T : ℕ} (hr : 0 < r) (hT : 0 < T) (hdvd : r ∣ T) (s : Fin r) :
    (s : ℕ) * (T / r) < T := by
  obtain ⟨q, hq⟩ := hdvd
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0; simp at hq; omega
    · exact hq0
  subst hq
  rw [Nat.mul_div_cancel_left q hr]
  exact Nat.mul_lt_mul_right hqpos |>.mpr s.isLt

omit [NeZero T] in
/-- **Bridge:** the counting-register phase state carrying eigenvalue `ω_r^s` is exactly the QFT
column `s·(T/r)`. -/
lemma eigenPhase_eq_phaseColumn {r : ℕ} (hr : 0 < r) (hT : 0 < T) (hdvd : r ∣ T) (s : Fin r) :
    (Real.sqrt T : ℂ)⁻¹ • ∑ x : Fin T, (qftω r ^ ((s : ℕ) * (x : ℕ))) • basisState x
      = phaseColumn T ⟨(s : ℕ) * (T / r), bridgeIndex_lt hr hT hdvd s⟩ := by
  ext y
  rw [phaseColumn_apply]
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sum_coord]
  rw [Finset.sum_eq_single y]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, basisState_apply, if_pos rfl, smul_eq_mul, mul_one]
    -- `ω_r^{s y} = ω_T^{y · (s · T/r)}`
    rw [qftω_div hr hT hdvd]
    rw [← pow_mul]
    congr 2
    ring
  · intro x _ hx
    rw [WithLp.ofLp_smul, Pi.smul_apply, basisState_apply, if_neg (fun h => hx h.symm),
      smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **M1 headline (`shor_order_readout`):** in the ideal case `r ∣ T`, inverse-QFT of the
counting-register phase state carrying eigenvalue `ω_r^s` yields the basis state `s·(T/r)` with
certainty. This is phase estimation reading the order's phase `s/r` exactly. -/
theorem shor_order_readout {r : ℕ} (hr : 0 < r) (hT : 0 < T) (hdvd : r ∣ T) (s : Fin r) :
    prob (applyQFTinv T
        ((Real.sqrt T : ℂ)⁻¹ • ∑ x : Fin T, (qftω r ^ ((s : ℕ) * (x : ℕ))) • basisState x))
      ⟨(s : ℕ) * (T / r), bridgeIndex_lt hr hT hdvd s⟩ = 1 := by
  rw [eigenPhase_eq_phaseColumn T hr hT hdvd s]
  exact phase_estimation_exact T _

end CSD.Empirical.QM.Shor

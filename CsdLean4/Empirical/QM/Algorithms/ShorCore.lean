import CsdLean4.Mathlib.QuantumInfo.Fourier
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Shor's algorithm — quantum core (M1 + M1.5: S1 + S2 + S3, ideal case `r ∣ T`)

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

## M1.5 — the joint two-register state and the full ideal-case output distribution

M1.5 assembles the genuine two-register joint state on `EuclideanSpace ℂ (Fin T × ZMod N)` and
proves the full ideal-case (`r ∣ T`) order-finding measurement distribution:

* **Joint register.** `tensorCN φ ψ` (coordinate `φ c * ψ y`) and the counting-register inverse
  QFT `qftInvCount` (acting on the `Fin T` index only), with the key reduction
  `qftInvCount_tensorCN : qftInvCount (tensorCN φ ψ) = tensorCN (applyQFTinv T φ) ψ`. The genuine
  Born marginal on the counting register is `probCount Φ c = ∑_y ‖Φ (c, y)‖²`.
* **The faithful state.** `jointModexp a` is the modular-exponentiation oracle `|x⟩|y⟩ ↦ |x⟩|a^x·y⟩`
  (a genuine permutation), and `jointModexp_initial` proves it sends the prepared
  `uniformCount ⊗ |1⟩` to `postModexpState = (1/√T) ∑_x |x⟩|a^x⟩`. So `postModexpState` IS the
  modexp output, not a posited form.
* **Eigenbasis expansion.** `basisState_apow_eq` (roots-of-unity inversion, dual to `sum_eigU`)
  rewrites `|a^x⟩` in the `eigU` eigenbasis; `postModexp_eq_eigenbasis` then expands the joint
  state as `(1/√r) ∑_s (phase column s·T/r) ⊗ u_s`, and `qftInvCount_postModexp` applies the
  inverse QFT to read each branch as `|s·T/r⟩ ⊗ u_s`.
* **HEADLINE `shor_order_distribution`:** for `r ∣ T`, measuring the counting register gives
  `probCount = 1/r` on each `s·(T/r)` (`s < r`), via `eigU_norm` (`‖u_s‖ = 1`) and the index
  injectivity `bridgeIndex_inj`; `shor_order_distribution_zero` gives `0` off the `r` multiples.
  This is the **uniform-`1/r`** marginal M1 flagged as deferred.

## Honest scope

M1 + M1.5 deliver the genuine oracle (S1), its eigenstructure with eigenvalues `e^{2πi s/r}` and
the `|1⟩ = (1/√r) ∑_s |u_s⟩` decomposition (S2), and the **full ideal-case (`r ∣ T`) order-finding
output distribution** (S3): on the genuine two-register modexp state, the counting-register
measurement is uniform `1/r` on the `r` multiples `{s·T/r : s < r}` and `0` elsewhere. **What
remains for full Shor:** the general `r ∤ T` case (Dirichlet-kernel `≥ 4/π²` bound, S4),
continued-fraction recovery of `r` (Legendre converse, S5), and the classical reduction
(nontrivial-sqrt-of-unity factor S6 + random-`a` success bound S7). All per `specs/shor-plan.md`;
S4 is the next open quantum piece.
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

/-! ## M1.5 — the joint two-register state and the ideal-case output distribution

The product-index joint register `EuclideanSpace ℂ (Fin T × ZMod N)`, the modular-exponentiation
oracle `|x⟩|y⟩ ↦ |x⟩|a^x·y⟩`, and the full ideal-case (`r ∣ T`) measurement distribution. -/

/-! ### The joint register `EuclideanSpace ℂ (Fin T × ZMod N)` -/

/-- The **tensor product** of a counting-register state and a work-register state, as a vector on
the product index: coordinate `(tensorCN φ ψ) (c, y) = φ c * ψ y`. -/
noncomputable def tensorCN (φ : EuclideanSpace ℂ (Fin T)) (ψ : EuclideanSpace ℂ (ZMod N)) :
    EuclideanSpace ℂ (Fin T × ZMod N) :=
  (WithLp.equiv 2 (Fin T × ZMod N → ℂ)).symm (fun p => φ p.1 * ψ p.2)

omit [NeZero T] in
set_option linter.unusedSectionVars false in
@[simp] lemma tensorCN_apply (φ : EuclideanSpace ℂ (Fin T)) (ψ : EuclideanSpace ℂ (ZMod N))
    (c : Fin T) (y : ZMod N) : tensorCN T φ ψ (c, y) = φ c * ψ y := rfl

omit [NeZero T] in
/-- The tensor is linear in the counting factor. -/
lemma tensorCN_smul_left (k : ℂ) (φ : EuclideanSpace ℂ (Fin T)) (ψ : EuclideanSpace ℂ (ZMod N)) :
    tensorCN T (k • φ) ψ = k • tensorCN T φ ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_smul, Pi.smul_apply, tensorCN_apply, tensorCN_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

omit [NeZero T] in
/-- The tensor commutes with finite sums in the counting factor. -/
lemma tensorCN_sum_left {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ (Fin T))
    (ψ : EuclideanSpace ℂ (ZMod N)) :
    tensorCN T (∑ k ∈ s, f k) ψ = ∑ k ∈ s, tensorCN T (f k) ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [tensorCN_apply, sum_coord, sum_coord, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [tensorCN_apply]

omit [NeZero T] in
/-- The tensor is linear in the work factor. -/
lemma tensorCN_smul_right (k : ℂ) (φ : EuclideanSpace ℂ (Fin T)) (ψ : EuclideanSpace ℂ (ZMod N)) :
    tensorCN T φ (k • ψ) = k • tensorCN T φ ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_smul, Pi.smul_apply, tensorCN_apply, tensorCN_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

omit [NeZero T] in
/-- The tensor commutes with finite sums in the work factor. -/
lemma tensorCN_sum_right {κ : Type*} (φ : EuclideanSpace ℂ (Fin T)) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ (ZMod N)) :
    tensorCN T φ (∑ k ∈ s, f k) = ∑ k ∈ s, tensorCN T φ (f k) := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [tensorCN_apply, sum_coord, sum_coord, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [tensorCN_apply]

omit [NeZero T] in
/-- On basis states the tensor is the joint basis state: `|c⟩ ⊗ |y⟩ = |(c, y)⟩`. -/
@[simp] lemma tensorCN_basis (c : Fin T) (y : ZMod N) :
    tensorCN T (basisState c) (basisState y) = basisState (c, y) := by
  ext p
  obtain ⟨c', y'⟩ := p
  rw [tensorCN_apply, basisState_apply, basisState_apply, basisState_apply]
  by_cases hc : c' = c <;> by_cases hy : y' = y <;>
    simp [hc, hy, Prod.ext_iff]

/-- The **inverse QFT on the counting register only**: coordinate
`(qftInvCount Φ) (c, y) = ∑_x (qftMatrix T)ᴴ c x · Φ (x, y)`. -/
noncomputable def qftInvCount (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) :
    EuclideanSpace ℂ (Fin T × ZMod N) :=
  (WithLp.equiv 2 (Fin T × ZMod N → ℂ)).symm
    (fun p => ∑ x : Fin T, (qftMatrix T)ᴴ p.1 x * Φ (x, p.2))

omit [NeZero T] in
set_option linter.unusedSectionVars false in
@[simp] lemma qftInvCount_apply (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) (c : Fin T) (y : ZMod N) :
    qftInvCount T Φ (c, y) = ∑ x : Fin T, (qftMatrix T)ᴴ c x * Φ (x, y) := rfl

omit [NeZero T] in
/-- The partial inverse QFT is linear. -/
lemma qftInvCount_smul (k : ℂ) (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) :
    qftInvCount T (k • Φ) = k • qftInvCount T Φ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_smul, Pi.smul_apply, qftInvCount_apply, qftInvCount_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

omit [NeZero T] in
/-- The partial inverse QFT commutes with finite sums. -/
lemma qftInvCount_sum {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ (Fin T × ZMod N)) :
    qftInvCount T (∑ k ∈ s, f k) = ∑ k ∈ s, qftInvCount T (f k) := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [qftInvCount_apply, sum_coord]
  simp_rw [sum_coord, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [qftInvCount_apply]

set_option linter.unusedSectionVars false in
/-- **Key reduction:** the partial inverse QFT commutes with the tensor and reduces to M1's
`applyQFTinv` on the counting factor. -/
lemma qftInvCount_tensorCN (φ : EuclideanSpace ℂ (Fin T)) (ψ : EuclideanSpace ℂ (ZMod N)) :
    qftInvCount T (tensorCN T φ ψ) = tensorCN T (applyQFTinv T φ) ψ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [qftInvCount_apply, tensorCN_apply]
  have happ : applyQFTinv T φ c = ∑ x, (qftMatrix T)ᴴ c x * φ x := by
    rw [applyQFTinv, Matrix.toLpLin_apply]; rfl
  rw [happ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [tensorCN_apply, mul_assoc]

/-- The **Born marginal on the counting register**: `probCount Φ c = ∑_y ‖Φ (c, y)‖²`. -/
noncomputable def probCount (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) (c : Fin T) : ℝ :=
  ∑ y : ZMod N, ‖Φ (c, y)‖ ^ 2

/-! ### The faithful modular-exponentiation state -/

/-- The **modular-exponentiation oracle** `|x⟩|y⟩ ↦ |x⟩|a^x·y⟩` on the joint register, the
genuine permutation reindexing the work register by multiplication by `a^x`. -/
noncomputable def jointModexp (a : (ZMod N)ˣ) (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) :
    EuclideanSpace ℂ (Fin T × ZMod N) :=
  (WithLp.equiv 2 (Fin T × ZMod N → ℂ)).symm
    (fun p => Φ (p.1, (((a ^ (p.1 : ℕ))⁻¹ : (ZMod N)ˣ) : ZMod N) * p.2))

omit [NeZero N] [NeZero T] in
@[simp] lemma jointModexp_apply (a : (ZMod N)ˣ) (Φ : EuclideanSpace ℂ (Fin T × ZMod N))
    (c : Fin T) (y : ZMod N) :
    jointModexp T a Φ (c, y) = Φ (c, (((a ^ (c : ℕ))⁻¹ : (ZMod N)ˣ) : ZMod N) * y) := rfl

omit [NeZero N] [NeZero T] in
/-- **The oracle sends the joint basis state `|x⟩|y⟩` to `|x⟩|a^x·y⟩`.** -/
@[simp] lemma jointModexp_basis (a : (ZMod N)ˣ) (x : Fin T) (y : ZMod N) :
    jointModexp T a (basisState (x, y)) = basisState (x, ((a ^ (x : ℕ) : (ZMod N)ˣ) : ZMod N) * y) := by
  ext p
  obtain ⟨c, z⟩ := p
  rw [jointModexp_apply, basisState_apply, basisState_apply]
  -- the two membership conditions are equivalent: c = x ∧ (a^c)⁻¹·z = y ⟺ c = x ∧ z = a^c·y
  have hiff : ((c, (((a ^ (c : ℕ))⁻¹ : (ZMod N)ˣ) : ZMod N) * z) = (x, y))
      ↔ ((c, z) = (x, ((a ^ (x : ℕ) : (ZMod N)ˣ) : ZMod N) * y)) := by
    rw [Prod.mk.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hcx, hzy⟩
      refine ⟨hcx, ?_⟩
      subst hcx
      rw [← hzy, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · rintro ⟨hcx, hzy⟩
      refine ⟨hcx, ?_⟩
      subst hcx
      rw [hzy, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  by_cases h : (c, z) = (x, ((a ^ (x : ℕ) : (ZMod N)ˣ) : ZMod N) * y)
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]

omit [NeZero T] in
set_option linter.unusedSectionVars false in
/-- The oracle is linear in the state. -/
lemma jointModexp_smul (a : (ZMod N)ˣ) (k : ℂ) (Φ : EuclideanSpace ℂ (Fin T × ZMod N)) :
    jointModexp T a (k • Φ) = k • jointModexp T a Φ := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [WithLp.ofLp_smul, Pi.smul_apply, jointModexp_apply, jointModexp_apply, WithLp.ofLp_smul,
    Pi.smul_apply]

omit [NeZero T] in
/-- The oracle commutes with finite sums. -/
lemma jointModexp_sum {κ : Type*} (a : (ZMod N)ˣ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ (Fin T × ZMod N)) :
    jointModexp T a (∑ k ∈ s, f k) = ∑ k ∈ s, jointModexp T a (f k) := by
  ext p
  obtain ⟨c, y⟩ := p
  rw [jointModexp_apply, sum_coord, sum_coord]
  exact Finset.sum_congr rfl fun k _ => by rw [jointModexp_apply]

/-- The **uniform counting register** `(1/√T) ∑_x |x⟩`. -/
noncomputable def uniformCount : EuclideanSpace ℂ (Fin T) :=
  (Real.sqrt T : ℂ)⁻¹ • ∑ x : Fin T, basisState x

/-- The **prepared initial state** `uniformCount ⊗ |1⟩`. -/
noncomputable def initialState : EuclideanSpace ℂ (Fin T × ZMod N) :=
  tensorCN T (uniformCount T) (basisState (1 : ZMod N))

/-- The **post-modexp state** `(1/√T) ∑_x |x⟩|a^x⟩`: the genuine output of the oracle on the
prepared input. -/
noncomputable def postModexpState (a : (ZMod N)ˣ) : EuclideanSpace ℂ (Fin T × ZMod N) :=
  (Real.sqrt T : ℂ)⁻¹ • ∑ x : Fin T, basisState (x, ((a ^ (x : ℕ) : (ZMod N)ˣ) : ZMod N))

set_option linter.unusedSectionVars false in
/-- **Faithfulness link:** the oracle on the prepared input `uniformCount ⊗ |1⟩` produces exactly
`postModexpState = (1/√T) ∑_x |x⟩|a^x⟩`. -/
theorem jointModexp_initial (a : (ZMod N)ˣ) :
    jointModexp T a (initialState T) = postModexpState T a := by
  rw [initialState, uniformCount, tensorCN_smul_left, tensorCN_sum_left,
    jointModexp_smul, jointModexp_sum, postModexpState]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tensorCN_basis, jointModexp_basis, mul_one]

/-! ### Two eigenstructure facts -/

omit [NeZero N] in
/-- **The orbit map `j ↦ a^j` is injective on `Fin (ord a)`** (distinct powers below the order). -/
lemma orbit_injective : Function.Injective (orbit a) := by
  intro i j hij
  have hpow : (a ^ (i : ℕ) : (ZMod N)ˣ) = (a ^ (j : ℕ) : (ZMod N)ˣ) := Units.ext hij
  exact Fin.ext (pow_injOn_Iio_orderOf i.isLt j.isLt hpow)

/-- **`‖u_s‖ = 1`:** the eigenvector is a unit vector. The orbit basis states are orthonormal
(`orbit_injective`), each phase coefficient is unimodular, and `‖(√r)⁻¹‖² · r = 1`. -/
theorem eigU_norm (s : Fin (ord a)) : ‖eigU a s‖ = 1 := by
  have hr : 0 < ord a := ord_pos a
  have hrne : (ord a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  -- coordinate of eigU at a point y
  have hcoord : ∀ y : ZMod N, eigU a s y
      = (Real.sqrt (ord a) : ℂ)⁻¹ *
          ∑ j : Fin (ord a), conj (omega a) ^ ((s : ℕ) * (j : ℕ)) * (if y = orbit a j then 1 else 0) := by
    intro y
    rw [eigU, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sum_coord]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [WithLp.ofLp_smul, Pi.smul_apply, basisState_apply, smul_eq_mul]
  -- the squared norm via the coordinate sum
  rw [← Real.sqrt_one]
  rw [EuclideanSpace.norm_eq]
  congr 1
  -- ∑_y ‖eigU y‖² = ∑_y (1/r) · ‖∑_j c_j [y = orbit j]‖² ; only the orbit image contributes
  have hsummand : ∀ y : ZMod N, ‖eigU a s y‖ ^ 2
      = (ord a : ℝ)⁻¹ *
          ‖∑ j : Fin (ord a), conj (omega a) ^ ((s : ℕ) * (j : ℕ)) * (if y = orbit a j then 1 else 0)‖ ^ 2 := by
    intro y
    rw [hcoord y, norm_mul, mul_pow]
    congr 1
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      ← Real.sqrt_inv]
    rw [Real.sq_sqrt (by positivity)]
  simp_rw [hsummand]
  rw [← Finset.mul_sum]
  -- the inner sum, over j, picks at most one j per y (orbit injective); switch to a sum over j
  have hinner : ∀ y : ZMod N,
      ‖∑ j : Fin (ord a), conj (omega a) ^ ((s : ℕ) * (j : ℕ)) * (if y = orbit a j then 1 else 0)‖ ^ 2
        = if ∃ j : Fin (ord a), y = orbit a j then 1 else 0 := by
    intro y
    by_cases hy : ∃ j : Fin (ord a), y = orbit a j
    · obtain ⟨j0, hj0⟩ := hy
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hj0, mul_one, if_pos ⟨j0, hj0⟩]
        have hω1 : ‖omega a‖ = 1 := by
          rw [omega]; exact (qftω_primitive (ord a)).norm'_eq_one hr.ne'
        rw [norm_pow, Complex.norm_conj, hω1, one_pow, one_pow]
      · intro b _ hb
        rw [if_neg (fun h => hb (orbit_injective a (hj0.symm.trans h)).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hy]
      rw [Finset.sum_eq_zero, norm_zero]; · simp
      intro j _
      rw [if_neg (fun h => hy ⟨j, h⟩), mul_zero]
  simp_rw [hinner]
  -- ∑_y [∃j, y = orbit j] = r  (orbit injective)
  have hcount : (∑ y : ZMod N, if ∃ j : Fin (ord a), y = orbit a j then (1 : ℝ) else 0)
      = (ord a : ℝ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    have hfilt : (Finset.univ.filter fun y => ∃ j : Fin (ord a), y = orbit a j)
        = Finset.image (orbit a) Finset.univ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun ⟨j, hj⟩ => ⟨j, hj.symm⟩, fun ⟨j, hj⟩ => ⟨j, hj.symm⟩⟩
    rw [hfilt, Finset.card_image_of_injective _ (orbit_injective a), Finset.card_univ,
      Fintype.card_fin]
  rw [hcount, inv_mul_cancel₀ hrne]

/-! ### The eigenbasis expansion of the post-modexp state -/

/-- **Roots-of-unity inversion (dual to `sum_eigU`):** for any `x : ℕ`,
`|a^x⟩ = (1/√r) ∑_s ω^{s·x} u_s`. The inner phase sum `∑_s ω^{s(x-j)}` collapses by orthogonality
to the single orbit term `a^{x mod r} = a^x`. -/
theorem basisState_apow_eq (x : ℕ) :
    basisState ((a ^ x : (ZMod N)ˣ) : ZMod N)
      = (Real.sqrt (ord a) : ℂ)⁻¹ • ∑ s : Fin (ord a), (omega a ^ ((s : ℕ) * x)) • eigU a s := by
  have hr : 0 < ord a := ord_pos a
  have hrne : (ord a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set c : ℂ := (Real.sqrt (ord a) : ℂ)⁻¹ with hc
  -- expand the double sum, swap order, collapse the inner phase sum over s
  have hexpand : c • ∑ s : Fin (ord a), (omega a ^ ((s : ℕ) * x)) • eigU a s
      = (c * c) •
          ∑ j : Fin (ord a),
            (∑ s : Fin (ord a),
              omega a ^ ((s : ℕ) * x) * conj (omega a) ^ ((s : ℕ) * (j : ℕ))) • basisState (orbit a j) := by
    have hfac : (∑ s : Fin (ord a), (omega a ^ ((s : ℕ) * x)) • eigU a s)
        = c • ∑ s : Fin (ord a),
            ∑ j : Fin (ord a),
              (omega a ^ ((s : ℕ) * x) * conj (omega a) ^ ((s : ℕ) * (j : ℕ))) • basisState (orbit a j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [eigU, smul_comm (omega a ^ ((s : ℕ) * x)) c, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul (omega a ^ ((s : ℕ) * x)) (conj (omega a) ^ ((s : ℕ) * (j : ℕ)))]
    rw [hfac, smul_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
  rw [hexpand]
  -- the inner sum over s collapses: ∑_s ω^{sx} conj(ω)^{sj} = ∑_s ω^{s(x-j mod ...)} = r·[j ≡ x mod r]
  have hcollapse : ∀ j : Fin (ord a),
      (∑ s : Fin (ord a), omega a ^ ((s : ℕ) * x) * conj (omega a) ^ ((s : ℕ) * (j : ℕ)))
        = if (a ^ (j : ℕ) : (ZMod N)ˣ) = (a ^ x : (ZMod N)ˣ) then (ord a : ℂ) else 0 := by
    intro j
    have hcω : conj (omega a) = (omega a)⁻¹ := by rw [omega]; exact qftω_conj (ord a)
    have hωne : omega a ≠ 0 := by rw [omega]; exact qftω_ne_zero (ord a)
    -- rewrite each summand as ζ^s with ζ = ω^x · conj(ω)^j
    set ζ : ℂ := omega a ^ x * conj (omega a) ^ (j : ℕ) with hζdef
    have hsum : (∑ s : Fin (ord a), omega a ^ ((s : ℕ) * x) * conj (omega a) ^ ((s : ℕ) * (j : ℕ)))
        = ∑ i ∈ Finset.range (ord a), ζ ^ i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ζ ^ i) (ord a)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hζdef, mul_pow, ← pow_mul, ← pow_mul, mul_comm x (s : ℕ), mul_comm (j : ℕ) (s : ℕ)]
    rw [hsum]
    by_cases hj : (a ^ (j : ℕ) : (ZMod N)ˣ) = (a ^ x : (ZMod N)ˣ)
    · -- j ≡ x mod r, so ζ = 1, sum = r
      have hmod : (j : ℕ) ≡ x [MOD ord a] := by
        have := (pow_eq_pow_iff_modEq (x := a)).mp hj
        rwa [← ord] at this
      have hζ1 : ζ = 1 := by
        rw [hζdef, hcω, inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hωne)]
        -- ω^x = ω^j since x ≡ j mod r and ω^r = 1
        have hωr : omega a ^ ord a = 1 := by rw [omega]; exact qftω_pow_N (ord a)
        have := pow_mul_mod_eq hωr 1 x
        have hjm := pow_mul_mod_eq hωr 1 (j : ℕ)
        rw [one_mul, one_mul] at this hjm
        rw [this, hjm]
        congr 1
        exact (Nat.ModEq.symm hmod)
      rw [hζ1, if_pos hj]
      simp
    · -- j ≢ x mod r, ζ ≠ 1 is an r-th root of unity, geometric sum vanishes
      have hζN : ζ ^ ord a = 1 := by
        rw [hζdef, mul_pow, ← pow_mul, ← pow_mul, mul_comm x (ord a), mul_comm (j : ℕ) (ord a),
          pow_mul, pow_mul]
        rw [show omega a ^ ord a = 1 by rw [omega]; exact qftω_pow_N (ord a)]
        rw [show conj (omega a) ^ ord a = 1 by rw [← map_pow, omega, qftω_pow_N, map_one]]
        rw [one_pow, one_pow, mul_one]
      have hζne : ζ ≠ 1 := by
        intro hζ1
        apply hj
        rw [hζdef, hcω, inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hωne)] at hζ1
        -- ω^x = ω^j ⟹ ω^{x mod r} = ω^{j mod r} ⟹ x mod r = j mod r ⟹ a^j = a^x
        have hωr : omega a ^ ord a = 1 := by rw [omega]; exact qftω_pow_N (ord a)
        have hprim : IsPrimitiveRoot (omega a) (ord a) := by rw [omega]; exact qftω_primitive (ord a)
        have hxm := pow_mul_mod_eq hωr 1 x
        have hjm := pow_mul_mod_eq hωr 1 (j : ℕ)
        rw [one_mul, one_mul] at hxm hjm
        have hmodeq : omega a ^ (x % ord a) = omega a ^ ((j : ℕ) % ord a) := by
          rw [← hxm, ← hjm]; exact hζ1
        have hxj : x % ord a = (j : ℕ) % ord a :=
          hprim.pow_inj (Nat.mod_lt _ hr) (Nat.mod_lt _ hr) hmodeq
        rw [pow_eq_pow_iff_modEq, ← ord]
        exact hxj.symm
      rw [geom_sum_eq hζne (ord a), hζN, sub_self, zero_div, if_neg hj]
  simp_rw [hcollapse]
  -- only the single index j₀ = x % r with a^{j₀} = a^x survives
  set j₀ : Fin (ord a) := ⟨x % ord a, Nat.mod_lt _ hr⟩ with hj₀def
  have hcond : (a ^ (j₀ : ℕ) : (ZMod N)ˣ) = (a ^ x : (ZMod N)ˣ) := by
    rw [pow_eq_pow_iff_modEq, ← ord, hj₀def]
    show (x % ord a) ≡ x [MOD ord a]
    exact Nat.mod_modEq x (ord a)
  have hsumcollapse : (∑ j : Fin (ord a),
        (if (a ^ (j : ℕ) : (ZMod N)ˣ) = (a ^ x : (ZMod N)ˣ) then (ord a : ℂ) else 0)
          • basisState (orbit a j))
      = (ord a : ℂ) • basisState (orbit a j₀) := by
    rw [Finset.sum_eq_single j₀]
    · rw [if_pos hcond]
    · intro j _ hj
      rw [if_neg, zero_smul]
      intro hcontra
      apply hj
      apply Fin.ext
      rw [pow_eq_pow_iff_modEq, ← ord] at hcontra
      have hmm : (j : ℕ) % ord a = x % ord a := hcontra
      rw [Nat.mod_eq_of_lt j.isLt] at hmm
      rw [hmm, hj₀def]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsumcollapse]
  -- the orbit at x % r equals a^x; combine the scalars c·c·r = 1
  have horb : orbit a j₀ = ((a ^ x : (ZMod N)ˣ) : ZMod N) := by
    rw [hj₀def, orbit, units_pow_mod a x]
  rw [horb, smul_smul, hc, inv_sqrtN_sq, inv_mul_cancel₀ hrne, one_smul]

set_option linter.unusedSectionVars false in
/-- The eigenphase counting state `(1/√T) ∑_x ω_r^{s x} |x⟩` equals the QFT column `s·(T/r)`,
re-stated with the M1 `omega a = qftω r` notation. -/
private lemma eigenPhase_eq_phaseColumn' {r : ℕ} (hr : 0 < r) (hT : 0 < T) (hdvd : r ∣ T)
    (s : Fin r) :
    (Real.sqrt T : ℂ)⁻¹ • ∑ x : Fin T, (qftω r ^ ((x : ℕ) * (s : ℕ))) • basisState x
      = phaseColumn T ⟨(s : ℕ) * (T / r), bridgeIndex_lt hr hT hdvd s⟩ := by
  rw [← eigenPhase_eq_phaseColumn T hr hT hdvd s]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.mul_comm (x : ℕ) (s : ℕ)]

/-- **Eigenbasis expansion of the post-modexp state:** in the ideal case `r ∣ T`,
`postModexpState = (1/√r) ∑_s (phase column s·T/r) ⊗ u_s`. -/
theorem postModexp_eq_eigenbasis (hr : 0 < ord a) (hT : 0 < T) (hdvd : ord a ∣ T) :
    postModexpState T a
      = (Real.sqrt (ord a) : ℂ)⁻¹ • ∑ s : Fin (ord a),
          tensorCN T (phaseColumn T ⟨(s : ℕ) * (T / ord a), bridgeIndex_lt hr hT hdvd s⟩)
            (eigU a s) := by
  rw [postModexpState]
  -- |x⟩|a^x⟩ = |x⟩ ⊗ |a^x⟩
  have hbasis : ∀ x : Fin T, basisState (x, ((a ^ (x : ℕ) : (ZMod N)ˣ) : ZMod N))
      = tensorCN T (basisState x) (basisState ((a ^ (x : ℕ) : (ZMod N)ˣ) : ZMod N)) := fun x => by
    rw [tensorCN_basis]
  simp_rw [hbasis]
  -- substitute basisState_apow_eq into the work factor
  simp_rw [basisState_apow_eq a]
  -- pull the (1/√r) scalar out of each tensor's work factor
  simp_rw [show ∀ (x : Fin T),
      tensorCN T (basisState x)
          ((Real.sqrt (ord a) : ℂ)⁻¹ • ∑ s : Fin (ord a), (omega a ^ ((s : ℕ) * (x : ℕ))) • eigU a s)
        = (Real.sqrt (ord a) : ℂ)⁻¹ • ∑ s : Fin (ord a),
            tensorCN T (basisState x) ((omega a ^ ((s : ℕ) * (x : ℕ))) • eigU a s)
      from fun x => by rw [tensorCN_smul_right, tensorCN_sum_right]]
  -- factor the outer (1/√T) and the inner (1/√r) into (1/√T)·(1/√r) and distribute into ∑_s
  rw [Finset.smul_sum]
  simp_rw [smul_smul, Finset.smul_sum]
  -- swap the x and s sums
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  -- factor u_s out: |x⟩ ⊗ (ω^{sx} • u_s) = ω^{sx} • (|x⟩ ⊗ u_s); collect into the phase column
  have hstep : ∀ x : Fin T,
      ((Real.sqrt T : ℂ)⁻¹ * (Real.sqrt (ord a) : ℂ)⁻¹)
          • tensorCN T (basisState x) ((omega a ^ ((s : ℕ) * (x : ℕ))) • eigU a s)
        = (Real.sqrt (ord a) : ℂ)⁻¹ •
            ((Real.sqrt T : ℂ)⁻¹ • (omega a ^ ((s : ℕ) * (x : ℕ))))
              • tensorCN T (basisState x) (eigU a s) := by
    intro x
    rw [tensorCN_smul_right, smul_smul, smul_smul, smul_eq_mul]
    congr 1
    ring
  simp_rw [hstep]
  rw [← Finset.smul_sum]
  congr 1
  -- ∑_x (1/√T · ω^{sx}) • (|x⟩ ⊗ u_s) = (phase column) ⊗ u_s
  simp_rw [← tensorCN_smul_left]
  rw [← tensorCN_sum_left]
  congr 1
  -- ∑_x (1/√T)·ω_r^{sx} • |x⟩ = phase column s·T/r
  rw [← eigenPhase_eq_phaseColumn' T hr hT hdvd s, omega, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, smul_eq_mul, Nat.mul_comm (s : ℕ) (x : ℕ)]

/-! ### Apply inverse-QFT and read the distribution -/

/-- **Inverse-QFT of the post-modexp state:** `qftInvCount postModexpState =
(1/√r) ∑_s |s·T/r⟩ ⊗ u_s`. The partial inverse QFT reduces each phase column to a basis state. -/
theorem qftInvCount_postModexp (hr : 0 < ord a) (hT : 0 < T) (hdvd : ord a ∣ T) :
    qftInvCount T (postModexpState T a)
      = (Real.sqrt (ord a) : ℂ)⁻¹ • ∑ s : Fin (ord a),
          tensorCN T (basisState ⟨(s : ℕ) * (T / ord a), bridgeIndex_lt hr hT hdvd s⟩) (eigU a s) := by
  rw [postModexp_eq_eigenbasis a T hr hT hdvd, qftInvCount_smul, qftInvCount_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [qftInvCount_tensorCN, applyQFTinv_phaseColumn]

omit [NeZero T] in
/-- **Index injectivity:** `s ↦ s·(T/r)` is injective on `Fin r` when `r ∣ T`, `r > 0`. -/
lemma bridgeIndex_inj {r : ℕ} (hr : 0 < r) (hT : 0 < T) (hdvd : r ∣ T) :
    Function.Injective (fun s : Fin r => (⟨(s : ℕ) * (T / r), bridgeIndex_lt hr hT hdvd s⟩ : Fin T)) := by
  intro s s' hss
  have hq : 0 < T / r := Nat.div_pos (Nat.le_of_dvd hT hdvd) hr
  have : (s : ℕ) * (T / r) = (s' : ℕ) * (T / r) := Fin.val_eq_of_eq hss
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hq this)

/-- **HEADLINE — the ideal-case order-finding distribution.** For `r ∣ T`, measuring the counting
register of the inverse-QFT'd modexp state gives `prob = 1/r` on each multiple `s·(T/r)`. This is
the **uniform-`1/r`** spread over the order's multiples that order recovery uses. -/
theorem shor_order_distribution (hr : 0 < ord a) (hT : 0 < T) (hdvd : ord a ∣ T) (s : Fin (ord a)) :
    probCount T (qftInvCount T (postModexpState T a))
        ⟨(s : ℕ) * (T / ord a), bridgeIndex_lt hr hT hdvd s⟩ = (ord a : ℝ)⁻¹ := by
  rw [qftInvCount_postModexp a T hr hT hdvd, probCount]
  -- coordinate at (s·T/r, y): only the s'=s branch survives by bridgeIndex_inj
  have hcoord : ∀ y : ZMod N,
      ((Real.sqrt (ord a) : ℂ)⁻¹ • ∑ s' : Fin (ord a),
          tensorCN T (basisState ⟨(s' : ℕ) * (T / ord a), bridgeIndex_lt hr hT hdvd s'⟩) (eigU a s'))
        (⟨(s : ℕ) * (T / ord a), bridgeIndex_lt hr hT hdvd s⟩, y)
      = (Real.sqrt (ord a) : ℂ)⁻¹ * eigU a s y := by
    intro y
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sum_coord]
    congr 1
    rw [Finset.sum_eq_single s]
    · rw [tensorCN_apply, basisState_apply, if_pos rfl, one_mul]
    · intro s' _ hs'
      rw [tensorCN_apply, basisState_apply, if_neg, zero_mul]
      intro heq
      exact hs' (bridgeIndex_inj T hr hT hdvd heq.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hcoord]
  -- ∑_y ‖(1/√r) (u_s)_y‖² = (1/r) ∑_y ‖(u_s)_y‖² = (1/r)·‖u_s‖² = 1/r
  have hnorm : ∀ y : ZMod N, ‖(Real.sqrt (ord a) : ℂ)⁻¹ * eigU a s y‖ ^ 2
      = (ord a : ℝ)⁻¹ * ‖eigU a s y‖ ^ 2 := by
    intro y
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_inv,
      Real.sq_sqrt (by positivity)]
  simp_rw [hnorm]
  rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, eigU_norm, one_pow, mul_one]

/-- **Complement:** off the `r` multiples `{s·(T/r)}`, the counting-register probability is `0`. -/
theorem shor_order_distribution_zero (hr : 0 < ord a) (hT : 0 < T) (hdvd : ord a ∣ T) (c : Fin T)
    (hc : ∀ s : Fin (ord a), (c : ℕ) ≠ (s : ℕ) * (T / ord a)) :
    probCount T (qftInvCount T (postModexpState T a)) c = 0 := by
  rw [qftInvCount_postModexp a T hr hT hdvd, probCount]
  rw [Finset.sum_eq_zero]
  intro y _
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sum_coord]
  have hzero : (∑ s : Fin (ord a),
      (tensorCN T (basisState ⟨(s : ℕ) * (T / ord a), bridgeIndex_lt hr hT hdvd s⟩) (eigU a s)) (c, y)) = 0 := by
    rw [Finset.sum_eq_zero]
    intro s _
    rw [tensorCN_apply, basisState_apply, if_neg, zero_mul]
    intro heq
    exact hc s (Fin.val_eq_of_eq heq)
  rw [hzero, mul_zero, norm_zero]
  norm_num

end CSD.Empirical.QM.Shor

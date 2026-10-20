/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.AdiabaticComparison

/-!
# The Born–Fock statement for states

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #163 (out of ~~#88~~, the sentence Kato's adiabatic theorem is named for).

Along a gapped `C²` path `Γ` with eigenprojector `P` and physical propagator `U_T` at speed `T`
(`U' = −iT·H U` on `[0, 1]`), **a state started in the instantaneous eigenspace stays in it up
to `O(1/T)`, uniformly in `s ∈ [0, 1]`**: for `ψ₀ ∈ range (P 0)`,

  `‖(1 − P s) (U_T s ψ₀)‖ ≤ (C / T) · ‖ψ₀‖`.

The two inputs are #161 (`U_A s ψ₀ ∈ range (P s)` *exactly*, the adiabatic propagator intertwines
the eigenprojections) and #162 (`‖U_T s − U_A s‖ ≤ C / T`): `(1 − P s) U_T ψ₀ = (1 − P s)(U_T − U_A) ψ₀`
and `‖1 − P s‖ ≤ 1`. Vectors are points of `EuclideanSpace ℂ (Fin N)` and a matrix acts through
`Matrix.toEuclideanCLM`, so the operator norm of a matrix (`L2Operator` scope) is exactly the
norm of its action.

* `Matrix.norm_le_one_of_conjTranspose_mul_self_eq` — a Hermitian idempotent has operator norm
  `≤ 1` (the C*-identity);
* `Matrix.norm_toEuclideanCLM_apply_le`, `norm_toEuclideanCLM_apply_of_conjTranspose_mul_self` —
  `‖A ψ‖ ≤ ‖A‖ ‖ψ‖`, and a unitary preserves the norm of a vector;
* `Matrix.norm_toEuclideanCLM_apply_sub_le` — `‖ψ‖ − ‖(1 − Q) ψ‖ ≤ ‖Q ψ‖`;
* `GappedPath.norm_proj_le`, `norm_one_sub_proj_le` — `‖P s‖ ≤ 1`, `‖1 − P s‖ ≤ 1`;
* `GappedPath.mem_range_proj_iff` — `ψ ∈ range (P s) ↔ P s ψ = ψ`;
* `GappedPath.proj_toEuclideanCLM_apply_of_eq` — an eigenvector of `H s` for `lam s` is fixed by `P s`;
* `GappedPath.IsPhysPropagator.norm_toEuclideanCLM_apply` — `‖U_T s ψ‖ = ‖ψ‖`;
* ★ `GappedPath.IsAdPropagator.toEuclideanCLM_apply_mem_range`,
  `one_sub_proj_toEuclideanCLM_apply` — **`U_A s ψ₀ ∈ range (P s)` exactly**, i.e.
  `(1 − P s) (U_A s ψ₀) = 0`, for `ψ₀ ∈ range (P 0)`;
* ★★ `GappedPath.exists_norm_toEuclideanCLM_sub_le` — **`U_T s ψ₀ = U_A s ψ₀ + O(1/T)`**:
  `‖U_T s ψ − U_A s ψ‖ ≤ (C / T) ‖ψ‖` for every vector `ψ`;
* ★★★ `GappedPath.exists_norm_one_sub_proj_le` — **the Born–Fock statement**:
  `‖(1 − P s) (U_T s ψ₀)‖ ≤ (C / T) ‖ψ₀‖` for `ψ₀ ∈ range (P 0)`, uniformly on `[0, 1]`;
* ★★ `GappedPath.exists_norm_proj_le` — the survival form `‖ψ₀‖ − (C / T) ‖ψ₀‖ ≤ ‖P s (U_T s ψ₀)‖`.

## Honest scope

* The hypotheses are #162's: the path is `C²`, the branch is an eigenvalue at every `s`, the gap
  is uniform. `C` is #162's constant (compactness, not a formula — BACKLOG #166).
* "Probability" statements are the squares of these norm statements for `‖ψ₀‖ = 1`
  (`‖(1 − P s) U_T ψ₀‖² ≤ (C/T)²` is the transition probability out of the branch); they are not
  restated.
* Finite dimensions, `L2Operator` norm scope, the action of a matrix is `Matrix.toEuclideanCLM`.

References: M. Born and V. Fock, "Beweis des Adiabatensatzes", Z. Phys. 51 (1928); T. Kato, "On
the adiabatic theorem of quantum mechanics", J. Phys. Soc. Japan 5 (1950), §3; S. Teufel,
*Adiabatic Perturbation Theory in Quantum Dynamics*, Thm 2.2; `AdiabaticComparison.lean` (#162),
`AdiabaticPropagators.lean` (#161); `specs/BACKLOG.md` #163, ~~#88~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix ContDiff Topology
open Matrix Metric Set Complex Real Filter

namespace Matrix

variable {N : ℕ}

/-- A Hermitian idempotent (`Qᴴ Q = Q`) has operator norm `≤ 1`: the C*-identity gives
`‖Q‖² = ‖Qᴴ Q‖ = ‖Q‖`. -/
theorem norm_le_one_of_conjTranspose_mul_self_eq {Q : Matrix (Fin N) (Fin N) ℂ}
    (hQ : Qᴴ * Q = Q) : ‖Q‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self Q
  rw [hQ] at h
  by_cases h0 : ‖Q‖ = 0
  · rw [h0]; exact zero_le_one
  · have h1 : ‖Q‖ * 1 = ‖Q‖ * ‖Q‖ := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ h0 h1).ge

/-- `‖A ψ‖ ≤ ‖A‖ ‖ψ‖`: the `L2Operator` norm of a matrix bounds its action on Euclidean space. -/
theorem norm_toEuclideanCLM_apply_le (A : Matrix (Fin N) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) : ‖toEuclideanCLM (𝕜 := ℂ) A x‖ ≤ ‖A‖ * ‖x‖ := by
  rw [← l2_opNorm_toEuclideanCLM]
  exact (toEuclideanCLM (𝕜 := ℂ) A).le_opNorm x

/-- A unitary matrix preserves the norm of a vector. -/
theorem norm_toEuclideanCLM_apply_of_conjTranspose_mul_self {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : Uᴴ * U = 1) (x : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanCLM (𝕜 := ℂ) U x‖ = ‖x‖ := by
  have hUn : ‖U‖ ≤ 1 := norm_le_one_of_conjTranspose_mul_self hU
  have hUHn : ‖Uᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact hUn
  refine le_antisymm ((norm_toEuclideanCLM_apply_le U x).trans ?_) ?_
  · calc ‖U‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  · have hx : x = toEuclideanCLM (𝕜 := ℂ) Uᴴ (toEuclideanCLM (𝕜 := ℂ) U x) := by
      rw [← mul_apply_eq_comp, ← map_mul, hU, map_one, one_apply_eq_self]
    calc ‖x‖ = ‖toEuclideanCLM (𝕜 := ℂ) Uᴴ (toEuclideanCLM (𝕜 := ℂ) U x)‖ := by rw [← hx]
      _ ≤ ‖Uᴴ‖ * ‖toEuclideanCLM (𝕜 := ℂ) U x‖ := norm_toEuclideanCLM_apply_le _ _
      _ ≤ 1 * ‖toEuclideanCLM (𝕜 := ℂ) U x‖ := by gcongr
      _ = ‖toEuclideanCLM (𝕜 := ℂ) U x‖ := one_mul _

/-- `‖ψ‖ − ‖(1 − Q) ψ‖ ≤ ‖Q ψ‖`: the triangle inequality for `ψ = Q ψ + (1 − Q) ψ`. -/
theorem norm_toEuclideanCLM_apply_sub_le (Q : Matrix (Fin N) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    ‖x‖ - ‖toEuclideanCLM (𝕜 := ℂ) (1 - Q) x‖ ≤ ‖toEuclideanCLM (𝕜 := ℂ) Q x‖ := by
  have hx : x = toEuclideanCLM (𝕜 := ℂ) Q x + toEuclideanCLM (𝕜 := ℂ) (1 - Q) x := by
    rw [← _root_.add_apply, ← map_add, add_sub_cancel, map_one,
      one_apply_eq_self]
  have := norm_add_le (toEuclideanCLM (𝕜 := ℂ) Q x) (toEuclideanCLM (𝕜 := ℂ) (1 - Q) x)
  rw [← hx] at this
  linarith

end Matrix

namespace Matrix.GappedPath

variable {N : ℕ} (Γ : GappedPath N)

/-- `‖P s‖ ≤ 1`. -/
theorem norm_proj_le (s : ℝ) : ‖Γ.proj s‖ ≤ 1 :=
  norm_le_one_of_conjTranspose_mul_self_eq (by rw [(Γ.proj_isHermitian s).eq, Γ.proj_mul_self])

/-- `‖1 − P s‖ ≤ 1`. -/
theorem norm_one_sub_proj_le (s : ℝ) : ‖1 - Γ.proj s‖ ≤ 1 :=
  norm_le_one_of_conjTranspose_mul_self_eq (by
    rw [conjTranspose_sub, conjTranspose_one, (Γ.proj_isHermitian s).eq, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Γ.proj_mul_self, sub_self, sub_zero])

/-- `ψ ∈ range (P s) ↔ P s ψ = ψ` (the projector is idempotent). -/
theorem mem_range_proj_iff (s : ℝ) (x : EuclideanSpace ℂ (Fin N)) :
    x ∈ Set.range (toEuclideanCLM (𝕜 := ℂ) (Γ.proj s)) ↔
      toEuclideanCLM (𝕜 := ℂ) (Γ.proj s) x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← mul_apply_eq_comp, ← map_mul, Γ.proj_mul_self]
  · intro h
    exact ⟨x, h⟩

/-- An eigenvector of `H s` for the branch eigenvalue lies in `range (P s)`:
`H s v = lam s • v → P s v = v` (through `X (λ − H) = 1 − P`, the reduced resolvent of #162). -/
theorem proj_toEuclideanCLM_apply_of_eq (s : ℝ) {v : EuclideanSpace ℂ (Fin N)}
    (hv : toEuclideanCLM (𝕜 := ℂ) (Γ.H s) v = (Γ.lam s : ℂ) • v) :
    toEuclideanCLM (𝕜 := ℂ) (Γ.proj s) v = v := by
  have h : toEuclideanCLM (𝕜 := ℂ) (1 - Γ.proj s) v = 0 := by
    rw [← Γ.redRes_mul_smul_one_sub_H, map_mul, mul_apply_eq_comp, map_sub, map_smul, map_one,
      _root_.sub_apply, _root_.smul_apply, one_apply_eq_self, hv, sub_self, map_zero]
  rw [map_sub, map_one, _root_.sub_apply, one_apply_eq_self] at h
  exact (sub_eq_zero.1 h).symm

namespace IsPhysPropagator

variable {Γ} {T : ℝ} {U : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- The physical propagator preserves the norm of a state: `‖U_T s ψ‖ = ‖ψ‖` on `[0, 1]`. -/
theorem norm_toEuclideanCLM_apply (hU : Γ.IsPhysPropagator T U) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (x : EuclideanSpace ℂ (Fin N)) : ‖toEuclideanCLM (𝕜 := ℂ) (U s) x‖ = ‖x‖ :=
  norm_toEuclideanCLM_apply_of_conjTranspose_mul_self (hU.conjTranspose_mul_self s hs) x

end IsPhysPropagator

namespace IsAdPropagator

variable {Γ} {T : ℝ} {U : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- ★ **The adiabatic propagator keeps a state in the instantaneous eigenspace exactly**:
`P s (U_A s ψ₀) = U_A s ψ₀` for `P 0 ψ₀ = ψ₀`, on `[0, 1]`. -/
theorem proj_toEuclideanCLM_apply (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : EuclideanSpace ℂ (Fin N)}
    (hx : toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0) x = x) :
    toEuclideanCLM (𝕜 := ℂ) (Γ.proj s) (toEuclideanCLM (𝕜 := ℂ) (U s) x)
      = toEuclideanCLM (𝕜 := ℂ) (U s) x := by
  rw [← mul_apply_eq_comp, ← map_mul, ← hU.mul_proj_zero hn hH s hs, map_mul,
    mul_apply_eq_comp, hx]

/-- `U_A s ψ₀ ∈ range (P s)` for `ψ₀ ∈ range (P 0)`. -/
theorem toEuclideanCLM_apply_mem_range (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : EuclideanSpace ℂ (Fin N)}
    (hx : x ∈ Set.range (toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0))) :
    toEuclideanCLM (𝕜 := ℂ) (U s) x ∈ Set.range (toEuclideanCLM (𝕜 := ℂ) (Γ.proj s)) :=
  (Γ.mem_range_proj_iff s _).2
    (hU.proj_toEuclideanCLM_apply hn hH hs ((Γ.mem_range_proj_iff 0 x).1 hx))

/-- `(1 − P s) (U_A s ψ₀) = 0` for `P 0 ψ₀ = ψ₀`. -/
theorem one_sub_proj_toEuclideanCLM_apply (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : EuclideanSpace ℂ (Fin N)}
    (hx : toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0) x = x) :
    toEuclideanCLM (𝕜 := ℂ) (1 - Γ.proj s) (toEuclideanCLM (𝕜 := ℂ) (U s) x) = 0 := by
  rw [map_sub, map_one, _root_.sub_apply, one_apply_eq_self,
    hU.proj_toEuclideanCLM_apply hn hH hs hx, sub_self]

end IsAdPropagator

/-! ### The Born–Fock statement -/

/-- ★★ **`U_T s ψ = U_A s ψ + O(1/T)`**: Kato's comparison on vectors,
`‖U_T s ψ − U_A s ψ‖ ≤ (C / T) ‖ψ‖` for every `ψ`, uniformly on `[0, 1]`. -/
theorem exists_norm_toEuclideanCLM_sub_le {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ UT UA : ℝ → Matrix (Fin N) (Fin N) ℂ,
      Γ.IsPhysPropagator T UT → Γ.IsAdPropagator T UA →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : EuclideanSpace ℂ (Fin N),
        ‖toEuclideanCLM (𝕜 := ℂ) (UT s) x - toEuclideanCLM (𝕜 := ℂ) (UA s) x‖ ≤ C / T * ‖x‖ := by
  obtain ⟨C, hC0, hC⟩ := Γ.exists_norm_sub_le hn hH hex
  refine ⟨C, hC0, fun T hT UT UA hUT hUA s hs x => ?_⟩
  rw [← _root_.sub_apply, ← map_sub]
  exact (norm_toEuclideanCLM_apply_le _ x).trans
    (mul_le_mul_of_nonneg_right (hC T hT UT UA hUT hUA s hs) (norm_nonneg x))

/-- ★★★ **The Born–Fock statement.** Along a gapped `C²` path whose branch is an eigenvalue,
there is a constant `C` such that for every speed `T > 0`, every physical propagator `U_T`, every
`s ∈ [0, 1]` and every state `ψ₀` in the initial eigenspace (`P 0 ψ₀ = ψ₀`),

  `‖(1 − P s) (U_T s ψ₀)‖ ≤ (C / T) ‖ψ₀‖`:

**the solution started in the instantaneous eigenspace stays in it up to `O(1/T)`, uniformly.**
(`C` is #162's constant.) -/
theorem exists_norm_one_sub_proj_le {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ UT : ℝ → Matrix (Fin N) (Fin N) ℂ,
      Γ.IsPhysPropagator T UT → ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : EuclideanSpace ℂ (Fin N),
        toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0) x = x →
        ‖toEuclideanCLM (𝕜 := ℂ) (1 - Γ.proj s) (toEuclideanCLM (𝕜 := ℂ) (UT s) x)‖
          ≤ C / T * ‖x‖ := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  obtain ⟨C, hC0, hC⟩ := Γ.exists_norm_toEuclideanCLM_sub_le hn hH hex
  refine ⟨C, hC0, fun T hT UT hUT s hs x hx => ?_⟩
  obtain ⟨UA, hUA⟩ := Γ.exists_isAdPropagator hn1 hH T
  have h0 := hUA.one_sub_proj_toEuclideanCLM_apply hn1 hH hs hx
  have hsplit : toEuclideanCLM (𝕜 := ℂ) (1 - Γ.proj s) (toEuclideanCLM (𝕜 := ℂ) (UT s) x)
      = toEuclideanCLM (𝕜 := ℂ) (1 - Γ.proj s)
          (toEuclideanCLM (𝕜 := ℂ) (UT s) x - toEuclideanCLM (𝕜 := ℂ) (UA s) x) := by
    rw [(toEuclideanCLM (𝕜 := ℂ) (1 - Γ.proj s)).map_sub, h0, sub_zero]
  rw [hsplit]
  calc ‖toEuclideanCLM (𝕜 := ℂ) (1 - Γ.proj s)
          (toEuclideanCLM (𝕜 := ℂ) (UT s) x - toEuclideanCLM (𝕜 := ℂ) (UA s) x)‖
      ≤ ‖1 - Γ.proj s‖ * ‖toEuclideanCLM (𝕜 := ℂ) (UT s) x - toEuclideanCLM (𝕜 := ℂ) (UA s) x‖ :=
        norm_toEuclideanCLM_apply_le _ _
    _ ≤ 1 * (C / T * ‖x‖) := by
        gcongr
        · exact Γ.norm_one_sub_proj_le s
        · exact hC T hT UT UA hUT hUA s hs x
    _ = C / T * ‖x‖ := one_mul _

/-- ★★ **The survival form**: `‖ψ₀‖ − (C / T) ‖ψ₀‖ ≤ ‖P s (U_T s ψ₀)‖` for `P 0 ψ₀ = ψ₀` —
the component that stays in the branch has norm at least `(1 − C/T) ‖ψ₀‖`. -/
theorem exists_norm_proj_le {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ UT : ℝ → Matrix (Fin N) (Fin N) ℂ,
      Γ.IsPhysPropagator T UT → ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : EuclideanSpace ℂ (Fin N),
        toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0) x = x →
        ‖x‖ - C / T * ‖x‖
          ≤ ‖toEuclideanCLM (𝕜 := ℂ) (Γ.proj s) (toEuclideanCLM (𝕜 := ℂ) (UT s) x)‖ := by
  obtain ⟨C, hC0, hC⟩ := Γ.exists_norm_one_sub_proj_le hn hH hex
  refine ⟨C, hC0, fun T hT UT hUT s hs x hx => ?_⟩
  have h1 := norm_toEuclideanCLM_apply_sub_le (Γ.proj s) (toEuclideanCLM (𝕜 := ℂ) (UT s) x)
  rw [hUT.norm_toEuclideanCLM_apply hs x] at h1
  linarith [hC T hT UT hUT s hs x hx]

end Matrix.GappedPath

end

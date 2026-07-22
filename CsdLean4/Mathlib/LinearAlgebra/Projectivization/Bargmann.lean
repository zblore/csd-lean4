/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity

/-!
# The Bargmann invariant on complex projective space

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

The (three-point) **Bargmann invariant** of rays `p, q, r` in a complex
inner-product space is the normalised triple product

    `Δ(p,q,r) = ⟪u,v⟫ ⟪v,w⟫ ⟪w,u⟫ / (‖u‖² ‖v‖² ‖w‖²)`

on representatives `u, v, w`. Each vector appears once in a conjugate-linear
slot and once in a linear slot, so rescaling any representative by `c ≠ 0`
multiplies the numerator and denominator by the same `‖c‖²`: the invariant is
well defined on rays. Its modulus is a function of pairwise transition
probabilities, but its PHASE is not: `Δ` is preserved by unitaries and
CONJUGATED by the antiunitary `conjProj`. It is the minimal ray invariant
separating the two Wigner branches, which is exactly what the CSD dynamics
spine consumes.

## Main results

- `bargmannVec`, `bargmann` : the vector-level and ray-level invariants, with
  the well-definedness rewriter `bargmann_mk`.
- `bargmann_smul_unitary` : unitaries preserve the invariant.
- `bargmann_conjProj` : the concrete antiunitary `conjProj` conjugates it.
- `bargmannVec_probe` / `bargmann_probe` : the concrete probe triple
  `(e_i, e_i + e_j, e_i + I·e_j)` (for `i ≠ j`) has `Δ = (1 + I)/4`, so
  `Im Δ = 1/4 ≠ 0` — the unitary and antiunitary branches are genuinely
  separated in dimension `≥ 2`.
- `exists_bargmann_im_ne_zero` : for `2 ≤ N` there is a probe triple with
  `Im Δ ≠ 0`.

**Provenance.** Needed by the CSD dynamics spine W3 clopen-datum closure
(`CsdLean4/LF4/BargmannSelection.lean`): the sign of `Im Δ` along the
projected flow is a continuous discriminator between the unitary and
antiunitary Wigner branches, turning the staged clopen hypothesis into a
scalar continuity hypothesis.

## Tags

projectivization, Bargmann invariant, Wigner theorem, antiunitary, phase
-/

open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-! ## Vector level -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The vector-level Bargmann triple product, normalised by the squared
norms. Each argument appears once as a bra and once as a ket, so the value is
invariant under nonzero rescaling of each argument separately
(`bargmannVec_smul_left` etc.), hence descends to rays. -/
noncomputable def bargmannVec (u v w : E) : ℂ :=
  (inner ℂ u v * inner ℂ v w * inner ℂ w u)
    / ((‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2 : ℝ) : ℂ)

/-- Rescaling the first argument by `c ≠ 0` leaves `bargmannVec` unchanged:
the numerator picks up `conj c * c = ‖c‖²` (once from the conjugate-linear
slot of `⟪u,v⟫`, once from the linear slot of `⟪w,u⟫`), cancelling the
`‖c‖²` in the denominator. -/
lemma bargmannVec_smul_left {c : ℂ} (hc : c ≠ 0) (u v w : E) :
    bargmannVec (c • u) v w = bargmannVec u v w := by
  unfold bargmannVec
  rw [inner_smul_left, inner_smul_right, norm_smul, mul_pow]
  have hnum : (starRingEnd ℂ) c * inner ℂ u v * inner ℂ v w * (c * inner ℂ w u)
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * (inner ℂ u v * inner ℂ v w * inner ℂ w u) := by
    rw [show ((‖c‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) c * c by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    ring
  have hden : (‖c‖ ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2 : ℝ)
      = ‖c‖ ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2) := by ring
  rw [hnum, hden]
  push_cast
  rw [mul_div_mul_left _ _
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)))]

/-- Rescaling the middle argument by `c ≠ 0` leaves `bargmannVec` unchanged. -/
lemma bargmannVec_smul_middle {c : ℂ} (hc : c ≠ 0) (u v w : E) :
    bargmannVec u (c • v) w = bargmannVec u v w := by
  unfold bargmannVec
  rw [inner_smul_right, inner_smul_left, norm_smul, mul_pow]
  have hnum : c * inner ℂ u v * ((starRingEnd ℂ) c * inner ℂ v w) * inner ℂ w u
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * (inner ℂ u v * inner ℂ v w * inner ℂ w u) := by
    rw [show ((‖c‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) c * c by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    ring
  have hden : (‖u‖ ^ 2 * (‖c‖ ^ 2 * ‖v‖ ^ 2) * ‖w‖ ^ 2 : ℝ)
      = ‖c‖ ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2) := by ring
  rw [hnum, hden]
  push_cast
  rw [mul_div_mul_left _ _
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)))]

/-- Rescaling the last argument by `c ≠ 0` leaves `bargmannVec` unchanged. -/
lemma bargmannVec_smul_right {c : ℂ} (hc : c ≠ 0) (u v w : E) :
    bargmannVec u v (c • w) = bargmannVec u v w := by
  unfold bargmannVec
  rw [inner_smul_right, inner_smul_left, norm_smul, mul_pow]
  have hnum : inner ℂ u v * (c * inner ℂ v w) * ((starRingEnd ℂ) c * inner ℂ w u)
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * (inner ℂ u v * inner ℂ v w * inner ℂ w u) := by
    rw [show ((‖c‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) c * c by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    ring
  have hden : (‖u‖ ^ 2 * ‖v‖ ^ 2 * (‖c‖ ^ 2 * ‖w‖ ^ 2) : ℝ)
      = ‖c‖ ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2) := by ring
  rw [hnum, hden]
  push_cast
  rw [mul_div_mul_left _ _
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)))]

/-! ## Ray level -/

/-- The **Bargmann invariant** of three projective points, defined on their
canonical representatives. Well-definedness across representative choice is
`bargmann_mk`. -/
noncomputable def bargmann (p q r : ℙ ℂ E) : ℂ :=
  bargmannVec p.rep q.rep r.rep

/-- A canonical representative of `mk v hv` is a nonzero scalar multiple of
`v`. (Local copy of the `TransitionProbability` helper, which is private.) -/
private lemma rep_mk_smul {v : E} (hv : v ≠ 0) :
    ∃ a : ℂˣ, (Projectivization.mk ℂ v hv).rep = a • v := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ v hv).rep v
      (Projectivization.rep_nonzero _) hv).mp (by rw [Projectivization.mk_rep])
  exact ⟨a, ha.symm⟩

/-- **Well-definedness rewriter.** For arbitrary nonzero representatives, the
ray-level Bargmann invariant equals the vector-level triple product. -/
lemma bargmann_mk {u v w : E} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    bargmann (Projectivization.mk ℂ u hu) (Projectivization.mk ℂ v hv)
      (Projectivization.mk ℂ w hw) = bargmannVec u v w := by
  unfold bargmann
  obtain ⟨a, ha⟩ := rep_mk_smul hu
  obtain ⟨b, hb⟩ := rep_mk_smul hv
  obtain ⟨c, hc⟩ := rep_mk_smul hw
  rw [ha, hb, hc, Units.smul_def, Units.smul_def, Units.smul_def,
    bargmannVec_smul_left (by exact_mod_cast a.ne_zero),
    bargmannVec_smul_middle (by exact_mod_cast b.ne_zero),
    bargmannVec_smul_right (by exact_mod_cast c.ne_zero)]

/-! ## Transformation laws under the Wigner branches -/

variable {N : ℕ}

/-- Unitaries preserve the vector-level Bargmann triple product: the inner
products are preserved (`inner_toEuclideanLin_unitary`) and so are the
norms. -/
lemma bargmannVec_toEuclideanLin_unitary (U : Matrix.unitaryGroup (Fin N) ℂ)
    (u v w : EuclideanSpace ℂ (Fin N)) :
    bargmannVec (Matrix.toEuclideanLin U.val u) (Matrix.toEuclideanLin U.val v)
      (Matrix.toEuclideanLin U.val w) = bargmannVec u v w := by
  have hnorm : ∀ x : EuclideanSpace ℂ (Fin N),
      ‖(Matrix.toEuclideanLin U.val) x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ,
      inner_toEuclideanLin_unitary U x x]
  unfold bargmannVec
  rw [inner_toEuclideanLin_unitary, inner_toEuclideanLin_unitary,
    inner_toEuclideanLin_unitary, hnorm, hnorm, hnorm]

/-- **Unitaries preserve the Bargmann invariant.** -/
theorem bargmann_smul_unitary (U : Matrix.unitaryGroup (Fin N) ℂ)
    (p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    bargmann (U • p) (U • q) (U • r) = bargmann p q r := by
  conv_lhs => rw [← p.mk_rep, ← q.mk_rep, ← r.mk_rep]
  rw [smul_mk_eq_mk_toEuclideanLin U p.rep_nonzero,
    smul_mk_eq_mk_toEuclideanLin U q.rep_nonzero,
    smul_mk_eq_mk_toEuclideanLin U r.rep_nonzero,
    bargmann_mk, bargmannVec_toEuclideanLin_unitary]
  rfl

/-- Coordinatewise conjugation conjugates the vector-level triple product:
each inner product is conjugated (`conjVec_inner`), the norms are fixed
(`conjVec_norm`), and the denominator is real. -/
lemma bargmannVec_conjVec (u v w : EuclideanSpace ℂ (Fin N)) :
    bargmannVec (conjVec u) (conjVec v) (conjVec w)
      = (starRingEnd ℂ) (bargmannVec u v w) := by
  unfold bargmannVec
  rw [conjVec_inner, conjVec_inner, conjVec_inner, conjVec_norm, conjVec_norm,
    conjVec_norm, map_div₀, map_mul, map_mul, Complex.conj_ofReal]

/-- **The antiunitary `conjProj` conjugates the Bargmann invariant.** This is
the phase-sensitivity that no function of pairwise transition probabilities
can see: it separates the two Wigner branches. -/
theorem bargmann_conjProj (p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    bargmann (conjProj p) (conjProj q) (conjProj r)
      = (starRingEnd ℂ) (bargmann p q r) := by
  show bargmann (Projectivization.mk ℂ (conjVec p.rep) (conjVec_ne_zero p.rep_nonzero))
      (Projectivization.mk ℂ (conjVec q.rep) (conjVec_ne_zero q.rep_nonzero))
      (Projectivization.mk ℂ (conjVec r.rep) (conjVec_ne_zero r.rep_nonzero))
    = (starRingEnd ℂ) (bargmann p q r)
  rw [bargmann_mk, bargmannVec_conjVec]
  rfl

/-! ## The non-degenerate probe triple -/

section Probe

variable {N : ℕ} {i j : Fin N}

/-- First probe: the basis ray representative `e_i` is nonzero. -/
lemma probe_fst_ne_zero (i : Fin N) :
    EuclideanSpace.single i (1 : ℂ) ≠ 0 := by
  simp [PiLp.single_eq_zero_iff]

/-- Second probe: `e_i + e_j` is nonzero for `i ≠ j` (its inner product with
`e_i` is `1`). -/
lemma probe_snd_ne_zero (hij : i ≠ j) :
    EuclideanSpace.single i (1 : ℂ) + EuclideanSpace.single j 1 ≠ 0 := by
  intro h0
  have h1 : (inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single i (1 : ℂ) + EuclideanSpace.single j 1) : ℂ) = 1 := by
    rw [inner_add_right, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left]
    simp [hij.symm]
  rw [h0, inner_zero_right] at h1
  exact zero_ne_one h1

/-- Third probe: `e_i + I·e_j` is nonzero for `i ≠ j`. -/
lemma probe_trd_ne_zero (hij : i ≠ j) :
    EuclideanSpace.single i (1 : ℂ) + Complex.I • EuclideanSpace.single j 1 ≠ 0 := by
  intro h0
  have h1 : (inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single i (1 : ℂ) + Complex.I • EuclideanSpace.single j 1) : ℂ)
      = 1 := by
    rw [inner_add_right, inner_smul_right, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left]
    simp [hij.symm]
  rw [h0, inner_zero_right] at h1
  exact zero_ne_one h1

/-- **The probe value.** On the triple `(e_i, e_i + e_j, e_i + I·e_j)` with
`i ≠ j`, the vector-level Bargmann triple product is `(1 + I)/4`: the inner
products are `1`, `1 + I`, `1` and the squared norms `1`, `2`, `2`. -/
theorem bargmannVec_probe (hij : i ≠ j) :
    bargmannVec (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)
      (EuclideanSpace.single i 1 + Complex.I • EuclideanSpace.single j 1)
      = (1 + Complex.I) / 4 := by
  have hii : (inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single i (1 : ℂ)) : ℂ) = 1 := by
    rw [EuclideanSpace.inner_single_left]
    simp
  have hij' : (inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single j (1 : ℂ)) : ℂ) = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp [hij.symm]
  have hji : (inner ℂ (EuclideanSpace.single j (1 : ℂ))
      (EuclideanSpace.single i (1 : ℂ)) : ℂ) = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp [hij]
  have hjj : (inner ℂ (EuclideanSpace.single j (1 : ℂ))
      (EuclideanSpace.single j (1 : ℂ)) : ℂ) = 1 := by
    rw [EuclideanSpace.inner_single_left]
    simp
  -- The three numerator inner products.
  have h1 : (inner ℂ (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single i (1 : ℂ) + EuclideanSpace.single j 1) : ℂ) = 1 := by
    rw [inner_add_right, hii, hij']; ring
  have h2 : (inner ℂ (EuclideanSpace.single i (1 : ℂ) + EuclideanSpace.single j 1)
      (EuclideanSpace.single i (1 : ℂ) + Complex.I • EuclideanSpace.single j 1) : ℂ)
      = 1 + Complex.I := by
    rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, hii, hij', hji, hjj]
    ring
  have h3 : (inner ℂ (EuclideanSpace.single i (1 : ℂ)
        + Complex.I • EuclideanSpace.single j 1)
      (EuclideanSpace.single i (1 : ℂ)) : ℂ) = 1 := by
    rw [inner_add_left, inner_smul_left, hii, hji]
    simp
  -- The three squared norms.
  have hn1 : ‖EuclideanSpace.single i (1 : ℂ)‖ ^ 2 = 1 := by
    rw [PiLp.norm_single]; simp
  have hn2 : ‖EuclideanSpace.single i (1 : ℂ) + EuclideanSpace.single j 1‖ ^ 2 = 2 := by
    rw [← @inner_self_eq_norm_sq ℂ]
    rw [inner_add_left, inner_add_right, inner_add_right, hii, hij', hji, hjj]
    norm_num
  have hn3 : ‖EuclideanSpace.single i (1 : ℂ)
      + Complex.I • EuclideanSpace.single j 1‖ ^ 2 = 2 := by
    rw [← @inner_self_eq_norm_sq ℂ]
    rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
      inner_smul_right, inner_smul_right, inner_smul_left, hii, hij', hji, hjj]
    simp [Complex.conj_I]
    norm_num
  unfold bargmannVec
  rw [h1, h2, h3, hn1, hn2, hn3]
  norm_num

/-- **The probe triple separates the branches.** The ray-level Bargmann
invariant of the probe triple is `(1 + I)/4`, with imaginary part `1/4 ≠ 0`. -/
theorem bargmann_probe (hij : i ≠ j) :
    bargmann (Projectivization.mk ℂ (EuclideanSpace.single i (1 : ℂ))
        (probe_fst_ne_zero i))
      (Projectivization.mk ℂ (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)
        (probe_snd_ne_zero hij))
      (Projectivization.mk ℂ
        (EuclideanSpace.single i 1 + Complex.I • EuclideanSpace.single j 1)
        (probe_trd_ne_zero hij))
      = (1 + Complex.I) / 4 := by
  rw [bargmann_mk, bargmannVec_probe hij]

/-- For `2 ≤ N` there is a probe triple whose Bargmann invariant has nonzero
imaginary part: the two Wigner branches are genuinely separated in dimension
at least `2`. -/
theorem exists_bargmann_im_ne_zero (hN : 2 ≤ N) :
    ∃ p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N)), (bargmann p q r).im ≠ 0 := by
  have h0 : (0 : ℕ) < N := by omega
  have h1 : (1 : ℕ) < N := by omega
  have hij : (⟨0, h0⟩ : Fin N) ≠ ⟨1, h1⟩ := Fin.ne_of_val_ne (by norm_num)
  refine ⟨Projectivization.mk ℂ (EuclideanSpace.single ⟨0, h0⟩ (1 : ℂ))
      (probe_fst_ne_zero _),
    Projectivization.mk ℂ
      (EuclideanSpace.single ⟨0, h0⟩ 1 + EuclideanSpace.single ⟨1, h1⟩ 1)
      (probe_snd_ne_zero hij),
    Projectivization.mk ℂ
      (EuclideanSpace.single ⟨0, h0⟩ 1
        + Complex.I • EuclideanSpace.single ⟨1, h1⟩ 1)
      (probe_trd_ne_zero hij), ?_⟩
  rw [bargmann_probe hij]
  norm_num [Complex.div_im, Complex.normSq_apply]

end Probe

end Projectivization

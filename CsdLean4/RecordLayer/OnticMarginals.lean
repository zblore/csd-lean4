/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.OnticComposite
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.PartialTrace
public import CsdLean4.LF4.ProjectedDynamics

/-!
# SigmaLayer/OnticMarginals: A6 steps 2–3 — ontic reduction maps, and marginal stability

**Category:** 7-SigmaLayer (Paper C A6 — composite systems).

## What this adds

Step 1 (`OnticComposite.lean`) made non-factorisation a theorem. This file supplies the other half
of A6's mathematical content:

* **Step 2 — the ontic reduction maps.** A composite ray has a density matrix (`rayDensity`,
  ray-well-defined, unit trace), and its subsystem marginals are the partial traces
  (`reduceA`, `reduceB`). This is the ontic-level `r_S` — the map from a point of the composite
  sector to what a subsystem observer can see of it.
* **Step 3 — marginal stability = ontic no-signalling.** Under a **local** unitary on `A`
  (the vector action `actA`, with no Kronecker plumbing):
  - **the `B`-marginal is invariant** (`reduceB_pointA_invariant`) — acting on `A` changes nothing
    `B` can see, at the level of the single ontic point;
  - **the `A`-marginal evolves by conjugation** (`reduceA_pointA_conj`) — the Heisenberg
    transformation law.
  Instantiated at the Schrödinger unitaries (`reduceB_local_flow_invariant`): **the local flow of
  any `A`-Hamiltonian leaves the `B`-marginal fixed at every time.** That is A6's "marginal
  stability", and it is the ontic-flow form of the corpus's operational
  `tensorSector_no_signalling`.

## ⚠️ Scope

* These are **kinematic identities about the reduction maps** under local unitaries; they are
  exactly what A6's marginal-stability clause asserts, and nothing here claims a new dynamics.
* Step 4 of the plan — *dynamical* no-signalling through the v0.7.0 measurement layer (a protocol
  acting on `A`'s register leaves the unconditioned `B`-marginal unchanged) — is **not** in this
  file.
* The maps are defined at the projective level (the base of `Σ`); the torus fibre plays no role in
  reduction, so the `KSigma` form is the composition with `Prod.fst` and is not separately stated.

## References

`SigmaLayer/OnticComposite.lean` (step 1); `Mathlib/LinearAlgebra/Matrix/PartialTrace.lean`
(`traceRight`, `traceLeft`); `LF4/ProjectedDynamics.lean` (`schrodingerUnitary`);
`LF3/Projectors/TensorModel.lean`, `SigmaLayer/TensorSector.lean` (the operational no-signalling
this is the ontic form of); `specs/reconstruction-status.md` §2 (the A6 row).
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization
open Matrix

namespace CSD.RecordLayer

variable {nA nB : ℕ}

/-! ### Step 2: the ray density and its marginals -/

/-- **The density matrix of a composite ray**: `ρ(x,y) = v(x)·conj(v(y))/‖v‖²` at the canonical
representative. Ray-well-defined (`rayDensity_mk`), unit trace (`rayDensity_trace`). -/
noncomputable def rayDensity (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    Matrix (Fin nA × Fin nB) (Fin nA × Fin nB) ℂ :=
  Matrix.of fun x y => p.rep x * star (p.rep y) / ((‖p.rep‖ ^ 2 : ℝ) : ℂ)

/-- The scale-invariance computation behind ray-well-definedness. -/
theorem rayDensity_ratio_smul (c : ℂ) (hc : c ≠ 0) (v : EuclideanSpace ℂ (Fin nA × Fin nB))
    (x y : Fin nA × Fin nB) :
    (c • v) x * star ((c • v) y) / ((‖c • v‖ ^ 2 : ℝ) : ℂ)
      = v x * star (v y) / ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  have hnum : (c • v) x * star ((c • v) y) = (c * star c) * (v x * star (v y)) := by
    simp only [PiLp.smul_apply, smul_eq_mul, star_mul']
    ring
  have hcs : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star c = (starRingEnd ℂ) c from rfl, mul_comm, Complex.conj_mul']
    push_cast
    ring
  have hden : ((‖c • v‖ ^ 2 : ℝ) : ℂ) = (c * star c) * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_smul, mul_pow, hcs]
    push_cast
    ring
  rw [hnum, hden, mul_div_mul_left]
  exact mul_ne_zero hc (star_ne_zero.mpr hc)

/-- **The density is well-defined on rays.** -/
theorem rayDensity_mk (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (hv : v ≠ 0) :
    rayDensity (Projectivization.mk ℂ v hv)
      = Matrix.of fun x y => v x * star (v y) / ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ v hv).rep v
        (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  ext x y
  show (Projectivization.mk ℂ v hv).rep x * star ((Projectivization.mk ℂ v hv).rep y)
      / ((‖(Projectivization.mk ℂ v hv).rep‖ ^ 2 : ℝ) : ℂ)
    = v x * star (v y) / ((‖v‖ ^ 2 : ℝ) : ℂ)
  rw [← ha]
  simp only [Units.smul_def]
  exact rayDensity_ratio_smul (↑a) (Units.ne_zero a) v x y

/-- `‖w‖²` as the diagonal sum `∑ₓ w(x)·conj(w(x))` — the casting workhorse for the marginal
computations. -/
theorem normSq_eq_sum_mul_star {ι : Type*} [Fintype ι] (w : EuclideanSpace ℂ ι) :
    ((‖w‖ ^ 2 : ℝ) : ℂ) = ∑ x, w x * star (w x) := by
  have h1 : ‖w‖ ^ 2 = ∑ x, ‖w x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [h1]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show star (w x) = (starRingEnd ℂ) (w x) from rfl, mul_comm, Complex.conj_mul']

/-- The ray density has **unit trace** — it is a genuine state. -/
theorem rayDensity_trace (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    (rayDensity p).trace = 1 := by
  have hne : (‖p.rep‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr p.rep_nonzero
  have hnorm : (0:ℝ) < ‖p.rep‖ ^ 2 := by positivity
  show (∑ x, rayDensity p x x) = 1
  simp only [rayDensity, Matrix.of_apply]
  rw [← Finset.sum_div, ← normSq_eq_sum_mul_star, div_self]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hnorm)

/-- **The `A`-marginal** of a composite ray: trace out `B`. -/
noncomputable def reduceA (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    Matrix (Fin nA) (Fin nA) ℂ :=
  traceRight (rayDensity p)

/-- **The `B`-marginal** of a composite ray: trace out `A`. -/
noncomputable def reduceB (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    Matrix (Fin nB) (Fin nB) ℂ :=
  traceLeft (rayDensity p)

/-! ### Step 3: local unitaries, and marginal stability -/

/-- **The local `A`-action on composite vectors**: `(actA U v)(j,k) = ∑ₐ U j a · v(a,k)` — the
vector form of `U ⊗ 1`, with no Kronecker plumbing. -/
noncomputable def actA (U : Matrix (Fin nA) (Fin nA) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) : EuclideanSpace ℂ (Fin nA × Fin nB) :=
  WithLp.toLp 2 fun jk => ∑ a, U jk.1 a * v (a, jk.2)

@[simp] theorem actA_apply (U : Matrix (Fin nA) (Fin nA) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (j : Fin nA) (k : Fin nB) :
    actA U v (j, k) = ∑ a, U j a * v (a, k) := rfl

theorem actA_actA (U W : Matrix (Fin nA) (Fin nA) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    actA U (actA W v) = actA (U * W) v := by
  apply PiLp.ext
  intro jk
  show ∑ a, U jk.1 a * (∑ b, W a b * v (b, jk.2)) = ∑ b, (U * W) jk.1 b * v (b, jk.2)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem actA_one (v : EuclideanSpace ℂ (Fin nA × Fin nB)) : actA 1 v = v := by
  apply PiLp.ext
  intro jk
  show ∑ a, (1 : Matrix (Fin nA) (Fin nA) ℂ) jk.1 a * v (a, jk.2) = v jk
  rw [Finset.sum_eq_single jk.1]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

theorem actA_zero (U : Matrix (Fin nA) (Fin nA) ℂ) :
    actA (nB := nB) U 0 = 0 := by
  apply PiLp.ext
  intro jk
  show ∑ a, U jk.1 a * (0 : EuclideanSpace ℂ (Fin nA × Fin nB)) (a, jk.2) = 0
  simp

theorem actA_ne_zero {U : Matrix (Fin nA) (Fin nA) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin nA) ℂ)
    {v : EuclideanSpace ℂ (Fin nA × Fin nB)} (hv : v ≠ 0) : actA U v ≠ 0 := by
  intro h0
  apply hv
  have hUU : star U * U = 1 := hU.1
  have h := congrArg (actA (star U)) h0
  rw [actA_actA, hUU, actA_one, actA_zero] at h
  exact h

/-- **★ The workhorse: local sums against a unitary collapse.** For `UᴴU = 1`,

  `∑ⱼ (actA U v)(j,k) · conj((actA U v)(j,k')) = ∑ₐ v(a,k) · conj(v(a,k'))`

for **every** pair of `B`-indices — the invariance computation behind both the norm and the
`B`-marginal. -/
theorem actA_column_sums {U : Matrix (Fin nA) (Fin nA) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin nA) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (k k' : Fin nB) :
    ∑ j, actA U v (j, k) * star (actA U v (j, k'))
      = ∑ a, v (a, k) * star (v (a, k')) := by
  classical
  have hUU : star U * U = 1 := hU.1
  have hexp : ∀ j, actA U v (j, k) * star (actA U v (j, k'))
      = ∑ a, ∑ b, U j a * v (a, k) * (star (U j b) * star (v (b, k'))) := by
    intro j
    rw [actA_apply, actA_apply, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [star_mul']
  calc ∑ j, actA U v (j, k) * star (actA U v (j, k'))
      = ∑ j, ∑ a, ∑ b, U j a * v (a, k) * (star (U j b) * star (v (b, k'))) :=
        Finset.sum_congr rfl fun j _ => hexp j
    _ = ∑ a, ∑ b, (∑ j, star (U j b) * U j a) * (v (a, k) * star (v (b, k'))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ a, ∑ b, (star U * U) b a * (v (a, k) * star (v (b, k'))) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        congr 1
    _ = ∑ a, v (a, k) * star (v (a, k')) := by
        rw [hUU]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          simp [hb]
        · simp

/-- The bilinear expansion of a row sum — no unitarity needed. -/
theorem actA_row_sums (U : Matrix (Fin nA) (Fin nA) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (j j' : Fin nA) :
    ∑ k, actA U v (j, k) * star (actA U v (j', k))
      = ∑ a, ∑ b, U j a * star (U j' b) * ∑ k, v (a, k) * star (v (b, k)) := by
  classical
  have hexp : ∀ k, actA U v (j, k) * star (actA U v (j', k))
      = ∑ a, ∑ b, U j a * star (U j' b) * (v (a, k) * star (v (b, k))) := by
    intro k
    rw [actA_apply, actA_apply, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [star_mul']
    ring
  calc ∑ k, actA U v (j, k) * star (actA U v (j', k))
      = ∑ k, ∑ a, ∑ b, U j a * star (U j' b) * (v (a, k) * star (v (b, k))) :=
        Finset.sum_congr rfl fun k _ => hexp k
    _ = ∑ a, ∑ b, U j a * star (U j' b) * ∑ k, v (a, k) * star (v (b, k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]

/-- Local unitaries preserve the composite norm. -/
theorem norm_actA {U : Matrix (Fin nA) (Fin nA) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin nA) ℂ)
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) : ‖actA U v‖ = ‖v‖ := by
  have hsq : ((‖actA U v‖ ^ 2 : ℝ) : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [normSq_eq_sum_mul_star, normSq_eq_sum_mul_star, Fintype.sum_prod_type,
      Fintype.sum_prod_type, Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => actA_column_sums hU v k k
  have h2 : ‖actA U v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast hsq
  have h3 := norm_nonneg (actA U v)
  have h4 := norm_nonneg v
  apply le_antisymm <;> nlinarith [h2, h3, h4]

/-- The local action on composite **rays**. -/
noncomputable def pointA {U : Matrix (Fin nA) (Fin nA) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin nA) ℂ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)) :=
  Projectivization.mk ℂ (actA U p.rep) (actA_ne_zero hU p.rep_nonzero)

/-- **★★ Marginal stability = ontic no-signalling.** A local unitary on `A` leaves the
`B`-marginal of the composite ray **unchanged**: acting on `A` changes nothing `B` can see, at the
level of the single ontic point. This is Paper C A6's marginal-stability clause, and the ontic form
of the corpus's operational `tensorSector_no_signalling`. -/
theorem reduceB_pointA_invariant {U : Matrix (Fin nA) (Fin nA) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin nA) ℂ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    reduceB (pointA hU p) = reduceB p := by
  ext k k'
  show traceLeft (rayDensity (pointA hU p)) k k' = traceLeft (rayDensity p) k k'
  rw [show pointA hU p = Projectivization.mk ℂ (actA U p.rep)
      (actA_ne_zero hU p.rep_nonzero) from rfl, rayDensity_mk]
  rw [show rayDensity p = Matrix.of fun x y =>
      p.rep x * star (p.rep y) / ((‖p.rep‖ ^ 2 : ℝ) : ℂ) by
    conv_lhs => rw [show p = Projectivization.mk ℂ p.rep p.rep_nonzero
      from (Projectivization.mk_rep p).symm]
    rw [rayDensity_mk]]
  simp only [traceLeft_apply, Matrix.of_apply]
  rw [← Finset.sum_div, ← Finset.sum_div, norm_actA hU, actA_column_sums hU]

/-- **The `A`-marginal evolves by conjugation** — the Heisenberg transformation law for the
reduction map. -/
theorem reduceA_pointA_conj {U : Matrix (Fin nA) (Fin nA) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin nA) ℂ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    reduceA (pointA hU p) = U * reduceA p * star U := by
  classical
  ext j j'
  show traceRight (rayDensity (pointA hU p)) j j'
    = (U * traceRight (rayDensity p) * star U) j j'
  rw [show pointA hU p = Projectivization.mk ℂ (actA U p.rep)
      (actA_ne_zero hU p.rep_nonzero) from rfl, rayDensity_mk]
  rw [show rayDensity p = Matrix.of fun x y =>
      p.rep x * star (p.rep y) / ((‖p.rep‖ ^ 2 : ℝ) : ℂ) by
    conv_lhs => rw [show p = Projectivization.mk ℂ p.rep p.rep_nonzero
      from (Projectivization.mk_rep p).symm]
    rw [rayDensity_mk]]
  -- Left side: the row sum over the transformed vector, with the norm preserved.
  have hlhs : traceRight (Matrix.of fun x y =>
        actA U p.rep x * star (actA U p.rep y) / ((‖actA U p.rep‖ ^ 2 : ℝ) : ℂ)) j j'
      = (∑ a, ∑ b, U j a * star (U j' b) * ∑ k, p.rep (a, k) * star (p.rep (b, k)))
          / ((‖p.rep‖ ^ 2 : ℝ) : ℂ) := by
    simp only [traceRight_apply, Matrix.of_apply]
    rw [norm_actA hU, ← Finset.sum_div, actA_row_sums]
  -- Right side: the conjugated matrix product expands to the same double sum.
  have hrhs : (U * traceRight (Matrix.of fun x y =>
        p.rep x * star (p.rep y) / ((‖p.rep‖ ^ 2 : ℝ) : ℂ)) * star U) j j'
      = (∑ a, ∑ b, U j a * star (U j' b) * ∑ k, p.rep (a, k) * star (p.rep (b, k)))
          / ((‖p.rep‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    calc ∑ b, (U * traceRight (Matrix.of fun x y =>
            p.rep x * star (p.rep y) / ((‖p.rep‖ ^ 2 : ℝ) : ℂ))) j b * (star U) b j'
        = ∑ b, ∑ a, (U j a * star (U j' b) * ∑ k, p.rep (a, k) * star (p.rep (b, k)))
            / ((‖p.rep‖ ^ 2 : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Matrix.mul_apply, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [traceRight_apply, Matrix.of_apply, Matrix.star_apply]
          rw [← Finset.sum_div]
          ring
      _ = (∑ b, ∑ a, U j a * star (U j' b) * ∑ k, p.rep (a, k) * star (p.rep (b, k)))
            / ((‖p.rep‖ ^ 2 : ℝ) : ℂ) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_div]
      _ = (∑ a, ∑ b, U j a * star (U j' b) * ∑ k, p.rep (a, k) * star (p.rep (b, k)))
            / ((‖p.rep‖ ^ 2 : ℝ) : ℂ) := by
          rw [Finset.sum_comm]
  rw [hlhs, hrhs]

/-- **★★ Marginal stability under local flows.** The Schrödinger flow of any `A`-Hamiltonian
leaves the `B`-marginal fixed **at every time** — A6's marginal-stability clause in flow form, the
ontic no-signalling statement. -/
theorem reduceB_local_flow_invariant [NeZero nA] {HA : Matrix (Fin nA) (Fin nA) ℂ}
    (hHA : HA.IsHermitian) (t : ℝ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    reduceB (pointA (CSD.LF4.schrodingerUnitary hHA t).2 p) = reduceB p :=
  reduceB_pointA_invariant _ p

end CSD.RecordLayer

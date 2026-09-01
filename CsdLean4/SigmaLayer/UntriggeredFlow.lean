/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FrozenBase

/-!
# SigmaLayer/UntriggeredFlow: one flow that records and back-reacts, with no trigger

**Category:** dynamical measurement — `specs/frozen-base-obstruction-scoping.md` brick 2.

## What this is

`specs/BACKLOG.md` row 350 closes on: *"the relocation is not the obstacle; the **trigger**
is."* The corpus's measurement is two strokes — create the record, then a **readout-triggered**
relocation. Brick 1 (`SigmaLayer/FrozenBase.lean`) says why one stroke could not do both while
the base stayed frozen: a `C¹` generator with a pointwise-frozen base is base-constant, so it
cannot depend on the outcome at all.

This module supplies the converse witness in the chart. **One** Hamiltonian, **one** flow, no
trigger, no second stroke:

  `𝓗(z) = (Σᵢ cᵢ xᵢ) · y_k`,  with `c k = 0`

the ontic analogue of the textbook von Neumann coupling `Â ⊗ p̂`, with the *base position* read
out onto the pointer. Hamilton's equations give, in closed form:

* `ẋ_k = Σᵢ cᵢ xᵢ` — **the record.** The pointer coordinate drifts at a rate set by the base,
  so its displacement *is* the measured value (`untriggeredCurve_records`).
* `ẏᵢ = −cᵢ · y_k` — **the back-reaction.** The base momenta move, at a rate set by the
  pointer momentum (`untriggeredCurve_backreacts`).
* `ẋⱼ = 0` for `j ≠ k`, and `ẏ_k = 0`: everything else is fixed, which is what makes the
  system integrable in closed form.

★★ `untriggeredCurve_isHamiltonianCurve` — the explicit curve **is** an integral curve of the
coupling.

## ★ The loop with brick 1 closes

`not_baseFrozen_interactionH` shows this generator is **not** `BaseFrozen` whenever the
coupling and the pointer momentum are both non-trivial — which brick 1 *requires*, since the
generator is outcome-dependent by construction. The two modules are the two directions of one
statement: brick 1 says an outcome-dependent `C¹` generator must move the base; this exhibits
one that does, and computes exactly how much (`−cᵢ·y_k` per unit time).

Note *which* base coordinate moves. The base **position** is fixed (`ẋⱼ = 0` for `j ≠ k`) —
the measured value is not disturbed, so the measurement is repeatable — while the base
**momentum** absorbs the back-reaction. That is the ontic form of "a measurement disturbs the
conjugate variable", and it is a computation here rather than a slogan.

## ⚠️ Honest scope — this does NOT close `H_int(M)`

1. **A chart witness, not an arena one.** `Chart n` is globally `ℝ^{2n}`; the arena is not,
   and nothing here transports (`SigmaLayer/ChartBracket.lean` honest scope). The
   chart→arena transport **remains open** (⚠️ RESIDUE(R-016)).
2. **A witness, not a derivation.** `𝓗` is *engineered* to record. That a physically natural
   interaction must take this form is not shown and is not the kind of thing Lean shows —
   which interaction an apparatus realises is a permanent boundary (⚠️ RESIDUE(R-015)).
3. **Records here are not yet Born weights.** This module builds the *dynamics*; it does not
   redo `shear_sector_born` on it, so the measure-theoretic half — that the basins of this
   flow carry the moment-map weights — is not established. That is the work an arena-level
   successor would have to do, and it is not attempted.
4. **`c k = 0` is a hypothesis**, and it is what keeps the system closed-form: with `c k ≠ 0`
   the pointer feeds back into its own drift rate and the flow is no longer affine.
5. ~~**Uniqueness is not proved here.**~~ **RESOLVED** — `SigmaLayer/UntriggeredVolume.lean`
   establishes the `LipschitzWith` bound (`lipschitzWith_interactionH_field`: the field is a
   continuous linear map, so its operator norm is a Lipschitz constant) and feeds it to brick
   0's `hamiltonianCurve_unique`, giving `untriggeredCurve_unique`: this is *the* integral
   curve through `z₀`, not merely *an* integral curve. The same module proves the flow
   preserves chart volume (`untriggeredCurve_measurePreserving`). *(This item originally
   recorded the gap; the strikethrough keeps the record.)*

## References

`specs/frozen-base-obstruction-scoping.md` (brick 2); `specs/BACKLOG.md` (row "★★ The
dynamical measurement layer (Paper D `H_int`)", the trigger); `specs/future-work.md`;
`SigmaLayer/ChartBracket.lean` (`Chart`, `dPos`, `dMom`, `hamiltonianField`);
`SigmaLayer/ChartIntegralCurve.lean` (brick 0 — `IsHamiltonianCurve`,
`hamiltonianCurve_unique`); `SigmaLayer/FrozenBase.lean` (brick 1 — `BaseFrozen`,
`not_baseFrozen_of_outcomeDependent`); `RecordLayer/ShearWitness.lean` (the two-stroke
witness this is the one-stroke counterpart to); `RecordLayer/JoinGeneration.lean`
(`joinSwap_eq_flowTimeOne`, the triggered relocation).
-/

@[expose] public section

namespace CSD.SigmaLayer

open Set

variable {n : ℕ}

/-! ### The coupling -/

/-- The base functional `z ↦ Σᵢ cᵢ xᵢ`, as a continuous linear map. -/
noncomputable def posCLM (c : Fin n → ℝ) : Chart n →L[ℝ] ℝ :=
  (∑ i, (c i) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))

@[simp] theorem posCLM_apply (c : Fin n → ℝ) (z : Chart n) :
    posCLM c z = ∑ i, c i * z.1 i := by
  simp [posCLM]

/-- The pointer-momentum functional `z ↦ y_k`. -/
noncomputable def momCoord (k : Fin n) : Chart n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).comp
    (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))

@[simp] theorem momCoord_apply (k : Fin n) (z : Chart n) : momCoord k z = z.2 k := rfl

/-- **The von Neumann coupling in the chart**: `𝓗(z) = (Σᵢ cᵢ xᵢ) · y_k`. The base position
is coupled to the pointer momentum, so the pointer translates at a base-dependent rate. -/
noncomputable def interactionH (c : Fin n → ℝ) (k : Fin n) (z : Chart n) : ℝ :=
  (∑ i, c i * z.1 i) * z.2 k

theorem hasFDerivAt_interactionH (c : Fin n → ℝ) (k : Fin n) (z : Chart n) :
    HasFDerivAt (interactionH (n := n) c k)
      ((∑ i, c i * z.1 i) • momCoord k + z.2 k • posCLM c) z := by
  have hA : HasFDerivAt (fun w : Chart n => ∑ i, c i * w.1 i) (posCLM c) z := by
    have hfun : (fun w : Chart n => ∑ i, c i * w.1 i) = ⇑(posCLM (n := n) c) := by
      funext w; rw [posCLM_apply]
    rw [hfun]
    exact (posCLM c).hasFDerivAt
  have hB : HasFDerivAt (fun w : Chart n => w.2 k) (momCoord k) z :=
    (momCoord (n := n) k).hasFDerivAt
  exact hA.mul hB

theorem fderiv_interactionH (c : Fin n → ℝ) (k : Fin n) (z : Chart n) :
    fderiv ℝ (interactionH (n := n) c k) z
      = (∑ i, c i * z.1 i) • momCoord k + z.2 k • posCLM c :=
  (hasFDerivAt_interactionH c k z).fderiv

/-! ### Hamilton's equations for the coupling -/

/-- Contracting a coefficient vector against a coordinate direction. -/
theorem sum_mul_single (c : Fin n → ℝ) (i : Fin n) :
    (∑ x, c x * (Pi.single i (1 : ℝ) : Fin n → ℝ) x) = c i := by
  classical
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro b _ hb
    simp [hb]

@[simp] theorem dPos_interactionH (c : Fin n → ℝ) (k : Fin n) (z : Chart n) (i : Fin n) :
    dPos (interactionH (n := n) c k) z i = c i * z.2 k := by
  classical
  rw [dPos, fderiv_interactionH]
  simp only [add_apply, smul_apply, posCLM_apply, momCoord_apply, posDir, smul_eq_mul]
  simp [sum_mul_single, mul_comm]

@[simp] theorem dMom_interactionH (c : Fin n → ℝ) (k : Fin n) (z : Chart n) (i : Fin n) :
    dMom (interactionH (n := n) c k) z i
      = if i = k then ∑ j, c j * z.1 j else 0 := by
  classical
  rw [dMom, fderiv_interactionH]
  simp only [add_apply, smul_apply, posCLM_apply, momCoord_apply, momDir, smul_eq_mul]
  by_cases h : i = k
  · subst h
    simp
  · simp [h, Ne.symm h]

/-! ### ★ The loop with brick 1 -/

/-- ★ **The recording generator is not base-frozen** — exactly as brick 1 requires. If the
coupling is non-trivial at some base index and the pointer momentum is non-zero somewhere,
`BaseFrozen` fails: the flow *must* move the base. -/
theorem not_baseFrozen_interactionH {c : Fin n → ℝ} {k : Fin n} {S : Finset (Fin n)}
    {i : Fin n} (hiS : i ∈ S) (hc : c i ≠ 0) (z : Chart n) (hz : z.2 k ≠ 0) :
    ¬ BaseFrozen (interactionH (n := n) c k) S := by
  intro h
  have := (h z i hiS).1
  rw [dPos_interactionH] at this
  exact (mul_ne_zero hc hz) this

/-! ### The flow, in closed form -/

/-- **The one-stroke measurement flow.** Positions: only the pointer coordinate `k` moves, at
the base-determined rate `Σᵢ cᵢ xᵢ`. Momenta: every base momentum drifts at `−cᵢ·y_k`, the
back-reaction. -/
noncomputable def untriggeredCurve (c : Fin n → ℝ) (k : Fin n) (z₀ : Chart n) (t : ℝ) :
    Chart n :=
  (fun j => if j = k then z₀.1 k + t * (∑ i, c i * z₀.1 i) else z₀.1 j,
   fun j => z₀.2 j - t * (c j * z₀.2 k))

@[simp] theorem untriggeredCurve_zero (c : Fin n → ℝ) (k : Fin n) (z₀ : Chart n) :
    untriggeredCurve c k z₀ 0 = z₀ := by
  refine Prod.ext ?_ ?_
  · funext j
    by_cases h : j = k
    · subst h; simp [untriggeredCurve]
    · simp [untriggeredCurve, h]
  · funext j
    simp [untriggeredCurve]

/-- The pointer momentum is conserved (because `c k = 0`), so the drift rate is constant. -/
theorem untriggeredCurve_snd_k (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0) (z₀ : Chart n)
    (t : ℝ) : (untriggeredCurve c k z₀ t).2 k = z₀.2 k := by
  show z₀.2 k - t * (c k * z₀.2 k) = z₀.2 k
  rw [hck, zero_mul, mul_zero, sub_zero]

/-- The base positions are conserved, so the measured value is not disturbed. -/
theorem untriggeredCurve_fst_ne (c : Fin n → ℝ) (k : Fin n) (z₀ : Chart n) (t : ℝ)
    {j : Fin n} (hj : j ≠ k) : (untriggeredCurve c k z₀ t).1 j = z₀.1 j := by
  show (if j = k then z₀.1 k + t * (∑ i, c i * z₀.1 i) else z₀.1 j) = z₀.1 j
  rw [if_neg hj]

/-- The coupling's value is conserved along the curve — the reason the system is affine. -/
theorem untriggeredCurve_sum (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0) (z₀ : Chart n)
    (t : ℝ) :
    (∑ i, c i * (untriggeredCurve c k z₀ t).1 i) = ∑ i, c i * z₀.1 i := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = k
  · rw [h, hck, zero_mul, zero_mul]
  · rw [untriggeredCurve_fst_ne c k z₀ t h]

/-! ### ★★ It is the integral curve -/

/-- ★★ **The one-stroke flow is an integral curve of the coupling** — a single Hamiltonian
flow that creates the record and back-reacts, with no readout trigger anywhere. -/
theorem untriggeredCurve_isHamiltonianCurve (c : Fin n → ℝ) (k : Fin n) (hck : c k = 0)
    (z₀ : Chart n) :
    IsHamiltonianCurve (interactionH (n := n) c k) (untriggeredCurve c k z₀) := by
  classical
  intro t
  rw [hamiltonianField]
  refine HasDerivAt.prodMk ?_ ?_
  · rw [hasDerivAt_pi]
    intro j
    by_cases h : j = k
    · simp only [if_pos h]
      rw [dMom_interactionH, if_pos h, untriggeredCurve_sum c k hck z₀ t]
      simpa using ((hasDerivAt_id t).mul_const (∑ i, c i * z₀.1 i)).const_add (z₀.1 k)
    · simp only [if_neg h]
      rw [dMom_interactionH, if_neg h]
      exact hasDerivAt_const t (z₀.1 j)
  · rw [hasDerivAt_pi]
    intro j
    rw [dPos_interactionH, untriggeredCurve_snd_k c k hck z₀ t]
    simpa using ((hasDerivAt_id t).mul_const (c j * z₀.2 k)).const_sub (z₀.2 j)

/-! ### ★ What it does: a record, and a back-reaction -/

/-- ★ **The record.** The pointer's displacement at time `t` is exactly `t` times the measured
base quantity — the readout, as a closed-form computation. -/
theorem untriggeredCurve_records (c : Fin n → ℝ) (k : Fin n) (z₀ : Chart n) (t : ℝ) :
    (untriggeredCurve c k z₀ t).1 k - z₀.1 k = t * ∑ i, c i * z₀.1 i := by
  simp [untriggeredCurve]

/-- ★ **The back-reaction.** Each base momentum moves at `−cᵢ·y_k`. The base *position* is
untouched (`untriggeredCurve_fst_ne`), so the measured value is repeatable while its conjugate
absorbs the disturbance. -/
theorem untriggeredCurve_backreacts (c : Fin n → ℝ) (k : Fin n) (z₀ : Chart n) (t : ℝ)
    (i : Fin n) : (untriggeredCurve c k z₀ t).2 i = z₀.2 i - t * (c i * z₀.2 k) := rfl

/-- The back-reaction is genuinely non-trivial: at any `t ≠ 0`, a non-trivial coupling and a
non-zero pointer momentum move the base momentum. -/
theorem untriggeredCurve_backreaction_ne (c : Fin n → ℝ) (k : Fin n) (z₀ : Chart n) {t : ℝ}
    (ht : t ≠ 0) {i : Fin n} (hc : c i ≠ 0) (hz : z₀.2 k ≠ 0) :
    (untriggeredCurve c k z₀ t).2 i ≠ z₀.2 i := by
  rw [untriggeredCurve_backreacts]
  intro h
  have : t * (c i * z₀.2 k) = 0 := by linarith [sub_eq_self.mp h]
  rcases mul_eq_zero.mp this with h1 | h2
  · exact ht h1
  · rcases mul_eq_zero.mp h2 with h3 | h4
    · exact hc h3
    · exact hz h4

end CSD.SigmaLayer

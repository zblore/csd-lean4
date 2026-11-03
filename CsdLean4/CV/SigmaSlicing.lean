/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.LocalLiebRobinson
public import CsdLean4.CV.RecordInfluence

/-!
# Σ records do not see the ontic order of spacelike writes

**Category:** 3-Local (CV; the record medium on the field arena). BACKLOG #285, part (ii), at the
level of Σ records.

#285 asks whether the ontic time's frame is hidden from records. On the fibred field arena a record
is a definite fact of the one trajectory: the stroke `recordStroke` shifts the record fibre by an
amount read off the base, and the flow moves the base and only rotates the fibre rigidly. No
probability enters, and this file uses none: it is about Σ's records, not about quantum statistics.

Two wings write records in some ontic order. `B`'s operation — a record write, or a write together
with an apparatus kick on the base — happens at ontic time `s`, before `A`'s write at `t`, or after
it, or not at all. What `A` writes is fixed by the base at `t`:

* **a record write leaves the base untouched**, so `B`'s write, before or after, changes nothing
  `A` writes — exactly;
* **an apparatus kick is a change of the base**, and its effect on `A`'s write is the kick's
  influence over the remaining flow time, which the local Lieb–Robinson bound makes at most
  `L_h L_g · 2 max(|Y|, 1) 2^{-d} ‖A‖` outside the cone.

## Main results

* `fibredFlow_add` (the fibred flow is a flow), `base_flow_strokeSnd` (a write between two flow
  steps leaves the base where the flow alone puts it);
* ★★★ `sigma_record_write_order_indep` (**`A`'s Σ record at `t` is the same whether `B` wrote at an
  earlier ontic time or not**: the order of spacelike writes is invisible to `A`'s record, exactly
  and with no light-cone condition);
* ★★★ `sigma_record_kick_order` (**an apparatus kick by `B` at ontic time `s`, before `A`'s write at
  `t`, changes `A`'s Σ record by at most the local Lieb–Robinson bound** — so "kick before" and
  "kick after", the second of which cannot reach `A`'s record, differ by at most that bound;
  `record_influence_le_of_separated_local` restarted at time `s`).

## Honest scope

⚠️ **The arena is the fibred field arena** of `FibredArenaBridge.lean`, with the corpus's record
mechanism (the skew stroke) and a field-structured flow with skew-Hermitian edge terms. The Dirac
chain's radar arenas are single-particle and carry their records in gated registers; carrying this
statement to them needs the chain's own cone bound and is not attempted here.

⚠️ **Permitted influence**: outside the cone the bound is the Lieb–Robinson tail; inside it nothing
is claimed (`RecordInfluence.lean`'s scope note).

References: `specs/BACKLOG.md` #285, #38, #39, #213; `CV/FibredArenaBridge.lean`
(`recordStroke`, `fibredKick`, `FieldStructuredFlow.fibredFlow`); `CV/RecordInfluence.lean`
(`recordStrokeSnd`, `recordStroke_channels_comm`); `CV/LocalLiebRobinson.lean`
(`record_influence_le_of_separated_local`); `CV/FieldStructuredFlow.lean` (`arenaFlow_add`).
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ} (F : FieldStructuredFlow K N)

/-- **The fibred flow is a flow.** -/
theorem fibredFlow_add (ω : ℝ × ℝ) (s t : ℝ) (x : FibredFieldArena K N) :
    F.fibredFlow ω t (F.fibredFlow ω s x) = F.fibredFlow ω (t + s) x := by
  simp only [FieldStructuredFlow.fibredFlow, F.arenaFlow_add]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show x.2.1 + ((s * ω.1 : ℝ) : AddCircle (1 : ℝ)) + ((t * ω.1 : ℝ) : AddCircle (1 : ℝ))
      = x.2.1 + (((t + s) * ω.1 : ℝ) : AddCircle (1 : ℝ))
    rw [add_assoc, ← AddCircle.coe_add]
    congr 2
    ring
  · show x.2.2 + ((s * ω.2 : ℝ) : AddCircle (1 : ℝ)) + ((t * ω.2 : ℝ) : AddCircle (1 : ℝ))
      = x.2.2 + (((t + s) * ω.2 : ℝ) : AddCircle (1 : ℝ))
    rw [add_assoc, ← AddCircle.coe_add]
    congr 2
    ring

/-- **A write between two flow steps leaves the base where the flow alone puts it.** -/
theorem base_flow_strokeSnd (ω : ℝ × ℝ) (s t : ℝ) (B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (g : ℝ → AddCircle (1 : ℝ)) (x : FibredFieldArena K N) :
    (F.fibredFlow ω (t - s) (recordStrokeSnd B g (F.fibredFlow ω s x))).1
      = (F.fibredFlow ω t x).1 := by
  show F.arenaFlow (t - s) (F.arenaFlow s x.1) = F.arenaFlow t x.1
  rw [← F.arenaFlow_add, sub_add_cancel]

/-- ★★★ **The order of spacelike writes is invisible to a Σ record.** `B` writes its record at
ontic time `s` and the trajectory flows on to `t`; or `B` does not write before `t`. Either way `A`
writes at `t` the same value `g_A(⟨A⟩ at the base)` — a write holds the base fixed and the flow
moves only the base and rotates the fibre rigidly. Exact, with no light-cone condition. -/
theorem sigma_record_write_order_indep (ω : ℝ × ℝ) (s t : ℝ)
    (A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) (gA gB : ℝ → AddCircle (1 : ℝ))
    (x : FibredFieldArena K N) :
    gA (arenaObs A (F.fibredFlow ω (t - s) (recordStrokeSnd B gB (F.fibredFlow ω s x))).1)
      = gA (arenaObs A (F.fibredFlow ω t x).1) := by
  rw [base_flow_strokeSnd]

variable [NeZero N] {V : Type*} [SeminormedAddCommGroup V]

/-- ★★★ **An apparatus kick before or after a spacelike record.** `B` kicks the base with `W`
(supported on `Y`, more than `d` hops from `A`'s read region `R`) at ontic time `s`, and the
trajectory flows on to `t`, within the local cone (`localLRVelocity · (t − s) ≤ d`). `A`'s Σ record
at `t` then differs from its value without the kick — which is its value when the kick comes after
`t` — by at most `L_h L_g · 2 max(|Y|, 1) 2^{-d} ‖A‖`. -/
theorem sigma_record_kick_order (hskew : ∀ e ∈ F.edges, (F.piece e)ᴴ = -(F.piece e)) {Δ : ℕ}
    (hdeg : DegreeLE F.edges Δ) {γ : ℝ} (hγ : 0 ≤ γ) (hγE : ∀ e ∈ F.edges, ‖F.piece e‖ ≤ γ)
    (emb : SiteEmbedding K V F.edges) {R Y : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (hA : SupportedOn R A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn Y W.val) {d : ℕ}
    (hd : 1 ≤ d) (hsep : ∀ y ∈ Y, ∀ r ∈ R, (d : ℝ) * emb.hop < ‖emb.pos y - emb.pos r‖)
    {s t : ℝ} (hst : s ≤ t) (hvt : localLRVelocity Δ γ * (t - s) ≤ d)
    {Lh Lg : NNReal} {h : RecordFibre → ℝ} (hh : LipschitzWith Lh h)
    {g : ℝ → RecordFibre} (hg : LipschitzWith Lg g) (ω : ℝ × ℝ) (x : FibredFieldArena K N) :
    |h (recordStroke A g (F.fibredFlow ω (t - s) (fibredKick W (F.fibredFlow ω s x)))).2
        - h (recordStroke A g (F.fibredFlow ω t x)).2|
      ≤ (Lh : ℝ) * (Lg : ℝ) * (2 * max (Y.card : ℝ) 1 * (1 / 2 : ℝ) ^ d * ‖A‖) := by
  have e : F.fibredFlow ω t x = F.fibredFlow ω (t - s) (F.fibredFlow ω s x) := by
    rw [fibredFlow_add, sub_add_cancel]
  rw [e]
  exact record_influence_le_of_separated_local F hskew hdeg hγ hγE emb hA hW hd hsep
    (sub_nonneg.2 hst) hvt hh hg ω (F.fibredFlow ω s x)

end CSD.CV

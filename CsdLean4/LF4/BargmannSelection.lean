import CsdLean4.LF4.UnitarySelection
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Bargmann

/-!
# W3 clopen-datum closure: the Bargmann discriminator

**Category:** 3-Programme (CSD dynamics spine, the W3 staged residual).

W3 (`UnitarySelection.lean`) selected the unitary Wigner branch STAGED on a
clopen datum: `IsClopen {t | ProjUnitary d t}`, the Lean image of
(i) continuity of `t ↦ projectedFlow t` and (ii) the disconnectedness of the
antiunitary component of the Fubini–Study isometry group. This module closes
that datum:

* **(ii) is PROVED.** The Bargmann invariant (the normalised triple product
  `Δ`, `Bargmann.lean`) is preserved by the unitary branch and CONJUGATED by
  the antiunitary branch. On a probe triple with `Im Δ ≠ 0` (exists for
  `N ≥ 2`) the two branches therefore sit at the two DISTINCT values
  `Δ` and `conj Δ` of one scalar observable: they are separated, and the
  Wigner disjunction is EXCLUSIVE (`not_projUnitary_and_projAntiunitary`).
* **(i) is REDUCED to a scalar continuity datum.** If the Bargmann observable
  `t ↦ Δ(Φ_t p, Φ_t q, Φ_t r)` of the flow is continuous, the unitary-time
  set is the preimage of the closed point `{Δ₀}` and its complement the
  preimage of `{conj Δ₀}` — both closed, so the set is CLOPEN
  (`projUnitary_isClopen_of_bargmann_continuous`), and the W3 selection fires
  unconditionally (`projectedFlow_unitary_of_bargmann_continuous`).

The degenerate dimensions need no datum at all: for `N ≤ 1` every
transformation of the (at most one-point) projective space is trivially the
projective unitary `1` (`projUnitary_of_dim_le_one`), so together the clopen
datum is closed at EVERY `N` — unconditionally for `N ≤ 1`, on the scalar
continuity datum for `N ≥ 2`.

## Honest posture (load-bearing)

The remaining hypothesis is `hcont : Continuous (bargmannObservable d p q r)`
— continuity IN `t` of ONE `ℂ`-valued observable of the flow at THREE fixed
probe rays. This is a strictly weaker posit than the compact-open continuity
of `t ↦ projectedFlow t` that (i) named: it follows from it (composing with
the continuity of `Δ` on `ℙ³`, a true statement whose formalisation needs
local sections of `mk` not present in the corpus — the named follow-on), and
it is the exact regularity the selection consumes. A genuine one-parameter
physical flow has continuous observables; the posit is physical, not a
placeholder for missing mathematics about the isometry group. Nothing here
derives continuity from the `KahlerOnticSetup` fields — measure-preservation
does not imply continuity (measure ≠ topology, the same discipline as
measure ≠ metric in W3).

## Non-vacuity

On `trivialKahlerOnticSetup` the Bargmann observable is constant, hence
continuous; with the `N ≥ 2` probe triple the full selection fires
(`trivialKahlerOnticSetup_bargmann_selection`). Genuine, not vacuous.

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no
`busch`, no `sorry`, no `native_decide`, no new axioms. Consumes W3
(`projectedFlow_unitary_or_antiunitary`, `projectedFlow_unitary_of_clopen`)
and the Bargmann layer; Wigner is not re-proved.
-/

open scoped LinearAlgebra.Projectivization
open Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ## The Bargmann observable of the projected flow -/

/-- The Bargmann observable of the projected flow along a fixed probe triple:
`t ↦ Δ(Φ_t p, Φ_t q, Φ_t r)`. One scalar function of time whose value
discriminates the Wigner branches. -/
noncomputable def bargmannObservable (d : KahlerOnticSetup N)
    (p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))) (t : ℝ) : ℂ :=
  bargmann (d.projectedFlow t p) (d.projectedFlow t q) (d.projectedFlow t r)

/-- On the unitary branch the Bargmann observable takes the reference value
`Δ(p,q,r)`. -/
lemma bargmannObservable_of_projUnitary {d : KahlerOnticSetup N} {t : ℝ}
    (h : ProjUnitary d t) (p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    bargmannObservable d p q r t = bargmann p q r := by
  obtain ⟨U, hU⟩ := h
  unfold bargmannObservable
  rw [hU, hU, hU, bargmann_smul_unitary]

/-- On the antiunitary branch the Bargmann observable takes the CONJUGATE
reference value `conj Δ(p,q,r)`. -/
lemma bargmannObservable_of_projAntiunitary {d : KahlerOnticSetup N} {t : ℝ}
    (h : ProjAntiunitary d t) (p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    bargmannObservable d p q r t = (starRingEnd ℂ) (bargmann p q r) := by
  obtain ⟨U, hU⟩ := h
  unfold bargmannObservable
  rw [hU, hU, hU, bargmann_smul_unitary, bargmann_conjProj]

/-- **The Wigner disjunction is exclusive** wherever a probe triple with
`Im Δ ≠ 0` exists: no time-`t` map is both projectively unitary and
projectively antiunitary. (In dimension `≤ 1` both branches DO coincide;
`Im Δ ≠ 0` is exactly the non-degeneracy that separates them.) -/
theorem not_projUnitary_and_projAntiunitary {d : KahlerOnticSetup N} {t : ℝ}
    {p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))} (him : (bargmann p q r).im ≠ 0)
    (h1 : ProjUnitary d t) (h2 : ProjAntiunitary d t) : False := by
  have e1 := bargmannObservable_of_projUnitary h1 p q r
  have e2 := bargmannObservable_of_projAntiunitary h2 p q r
  rw [e1] at e2
  have him2 : (bargmann p q r).im = -(bargmann p q r).im := by
    conv_lhs => rw [e2]
    exact Complex.conj_im _
  apply him
  linarith

/-! ## The clopen datum, derived -/

/-- **The W3 clopen datum, DERIVED.** For a transition-probability-preserving
projected flow whose Bargmann observable along a non-degenerate probe triple
is continuous in `t`, the unitary-time set is clopen: it is the preimage of
the closed singleton `{Δ₀}` and its complement the preimage of `{conj Δ₀}`,
`Δ₀ ≠ conj Δ₀` since `Im Δ₀ ≠ 0`. This discharges (ii) — the branch
separation — outright, and reduces (i) to the scalar continuity hypothesis
`hcont`. -/
theorem projUnitary_isClopen_of_bargmann_continuous
    (d : KahlerOnticSetup N)
    (hTPP : ∀ t, TransProbPreserving (d.projectedFlow t))
    {p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))} (him : (bargmann p q r).im ≠ 0)
    (hcont : Continuous (bargmannObservable d p q r)) :
    IsClopen {t : ℝ | ProjUnitary d t} := by
  have hset : {t : ℝ | ProjUnitary d t}
      = bargmannObservable d p q r ⁻¹' {bargmann p q r} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact bargmannObservable_of_projUnitary h p q r
    · intro he
      rcases projectedFlow_unitary_or_antiunitary d hTPP t with h | h
      · exact h
      · exfalso
        rw [bargmannObservable_of_projAntiunitary h p q r] at he
        apply him
        have him2 : (bargmann p q r).im = -(bargmann p q r).im := by
          conv_lhs => rw [← he]
          exact Complex.conj_im _
        linarith
  have hsetc : {t : ℝ | ProjUnitary d t}ᶜ
      = bargmannObservable d p q r ⁻¹' {(starRingEnd ℂ) (bargmann p q r)} := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · intro h
      rcases projectedFlow_unitary_or_antiunitary d hTPP t with h' | h'
      · exact absurd h' h
      · exact bargmannObservable_of_projAntiunitary h' p q r
    · intro he h
      rw [bargmannObservable_of_projUnitary h p q r] at he
      apply him
      have him2 : (bargmann p q r).im = -(bargmann p q r).im := by
        conv_lhs => rw [he]
        exact Complex.conj_im _
      linarith
  constructor
  · rw [hset]
    exact isClosed_singleton.preimage hcont
  · rw [← isClosed_compl_iff, hsetc]
    exact isClosed_singleton.preimage hcont

/-- **The W3 unitary selection, on the Bargmann continuity datum.** For a
transition-probability-preserving projected flow that is unitary at `t = 0`
and whose Bargmann observable along a non-degenerate probe triple is
continuous, EVERY time-`t` map is on the unitary branch. The staged clopen
hypothesis of `projectedFlow_unitary_of_clopen` is now derived, not
posited. -/
theorem projectedFlow_unitary_of_bargmann_continuous
    (d : KahlerOnticSetup N)
    (hTPP : ∀ t, TransProbPreserving (d.projectedFlow t))
    (h0 : ProjUnitary d 0)
    {p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))} (him : (bargmann p q r).im ≠ 0)
    (hcont : Continuous (bargmannObservable d p q r)) :
    ∀ t, ProjUnitary d t :=
  projectedFlow_unitary_of_clopen d h0
    (projUnitary_isClopen_of_bargmann_continuous d hTPP him hcont)

/-! ## The degenerate dimensions (`N ≤ 1`): no datum needed -/

/-- For `N ≤ 1` the projective space has at most one point. -/
lemma projectivization_subsingleton (hN : N ≤ 1) :
    ∀ p q : ℙ ℂ (EuclideanSpace ℂ (Fin N)), p = q := by
  intro p q
  interval_cases N
  · -- `N = 0`: the projective space is empty (no nonzero vectors).
    refine absurd ?_ p.rep_nonzero
    ext k
    exact k.elim0
  · -- `N = 1`: any two nonzero vectors are colinear.
    conv_lhs => rw [← p.mk_rep]
    conv_rhs => rw [← q.mk_rep]
    rw [Projectivization.mk_eq_mk_iff' ℂ _ _ p.rep_nonzero q.rep_nonzero]
    have hq0 : q.rep 0 ≠ 0 := by
      intro h0
      apply q.rep_nonzero
      ext k
      rw [Subsingleton.elim k (0 : Fin 1)]
      exact h0
    refine ⟨p.rep 0 / q.rep 0, ?_⟩
    ext k
    rw [Subsingleton.elim k (0 : Fin 1)]
    show (p.rep 0 / q.rep 0) * q.rep 0 = p.rep 0
    exact div_mul_cancel₀ _ hq0

/-- **The degenerate case needs no datum:** for `N ≤ 1` every self-map of the
(at most one-point) projective space — in particular every time-`t` projected
flow map — is realised by the projective unitary `1`. Together with the
Bargmann route for `N ≥ 2`, the W3 clopen datum is closed at every `N`. -/
theorem projUnitary_of_dim_le_one (hN : N ≤ 1)
    (d : KahlerOnticSetup N) (t : ℝ) : ProjUnitary d t := by
  refine ⟨1, fun p => ?_⟩
  rw [one_smul]
  exact projectivization_subsingleton hN _ p

/-! ## Non-vacuity on the `trivialKahlerOnticSetup` witness -/

/-- The Bargmann selection FIRES on the inhabitation witness (`N ≥ 2`): the
identity flow's Bargmann observable is constant (hence continuous), the
probe triple exists, `t = 0` is unitary, and the conclusion — unitary at
every time — is genuine. Confirms the hypotheses of
`projectedFlow_unitary_of_bargmann_continuous` are jointly satisfiable. -/
theorem trivialKahlerOnticSetup_bargmann_selection
    (hN : 2 ≤ N) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ∀ t, ProjUnitary (trivialKahlerOnticSetup N p₀) t := by
  obtain ⟨p, q, r, him⟩ := exists_bargmann_im_ne_zero hN
  refine projectedFlow_unitary_of_bargmann_continuous
    (trivialKahlerOnticSetup N p₀)
    (trivialKahlerOnticSetup_transProbPreserving N p₀)
    (trivialKahlerOnticSetup_projUnitary N p₀ 0) him ?_
  show Continuous fun _ : ℝ => bargmann p q r
  exact continuous_const

end LF4
end CSD

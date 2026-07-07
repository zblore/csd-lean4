import CsdLean4.LF4.KahlerOnticSetup
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity

/-!
# W3: the Wigner selection on a Kähler ontic setup

This module consumes W1 (the Wigner / Fubini-Study rigidity converse,
`Projectivization.wigner_rigidity_unitaryGroup`) through the W2 sector interface
`KahlerOnticSetup N`. It delivers, for a transition-probability-preserving
projected flow, the honest Wigner disjunction (each time-`t` map is realised by a
unitary OR an antiunitary), and the continuous-one-parameter-from-identity
refinement that selects the UNITARY branch.

## The measure ≠ metric scoping (load-bearing, do NOT violate)

The W2 interface asserts `flow_preserves_volume` (Liouville / measure
preservation) and `projectable` (a bare descent equation
`pi (flow t x) = projectedFlow t (pi x)`). It does **NOT** assert that
`projectedFlow t` preserves TRANSITION PROBABILITIES. Measure-preservation does
**not** imply transition-probability preservation (measure ≠ metric): a
measure-preserving map of `ℂℙ^{N-1}` need not be a Fubini-Study isometry. So W3
takes transition-probability preservation as an explicit HYPOTHESIS

    `hTPP : ∀ t, Projectivization.TransProbPreserving (d.projectedFlow t)`

the physical FS-isometry posit. It is **NOT** derived from
`flow_preserves_volume`; deriving it would be the exact §13.2 trap.

## What is proved vs staged

* `projectedFlow_unitary_or_antiunitary` (PROVED): the Wigner disjunction per
  `t`, the direct consumption of W1 by the interface. Genuine: the antiunitary
  branch (`ProjAntiunitary`, via `conjProj`) is not dropped.
* `projectedFlow_unitary_of_clopen` (PROVED, staged refinement): from the clopen
  hypothesis on the unitary-time set plus one unitary time, connectedness of `ℝ`
  (`PreconnectedSpace ℝ`) forces the whole real line into the unitary branch. The
  identity at `t = 0` is unitary, so this excludes the antiunitary branch for a
  genuine one-parameter flow.

The clopen hypothesis is the honest STAGED residual. It is the Lean-level image of
two topological facts NOT in Mathlib for this space:

  (i) `t ↦ d.projectedFlow t` is continuous into the self-maps of `ℂℙ^{N-1}`
      (compact-open topology) — the genuine-one-parameter-flow content;
  (ii) the projective unitary group `PU(N)` is a clopen subgroup of the full
      Fubini-Study isometry (semi-unitary) group, i.e. the antiunitary coset is a
      separated component disjoint from the identity component.

Given (i)+(ii) the branch selector `ℝ → Bool` is continuous, so
`{t | ProjUnitary d t}` is clopen. Neither (i) nor (ii) is formalised in the
corpus; W3 takes their consequence (clopen-ness) as the explicit hypothesis and
discharges the connectedness step (`IsClopen.eq_univ` on `ℝ`). The topological
residual named precisely is exactly (i)+(ii): the continuity of the one-parameter
family and the disconnectedness of the antiunitary component. There is no `sorry`
and no axiom; the unitary-branch SELECTION is STAGED on the clopen datum, not
claimed unconditionally.

**Datum closure (2026-07-07, `LF4/BargmannSelection.lean`):** (ii) is now
PROVED — the Bargmann invariant separates the branches (`Δ` vs `conj Δ` on a
probe triple with `Im Δ ≠ 0`, which exists for `N ≥ 2`) — and (i) is REDUCED
to the scalar datum "the Bargmann observable `t ↦ Δ(Φ_t p, Φ_t q, Φ_t r)` is
continuous": `projUnitary_isClopen_of_bargmann_continuous` DERIVES the clopen
hypothesis, and `projectedFlow_unitary_of_bargmann_continuous` runs the
selection on it. For `N ≤ 1` no datum is needed
(`projUnitary_of_dim_le_one`). This module's clopen-hypothesis form remains
the general interface the closure feeds.

## Non-vacuity

`trivialKahlerOnticSetup` (identity flow) satisfies `hTPP` (the identity is
transition-probability preserving) and the conclusion is genuine (the identity is
the projective unitary `1`, not vacuously true). The clopen hypothesis holds
(the unitary-time set is all of `ℝ`), so the refinement fires.

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no `busch`,
no `sorry`, no `native_decide`, no new axioms. Reuses `wigner_rigidity_unitaryGroup`,
`conjProj`, and the W2 `KahlerOnticSetup`; Wigner is not re-proved.
-/

open MeasureTheory
open scoped LinearAlgebra.Projectivization
open Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- The time-`t` projected flow is realised by a projective **unitary**: there is
`U : Matrix.unitaryGroup (Fin N) ℂ` with `d.projectedFlow t p = U • p` for all `p`.
This is the unitary branch of the Wigner disjunction. -/
def ProjUnitary (d : KahlerOnticSetup N) (t : ℝ) : Prop :=
  ∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, d.projectedFlow t p = U • p

/-- The time-`t` projected flow is realised by an **antiunitary**: there is
`U : Matrix.unitaryGroup (Fin N) ℂ` with `d.projectedFlow t p = U • conjProj p`
for all `p`, where `conjProj` is coordinatewise complex conjugation (the
concrete antiunitary witness from `WignerRigidity`). This is the antiunitary
branch of the Wigner disjunction. -/
def ProjAntiunitary (d : KahlerOnticSetup N) (t : ℝ) : Prop :=
  ∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, d.projectedFlow t p = U • conjProj p

/-- **The Wigner selection (core, PROVED).** For a transition-probability-
preserving projected flow, each time-`t` map is realised by a unitary OR an
antiunitary. The direct consumption of W1 (`wigner_rigidity_unitaryGroup`) by
the W2 interface; the honest per-`t` disjunction, antiunitary branch genuine.

`hTPP` is a HYPOTHESIS (the FS-isometry posit), NOT derived from the interface's
`flow_preserves_volume` (measure ≠ metric). -/
theorem projectedFlow_unitary_or_antiunitary
    (d : KahlerOnticSetup N)
    (hTPP : ∀ t, TransProbPreserving (d.projectedFlow t)) (t : ℝ) :
    ProjUnitary d t ∨ ProjAntiunitary d t :=
  wigner_rigidity_unitaryGroup (hTPP t)

/-- **The continuous-from-identity refinement (PROVED, STAGED on the clopen
datum).** If the set of times at which the projected flow is unitary is clopen
and inhabited (e.g. by `t = 0`, the identity), then by connectedness of `ℝ` the
flow is unitary at every time. This EXCLUDES the antiunitary branch for a genuine
one-parameter flow from the identity.

The clopen hypothesis is the STAGED topological residual: it is the consequence of
(i) continuity of `t ↦ d.projectedFlow t` and (ii) the disconnectedness of the
antiunitary component of the Fubini-Study isometry group, neither of which is
formalised in the corpus (see the module docstring). The connectedness step
itself is discharged here via `IsClopen.eq_univ` on `PreconnectedSpace ℝ`. -/
theorem projectedFlow_unitary_of_clopen
    (d : KahlerOnticSetup N)
    (h0 : ProjUnitary d 0)
    (hclopen : IsClopen {t : ℝ | ProjUnitary d t}) :
    ∀ t, ProjUnitary d t := by
  have huniv : {t : ℝ | ProjUnitary d t} = Set.univ :=
    hclopen.eq_univ ⟨0, h0⟩
  intro t
  have ht : t ∈ {t : ℝ | ProjUnitary d t} := by rw [huniv]; trivial
  exact ht

/-! ## Non-vacuity on the `trivialKahlerOnticSetup` witness -/

/-- The identity flow of the inhabitation witness is transition-probability
preserving (`projectedFlow t = id`, and the identity preserves `transProb`
definitionally). Confirms the `hTPP` hypothesis is satisfiable. -/
theorem trivialKahlerOnticSetup_transProbPreserving
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) (t : ℝ) :
    TransProbPreserving ((trivialKahlerOnticSetup N p₀).projectedFlow t) :=
  fun _ _ => rfl

/-- On the inhabitation witness, the projected flow is unitary at every time: the
identity is the projective unitary `1`. This is GENUINE (`id = (1 : _) • ·`), not
a vacuous instance of `ProjUnitary`. -/
theorem trivialKahlerOnticSetup_projUnitary
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) (t : ℝ) :
    ProjUnitary (trivialKahlerOnticSetup N p₀) t := by
  refine ⟨1, fun p => ?_⟩
  have hid : (trivialKahlerOnticSetup N p₀).projectedFlow t p = p := rfl
  rw [hid, one_smul]

/-- The Wigner disjunction lands genuinely on the UNITARY branch for the
inhabitation witness (`Or.inl`, not `Or.inr`). Confirms the disjunction is
non-vacuous. -/
theorem trivialKahlerOnticSetup_unitary_or_antiunitary
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) (t : ℝ) :
    ProjUnitary (trivialKahlerOnticSetup N p₀) t
      ∨ ProjAntiunitary (trivialKahlerOnticSetup N p₀) t :=
  Or.inl (trivialKahlerOnticSetup_projUnitary N p₀ t)

/-- The staged refinement FIRES on the inhabitation witness: its clopen
hypothesis holds (the unitary-time set is all of `ℝ`), the identity is unitary at
`t = 0`, and the conclusion (unitary at every time) is genuine. Confirms the
refinement's hypotheses are jointly satisfiable and non-vacuous. -/
theorem trivialKahlerOnticSetup_unitary_of_clopen
    (N : ℕ) (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ∀ t, ProjUnitary (trivialKahlerOnticSetup N p₀) t := by
  refine projectedFlow_unitary_of_clopen (trivialKahlerOnticSetup N p₀)
    (trivialKahlerOnticSetup_projUnitary N p₀ 0) ?_
  have huniv : {t : ℝ | ProjUnitary (trivialKahlerOnticSetup N p₀) t} = Set.univ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact trivialKahlerOnticSetup_projUnitary N p₀ t
  rw [huniv]
  exact isClopen_univ

end LF4
end CSD

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.FibredArenaBridge

/-!
# ST-1: the influence preorder on records

**Category:** 3-Local (CV; the first theorem about *records* with a causal shape).
BACKLOG #38, brick `ST-1` of [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md).

The CV chain states causality about **operators** (`SupportedOn`, commutators, the Lieb–Robinson
cone); [`FibredArenaBridge.lean`](FibredArenaBridge.lean) carried it to the **record** medium with an
error bound. This module states it as a **relation between read regions** and proves the three things
the scoping note asked of `ST-1`: the relation is a preorder in the period count, spacelike records
are jointly measurable and unsteerable from one another, and their joint law factors.

* `Influences E S₁ S₂ n` — **the record of a context reading `S₁` can influence the record of a
  context reading `S₂` within `n` interacting periods**, defined as `S₂ ⊆ graphBall E S₁ n`;
  ★ `influences_refl`, ★ `influences_mono`, ★★ `influences_trans` (the periods add, via the new
  `graphBall_add` and `graphBall_subset_of_subset`), ★ `influences_trans_le`;
* `Spacelike E R T n` — neither cone has reached the other; ★ `spacelike_of_le` (antitone in the
  period count), ★ `not_influences_of_spacelike`;
* ★★ `commute_record_of_spacelike` — **spacelike records are jointly measurable**: their evolved
  observables commute, so the record layer may assign them outcomes at once;
* ★★★ `arenaObs_heisenberg_kick_of_spacelike` and
  ★★★ `recordStroke_heisenberg_comm_kick_of_spacelike` — **a record outside the cone cannot be
  steered, exactly**. `record_lightcone` is the continuous-time statement with a Lieb–Robinson
  error; in discrete periods the evolved observable's support sits inside the cone on the nose, so
  the record's reading and the record *write* are unchanged with no error term at all;
* `recordStroke₂` — two records written into the two channels of the `T²` fibre, with
  ★★ `recordStroke_channels_comm` (either order, same point: a write holds the base fixed) and
  ★★★ `map_recordStroke₂_prod` — **the joint record law is the product law of the medium**, for any
  translation-invariant channel law. The medium contributes neither correlation nor bias, so a
  correlation between two records is a fact about their base readings.

## Honest scope

⚠️ **This is not emergent spacetime, and it is not a metric.** `Influences` is the causal shape the
**assumed** coupling graph `E` defines on mode regions, with the period count as the only notion of
duration. There is no light speed, no Lorentzian signature, no continuum, and no derivation of `E`
from anything. The scoping note's finding stands: what is missing for emergence proper is **which
coarse-graining projection defines the macroscopic coordinates** (Paper D §5.2), and that is a
decision for the author rather than a lemma. Finiteness of the arena is not what stands in the way
— it bounds what is defined *directly* from `Σ`, not what can arise after coarse-graining over many
records.

⚠️ **"Record" here is the corpus's record mechanism**, the skew stroke of
`RecordLayer/ShearWitness.lean` as carried to the field arena by `FibredArenaBridge.lean`: a
base-dependent shift of the fibre, read through a region-supported arena observable. Contexts enter
only through their read regions and their write maps.

⚠️ **The factoring theorem is about the medium, not about the state.** `map_recordStroke₂_prod`
says the fibre contributes no correlation; it does *not* say two spacelike records are statistically
independent, which would also need the base readings to be independent — a statement about the
preparation (a product point), and one that needs a tensor factorisation of the field space over a
mode partition that the corpus does not have. Saying more than this would be the mistake the scoping
note was written to avoid.

⚠️ Discrete periods of the *fixed* interacting unitary `graphInteractingU`, and `Finset`-indexed
mode regions at a finite cutoff.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-1`;
`CV/SupportSpreading.lean` (`graphBall`, `commute_heisenberg_graphInteractingU_pow`);
`CV/FibredArenaBridge.lean` (`recordStroke`, `record_lightcone`);
`RecordLayer/ShearWitness.lean` (the stroke this is about); `specs/BACKLOG.md` #38 and #39.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CSD.CV

variable {K N : ℕ}

/-! ### The light cone is monotone in its region -/

theorem graphNeighborhood_subset_of_subset (E : Finset (Fin K × Fin K))
    {R S : Finset (Fin K)} (h : R ⊆ S) :
    graphNeighborhood E R ⊆ graphNeighborhood E S := by
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · exact Finset.mem_union_left _ (h hk)
  · obtain ⟨e, he, hke⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨heE, hte⟩ := Finset.mem_filter.mp he
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨e, Finset.mem_filter.mpr ⟨heE, ?_⟩, hke⟩)
    rcases hte with h1 | h2
    · exact Or.inl (h h1)
    · exact Or.inr (h h2)

theorem graphBall_subset_of_subset (E : Finset (Fin K × Fin K))
    {R S : Finset (Fin K)} (h : R ⊆ S) (n : ℕ) :
    graphBall E R n ⊆ graphBall E S n := by
  induction n with
  | zero => exact h
  | succ n ih => exact graphNeighborhood_subset_of_subset E ih

/-- The cones compose: `m` periods then `n` more is `m + n` periods. -/
theorem graphBall_add (E : Finset (Fin K × Fin K)) (R : Finset (Fin K)) (m n : ℕ) :
    graphBall E R (m + n) = graphBall E (graphBall E R m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from by ring, graphBall_succ, graphBall_succ, ih]

/-! ### The influence relation on read regions -/

/-- **Influence within `n` periods.** The record of a context that reads the mode region `S₁` can
influence the record of a context that reads `S₂` within `n` interacting periods exactly when `S₂`
lies in the coupling graph's `n`-ball around `S₁`.

⚠️ This is the causal shape **the coupling graph defines**, relative to an assumed `E`. It is not a
metric, not a Lorentzian structure, and not emergent spacetime: see the module docstring. -/
def Influences (E : Finset (Fin K × Fin K)) (S₁ S₂ : Finset (Fin K)) (n : ℕ) : Prop :=
  S₂ ⊆ graphBall E S₁ n

/-- ★ **Reflexive at zero periods**: a record influences itself, now. -/
theorem influences_refl (E : Finset (Fin K × Fin K)) (S : Finset (Fin K)) :
    Influences E S S 0 := by
  rw [Influences, graphBall_zero]

/-- ★ **Monotone in the period count**: more time can only add influence. -/
theorem influences_mono {E : Finset (Fin K × Fin K)} {S₁ S₂ : Finset (Fin K)} {m n : ℕ}
    (h : Influences E S₁ S₂ m) (hmn : m ≤ n) : Influences E S₁ S₂ n :=
  h.trans (graphBall_mono E S₁ hmn)

/-- ★★ **Transitive, with the periods adding**: influence composes along the graph, which is what
makes the relation a preorder on regions once the period count is carried. -/
theorem influences_trans {E : Finset (Fin K × Fin K)} {S₁ S₂ S₃ : Finset (Fin K)} {m n : ℕ}
    (h₁ : Influences E S₁ S₂ m) (h₂ : Influences E S₂ S₃ n) :
    Influences E S₁ S₃ (m + n) := by
  rw [Influences, graphBall_add]
  exact h₂.trans (graphBall_subset_of_subset E h₁ n)

/-- ★ **The relation at a fixed budget is a preorder**, once "within `n`" is read as "within at most
`n`": reflexivity is the zero ball and transitivity is `influences_trans` followed by
`influences_mono`. -/
theorem influences_trans_le {E : Finset (Fin K × Fin K)} {S₁ S₂ S₃ : Finset (Fin K)} {m n p : ℕ}
    (h₁ : Influences E S₁ S₂ m) (h₂ : Influences E S₂ S₃ n) (hp : m + n ≤ p) :
    Influences E S₁ S₃ p :=
  influences_mono (influences_trans h₁ h₂) hp

/-! ### Spacelike regions -/

/-- **Spacelike at `n` periods**: neither region's light cone has reached the other's, so neither
record can influence the other within `n` periods. -/
def Spacelike (E : Finset (Fin K × Fin K)) (R T : Finset (Fin K)) (n : ℕ) : Prop :=
  Disjoint (graphBall E R n) (graphBall E T n)

theorem spacelike_symm {E : Finset (Fin K × Fin K)} {R T : Finset (Fin K)} {n : ℕ}
    (h : Spacelike E R T n) : Spacelike E T R n := h.symm

/-- ★ **Spacelike is antitone in the period count**: if the cones have not met by `n`, they had not
met earlier either. -/
theorem spacelike_of_le {E : Finset (Fin K × Fin K)} {R T : Finset (Fin K)} {m n : ℕ}
    (h : Spacelike E R T n) (hmn : m ≤ n) : Spacelike E R T m :=
  Finset.disjoint_of_subset_left (graphBall_mono E R hmn)
    (Finset.disjoint_of_subset_right (graphBall_mono E T hmn) h)

/-- The region sits inside its own cone. -/
theorem subset_graphBall (E : Finset (Fin K × Fin K)) (R : Finset (Fin K)) (n : ℕ) :
    R ⊆ graphBall E R n := by
  simpa using graphBall_mono E R (Nat.zero_le n)

/-- ★ **Spacelike regions do not influence one another** — the relation and its negation line up,
provided the target region is actually there to be influenced. -/
theorem not_influences_of_spacelike {E : Finset (Fin K × Fin K)} {R T : Finset (Fin K)} {n : ℕ}
    (h : Spacelike E R T n) (hT : T.Nonempty) : ¬Influences E R T n := by
  intro hinf
  obtain ⟨k, hk⟩ := hT
  exact (Finset.disjoint_left.mp h (hinf hk)) (subset_graphBall E T n hk)

/-- A kick on a spacelike region is disjoint from the record's cone. -/
theorem disjoint_graphBall_of_spacelike {E : Finset (Fin K × Fin K)} {R T : Finset (Fin K)}
    {n : ℕ} (h : Spacelike E R T n) : Disjoint (graphBall E R n) T :=
  Finset.disjoint_of_subset_right (subset_graphBall E T n) h

/-! ### Spacelike records commute -/

/-- ★★ **Spacelike records are jointly measurable.** Two contexts whose read regions are spacelike
at `n` periods have commuting evolved observables, so the record layer may assign them outcomes
simultaneously — `commute_heisenberg_graphInteractingU_pow` read in the influence vocabulary. -/
theorem commute_record_of_spacelike {R T : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ lam : ℝ)
    (E : Finset (Fin K × Fin K)) (g : Fin K × Fin K → Fin N → Fin N → ℝ) (n : ℕ)
    (hRT : Spacelike E R T n) (hA : SupportedOn R A) (hB : SupportedOn T B) :
    heisenberg (graphInteractingU K N τ lam E g ^ n) A
        * heisenberg (graphInteractingU K N τ lam E g ^ n) B
      = heisenberg (graphInteractingU K N τ lam E g ^ n) B
        * heisenberg (graphInteractingU K N τ lam E g ^ n) A :=
  commute_heisenberg_graphInteractingU_pow τ lam E g n hRT hA hB

/-! ### A record outside the cone cannot be steered — exactly -/

/-- ★★★ **The exact discrete record cone.** A kick supported on a region spacelike from the
record's read region leaves the record's base reading **exactly** unchanged, after any number of
interacting periods. `record_lightcone` of `FibredArenaBridge.lean` is the continuous-time
statement with a Lieb–Robinson error; this is the discrete-time statement with no error at all,
because the support of the evolved observable is contained in the cone on the nose. -/
theorem arenaObs_heisenberg_kick_of_spacelike [NeZero N] {R T : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ lam : ℝ)
    (E : Finset (Fin K × Fin K)) (g : Fin K × Fin K → Fin N → Fin N → ℝ) (n : ℕ)
    (hRT : Spacelike E R T n) (hA : SupportedOn R A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn T W.val)
    (p : FieldArena K N) :
    arenaObs (heisenberg (graphInteractingU K N τ lam E g ^ n) A) (arenaKick W p)
      = arenaObs (heisenberg (graphInteractingU K N τ lam E g ^ n) A) p :=
  arenaObs_kick_of_disjointSupport (disjoint_graphBall_of_spacelike hRT)
    (heisenberg_graphInteractingU_pow_supportedOn τ lam E g n hA) hW p

/-- ★★★ **The record write is unsteerable from outside the cone.** Kick a spacelike region and
write the record, or write it and then kick: the same point of the fibred arena, exactly. -/
theorem recordStroke_heisenberg_comm_kick_of_spacelike [NeZero N] {R T : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ lam : ℝ)
    (E : Finset (Fin K × Fin K)) (gc : Fin K × Fin K → Fin N → Fin N → ℝ) (n : ℕ)
    (hRT : Spacelike E R T n) (hA : SupportedOn R A)
    {W : Matrix.unitaryGroup (FieldConfig K N) ℂ} (hW : SupportedOn T W.val)
    (g : ℝ → RecordFibre) (x : FibredFieldArena K N) :
    recordStroke (heisenberg (graphInteractingU K N τ lam E gc ^ n) A) g (fibredKick W x)
      = fibredKick W (recordStroke (heisenberg (graphInteractingU K N τ lam E gc ^ n) A) g x) :=
  recordStroke_comm_kick (disjoint_graphBall_of_spacelike hRT)
    (heisenberg_graphInteractingU_pow_supportedOn τ lam E gc n hA) hW g x

/-! ### Two records in the two channels of the fibre -/

/-- Two records written into the two coordinates of the `T²` fibre: one context reads `A₁` and
shifts the first circle, the other reads `A₂` and shifts the second. -/
def recordStroke₂ (A₁ A₂ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (g₁ g₂ : ℝ → AddCircle (1 : ℝ)) (x : FibredFieldArena K N) : FibredFieldArena K N :=
  (x.1, (x.2.1 + g₁ (arenaObs A₁ x.1), x.2.2 + g₂ (arenaObs A₂ x.1)))

/-- The first channel alone. -/
def recordStrokeFst (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (g : ℝ → AddCircle (1 : ℝ)) (x : FibredFieldArena K N) : FibredFieldArena K N :=
  (x.1, (x.2.1 + g (arenaObs A x.1), x.2.2))

/-- The second channel alone. -/
def recordStrokeSnd (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (g : ℝ → AddCircle (1 : ℝ)) (x : FibredFieldArena K N) : FibredFieldArena K N :=
  (x.1, (x.2.1, x.2.2 + g (arenaObs A x.1)))

/-- ★★ **The two channels commute, and their composite is the joint write.** Neither order of
writing is privileged: a record write holds the base fixed, so the second write reads exactly what
the first one read. -/
theorem recordStroke_channels_comm (A₁ A₂ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (g₁ g₂ : ℝ → AddCircle (1 : ℝ)) (x : FibredFieldArena K N) :
    recordStrokeFst A₁ g₁ (recordStrokeSnd A₂ g₂ x)
        = recordStrokeSnd A₂ g₂ (recordStrokeFst A₁ g₁ x)
      ∧ recordStrokeFst A₁ g₁ (recordStrokeSnd A₂ g₂ x) = recordStroke₂ A₁ A₂ g₁ g₂ x :=
  ⟨rfl, rfl⟩

/-! ### The record medium adds no correlation -/

/-- The fibre part of the joint write, at a fixed base point. -/
def fibreShift (a b : AddCircle (1 : ℝ)) (θ : RecordFibre) : RecordFibre := (θ.1 + a, θ.2 + b)

theorem recordStroke₂_fibre (A₁ A₂ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (g₁ g₂ : ℝ → AddCircle (1 : ℝ)) (x : FibredFieldArena K N) :
    (recordStroke₂ A₁ A₂ g₁ g₂ x).2
      = fibreShift (g₁ (arenaObs A₁ x.1)) (g₂ (arenaObs A₂ x.1)) x.2 := rfl

/-- ★★ **The record medium adds no correlation and no bias.** For any translation-invariant law `μ`
on a channel — Haar being the case the corpus uses — the joint law of the two channels is the
product `μ ⊗ μ`, and the joint write preserves it: whatever the two contexts read, the pair of
records is distributed exactly as the untouched medium was. -/
theorem measurePreserving_fibreShift {μ : Measure (AddCircle (1 : ℝ))}
    [μ.IsAddRightInvariant] [SFinite μ] (a b : AddCircle (1 : ℝ)) :
    MeasurePreserving (fibreShift a b) (μ.prod μ) (μ.prod μ) := by
  have hfun : fibreShift a b = Prod.map (fun θ : AddCircle (1 : ℝ) => θ + a)
      (fun θ : AddCircle (1 : ℝ) => θ + b) := by
    funext θ
    rfl
  rw [hfun]
  exact (measurePreserving_add_right μ a).prod (measurePreserving_add_right μ b)

/-- ★★★ **The joint record law of two records factors.** At every base point, the law of the pair of
records written by two contexts into the two channels of the fibre is the product law `μ ⊗ μ` of the
medium — independent channels, each unbiased. So any correlation between two records lives in their
base readings, never in the medium; and when the read regions are spacelike, those readings are
jointly measurable (`commute_record_of_spacelike`) and neither is steerable from the other's region
(`recordStroke_heisenberg_comm_kick_of_spacelike`). That is the causal package the influence
preorder was defined for. -/
theorem map_recordStroke₂_prod {μ : Measure (AddCircle (1 : ℝ))}
    [μ.IsAddRightInvariant] [SFinite μ]
    (A₁ A₂ : Matrix (FieldConfig K N) (FieldConfig K N) ℂ)
    (g₁ g₂ : ℝ → AddCircle (1 : ℝ)) (p : FieldArena K N) :
    Measure.map (fun θ : RecordFibre => (recordStroke₂ A₁ A₂ g₁ g₂ (p, θ)).2) (μ.prod μ)
      = μ.prod μ := by
  have hfun : (fun θ : RecordFibre => (recordStroke₂ A₁ A₂ g₁ g₂ (p, θ)).2)
      = fibreShift (g₁ (arenaObs A₁ p)) (g₂ (arenaObs A₂ p)) := by
    funext θ
    rfl
  rw [hfun]
  exact (measurePreserving_fibreShift _ _).map_eq

end CSD.CV

end

end

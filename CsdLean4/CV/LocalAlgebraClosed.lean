/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.SupportSpreading
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# CV-11: the non-diagonal light cone — exp-closure of the local algebra

**Category:** CV (continuous variables — the multi-mode field).

CV-8's light cone covered diagonal (density) couplings. This module removes
that restriction: the local algebra is **topologically closed**, so the
exponential of a locally supported generator is locally supported, and the
coupling-graph light cone extends to kicked drives with **arbitrary —
non-diagonal, hopping — local kicks**.

* `SupportedOn.zero`, `localSubmodule T`, `localAlgebra T` — the local
  algebra packaged as a `Submodule`/`Subalgebra` (from the CV-8 closure
  lemmas), with `isClosed_localSubmodule`: a subspace of a
  finite-dimensional matrix space is closed.
* ★ `SupportedOn.exp` — **exp-closure**: `exp` of a `T`-supported matrix is
  `T`-supported (every partial sum of the exponential series lives in the
  algebra; the limit stays by closedness).
* `KickData` / `KickData.ofGenerator` — a local kick as a unitary supported
  on an edge; the smart constructor builds it from any skew-Hermitian
  edge-supported generator (`expKick_unitary` + exp-closure), so hopping
  generators like `i(a†ₖaₗ − a†ₗaₖ)` are now admissible.
* `kickFoldStep` / `kickFold` — the per-period support growth of a kick
  LIST: each kick enlarges the region by its edge exactly when it touches
  (`heisenberg_eq_of_disjoint` keeps untouched kicks trivial), and
  sequential kicks may chain within a period — the fold records that
  honestly. For a single kick, or kicks touching disjoint regions, the
  fold reduces to CV-8's `graphNeighborhood`-style growth.
* ★★ `heisenberg_kickedStep_pow_supportedOn` — **the non-diagonal light
  cone**: after `n` periods of the kicked drive (free step + the kick
  list), support lies inside the `n`-fold `kickFold` ball. With
  `commute_heisenberg_kickedStep_pow`: observables whose fold-balls stay
  disjoint still commute — locality survives arbitrary local kicks.

⚠️ Honest scope: kicked drives only. The light cone for the full
`exp(-(iτ)(H_free + V))` with a non-commuting non-diagonal `V` is genuine
Lieb–Robinson (velocity bounds from commutator norms) — the promoted
Stage-5 goal (`specs/eft-stage4-plan.md`, horizon note), not claimed here.
Norms/topology: the scoped `Matrix.Norms.L2Operator` instances, used only
internally (the statements are topology-free).

## References

`CV/LocalAlgebra.lean` (CV-8 (i), the closure lemmas);
`CV/SupportSpreading.lean` (CV-8 (ii)–(iv), `heisenberg_supportedOn_union`,
`heisenberg_eq_of_disjoint`); `specs/eft-stage4-plan.md` (row CV-11);
`specs/future-work.md`.
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {K N : ℕ}

/-! ### The local algebra, packaged -/

/-- The zero matrix is supported on every region. -/
protected theorem SupportedOn.zero {S : Finset (Fin K)} :
    SupportedOn S (0 : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) := by
  constructor
  · intro c d k _ _
    rfl
  · intro c d c' d' _ _ _ _
    rfl

/-- The local algebra as a `ℂ`-submodule. -/
def localSubmodule (T : Finset (Fin K)) :
    Submodule ℂ (Matrix (FieldConfig K N) (FieldConfig K N) ℂ) where
  carrier := {A | SupportedOn T A}
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := SupportedOn.zero
  smul_mem' := fun c _ hA => hA.smul c

/-- The local algebra as a `ℂ`-subalgebra. -/
def localAlgebra (T : Finset (Fin K)) :
    Subalgebra ℂ (Matrix (FieldConfig K N) (FieldConfig K N) ℂ) where
  carrier := {A | SupportedOn T A}
  add_mem' := fun ha hb => ha.add hb
  mul_mem' := fun ha hb => ha.mul hb
  algebraMap_mem' := fun r => by
    show SupportedOn T (algebraMap ℂ _ r)
    rw [Algebra.algebraMap_eq_smul_one]
    exact SupportedOn.one.smul r

/-- Membership in the local algebra IS the support condition. -/
@[simp] lemma mem_localAlgebra {T : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} :
    A ∈ localAlgebra T ↔ SupportedOn T A := Iff.rfl

/-- **The local algebra is topologically closed** — a subspace of a
finite-dimensional matrix space. -/
theorem isClosed_localSubmodule (T : Finset (Fin K)) :
    IsClosed ((localSubmodule (K := K) (N := N) T) : Set
      (Matrix (FieldConfig K N) (FieldConfig K N) ℂ)) :=
  Submodule.closed_of_finiteDimensional _

/-! ### Exp-closure -/

/-- Powers of a supported matrix are supported. -/
protected theorem SupportedOn.pow {T : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn T A) (n : ℕ) : SupportedOn T (A ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact SupportedOn.one
  | succ n ih => rw [pow_succ]; exact ih.mul hA

/-- ★ **Exp-closure of the local algebra**: the exponential of a
`T`-supported matrix is `T`-supported. Every partial sum of the exponential
series lives in the algebra; the limit stays by closedness. -/
protected theorem SupportedOn.exp {T : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn T A) : SupportedOn T (exp A) := by
  have hsum := exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hmem : ∀ n : ℕ,
      ((n.factorial : ℂ)⁻¹ • A ^ n) ∈ localSubmodule (K := K) (N := N) T :=
    fun n => Submodule.smul_mem _ _ (hA.pow n)
  have hclosed := isClosed_localSubmodule (K := K) (N := N) T
  exact hclosed.mem_of_tendsto hsum.tendsto_sum_nat
    (Filter.Eventually.of_forall fun n =>
      Submodule.sum_mem _ fun i _ => hmem i)

/-! ### Local kicks from arbitrary skew-Hermitian generators -/

/-- A skew-Hermitian generator exponentiates to a unitary (the generic
unitarity core, at the `FieldConfig` index). -/
theorem expKick_unitary {G : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : Gᴴ = -G) : exp G ∈ Matrix.unitaryGroup (FieldConfig K N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    ← Matrix.exp_conjTranspose, hG,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl G).neg_left),
    neg_add_cancel, exp_zero]

/-- **A local kick**: a unitary supported on an edge. The support field is
all the light-cone argument consumes. -/
structure KickData (K N : ℕ) where
  /-- The coupled edge. -/
  edge : Fin K × Fin K
  /-- The kick unitary. -/
  U : Matrix.unitaryGroup (FieldConfig K N) ℂ
  /-- The kick is supported on its edge. -/
  supported : SupportedOn {edge.1, edge.2} U.val

/-- **Smart constructor**: any skew-Hermitian edge-supported generator —
hopping terms included — yields a local kick, by unitarity of the
exponential and exp-closure of the local algebra. -/
noncomputable def KickData.ofGenerator (e : Fin K × Fin K)
    {G : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hG : Gᴴ = -G) (hsupp : SupportedOn {e.1, e.2} G) : KickData K N where
  edge := e
  U := ⟨exp G, expKick_unitary hG⟩
  supported := hsupp.exp

/-! ### The kicked drive and its fold light cone -/

/-- One kick's support growth: the edge is absorbed exactly when it
touches the region. -/
def kickFoldStep (e : Fin K × Fin K) (R : Finset (Fin K)) : Finset (Fin K) :=
  if e.1 ∈ R ∨ e.2 ∈ R then insert e.1 (insert e.2 R) else R

/-- The per-period support growth of a kick list (kicks may chain within
a period; the fold records that honestly). -/
def kickFold (es : List (Fin K × Fin K)) (R : Finset (Fin K)) :
    Finset (Fin K) :=
  es.foldl (fun R e => kickFoldStep e R) R

/-- The `n`-period fold ball. -/
def kickFoldBall (es : List (Fin K × Fin K)) (R : Finset (Fin K)) :
    ℕ → Finset (Fin K)
  | 0 => R
  | n + 1 => kickFold es (kickFoldBall es R n)

/-- **The kicked drive**: one free period followed by the kick list. -/
noncomputable def kickedStep (τ : ℝ) (ks : List (KickData K N)) :
    Matrix.unitaryGroup (FieldConfig K N) ℂ :=
  freeFieldU K N τ * (ks.map KickData.U).prod

/-- One kick spreads support at most onto its fold step. -/
theorem heisenberg_kick_supportedOn {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (k : KickData K N)
    (hA : SupportedOn R A) :
    SupportedOn (kickFoldStep k.edge R) (heisenberg k.U A) := by
  rw [kickFoldStep]
  by_cases h : k.edge.1 ∈ R ∨ k.edge.2 ∈ R
  · rw [if_pos h]
    refine (heisenberg_supportedOn_union k.supported hA).mono ?_
    intro x hx
    rcases Finset.mem_union.mp hx with hxR | hxe
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxR)
    · rcases Finset.mem_insert.mp hxe with h1 | h2
      · exact h1 ▸ Finset.mem_insert_self _ _
      · rw [Finset.mem_singleton.mp h2]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · rw [if_neg h]
    rw [heisenberg_eq_of_disjoint ?_ k.supported hA]
    · exact hA
    · rw [Finset.disjoint_right]
      intro x hxe hxR
      rcases Finset.mem_insert.mp hxe with h1 | h2
      · exact h (Or.inl (h1 ▸ hxR))
      · exact h (Or.inr (Finset.mem_singleton.mp h2 ▸ hxR))

/-- A kick list spreads support at most onto its fold. -/
theorem heisenberg_kickList_supportedOn {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (ks : List (KickData K N)) (hA : SupportedOn R A) :
    SupportedOn (kickFold (ks.map KickData.edge) R)
      (heisenberg (ks.map KickData.U).prod A) := by
  induction ks generalizing R A with
  | nil =>
    simp only [List.map_nil, List.prod_nil, heisenberg_one]
    exact hA
  | cons k rest ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [heisenberg_mul]
    exact ih (heisenberg_kick_supportedOn k hA)

/-- One kicked period spreads support at most onto the fold. -/
theorem heisenberg_kickedStep_supportedOn {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ : ℝ)
    (ks : List (KickData K N)) (hA : SupportedOn R A) :
    SupportedOn (kickFold (ks.map KickData.edge) R)
      (heisenberg (kickedStep τ ks) A) := by
  rw [kickedStep, heisenberg_mul]
  exact heisenberg_kickList_supportedOn ks
    (heisenberg_freeFieldU_supportedOn τ hA)

/-- ★★ **The non-diagonal light cone**: after `n` periods of the kicked
drive — free step plus ARBITRARY local kicks, hopping included — support
lies inside the `n`-fold ball. -/
theorem heisenberg_kickedStep_pow_supportedOn {R : Finset (Fin K)}
    {A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ : ℝ)
    (ks : List (KickData K N)) (n : ℕ) (hA : SupportedOn R A) :
    SupportedOn (kickFoldBall (ks.map KickData.edge) R n)
      (heisenberg (kickedStep τ ks ^ n) A) := by
  induction n with
  | zero => rw [pow_zero, heisenberg_one]; exact hA
  | succ n ih =>
    rw [pow_succ, heisenberg_mul]
    exact heisenberg_kickedStep_supportedOn τ ks ih

/-- ★★ **Locality outside the fold cones**: observables whose fold-balls
stay disjoint after `n` kicked periods still commute. -/
theorem commute_heisenberg_kickedStep_pow {R T : Finset (Fin K)}
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ} (τ : ℝ)
    (ks : List (KickData K N)) (n : ℕ)
    (hRT : Disjoint (kickFoldBall (ks.map KickData.edge) R n)
      (kickFoldBall (ks.map KickData.edge) T n))
    (hA : SupportedOn R A) (hB : SupportedOn T B) :
    heisenberg (kickedStep τ ks ^ n) A * heisenberg (kickedStep τ ks ^ n) B
      = heisenberg (kickedStep τ ks ^ n) B
        * heisenberg (kickedStep τ ks ^ n) A :=
  commute_of_disjointSupport hRT
    (heisenberg_kickedStep_pow_supportedOn τ ks n hA)
    (heisenberg_kickedStep_pow_supportedOn τ ks n hB)

end CSD.CV

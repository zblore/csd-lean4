import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-!
# Empirical: Kochen-Specker theorem (Cabello 1996 18-vector configuration)

**Category:** 2-Framework candidate for the abstract combinatorial
impossibility (`no_value_assignment_18_9`); 3-Local for the concrete
Cabello-Estebaranz-García-Alcaine 1996 18-basis instance
(`ks_no_value_assignment_cabello18`). The abstract impossibility is
purely combinatorial — no Hilbert space, no CSD ontology — and is
**promotion-ready to 2-Framework** on demand. Extraction to
`CsdLean4/Framework/QM/KochenSpecker.lean` or upstreaming to
`Mathlib/Combinatorics/KochenSpecker.lean` is deferred until LF4
creates the `Framework/` subtree (CONVENTIONS.md §1.Cat-2).

## What KS says

The Kochen-Specker theorem (Kochen-Specker 1967): in dimension `d ≥ 3`,
there is no way to assign predetermined values `λ : ⟨projections⟩ → {0, 1}`
to all rank-1 projection operators on `ℂ^d` such that, for every
complete orthonormal basis `(v₁, …, v_d)` of the Hilbert space, exactly
one of the `λ(|vᵢ⟩⟨vᵢ|)` equals `1`.

This is the structural signature of QM **contextuality**: no global
non-contextual value assignment is consistent with QM's eigenvalue
structure.

## Cabello-Estebaranz-García-Alcaine 1996

The simplest KS witness (Cabello-Estebaranz-García-Alcaine 1996, *Phys.
Rev. Lett.* **76**, 1881) uses 18 vectors in `ℝ⁴` that organise into 9
orthogonal 4-tuples, with each vector appearing in **exactly 2** of the
9 bases. The 18 vectors (cited in the docstring of `cabelloBasis`
below) and their 9-basis structure are an explicit construction;
verifying their pairwise orthogonality in ℝ⁴ is a separate geometric
check whose Lean formalisation is deferred to a follow-up.

The combinatorial impossibility argument: under any `{0, 1}` assignment
satisfying "exactly one vector per basis is assigned `1`", summing over
the 9 bases gives `9` total "1"s. But by appearance-count `2`, the
same total equals `2 · k` where `k` is the number of vectors assigned
`1`. So `9 = 2k` for integer `k`, which is impossible.

This is a **pure finite combinatorial argument**: the QM content
(Hilbert space, orthogonality, eigenvalue structure) is needed only to
verify that the 18 vectors do form 9 orthonormal bases in `ℝ⁴`; the
contradiction itself is dimension-free and the geometric verification
is deferred to a future revision.

## Distinction from CHSH and GHZ

- **CHSH (Bell.lean):** statistical inequality violation `|S| ≤ 2`
  exceeded by QM's `2√2`. Probabilistic content.
- **GHZ (Multipartite/GHZ.lean):** algebraic single-shot contradiction
  from QM expectation values. Specific to *local* hidden variables.
- **KS (this file):** structural contradiction from QM's eigenvalue
  structure alone — rules out *any* non-contextual hidden-variable
  assignment to projectors, not specifically local ones. Single-system,
  no spatial separation, no expectation values needed.

## Experimental verification

- Cabello-Estebaranz-García-Alcaine 1996: *Phys. Rev. Lett.* **76**, 1881
  (theoretical 18-vector proof).
- Kochen-Specker 1967: original 117-vector theorem (*J. Math. Mech.* **17**, 59).
- Kirchmair, Zähringer, Gerritsma, Kleinmann, Gühne, Cabello, Blatt,
  Roos 2009: *Nature* **460**, 494 (trapped-ion experimental test).
- Bartosik, Klepp, Schmitzer, Sponar, Cabello, Rauch, Hasegawa 2009:
  *Phys. Rev. Lett.* **103**, 040403 (neutron experimental test).

## Future work: vector data + orthogonality verification

A follow-up commit will add:

- 18 unit vectors `cabelloVec : Fin 18 → EuclideanSpace ℝ (Fin 4)`
  with rational components (e.g. `cabelloVec 0 = (0, 0, 0, 1)`, etc.).
- 36 pairwise orthogonality lemmas (one per orthogonal pair within
  each of the 9 bases; `decide`/`norm_num` closeable from rational
  components).
- A QM-bridge corollary identifying the Cabello-18 configuration with
  9 complete orthonormal bases of `ℝ⁴ ↪ ℂ⁴`.

The headline `ks_no_value_assignment_cabello18` impossibility holds
without any of this geometric content: it is a purely combinatorial
consequence of `cabelloBasis` + `cabelloBasis_appears_twice`.
-/

open scoped BigOperators

namespace CSD
namespace Empirical
namespace KochenSpecker

/-! ## Abstract combinatorial impossibility -/

/-- **Abstract Kochen-Specker impossibility.** No `Bool`-valued
assignment on `Fin 18` can satisfy the per-basis-exactly-one constraint
on a `Fin 9 → Finset (Fin 18)` basis family whose appearance count is
`2` for every vector.

Argument: summing the per-basis cardinal counts gives `9` (one per
basis). The same sum equals `2 · k` where `k = |{v : λ v = true}|` by
the appearance-count hypothesis (Fubini swap). So `9 = 2k`, impossible.

This is the combinatorial core of the Kochen-Specker theorem: the
contradiction is dimension-free and Hilbert-space-free. The geometric
content (that the Cabello-18 configuration actually realises a 9-basis
appearance-2 structure in `ℝ⁴`) is verified separately in
`cabelloBasis_appears_twice` below; full orthogonality verification is
deferred per the module docstring's "Future work" section. -/
theorem no_value_assignment_18_9
    (bases : Fin 9 → Finset (Fin 18))
    (h_appears : ∀ v : Fin 18,
      ((Finset.univ : Finset (Fin 9)).filter (fun B => v ∈ bases B)).card = 2) :
    ¬ ∃ lambda : Fin 18 → Bool,
      ∀ B : Fin 9, ((bases B).filter (fun v => lambda v = true)).card = 1 := by
  rintro ⟨lambda, h_one⟩
  -- LHS sum is 9.
  have h9 : ∑ B : Fin 9, ((bases B).filter (fun v => lambda v = true)).card = 9 := by
    simp [h_one]
  -- LHS sum is 2 · |{v : λ v = true}| by Fubini double-count.
  -- The proof: count pairs (B, v) with v ∈ bases B ∧ λ v = true.
  -- Indicator function on (Fin 9) × (Fin 18).
  let f : Fin 9 → Fin 18 → ℕ := fun B v =>
    if v ∈ bases B ∧ lambda v = true then 1 else 0
  -- Per-basis count = sum-over-Fin-18 of f.
  have rewrite_basis : ∀ B : Fin 9,
      ((bases B).filter (fun v => lambda v = true)).card = ∑ v : Fin 18, f B v := by
    intro B
    rw [show ((bases B).filter (fun v => lambda v = true))
          = ((Finset.univ : Finset (Fin 18)).filter
              (fun v => v ∈ bases B ∧ lambda v = true)) from ?_]
    · simp only [f, Finset.card_filter]
    · ext v
      simp [Finset.mem_filter]
  -- Per-vector count: sum-over-Fin-9 of f = (if λ v = true then appearance(v) else 0).
  have rewrite_vec : ∀ v : Fin 18,
      ∑ B : Fin 9, f B v
        = if lambda v = true then
            ((Finset.univ : Finset (Fin 9)).filter (fun B => v ∈ bases B)).card
          else 0 := by
    intro v
    by_cases hl : lambda v = true
    · -- LHS becomes ∑ B, if v ∈ bases B then 1 else 0 = card_filter
      have h_summand : ∀ B, f B v = if v ∈ bases B then (1 : ℕ) else 0 := by
        intro B; simp only [f, hl, and_true]
      rw [Finset.sum_congr rfl (fun B _ => h_summand B), if_pos hl, Finset.card_filter]
    · -- LHS becomes ∑ B, 0 = 0
      have h_summand : ∀ B, f B v = (0 : ℕ) := by
        intro B
        simp only [f]
        rw [if_neg]
        intro ⟨_, h⟩
        exact hl h
      rw [Finset.sum_congr rfl (fun B _ => h_summand B), if_neg hl, Finset.sum_const_zero]
  -- Combine: total = 2 * |{λ-true}|.
  have hT_card :
      ∑ B : Fin 9, ((bases B).filter (fun v => lambda v = true)).card
        = 2 * ((Finset.univ : Finset (Fin 18)).filter (fun v => lambda v = true)).card := by
    calc ∑ B : Fin 9, ((bases B).filter (fun v => lambda v = true)).card
        = ∑ B : Fin 9, ∑ v : Fin 18, f B v := by
          exact Finset.sum_congr rfl (fun B _ => rewrite_basis B)
      _ = ∑ v : Fin 18, ∑ B : Fin 9, f B v := Finset.sum_comm
      _ = ∑ v : Fin 18,
            (if lambda v = true then
                ((Finset.univ : Finset (Fin 9)).filter (fun B => v ∈ bases B)).card
              else 0) := by
          exact Finset.sum_congr rfl (fun v _ => rewrite_vec v)
      _ = ∑ v : Fin 18, (if lambda v = true then 2 else 0) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [h_appears v]
      _ = 2 * ((Finset.univ : Finset (Fin 18)).filter (fun v => lambda v = true)).card := by
          rw [← Finset.sum_filter, Finset.sum_const]
          exact Nat.mul_comm _ _
  rw [hT_card] at h9
  -- 2 · k = 9 ⟹ contradiction.
  omega

/-! ## Cabello-Estebaranz-García-Alcaine 1996 basis structure

The 9 orthogonal 4-tuples of the 18-vector configuration, indexed by
`Fin 18 → Fin 9 → Bool` membership.

The underlying vectors (deferred per the module docstring):

```
v0  = (0, 0, 0, 1)         v9  = (0, 0, 1, 1)
v1  = (0, 0, 1, 0)         v10 = (1, 1, 1, 1)
v2  = (1, 1, 0, 0)         v11 = (0, 1, 0, -1)
v3  = (1, -1, 0, 0)        v12 = (1, 0, 0, 1)
v4  = (0, 1, 0, 0)         v13 = (1, 0, 0, -1)
v5  = (1, 0, 1, 0)         v14 = (0, 1, -1, 0)
v6  = (1, 0, -1, 0)        v15 = (1, 1, -1, 1)
v7  = (1, -1, 1, -1)       v16 = (1, 1, 1, -1)
v8  = (1, -1, -1, 1)       v17 = (-1, 1, 1, 1)
```

The 9 orthogonal 4-tuples (each is a complete orthogonal basis of
ℝ⁴; orthogonality verification deferred):

```
B₀ = {v0, v1, v2, v3}     B₅ = {v8, v10, v13, v14}
B₁ = {v0, v4, v5, v6}     B₆ = {v3, v9, v15, v16}
B₂ = {v2, v7, v8, v9}     B₇ = {v5, v11, v15, v17}
B₃ = {v6, v7, v10, v11}   B₈ = {v12, v14, v16, v17}
B₄ = {v1, v4, v12, v13}
```

Appearance count: each `vᵢ` appears in exactly 2 of the 9 bases (e.g.
`v0 ∈ B₀ ∩ B₁`, `v7 ∈ B₂ ∩ B₃`, etc.). Verified by `decide` over the
finite combinatorial structure. -/
def cabelloBasis : Fin 9 → Finset (Fin 18)
  | 0 => {0, 1, 2, 3}
  | 1 => {0, 4, 5, 6}
  | 2 => {2, 7, 8, 9}
  | 3 => {6, 7, 10, 11}
  | 4 => {1, 4, 12, 13}
  | 5 => {8, 10, 13, 14}
  | 6 => {3, 9, 15, 16}
  | 7 => {5, 11, 15, 17}
  | 8 => {12, 14, 16, 17}

/-- Each Cabello vector appears in exactly 2 of the 9 bases. Verified
by `decide` over the finite combinatorial structure of `cabelloBasis`. -/
theorem cabelloBasis_appears_twice (v : Fin 18) :
    ((Finset.univ : Finset (Fin 9)).filter (fun B => v ∈ cabelloBasis B)).card = 2 := by
  fin_cases v <;> decide

/-- **Kochen-Specker no-value-assignment theorem (Cabello-18
instance).** No `Bool`-valued assignment `λ : Fin 18 → Bool` on the
Cabello-Estebaranz-García-Alcaine 1996 18-vector configuration
satisfies the per-basis-exactly-one constraint.

Specialisation of the abstract `no_value_assignment_18_9` to the
concrete `cabelloBasis`, discharging the appearance-count hypothesis
via `cabelloBasis_appears_twice`.

**QM interpretation.** For each of the 9 orthogonal 4-tuples in
`cabelloBasis`, viewed as a complete orthonormal basis of ℝ⁴ (or, by
inclusion, of ℂ⁴), QM requires exactly one basis vector to be assigned
eigenvalue `1` (the measurement outcome) and the rest `0`. Any
non-contextual value assignment to the projectors `|vᵢ⟩⟨vᵢ|` for
`i ∈ Fin 18` must respect this constraint on all 9 bases
simultaneously. The theorem shows no such assignment exists.

**Distinction from Bell-style hidden variables.** The KS impossibility
rules out *any* non-contextual hidden-variable assignment to
projectors, not specifically *local* hidden variables. The Cabello-18
construction does not require spatial separation, multiple parties, or
statistical sampling: it is a single-system, single-shot, algebraic
constraint on value assignments.

**Experimental verification:** Kirchmair et al. 2009 (trapped ions);
Bartosik et al. 2009 (neutrons). -/
theorem ks_no_value_assignment_cabello18 :
    ¬ ∃ lambda : Fin 18 → Bool,
      ∀ B : Fin 9, ((cabelloBasis B).filter (fun v => lambda v = true)).card = 1 :=
  no_value_assignment_18_9 cabelloBasis cabelloBasis_appears_twice

end KochenSpecker
end Empirical
end CSD

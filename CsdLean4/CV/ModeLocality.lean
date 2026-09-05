/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Dispersion

/-!
# CV/ModeLocality: commuting algebras of disjoint mode sets (EFT Stage 2b)

**Category:** CV (continuous variables — the multi-mode field).

The **locality** half of EFT Stage 2, stated at the finite cutoff where it is actually true.

An operator on the field is **supported on** a set `S` of modes (`SupportedOn`) when it (i) does
not move the modes outside `S` and (ii) has entries that do not depend on those spectator modes.
⚠️ **Name check (2026-09-05, CR-8): this is mode-disjoint commutation, not the Haag–Kastler axiom.** The index sets here are **modes**, not spacetime regions, and there is no net, no isotony and no covariance — so the name imports structure the corpus does not have. Haag–Kastler is cited as the *analogue*, never as what is proved.

The headline is **mode-disjoint commutation**, the finite-cutoff analogue of the Haag–Kastler
kinematic locality axiom:

  `commute_of_disjointSupport` — `S ∩ T = ∅` ⟹ `A * B = B * A`

for `A` supported on `S` and `B` supported on `T`. Observables of disjoint mode sets commute, so
they are jointly measurable and the record layer can assign them outcomes simultaneously.

A non-vacuous witness is supplied rather than assumed: `modeOp k₀ a` acts as the single-mode
matrix `a` on mode `k₀` and as the identity elsewhere, is provably `SupportedOn {k₀}`
(`modeOp_supportedOn`), and two such at distinct modes commute (`commute_modeOp`) for *every*
pair of single-mode matrices.

## What "locality" does and does not mean here

The theorem is about **disjoint tensor factors**. Under the position-space reading — the `K`
modes are lattice *sites*, as seeded by `CV/Position.lean` — this is genuine spatial locality:
observables of disjoint regions of the lattice commute. Under the momentum-space reading (the
`p k` of `CV/Dispersion.lean`) the modes are delocalised, and mode-disjointness is *not* spatial
separation; the statement is then subsystem locality, not microcausality.

**Continuum microcausality — `[φ(x), φ(y)] = 0` for spacelike-separated `x, y` — is NOT proved
here, and does not hold exactly at a finite cutoff.** It needs the continuum limit, which the EFT
posture of this chain deliberately defers (`CV/ApproxCCR.lean` `no_exact_finite_ccr`: no finite
model satisfies the CCR exactly). What is delivered is the finite-cutoff statement that survives
that limit as the locality axiom: commuting algebras for disjoint regions. Calling this
microcausality would overstate it; it is its kinematic core.

## References

`CV/Dispersion.lean` (Stage 2a, the dispersion relation); `CV/FieldModes.lean` (Stage 1, the mode
product); `CV/Position.lean` (the spatial lattice, under which mode-disjointness reads as spatial
disjointness); `CV/ApproxCCR.lean` (`no_exact_finite_ccr`, why the continuum is deferred);
`RecordLayer/Measurement.lean` (the record layer that commuting observables let act jointly);
`specs/BACKLOG.md` (the CV-chain row); `specs/future-work.md`.
Haag, *Local Quantum Physics* (1992); Haag–Kastler (1964).
-/

@[expose] public section

open MeasureTheory Matrix

namespace CSD.CV

variable {K N : ℕ}

/-! ### Support on a set of modes -/

/-- An operator is **supported on the mode set `S`** when it acts only on those modes: it does
not move the spectator modes outside `S` (`offDiag`), and its entries do not depend on them
(`indep`). This is the finite-cutoff form of "an observable localised in a region". -/
structure SupportedOn (S : Finset (Fin K))
    (A : Matrix (FieldConfig K N) (FieldConfig K N) ℂ) : Prop where
  /-- `A` does not move the modes outside `S`: an entry between configurations that differ on a
  spectator mode vanishes. -/
  offDiag : ∀ {c d : FieldConfig K N} {k : Fin K}, k ∉ S → c k ≠ d k → A c d = 0
  /-- `A`'s entries depend only on the modes in `S`: two entries whose `S`-components agree, and
  whose spectator components are unmoved, are equal. -/
  indep : ∀ {c d c' d' : FieldConfig K N},
    (∀ k ∈ S, c k = c' k) → (∀ k ∈ S, d k = d' k) →
    (∀ k, k ∉ S → c k = d k) → (∀ k, k ∉ S → c' k = d' k) → A c d = A c' d'

/-! ### Locality: disjoint supports commute -/

/-- **Mode-disjoint commutation at a finite cutoff** (the Haag–Kastler analogue on mode sets, not
regions). Operators supported on disjoint mode
sets commute — so observables of disjoint regions are jointly measurable, and the record layer
can assign them outcomes simultaneously.

The proof is the uniqueness of the intermediate configuration. If `c` and `d` differ on a mode
outside `S ∪ T`, then *every* term of both matrix products vanishes. Otherwise exactly one
intermediate configuration survives in each product — `e₁` (`d` on `S`, `c` off `S`) in `A·B` and
`e₂` (`c` on `S`, `d` off `S`) in `B·A` — and the two surviving products are the same two numbers
in the other order, by `indep`. -/
theorem commute_of_disjointSupport {S T : Finset (Fin K)} (hST : Disjoint S T)
    {A B : Matrix (FieldConfig K N) (FieldConfig K N) ℂ}
    (hA : SupportedOn S A) (hB : SupportedOn T B) :
    A * B = B * A := by
  classical
  have hTS : ∀ {k : Fin K}, k ∈ S → k ∉ T := fun hk => Finset.disjoint_left.mp hST hk
  have hST' : ∀ {k : Fin K}, k ∈ T → k ∉ S := fun hk => Finset.disjoint_right.mp hST hk
  ext c d
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hout : ∀ k, k ∉ S → k ∉ T → c k = d k
  · -- The surviving intermediate configurations.
    set e₁ : FieldConfig K N := fun k => if k ∈ S then d k else c k with he₁
    set e₂ : FieldConfig K N := fun k => if k ∈ S then c k else d k with he₂
    have he₁S : ∀ k ∈ S, e₁ k = d k := fun k hk => by simp [he₁, hk]
    have he₁S' : ∀ k, k ∉ S → e₁ k = c k := fun k hk => by simp [he₁, hk]
    have he₂S : ∀ k ∈ S, e₂ k = c k := fun k hk => by simp [he₂, hk]
    have he₂S' : ∀ k, k ∉ S → e₂ k = d k := fun k hk => by simp [he₂, hk]
    -- `A · B` collapses to the single term at `e₁`.
    have hAB : (∑ e, A c e * B e d) = A c e₁ * B e₁ d := by
      refine Finset.sum_eq_single e₁ ?_ (fun h => absurd (Finset.mem_univ _) h)
      intro e _ hne
      obtain ⟨k, hk⟩ : ∃ k, e k ≠ e₁ k := by
        by_contra hcon
        exact hne (funext fun k => not_not.mp (fun h => hcon ⟨k, h⟩))
      by_cases hkS : k ∈ S
      · -- On `S` the surviving `e` must match `d`, else `B` kills the term.
        rw [hB.offDiag (hTS hkS) (by rw [← he₁S k hkS]; exact hk), mul_zero]
      · -- Off `S` it must match `c`, else `A` kills the term.
        rw [hA.offDiag hkS (fun hcd => hk (by rw [← hcd, he₁S' k hkS])), zero_mul]
    -- `B · A` collapses to the single term at `e₂`.
    have hBA : (∑ e, B c e * A e d) = B c e₂ * A e₂ d := by
      refine Finset.sum_eq_single e₂ ?_ (fun h => absurd (Finset.mem_univ _) h)
      intro e _ hne
      obtain ⟨k, hk⟩ : ∃ k, e k ≠ e₂ k := by
        by_contra hcon
        exact hne (funext fun k => not_not.mp (fun h => hcon ⟨k, h⟩))
      by_cases hkS : k ∈ S
      · rw [hB.offDiag (hTS hkS) (fun hcd => hk (by rw [← hcd, he₂S k hkS])), zero_mul]
      · rw [hA.offDiag hkS (by rw [← he₂S' k hkS]; exact hk), mul_zero]
    rw [hAB, hBA]
    -- The two surviving entries are equal in pairs.
    have hAeq : A c e₁ = A e₂ d :=
      hA.indep (fun k hk => (he₂S k hk).symm) (fun k hk => he₁S k hk)
        (fun k hk => (he₁S' k hk).symm) (fun k hk => he₂S' k hk)
    have hBeq : B e₁ d = B c e₂ := by
      refine hB.indep (fun k hk => he₁S' k (hST' hk)) (fun k hk => (he₂S' k (hST' hk)).symm)
        (fun k hk => ?_) (fun k hk => ?_)
      · -- off `T`: `e₁ = d`, using `hout` on the modes outside both sets
        by_cases hkS : k ∈ S
        · exact he₁S k hkS
        · rw [he₁S' k hkS]; exact hout k hkS hk
      · -- off `T`: `c = e₂`
        by_cases hkS : k ∈ S
        · exact (he₂S k hkS).symm
        · rw [he₂S' k hkS]; exact hout k hkS hk
    rw [hAeq, hBeq]
    ring
  · -- `c` and `d` differ on a spectator mode of both: every term of both products vanishes.
    push Not at hout
    obtain ⟨k, hkS, hkT, hne⟩ := hout
    have hzeroAB : ∀ e : FieldConfig K N, A c e * B e d = 0 := by
      intro e
      by_cases h : c k = e k
      · rw [hB.offDiag hkT (fun hed => hne (h.trans hed)), mul_zero]
      · rw [hA.offDiag hkS h, zero_mul]
    have hzeroBA : ∀ e : FieldConfig K N, B c e * A e d = 0 := by
      intro e
      by_cases h : c k = e k
      · rw [hA.offDiag hkS (fun hed => hne (h.trans hed)), mul_zero]
      · rw [hB.offDiag hkT h, zero_mul]
    rw [Finset.sum_eq_zero (fun e _ => hzeroAB e), Finset.sum_eq_zero (fun e _ => hzeroBA e)]

/-! ### A non-vacuous witness: single-mode operators -/

/-- The operator acting as the single-mode matrix `a` on mode `k₀` and as the identity on every
other mode. -/
noncomputable def modeOp (k₀ : Fin K) (a : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (FieldConfig K N) (FieldConfig K N) ℂ :=
  fun c d => if (∀ k, k ≠ k₀ → c k = d k) then a (c k₀) (d k₀) else 0

theorem modeOp_apply_of_agree (k₀ : Fin K) (a : Matrix (Fin N) (Fin N) ℂ)
    {c d : FieldConfig K N} (h : ∀ k, k ≠ k₀ → c k = d k) :
    modeOp k₀ a c d = a (c k₀) (d k₀) := by
  rw [modeOp, if_pos h]

/-- **A single-mode operator is supported on that one mode.** The support notion is not vacuous:
every `modeOp` inhabits it. -/
theorem modeOp_supportedOn (k₀ : Fin K) (a : Matrix (Fin N) (Fin N) ℂ) :
    SupportedOn {k₀} (modeOp k₀ a) := by
  classical
  constructor
  · intro c d k hk hcd
    rw [modeOp, if_neg]
    exact fun h => hcd (h k (by simpa using hk))
  · intro c d c' d' hS hS' hoff hoff'
    have hk₀ : (k₀ : Fin K) ∈ ({k₀} : Finset (Fin K)) := Finset.mem_singleton_self k₀
    rw [modeOp_apply_of_agree k₀ a (fun k hk => hoff k (by simpa using hk)),
      modeOp_apply_of_agree k₀ a (fun k hk => hoff' k (by simpa using hk)),
      hS k₀ hk₀, hS' k₀ hk₀]

/-- **Single-mode operators at distinct modes commute** — for every pair of single-mode matrices.
The concrete instance of `commute_of_disjointSupport`, and the reason the locality statement has
content. -/
theorem commute_modeOp {k₀ k₁ : Fin K} (h : k₀ ≠ k₁) (a b : Matrix (Fin N) (Fin N) ℂ) :
    modeOp k₀ a * modeOp k₁ b = modeOp k₁ b * modeOp k₀ a := by
  classical
  refine commute_of_disjointSupport ?_ (modeOp_supportedOn k₀ a) (modeOp_supportedOn k₁ b)
  simpa using h

end CSD.CV

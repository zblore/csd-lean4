# LF3 TODO: items deferred from LF2

Items LF2 deliberately left for LF3, with rationale and concrete pickup notes.

## 1. Unitary covariance clause of OperationalPackage (spec Def 5.1 clause 3)

**Status:** LF2 omits the `unitary_covariance` field. `Effect.conjugateBy` is in place as the structural helper.

**Why deferred:** Two readings of spec clause 3, and the wrong one over-constrains:

- **Invariance reading** — `p (Effect.conjugateBy U E) = p E` for all U. Rules out pure-state packages.
- **Covariant reading** — a functor `OperationalPackage.conjugateBy U : OperationalPackage N → OperationalPackage N` with `(conjugateBy U OP).p E = OP.p (Effect.conjugateBy U E)`. Mathematically correct, type-heavy.

**Pickup:**
1. Implement `OperationalPackage.conjugateBy` as a function producing a new package.
2. Prove the structure fields (nonneg, le_one, total_one, additivity) carry through conjugation. Most reduce to applying `Effect.conjugateBy` inside and invoking the original field.
3. `total_one` requires showing `Effect.conjugateBy U Effect.one = Effect.one` (since `U† · 1 · U = 1` for unitary `U`).
4. `additivity` requires `Effect.conjugateBy U (Effect.add E F hLe) = Effect.add (conjugateBy U E) (conjugateBy U F) hLe'` for some derived `hLe'`. Distributivity of conjugation over matrix addition closes it.
5. Once the functor is in place, state a covariance theorem: `(conjugateBy U OP).p E = OP.p (Effect.conjugateBy U E)` — tautological by construction.

**Depends on:** `Matrix.unitaryGroup` (already imported in LF2), `Effect.conjugateBy` (LF2).

---

## 2. Preparation-to-Hilbert-vector correspondence

**Status:** Not addressed in LF2. This is the missing piece for a full LF1 → Born-form chain.

**Why deferred:** LF1's `μprep : Measure Σ` and LF2-BornWrapper's `ψ : EuclideanSpace ℂ (Fin N)` live in disjoint type universes. Connecting them requires introducing `P ↔ Projectivization ℂ (EuclideanSpace ℂ (Fin N))` and a concentration argument.

**Pickup sketch:**
1. In LF3, specialise LF2's abstract `P` to `Projectivization ℂ (EuclideanSpace ℂ (Fin N))`.
2. Introduce a "pure preparation" predicate on `μprep`: something like "the pushforward `π * μprep` is a Dirac measure at a projective point `[ψ] ∈ CP^{N-1}`."
3. Lift `[ψ]` to a unit vector `ψ : EuclideanSpace ℂ (Fin N)` (choice of representative mod phase).
4. Connect the resulting `OperationalPackage` (derived from `μprep` via the measure bridge + Radon–Nikodym) to `rankOneDensity ψ` via `busch_effect_gleason` + `rankOneDensity_unique_of_certainty`.
5. Chain with `LF1_main_theorem_projective` and `pure_state_born_weights_of_certainty` to obtain: **LF1 frequency → ‖⟨ψ, φ⟩‖²**.

**Depends on:** Mathlib's `Projectivization`, Radon–Nikodym derivatives, Haar-measure / Dirac-concentration arguments.

---

## 3. Rank-1 effects from projective points (not from unit vectors)

**Status:** `rankOneEffect`, `rankOneDensity` take `EuclideanSpace ℂ (Fin N)` unit vectors, not projective points.

**Why deferred:** LF3 needs outcomes specified projectively (`[φ] ∈ CP^{N-1}`), not as unit vectors. Currently a phase-dependent vector is required. Phase-invariance of the outer product `|φ⟩⟨φ|` makes this sound, but LF2 doesn't expose it.

**Pickup:**
1. Prove `rankOneEffect φ hφ = rankOneEffect (c • φ) hφ'` for `|c| = 1` (phase invariance of the outer product). One-line calculation: `(c • φ) * star (c • φ) = c · star c · (φ * star φ) = ‖c‖² · (φ * star φ) = φ * star φ`.
2. Lift to projective points: for `[φ] : Projectivization ℂ (EuclideanSpace ℂ (Fin N))`, define `rankOneEffectProj [φ]` via choice of unit-vector representative, using the phase-invariance lemma to show well-definedness.
3. Similarly for `rankOneDensityProj`.

**Depends on:** `Mathlib.LinearAlgebra.Projectivization.Basic`.

---

## 4. Prove `rankOneDensity_unique_of_certainty` (remove axiom)

**Status:** Axiomatised in LF2. Full proof sketch is in the module docstring.

**Why deferred:** Rigorous proof needs Mathlib's spectral theorem + PSD functional calculus. Significant Lean-level plumbing that isn't worth doing for LF2 alone.

**Pickup:**
1. Use `Matrix.IsHermitian.spectralTheorem` to diagonalise `ρ`.
2. Show `⟨ψ, ρ ψ⟩ = 1` + `Tr(ρ) = 1` + PSD imply `ρ` has eigenvalue 1 on `ψ` and 0 elsewhere.
3. Reconstruct `ρ = |ψ⟩⟨ψ|` from the eigenstructure.

Alternative path: use the `ρ² ≤ ρ` + Cauchy–Schwarz route sketched in the axiom docstring, avoiding the full spectral theorem. Possibly cleaner if Mathlib lemmas line up.

**Depends on:** `Matrix.IsHermitian.spectralTheorem`, PSD functional calculus, or the `ρ² ≤ ρ` inequality for densities (whichever lands first in Mathlib).

---

## 5. Prove the two spec-mandated axioms (long-term)

**Status:** `invariant_measure_uniqueness` and `busch_effect_gleason` remain axioms. Spec §7.4 accepts this.

**Why deferred:** Each is a Mathlib-scale contribution.

- `invariant_measure_uniqueness` — Haar measure on compact homogeneous spaces (`SU(N)/U(N-1) ≅ CP^{N-1}`). Mathlib has Haar on topological groups; the quotient/homogeneous-space case requires more work. Months of Mathlib contribution.

- `busch_effect_gleason` — effect-algebra infrastructure (not currently in Mathlib), plus Busch 2003's proof. Larger task; full effect-algebra / POVM machinery is an open Mathlib gap.

**Pickup:**
- Both remain axioms until Mathlib integration makes them theorems. When one lands, swap `axiom` for `theorem`-via-import in LF2. Signatures are already in the right shape — no downstream changes needed.

---

## 6. σ-additivity vs finite additivity of OperationalPackage

**Status:** LF2 encodes only finite additivity (pairwise). Busch's original result uses σ-additivity.

**Why deferred:** In finite dimension the distinction is usually inessential — the effect algebra is "compact enough" that finite additivity implies σ-additivity. But we haven't verified this formally.

**Pickup:**
1. Before LF3 attempts to *prove* `busch_effect_gleason` (rather than import), verify: in finite dim, finite additivity + other Def 5.1 clauses imply σ-additivity.
2. If yes, no code change needed. If no, weaken `OperationalPackage.additivity` to a `σ`-additive form over countable effect families.

---

## 7. Outcome specification: ontic-first vs projective-first

**Status:** LF1's `OutcomeRegion` has `Ω : Set Sigma` (ontic-first). LF2's `LF1_main_theorem_projective` takes a correspondence hypothesis `O.preEvent = D.π ⁻¹' Oep` linking them.

**Why deferred:** A cleaner LF3 architecture would let callers specify outcomes projectively and derive the ontic counterpart. Currently the caller must supply both and prove the correspondence.

**Pickup:**
1. Build a helper `SectorData.outcomeOfProjective : {Oep : Set P} → MeasurableSet Oep → D.toOntic.OutcomeRegion` that constructs the LF1-side outcome from a projective outcome region (with `Ω := Φ⁻¹(π⁻¹(Oep))` or similar).
2. Prove the correspondence automatically so callers don't need to supply `hCorresp`.

---

## 8. Concrete Sigma / P / G instantiation

**Status:** LF2's `SectorData` is abstract in `(Sigma, P, G)`. LF3 will want a concrete realisation.

**Pickup:**
1. In LF3, take `Sigma := ` a specific phase space (or continue abstract).
2. `P := Projectivization ℂ (EuclideanSpace ℂ (Fin N))` with `[Fintype (Fin N)]`, `[DecidableEq (Fin N)]`.
3. `G := Matrix.specialUnitaryGroup (Fin N) ℂ` (or `Matrix.unitaryGroup` for the full unitary case).
4. Construct the Fubini–Study measure `μFS` as a probability measure on `P` (concretely: via the normalised round measure on the sphere, pushed forward through the quotient `S^{2N-1} → CP^{N-1}`).
5. Verify the invariance / equivariance hypotheses of `SectorData`.

**Depends on:** `Mathlib.LinearAlgebra.Projectivization.Basic`, `Matrix.specialUnitaryGroup` (if available; otherwise construct), the quotient measure theory for compact groups.

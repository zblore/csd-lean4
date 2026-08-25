/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.EpistemicDisintegration
public import CsdLean4.SigmaLayer.PreparationDensity
public import CsdLean4.Mathlib.MeasureTheory.MutuallySingularMap

/-!
# C2: the exact sharp preparation interface is ψ-ontic in the Harrigan–Spekkens sense

**Category:** 7-SigmaLayer (C2 PBR preparation capstone).

**Glossary:** https://glossary.constraintsurfacedynamics.com/does-csd-conflict-with-pbr/
Plain-language, CSD-role and formal statements of CSD's PBR status, with this module —
`pbr_sharp_preparation_capstone` — as its Lean anchor. Kept symmetric by
`scripts/check-glossary.sh`.

## Three claims that are NOT the same claim

This module exists because the corpus previously ran them together, and the C2 companion paper
needs them apart. Read this list before citing anything below.

1. **CSD epistemicity of `[ψ]`.** The projective state is a *many-to-one, incomplete* operational
   coordinate: `π : Σ → ℂℙ^{N-1}` is not injective, and the fibre carries structure the base does
   not. This is a statement about how much of the microstate `[ψ]` determines. It is CSD's own
   sense of "the state is epistemic", and nothing here touches it.

2. **Harrigan–Spekkens ψ-onticity.** A *technical classification of a preparation interface*: an
   interface is ψ-ontic when the ontic measures of distinct exact pure-state preparations are
   **mutually singular** (no overlap), and ψ-epistemic when some distinct pair overlaps. ★★ For the
   canonical **exact sharp** interface, this module proves CSD is ψ-**ONTIC**
   (`sharp_preparations_mutuallySingular`, `epistemicMeasure_mutuallySingular`) — so CSD *satisfies*
   the PBR disjointness conclusion rather than evading it.

3. **Finite-resolution preparation overlap.** Positive-volume *region* preparations
   (`SigmaLayer.Preparation`) with overlapping regions have non-mutually-singular conditional laws
   (`Preparation.conditional_not_mutuallySingular`, `kahler_preparations_overlap`). That is a
   theorem about a **different preparation class** — finite-resolution regions, not exact pure
   states — and it does **not** make the exact interface ψ-epistemic in sense (2).

(1) and (3) are true; (2) says CSD is ψ-ontic on the exact interface. There is no tension: they are
claims about different objects. Conflating (3) with (2) was the error this module corrects.

## What is proved

* `Measure.MutuallySingular.of_map` (Cat-1, `Mathlib/MeasureTheory/MutuallySingularMap.lean`) —
  mutual singularity of pushforwards pulls back along a measurable map. Mathlib carries only the
  forward direction and only for embeddings; this direction needs neither.
* `dirac_mutuallySingular_of_ne` — distinct Diracs are mutually singular.
* `epistemicMeasure_projectiveLaw` — the concrete exact witness `δ_p ⊗ Haar` has projective
  pushforward exactly `δ_p`. C2 must not *assume* this; the repo now shows it.
* ★★ `sharp_preparations_mutuallySingular` — **the general C2 result.** ANY two ontic measures whose
  projective laws are Diracs at distinct points are mutually singular. No `Preparation` structure,
  no region, no finiteness: the hypothesis is the Dirac projective pushforward and nothing else.
* `epistemicMeasure_mutuallySingular` — the concrete corollary, derived through the general theorem
  rather than around it, so the dependency C2 cites is the one the kernel checked.
* `no_region_preparation_exact_fibre` — an exact projective fibre is `kMuL`-null, so it is **not**
  the region of any positive-volume `SigmaLayer.Preparation`.

## ⚠️ What is NOT proved, and must not be inferred

* **Nothing here bears on PBR preparation independence.** PI is a compositional assumption about
  independently prepared systems. This module proves a disjointness statement about single-system
  preparation measures. PI is neither established nor refuted, here or anywhere in the corpus.
* **Global non-factorisation of the composite ontology does NOT imply PI fails.** The Segre-layer
  results (`RecordLayer/OnticComposite.lean`) are composite-*geometry* results. Reading them as a
  PBR contradiction was the superseded Q28 interpretation; see `specs/c2-support-plan.md`.
* **`no_region_preparation_exact_fibre` does not say sharp preparations are illegitimate.** It says
  exact fibre-supported measures are *singular* objects, not obtainable by conditioning `kMuL` on a
  positive-volume region. Singular exact preparations remain a separate admissible interface — that
  is precisely the interface classified in (2).

Reference: `specs/c2-support-plan.md` (the supersession note); `specs/BACKLOG.md` (Q28);
`AXIOMS.md`; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD
namespace RecordLayer

variable {N : ℕ}

/-! ### Distinct Diracs -/

/-- Distinct Dirac measures are mutually singular: `{x}ᶜ` separates them. -/
theorem dirac_mutuallySingular_of_ne {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {x y : α} (h : x ≠ y) :
    (Measure.dirac x).MutuallySingular (Measure.dirac y) := by
  refine ⟨{x}ᶜ, (measurableSet_singleton x).compl, ?_, ?_⟩
  · rw [Measure.dirac_apply]
    simp
  · rw [compl_compl, Measure.dirac_apply]
    simp [h.symm]

/-! ### Part C — the exact sharp witness has a Dirac projective law -/

/-- ★ **The exact sharp preparation has Dirac projective pushforward.**
`δ_p ⊗ Haar` pushed to the base is `δ_p`, because the torus fibre carries a probability measure.

C2 needs this shown rather than assumed: the classification below is stated for *any* measure with
a Dirac projective law, and this is what puts the corpus's own witness inside that class. -/
theorem epistemicMeasure_projectiveLaw (p : LF4.CPN N) :
    Measure.map Prod.fst (epistemicMeasure p) = Measure.dirac p := by
  rw [epistemicMeasure, Measure.map_fst_prod, measure_univ, one_smul]

/-- The same fact in `ProjectiveSector` clothing, for the Kähler base sector. -/
theorem kahlerFstSector_epistemicMeasure_projectiveLaw
    (D : SigmaLayer.ConstraintDynamics (LF4.KSigma N)) (p : LF4.CPN N) :
    (SigmaLayer.kahlerFstSector D).projectiveLaw (epistemicMeasure p) = Measure.dirac p :=
  epistemicMeasure_projectiveLaw p

/-! ### Part D — the general sharp-preparation separation -/

/-- ★★ **The C2 theorem.** Two ontic measures whose projective laws are Dirac at *distinct*
projective states are mutually singular.

This is Harrigan–Spekkens ψ-**onticity** of the exact sharp preparation interface: distinct exact
pure states have no ontic overlap, which is the PBR disjointness conclusion.

The hypothesis is exactly "the projective law is a Dirac" — no `Preparation` structure, no region,
no finiteness, no absolute continuity. Any preparation interface meeting that description is
covered, which is what makes the classification a statement about the *interface* rather than about
one witness.

⚠️ This says nothing about PBR preparation independence. -/
theorem sharp_preparations_mutuallySingular
    {Sigma : Type*} [MeasurableSpace Sigma]
    {D : SigmaLayer.ConstraintDynamics Sigma} (Q : SigmaLayer.ProjectiveSector N D)
    {muPsi muPhi : Measure Sigma} {psi phi : SigmaLayer.ProjectiveState N}
    (hpsi : Q.projectiveLaw muPsi = Measure.dirac psi)
    (hphi : Q.projectiveLaw muPhi = Measure.dirac phi)
    (hne : psi ≠ phi) :
    muPsi.MutuallySingular muPhi := by
  refine Measure.MutuallySingular.of_map Q.measurable_pi ?_
  have hp : Measure.map Q.pi muPsi = Measure.dirac psi := hpsi
  have hq : Measure.map Q.pi muPhi = Measure.dirac phi := hphi
  rw [hp, hq]
  exact dirac_mutuallySingular_of_ne hne

/-! ### Part E — the concrete CSD corollary -/

/-- ★★ **Distinct exact sharp CSD preparations are mutually singular.**

The theorem C2 cites for the concrete witness. Derived *through*
`sharp_preparations_mutuallySingular` and `epistemicMeasure_projectiveLaw` rather than around them,
so the proof graph C2 describes — Dirac projective law, then general separation, then the concrete
pair — is the one the kernel checked. -/
theorem epistemicMeasure_mutuallySingular {p q : LF4.CPN N} (hne : p ≠ q) :
    (epistemicMeasure p).MutuallySingular (epistemicMeasure q) :=
  sharp_preparations_mutuallySingular
    (SigmaLayer.kahlerFstSector
      (SigmaLayer.trivialDynamics (0 : MeasureTheory.FiniteMeasure (LF4.KSigma N))))
    (kahlerFstSector_epistemicMeasure_projectiveLaw _ p)
    (kahlerFstSector_epistemicMeasure_projectiveLaw _ q) hne

/-! ### Part F — an exact fibre is not a positive-volume region -/

/-- ★ **An exact projective fibre is not the region of any `SigmaLayer.Preparation`.**

`Preparation.nonzero_region` demands positive Liouville measure; `kMuL_fibre_null` says the exact
fibre `Prod.fst ⁻¹' {q}` has measure exactly zero. So the two preparation classes are genuinely
disjoint as *objects*, not merely described differently.

⚠️ **This does not say sharp preparations are illegitimate or unphysical.** Its content is narrow
and exact: an exact fibre-supported sharp measure is a **singular** preparation object, and is not
obtainable by ordinary positive-volume Liouville conditioning. That is all it says. Singular exact
preparations remain a separate admissible interface — the one `sharp_preparations_mutuallySingular`
classifies as ψ-ontic. -/
theorem no_region_preparation_exact_fibre (hN : 2 ≤ N) (p₀ q : LF4.CPN N) :
    ¬ ∃ P : SigmaLayer.Preparation
          (SigmaLayer.trivialDynamics
            (⟨LF4.kMuL p₀, inferInstance⟩ : MeasureTheory.FiniteMeasure (LF4.KSigma N))),
        P.region = Prod.fst ⁻¹' {q} := by
  rintro ⟨P, hP⟩
  exact P.nonzero_region (hP ▸ SigmaLayer.kMuL_fibre_null hN p₀ q)

/-! ### Part G — the single citable headline -/

/-- ★★★ **The C2 PBR capstone.** For distinct projective states, the exact sharp CSD preparations
have Dirac projective laws *and* are mutually singular.

The conjunction is the point: the first two conjuncts show the Harrigan–Spekkens hypothesis is
**met** by the corpus's own witness rather than assumed of it, and the third gives the PBR
disjointness conclusion. Citing this one name gives C2 the classification and its premise together.

⚠️ Says nothing about PBR preparation independence. -/
theorem pbr_sharp_preparation_capstone {p q : LF4.CPN N} (hne : p ≠ q) :
    Measure.map Prod.fst (epistemicMeasure p) = Measure.dirac p
      ∧ Measure.map Prod.fst (epistemicMeasure q) = Measure.dirac q
      ∧ (epistemicMeasure p).MutuallySingular (epistemicMeasure q) :=
  ⟨epistemicMeasure_projectiveLaw p, epistemicMeasure_projectiveLaw q,
    epistemicMeasure_mutuallySingular hne⟩

end RecordLayer
end CSD

#!/usr/bin/env bash
# check-claims.sh
#
# Machine-enforces the QUANTITATIVE / SEMANTIC honesty claims that the other
# guards (check-connectivity / check-sector-linkage / check-axiom-imports) do
# NOT check — the drift surface where the "nine vs eleven" and "hpos" desyncs
# lived. The canonical facts are the CLAIMS block below (single source of truth,
# version-controlled, diffable); the checks assert the CODE matches them.
#
# It checks:
#   (1) the imported-axiom SET (real `axiom` declarations, comments stripped)
#       equals the declared set  — the "exactly one axiom" claim.
#   (2) the `:= True` placeholder SET equals the declared inventory
#       — catches new vacuity regressions.
#   (3) FiniteQMClosure has the declared number of fields
#       — catches the "nine vs eleven" class of drift.
#   (4) every declared backing theorem still EXISTS as a declaration
#       — catches a rename/deletion silently orphaning a CONNECTED claim.
#   (5) the forbidden A5-overclaim phrases are absent from the forward-claim docs.
#   (6) EPISTEMIC STATUS: no settled-claim word ("provably", "DISSOLVED", "is
#       complete") sits beside a non-proof artifact (a Python experiment, numerics,
#       a hypothesis field), and a blocklist of never-acceptable phrases is absent.
#       Added 2026-07-28. Regression-tested against commit 4a31220: it fires on all
#       three overclaims an external review found there, plus three more instances
#       of the same class that a manual sweep had missed.
#
#       KNOWN LIMIT — it is a co-occurrence rule, so it only sees an overclaim that
#       cites weak evidence ON THE SAME LINE. A bare "the goal is met", with nothing
#       weak beside it, is invisible to it; two such lines in reconstruction-status.md
#       had to be found by reading. This check narrows the surface; it does not close it.
#       Checks (7) and (8) below were added to attack exactly that residue.
#   (7) SYMPLECTIC-VOCABULARY INVENTORY: every declaration whose NAME contains a
#       load-bearing geometric word (Liouville / symplectic / Kähler) must appear in
#       the declared inventory, each entry carrying the arena and its DIMENSION PARITY.
#       Added 2026-08-04 after the fifth external review found `nullSeamLiouville` on
#       S^1 x CP^2 — real dimension 5, ODD, hence not symplectic, so "Liouville" was
#       unearned. The name was a claim in an identifier, where nothing could check it.
#       This is the corpus's SECOND odd-dimension slip (the fibred-Σ mislabel was the
#       first), which is why it gets a guard rather than a resolution to be careful.
#       Set equality, so a NEW such name fails loudly and forces a conscious parity
#       justification; renaming to a construction-describing name (nullSeamMeasure)
#       is the other way to pass.
#   (7d) ABSTRACT-SIGMA INSTANTIATIONS: every declaration whose RESULT type is
#       `KahlerOnticSetup` must appear in a declared inventory with a verified EVEN
#       Sigma parity. Added 2026-08-06 (BACKLOG D2): (7a-c) see NAMES, so an abstract
#       setup — whose `Sigma` is a structure field with no parity claim of its own —
#       could be instantiated at an odd-dimensional Sigma with no name changing.
#   (8) OPEN-SCOPE INVENTORY: per-file counts of the honest-scope phrases ("remains
#       open", "recorded extension", "not claimed here"). Added 2026-08-04, same
#       review: MeasurementCapstone.lean still said the conditioned mixed update
#       "remains open" hours after MixedLuders.lean closed it.
#
#       KNOWN LIMIT (narrowed 2026-08-06, not closed) — this fires when such a claim is
#       ADDED or REMOVED, not when the underlying fact changes underneath a claim that
#       stays put. Check (8b) attacks the tracked half of that residue.
#
#       ASYMMETRY, recorded 2026-08-06: this whole family polices OVERclaim. An
#       UNDERclaim — a doc selling the corpus short — is invisible to every check here.
#       Exhibit: README carried "Born statistics established at the selector level only"
#       for two days after povm_sector_born discharged it; nothing fired, because no
#       guard has a notion of a doc claiming less than the theorems deliver. Accepted as
#       out of scope (an underclaim is honest, merely stale); the release-pass discipline
#       — re-read the front page at each tag — is the compensating control.
#   (8b) SCOPE-EXPIRY LEDGER: each open-scope file carries the BACKLOG row its boundary
#       waits on (or `none`); when that row is struck DONE, this FAILS until the site
#       is re-read and superseded at source. Added 2026-08-06 (BACKLOG D1). The `none`
#       half — permanent boundaries and rowless extensions — remains untracked by
#       construction; the improvement is that every boundary is now CLASSIFIED, and
#       the tracked ones expire mechanically.
#
# Scope: the core QM library. (The ecdsa.fail / ECDLP track was extracted to its own
# repository 2026-07-20 and is no longer present here.)
#
# Usage:  bash scripts/check-claims.sh   (grep/awk only, no Lean build)
#
# PERFORMANCE — this header said "seconds" for a year; measured 2026-08-04 on
# Windows/git-bash it was 6m51s (user 1m05, sys 7m35: almost pure process-spawn
# cost, ~2500 forks from the per-file `while read` loops in checks (1) and (2)).
# "Seconds" was a Linux-CI figure that never held on the author's machine, which is
# why a guard advertised as pre-commit-cheap was in practice only ever run inside
# the long gate chain. Checks (1) and (2) now batch through xargs with a raw-grep
# fast path, and the newer checks (7)/(8) batch by construction.

set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
SRC="CsdLean4"

# ------------------------------------------------------------------ CLAIMS ----
# THE canonical source of truth. Update HERE when the code legitimately changes;
# the checks below fail loudly if code and these facts disagree.
#
# ZERO imported axioms. `busch_effect_gleason` was the last one; it was discharged
# 2026-07-21 (proved in LF2/EffectGleason.lean as
# `OperationalPackage.effect_gleason_representation`). The corpus now stands on the
# foundational triple alone (propext / Classical.choice / Quot.sound); even the
# measure-bridge realisers `cp_measure_bridge` / `k_measure_bridge` are proved
# theorems, not axioms (see AXIOMS.md §2). This gate now fails loudly on ANY
# `^axiom ` declaration under CsdLean4/ — the zero-axiom posture.
DECLARED_AXIOMS=""

# All Kähler `:= True` placeholders were de-vacuumed 2026-07-19 (IsKahlerSector →
# IsFubiniStudyKahler, the proved pointwise FS Kähler compatibility; the trivial
# witness's IsLiouvilleKahlerVolume → IsProbabilityMeasure). Inventory now empty:
# a new `:= True` anywhere is a fresh vacuity regression the check below catches.
DECLARED_PLACEHOLDERS=""

FINITEQMCLOSURE_FIELDS=11

DECLARED_BACKING_THEOREMS="unifiedFiniteQMClosure
unified_projectiveSector_capstone
manyToOneSchrodingerSetup_both_pillars
manyToOneSchrodingerSetup_schrodinger_derived
bornRegion_fs_measure
born_frequency_convergence_N
conditioning_luders_effect_equivalence
flow_admits_invariant_ne_fubiniStudy
compositeAlgReconstruction"

FORBIDDEN_PHRASES=(
  "A5 is closed"
  "the sector is no longer posited"
  "derives the sector from the deterministic flow"
)
# Docs that make FORWARD claims and so must never contain the overclaims — even
# as text. (connectivity-manifest.md legitimately QUOTES them in its ❌ list, so
# it is deliberately NOT scanned here; check-connectivity covers README/INDEX.)
FORWARD_DOCS=("README.md" "specs/reconstruction-status.md")

# The A5-mislabel aliases. Paper C's Axiom A5 is the *quantum-effective /
# projectability* condition on Hamiltonians (H = h∘π + δH, sup‖d(δH)|_V‖ ≤ ε), which
# SELECTS the sector — it is NOT the sector-origin question. The sector-origin gap
# (the origin of (Σ,π,μL)) is SO-1. These aliases wrongly attach "A5" to the origin
# and MUST NOT reappear in the forward-claim doc surface. (SO-1 was formerly, and
# also wrongly, tracked as "SL-1".)
FORBIDDEN_ALIASES=(
  "A5 / SL-1"
  "A5/SL-1"
  "A5 sector origin"
  "A5→D1"
  "A5 → D1"
)
# Cleaned forward-claim docs (all swept in the 2026-07-23 honest-alignment closeout).
# Unlike FORWARD_DOCS above, these do NOT quote the old overclaims, so they can be
# scanned for the new aliases without false positives.
ALIAS_DOCS=("README.md" "AXIOMS.md" "CLAUDE.md" "specs/reconstruction-status.md" \
            "specs/connectivity-manifest.md" "specs/INDEX.md" "specs/BACKLOG.md" \
            "specs/future-work.md")

# ------------------------------------------------------ EPISTEMIC-STATUS SCAN --
# Added 2026-07-28 after an external review found three overclaims that every
# existing guard passed over silently. The defect class is NOT a false statement —
# it is a STRONG claim word attached to a WEAK artifact:
#
#   "provably dead"                 cited to a Python experiment + an informal argument
#   "DISSOLVED — not a research problem"   while the same doc and the Lean docstring
#                                          both said the obligation was open
#   "the reconstruction of QM is complete" while the partition was prep-indexed
#
# None of (1)–(5) can see this: they check axiom sets, field counts, declaration
# existence and a fixed A5 phrase list. This one is a CO-OCCURRENCE rule — a strong
# word is only a defect when the evidence cited beside it is weak — plus a small
# blocklist of phrases that are never acceptable unretracted.
#
# Lines that are themselves RETRACTIONS are exempt, otherwise the scan fires on its
# own corrections (which necessarily quote the old wording).
# 2026-07-29: sigma-fibre-contextuality.md was NOT in this list and so was never scanned --
# it still read "necessarily in the fibre" three days after that claim was retracted
# elsewhere. A scan is only as good as its file list; add new claim docs here.
EPISTEMIC_DOCS=("README.md" "EMPIRICAL.md" "AXIOMS.md" "specs/BACKLOG.md" \
                "specs/record-layer-plan.md" "specs/active-todo.md" \
                "specs/CSD-CHARTER.md" "specs/reconstruction-status.md" \
                "specs/connectivity-manifest.md" "specs/future-work.md" \
                "specs/INDEX.md" "specs/sigma-fibre-contextuality.md")

# Words asserting that something is SETTLED.
EPISTEMIC_STRONG='provably|proves|proved|proven|no-go|[Dd]issolved|DISSOLVED|discharged|is complete|are complete|fully solved|settled|refuted|NOT A TARGET|confirmed dead'

# Markers that the ARTIFACT being cited is not a proof.
#
# Deliberately narrow. The first draft also listed "posited", "assumed", "conjecture",
# "informal" — and fired on five honest README lines, because those words are how a
# careful author FLAGS weak evidence. Penalising them would train exactly the wrong
# behaviour. Only artifact types belong here: a script, a number, a hypothesis field.
# Specific known-bad wordings are handled by the blocklist below instead.
EPISTEMIC_WEAK='scripts/experiments|\.py\b|numerics|numerically|Monte Carlo|hypothesis field'

# Retraction / self-correction context — these lines legitimately quote the bad wording.
EPISTEMIC_EXEMPT='retracted|RETRACTED|overclaim|overstated|was wrong|is lifted|no business|previously read|previously ended|corrected 20|CORRECTED 20|Corrected 20'

# Phrases that are never acceptable outside a retraction, whatever else the line says.
EPISTEMIC_BLOCKLIST=(
  "provably dead"
  "reconstruction of QM is complete"
  "no separate flow to derive"
  "not a research problem"
  # E5(b), 2026-08-23. E4 (Thermo/Equilibration.lean) is a CONDITIONAL: its
  # consequent holds only given (i) a mu_FS-preserving flow and (ii) quantitative
  # correlation decay with a summable envelope. Neither is proved for any Sigma, and
  # not_hasCorrelationDecay_blockPop_of_periodic shows periodic flows CANNOT satisfy
  # (ii) for a nontrivial subsystem. These phrasings drop the antecedent and are the
  # exact overclaim the arc plan asked to be blocked at the doc surface.
  "equilibration is derived"
  "equilibration is proved"
  "the flow is shown to mix"
  "mixing is established"
  "CSD derives thermalisation"
  "CSD derives thermalization"
)
# ------------------------------------------------------------------------------

fail=0
say_fail() { echo "  FAIL  $1"; fail=1; }
say_ok()   { echo "  ok    $1"; }

# Strip Lean block comments (/- .. -/, /-- .. --/, /-! .. -/) so docstring prose
# beginning with a keyword is not mistaken for a declaration.
strip_comments() {
  awk '
    { line = $0
      while (length(line) > 0) {
        if (inc) { i = index(line, "-/"); if (i == 0) { line=""; break }
                   line = substr(line, i+2); inc = 0 }
        else     { i = index(line, "/-"); if (i == 0) break
                   pre = substr(line, 1, i-1); line = substr(line, i+2); inc = 1
                   printf "%s\n", pre }
      }
      if (!inc && length(line) > 0) print line
    }' "$1"
}

srcfiles() { git ls-files "$SRC/**/*.lean" 2>/dev/null; }

# --------------------------------------------- SYMPLECTIC-VOCABULARY INVENTORY --
# Declarations whose NAME asserts geometric content. Each MUST record the arena and
# its real-dimension parity: symplectic/Kähler/Liouville require EVEN dimension.
# Adding a name here is a claim; if you cannot fill in the parity line, rename the
# declaration after its construction instead (e.g. `…Measure`, not `…Liouville`).
DECLARED_SYMPLECTIC_VOCAB="arenaLiouville
fieldHamiltonian
interactionHamiltonian
hamiltonianField
hamiltonian
hamiltonianVectorFieldOf
HasHamiltonianRealisation
IsForcedKahlerVolume
IsFubiniStudyKahler
kahlerConstraintDynamics
kahlerFstSector
KahlerOnticSetup
kahlerProjectiveSector
ofKählerPreparation
ofKählerPreparationFlow
pointerLiouville
relFieldHamiltonian
trivialKahlerOnticSetup"
#
# PARITY LEDGER (why each name is earned).
# ⚠️ Corrected 2026-08-04, same day it was written: the first draft asserted "all on
# CP^{N-1} (x T^2) sectors: even factors only" for five names at once. Three of them
# do not fix an arena at all — they abstract over `Sigma : Type*` — so a parity claim
# about them was not merely unverified, it was not even well-formed. Writing an
# unchecked justification into the guard that exists to stop unchecked justifications
# is precisely the failure mode this check is for; it was caught by reading the
# definitions when asked whether the check had actually been run.
#
#   HAMILTONIAN NAMES — the word was added to this check 2026-08-04. CONVENTIONS 8.3a
#   listed "Hamiltonian" as claim-bearing from the day it was written, but the guard's
#   pattern did not include it — which is exactly how `shear_piecewise_hamiltonian` (a
#   THEOREM; see the theorem-level inventory below) escaped the sweep that caught
#   `nullSeamLiouville`. The rule and the guard disagreed, and the guard lost. For these
#   the question is not parity but GENERATOR EXHIBITED?:
#     hamiltonian / fieldHamiltonian / relFieldHamiltonian — CV energy matrices: Hermitian,
#       with eigenvalue equations proved. The word names an OPERATOR, not a flow.  EARNED.
#     interactionHamiltonian — (Interaction.lean, CV-7, 2026-08-07) diagonal real
#       potential matrix: Hermitian PROVED (interactionHamiltonian_isHermitian) and the
#       GENERATOR ROLE EXHIBITED — interactingU_eq_exp proves the drive is
#       exp(-(i tau).(H_field + lam.V)). Same pattern as fieldHamiltonian.       EARNED.
#     hamiltonianField — (ChartBracket.lean, A3) the vector field `(∂_y H, −∂_x H)` in a
#       DARBOUX CHART, written out explicitly. The name is earned because in canonical
#       coordinates the field IS that formula: no `ω⁻¹` is invoked, nothing is asserted.
#       Caught by this very check when it was added, 2026-08-04.        EARNED (chart-level).
#     HasHamiltonianRealisation — a Prop DEMANDING an explicit Hermitian `H` with
#       `U t = exp(-itH)`; `productProjectedFlow_hasHamiltonianRealisation` exhibits one.
#       This is CONVENTIONS 8.3a option (1) done right.                            EARNED.
#     hamiltonianVectorFieldOf — (HamiltonianVectorField.lean, A4's linear fragment,
#       2026-08-06) the ω-dual `-(J w)` of a gradient representative. The word is earned
#       by the DEFINING-EQUATION THEOREM in the same module:
#       `fundamentalForm_hamiltonianVectorFieldOf` proves `ω (X w) v = g w v`, i.e.
#       `ι_X ω = dH` once `w` is the gradient (`hamiltonian_duality`). Flat model,
#       constant ω; the manifold statement stays §2a.                EARNED (linear-level).
#
#   CONCRETE ARENA — parity verified by reading the definition:
#     arenaLiouville          — UnifiedArena: CP^{N-1} x T^2 x (bank), even factors.  EVEN.
#     pointerLiouville        — PointerArena: CP^{N-1} x T^2 x CP^K, 2(N-1)+2+2K.     EVEN.
#     IsFubiniStudyKahler     — pointwise Kähler compatibility on a complex
#                               inner-product space (KahlerForm.lean); complex ⇒      EVEN.
#     IsForcedKahlerVolume    — `Measure (CPN N)`, i.e. CP^{N-1}: dim 2(N-1).         EVEN.
#     trivialKahlerOnticSetup — Sigma := ℙ ℂ (EuclideanSpace ℂ (Fin N)) = CP^{N-1}.   EVEN.
#     ofKählerPreparation(Flow) — CPN 4 = CP^3, dim 6.                                EVEN.
#
#   kahlerFstSector — (2026-08-21, Q28, SigmaLayer/PreparationDensity.lean) the base
#     projection of the CONCRETE Kähler arena `KSigma N = ℂℙ^{N-1} × T²` as a
#     ProjectiveSector. Real dimension 2(N−1) + 2 — EVEN. The word names the arena the
#     declaration is anchored to (same referent as kMuL/KSigma), not a new Kähler claim.
#   ABSTRACT ARENA — NO parity claim is made or possible here:
#     KahlerOnticSetup        — a structure with `Sigma : Type*` as a FIELD.
#     kahlerConstraintDynamics / kahlerProjectiveSector
#                             — both consume `K : KahlerOnticSetup N` and work on
#                               `K.Sigma`, whatever that is.
#     For these the parity obligation belongs to whoever INSTANTIATES them; the only
#     concrete instantiations in-tree (trivialKahlerOnticSetup, ManyToOnePillars) use
#     CP^{N-1} and are even. A future instantiation on an odd-dimensional Sigma would
#     be a real defect that this check cannot see.
# REJECTED 2026-08-04: `nullSeamLiouville` on S^1 x CP^2 — dim 1 + 4 = 5, ODD. Renamed
# `nullSeamMeasure`; the T^2 x CP^2 lift that would earn the word is a BACKLOG row.

# --------------------------------------- (7d) ABSTRACT-SIGMA INSTANTIATIONS ----
# Closes check (7)'s documented blind spot (BACKLOG D2, closed 2026-08-06): the
# vocabulary checks see NAMES, so an abstract `KahlerOnticSetup` — whose `Sigma` is a
# structure field carrying no parity claim of its own — can be INSTANTIATED at an
# odd-dimensional Sigma without any name anywhere changing. The corpus has hit the
# odd-dimension slip twice (the fibred-Σ mislabel; `nullSeamLiouville` on S¹×ℂℙ²), so
# instantiation sites get the same set-equality treatment as names: every declaration
# whose RESULT type is `KahlerOnticSetup` must appear here, each with its concrete
# `Sigma` and a verified EVEN real dimension.
DECLARED_KAHLER_INSTANTIATIONS="manyToOneRotationSetup
manyToOneSchrodingerSetup
manyToOneSetup
rotationSetup
trivialKahlerOnticSetup
unitaryFlowSetup"
#
# INSTANTIATION PARITY LEDGER (each read from its `Sigma :=` field, 2026-08-06):
#   trivialKahlerOnticSetup   — Sigma := ℙ ℂ (E^N) = ℂℙ^{N-1}, dim 2(N-1).          EVEN.
#   unitaryFlowSetup          — Sigma := ℙ ℂ (E^N) = ℂℙ^{N-1}.                       EVEN.
#   rotationSetup             — = unitaryFlowSetup 2 rotU p₀ (ℂℙ¹, dim 2).           EVEN.
#   manyToOneSetup            — Sigma := KSigma N = ℂℙ^{N-1} × T², dim 2(N-1)+2.     EVEN.
#   manyToOneRotationSetup    — rides manyToOneSetup at N = 2 (dim 4).               EVEN.
#   manyToOneSchrodingerSetup — rides manyToOneSetup (dim 2(N-1)+2).                 EVEN.
# A new instantiation must add its row here WITH the parity computation, or the check
# fails loudly. Consumers (declarations taking a KahlerOnticSetup argument) are exempt:
# they inherit whatever parity their argument has and assert nothing.

# ------------------------------------------------------- OPEN-SCOPE INVENTORY --
# Per-file counts of honest-scope phrases. These are GOOD — they are how a module
# states its boundary — so this is not a budget to drive to zero; it is a diffable
# ledger so that a boundary claim cannot go stale unnoticed when the work lands.
DECLARED_OPEN_SCOPE="CsdLean4/CV/ChannelRG.lean:1
CsdLean4/CV/CompositeArena.lean:1
CsdLean4/CV/DispersionEarned.lean:1
CsdLean4/CV/EntangledWeights.lean:1
CsdLean4/CV/FibredArenaBridge.lean:1
CsdLean4/CV/LocalAlgebraClosed.lean:1
CsdLean4/CV/PriceAttainment.lean:1
CsdLean4/CV/SupportSpreading.lean:1
CsdLean4/Empirical/QM/QEC/ErrorDiscretization.lean:1
CsdLean4/LF4/PhaseLift.lean:1
CsdLean4/LF4/TypicalityForcing.lean:1
CsdLean4/RecordLayer/ApproxProjectability.lean:1
CsdLean4/SigmaLayer/FiniteQMClosure.lean:1
CsdLean4/RecordLayer/MeasurementCapstone.lean:2
CsdLean4/RecordLayer/MixedLuders.lean:1
CsdLean4/RecordLayer/MixedSwap.lean:1
CsdLean4/RecordLayer/PointerBorn.lean:1
CsdLean4/RecordLayer/PointerGeneration.lean:2
CsdLean4/RecordLayer/PointerLudersMarginal.lean:1
CsdLean4/RecordLayer/PovmDynamics.lean:2
CsdLean4/RecordLayer/PovmSectorBorn.lean:1
CsdLean4/RecordLayer/RecordLayerClosure.lean:1
CsdLean4/Tests/AxiomAudit/MathlibStaging.lean:2
CsdLean4/Tests/AxiomAudit/SigmaLayer.lean:2"

# --------------------------------------------- (8b) SCOPE-EXPIRY LEDGER --------
# Closes check (8)'s documented blind spot (BACKLOG D1, closed 2026-08-06): (8) fires
# when a boundary claim is ADDED or REMOVED, never when the fact beneath a claim that
# stays put changes. This ledger names, for each open-scope FILE above, the BACKLOG row
# its boundary waits on — `none` for permanent physics/architecture boundaries and for
# supersession records (struck notes kept as history). The check fires when a named row
# is struck DONE (`| ~~TAG~~ |`) in BACKLOG.md while the file still carries its boundary:
# the fix is to re-read the site, supersede the stale note at source, and re-tag `none`.
#
# Motivating case, found while building this ledger: PointerGeneration.lean still said
# the Lüders composition "is a recorded extension, not delivered here" a day after B3b
# delivered it — the exact staleness class, silent under (8) because the claim never
# moved. (Fixed at source the same commit.)
#
# KNOWN LIMIT — a `none` tag is an untracked boundary: fine for genuinely permanent
# scope (physics, architecture, supersession records), wrong if the boundary actually
# waits on unlabelled work. §E items now carry stable IDs (E1–E5) so long-horizon waits
# are taggable; foundations-frontier waits (MD-1, §2a) have no BACKLOG row and stay
# `none` with the wait named in the site's own prose.
DECLARED_SCOPE_WAITS="CsdLean4/CV/ChannelRG.lean|none
CsdLean4/CV/CompositeArena.lean|none
CsdLean4/CV/DispersionEarned.lean|none
CsdLean4/CV/EntangledWeights.lean|Q27
CsdLean4/CV/FibredArenaBridge.lean|none
CsdLean4/CV/LocalAlgebraClosed.lean|none
CsdLean4/CV/PriceAttainment.lean|none
CsdLean4/CV/SupportSpreading.lean|none
CsdLean4/Empirical/QM/QEC/ErrorDiscretization.lean|none
CsdLean4/Empirical/QM/QEC/SyndromeCollapse.lean|none
CsdLean4/LF4/PhaseLift.lean|none
CsdLean4/LF4/TypicalityForcing.lean|none
CsdLean4/RecordLayer/ApproxProjectability.lean|none
CsdLean4/SigmaLayer/FiniteQMClosure.lean|none
CsdLean4/RecordLayer/MeasurementCapstone.lean|none
CsdLean4/RecordLayer/MixedLuders.lean|none
CsdLean4/RecordLayer/MixedSwap.lean|none
CsdLean4/RecordLayer/PointerBorn.lean|none
CsdLean4/RecordLayer/PointerGeneration.lean|none
CsdLean4/RecordLayer/PointerLudersMarginal.lean|none
CsdLean4/RecordLayer/PovmDynamics.lean|none
CsdLean4/RecordLayer/PovmSectorBorn.lean|none
CsdLean4/RecordLayer/RecordLayerClosure.lean|none
CsdLean4/Tests/AxiomAudit/MathlibStaging.lean|none
CsdLean4/Tests/AxiomAudit/SigmaLayer.lean|none"
# WAIT LEDGER (why each tag):
#   SyndromeCollapse|none — was tagged E1; ShorNine.lean landed the concatenated code
#     (2026-08-13) and the boundary was superseded at source, so the tag retired exactly
#     as the mechanism intends (supersession record kept in the module docstring).
#   MixedLuders|none — was tagged D3 when the ledger was built; D3a landed the same day
#     (MixedJoinLuders.lean) and the note was superseded at source, so the tag retired
#     exactly as the mechanism intends.
#   ErrorDiscretization / MeasurementCapstone / MixedSwap / PovmDynamics(1 of 2) —
#     supersession records: struck notes kept as history, nothing waited on.
#   ArenaBridge|(retired 2026-08-20) — was tagged none as "the P1 boundary: re-read on
#     any P1 landing". P1 landed in full (FieldStructuredFlow.lean and
#     FibredArenaBridge.lean, both 2026-08-20) and the boundary note was superseded at source,
#     so the entry retired exactly as the mechanism intends.
#   CompositeArena|none — architecture boundary stated at the P2 close (2026-08-20):
#     homogeneous field sectors (same level count N, mode-disjoint composition — the
#     field-native case). Heterogeneous composites need the arena API generalised over
#     its index type: a rule-of-two note on ArenaBridge, not a queued row. Also states
#     that composite mixed-state theory is CV-26 coarse-graining territory by design.
#   EntangledWeights|Q27 — boundary stated at the Q27 first-brick landing (2026-08-20):
#     the Fin-indexed LF2 mixed-tier transport of the delivered re tr(reducedDM·A) form
#     is declared index plumbing and not claimed; sequential/record-conditioned versions
#     are Q25's territory. Tagged Q27 so the note is force-re-read when the row is struck.
#   LindbladPositivity|(retired 2026-08-21) — was tagged none at the Q16 CP-brick landing
#     as "the id-tensor-Phi identification is the named remainder". The remainder was
#     queued as Q23 the same day and Q23 delivered it (idTensor_lindbladSemigroup +
#     lindbladSemigroup_completelyPositive); the boundary note was superseded at source
#     (supersession record kept in the module docstring), so the entry retired exactly
#     as the mechanism intends.
#   DispersionEarned|none — permanent physics boundary stated at the P4 close (2026-08-20):
#     the identification of the (E,p) light rays with the dynamical Lieb-Robinson cone is
#     not made — the LR cone is an upper bound with a model-dependent velocity, not an
#     exact invariant set. Kinematic scope inherited from Boost.lean (no lattice boost
#     action). No queued row; making the identification would be a new scoping decision.
#   FibredArenaBridge|none — permanent scope boundary stated at the P1 close (2026-08-20):
#     fibre activity is the STROKE shape (base-dependent fibre shifts, the corpus's own
#     ShearWitness record mechanism); continuous-time skew flows with base-coupled fibre
#     VELOCITY are a stronger class nothing in the record layer needs. Covering them
#     would be a new scoping decision, not the discharge of this boundary — no row.
#   ChannelRG|none — permanent physics boundaries stated at CV-26 (2026-08-18): one
#     coarse-graining step and not an RG flow (no iteration, no fixed point, no beta
#     function); mode tracing only, level decimation unselected pending a leakage
#     estimate; the budget uniform in distance. None of these waits on a queued row —
#     an RG flow would be a new scoping decision, not the discharge of this boundary.
#   PhaseLift / TypicalityForcing / ApproxProjectability / FiniteQMClosure /
#   RecordLayerClosure — architecture/foundations boundaries (§2a wall, ergodicity
#     substrate, MD-1 frontier): no BACKLOG row; the wait is named in the site's prose.
#   PointerBorn / PointerGeneration / PointerLudersMarginal / PovmSectorBorn /
#   PovmDynamics(2 of 2) — recorded extensions without a BACKLOG row (mixed-ε weights,
#     Hamiltonian relocation stroke, V-as-unitary-stroke): boundaries by design, not
#     queued work; if one becomes a row, re-tag it here.
#   SupportSpreading / LocalAlgebraClosed — the CV-6 boundary, narrowed three times
#     exactly as the ledger intended (CV-8 spreading bound; CV-9 pricing; CV-11 the
#     non-diagonal KICKED cone 2026-08-09, SupportSpreading re-read and re-worded at
#     source). What stands now: both wait on the full-exponential cone = Lieb-Robinson,
#     the promoted Stage-5 headline (eft-stage4-plan horizon note; gated on CV-12, no
#     Ref yet). Re-read both when Stage 5 opens.
#   InteractionPrice|(retired 2026-08-20) — waited on attainment; P5-attainment landed
#     (CV/PriceAttainment.lean) and the boundary was superseded at source (both halves:
#     attainment closed, and the non-diagonal-cone half had been stale since CV-11),
#     so the entry retired exactly as the mechanism intends.
#   PriceAttainment|none — scope boundary stated at the P5-attainment close (2026-08-20):
#     attainment is an existence claim discharged by one witness (K = N = 2, one coupling
#     shape); the exact-distance identification on the witness and constant-matching
#     (1/π vs 2) are not claimed. No queued row; sharpening constants would be a new
#     scoping decision."

# (7b) STRUCTURE FIELDS carrying the same vocabulary. Found 2026-08-04 immediately
# after (7a) shipped: `liouvilleMeasure`, `IsKahlerSector` and friends are structure
# FIELDS, and (7a)'s regex is anchored to `def|abbrev|structure`, so it never saw
# them. A name is a claim wherever it appears, not only at top level.
# Matches declarations (`name : Type`) and deliberately not instantiations
# (`name := value`), which are uses of an already-declared field.
# Inventory updated 2026-08-06 (G3 / F-04 tightening): the abstract pairs
# IsKahlerSector/kahler_condition and IsLiouvilleKahlerVolume/liouville_eq_kahler_volume
# were replaced by CONCRETE fields, each carrying its justification in the field type:
#   kahler_pointwise : IsFubiniStudyKahler N  (the proved pointwise FS Kahler triple;
#     flat d-omega = 0 also proved, KahlerClosed.lean 2026-08-06)
#   liouville_isProbability : IsProbabilityMeasure liouvilleMeasure  (normalized volume,
#     an instance)
DECLARED_VOCAB_FIELDS="kahler_pointwise
liouville
liouvilleMeasure
liouville_isProbability"
#
# FIELD LEDGER: all six are fields of `KahlerOnticSetup` (LF4/KahlerOnticSetup.lean),
# whose `Sigma` is abstract — so, as above, they carry no parity claim in themselves.
# Note `IsKahlerSector : Prop` and `IsLiouvilleKahlerVolume : Prop` are the honest
# shape: the Kähler and Liouville conditions are *obligations the instantiator must
# discharge*, not adjectives asserted by fiat. That is CONVENTIONS 8.3a option (1),
# and it is why these names are earned where a bare `…Liouville` would not be.

# (7c) THEOREM/LEMMA names carrying the vocabulary. Most inherit their object's word
# (`trivialKahlerOnticSetup_*`, `hamiltonian_*`) and assert nothing new; the ones that
# matter are those whose name states a CLASSIFICATION, and this inventory exists to keep
# exactly those visible. Two are worth naming:
#   shear_piecewise_hamiltonian — KNOWN MISNOMER, retained for pin stability. Its own
#     module header withdrew the Hamiltonian reading (torus flux: `ι_Xω = a·dp` is closed
#     but NOT exact on T^2, so no global generator exists) and gives the correct name,
#     "piecewise rigid symplectic translation". Its statement proves ContinuousOn per basin
#     cylinder plus a null seam set — no generator, no symplectic form, no flow appears in
#     it. Declared here so the exception is VISIBLE rather than silent.
#   schrodinger_flow_kahler_symplectomorphism — read 2026-08-04: an FS-isometry statement;
#     "symplectomorphism" is carried by the pointwise Kähler triple (KahlerForm.lean),
#     which is proved. No manifold-level symplectic claim is made.
#   fundamentalForm_hamiltonianVectorFieldOf / hamiltonian_duality /
#   quadraticEnergy_hamiltonian_duality / coupling_hamiltonian_duality — (2026-08-06,
#     HamiltonianVectorField.lean + PointerHamiltonianField.lean, A4's linear fragment)
#     each PROVES an ι_Xω = dH statement — the word names the established duality, with
#     the Schrödinger field -(i•Ax) exhibited explicitly in the quadratic/coupling cases.
#     Flat model, fixed weights; the joint-arena manifold form stays §2a.
#   kSectorData_fromPreparation_liouville_apply — (2026-08-12, witness suite WS-D)
#     inherits the word from the production OperationalPackage.fromPreparation_
#     liouville_apply it instantiates; the statement genuinely concerns the Liouville
#     preparation (the package built from kMuL). No new Liouville claim.
#   kahlerFstSector_projectiveLaw / kahler_preparation_density /
#   kahler_preparations_overlap — (2026-08-21, Q28 items 3-4,
#     SigmaLayer/PreparationDensity.lean) all three are statements ABOUT the concrete
#     Kähler arena KSigma N (the c = 1 base pushforward of kMuL; ρ_ep against μFS; the
#     ψ-epistemic overlap witness). The word names the arena — the same earned referent
#     as kMuL/kahlerFstSector — and no new Kähler-structure claim is made.
DECLARED_VOCAB_THEOREMS="arenaLiouville_cylinder
kahlerFstSector_projectiveLaw
kahler_preparation_density
kahler_preparations_overlap
kSectorData_fromPreparation_liouville_apply
arenaLiouville_sys_marginal
coupling_hamiltonian_duality
fieldHamiltonian_mulVec_single
fubiniStudy_pointwise_kahler_compatibility
fundamentalForm_hamiltonianVectorFieldOf
hamiltonian_duality
fubiniStudyMeasure_isForcedKahlerVolume
hamiltonian_eq_diagonal
hamiltonian_groundEnergy
fieldHamiltonian_isHermitian
hamiltonian_isHermitian
interactionHamiltonian_isHermitian
hamiltonian_mulVec_single
isFubiniStudyKahler
kahler_robertson_ontic_variance
kahler_structure_isometry_invariant
kahlerConstraintDynamics_flow
kahlerProjectiveSector_pi
manyToOneSetup_baseVolume_isForcedKahlerVolume
manyToOneSetup_liouville_eq_product
ofKählerPreparation_singlet_frequency_convergence
ofKählerPreparationFlow_flow_frequency_convergence
ofKählerPreparationFlow_phi_ne_id
ofKählerPreparationFlow_preEvent
pointerLiouville_arenaReady
productProjectedFlow_hasHamiltonianRealisation
quadraticEnergy_hamiltonian_duality
relFieldHamiltonian_isHermitian
relFieldHamiltonian_mulVec_single
schrodinger_flow_kahler_symplectomorphism
shear_piecewise_hamiltonian
trivialKahlerOnticSetup_bargmann_selection
trivialKahlerOnticSetup_eq_unitary_family
trivialKahlerOnticSetup_phase_lift
trivialKahlerOnticSetup_projective_representation
trivialKahlerOnticSetup_projUnitary
trivialKahlerOnticSetup_schrodinger_form
trivialKahlerOnticSetup_sigmaFlow_schrodinger_form
trivialKahlerOnticSetup_transProbPreserving
trivialKahlerOnticSetup_unitary_of_clopen
trivialKahlerOnticSetup_unitary_or_antiunitary
unitaryFlowSetup_liouville_isForcedKahlerVolume
unitaryFlowSetup_liouville_isProbability"

OPEN_SCOPE_PHRASES='remains open|recorded extension|not claimed here'

# ------------------------------------------------- (7e) GROUP-NAMING INVENTORY --
# Added 2026-08-20 after the SU(N)/U(N) fix. Every definition and theorem in the
# Fubini-Study layer quantifies over Matrix.unitaryGroup = U(N), but docstrings said
# "SU(N)" for a year — recorded by necessity-audit item 13 (2026-08-09) yet never
# fixed, because audit findings have no expiry hook. This check is the mechanical
# residue: any "SU(" in Lean source outside the declared explanatory sites fails
# loudly, forcing the U(N)-vs-SU(N) question to be answered consciously at the site.
# The two declared sites are the equivalence remarks kept ON PURPOSE (the centre
# acts trivially on projective space, so the literature's SU(N) reading is the same
# condition; FubiniStudy.lean header) and LF2/Setup.lean's abstract-G note.
DECLARED_SU_MENTIONS="CsdLean4/LF2/Setup.lean:1
CsdLean4/Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean:2"

echo "check-claims: verifying code against the canonical claims block…"

# (1) axiom set
# Fast path: a raw batched grep for `^axiom` is a strict SUPERSET of the
# comment-stripped result (stripping can only remove matches, never add one), so
# when it finds nothing the answer is provably empty and no per-file awk is needed.
# Only candidate files pay the strip_comments cost.
ax_candidates="$(srcfiles | tr '\n' '\0' \
  | xargs -0 grep -lE '^axiom[[:space:]]' 2>/dev/null || true)"
if [ -z "$ax_candidates" ]; then
  found_ax=""
else
  found_ax="$(printf '%s\n' "$ax_candidates" | while read -r f; do
      [ -n "$f" ] || continue
      strip_comments "$f" | grep -oE '^axiom[[:space:]]+[A-Za-z_][A-Za-z0-9_'\'']*' \
        | awk '{print $2}'
    done | sort -u)"
fi
decl_ax="$(printf '%s\n' "$DECLARED_AXIOMS" | grep -v '^[[:space:]]*$' | sort -u)"
if [ "$found_ax" = "$decl_ax" ]; then
  if [ -z "$found_ax" ]; then
    say_ok "imported axioms: none (zero-axiom posture — busch_effect_gleason discharged)"
  else
    say_ok "imported axioms == { $(echo "$found_ax" | tr '\n' ' ')}"
  fi
else
  say_fail "axiom set mismatch. declared: [$(echo "$decl_ax" | tr '\n' ' ')]  found: [$(echo "$found_ax" | tr '\n' ' ')]"
fi

# (2) := True placeholder inventory
found_ph="$(srcfiles | tr '\n' '\0' \
  | xargs -0 grep -nE '[A-Za-z_][A-Za-z0-9_]*[[:space:]]*:=[[:space:]]*True([[:space:]]|$)' 2>/dev/null \
  | sed -E 's|^([^:]+):[0-9]+:[[:space:]]*([A-Za-z_][A-Za-z0-9_]*)[[:space:]]*:=.*|\1:\2|' \
  | sort -u)"
decl_ph="$(printf '%s\n' "$DECLARED_PLACEHOLDERS" | grep -v '^[[:space:]]*$' | sort -u)"
if [ "$found_ph" = "$decl_ph" ]; then
  if [ -z "$found_ph" ]; then
    say_ok ":= True placeholders: none remain (all de-vacuumed)"
  else
    say_ok ":= True placeholders == declared inventory ($(printf '%s\n' "$decl_ph" | grep -c .) sites)"
  fi
else
  say_fail "placeholder set mismatch (new/removed := True — fix code or update the CLAIMS block)."
  echo "        declared:"; printf '%s\n' "$decl_ph"   | sed 's/^/          /'
  echo "        found:";    printf '%s\n' "$found_ph"  | sed 's/^/          /'
fi

# (3) FiniteQMClosure field count
FQC="$SRC/SigmaLayer/FiniteQMClosure.lean"
n_fields="$(awk '/^structure FiniteQMClosure/{s=1;next} /^theorem unifiedFiniteQMClosure/{s=0} s' "$FQC" \
            | grep -cE '^  [a-z_]+ :')"
if [ "$n_fields" = "$FINITEQMCLOSURE_FIELDS" ]; then
  say_ok "FiniteQMClosure has $FINITEQMCLOSURE_FIELDS fields"
else
  say_fail "FiniteQMClosure field count: declared $FINITEQMCLOSURE_FIELDS, found $n_fields"
fi

# (4) backing theorems exist
while read -r thm; do
  [ -z "$thm" ] && continue
  if srcfiles | xargs grep -lE "^(theorem|lemma|def|noncomputable def)[[:space:]]+([A-Za-z0-9_'.]+\.)?$thm([[:space:](:{]|\$)" >/dev/null 2>&1; then
    :
  else
    say_fail "backing theorem '$thm' not found as a declaration (CONNECTED claim orphaned?)"
  fi
done <<< "$DECLARED_BACKING_THEOREMS"
[ "$fail" -eq 0 ] && say_ok "all $(printf '%s\n' "$DECLARED_BACKING_THEOREMS" | grep -c .) backing theorems exist" || true

# (5) forbidden phrases in forward-claim docs
for doc in "${FORWARD_DOCS[@]}"; do
  [ -f "$doc" ] || { say_fail "forward-claim doc missing: $doc"; continue; }
  for phrase in "${FORBIDDEN_PHRASES[@]}"; do
    if grep -Fq "$phrase" "$doc"; then
      say_fail "forbidden phrase in $doc: \"$phrase\""
    fi
  done
done
[ "$fail" -eq 0 ] && say_ok "no forbidden A5-overclaim phrases in forward-claim docs" || true

# (5b) A5-mislabel aliases in the swept forward-claim docs
alias_fail=0
for doc in "${ALIAS_DOCS[@]}"; do
  [ -f "$doc" ] || { say_fail "alias-scan doc missing: $doc"; alias_fail=1; continue; }
  for alias in "${FORBIDDEN_ALIASES[@]}"; do
    if grep -Fq "$alias" "$doc"; then
      say_fail "A5-mislabel alias in $doc: \"$alias\" (use SO-1 for the sector-origin gap; A5 = projectability)"
      alias_fail=1
    fi
  done
done
[ "$alias_fail" -eq 0 ] && say_ok "no A5-mislabel aliases in the swept forward-claim docs (A5≠SO-1 kept distinct)" || true

# (6) epistemic-status scan: strong claim word + weak evidence on the same line
epi_fail=0
for doc in "${EPISTEMIC_DOCS[@]}"; do
  [ -f "$doc" ] || { say_fail "epistemic-scan doc missing: $doc"; epi_fail=1; continue; }

  # (6a) co-occurrence: a settled-claim word beside evidence that is not a proof.
  while IFS= read -r hit; do
    [ -z "$hit" ] && continue
    ln="${hit%%:*}"
    say_fail "epistemic overclaim $doc:$ln — a settled-claim word cites non-proof evidence; qualify it or mark it a conjecture"
    epi_fail=1
  done < <(grep -nE "$EPISTEMIC_STRONG" "$doc" 2>/dev/null \
           | grep -E "$EPISTEMIC_WEAK" \
           | grep -vE "$EPISTEMIC_EXEMPT" \
           | cut -d: -f1 | sed 's/$/:/')

  # (6b) blocklist: phrases never acceptable unless the line retracts them.
  for phrase in "${EPISTEMIC_BLOCKLIST[@]}"; do
    while IFS= read -r ln; do
      [ -z "$ln" ] && continue
      say_fail "forbidden epistemic phrase in $doc:$ln — \"$phrase\" (retract it or state the actual evidence)"
      epi_fail=1
    done < <(grep -nF "$phrase" "$doc" 2>/dev/null \
             | grep -vE "$EPISTEMIC_EXEMPT" \
             | cut -d: -f1)
  done
done
[ "$epi_fail" -eq 0 ] && say_ok "no epistemic overclaims (settled-claim words all cite proofs, not numerics/conjecture)" || true

# (7) symplectic-vocabulary inventory + parity discipline
# NOTE: batched through xargs, one grep per BATCH not per file. The per-file
# `while read` idiom used by checks (1)-(2) costs ~500 process spawns each, which is
# cheap on Linux CI and expensive enough on Windows to push this script past a
# five-minute timeout once two more passes were added (measured 2026-08-04).
found_vocab="$(srcfiles | tr '\n' '\0' \
  | xargs -0 grep -hoE "^(noncomputable )?(def|abbrev|structure) [A-Za-z0-9_']*([Ll]iouville|[Ss]ymplectic|[Kk]ahler|Kähler|[Hh]amiltonian)[A-Za-z0-9_']*" 2>/dev/null \
  | awk '{print $NF}' | sort -u)"
decl_vocab="$(printf '%s\n' "$DECLARED_SYMPLECTIC_VOCAB" | grep -v '^[[:space:]]*$' | sort -u)"
if [ "$found_vocab" = "$decl_vocab" ]; then
  say_ok "symplectic-vocabulary names == declared inventory ($(printf '%s\n' "$decl_vocab" | grep -c .) names, each with a recorded EVEN-parity justification)"
else
  say_fail "symplectic-vocabulary drift. A declaration name asserting Liouville/symplectic/Kähler is a CLAIM: add it to DECLARED_SYMPLECTIC_VOCAB with its arena's dimension parity (must be EVEN), or rename it after its construction."
  echo "        declared:"; printf '%s\n' "$decl_vocab" | sed 's/^/          /'
  echo "        found:";    printf '%s\n' "$found_vocab" | sed 's/^/          /'
fi

# (7b) the same vocabulary at structure-FIELD level
found_vfields="$(srcfiles | tr '\n' '\0' \
  | xargs -0 grep -hoE '^[[:space:]]+[A-Za-z0-9_]*([Ll]iouville|[Ss]ymplectic|[Kk]ahler|Kähler)[A-Za-z0-9_]*[[:space:]]*:[^=]' 2>/dev/null \
  | sed -E 's/^[[:space:]]+//; s/[[:space:]]*:.*//' | sort -u)"
decl_vfields="$(printf '%s\n' "$DECLARED_VOCAB_FIELDS" | grep -v '^[[:space:]]*$' | sort -u)"
if [ "$found_vfields" = "$decl_vfields" ]; then
  say_ok "symplectic-vocabulary FIELDS == declared inventory ($(printf '%s\n' "$decl_vfields" | grep -c .) fields)"
else
  say_fail "symplectic-vocabulary field drift. A structure field asserting Liouville/symplectic/Kähler is a claim too: add it to DECLARED_VOCAB_FIELDS with its justification, make it a Prop obligation, or rename it."
  echo "        declared:"; printf '%s\n' "$decl_vfields" | sed 's/^/          /'
  echo "        found:";    printf '%s\n' "$found_vfields" | sed 's/^/          /'
fi

# (7c) theorem/lemma names carrying the vocabulary
found_vthms="$(srcfiles | tr '\n' '\0' \
  | xargs -0 grep -hoE "^(theorem|lemma) [A-Za-z0-9_']*([Ll]iouville|[Ss]ymplectic|[Kk]ahler|Kähler|[Hh]amiltonian)[A-Za-z0-9_']*" 2>/dev/null \
  | awk '{print $NF}' | sort -u)"
decl_vthms="$(printf '%s\n' "$DECLARED_VOCAB_THEOREMS" | grep -v '^[[:space:]]*$' | sort -u)"
if [ "$found_vthms" = "$decl_vthms" ]; then
  say_ok "vocabulary-bearing THEOREM names == declared inventory ($(printf '%s\n' "$decl_vthms" | grep -c .) names; the one known misnomer is declared)"
else
  say_fail "vocabulary theorem drift. A theorem name asserting Liouville/symplectic/Kähler/Hamiltonian is a claim about what was PROVED: add it to DECLARED_VOCAB_THEOREMS with a justification, or rename it to what the statement establishes."
  echo "        declared:"; printf '%s\n' "$decl_vthms" | sed 's/^/          /'
  echo "        found:";    printf '%s\n' "$found_vthms" | sed 's/^/          /'
fi

# (7d) abstract-Sigma instantiation inventory + parity discipline
# A declaration whose RESULT type is KahlerOnticSetup is an instantiation site: it fixes
# the abstract Sigma and thereby OWES the parity claim the abstract structure cannot make.
# Signature scan: from a def/abbrev line to the first `:=`/`where` (or the decl line
# itself for one-liners), with parenthesised binder groups stripped so consumer arguments
# `(d : KahlerOnticSetup N)` do not count.
found_inst="$(srcfiles | tr '\n' '\0' | xargs -0 awk '
  function flush() {
    if (!inhdr) return
    s = buf
    while (match(s, /\([^()]*\)/)) { s = substr(s,1,RSTART-1) substr(s,RSTART+RLENGTH) }
    if (s ~ /:[^:]*KahlerOnticSetup/) print decl
    inhdr = 0
  }
  /^(noncomputable )?(def|abbrev) / {
    flush()
    decl = $0
    sub(/^(noncomputable )?(def|abbrev) /, "", decl); sub(/[^A-Za-z0-9_'"'"'].*$/, "", decl)
    buf = $0; inhdr = 1
    if ($0 ~ /:=| where/) flush()
    next
  }
  inhdr {
    buf = buf " " $0
    if ($0 ~ /:=|^ *where|[^A-Za-z]where$/) flush()
  }
  END { flush() }
' 2>/dev/null | sort -u)"
decl_inst="$(printf '%s\n' "$DECLARED_KAHLER_INSTANTIATIONS" | grep -v '^[[:space:]]*$' | sort -u)"
if [ "$found_inst" = "$decl_inst" ]; then
  say_ok "KahlerOnticSetup instantiations == declared inventory ($(printf '%s\n' "$decl_inst" | grep -c .) sites, each with a verified EVEN-parity Sigma)"
else
  say_fail "abstract-Sigma instantiation drift. A new KahlerOnticSetup instance fixes a concrete Sigma and OWES a parity justification: add it to DECLARED_KAHLER_INSTANTIATIONS with its Sigma's real dimension (must be EVEN)."
  echo "        declared:"; printf '%s\n' "$decl_inst" | sed 's/^/          /'
  echo "        found:";    printf '%s\n' "$found_inst" | sed 's/^/          /'
fi

# (7e) group-naming inventory: SU( mentions must be the declared explanatory sites
found_su="$(srcfiles | tr '\n' '\0' \
  | xargs -0 grep -cE 'SU\(' 2>/dev/null \
  | grep -v ':0$' | sort)"
decl_su="$(printf '%s\n' "$DECLARED_SU_MENTIONS" | grep -v '^[[:space:]]*$' | sort)"
if [ "$found_su" = "$decl_su" ]; then
  say_ok "group naming: SU( mentions == declared explanatory sites ($(printf '%s\n' "$decl_su" | grep -c .) files) — everything else says U(N), matching the quantifier"
else
  say_fail "group-naming drift. The corpus quantifies over Matrix.unitaryGroup = U(N); a new 'SU(' mention must either become U(N) or be added to DECLARED_SU_MENTIONS with its equivalence justification (necessity-audit item 13 is the case history)."
  echo "        declared:"; printf '%s\n' "$decl_su" | sed 's/^/          /'
  echo "        found:";    printf '%s\n' "$found_su" | sed 's/^/          /'
fi

# (8) open-scope inventory: boundary claims are diffable, so they cannot go stale silently
found_scope="$(srcfiles | tr '\n' '\0' \
  | xargs -0 grep -cE "$OPEN_SCOPE_PHRASES" 2>/dev/null \
  | grep -v ':0$' | sort)"
decl_scope="$(printf '%s\n' "$DECLARED_OPEN_SCOPE" | grep -v '^[[:space:]]*$' | sort)"
if [ "$found_scope" = "$decl_scope" ]; then
  say_ok "open-scope claims == declared inventory ($(printf '%s\n' "$decl_scope" | grep -c .) files) — re-read these when a BACKLOG row is discharged"
else
  say_fail "open-scope inventory drift. An honest-scope claim was added or removed: update DECLARED_OPEN_SCOPE, and CHECK whether a claim that stayed put has gone stale (that is the case this guard cannot see)."
  echo "        declared:"; printf '%s\n' "$decl_scope" | sed 's/^/          /'
  echo "        found:";    printf '%s\n' "$found_scope" | sed 's/^/          /'
fi

# (8b) scope-expiry ledger: a discharged BACKLOG row may not leave a boundary standing
expiry_fail=0
covered=""
while IFS='|' read -r sf stag; do
  [ -z "$sf" ] && continue
  covered="$covered $sf"
  if [ "$stag" != "none" ]; then
    if grep -qE "\| ~~${stag}~~" specs/BACKLOG.md 2>/dev/null; then
      say_fail "scope expiry: BACKLOG row ${stag} is struck DONE but ${sf} still carries the open boundary waiting on it — re-read the site, supersede the stale note at source, then re-tag it 'none' in DECLARED_SCOPE_WAITS"
      expiry_fail=1
    fi
  fi
done <<< "$DECLARED_SCOPE_WAITS"
# every open-scope file must carry a wait tag, so a new boundary cannot skip the ledger
while IFS=: read -r sf _; do
  [ -z "$sf" ] && continue
  case " $covered " in
    *" $sf "*) : ;;
    *) say_fail "scope expiry: $sf appears in DECLARED_OPEN_SCOPE but has no row in DECLARED_SCOPE_WAITS — classify its boundary (a BACKLOG row tag, or 'none' with a ledger note)"
       expiry_fail=1 ;;
  esac
done <<< "$DECLARED_OPEN_SCOPE"
[ "$expiry_fail" -eq 0 ] && say_ok "scope-expiry ledger: no boundary outlives its BACKLOG row (every open-scope file classified)" || true

# ------------------------------------------------------- LANDING-SURFACE GUARDS --
# The README is the surface a citing reader meets first, so it carries its own
# rules: the axiom claim must never appear unqualified, the register excludes em
# dashes, dated correction narratives belong in specs/archive, and the file must
# stay short enough to read in one screen.

# (9) "zero axioms" must be qualified in the same paragraph.
if [ -f README.md ]; then
  zero_bad=0
  while IFS= read -r para; do
    case "$para" in
      *"zero axiom"*)
        case "$para" in
          *logical*|*foundational*|*"physical posit"*) : ;;
          *) zero_bad=1 ;;
        esac ;;
    esac
  done <<< "$(awk 'BEGIN{RS="";ORS="\n"} {gsub(/\n/," "); print}' README.md)"
  if [ "$zero_bad" -eq 0 ]; then
    say_ok "README: no unqualified \"zero axioms\" claim"
  else
    say_fail "README says \"zero axioms\" without qualifying it (logical vs physical) in the same paragraph"
  fi

  # (10) register: no em dashes in the two landing documents.
  em_readme=$(grep -c '—' README.md || true)
  em_tour=0
  [ -f docs/TOUR.md ] && em_tour=$(grep -c '—' docs/TOUR.md || true)
  if [ "$em_readme" -eq 0 ] && [ "$em_tour" -eq 0 ]; then
    say_ok "landing surface: no em dashes in README or docs/TOUR.md"
  else
    say_fail "em dash found in README ($em_readme) or docs/TOUR.md ($em_tour); use commas, colons, parentheses, or separate sentences"
  fi

  # (11) no dated correction narrative in README.
  dated=$(grep -cE '(^|[^0-9])(19|20)[0-9]{2}-[0-9]{2}-[0-9]{2}([^0-9]|$)' README.md || true)
  if [ "$dated" -eq 0 ]; then
    say_ok "README: no dated correction lines (they belong in specs/archive)"
  else
    say_fail "README carries $dated dated line(s); move correction narrative to docs/TOUR.md or specs/archive/"
  fi

  # (12) size guard.
  readme_bytes=$(wc -c < README.md | tr -d ' ')
  if [ "$readme_bytes" -le 6144 ]; then
    say_ok "README size ${readme_bytes}B (limit 6144B)"
  else
    say_fail "README is ${readme_bytes}B, over the 6144B landing-surface limit"
  fi
fi

# (13) CITATION.cff C1 anchor: the "cite tagged release" line must name the newest C1
# tag. The line went stale three times (R2, R3, and the v1.4.x pair — found 2026-08-17);
# its own "update it in the same commit" instruction does not self-execute, so the guard
# executes it. Skips gracefully when tags are absent (shallow CI checkouts fetch none —
# the check then binds locally and on any full clone).
newest_c1=$(git tag -l 'v*-c1-*' 2>/dev/null | sort -V | tail -1)
if [ -n "$newest_c1" ] && [ -f CITATION.cff ]; then
  if grep -q "cite tagged release \`$newest_c1\`" CITATION.cff; then
    say_ok "CITATION.cff C1 anchor names the newest C1 tag ($newest_c1)"
  else
    say_fail "CITATION.cff C1 anchor is stale: newest C1 tag is $newest_c1 but the 'cite tagged release' line does not name it"
  fi
fi

echo
if [ "$fail" -eq 0 ]; then echo "check-claims: PASS"; exit 0
else echo "check-claims: FAIL — code and the canonical claims block disagree (fix code or update the CLAIMS block)"; exit 1; fi

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
#   (8) OPEN-SCOPE INVENTORY: per-file counts of the honest-scope phrases ("remains
#       open", "recorded extension", "not claimed here"). Added 2026-08-04, same
#       review: MeasurementCapstone.lean still said the conditioned mixed update
#       "remains open" hours after MixedLuders.lean closed it.
#
#       KNOWN LIMIT — this fires when such a claim is ADDED or REMOVED, not when the
#       underlying fact changes underneath a claim that stays put. It cannot detect
#       the stale note by itself; what it does is make the inventory visible and
#       diffable, so discharging a BACKLOG row has a mechanical companion step:
#       re-read the sites this check prints. Converting "remember to sweep" into
#       "read this list" is the whole of the improvement — do not oversell it.
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
hamiltonianField
hamiltonian
HasHamiltonianRealisation
IsForcedKahlerVolume
IsFubiniStudyKahler
kahlerConstraintDynamics
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
#     hamiltonianField — (ChartBracket.lean, A3) the vector field `(∂_y H, −∂_x H)` in a
#       DARBOUX CHART, written out explicitly. The name is earned because in canonical
#       coordinates the field IS that formula: no `ω⁻¹` is invoked, nothing is asserted.
#       Caught by this very check when it was added, 2026-08-04.        EARNED (chart-level).
#     HasHamiltonianRealisation — a Prop DEMANDING an explicit Hermitian `H` with
#       `U t = exp(-itH)`; `productProjectedFlow_hasHamiltonianRealisation` exhibits one.
#       This is CONVENTIONS 8.3a option (1) done right.                            EARNED.
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

# ------------------------------------------------------- OPEN-SCOPE INVENTORY --
# Per-file counts of honest-scope phrases. These are GOOD — they are how a module
# states its boundary — so this is not a budget to drive to zero; it is a diffable
# ledger so that a boundary claim cannot go stale unnoticed when the work lands.
DECLARED_OPEN_SCOPE="CsdLean4/Empirical/QM/QEC/ErrorDiscretization.lean:1
CsdLean4/Empirical/QM/QEC/SyndromeCollapse.lean:1
CsdLean4/LF4/PhaseLift.lean:1
CsdLean4/LF4/TypicalityForcing.lean:1
CsdLean4/SigmaLayer/ApproxProjectability.lean:1
CsdLean4/SigmaLayer/FiniteQMClosure.lean:1
CsdLean4/SigmaLayer/MeasurementCapstone.lean:2
CsdLean4/SigmaLayer/MixedLuders.lean:1
CsdLean4/SigmaLayer/MixedSwap.lean:1
CsdLean4/SigmaLayer/PointerBorn.lean:1
CsdLean4/SigmaLayer/PointerGeneration.lean:2
CsdLean4/SigmaLayer/PovmDynamics.lean:2
CsdLean4/SigmaLayer/PovmSectorBorn.lean:1
CsdLean4/SigmaLayer/RecordLayerClosure.lean:1
CsdLean4/Tests/AxiomAudit.lean:4"

# (7b) STRUCTURE FIELDS carrying the same vocabulary. Found 2026-08-04 immediately
# after (7a) shipped: `liouvilleMeasure`, `IsKahlerSector` and friends are structure
# FIELDS, and (7a)'s regex is anchored to `def|abbrev|structure`, so it never saw
# them. A name is a claim wherever it appears, not only at top level.
# Matches declarations (`name : Type`) and deliberately not instantiations
# (`name := value`), which are uses of an already-declared field.
DECLARED_VOCAB_FIELDS="IsKahlerSector
IsLiouvilleKahlerVolume
kahler_condition
liouville
liouvilleMeasure
liouville_eq_kahler_volume"
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
DECLARED_VOCAB_THEOREMS="arenaLiouville_cylinder
arenaLiouville_sys_marginal
fieldHamiltonian_mulVec_single
fubiniStudy_pointwise_kahler_compatibility
fubiniStudyMeasure_isForcedKahlerVolume
hamiltonian_eq_diagonal
hamiltonian_groundEnergy
hamiltonian_isHermitian
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

echo
if [ "$fail" -eq 0 ]; then echo "check-claims: PASS"; exit 0
else echo "check-claims: FAIL — code and the canonical claims block disagree (fix code or update the CLAIMS block)"; exit 1; fi

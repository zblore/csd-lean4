#!/usr/bin/env bash
# extract-eponyms.sh
#
# Builds the GLOSSARY KEY SET from the corpus, rather than from taste.
#
# Motivating case (2026-08-13): the corpus explains itself to specialists and to
# nobody else. Eight of nine reader personas identified in the CSD query research
# have a repo path built for them and no page anywhere that says what the thing
# IS. The terms those readers search for are overwhelmingly EPONYMS -- Fubini-Study,
# Duistermaat-Heckman, Busch, Gleason, Lueders, Naimark -- because that is how the
# mathematics is named, and it is how the declarations in this repo are named too.
#
# So the key set is not a matter of judgement. It is derivable: the eponyms that
# appear in declaration names and module docs ARE the terms that need explaining.
#
# WHAT IT REPORTS
#   (A) known eponyms   -- from the curated list below, with the number of
#                          DECLARATIONS whose name contains them and the number of
#                          files touched. A declaration-name count is used rather
#                          than a raw line count because line counts are dominated
#                          by substring noise ("Ou" matches 512 lines and names
#                          exactly one concept, Hong-Ou-Mandel).
#   (B) candidates      -- capitalised CamelCase segments appearing in declaration
#                          or module names that are NOT in the curated list and are
#                          not common Lean/Mathlib vocabulary. These are how a NEW
#                          eponym entering the corpus surfaces as a glossary gap.
#
# WHAT IT DELIBERATELY DOES NOT DO
#   It does not decide which eponyms deserve an entry, and it does not collapse
#   pairs. Fubini + Study are one measure; Duistermaat + Heckman are one theorem;
#   Kochen + Specker, Stern + Gerlach, Mach + Zehnder, Leggett + Garg, Elitzur +
#   Vaidman and Hong + Ou + Mandel are each one concept. Collapsing them is an
#   editorial act and belongs in docs/glossary.yaml, not here. The report is raw
#   material for that file.
#
# Usage:  bash scripts/extract-eponyms.sh            (report)
#         bash scripts/extract-eponyms.sh --keys     (bare key list, one per line)
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
SRC="CsdLean4"
KEYS_ONLY=0
[ "${1:-}" = "--keys" ] && KEYS_ONLY=1

# The curated list. Surnames cannot be detected reliably by pattern, so they are
# named. Section (B) is what keeps this list honest as the corpus grows.
EPONYMS="Fubini Study Busch Gleason Wigner Bargmann Naimark Duistermaat Heckman
Dirichlet Liouville Kahler Kähler Haar Weil Levy Lévy Luders Lueders Bell CGLMP
GHZ Mermin Peres Kochen Specker Neumann Born Schrodinger Schrödinger Riemann
Hilbert Ashtekar Schilling Kibble Wootters Zurek Gibbs Landauer Ramsey Grover
Shor Deutsch Jozsa Elitzur Vaidman Zehnder Mach Malus Leggett Garg Hong Mandel
Stern Gerlach Tsirelson Gisin Sorkin Prokhorov Cauchy Schwarz Lipschitz Borel
Lebesgue Radon Nikodym Birkhoff Stone Kronecker Loewner Löwner Grothendieck
Nagasawa Madelung Bohm Koopman Nelson Fisher Rao Bloch Pauli Everett Planck
Euclidean Hermitian Hermite Euclid Poisson Jacobi Noether Casimir Frobenius Weyl"

FILES="$(git ls-files "$SRC/**/*.lean")"
[ -z "$FILES" ] && { echo "  FAIL  no source files found"; exit 1; }

# Every declaration name in the corpus, plus every module path. Declaration names
# are the load-bearing surface: a name is a claim (CONVENTIONS.md 8.3a).
DECLS="$(printf '%s\n' $FILES | xargs grep -hE '^(public |private |protected |noncomputable |scoped |partial |unsafe |nonrec )*(def|abbrev|structure|class|inductive|instance|theorem|lemma) ' 2>/dev/null \
  | sed -E 's/^(public |private |protected |noncomputable |scoped |partial |unsafe |nonrec )*(def|abbrev|structure|class|inductive|instance|theorem|lemma) +//' \
  | sed -E 's/[^A-Za-z0-9_'"'"'.].*$//')"
MODULES="$(printf '%s\n' $FILES | sed -E 's#^CsdLean4/##; s#\.lean$##')"
NAMESPACE="$(printf '%s\n%s\n' "$DECLS" "$MODULES")"

if [ "$KEYS_ONLY" -eq 1 ]; then
  for e in $EPONYMS; do
    n=$(printf '%s\n' "$NAMESPACE" | grep -ci "$e" || true)
    [ "$n" -gt 0 ] && echo "$e"
  done
  exit 0
fi

echo "extract-eponyms: building the glossary key set from declaration and module names…"
echo
printf '  (A) known eponyms — %-28s %8s %8s\n' "eponym" "decls" "files"
echo "      ----------------------------------------------------------------"

# NB: the table is built into a variable, not piped straight to sort. Piping puts
# the loop in a subshell, so a counter incremented inside it is lost -- which is how
# an earlier revision reported "0 known eponyms present" above a table listing 48.
TABLE="$(for e in $EPONYMS; do
  n=$(printf '%s
' "$NAMESPACE" | grep -ci "$e" || true)
  [ "$n" -eq 0 ] && continue
  f=$(printf '%s
' $FILES | xargs grep -lie "$e" 2>/dev/null | wc -l | tr -d ' ')
  printf '      %-32s %8s %8s
' "$e" "$n" "$f"
done | sort -k2 -rn)"
printf '%s
' "$TABLE"
found="$(printf '%s
' "$TABLE" | grep -c . || true)"

echo
echo "      $found known eponyms present. Section (B) below is what keeps that list honest."
echo
echo "  (B) candidate eponyms — capitalised segments not in the curated list:"
echo "      (new mathematics entering the corpus shows up here first)"
echo

# Split CamelCase into segments, drop Lean/Mathlib vocabulary and the known list.
KNOWN_RE="$(printf '%s\n' $EPONYMS | paste -sd'|' -)"
printf '%s\n' "$NAMESPACE" \
  | tr './_' '\n\n\n' \
  | sed -E 's/([a-z0-9])([A-Z])/\1\n\2/g' \
  | grep -E '^[A-Z][a-z]{3,}$' \
  | grep -viE "^($KNOWN_RE)$" \
  | grep -viE '^(Basic|Setup|Main|Theorem|Lemma|Measure|Space|Type|Prop|Real|Complex|Matrix|Finset|Order|Group|Ring|Field|Module|Linear|Algebra|Analysis|Topology|Geometry|Manifold|Function|Filter|Sigma|Omega|Delta|Gamma|Alpha|Beta|Data|List|Tactic|Simp|Norm|Inner|Product|Sum|Prod|Unique|Exists|Forall|Empty|Univ|Union|Inter|Compl|Image|Range|Domain|Support|Bound|Limit|Cont|Deriv|Integral|Volume|Weight|Region|Sector|State|Vector|Scalar|Point|Line|Plane|Sphere|Ball|Open|Closed|Compact|Dense|Conv|Seq|Iter|Step|Flow|Time|Index|Chart|Fibre|Fiber|Base|Total|Part|Trace|Rank|Kernel|Image|Proj|Push|Pull|Map|Hom|Iso|Equiv|Embed|Quot|Sub|Super|Pre|Post|Aux|Util|Helper|Core|Layer|Tier|Phase|Stage|Audit|Check|Test|Spec|Todo|Note|Doc|Ref|Link|Path|File|Dir|Root|Node|Tree|Graph|Edge|Wrap|Bridge|Pillar|Anchor|Witness|Instance|Model|Trial|Outcome|Record|Basin|Pointer|Apparatus|Context|Prep|Read|Out|Cell|Cast|Succ|Zero|One|Two|Three|Four|Five|Mixed|Pure|Joint|Marginal|Cond|Update|Coll|Global|Local|Approx|Exact|Free|Full|Half|Bar|Box|Hat|Star|Dual|Adj|Self|Auto|Semi|Multi|Poly|Mono|Bi|Tri|Non|Anti|Inv|Rev|Fwd|Back|Next|Last|First|New|Old|Tmp|Temp|Var|Val|Fun|Arg|Res|Ret|Err|Fail|Pass|True|False|Some|None|Left|Right|Up|Down|Top|Bot|Min|Max|Abs|Sign|Pos|Neg|Even|Odd|Nat|Int|Rat|Bool|Char|String|Unit|Void|Empirical|Prob|Plus|Minus|Mathlib|Preserving|Quantum|Seam|Deisolation|Measurement|Evolve|Layout|Swap|Reduced|Info|Density|Basis|Ontic|Epistemic|Pushforward|Invariant|Projective|Projectivization|Effect|Package|Operational|Frequency|Convergence|Typicality|Constraint|Surface|Dynamics|Closure|Semantics|Discharge|Rigidity|Uniqueness|Correspondence|Composite|Adapters|Interface|Conditioning|Collapse|Degenerate|Isolation|Signature|Propagator|Reversible|Elliptic|Curve|Modular|Arith|Circuit|Gate|Algorithms|Metrology|Thermo|Contextuality|Multipart|Multipartite|Qubit|Qutrit|Qudit|Singlet|Entangled|Nonlocality|Correlation|Observable|Spectral|Carving|Simplex|Barycentric|Apex|Moment|Chain|Capstone|Forward|Sigma|Kappa)$' \
  | sort | uniq -c | sort -rn | head -25 | while read -r c t; do
      printf '      %-32s %8s\n' "$t" "$c"
    done

echo
echo "  Neither section is a decision. docs/glossary.yaml decides which of these"
echo "  get an entry, and collapses pairs into single concepts."

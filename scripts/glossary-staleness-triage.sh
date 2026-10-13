#!/usr/bin/env bash
# glossary-staleness-triage.sh -- thin wrapper. The triage is scripts/lib/glossary_staleness.py
#
# `check-glossary.sh` says WHICH entries are stale against a moved module. This says which of
# those moved in a way that can change what the entry says: a corpus-wide mechanical rename moves
# every module, so after a pin move the staleness list is dominated by entries whose prose cannot
# have gone stale. It bumps no dates -- the author's rule is re-read, then bump.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
exec python scripts/lib/glossary_staleness.py

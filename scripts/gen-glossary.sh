#!/usr/bin/env bash
# gen-glossary.sh -- thin wrapper. The generator is scripts/lib/gen_glossary.py
# Output lands in docs/_site/ and is NOT committed; Actions builds and deploys it.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
exec python scripts/lib/gen_glossary.py

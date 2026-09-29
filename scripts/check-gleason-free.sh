#!/usr/bin/env bash
# Check all declared modules, including SingletBell, against the Busch/projection/core
# reconstruction roots and exercise alias/allowed-route controls. Build both targets first.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
if ! lake env lean scripts/gleason-free.lean; then
  echo "check-gleason-free: FAILED"
  exit 1
fi

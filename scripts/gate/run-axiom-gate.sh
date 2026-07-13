#!/usr/bin/env bash
set -euo pipefail

# Resolve repo root as two levels up from this script's directory.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

cd "${REPO_ROOT}"

echo "Running axiom gate from: ${REPO_ROOT}"

output="$(lake env lean scripts/gate/AxiomGate.lean 2>&1)"
echo "${output}"

if echo "${output}" | grep -q "AXIOM-GATE-VERDICT PASS"; then
  exit 0
else
  echo ""
  echo "AXIOM-GATE FAILED: sorryAx, native_decide, or unauthorized axiom detected — see QUARANTINE lines above"
  exit 1
fi

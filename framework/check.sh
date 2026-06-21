#!/usr/bin/env bash
# check.sh -- the canonical Lux high-assurance gate.
#
# ONE gate, run against ANY crypto repo, enforcing the disclosure discipline in
# framework/ASSURANCE.tex. It encodes the failure modes found in the 2026-06
# Lux PQ-crypto audit so they can never ship again:
#
#   circular-proof    a security theorem discharged by an axiom that restates
#                     it, or a vacuous `:= True`/`sorry` Lean body.
#   proof-by-rename   a "CLOSED" security property enforced only by an
#                     identifier-name grep, not a functional test.
#   fail-open         a Verify/Validate/Check function that always accepts.
#   axiom-budget      sorry/admit/axiom counts drifting above the declared
#                     budget in .assurance/budget.txt.
#   claims-vs-reality PROOF-CLAIMS prose that contradicts the artifacts.
#
# Each crypto repo's own scripts/check-high-assurance.sh should invoke this
# (one way to do everything) and add its repo-specific gates (jasmin, ec
# compile, dudect) on top.
#
# Usage: check.sh <repo-root> [repo-root ...]   (default: well-known luxfi repos)
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CHECKS=(circular-proof proof-by-rename fail-open axiom-budget claims-vs-reality)

run_repo() {
  local repo="$1" overall=0
  echo "==> high-assurance gate: $repo"
  for c in "${CHECKS[@]}"; do
    echo "  -- $c"
    bash "$HERE/checks/$c.sh" "$repo"; local rc=$?
    [ "$rc" -ne 0 ] && overall=$rc
  done
  echo
  return $overall
}

repos=("$@")
if [ "${#repos[@]}" -eq 0 ]; then
  base="$(cd "$HERE/../.." && pwd)/luxfi"
  for r in pulsar corona magnetar p3q consensus; do [ -d "$base/$r" ] && repos+=("$base/$r"); done
fi

GLOBAL=0
for repo in "${repos[@]}"; do run_repo "$repo" || GLOBAL=$?; done
if [ "$GLOBAL" -ne 0 ]; then
  echo "HIGH-ASSURANCE GATE: FAIL"
  exit "$GLOBAL"
fi
echo "HIGH-ASSURANCE GATE: PASS"
exit 0

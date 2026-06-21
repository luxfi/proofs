#!/usr/bin/env bash
# axiom-budget.sh -- count unproven-assertion primitives in a proof tree and
# fail if they drift above the declared budget.
#
# The framework's honest-disclosure rule: every `sorry`, `admit`, `axiom`,
# `declare axiom`, and vacuous `:= True`/`trivial` is an UNPROVEN assertion.
# Their count is the proof's real surface of trust. It must be DECLARED (in
# `<repo>/.assurance/budget.txt`, one `KEY=MAX` per line) and may never silently
# grow. Magnetar shipped 69 such assertions while PROOF-CLAIMS read "proven".
#
# budget.txt keys: SORRY, ADMIT, AXIOM, VACUOUS (omitted key => max 0).
# No budget.txt => report-only the first time (prints the counts to seed one).
#
# Usage: axiom-budget.sh <repo-root>
set -uo pipefail
ROOT="${1:?usage: axiom-budget.sh <repo-root>}"
PD=""
for d in "$ROOT/proofs" "$ROOT/spec" "$ROOT"; do [ -d "$d" ] && PD="$d" && break; done
[ -z "$PD" ] && { echo "    [skip] no proof tree"; exit 0; }

count() { find "$PD" \( -name '*.ec' -o -name '*.lean' \) 2>/dev/null -exec grep -hoE "$1" {} + 2>/dev/null | wc -l | tr -d ' '; }
SORRY=$(count '\bsorry\b'); ADMIT=$(count '\badmit\b')
AXIOM=$(count '^[[:space:]]*(declare[[:space:]]+)?axiom[[:space:]]')
VACUOUS=$(find "$PD" -name '*.lean' -exec grep -hcE ':=[[:space:]]*(True|trivial)([[:space:]]|$)' {} + 2>/dev/null | awk '{s+=$1} END{print s+0}')

echo "    counts: SORRY=$SORRY ADMIT=$ADMIT AXIOM=$AXIOM VACUOUS=$VACUOUS"
BUD="$ROOT/.assurance/budget.txt"
if [ ! -f "$BUD" ]; then
  echo "    [warn] no $BUD -- declare a budget to enforce drift. Seed it with the counts above."
  exit 0
fi
get() { grep -E "^$1=" "$BUD" 2>/dev/null | tail -1 | cut -d= -f2 | tr -dc '0-9'; }
fail=0
for k in SORRY ADMIT AXIOM VACUOUS; do
  cur=$(eval echo \$$k); max=$(get "$k"); max=${max:-0}
  if [ "$cur" -gt "$max" ]; then
    echo "    [FAIL] $k=$cur exceeds declared budget $max -- new unproven assertions added without updating .assurance/budget.txt + PROOF-CLAIMS"
    fail=1
  fi
done
[ "$fail" -eq 0 ] && { echo "    [ok]   unproven-assertion counts within declared budget"; exit 0; }
exit 2

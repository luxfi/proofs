#!/usr/bin/env bash
# claims-vs-reality.sh -- cross-check PROOF-CLAIMS prose against the artifacts.
#
# Honest-disclosure rule: a claim's WORD must match the artifact's STATE.
#   - "machine-checked / proven / discharged" naming a .lean/.ec file that
#     actually contains sorry/admit/`:= True` is a false claim.
#   - "byte-equal / interchangeable ... proven/verified" must be backed by
#     interop against an INDEPENDENT verifier (>= 2 implementations), not the
#     same library the signer used.
#
# Usage: claims-vs-reality.sh <repo-root>
set -euo pipefail
ROOT="${1:?usage: claims-vs-reality.sh <repo-root>}"
PC=""
for c in "$ROOT/PROOF-CLAIMS.md" "$ROOT/audit"/*/README.md; do [ -f "$c" ] && PC="$c" && break; done
[ -z "$PC" ] && { echo "    [skip] no PROOF-CLAIMS.md"; exit 0; }
findings=0

# 1. Strong claim on the same line as a proof file that is not actually clean.
while IFS= read -r line; do
  ref="$(echo "$line" | grep -oE '[A-Za-z0-9_/.-]+\.(lean|ec)' | head -1)"
  [ -z "$ref" ] && continue
  f=""
  for cand in "$ROOT/$ref" "$(find "$ROOT" -name "$(basename "$ref")" 2>/dev/null | head -1)"; do
    [ -f "$cand" ] && f="$cand" && break
  done
  [ -z "$f" ] && continue
  if grep -qE '\b(sorry|admit)\b|:=[[:space:]]*(True|trivial)([[:space:]]|$)' "$f" 2>/dev/null; then
    echo "$PC: claims '$(echo "$line" | sed 's/^[[:space:]]*//;s/|.*//' | cut -c1-70)' but $ref contains sorry/admit/vacuous body"
    findings=$((findings + 1))
  fi
done < <(grep -inE '(machine.?checked|fully proven|formally proven|discharged|proven sound|qed).*\.(lean|ec)' "$PC" 2>/dev/null || true)

# 2. byte-equality claimed proven but no independent (>=2) verifier in tests.
if grep -qiE '(byte.?equal|interchang).*(proven|verified|demonstrated|holds)' "$PC" 2>/dev/null; then
  libs=$(grep -rhoE 'circl|pq-crystals|dilithium|sphincsplus|slhdsa|boringssl|aws-lc|openssl' \
          "$ROOT" --include='*_test.go' 2>/dev/null | tr 'A-Z' 'a-z' | sort -u | grep -cE 'circl|pq-crystals|dilithium|sphincs|slhdsa|boringssl|aws-lc|openssl' || true)
  if [ "${libs:-0}" -lt 2 ]; then
    echo "$PC: claims byte-equality/interchangeability proven, but tests reference < 2 independent FIPS verifiers (found $libs) -- demonstrate against an INDEPENDENT verifier, not the signer's own library"
    findings=$((findings + 1))
  fi
fi

if [ "$findings" -gt 0 ]; then
  echo "    [FAIL] $findings claim(s) do not match the artifacts -- the disclosure word must match the proof state."
  exit 2
fi
echo "    [ok]   PROOF-CLAIMS prose matches the proof artifacts"
exit 0

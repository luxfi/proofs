#!/usr/bin/env bash
# proof-by-rename.sh -- flag a RUNTIME-BEHAVIOUR security property (constant
# time, no-transient-secret, no-secret-dependent-branch) "enforced" by an
# identifier-name grep instead of a functional/timing test, and a single
# blocker entry that is marked CLOSED while its own prose admits the secret is
# still reconstructed/revealed.
#
# Found in the 2026-06 audit: Magnetar declared MAGNETAR-STRICT-ATOM-V11
# "CLOSED" while the combiner still reconstructed the full FIPS 205 seed; the
# enforcing test checked that identifier NAMES did not appear in branch/index
# positions. Rename a secret to `tmp` and it passes.
#
# A grep is a fine way to assert a SYNTACTIC fact (a retired axiom is absent,
# code compiles, a secret is not handed to a logger). It is NOT a way to
# certify a TIMING / no-runtime-secret property -- those need a
# dudect/valgrind/ctgrind harness or a byte-level test. Only that mismatch is
# flagged; legitimate grep-gates (ec-compile, jasmin, regression guards) pass.
#
# Usage: proof-by-rename.sh <repo-root>
set -uo pipefail
ROOT="${1:?usage: proof-by-rename.sh <repo-root>}"
findings=0
RUNTIME='constant.?time|no.?transient|no.?secret.?dependent|secret.?independent|timing.?safe|side.?channel'

# (1) constant-time / no-runtime-secret property "enforced" by name grep only.
while IFS= read -r sh; do
  [ -f "$sh" ] || continue
  grep -qiE "$RUNTIME" "$sh" || continue
  greps=$(grep -cE '\b(grep|rg|ast-grep)\b' "$sh" || true)
  harness=$(grep -cE 'dudect|valgrind|ctgrind|cachegrind|go test|cargo test|\.Verify\(|byte.?equal|memcmp|ConstantTime|rdtsc' "$sh" || true)
  if [ "$greps" -gt 0 ] && [ "$harness" -eq 0 ]; then
    echo "$sh:1: '$(basename "$sh")' claims a constant-time/no-runtime-secret property but enforces it by identifier grep only -- a name grep cannot certify a runtime property (proof-by-rename)"
    findings=$((findings + 1))
  fi
done < <(find "$ROOT" -path '*scripts*' -name '*.sh' 2>/dev/null)

# (2) a SINGLE blocker section marked CLOSED whose own prose admits the secret
#     is still reconstructed/revealed (section-aware, not file-wide).
for bl in "$ROOT/BLOCKERS.md" "$ROOT/audit"/*/KNOWN_BAD*.md; do
  [ -f "$bl" ] || continue
  hits="$(awk -v F="$bl" '
    function flush(  ) {
      if (sec != "" && closed && admits)
        printf("%s:%d: blocker section \"%s\" is marked CLOSED/RESOLVED but its prose admits the secret is still reconstructed/revealed -- re-open or re-label\n", F, secline, sec)
      closed=0; admits=0
    }
    /^#{1,4}[[:space:]]/ { flush(); sec=$0; sub(/^#+[[:space:]]*/,"",sec); secline=NR; next }
    /(Status|State)[^A-Za-z]*(^|[^A-Za-z])(CLOSED|RESOLVED)([^A-Za-z]|$)/ { closed=1 }
    /\*\*[[:space:]]*(CLOSED|RESOLVED)[[:space:]]*\*\*/ { closed=1 }
    /^[[:space:]]*[-*][[:space:]]*\[[xX]\].*(CLOSED|RESOLVED)/ { closed=1 }
    /\|[[:space:]]*(CLOSED|RESOLVED)[[:space:]]*\|/ { closed=1 }
    /do exist transiently|still reconstruct|reconstructs the (full|whole)|bytes of the .* master|reveals the master/ { admits=1 }
    END { flush() }
  ' "$bl")"
  if [ -n "$hits" ]; then echo "$hits"; findings=$((findings + $(echo "$hits" | grep -c ':'))); fi
done

if [ "$findings" -gt 0 ]; then
  echo "    [FAIL] $findings proof-by-rename / contradictory-disclosure finding(s)."
  exit 2
fi
echo "    [ok]   no constant-time/no-secret property enforced solely by grep; no CLOSED-but-reconstructs blocker"
exit 0

#!/usr/bin/env bash
# fail-open.sh -- flag verifier functions that ALWAYS accept (fail open).
#
# Two shapes from the 2026-06 audit:
#   1. A registered-verifier default that returns nil instead of an error, so a
#      missing real verifier reads as "valid".
#   2. A verifier stub whose whole body is `return nil` -- it certifies nothing.
#
# Precise on purpose: it flags a Verify/Validate/Authenticate function returning
# `error` whose body, stripped of comments and braces, is EXACTLY `return nil`
# (a no-op that always accepts), OR a Verify method on a type whose name says it
# is a default/disabled/unregistered/noop verifier and that returns nil. A real
# verifier with logic (loops, channels, delegation) is NOT flagged; HealthCheck
# and the like are excluded. The subtler "conditional return nil" regression is
# left to the proof / claims gates and human review.
#
# Usage: fail-open.sh <repo-root>
set -uo pipefail
ROOT="${1:?usage: fail-open.sh <repo-root>}"

findings=$(find "$ROOT" -name '*.go' ! -name '*_test.go' \
    ! -path '*/chaintest/*' ! -path '*/blocktest/*' ! -path '*/testutil/*' \
    ! -path '*/testdata/*' ! -path '*/mock/*' ! -path '*/mocks/*' 2>/dev/null | while IFS= read -r gf; do
  awk -v F="$gf" '
    function emit(why) { printf("%s:%d: %s `%s` %s (fail-open)\n", F, start, kind, name, why) }
    # Candidate: func/method named Verify/Validate/Authenticate returning error.
    # Exclude *Health* and pure liveness checks.
    /^func[[:space:]].*(Verify|Validate|Authenticate)[A-Za-z0-9_]*\(.*\)[[:space:]]+error[[:space:]]*\{/ {
      if ($0 ~ /Health/) { next }
      inf=1; depth=1; start=NR; stmts=""; recv=$0; kind="verifier"
      name=$0; sub(/\(.*/,"",name); sub(/^func[[:space:]]+(\([^)]*\)[[:space:]]*)?/,"",name)
      # receiver type, for the default/disabled/noop heuristic
      rtype=""; if (match($0, /^func[[:space:]]+\([^)]*\)/)) { rtype=substr($0,RSTART,RLENGTH) }
      next
    }
    inf {
      line=$0
      n=gsub(/\{/,"{",line); m=gsub(/\}/,"}",line); depth += n - m
      s=$0
      sub(/\/\/.*/,"",s)                # strip line comments
      gsub(/[{}]/,"",s); gsub(/^[[:space:]]+|[[:space:]]+$/,"",s)
      if (s != "" && s !~ /^func/) stmts = stmts "|" s
      if (depth <= 0) {
        inf=0
        # body reduced to exactly one statement: return nil
        clean=stmts; gsub(/^\|+|\|+$/,"",clean)
        if (clean == "return nil") emit("body is exactly `return nil` -- a no-op verifier that certifies nothing")
        else if (tolower(rtype) ~ /default|disabled|noop|no_op|unregistered|stub|fail.?open/ && stmts ~ /return nil/)
          emit("default/disabled-type verifier returns nil -- must fail CLOSED (return an error)")
      }
    }
  ' "$gf"
done)

if [ -n "$findings" ]; then
  echo "$findings"
  n=$(echo "$findings" | grep -c ':' || true)
  echo "    [FAIL] $n verifier(s) always accept -- a verification function must reject something; a default/unregistered verifier must fail CLOSED."
  exit 2
fi
echo "    [ok]   no no-op / fail-open verifier"
exit 0

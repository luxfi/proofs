#!/usr/bin/env bash
# circular-proof.sh -- catch the two unambiguous proof cheats and force
# disclosure of every axiom-backed load-bearing claim.
#
#   HARD FAIL (always): a load-bearing Lean theorem/def whose body is
#     `:= True` / `:= trivial` / `sorry` / `admit`. There is no honest reason
#     for a security claim to be vacuous. (Magnetar's `strict_atom_byte_equality
#     := by sorry` and `strictAtomDisciplineSatisfied : Prop := True` were
#     exactly this; this gate catches them.)
#
#   FAIL unless acknowledged: an EasyCrypt load-bearing lemma discharged by a
#     locally declared axiom. This MIGHT be legitimate (a standard algebraic
#     primitive such as `lagrange_inverse_eval`, the Lagrange identity) or the
#     cheat (axiomatizing the security conclusion itself, as Magnetar's
#     `combine_assemble_axiom` did). The framework does not guess: every such
#     axiom MUST be acknowledged with a justification in
#     `<repo>/.assurance/reviewed-axioms.txt` (one `AXIOM_NAME  justification`
#     per line). Acknowledged => disclosed-and-passed; unacknowledged => FAIL.
#     This forces the trust surface to be written down.
#
# Usage: circular-proof.sh <repo-root>
set -uo pipefail
ROOT="${1:?usage: circular-proof.sh <repo-root>}"
LOADBEARING='byte_equal|byte_equiv|interchang|unforge|euf|sound|secure|hiding|binding|zero.?knowledge|hvzk|no.?leak|non.?reveal|secret|reconstruct|preserves|well.?formed|clearance'
ALLOW="$ROOT/.assurance/reviewed-axioms.txt"
hard=0; unack=0

ack() { # is axiom $1 acknowledged in the allowlist?
  [ -f "$ALLOW" ] && grep -qE "^[[:space:]]*$1([[:space:]]|$)" "$ALLOW"
}

# ---- EasyCrypt: load-bearing lemma discharged by a local axiom ----
while IFS= read -r ecf; do
  [ -f "$ecf" ] || continue
  axset="$(grep -rhoE '^[[:space:]]*(declare[[:space:]]+)?axiom[[:space:]]+[A-Za-z0-9_]+' \
            "$(dirname "$ecf")" 2>/dev/null | awk '{print $NF}' | sort -u | tr '\n' ' ')"
  [ -z "${axset// /}" ] && continue
  while IFS= read -r hit; do
    [ -z "$hit" ] && continue
    ax="$(echo "$hit" | sed -n 's/.*||AX=\([A-Za-z0-9_]*\)||.*/\1/p')"
    msg="$(echo "$hit" | sed 's/||AX=[A-Za-z0-9_]*||//')"
    if ack "$ax"; then
      echo "    [disclosed] $msg (acknowledged in reviewed-axioms.txt)"
    else
      echo "$msg -- axiom NOT acknowledged in .assurance/reviewed-axioms.txt"
      unack=$((unack + 1))
    fi
  done < <(awk -v AX="$axset" -v LB="$LOADBEARING" -v F="$ecf" '
    BEGIN { n=split(AX, a, " "); for (i=1;i<=n;i++) if (a[i]!="") axiom[a[i]]=1 }
    /^[[:space:]]*(lemma|equiv|hoare)[[:space:]]+[A-Za-z0-9_]+/ {
      name=$2; gsub(/[^A-Za-z0-9_]/,"",name)
      inproof=1; span=0; usedax=""; lbname=(tolower(name) ~ LB); start=NR; next
    }
    inproof {
      span++
      for (ax in axiom) if ($0 ~ ("(apply|exact)[^A-Za-z0-9_]+" ax "([^A-Za-z0-9_]|$)")) usedax=ax
      if ($0 ~ /(^|[[:space:]])qed\./ || $0 ~ /^[[:space:]]*qed[[:space:]]*$/) {
        if (lbname && usedax != "" && span <= 12)
          printf("%s:%d: load-bearing `%s` discharged by axiom `%s` (%d-line proof)||AX=%s||\n", F, start, name, usedax, span, usedax)
        inproof=0
      }
    }
  ' "$ecf")
done < <(find "$ROOT" -name '*.ec' 2>/dev/null)

# ---- Lean: load-bearing vacuous body -> HARD FAIL (never acknowledgeable) ----
# Scan the WHOLE body of each load-bearing declaration (until the next
# declaration / end), not a fixed window: a `sorry` can sit many lines into a
# multi-line proof (Magnetar's was 10 lines in).
while IFS= read -r lf; do
  [ -f "$lf" ] || continue
  awk -v LB="$LOADBEARING" -v F="$lf" '
    function isdecl(s){ return s ~ /^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+)*(theorem|lemma|def|instance|abbrev|example)[[:space:]]/ }
    function flushlb(  ){ if (inlb && bad) printf("%s:%d: load-bearing Lean `%s` is VACUOUS (sorry/admit/:= True/trivial) -- proves nothing\n", F, start, name); inlb=0; bad=0 }
    {
      if (isdecl($0) || $0 ~ /^[[:space:]]*(end|section|namespace)([^A-Za-z]|$)/) {
        flushlb()
        if (isdecl($0)) {
          name=$0; sub(/^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+)*(theorem|lemma|def|instance|abbrev|example)[[:space:]]+/,"",name); sub(/[^A-Za-z0-9_'"'"'].*/,"",name)
          if (tolower($0) ~ LB) { inlb=1; start=NR }
        }
      }
      if (inlb && ($0 ~ /:=[[:space:]]*(True|trivial)([[:space:]]|$)/ || $0 ~ /:=[[:space:]]*by[[:space:]]+(trivial|sorry|admit)([[:space:]]|$)/ || $0 ~ /(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)/)) bad=1
    }
    END { flushlb() }
  ' "$lf"
done < <(find "$ROOT" -name '*.lean' 2>/dev/null) > /tmp/_circ_lean.$$ 2>/dev/null || true
if [ -s /tmp/_circ_lean.$$ ]; then cat /tmp/_circ_lean.$$; hard=$((hard + $(wc -l < /tmp/_circ_lean.$$))); fi
rm -f /tmp/_circ_lean.$$

if [ "$hard" -gt 0 ]; then
  echo "    [FAIL] $hard vacuous load-bearing Lean claim(s) -- a security theorem may never be := True/trivial/sorry."
  exit 2
fi
if [ "$unack" -gt 0 ]; then
  echo "    [FAIL] $unack load-bearing lemma(s) rest on an UNACKNOWLEDGED axiom -- add it (with justification) to .assurance/reviewed-axioms.txt or discharge it."
  exit 2
fi
echo "    [ok]   no vacuous claim; every axiom-backed load-bearing lemma is acknowledged"
exit 0

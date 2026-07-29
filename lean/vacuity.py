#!/usr/bin/env python3
"""Report declarations that carry less than they appear to.

Four ways a corpus can look larger than it is, all invisible to a build:

`... True`. `axiom mlwe_b_hard : forall (rp : RingParams), True` asserts nothing
— `True` is provable by `trivial`, so it constrains no model and a theorem
"reducing to" it reduces to nothing. It reads as a stated hardness assumption
and is a comment with a keyword in front of it.

`exists x, e = x`, closed by `rfl`. The witness is whatever the other side
evaluates to, so the equation says only that it has a value.

A conclusion that is one of its own hypotheses: `P -> P`, which proves nothing
about P.

An absent proof. `sorry` and `admit` close a goal by assertion. Both compile.

Lean accepts all four, `lake build` goes green, and an axiom count looks like
honest bookkeeping. So all are counted here, next to the build that cannot see
them, and counted over comment-stripped source — the naive grep for `sorry`
matches the word in prose and reports a corpus as unfinished when it is not.

The claim of a `def` is its body; of an axiom or theorem, everything before
`:=`. Cutting at `:=` for both is what let `TSUFBound : Prop := exists _a, True`
pass as content.

Exit status is 0 unless --strict is passed: these are numbers to publish and
watch before they are a gate.
"""

import re
import sys
from pathlib import Path

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:private |protected |noncomputable |partial |unsafe |scoped |local |nonrec )*"
    r"(axiom|theorem|lemma|def)\s+([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
BLOCK = re.compile(r"/-.*?-/", re.S)


def strip(text: str) -> str:
    """Remove block and line comments, then blank lines."""
    text = BLOCK.sub(" ", text)
    lines = (re.sub(r"--.*$", "", ln) for ln in text.splitlines())
    return "\n".join(ln for ln in lines if ln.strip())


def declarations(path: Path):
    """Yield (line, kind, name, body) for each top-level declaration."""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    starts = [(i, m) for i, ln in enumerate(lines) if (m := DECL.match(ln))]
    for n, (i, m) in enumerate(starts):
        end = starts[n + 1][0] if n + 1 < len(starts) else len(lines)
        yield i + 1, m.group(1), m.group(2), "\n".join(lines[i:end])


def arrows(stated: str):
    """Split a statement on top-level `→`, ignoring arrows inside brackets."""
    parts, depth, start = [], 0, 0
    for i, ch in enumerate(stated):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "→" and depth == 0:
            parts.append(stated[start:i]); start = i + 1
    parts.append(stated[start:])
    return [p.strip() for p in parts]


def vacuous(body: str, kind: str) -> str | None:
    """Name the way a statement carries no information, or None.

    For a theorem or axiom the claim is everything before `:=`; anything after
    is a proof term. For a `def` returning `Prop` the claim IS the body, which
    is why `TSUFBound : Prop := ∃ _a, True` reads as content until you look.
    """
    text = strip(body)
    stated = text.split(":=", 1)[1] if kind == "def" and ":=" in text else text.split(":=")[0]
    stated = stated.rstrip()

    # `... True` — provable by `trivial`, so it constrains nothing.
    if re.search(r"(?:^|[\s(,])True\s*$", stated):
        return "states True"

    # `∃ x, <expr> = x` — provable by `⟨_, rfl⟩`: the witness is whatever the
    # other side evaluates to, so the equation asserts only that it has a value.
    if m := re.search(r"∃\s*\(?\s*(?:_)?([A-Za-z][A-Za-z0-9_']*)\s*[:)][^,]*,\s*(.+)$",
                      stated, re.S):
        var, concl = m.group(1), m.group(2).strip()
        sides = [s.strip() for s in concl.split("=")]
        if len(sides) == 2 and var in sides and sides[0] != sides[1]:
            return "is provable by rfl"

    # `P → ... → P` — the conclusion is one of its own hypotheses.
    parts = arrows(stated)
    if len(parts) > 1:
        concl = re.sub(r"\s+", " ", parts[-1])
        for h in parts[:-1]:
            if re.sub(r"\s+", " ", h) == concl and len(concl) > 12:
                return "restates a hypothesis"
    return None


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    strict = "--strict" in sys.argv
    found, open_goals = [], []
    for path in sorted(root.rglob("*.lean")):
        # .lake holds the fetched dependencies. Counting Mathlib's declarations
        # as ours inflates every number here, and only after a build — so the
        # figure differs before and after CI runs, which is how this was found.
        if path.name == "lakefile.lean" or ".lake" in path.parts:
            continue
        rel = path.relative_to(root)
        for line, kind, name, body in declarations(path):
            if why := vacuous(body, kind):
                found.append((rel, line, kind, name, why))
        source = path.read_text(encoding="utf-8", errors="replace")
        for n, text in enumerate(strip(source).splitlines(), 1):
            if re.search(r"\b(sorry|admit)\b", text):
                open_goals.append((rel, n, text.strip()))

    by_kind = {}
    for _, _, kind, _, _ in found:
        by_kind[kind] = by_kind.get(kind, 0) + 1

    for path, line, kind, name, why in found:
        print(f"{path}:{line}: {kind} {name} {why}")
    for path, line, text in open_goals:
        print(f"{path}:{line}: unproved goal: {text}")

    print(f"\nvacuous declarations: {len(found)}", end="")
    if by_kind:
        print(" (" + ", ".join(f"{k} {n}" for k, n in sorted(by_kind.items())) + ")")
    else:
        print()
    print(f"unproved goals:       {len(open_goals)}")

    return 1 if (strict and (found or open_goals)) else 0


if __name__ == "__main__":
    sys.exit(main())

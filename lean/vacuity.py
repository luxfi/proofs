#!/usr/bin/env python3
"""Report declarations that carry less than they appear to.

Two ways a corpus can look larger than it is, both invisible to a build:

An empty statement. `axiom mlwe_b_hard : forall (rp : RingParams), True` asserts
nothing — `True` is provable by `trivial`, so the axiom constrains no model and
a theorem "reducing to" it reduces to nothing. It reads as a stated hardness
assumption and is a comment with a keyword in front of it.

An absent proof. `sorry` and `admit` close a goal by assertion. Both compile.

Lean accepts either, `lake build` goes green, and an axiom count looks like
honest bookkeeping. So both are counted here, next to the build that cannot see
them, and counted over comment-stripped source — the naive grep for `sorry`
matches the word in prose and reports a corpus as unfinished when it is not.

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


def vacuous(body: str) -> bool:
    """True when the statement's conclusion is the proposition `True`.

    The conclusion is what survives stripping comments and cutting the body at
    `:=`, since anything after it is a proof term rather than a claim.
    """
    stated = strip(body).split(":=")[0]
    return bool(re.search(r"(?:^|[\s(,])True\s*$", stated.rstrip()))


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    strict = "--strict" in sys.argv
    found, open_goals = [], []
    for path in sorted(root.rglob("*.lean")):
        if path.name == "lakefile.lean":
            continue
        rel = path.relative_to(root)
        for line, kind, name, body in declarations(path):
            if vacuous(body):
                found.append((rel, line, kind, name))
        source = path.read_text(encoding="utf-8", errors="replace")
        for n, text in enumerate(strip(source).splitlines(), 1):
            if re.search(r"\b(sorry|admit)\b", text):
                open_goals.append((rel, n, text.strip()))

    by_kind = {}
    for _, _, kind, _ in found:
        by_kind[kind] = by_kind.get(kind, 0) + 1

    for path, line, kind, name in found:
        print(f"{path}:{line}: {kind} {name} states True")
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

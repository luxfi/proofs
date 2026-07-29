#!/usr/bin/env python3
"""Report what every theorem in the corpus actually rests on.

A green build says each proof follows from what it was given. It does not say
what that was. `theorem safety` compiles whether it is proved from arithmetic or
handed to itself as an axiom two lines above, and only `#print axioms` tells
them apart.

Lean's own three axioms — propext, Classical.choice, Quot.sound — are the
ambient logic and are not assumptions about our systems. A theorem depending on
those alone is proved. A theorem depending on anything else is conditional on
it, and the axiom it names is load-bearing: if that axiom is false, the theorem
says nothing.

This generates a query file for every theorem in the corpus, runs it through
Lean, and reports the split, plus which of our axioms carry the most weight.

  python3 axioms.py .            report
  python3 axioms.py . --strict   exit 1 if any theorem rests on a vacuous axiom

Requires a built corpus: run `lake build` first.
"""

import re
import subprocess
import sys
from pathlib import Path

# The ambient logic of Lean plus Mathlib, not assumptions about our systems.
FOUNDATION = {"propext", "Classical.choice", "Quot.sound"}

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:private |protected |noncomputable |partial |unsafe |scoped |local |nonrec )*"
    r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?]*)"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
END = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_.']*)")
BLOCK = re.compile(r"/-.*?-/", re.S)


def module(path: Path, root: Path) -> str:
    return str(path.relative_to(root).with_suffix("")).replace("/", ".")


def theorems(path: Path, root: Path):
    """Yield (module, fully-qualified name) for each theorem in the file."""
    text = BLOCK.sub(lambda m: "\n" * m.group().count("\n"), path.read_text(
        encoding="utf-8", errors="replace"))
    scope, mod = [], module(path, root)
    for line in text.splitlines():
        line = re.sub(r"--.*$", "", line)
        if m := NAMESPACE.match(line):
            scope.append(m.group(1))
        elif m := END.match(line):
            if scope and scope[-1] == m.group(1):
                scope.pop()
        elif m := DECL.match(line):
            yield mod, ".".join(scope + [m.group(2)])


def built(root: Path) -> set:
    """Modules the build actually produced, by their .olean.

    A module in no library has no .olean, and importing one aborts the whole
    query file — so the modules this cannot report on are exactly the ones
    nothing checks. `lake build` names them; they are counted, not imported.
    """
    lib = root / ".lake" / "build" / "lib"
    return {str(p.relative_to(lib).with_suffix("")).replace("/", ".")
            for p in lib.rglob("*.olean")} if lib.is_dir() else set()


def query(root: Path, found) -> str:
    """A Lean file importing every module and printing each theorem's axioms."""
    mods = sorted({m for m, _ in found})
    lines = [f"import {m}" for m in mods]
    lines += [f"#print axioms {name}" for _, name in found]
    return "\n".join(lines) + "\n"


def parse(out: str):
    """Map theorem -> set of axioms it depends on."""
    deps = {}
    for m in re.finditer(
            r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
            out):
        name, axs = m.group(1), m.group(2)
        deps[name] = {a.strip() for a in axs.split(",") if a.strip()} if axs else set()
    return deps


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
    strict = "--strict" in sys.argv

    all_found = [(m, n) for p in sorted(root.rglob("*.lean"))
                 if p.name not in ("lakefile.lean",) and ".lake" not in p.parts
                 for m, n in theorems(p, root)]
    have = built(root)
    found = [(m, n) for m, n in all_found if m in have]
    skipped = sorted({m for m, _ in all_found if m not in have})
    if not found:
        print("no built theorems found; run `lake build` first", file=sys.stderr)
        return 1
    if skipped:
        print(f"not queried, module never compiled ({len(skipped)}): "
              + ", ".join(skipped) + "\n")

    path = root / "axioms_query.lean"
    path.write_text(query(root, found))
    try:
        run = subprocess.run(["lake", "env", "lean", str(path)],
                             cwd=root, capture_output=True, text=True, timeout=1800)
    finally:
        path.unlink(missing_ok=True)

    deps = parse(run.stdout)
    if not deps:
        print("no axiom output; is the corpus built? run `lake build`", file=sys.stderr)
        print(run.stderr[-2000:], file=sys.stderr)
        return 1

    # A theorem is proved when it rests on the ambient logic alone.
    proved = {n for n, a in deps.items() if a <= FOUNDATION}
    conditional = {n: a - FOUNDATION for n, a in deps.items() if not a <= FOUNDATION}

    weight = {}
    for axs in conditional.values():
        for a in axs:
            weight[a] = weight.get(a, 0) + 1

    for name in sorted(conditional):
        print(f"{name} rests on {', '.join(sorted(conditional[name]))}")

    total = len(deps)
    print(f"\ntheorems queried:   {total}")
    print(f"proved outright:    {len(proved)}")
    print(f"resting on axioms:  {len(conditional)}")
    if weight:
        print("\nload-bearing axioms, by number of theorems resting on them:")
        for a, n in sorted(weight.items(), key=lambda kv: (-kv[1], kv[0]))[:20]:
            print(f"  {n:>4}  {a}")

    if strict:
        # An axiom stating `True` carries no information, so a theorem resting
        # on one has no more content than the axiom does.
        vac = subprocess.run([sys.executable, str(root / "vacuity.py"), str(root)],
                             capture_output=True, text=True)
        empty = {m.group(1) for m in re.finditer(r"axiom (\S+) states True", vac.stdout)}
        bad = {n: a & empty for n, a in conditional.items() if a & empty}
        if bad:
            print(f"\n{len(bad)} theorems rest on an axiom that states `True`:")
            for n in sorted(bad):
                print(f"  {n} <- {', '.join(sorted(bad[n]))}")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Compute what upstreaming a mirror file would add to its Mathlib target's transitive imports.

`README.md`'s mirror-tree section asks a mirror file's module docstring to state that number, and
thirty-odd files under `Oka/` now do.  Before this script every one of those figures was produced
by a breadth-first search written from scratch in the session that needed it and thrown away
afterwards, and **on 2026-08-23 that instrument was written wrong twice, by two different agents,
and both wrong figures passed the project's standard validation.**  This is the same computation
with a test attached.

Usage:

    python3 scripts/import_cost.py Oka/Algebra/Category/ModuleCat/Sheaf/Generators.lean
    python3 scripts/import_cost.py --target Mathlib.Analysis.Complex.CoveringMap \
        Mathlib.FieldTheory.IsAlgClosed.Basic
    python3 scripts/import_cost.py --self-test

It reads text and nothing else: no build, no oleans, no `lake`.  Exit 0 unless something is wrong
with the arguments or the self-test fails; the cost itself is output, not a verdict, because the
figures live in English prose and nothing can check them mechanically.  See
`.orchestra/validation.sh` for what *is* a gate.

## The defect this exists to stop, which is not hypothetical

The obvious instrument is `re.compile(r"^(?:public\\s+)?import\\s+([\\w.]+)", re.M)` over the raw
file text.  **That matches `import` lines inside docstrings.**  Under `Mathlib/` there are

* **14 files** carrying such a line, **29 lines** in all;
* **2 of them a bare `import Mathlib`** — `Mathlib/Tactic/Rify.lean` and
  `Mathlib/Analysis/Normed/Algebra/Exponential.lean`, both inside fenced example blocks — at which
  point the computed closure becomes the entire library;
* and one that reaches almost every closure: **`Mathlib/Tactic/FunProp.lean`**, whose documentation
  shows `import Mathlib.Analysis.Complex.Trigonometric` as an example.  That single phantom edge
  pulls in **274** analysis modules.

The full list, for a reader who wants to check rather than believe: `AlgebraicGeometry/Scheme`,
`Tactic/Rify`, `Tactic/MinImports`, `Tactic/FunProp`, `Tactic/Common`, `Tactic/ExtractGoal`,
`Tactic/Linter/UpstreamableDecl`, `Tactic/Linter/Header`, `LinearAlgebra/Basis/VectorSpace`,
`RingTheory/AdicCompletion/AsTensorProduct`, `RingTheory/AdicCompletion/Functoriality`,
`Algebra/Group/UniqueProds/Basic`, `Data/Int/Log`, `Analysis/Normed/Algebra/Exponential`.  It is a
fact about Mathlib at a version and it will drift; the masking is what does not.

**The direction of the error is not predictable.**  The baseline always inflates, but the marginal
cost can move either way, because the phantom modules land on *both* sides of the subtraction.  In
the real instance, the true cost 103 was reported as 75.  "The total may be off but the delta is
probably fine" is a reading this project has used and it is not safe.

## Why the usual validation does not catch it

The convention here is to check a fresh instrument against the two figures the tree already
carries — `Mathlib.RingTheory.Localization.Finiteness` costs
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` **2**, and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` costs
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` **3**.  Both are in `self_test` below as regression
cases, and **both reproduce on the broken instrument**: neither target's closure reaches a
comment-embedded import in a way that moves the delta, because they sit in categories and algebra
and the phantom edges lead into analysis.  Two agreeing deltas in one corner of the library are
not a test of a closure computation.  The case that is a test is
`self_test`'s `import Mathlib` fixture, and the tripwire in `closure` is the cheap version of it.

## What is counted

**Mathlib modules only** — modules with a file under `Mathlib/`.  A closure also contains
`Aesop.*`, `Batteries.*`, `Init.*` and `Lean.*`, roughly a hundred of them, and two reviewers have
independently hit that discrepancy and each spent a paragraph attributing it.  The output says so
on every line that carries a number.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import deque
from pathlib import Path

MATHLIB = "/.lake/packages/mathlib"

IMPORT = re.compile(r"^(?:public\s+)?import\s+([\w.]+)", re.M)


def strip_comments(text: str) -> str:
    """`text` with comment *contents* removed and newlines kept.

    Block comments nest, and `/-!` and `/--` open one like any other `/-`.  Line comments run to
    the end of the line.  Without this, an `import` line inside a docstring is followed as if it
    were an import; see the module docstring for how much that costs.
    """
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i) and not text.startswith("-/", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


class Mathlib:
    """The Mathlib checkout, and import closures within it."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self._imports: dict[str, list[str] | None] = {}
        self.total = sum(1 for _ in (root / "Mathlib").rglob("*.lean"))

    def path_of(self, module: str) -> Path:
        return self.root / (module.replace(".", "/") + ".lean")

    def exists(self, module: str) -> bool:
        return self.path_of(module).exists()

    def imports_of(self, module: str) -> list[str] | None:
        """The modules `module` imports, or `None` if it has no file (Aesop, Batteries, …)."""
        if module in self._imports:
            return self._imports[module]
        path = self.path_of(module)
        if not path.exists():
            self._imports[module] = None
            return None
        found = IMPORT.findall(strip_comments(path.read_text(encoding="utf-8")))
        self._imports[module] = found
        return found

    def closure(self, modules: list[str]) -> set[str]:
        """Every Mathlib module reachable from `modules`, `modules` included.

        The size assertion is the cheap form of the self-test: a bare `import Mathlib` inside a
        docstring makes the closure the whole library, and no honest closure of a leaf module is
        anywhere near that.  It has fired.
        """
        seen: set[str] = set()
        queue = deque(modules)
        while queue:
            m = queue.popleft()
            if m in seen:
                continue
            seen.add(m)
            for x in self.imports_of(m) or []:
                if x not in seen:
                    queue.append(x)
        mathlib_only = {m for m in seen if self.exists(m)}
        assert len(mathlib_only) < self.total, (
            f"closure of {modules} is {len(mathlib_only)} of {self.total} Mathlib files — that is "
            "the whole library, which means a phantom `import Mathlib` was followed"
        )
        return mathlib_only

    def cost(self, target: str, new: list[str]) -> tuple[int, int, set[str]]:
        """`(baseline, cost, the modules added)` for adding `new` to `target`'s closure."""
        base = self.closure([target])
        both = self.closure([target] + new)
        return len(base), len(both) - len(base), both - base


def target_of(mirror: str) -> str | None:
    """`Oka/X/Y.lean` -> `Mathlib.X.Y`, or `None` when the path is not a mirror path."""
    p = Path(mirror)
    if p.parts[:1] != ("Oka",) or p.suffix != ".lean" or len(p.parts) < 2:
        return None
    return "Mathlib." + ".".join(p.parts[1:-1] + (p.stem,))


def report(ml: Mathlib, target: str, new: list[str]) -> None:
    base, delta, added = ml.cost(target, new)
    print(f"{target.replace('.', '/')}.lean: closure {base} Mathlib modules (Mathlib files only)")
    if not new:
        print("  no Mathlib imports to price")
        return
    print(f"  + {len(new)} import(s) -> cost {delta} Mathlib module(s)")
    if 0 < len(added) <= 30:
        for m in sorted(added):
            print(f"      {m}")
    elif added:
        print(f"      ({len(added)} modules, not listed)")


def self_test(ml: Mathlib) -> int:
    failures = 0

    def check(name: str, got: object, want: object) -> None:
        nonlocal failures
        ok = got == want
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: got {got!r}, want {want!r}")
        failures += not ok

    # The case the two regression figures below cannot see.  This is the whole point of the file.
    fixture = "module\npublic import A.B\n/-!\n```\nimport Mathlib\n```\n-/\npublic import C.D\n"
    check("an `import` inside a docstring is not followed",
          IMPORT.findall(strip_comments(fixture)), ["A.B", "C.D"])
    check("...and the unmasked regex does follow it, so the fixture is not vacuous",
          IMPORT.findall(fixture), ["A.B", "Mathlib", "C.D"])
    check("a nested block comment closes correctly",
          IMPORT.findall(strip_comments("/- a /- b -/ c -/\npublic import E.F\n")), ["E.F"])
    check("a line comment hides an import",
          IMPORT.findall(strip_comments("-- import G.H\npublic import I.J\n")), ["I.J"])

    # The two figures the tree already carries.  Regression cases, and NOT a test of the masking:
    # both reproduce on an instrument that does not mask, because neither target's closure reaches
    # a comment-embedded import in a way that moves the delta.  See the module docstring.
    check("Localization.Finiteness into Modules/Tilde.lean",
          ml.cost("Mathlib.AlgebraicGeometry.Modules.Tilde",
                  ["Mathlib.RingTheory.Localization.Finiteness"])[1], 2)
    check("ModuleCat.Sheaf.Generators into Modules/Sheaf.lean",
          ml.cost("Mathlib.AlgebraicGeometry.Modules.Sheaf",
                  ["Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators"])[1], 3)

    check("a mirror path maps to its target",
          target_of("Oka/Algebra/Category/ModuleCat/Sheaf/Free.lean"),
          "Mathlib.Algebra.Category.ModuleCat.Sheaf.Free")
    check("a non-mirror path maps to nothing", target_of("OkaTest/Foo.lean"), None)

    print("self-test failed" if failures else "self-test passed")
    return 1 if failures else 0


def main() -> int:
    root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    )
    mathlib_root = Path(str(root) + MATHLIB)
    if not (mathlib_root / "Mathlib").is_dir():
        print(f"no Mathlib checkout at {mathlib_root}; run `lake exe cache get` first")
        return 2
    ml = Mathlib(mathlib_root)

    args = sys.argv[1:]
    if "--self-test" in args:
        return self_test(ml)

    if args[:1] == ["--target"]:
        if len(args) < 2:
            print("--target needs a module name")
            return 2
        report(ml, args[1], args[2:])
        return 0

    if len(args) != 1:
        print(__doc__.split("Usage:")[1].split("It reads text")[0].strip())
        return 2

    mirror = args[0]
    target = target_of(mirror)
    if target is None:
        print(f"{mirror} is not a mirror path (`Oka/X/Y.lean`); use --target to price by hand")
        return 2
    if not ml.exists(target):
        print(f"{mirror} mirrors {target.replace('.', '/')}.lean, which does not exist in Mathlib")
        return 2
    path = root / mirror
    if not path.exists():
        print(f"{mirror} does not exist")
        return 2
    mods = [m for m in IMPORT.findall(strip_comments(path.read_text(encoding="utf-8")))
            if m.startswith("Mathlib.")]
    report(ml, target, mods)
    return 0


if __name__ == "__main__":
    sys.exit(main())

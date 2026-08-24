#!/usr/bin/env python3
"""Check that every entry under `scripts/` is named in `README.md`.

Nothing else notices a script nobody wrote a sentence about.  `lake build`, `lake lint`,
`lake exe lint-style`, `mk_all --check`, `scripts/check_docstring_names.py` and
`scripts/check_module_docstrings.py` all look at `.lean` files under `Oka/` and `OkaTest/`, or at
declarations in the environment; not one of them reads the `scripts/` directory listing.  On
2026-08-24, `README.md` named **three** of the six entries under `scripts/`, and the three it did
not name included `check_docstring_names.py` — a check `.orchestra/validation.sh` runs and whose
figures every pull request body on this project quotes, described twice in `README.md` and never
given a filename.  Four days of drift, and every check in the repository was green throughout.

Usage:

    python3 scripts/check_scripts_documented.py       # check the tree
    python3 scripts/check_scripts_documented.py --self-test

Exits 0 when every entry under `scripts/` is named, 1 when some are not.  It reads two things —
the directory listing and `README.md` — and nothing else: no build, no oleans, no `lake`.

## The rule, and how little it secures

An entry passes when its **bare name** occurs as a literal substring anywhere in `README.md`.
That is deliberately the loosest form, and the honest description of what it buys is: it catches a
file under `scripts/` that nobody wrote a sentence about, and **nothing else**.  It cannot tell
you that a description is present, or true, or that it still matches the script.  This is the same
guarantee Mathlib's own `undocumentedScripts` gives — its whole test is one `String.contains`
call, at `.lake/packages/mathlib/scripts/lint-style.lean:180` — and taxis #964 measured that a
file holding six backticked names and not one word of prose satisfies it and exits 0.

Three choices are deliberate and each has a cheaper-looking alternative that is wrong here.

* **The bare name, not the path.**  `README.md` already writes the path form in one place
  (`` `scripts/check_module_docstrings.py` ``) and a command in another
  (`` `bash scripts/check_file.sh FILE.lean` ``), so the two forms in the tree differ; a
  path-form rule would fail on text that is perfectly clear.
* **Anywhere in the file, not inside `### Checking`.**  Scoping to a heading is stricter and it
  makes that heading something a check depends on, so renaming a section breaks the build.  The
  looser rule never does, and the drift this check exists to catch is a file mentioned *nowhere*
  rather than a file mentioned in the wrong paragraph.
* **No exemption list, and no ignore file.**  `scripts/docstring-names-ignore.txt` is a data file
  rather than a script, and Mathlib's check would report it too — its `dataFiles` array exempts
  Mathlib's own two data files and not ours.  The cheap answer is an exemption; the cheaper one is
  a sentence in `README.md` saying what the file is, which costs less than any mechanism and
  leaves the reader better off.  taxis #954 declined to create an empty exception file for
  `lint-style` on the same reasoning, and `scripts/docstring-names-ignore.txt`'s own history —
  created 2026-08-22 16:53Z asserting it would stay empty, two entries by 19:49Z — is what that
  decision was made on.

## The one way the loose rule can be unsound, and it is checked rather than assumed

If one entry's name is a substring of another's — `foo.py` and `myfoo.py`, say — then naming the
longer satisfies the shorter, and the check would pass a tree in which the shorter is undocumented.
That is a property of the *directory*, not of `README.md`, so it is testable directly and this
script reports it as a failure rather than leaving the rule quietly wrong.  No such pair exists
today; the guard is here so that the day one is added is the day somebody is told.

`--self-test` plants each shape and confirms it is reported, because a check that has only ever
been seen to pass is not evidence of anything.  `.orchestra/validation.sh` records the same
discipline for its own checks, and records `lake exe lint-style` reaching half the tree for weeks
while every pull request quoted it as evidence that style had been checked.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

# The directory whose entries must be named, and the file they must be named in.  Both are
# relative to the repository root.
SCRIPTS = "scripts"
INDEX = "README.md"


def entries(root: Path) -> list[str]:
    """The names of the top-level entries under `scripts/`, sorted.

    Top-level rather than recursive: a directory is one thing to describe, and describing it is
    what the sentence in `README.md` would be about.  There are none today.
    """
    d = root / SCRIPTS
    return sorted(p.name for p in d.iterdir()) if d.is_dir() else []


def shadowed(names: list[str]) -> list[tuple[str, str]]:
    """Pairs `(short, long)` where naming `long` would satisfy `short` by accident."""
    return [(a, b) for a in names for b in names if a != b and a in b]


def undocumented(names: list[str], index: str) -> list[str]:
    """Those of `names` that do not occur as a substring of `index`."""
    return [n for n in names if n not in index]


def check(root: Path) -> int:
    names = entries(root)
    index = (root / INDEX).read_text(encoding="utf-8")
    missing = undocumented(names, index)
    pairs = shadowed(names)
    for name in missing:
        print(f"{SCRIPTS}/{name}: not named anywhere in {INDEX}")
    for short, long in pairs:
        print(
            f"{SCRIPTS}/{short}: its name is a substring of {SCRIPTS}/{long}, so naming the "
            f"second would satisfy the first and this check would stop covering it"
        )
    print(f"checked {len(names)} entries under {SCRIPTS}/: {len(missing)} not named in {INDEX}")
    if missing or pairs:
        print(
            f"Every file under {SCRIPTS}/ needs a sentence in {INDEX} saying what it is for. "
            f"See the `### Checking` section, which is where the others are described."
        )
        return 1
    return 0


def self_test() -> int:
    """Plant each shape and confirm this script reports it.

    Both directions, because a checker that always failed would pass a negative test on its own:
    a tree in which every entry is named exits 0, and each of the two defects exits 1.
    """
    cases: list[tuple[str, list[str], str, list[str]]] = [
        ("every name present", ["a.py", "b.sh"], "run `a.py` and `b.sh`.", []),
        ("one name absent", ["a.py", "b.sh"], "run `a.py`.", ["b.sh"]),
        ("no names present", ["a.py", "b.sh"], "nothing here.", ["a.py", "b.sh"]),
        # The path form is *not* required: `README.md` writes both forms today and a path rule
        # would reject prose that is perfectly clear.
        ("a bare name inside a longer path", ["a.py"], "`scripts/a.py`", []),
        # And a name that occurs in ordinary prose rather than in backticks passes.  The rule is
        # substring containment; requiring backticks would be a second convention to keep.
        ("a name outside backticks", ["a.py"], "we run a.py nightly.", []),
    ]
    failures = 0
    for name, names, index, want in cases:
        got = undocumented(names, index)
        ok = got == want
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: reports {got or 'nothing'}")
        failures += not ok

    shadow_cases: list[tuple[str, list[str], list[tuple[str, str]]]] = [
        ("no name shadows another", ["a.py", "b.sh"], []),
        ("one name contains another", ["foo.py", "myfoo.py"], [("foo.py", "myfoo.py")]),
    ]
    for name, names, want in shadow_cases:
        got = shadowed(names)
        ok = got == want
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: reports {got or 'nothing'}")
        failures += not ok

    # And the same end to end, through `check` and its exit code, on a throwaway tree.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / SCRIPTS).mkdir()
        (root / SCRIPTS / "documented.py").write_text("", encoding="utf-8")
        (root / INDEX).write_text(
            "Run `scripts/documented.py` to do the thing.\n", encoding="utf-8"
        )
        green = check(root)
        print(f"  [{'ok' if green == 0 else 'FAIL'}] a named tree exits 0 (got {green})")
        failures += green != 0

        (root / SCRIPTS / "silent.sh").write_text("", encoding="utf-8")
        red = check(root)
        print(f"  [{'ok' if red == 1 else 'FAIL'}] a planted unnamed script exits 1 (got {red})")
        failures += red != 1
        (root / SCRIPTS / "silent.sh").unlink()

        # The shadowing guard end to end: both names occur in the index, so the containment rule
        # would report nothing, and the check must still fail.
        (root / SCRIPTS / "undocumented.py").write_text("", encoding="utf-8")
        (root / INDEX).write_text(
            "Run `scripts/undocumented.py` to do the thing.\n", encoding="utf-8"
        )
        red = check(root)
        print(f"  [{'ok' if red == 1 else 'FAIL'}] a planted shadowing pair exits 1 (got {red})")
        failures += red != 1

    print("self-test failed" if failures else "self-test passed")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv[1:]:
        return self_test()
    root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    )
    return check(root)


if __name__ == "__main__":
    sys.exit(main())

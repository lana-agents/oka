#!/usr/bin/env python3
"""Check that every backticked dotted name in a comment or docstring resolves.

Nothing else in this repository looks inside a comment.  `lake build --wfail` sees only
elaborated terms; `lake lint` checks declaration *names* and `simp` normal forms; `lake exe
lint-style` checks whitespace, line endings and unicode; `mk_all --check` checks imports; and the
declaration-name diff that every pull request body runs compares declarations rather than the
prose citing them.  A backticked name in a `/-- … -/` or `/-! … -/` block that names nothing at
all passes every one of them, and on 2026-08-20/21 that cost four separate findings in one day,
each caught by a human who happened to be reading the file for another reason.  The worst was
five wrong names appearing at once because the cause was structural — a file drafted in a
scratch buffer with no `namespace` line — which is the class that proofreading cannot see and a
checker cannot miss.

Usage:

    python3 scripts/check_docstring_names.py            # dump the environment, then check
    python3 scripts/check_docstring_names.py --dump F   # reuse a dump written earlier

Exits 0 when every candidate resolves, 1 when some do not, 2 when the environment dump fails.
`lake build` must have run first: this reads the oleans, it does not produce them.

## What counts as a candidate

A backtick-delimited run of non-backtick, non-whitespace characters, occurring inside a `--`,
`/- -/`, `/-- -/` or `/-! -/` region of a `.lean` file under `Oka/` or `OkaTest/`, containing at
least one `.`, and shaped like a Lean name: every dot-separated component non-empty and starting
with a letter or `_`, every character alphanumeric or one of `_ ' ! ?`.  That shape test alone
discards `Mathlib/RingTheory/Filtration.lean`, `[M.IsCoherent]`, `Scheme.{0}`,
`?V.isOpenEmbedding` and `⊤.isOpenEmbedding` without any of them needing to be listed anywhere.

## What counts as resolving

Deliberately more permissive than Lean's own name resolution, in the direction that avoids false
positives.  A candidate resolves if any of the following holds.

* **Suffix rule.**  Some constant in the environment of `Oka` + `OkaTest` ends with it, as a run
  of whole components.  This is "resolves with every namespace in the environment open", so
  `Multicoequalizer.desc` passes in a file that opens `CategoryTheory.Limits` and equally in one
  that does not.  Tracking each file's own `open`s and `namespace`s, which is what Lean would
  do, buys precision this check does not need and costs a false positive every time the tracking
  is wrong.

* **Module rule.**  It is the name of a module in the environment.  Docstrings here cite modules
  in the same backticked form as declarations: `Oka.Weierstrass`, `Mathlib.RingTheory.Filtration`.

* **File rule.**  It names a file that exists in the repository.  This is what lets `README.md`
  and `lakefile.toml` — whose components happen to be identifier-shaped, unlike anything with a
  `/` in it — through without an entry each in the ignore file.

* **Field-notation rule.**  Splitting the candidate as `head.tail` at any dot, `head` resolves by
  the suffix or module rule and is *not itself a namespace* — no constant or module has it as a
  run of components with further components after it.  Then `head.tail` is generalised field
  notation on the term `head` rather than a declaration name, which is legitimate and idiomatic
  prose: `restrictTopIso.hom`, `adicCompletionEquiv.symm`, `existsUnique_axisIncl.exists.choose`,
  `AlgebraicGeometry.identityToΓSpec.naturality`.

  The namespace condition is what keeps this from swallowing the findings it is meant to leave
  alone.  `AlgebraicGeometry.Scheme.OpenCover.glueMorphisms` — the reference this checker was
  written to catch, Mathlib having renamed the namespace to `Scheme.Cover` while leaving the
  *type* called `X.OpenCover` — has `AlgebraicGeometry.Scheme.OpenCover` as a head that does
  resolve, so without the namespace condition it would be accepted; with it the head is a
  namespace with twenty declarations in it and the candidate is still reported.

  The hole this leaves, stated so that nobody has to rediscover it: a *misspelled* declaration in
  a namespace that contains no other declaration is read as field notation and accepted.  The
  common structural failure — a whole file's worth of names in the wrong namespace — is not of
  that shape, because the namespace either exists with declarations in it or does not resolve
  at all.

* **Short-head rule.**  The head component is at most two characters *and is not a root
  namespace* — no constant begins with it.  `i.stalkMap`, `Γ.map`, `φ.symm`, `U.extend'`, `w.2`
  are field notation on a local binder.

  The second condition is not decoration.  An earlier version of this rule said that no namespace
  on this project or in Mathlib is that short; that is **false** — `Eq`, `Or`, `Ne` and `Id` are,
  with 52, 24, 38 and 20 constants under them, `Eq.symm` and `Eq.mp` among them — so without it a
  misspelled `Eq.symmm` is accepted silently.

  *Root* namespace rather than namespace-anywhere, and the difference is the whole live
  population of this rule.  `Γ`, `M`, `V`, `X` and `w` all occur as interior components of some
  constant (`…Γ.map`, `…M.foo`), so the namespace-anywhere test rejects every one of the seven
  short heads actually used in this tree and reports twelve false positives.  None of them occurs
  at the root, and `Eq`, `Or`, `Ne`, `Id` all do.  Measured, not assumed — the first version of
  this rule assumed and was wrong in both directions on the same day.

Anything left over is a finding unless `scripts/docstring-names-ignore.txt` lists it.

## What a green here does NOT mean

A name that resolves *somewhere* but not where the prose means it to is accepted; so is a name
spelled correctly that describes the wrong theorem, and any name outside backticks.  The suffix
rule in particular accepts `Foo.bar` whenever any namespace at all has a `bar` in it.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IGNORE_FILE = os.path.join("scripts", "docstring-names-ignore.txt")
DUMP_SCRIPT = os.path.join("scripts", "DumpEnvNames.lean")
ROOTS = ("Oka", "OkaTest")

# A candidate whose head component is at most this long, and is not a root namespace, is field
# notation on a local binder rather than a declaration reference.
MAX_LOCAL_HEAD = 2


def comment_regions(text: str) -> list[tuple[int, int]]:
    """Offsets of every comment and docstring region, block comments nesting as Lean's do.

    String literals are skipped, so that a `--` or `/-` inside one does not open a region.
    """
    regions = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                j = n
            regions.append((i, j))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            start = j
            while j < n and depth > 0:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            regions.append((start, j - 2 if depth == 0 else n))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            i = j
        else:
            i += 1
    return regions


def is_name_shaped(s: str) -> bool:
    """Whether `s` could be a Lean name: dot-separated components of identifier characters."""
    parts = s.split(".")
    if len(parts) < 2:
        return False
    for p in parts:
        if not p or not (p[0].isalpha() or p[0] == "_"):
            return False
        if any(not (c.isalnum() or c in "_'!?") for c in p):
            return False
    return True


def candidates() -> dict[str, list[tuple[str, int]]]:
    """Every candidate name in the tree, as a map from the name to the places it occurs."""
    paths = []
    for root in ROOTS:
        for dirpath, _, filenames in os.walk(os.path.join(REPO, root)):
            paths += [os.path.join(dirpath, f) for f in filenames if f.endswith(".lean")]
        paths.append(os.path.join(REPO, root + ".lean"))
    found: dict[str, list[tuple[str, int]]] = {}
    for path in sorted(paths):
        rel = os.path.relpath(path, REPO)
        with open(path, encoding="utf-8") as f:
            text = f.read()
        for (a, b) in comment_regions(text):
            for m in re.finditer(r"`([^`\s]+)`", text[a:b]):
                s = m.group(1)
                if "." not in s or not is_name_shaped(s):
                    continue
                found.setdefault(s, []).append((rel, text.count("\n", 0, a + m.start()) + 1))
    return found


def scan(dump: str, wanted: set[str],
         heads: set[str]) -> tuple[set[str], set[str], set[str], int]:
    """One pass over the dump, classifying `wanted` and `heads` against every name in it.

    A *suffix* is a run of whole components reaching the end of the name; a *namespace* is a run
    of whole components with at least one component after it; a *root namespace* is a namespace
    run that also starts at the first component.  Iterating over the dump and testing its runs
    against the two small sets, rather than indexing every run of every name, keeps this linear
    in the dump with nothing but those sets held in memory.

    Returns `(resolved, namespaces, root_namespaces, lines)`.
    """
    resolved: set[str] = set()
    namespaces: set[str] = set()
    root_namespaces: set[str] = set()
    lines = 0
    with open(dump, encoding="utf-8") as f:
        for line in f:
            full = line.rstrip("\n")
            if not full:
                continue
            lines += 1
            parts = full.split(".")
            last = len(parts) - 1
            for i in range(len(parts)):
                run = parts[i]
                for j in range(i, len(parts)):
                    if j > i:
                        run += "." + parts[j]
                    if j == last:
                        if run in wanted:
                            resolved.add(run)
                    elif run in heads:
                        namespaces.add(run)
                        if i == 0:
                            root_namespaces.add(run)
    return resolved, namespaces, root_namespaces, lines


def read_ignore() -> set[str]:
    path = os.path.join(REPO, IGNORE_FILE)
    if not os.path.exists(path):
        return set()
    out = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                out.add(line)
    return out


def build_dump() -> str:
    """Run `scripts/DumpEnvNames.lean` and return the path it wrote."""
    fd, path = tempfile.mkstemp(prefix="oka-env-names-", suffix=".txt")
    os.close(fd)
    proc = subprocess.run(
        ["lake", "env", "lean", DUMP_SCRIPT], cwd=REPO,
        env=dict(os.environ, OKA_ENV_NAME_DUMP=path), capture_output=True, text=True,
    )
    if proc.returncode != 0 or not os.path.getsize(path):
        sys.stderr.write(proc.stdout + proc.stderr)
        sys.stderr.write(
            "\nFailed to dump the environment of `Oka` + `OkaTest`. `lake build` must have run\n"
            "first: this reads the oleans, it does not produce them.\n"
        )
        os.unlink(path)
        sys.exit(2)
    return path


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Check that backticked dotted names in comments resolve.")
    ap.add_argument("--dump", metavar="FILE",
                    help="reuse a name dump written earlier instead of building one")
    args = ap.parse_args()

    found = candidates()
    # Every proper prefix of every candidate is a possible head for the field-notation rule, and
    # has to be classified as resolving-or-not and as a namespace-or-not just as candidates do.
    wanted = set(found)
    heads = set()
    for name in found:
        parts = name.split(".")
        for k in range(1, len(parts)):
            heads.add(".".join(parts[:k]))
    wanted |= heads

    dump = args.dump or build_dump()
    resolved, namespaces, root_namespaces, dumped = scan(dump, wanted, heads)
    if not args.dump:
        os.unlink(dump)

    def is_field_notation(name: str) -> bool:
        parts = name.split(".")
        for k in range(len(parts) - 1, 0, -1):
            head = ".".join(parts[:k])
            if head in resolved and head not in namespaces:
                return True
        return False

    def is_local_binder(name: str) -> bool:
        head = name.split(".")[0]
        return len(head) <= MAX_LOCAL_HEAD and head not in root_namespaces

    ignored = read_ignore()
    findings = [
        name for name in sorted(found)
        if name not in resolved
        and name not in ignored
        and not is_local_binder(name)
        and not os.path.exists(os.path.join(REPO, name))
        and not is_field_notation(name)
    ]

    for name in findings:
        for (path, line) in found[name]:
            print(f"{path}:{line}: `{name}` names nothing in the environment")

    total = sum(len(v) for v in found.values())
    print(f"checked {total} backticked names ({len(found)} distinct) against {dumped} "
          f"declarations and modules: {len(findings)} unresolved")
    if findings:
        print(
            "\nEach name above is spelled in a comment and resolves to nothing. Fix the prose.\n"
            f"If one of them is not a declaration reference at all, add it to {IGNORE_FILE}\n"
            "with a comment saying what it is instead.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

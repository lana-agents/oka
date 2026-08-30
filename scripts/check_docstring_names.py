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

    python3 scripts/check_docstring_names.py             # dump the environment, then check
    python3 scripts/check_docstring_names.py --dump F    # reuse a dump written earlier
    python3 scripts/check_docstring_names.py --tree DIR  # ...against another checkout
    python3 scripts/check_docstring_names.py --diff BASE # the name diff, no build needed
    python3 scripts/check_docstring_names.py --diff BASE --sites   # ...per occurrence
    python3 scripts/check_docstring_names.py --self-test

Exits 0 when every candidate resolves, 1 when some do not, and 2 when the tool itself cannot
answer: the environment dump fails, `--tree` or `--diff` names something that is not a checkout of
this repository, `--sites` is given without `--diff`, or the self-test does not pass.  `lake build`
must have run first: this reads the oleans, it does not produce them.  `--diff` is the exception
and reads no environment at all.

## The name diff, and the no-op that used to drive it

Every pull request body on this project reports how the *distinct* candidate count moved between
the base and the branch, and until 2026-08-29 this script offered no way to compute one, so each
session wrote its own driver.  The obvious driver is wrong:

    spec = importlib.util.spec_from_file_location("chk", "scripts/check_docstring_names.py")
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    def names(tree):
        os.chdir(tree); return set(m.candidates())     # the chdir is inert

`REPO` below is bound **at import time from this file's own path**, and `os.chdir` does not move
it, so that driver scans one tree twice and prints `added: [] removed: []` with equal counts
whatever the branch did.  **Its failure mode is the answer the reader is hoping for**: a
docs-only branch is supposed to move the count by zero, so the no-op's output is what a clean
branch produces — no error, no traceback, no suspicious figure.  It shipped in two verdicts
before anything noticed, and what noticed was a delivery note whose figure disagreed with it.

So `--diff BASE` is here, it needs no build because candidacy is a text property, and
`--self-test` is a **positive** control: two fixture trees that differ, asserted to diff to
non-empty.  "Two identical trees diff to empty" is the test the broken driver passes.

**One implementation scans both trees** — this file's, whichever tree it lives in.  That is
deliberate and it is what isolates a change in the *prose* from a change in the *rules*: a branch
that edits `is_name_shaped` or `comment_regions` will not show up in `--diff` at all.  Run the
check itself, not the diff, to see the effect of a rule change.

**`--diff` alone is silent on a branch that only rewords, and `--sites` is what is not.**  A
docstring commit that swaps words *between* backticked names that already exist adds no name and
no occurrence, so `added`, `removed` and both figures are identical on the two trees — which is
byte-for-byte the output of a driver that read one tree twice.  That happened on
lana-agents/oka#246, whose delivery note had to say in terms that none of its figures was
evidence.  `--sites` compares the `file:line` of every occurrence instead of the name set: on that
branch it reports **9 moved sites across 8 names, all in the edited file, every delta `+1`**, and
an empty site diff is what a same-tree comparison returns by construction.  Pick the report by
what the branch can move — declarations move the distinct count, rewording moves occurrences, a
word swapped between two existing names moves only sites.

**The two figures `--diff` prints are the headline's own**, and there is no second definition of
either: the `N backticked names (M distinct)` line at the end of a normal run is
`sum(len(v) for v in candidates().values())` and `len(candidates())`, which is exactly what
`report` below computes.  So `--diff BASE --tree BASE` reproduces the base's own headline, and a
pull request body can quote both figures from one command.  Measured 2026-08-29: `f6a5fa9` gives
`6112 backticked names (2159 distinct)` and `70580e1` gives `6115 (2159)`, each agreeing with
that tree's own copy of this script loaded by path.  A note on taxis #1192 reported the
occurrence count as running "one or two below" the headline; it does not, and what was being
compared was two different trees.

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

  **A generated name does not count as making its parent a namespace**, and this is not a
  refinement: without it the rule is *non-monotone*, which no other rule here is.  Lean plants an
  equation lemma under a definition's own name — `thatDef.eq_1`, and `_proof_1` beside it — the
  first time any tactic anywhere unfolds it.  So `rw [thatDef]` in one file would make `thatDef`
  a namespace, and every `` `thatDef.someField` `` citation *in every other file* would start
  being reported, at a distance, with a message about the environment having nothing in it when
  what happened is that the environment gained something.  Measured on `master` = `7b6faa9`, with
  no branch involved: `AlgebraicGeometry.AffineScheme.Γ` has exactly one child in the whole
  environment, `AlgebraicGeometry.AffineScheme.Γ.eq_1`, and before this condition existed
  `` `AlgebraicGeometry.AffineScheme.Γ.someField` `` was reported while the structurally identical
  `` `AlgebraicGeometry.identityToΓSpec.naturality` `` — whose head has no children at all — was
  accepted.

  `GENERATED_COMPONENT` is deliberately narrow: the components generated for a *`def`*, and not
  the ones generated for an inductive or a structure (`rec`, `casesOn`, `mk`, `injEq`,
  `noConfusion`, `sizeOf_spec`, `ctorIdx`).  A head that carries *those* really is a type, and the
  namespace exclusion is right about it.  **How the list going stale would be noticed**: not by
  maintaining it against Lean's, but by the finding message, which names the head, says it does
  resolve, and names the declaration that made it a namespace — so a suffix this list is missing
  costs one line rather than the session the first instance cost.  On `master` the whole list
  changes the classification of exactly one head, `AlgebraicGeometry.AffineScheme.Γ`, out of the
  236 that both resolve and are namespaces.

  The hole this leaves, stated so that nobody has to rediscover it: a *misspelled* declaration in
  a namespace that contains no other declaration — or none other than generated ones — is read as
  field notation and accepted.  The common structural failure — a whole file's worth of names in
  the wrong namespace — is not of that shape, because the namespace either exists with
  declarations in it or does not resolve at all.

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
import collections
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

# A name component the elaborator generates for the declaration it hangs off, rather than one an
# author wrote.  Such a component must not make its parent a namespace: see the field-notation
# rule in the module docstring above for why, and for the measurement that says this list is
# narrow on purpose.  Everything here is generated *for a `def`* and appears without warning the
# first time a tactic unfolds one; the components generated for an *inductive* or a *structure* —
# `rec`, `casesOn`, `mk`, `injEq`, `noConfusion`, `ctorIdx`, `sizeOf_spec` — are deliberately
# absent, because a head that has those really is a type and the namespace exclusion is right
# about it.
GENERATED_COMPONENT = re.compile(
    r"_.*|eq_\d+|eq_def|eq_unfold|match_\d+|proof_\d+|induct|fun_cases")


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


def candidates(repo: str | None = None) -> dict[str, list[tuple[str, int]]]:
    """Every candidate name in the tree, as a map from the name to the places it occurs.

    `repo` is the checkout to walk, defaulting to the one this file lives in.  It is a parameter
    and not the module-level `REPO` so that two trees can be scanned in one process, which is
    what `--diff` needs and what the `os.chdir` driver this replaced could not do.
    """
    repo = REPO if repo is None else repo
    paths = []
    for root in ROOTS:
        for dirpath, _, filenames in os.walk(os.path.join(repo, root)):
            paths += [os.path.join(dirpath, f) for f in filenames if f.endswith(".lean")]
        paths.append(os.path.join(repo, root + ".lean"))
    found: dict[str, list[tuple[str, int]]] = {}
    for path in sorted(paths):
        rel = os.path.relpath(path, repo)
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
         heads: set[str]) -> tuple[set[str], set[str], set[str], dict[str, str], int]:
    """One pass over the dump, classifying `wanted` and `heads` against every name in it.

    A *suffix* is a run of whole components reaching the end of the name; a *namespace* is a run
    of whole components with at least one component after it, **where that next component is one
    an author wrote**; a *root namespace* is a namespace run that also starts at the first
    component.  Iterating over the dump and testing its runs against the two small sets, rather
    than indexing every run of every name, keeps this linear in the dump with nothing but those
    sets held in memory.

    The `GENERATED_COMPONENT` condition is the one thing here that is not the obvious reading of
    "namespace".  Without it a `def` becomes a namespace the moment any tactic anywhere unfolds
    it, because that plants an equation lemma under its own name — so the classification would
    depend on which files happen to contain a `rw [thatDef]`, and it would turn *off* the
    field-notation rule for citations of that definition in unrelated files.

    Returns `(resolved, namespaces, root_namespaces, namespace_cause, lines)`, the fourth being
    one witness per namespace: the shortest name in the dump that put it there, which is what
    the finding message needs in order to say why field notation was not tried.
    """
    resolved: set[str] = set()
    namespaces: set[str] = set()
    root_namespaces: set[str] = set()
    namespace_cause: dict[str, str] = {}
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
                    elif run in heads and not GENERATED_COMPONENT.fullmatch(parts[j + 1]):
                        namespaces.add(run)
                        namespace_cause.setdefault(run, ".".join(parts[:j + 2]))
                        if i == 0:
                            root_namespaces.add(run)
    return resolved, namespaces, root_namespaces, namespace_cause, lines


def read_ignore(repo: str | None = None) -> set[str]:
    path = os.path.join(REPO if repo is None else repo, IGNORE_FILE)
    if not os.path.exists(path):
        return set()
    out = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                out.add(line)
    return out


def build_dump(repo: str | None = None) -> str:
    """Run `scripts/DumpEnvNames.lean` in `repo` and return the path it wrote."""
    repo = REPO if repo is None else repo
    fd, path = tempfile.mkstemp(prefix="oka-env-names-", suffix=".txt")
    os.close(fd)
    proc = subprocess.run(
        ["lake", "env", "lean", DUMP_SCRIPT], cwd=repo,
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


def report(repo: str, found: dict[str, list[tuple[str, int]]]) -> str:
    """The one line that names a tree and its two figures, in the headline's own wording."""
    total = sum(len(v) for v in found.values())
    return f"{repo}: {total} backticked names ({len(found)} distinct)"


def check_tree(path: str, what: str) -> str:
    """Resolve a `--tree` / `--diff` argument, failing loudly rather than on a missing file.

    Without this a mistyped path reaches `candidates`, which walks a directory that is not there
    — `os.walk` on a missing directory yields nothing rather than raising — and then dies on
    `Oka.lean` with a bare `FileNotFoundError`.  A worktree that has not been created yet is the
    common case and it deserves a sentence.
    """
    real = os.path.realpath(path)
    if not all(os.path.exists(os.path.join(real, f + ".lean")) for f in ROOTS):
        sys.stderr.write(
            f"{what} {path!r} is not a checkout of this repository: expected "
            + " and ".join(f"{f}.lean" for f in ROOTS) + f" under {real}.\n"
            "Create the base with `git worktree add /tmp/<dir> <sha>`.\n")
        sys.exit(2)
    return real


def site_map(found: dict[str, list[tuple[str, int]]]) -> dict[str, dict[str, list[int]]]:
    """`name -> file -> sorted lines`, which is `candidates()` regrouped and nothing more."""
    out: dict[str, dict[str, list[int]]] = {}
    for name, sites in found.items():
        per = out.setdefault(name, {})
        for path, line in sites:
            per.setdefault(path, []).append(line)
    for per in out.values():
        for lines in per.values():
            lines.sort()
    return out


def site_changes(base_found: dict[str, list[tuple[str, int]]],
                 tree_found: dict[str, list[tuple[str, int]]]
                 ) -> tuple[dict[str, list[tuple[str, int, int]]],
                            dict[str, list[tuple[str, int]]],
                            dict[str, list[tuple[str, int]]]]:
    """Where every occurrence sits, compared per name **and per file**.

    Returns `(moved, added, removed)`, each keyed by file.  A name keeps its count in a file, so
    its lines pair up in order and each changed pair is a *move* — that is the common case, since
    inserting a line shifts every citation below it by the same amount.  When the count in that
    file changes, the lines are reported as added and removed instead and no pairing is guessed:
    a name that gains an occurrence *and* shifts in the same file shows up as several additions
    and removals rather than as one gain plus some moves, and saying so is cheaper than a
    heuristic that would be wrong somewhere.  Keying by file keeps a gain in one file from
    disturbing the pairing in another.

    **That difference is a multiset difference and not a set one**, because `candidates()`
    returns one entry per *occurrence*: a name backticked twice on one line is two entries with
    the same line number, so under `set` a line that loses one of a pair cancels against itself
    and the whole report comes out empty — the same-tree output, on trees that differ.  Five
    lines on `master` carry a name twice, so it is not hypothetical.  `Counter` is what keeps the
    promise the paragraph above makes.
    """
    before, after = site_map(base_found), site_map(tree_found)
    moved: dict[str, list[tuple[str, int, int]]] = {}
    added: dict[str, list[tuple[str, int]]] = {}
    removed: dict[str, list[tuple[str, int]]] = {}
    for name in sorted(set(before) | set(after)):
        per_before, per_after = before.get(name, {}), after.get(name, {})
        for path in sorted(set(per_before) | set(per_after)):
            was, now = per_before.get(path, []), per_after.get(path, [])
            if was == now:
                continue
            if len(was) == len(now):
                for old_line, new_line in zip(was, now):
                    if old_line != new_line:
                        moved.setdefault(path, []).append((name, old_line, new_line))
            else:
                was_at, now_at = collections.Counter(was), collections.Counter(now)
                for line in sorted((was_at - now_at).elements()):
                    removed.setdefault(path, []).append((name, line))
                for line in sorted((now_at - was_at).elements()):
                    added.setdefault(path, []).append((name, line))
    return moved, added, removed


def print_sites(moved: dict[str, list[tuple[str, int, int]]],
                added: dict[str, list[tuple[str, int]]],
                removed: dict[str, list[tuple[str, int]]]) -> None:
    """The `--sites` half of the report: every occurrence that is not where it was.

    Grouped by file, with each file's line named once, because a one-line insertion moves every
    citation below it and the interesting thing is then the *shape* — one file, one delta — and
    not the list.  The list is printed anyway and nothing is truncated: a report that silently
    caps reads as "that was all of it".
    """
    files = sorted(set(moved) | set(added) | set(removed))
    total_moved = sum(len(v) for v in moved.values())
    total_added = sum(len(v) for v in added.values())
    total_removed = sum(len(v) for v in removed.values())
    print(f"sites {total_moved} moved, {total_added} added, {total_removed} removed, "
          f"in {len(files)} file(s)")
    if not files:
        print("  (none)")
    for path in files:
        deltas = {new - old for _, old, new in moved.get(path, [])}
        shape = f"{len(moved.get(path, []))} moved"
        if len(deltas) == 1:
            shape += f", all {next(iter(deltas)):+d}"
        elif deltas:
            shape += f", deltas {min(deltas):+d}..{max(deltas):+d}"
        for label, count in (("added", len(added.get(path, []))),
                             ("removed", len(removed.get(path, [])))):
            if count:
                shape += f", {count} {label}"
        print(f"  {path} \u2014 {shape}")
        for name, old_line, new_line in sorted(moved.get(path, []), key=lambda s: s[1]):
            print(f"    ~ {old_line} \u2192 {new_line} ({new_line - old_line:+d})\t{name}")
        for name, line in sorted(added.get(path, []), key=lambda s: s[1]):
            print(f"    + {line}\t{name}")
        for name, line in sorted(removed.get(path, []), key=lambda s: s[1]):
            print(f"    - {line}\t{name}")


def diff_trees(base: str, tree: str, sites: bool = False) -> int:
    """Print the added and removed *distinct* candidate names between two checkouts.

    Both trees are scanned by this file's rules; see the module docstring for why, and for what
    that hides.  This is a reporter and not a gate — `scripts/guard_coverage.py` is the model —
    so it exits 0 whatever the diff is.  A removal is not by itself a defect: a name leaves the
    set when the last docstring citing it is reworded, which is what most prose commits do.

    With `sites`, the per-occurrence report follows; see the module docstring for the branch that
    needs it.  The summary above it is unchanged, so a body that quotes the two figures reads the
    same with the flag and without.
    """
    base_found = candidates(base)
    tree_found = candidates(tree)
    added = sorted(set(tree_found) - set(base_found))
    removed = sorted(set(base_found) - set(tree_found))
    print("base   " + report(base, base_found))
    print("branch " + report(tree, tree_found))
    print(f"distinct {len(base_found)} \u2192 {len(tree_found)}: "
          f"{len(added)} added, {len(removed)} removed")
    for label, names, where in (("added", added, tree_found), ("removed", removed, base_found)):
        print(f"{label}:")
        if not names:
            print("  (none)")
        for name in names:
            path, line = where[name][0]
            extra = f" (+{len(where[name]) - 1} more)" if len(where[name]) > 1 else ""
            print(f"  {name}\t{path}:{line}{extra}")
    if sites:
        print_sites(*site_changes(base_found, tree_found))
    return 0


def self_test() -> int:
    """Plant two fixture trees that differ and assert the diff names the difference.

    **The test that matters is the positive one.**  "Two identical trees diff to empty" is what
    the `os.chdir` driver this option replaced printed on every branch it was ever run on, so a
    self-test built only from that would have passed while measuring nothing.  **Every check below
    carries a `positive:` or `negative:` label and there are twelve and four** — a count is stated
    here rather than left to be inferred because a reader who trusts the labels has to be able to
    see that none is missing.

    The last four are about the *rules* rather than about the walk, and they reach them by
    planting an environment as a `--dump` file instead of building one.  That is the only way to
    hold everything fixed but the environment, which is the variable the field-notation rule turns
    on, and it keeps the whole self-test free of `lake`.
    """
    def plant(root: str, body: str) -> str:
        os.makedirs(os.path.join(root, "Oka"), exist_ok=True)
        os.makedirs(os.path.join(root, "OkaTest"), exist_ok=True)
        for f in ("Oka.lean", "OkaTest.lean"):
            with open(os.path.join(root, f), "w", encoding="utf-8") as h:
                h.write("import Oka.Fixture\n")
        with open(os.path.join(root, "Oka", "Fixture.lean"), "w", encoding="utf-8") as h:
            h.write(body)
        return root

    failures: list[str] = []

    def check(label: str, ok: bool, detail: str = "") -> None:
        print(f"{'ok  ' if ok else 'FAIL'} {label}" + (f" \u2014 {detail}" if detail else ""))
        if not ok:
            failures.append(label)

    with tempfile.TemporaryDirectory(prefix="oka-docstring-names-selftest-") as tmp:
        shared = "/-! `Shared.one` and `Shared.one` again, plus `Shared.two`. -/\n"
        a = plant(os.path.join(tmp, "a"), shared + "/-- `Only.inA` -/\ndef f := 1\n")
        b = plant(os.path.join(tmp, "b"), shared + "/-- `Only.inB` -/\ndef f := 1\n")

        ca, cb = candidates(a), candidates(b)

        # POSITIVE control, and the only one the broken driver fails.  Both trees are scanned in
        # one process, which is exactly what `os.chdir` could not make happen.
        # Note the two counts are *equal* here, on purpose: a driver that compares only the
        # `M distinct` figures passes a pair of trees whose name sets differ.
        check("positive: two trees scanned in one process differ", set(ca) != set(cb),
              f"{len(ca)} vs {len(cb)} distinct, and the sets differ")
        check("positive: the added name is the one planted",
              sorted(set(cb) - set(ca)) == ["Only.inB"], str(sorted(set(cb) - set(ca))))
        check("positive: the removed name is the one planted",
              sorted(set(ca) - set(cb)) == ["Only.inA"], str(sorted(set(ca) - set(cb))))

        # Negative control.  Stated as such: the driver this replaced passed this one too.
        check("negative: a tree against itself diffs to empty",
              set(ca) == set(candidates(a)))

        # The defect itself, asserted rather than described: `os.chdir` does not move the walk,
        # because `REPO` is bound at import from `__file__`.  This is the one check that scans
        # the real tree, and it is why the parameter above had to exist.
        cwd = os.getcwd()
        try:
            os.chdir(a)
            check("negative: `os.chdir` does not move the walk (the defect this option fixes)",
                  set(candidates()) != set(ca) and set(candidates()) == set(candidates(REPO)),
                  f"{len(candidates())} distinct from {REPO} while cwd is the fixture")
        finally:
            os.chdir(cwd)

        # Occurrences are counted per site, distinct names once.  The headline's two figures.
        check("positive: occurrences count every site", len(ca.get("Shared.one", [])) == 2,
              str(ca.get("Shared.one")))
        check("positive: `Shared.two` is one occurrence", len(ca.get("Shared.two", [])) == 1)

        # The case `--sites` exists for, and the one every other check here is blind to: a tree
        # with a line inserted above the citations.  Identical name sets, identical occurrence
        # counts, every moved site at the same delta.  The assertion is on the *set* of deltas
        # and not on a number of moves: `shared` carries three citations, so the number here is
        # four, and a number written down would go stale the next time a fixture gains a name.
        # A same-tree comparison returns nothing, which is what makes this a positive control
        # rather than a restatement of "two trees differ".
        d = plant(os.path.join(tmp, "d"), "/-! spacer -/\n" + shared
                  + "/-- `Only.inA` -/\ndef f := 1\n")
        cd = candidates(d)
        moved, gained, lost = site_changes(ca, cd)
        same = site_changes(ca, ca)
        check("positive: a line inserted above a citation moves its site and nothing else",
              set(ca) == set(cd)
              and sum(len(v) for v in ca.values()) == sum(len(v) for v in cd.values())
              and not gained and not lost
              and {n - o for sites in moved.values() for _, o, n in sites} == {1}
              and same == ({}, {}, {}),
              f"{sum(len(v) for v in moved.values())} moved, "
              f"{len(gained)} added, {len(lost)} removed; same-tree {same}")

        # The other way a site report can go silent, and it is the one `set` made it go silent
        # *by construction*: two citations of one name on one line are two entries with the same
        # line number, so dropping one of them cancels under a set difference.  Here the name
        # sets are identical, the occurrence totals differ by one, and the honest answer is one
        # removed site — which the pairing branch never sees, because the counts are unequal.
        e = plant(os.path.join(tmp, "e"), "/-! `Dup.name` and `Dup.name` again. -/\n")
        g = plant(os.path.join(tmp, "g"), "/-! `Dup.name` once. -/\n")
        ce, cg = candidates(e), candidates(g)
        dropped = site_changes(ce, cg)
        check("positive: dropping one of two citations of a name on one line is a removed site",
              set(ce) == set(cg)
              and sum(len(v) for v in ce.values()) - sum(len(v) for v in cg.values()) == 1
              and dropped == ({}, {}, {"Oka/Fixture.lean": [("Dup.name", 1)]})
              and site_changes(ce, ce) == ({}, {}, {}),
              f"{sum(len(v) for v in ce.values())} → "
              f"{sum(len(v) for v in cg.values())} occurrences; {dropped[2]}")

        # Candidacy is a property of comment regions, so code is not scanned.
        c = plant(os.path.join(tmp, "c"), "/-! nothing here -/\ndef g := `NotA.candidate\n")
        check("negative: a backtick outside a comment is not a candidate",
              "NotA.candidate" not in candidates(c), str(sorted(candidates(c))))

        # The CLI itself, end to end, because a recipe that is quoted has to be executable as
        # printed.  `--diff` must not need a build.
        proc = subprocess.run(
            [sys.executable, os.path.abspath(__file__), "--diff", a, "--tree", b],
            capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        check("positive: the CLI runs `--diff` with no build and reports the added name",
              proc.returncode == 0 and "Only.inB" in proc.stdout,
              proc.stdout.strip().replace("\n", " | ") or proc.stderr.strip())

        bad = subprocess.run(
            [sys.executable, os.path.abspath(__file__), "--diff",
             os.path.join(tmp, "does-not-exist")],
            capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        check("positive: a path that is not a checkout is reported, not a traceback",
              bad.returncode == 2 and "Traceback" not in bad.stderr
              and "is not a checkout" in bad.stderr,
              bad.stderr.strip().replace("\n", " | ") or f"rc={bad.returncode}")

        # The field-notation rule, against a *planted environment* rather than the real one.
        # `--dump` is what makes this possible without a build: the four runs below differ only
        # in which names the environment contains, which is exactly the variable under test.
        h = plant(os.path.join(tmp, "h"), "/-! `Planted.someField` -/\n")

        def env(name: str, *names: str) -> str:
            path = os.path.join(tmp, name)
            with open(path, "w", encoding="utf-8") as f:
                f.write("".join(n + "\n" for n in names))
            return path

        def run_on(dump: str) -> subprocess.CompletedProcess:
            return subprocess.run(
                [sys.executable, os.path.abspath(__file__), "--tree", h, "--dump", dump],
                capture_output=True, text=True,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))

        # The control: `Planted` resolves and has nothing under it, so `Planted.someField` is
        # field notation on a definition and is accepted.  Without this the two checks after it
        # could both pass on a script that accepts everything.
        bare = run_on(env("env-bare.txt", "Planted", "Unrelated.decl"))
        check("positive: field notation on a definition with no children is accepted",
              bare.returncode == 0 and "names nothing" not in bare.stdout,
              bare.stdout.strip().replace("\n", " | "))

        # **The defect.**  A tactic in some other file unfolds `Planted`, Lean plants its equation
        # lemma, and the citation above — untouched, in a file nobody edited — starts failing.
        # This is the check that fails on the un-fixed script, where it exits 1.
        eqn = run_on(env("env-eq.txt", "Planted", "Planted.eq_1", "Planted._proof_1",
                         "Unrelated.decl"))
        check("positive: a generated equation lemma does not make its definition a namespace",
              eqn.returncode == 0 and "names nothing" not in eqn.stdout,
              eqn.stdout.strip().replace("\n", " | ") or "rc=0, nothing reported")

        # The half of the rule that must survive the fix, and would not survive deleting the
        # namespace condition: an author-written declaration under the head still means the head
        # is a namespace and `Planted.someField` is a misspelling rather than field notation.
        real = run_on(env("env-real.txt", "Planted", "Planted.realChild", "Unrelated.decl"))
        check("negative: a declaration an author wrote still blocks field notation",
              real.returncode == 1 and "`Planted.someField` names nothing" in real.stdout,
              real.stdout.strip().replace("\n", " | ") or f"rc={real.returncode}")

        # And the message says *why*, naming both the head and the declaration that made it a
        # namespace — the two facts whose absence made the first instance of this defect take a
        # session to diagnose, and the reason a suffix missing from `GENERATED_COMPONENT` is a
        # one-line fix rather than another one.
        check("positive: the message names the head that resolves and what made it a namespace",
              "`Planted` does resolve" in real.stdout
              and "`Planted.realChild` makes it a namespace" in real.stdout,
              real.stdout.strip().replace("\n", " | "))

    if failures:
        print(f"\n{len(failures)} check(s) failed: " + ", ".join(failures))
        return 2
    print("\nself-test passed.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Check that backticked dotted names in comments resolve.")
    ap.add_argument("--dump", metavar="FILE",
                    help="reuse a name dump written earlier instead of building one")
    ap.add_argument("--tree", metavar="DIR", default=REPO,
                    help="the checkout to read, defaulting to the one this script lives in")
    ap.add_argument("--diff", metavar="BASE_DIR",
                    help="report the distinct-name diff from BASE_DIR to --tree, and stop; "
                         "reads no environment, so no build is needed")
    ap.add_argument("--sites", action="store_true",
                    help="with --diff, also report every occurrence that moved, by file:line; "
                         "this is the only report a branch that only rewords can move")
    ap.add_argument("--self-test", action="store_true",
                    help="plant two fixture trees that differ and assert the diff sees it")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    repo = check_tree(args.tree, "--tree")
    if args.diff:
        return diff_trees(check_tree(args.diff, "--diff"), repo, sites=args.sites)
    if args.sites:
        sys.stderr.write("--sites reports where occurrences moved between two trees, so it needs "
                         "--diff BASE_DIR to have a second tree to move them from.\n")
        sys.exit(2)

    found = candidates(repo)
    # Every proper prefix of every candidate is a possible head for the field-notation rule, and
    # has to be classified as resolving-or-not and as a namespace-or-not just as candidates do.
    wanted = set(found)
    heads = set()
    for name in found:
        parts = name.split(".")
        for k in range(1, len(parts)):
            heads.add(".".join(parts[:k]))
    wanted |= heads

    dump = args.dump or build_dump(repo)
    resolved, namespaces, root_namespaces, namespace_cause, dumped = scan(dump, wanted, heads)
    if not args.dump:
        os.unlink(dump)

    def is_field_notation(name: str) -> bool:
        parts = name.split(".")
        for k in range(len(parts) - 1, 0, -1):
            head = ".".join(parts[:k])
            if head in resolved and head not in namespaces:
                return True
        return False

    def blocked_head(name: str) -> tuple[str, str] | None:
        """The head that resolves but is a namespace, so field notation was not tried on it.

        The one thing a reader of a finding cannot see from the message alone.  A head that
        resolves is a head the prose is probably right about, and *why* the rule declined it is
        a fact about some other declaration entirely — see `scan`.
        """
        parts = name.split(".")
        for k in range(len(parts) - 1, 0, -1):
            head = ".".join(parts[:k])
            if head in resolved and head in namespaces:
                return head, namespace_cause.get(head, "another declaration under it")
        return None

    def is_local_binder(name: str) -> bool:
        head = name.split(".")[0]
        return len(head) <= MAX_LOCAL_HEAD and head not in root_namespaces

    ignored = read_ignore(repo)
    findings = [
        name for name in sorted(found)
        if name not in resolved
        and name not in ignored
        and not is_local_binder(name)
        and not os.path.exists(os.path.join(repo, name))
        and not is_field_notation(name)
    ]

    for name in findings:
        for (path, line) in found[name]:
            print(f"{path}:{line}: `{name}` names nothing in the environment")
        blocked = blocked_head(name)
        if blocked:
            head, cause = blocked
            print(f"    `{head}` does resolve, so this would be read as field notation, but "
                  f"`{cause}` makes it a namespace and the field-notation rule does not apply "
                  f"to namespaces")

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

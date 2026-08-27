#!/usr/bin/env python3
"""Report which declarations a module docstring advertises as main results and nothing guards.

`OkaTest/Axioms/` is this repository's regression test that the library rests only on `propext`,
`Classical.choice` and `Quot.sound`.  `OkaTest/Axioms.lean` states a **placement** rule — which
file, which heading — and says nothing about which declarations ought to be guarded, so a reader
is entitled to think the guards are complete.  They are not, nothing measured how incomplete, and
this is the measurement.

Usage:

    python3 scripts/guard_coverage.py                 # the report
    python3 scripts/guard_coverage.py --cone          # ...split by what a guard already reaches
    python3 scripts/guard_coverage.py --by-file       # ...with every gap listed by file
    python3 scripts/guard_coverage.py --self-test
    python3 scripts/guard_coverage.py --dump FILE     # reuse a declaration dump
    python3 scripts/guard_coverage.py --cone FILE     # ...and a `DumpGuardCone` dump
    python3 scripts/guard_coverage.py --env-dump FILE # ...and reconcile against `DumpEnvNames`

It runs `lake env lean scripts/DumpOkaDecls.lean` unless `--dump` is given, and
`scripts/DumpGuardCone.lean` when `--cone` is given without a file, so the build must have run
first: it reads the oleans, it does not produce them.

## `--cone`, and why the bare figure is the wrong one to act on

**`#print axioms` is transitive.**  A `sorry` anywhere below a guarded theorem turns *that*
theorem's guard red, so a declaration in the cone of some guard is already covered by the
regression test and a second `#print axioms` naming it would fail at exactly the same times.
Without `--cone` this script counts *advertised results with no guard of their own*, which is a
larger and much less interesting set: at `d12d334` it was **301 in 84 files, of which 259 were in
some guard's cone and 42, in 29 files, were reached by nothing at all.**

So the bare number has no right value — two tranches and three sessions declined to say what it
should be — while `reached by no guard at all` has an obvious one, namely zero, because such a
result is one no regression test touches.  `OkaTest/Axioms.lean` carries the two probes that
establish the difference is real rather than a property of this script's arithmetic.

**Even so this is a reporter and not a gate, and it must not be wired into
`.orchestra/validation.sh`.**  The uncovered figure is zero today and the way it stops being zero
is a pull request that advertises a result — an ordinary and desirable thing to do, which no
author should meet as a red build in a script they have never run.  `scripts/import_cost.py` is
the model, and its docstring gives the reason in a sentence: *"the cost itself is output, not a
verdict, because the figures live in English prose and nothing can check them mechanically."*
Exit is 0 whatever the coverage is, and non-zero only when an argument is wrong, a dump cannot
be built, or the self-test fails.

## The defect this exists to stop

`ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` was added to `Oka/AnalyticSpace/Sigma.lean`'s
`## Main results` by lana-agents/oka#191 — which was itself taking a reviewer's note that the list
was missing it — **without the matching guard**, and the two lists then disagreed by exactly one
entry.  It was caught by a reviewer reading both lists by eye, routed to taxis #1051 and fixed in
lana-agents/oka#194.  Nothing mechanical would have caught it.  The argument that settled it was a
precedent inside the same guard file: `ComplexAnalytic.AnalyticSpace.ι_glueMorphisms` was already
guarded and stands to `glueMorphisms` exactly as `sigmaι_sigmaDesc` stands to `sigmaDesc`.  That
is a good argument about one declaration and it does not scale.

## What is counted, and it is not what a prefix test would count

*Guarded* is a `#print axioms <name>` command under `OkaTest/Axioms/`, with comments masked.
*Advertised* is a backticked token inside a section of a **module** docstring under `Oka/` whose
heading begins `Main`, kept when it names a declaration this repository owns.

**Any heading beginning `Main`, and not the exact string `## Main results`** — which is a
correction to what this script did until 2026-08-27, and it was worth 238 declarations.  This
repository writes `## Main results` 109 times, `## Main definitions` 74 times and
`## Main declarations` once; Mathlib uses at least ten spellings, including
`## Main definitions and results` and `## Main statements`.  Whether an author reached for
*results* or *definitions* is not a fact about whether a declaration is announced, so a
denominator that turns on it cannot be quoted.  `report` prints the spellings it saw, with
counts, so that an eleventh is announced rather than swallowed.

Ownership is read from `scripts/DumpOkaDecls.lean`, which asks Lean which module declared each
constant.  A prefix test on the name would be wrong in both directions: this repository declares
into `AlgebraicGeometry`, `CategoryTheory` and `Polynomial` from its mirror tree — those names
have nothing beginning with `Oka` about them — and a `Main …` section may cite a Mathlib
declaration in a namespace this repository also declares into.  So `AlgebraicGeometry.…` alone
decides nothing, and the dump is what separates the two.

## Six things it cannot see, in decreasing order of how much they matter

* **A main result named in prose and not backticked is invisible**, so the *advertised* figure is
  a lower bound on what the docstrings claim.  `Oka/Weierstrass.lean`'s `localweierstrass_division`
  is backticked and guarded and so lands in the overlap; a result described in words is not
  counted at all.
* **Without `--cone` it has no opinion about whether a name ought to be guarded**, and the file
  that used to be the example of why — `Oka/Analytic/ParametricCircleIntegral.lean`, general
  complex analysis with a Mathlib destination, 17 of 17 advertised results unguarded — is the
  example of what `--cone` answers instead: sixteen of the seventeen are in the cone of the
  three `OkaTest/Axioms/Weierstrass.lean` guards, because that file exists to prove the two
  lemmas `Oka/Weierstrass.lean` consumes.  It needed one guard, not seventeen and not an
  exclusion.  With `--cone` the judgement left over is genuinely small; see `OkaTest/Axioms.lean`.
* **A guard can move a name out of the uncovered column without naming it**, since it brings its
  whole cone with it.  Guarding the 42 of `d12d334` took 41 guards: `MvPolynomial.awayBaseHom`
  is in the cone of `MvPolynomial.isLocalization_away_quotient_awayIdeal`, which was itself one
  of the 42.  Do not read a delta in this figure as a count of guards added.
* **A cone membership is weaker than a guard and this script cannot see the difference.**  A
  guard on `f` holds whatever else changes; `f`'s membership of `g`'s cone lasts exactly as long
  as `g`'s proof mentions `f`, so a refactor of `g` can end it in silence.  What makes that
  tolerable is that nothing is recorded: re-run this and a name that has dropped out of every
  cone is back in the uncovered column.
* **The reverse direction is not a defect.**  A guard on a lemma no docstring advertises is fine
  and there are many; the count is printed because it is the other half of the divergence, not
  because anything should be done about it.
* **A `Main …` list can advertise a declaration that lives in another file.**  That is
  legitimate — a file may be the natural place to announce a result it re-exports — and the
  report says how many such entries there are rather than treating them as errors.

## Why the instrument gets its own self-test

`scripts/import_cost.py` records that the obvious instrument for *its* question "was written
wrong twice, by two different agents, and both wrong figures passed the project's standard
validation."  This is the same species: a count over docstrings, produced once, quoted afterwards
in prose that nothing checks.  The failure that actually happened here is on this issue's own
thread — the first version of taxis #1057 gave five figures that were all correct about the tree
they were taken on, which was the filer's branch and not `master`.  **A number can be right and
its description wrong**, and no self-test can catch that one; what `--self-test` does catch is the
extraction, which is the part with a wrong answer that looks like a right one.

Both halves are pinned with a control, so neither check can go vacuous: the masking fixture
asserts that the unmasked regex *does* find the thing masking removes, and the module-docstring
fixture asserts that the same text in a `/--` declaration docstring is *not* read as a list of
main results.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DUMP_SCRIPT = os.path.join("scripts", "DumpOkaDecls.lean")
CONE_SCRIPT = os.path.join("scripts", "DumpGuardCone.lean")
LIBRARY_DIR = "Oka"
GUARD_DIR = os.path.join("OkaTest", "Axioms")

# What every guard in this repository asserts, and so what the cone of all of them must contain
# and nothing more.  A fourth axiom here is either a regression or, far more likely, a traversal
# in `DumpGuardCone.lean` that is not the one `#print axioms` performs.
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

PRINT_AXIOMS = re.compile(r"^[ \t]*#print axioms(?:[ \t]+|[ \t]*\n[ \t]+)(\S+)[ \t]*$", re.M)
PRINT_AXIOMS_CMD = re.compile(r"^[ \t]*#print axioms\b", re.M)
BACKTICKED = re.compile(r"`([^`\s]+)`")
MAIN_HEADING = re.compile(r"^#{1,6}\s+Main\b.*$")
HEADING = re.compile(r"^#{1,6}\s")


def strip_comments(text: str) -> str:
    """`text` with comment *contents* removed and newlines kept.

    Block comments nest, and `/-!` and `/--` open one like any other `/-`; line comments run to
    the end of the line.  Without this a `#print axioms` shown inside a docstring — which is how
    one would document the convention — would be counted as a guard.
    """
    out: list[str] = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
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


def module_docstrings(text: str) -> list[tuple[int, str]]:
    """`(offset, contents)` for every `/-! … -/` region, nesting as Lean's comments do.

    Declaration docstrings (`/-- … -/`) and plain comments are deliberately not returned: a
    `## Main results` heading is a module-docstring convention, and a `/--` on a declaration that
    happened to contain one would otherwise be read as a second list.
    """
    out: list[tuple[int, str]] = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if text.startswith("/-", i):
            module = text.startswith("/-!", i)
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
            end = j - 2 if depth == 0 else n
            if module:
                out.append((start, text[start:end]))
            i = j
            continue
        if text[i] == '"':
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
            continue
        i += 1
    return out


def main_results_tokens(text: str) -> list[tuple[str, int]]:
    """Every backticked token inside a `## Main results` section of a module docstring.

    A section runs from its heading to the next heading of any level or to the end of the
    docstring, so a `## What is not here` list — which on this project cites the names of things
    that are *absent* — cannot leak into the count.

    *Its* heading is anything beginning `Main`, not the exact string `## Main results`.  Under
    the narrow reading this repository advertised 521 declarations at `d12d334` and the 74
    `## Main definitions` and one `## Main declarations` sections were invisible, worth 238 more
    declarations of which 151 had no guard; Mathlib uses at least ten spellings of the heading,
    `## Main definitions and results` and `## Main statements` among them.  A denominator that
    depends on which of those an author picked is not a denominator, so `report` prints the
    spellings it saw — a new one is then announced rather than silently swallowed.
    """
    out: list[tuple[str, int]] = []
    for offset, body in module_docstrings(text):
        pos = 0
        inside = False
        for line in body.splitlines(keepends=True):
            if MAIN_HEADING.match(line):
                inside = True
            elif HEADING.match(line):
                inside = False
            elif inside:
                for m in BACKTICKED.finditer(line):
                    at = offset + pos + m.start()
                    out.append((m.group(1), text.count("\n", 0, at) + 1))
            pos += len(line)
    return out


def main_headings(text: str) -> list[str]:
    """The `Main …` headings of `text`'s module docstrings, as written."""
    return [line.strip() for _, body in module_docstrings(text)
            for line in body.splitlines() if MAIN_HEADING.match(line)]


def guarded_names(text: str) -> list[tuple[str, int]]:
    """Every `#print axioms <name>` in `text`, comments masked.

    The name may be on the line after the command: one guard in this repository is
    `#print axioms` followed by an indented 100-character name, because that is what fits.  **The
    obvious line regex misses it**, and both instruments that have counted these guards missed it
    — at `0b19eb1` the count was reported as 471, in the issue that asked for this script and
    again in this script's first draft, and it was 472.  `guard_count` is the tripwire that
    would have said so.
    """
    masked = strip_comments(text)
    return [(m.group(1), masked.count("\n", 0, m.start()) + 1)
            for m in PRINT_AXIOMS.finditer(masked)]


def guard_count(text: str) -> int:
    """How many `#print axioms` commands `text` has, however their argument is laid out.

    Compared against `len(guarded_names(text))` by the caller, so that a layout this file does not
    parse is reported rather than silently dropped.  A count and an extraction that disagree is
    the only way an instrument like this one can say *"there is something here I did not read"*.
    """
    return len(PRINT_AXIOMS_CMD.findall(strip_comments(text)))


def lean_files(*roots: str) -> list[str]:
    """Every `.lean` file under `roots`, repository-relative and sorted."""
    paths: list[str] = []
    for root in roots:
        for dirpath, _, filenames in os.walk(os.path.join(REPO, root)):
            paths += [os.path.relpath(os.path.join(dirpath, f), REPO)
                      for f in filenames if f.endswith(".lean")]
    return sorted(paths)


def read_decls(dump: str) -> dict[str, str]:
    """`name -> declaring module`, from `scripts/DumpOkaDecls.lean`'s output."""
    decls: dict[str, str] = {}
    with open(dump, encoding="utf-8") as f:
        for line in f:
            module, _, name = line.rstrip("\n").partition("\t")
            if name:
                decls[name] = module
    return decls


def read_env(dump: str) -> set[str]:
    """Every name in `scripts/DumpEnvNames.lean`'s output — the whole environment, Mathlib too."""
    with open(dump, encoding="utf-8") as f:
        return {line.rstrip("\n") for line in f if line.strip()}


def build_dump() -> str:
    """Run `scripts/DumpOkaDecls.lean` and return the path it wrote."""
    fd, path = tempfile.mkstemp(prefix="oka-decls-", suffix=".txt")
    os.close(fd)
    proc = subprocess.run(
        ["lake", "env", "lean", DUMP_SCRIPT], cwd=REPO,
        env=dict(os.environ, OKA_DECL_DUMP=path), capture_output=True, text=True,
    )
    if proc.returncode != 0 or not os.path.getsize(path):
        sys.stderr.write(proc.stdout + proc.stderr)
        sys.stderr.write(
            "\nFailed to dump the declarations of `Oka` + `OkaTest`. `lake build` must have run\n"
            "first: this reads the oleans, it does not produce them.\n"
        )
        os.unlink(path)
        sys.exit(2)
    return path


def read_cone(dump: str) -> tuple[set[str], set[str], list[str], list[str]]:
    """`(cone, axioms, missing roots, unreadable rows)`, from `scripts/DumpGuardCone.lean`.

    The fourth component is the tripwire, and it is the same one `guard_count` is: a row this
    reader does not understand is *reported* rather than dropped, so that a change to the Lean
    side which this side has not been taught cannot look like a smaller cone.
    """
    cone: set[str] = set()
    axioms: set[str] = set()
    missing: list[str] = []
    unread: list[str] = []
    with open(dump, encoding="utf-8") as f:
        for line in f:
            row = line.rstrip("\n")
            if not row:
                continue
            tag, _, name = row.partition("\t")
            if tag == "cone" and name:
                cone.add(name)
            elif tag == "axiom" and name:
                axioms.add(name)
            elif tag == "missing" and name:
                missing.append(name)
            else:
                unread.append(row)
    return cone, axioms, missing, unread


def build_cone(roots: list[str]) -> str:
    """Run `scripts/DumpGuardCone.lean` on `roots` and return the path it wrote."""
    fd, roots_path = tempfile.mkstemp(prefix="oka-guard-roots-", suffix=".txt")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        f.write("".join(name + "\n" for name in sorted(roots)))
    fd, path = tempfile.mkstemp(prefix="oka-guard-cone-", suffix=".txt")
    os.close(fd)
    proc = subprocess.run(
        ["lake", "env", "lean", CONE_SCRIPT], cwd=REPO,
        env=dict(os.environ, OKA_CONE_ROOTS=roots_path, OKA_CONE_OUT=path),
        capture_output=True, text=True,
    )
    os.unlink(roots_path)
    if proc.returncode != 0 or not os.path.getsize(path):
        sys.stderr.write(proc.stdout + proc.stderr)
        sys.stderr.write(
            "\nFailed to dump the axiom cone of the guards. `lake build` must have run first:\n"
            "this reads the oleans, it does not produce them.\n"
        )
        os.unlink(path)
        sys.exit(2)
    return path


def module_of(path: str) -> str:
    """`Oka/Foo/Bar.lean` -> `Oka.Foo.Bar`."""
    return path[:-len(".lean")].replace(os.sep, ".")


def report(decls: dict[str, str], env: set[str] | None, by_file: bool,
           cone_arg: str | None = None) -> None:
    guarded: dict[str, str] = {}
    unread: list[tuple[str, int, int]] = []
    for path in lean_files(GUARD_DIR):
        with open(os.path.join(REPO, path), encoding="utf-8") as f:
            text = f.read()
        found = guarded_names(text)
        for name, _ in found:
            guarded[name] = path
        if len(found) != guard_count(text):
            unread.append((path, guard_count(text), len(found)))

    cone: set[str] | None = None
    axioms: set[str] = set()
    cone_missing: list[str] = []
    cone_unread: list[str] = []
    if cone_arg is not None:
        cone_dump = cone_arg or build_cone(sorted(guarded))
        try:
            cone, axioms, cone_missing, cone_unread = read_cone(cone_dump)
        finally:
            if not cone_arg:
                os.unlink(cone_dump)

    advertised: dict[str, set[str]] = {}
    foreign: dict[str, int] = {"module": 0, "Mathlib": 0, "other": 0}
    unresolved: list[tuple[str, str, int]] = []
    unresolved_all: list[tuple[str, str, int]] = []
    modules = {module_of(p) for p in lean_files(LIBRARY_DIR, "OkaTest")} | {"Oka", "OkaTest"}
    spellings: dict[str, int] = {}
    for path in lean_files(LIBRARY_DIR) + ["Oka.lean"]:
        with open(os.path.join(REPO, path), encoding="utf-8") as f:
            text = f.read()
        for heading in main_headings(text):
            spellings[heading] = spellings.get(heading, 0) + 1
        for token, line in main_results_tokens(text):
            if token in decls:
                advertised.setdefault(path, set()).add(token)
                continue
            unresolved_all.append((token, path, line))
            if token in modules:
                foreign["module"] += 1
            elif token.startswith("Mathlib.") or (env is not None and token in env):
                foreign["Mathlib"] += 1
            else:
                foreign["other"] += 1
                unresolved.append((token, path, line))

    names = {n for ns in advertised.values() for n in ns}
    unguarded = names - set(guarded)
    covered = {n for n in unguarded if n in cone} if cone is not None else set()
    uncovered = unguarded - covered
    gaps = {path: sorted(ns - set(guarded)) for path, ns in advertised.items()}
    gaps = {path: ns for path, ns in gaps.items() if ns}
    holes = {path: [n for n in ns if n in uncovered] for path, ns in gaps.items()}
    holes = {path: ns for path, ns in holes.items() if ns}
    elsewhere = sum(1 for path, ns in advertised.items() for n in ns
                    if decls[n] != module_of(path))

    print(f"guards under {GUARD_DIR}/            {len(guarded)} distinct names, "
          f"{len(lean_files(GUARD_DIR))} files")
    print(f"advertised under a `Main …` heading {len(names)} distinct declarations of this "
          f"repository, in {len(advertised)} files")
    for heading, count in sorted(spellings.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"    {count:3d}  {heading}")
    print(f"  of those, unguarded               {len(unguarded)}"
          f" ({100 * len(unguarded) // max(len(names), 1)}%), in {len(gaps)} files")
    if cone is not None:
        print(f"    already in a guard's cone       {len(covered)}"
              "  (`#print axioms` is transitive)")
        print(f"    reached by no guard at all      {len(uncovered)}, in {len(holes)} files")
    print(f"  in both lists                     {len(names) - len(unguarded)}")
    print(f"guarded and advertised nowhere      {len(set(guarded) - names)}"
          "  (not a defect — see this script's docstring)")
    print(f"advertised from another file        {elsewhere}")
    suffixes: dict[str, set[str]] = {}
    for name in decls:
        parts = name.split(".")
        for i in range(1, len(parts)):
            suffixes.setdefault(".".join(parts[i:]), set()).add(name)
    abbreviated = sorted({t for t, _, _ in unresolved_all if t in suffixes})
    dotted = [t for t in abbreviated if "." in t]
    print(f"abbreviated citations, not counted  {len(abbreviated)}"
          f" ({len(dotted)} of them dotted) — so the figure above is a lower bound")
    if by_file:
        for token in abbreviated:
            owners = sorted(suffixes[token])
            print(f"      `{token}` -> {owners[0]}"
                  f"{f'  (ambiguous, {len(owners)} declarations)' if len(owners) > 1 else ''}")
    print(f"backticked tokens skipped           {foreign['module']} repository module name(s), "
          f"{foreign['Mathlib']} name(s) this repository does not declare, "
          f"{foreign['other']} that resolve to nothing")
    if env is None and foreign["other"]:
        print("  (without --env-dump the last two cannot be told apart for a name outside the\n"
              "   `Mathlib.` namespace; the count above is an upper bound on real typos)")
    for token, path, line in unresolved if env is not None else []:
        print(f"      {path}:{line}: `{token}`")
    for path, commands, read in unread:
        print(f"  !! {path}: {commands} `#print axioms` command(s), {read} name(s) read — "
              "a layout this script does not parse")
    if cone is not None:
        extra = sorted(axioms - STANDARD_AXIOMS)
        print(f"axioms reached from every guard     {len(axioms)}"
              f"{' — the three standard ones' if not extra else ''}")
        for name in extra:
            print(f"  !! {name}: an axiom no guard's `#guard_msgs` records — see "
                  f"{CONE_SCRIPT}")
        for name in cone_missing:
            print(f"  !! {name}: guarded, and not a declaration in this environment")
        for row in cone_unread:
            print(f"  !! a row of the cone dump this script cannot read: {row!r}")

    guards_outside = sorted(set(guarded) - set(decls))
    if guards_outside:
        print(f"guards on declarations this repository does not own: {len(guards_outside)}")
        for name in guards_outside:
            print(f"      {name}  ({guarded[name]})")

    print()
    if cone is None:
        print("largest gaps (unguarded / advertised):")
        order = sorted(gaps, key=lambda p: (-len(gaps[p]), p))
        for path in order if by_file else order[:12]:
            print(f"  {len(gaps[path]):3d} / {len(advertised[path]):-3d}  {path}")
            if by_file:
                for name in gaps[path]:
                    print(f"           {name}")
        if not by_file and len(order) > 12:
            print(f"  ({len(order) - 12} more files with a gap; --by-file lists every one)")
        return

    # With a cone in hand the interesting order is by what nothing reaches, not by what has no
    # guard of its own: a file all of whose advertised results sit under a guard downstream is
    # not a gap in any sense a regression test cares about, and 41 of the 60 are exactly that.
    if not holes:
        print("No advertised result is outside every guard's cone — the figure that has a right"
              f" value,\nat it.  The {len(covered)} above have no guard of their own and, while"
              " the proofs that reach\nthem stay as they are, need none.")
        return
    print("reached by no guard (uncovered / in a cone / advertised):")
    order = sorted(holes, key=lambda p: (-len(holes[p]), p))
    for path in order if by_file else order[:12]:
        print(f"  {len(holes[path]):3d} / {len(gaps[path]) - len(holes[path]):-3d} /"
              f" {len(advertised[path]):-3d}  {path}")
        if by_file:
            for name in gaps[path]:
                print(f"      {'!!' if name in uncovered else '  '}     {name}")
    if not by_file and len(order) > 12:
        print(f"  ({len(order) - 12} more files with an uncovered result; --by-file lists all)")
    silent = sorted(p for p in gaps if p not in holes)
    print(f"  ({len(silent)} further files have an unguarded advertised result and no uncovered"
          " one)")
    if by_file:
        for path in silent:
            print(f"    {len(gaps[path]):3d} in a cone  {path}")


def self_test() -> int:
    failures = 0

    def check(name: str, got: object, want: object) -> None:
        nonlocal failures
        ok = got == want
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: got {got!r}, want {want!r}")
        failures += not ok

    # The fixture taxis #1057 asks for: a guarded name, an unguarded name, a repository module
    # name and a `Mathlib.` name, in one `## Main results` block.
    fixture = (
        "/-!\n# A file\n\n## Main results\n\n"
        "- `Oka.Guarded.thm` and `Oka.Unguarded.thm`, proved from `Mathlib.Order.Basic`'s\n"
        "  machinery; see `Oka.Weierstrass`.\n\n"
        "## What is not here\n\n- `Oka.Absent.thm`, which nothing proves.\n-/\n"
        "/-- `Oka.NotAMainResult.thm` is only a declaration docstring.\n\n"
        "## Main results\n\n- `Oka.AlsoNotOne.thm`\n-/\ntheorem foo : True := trivial\n"
    )
    check("every backticked token of the `## Main results` block, and only those",
          [t for t, _ in main_results_tokens(fixture)],
          ["Oka.Guarded.thm", "Oka.Unguarded.thm", "Mathlib.Order.Basic", "Oka.Weierstrass"])
    decls = {"Oka.Guarded.thm": "Oka.A", "Oka.Unguarded.thm": "Oka.B", "Oka.Absent.thm": "Oka.C"}
    check("...of which two are declarations of this repository",
          sorted({t for t, _ in main_results_tokens(fixture) if t in decls}),
          ["Oka.Guarded.thm", "Oka.Unguarded.thm"])
    check("a `## What is not here` name is not advertised, though it is a declaration",
          "Oka.Absent.thm" in [t for t, _ in main_results_tokens(fixture)], False)
    check("a `## Main results` inside a `/--` docstring is not a list of main results",
          [t for t in ["Oka.NotAMainResult.thm", "Oka.AlsoNotOne.thm"]
           if t in [x for x, _ in main_results_tokens(fixture)]], [])
    check("...and the same text opened with `/-!` is, so the control is not vacuous",
          [t for t, _ in main_results_tokens(
              "/-!\n## Main results\n\n- `Oka.AlsoNotOne.thm`\n-/\n")],
          ["Oka.AlsoNotOne.thm"])

    # The heading is anything beginning `Main`.  Until 2026-08-27 it was the exact string
    # `## Main results`, which missed 74 `## Main definitions` sections in this repository and
    # would miss `## Main definitions and results`, a spelling Mathlib uses twelve times.
    for heading in ["## Main results", "## Main definitions", "## Main declarations",
                    "## Main definitions and results", "### Main statements", "## Main Results"]:
        check(f"`{heading}` opens a section",
              [t for t, _ in main_results_tokens(f"/-!\n{heading}\n\n- `Oka.In.thm`\n-/")],
              ["Oka.In.thm"])
    # ...and the control, since a prefix test rather than a word boundary would swallow these.
    check("a heading that merely starts with the letters of `Main` does not",
          ([t for t, _ in main_results_tokens("/-!\n## Maintenance\n\n- `Oka.Out.thm`\n-/")],
           [t for t, _ in main_results_tokens("/-!\n## Mainly plumbing\n\n- `Oka.Out.thm`\n-/")],
           [t for t, _ in main_results_tokens("/-!\n## Main\n\n- `Oka.In.thm`\n-/")]),
          ([], [], ["Oka.In.thm"]))
    check("the spellings are reported as written, so an unseen one is announced",
          main_headings("/-!\n## Main results\n\n- `a`\n\n## Other\n\n## Main definitions\n-/"),
          ["## Main results", "## Main definitions"])

    # A heading of a different level closes the section too; `Oka/` uses `##` throughout today,
    # and a file that used `###` for its subsections would otherwise leak them into the count.
    check("a deeper heading closes the section",
          [t for t, _ in main_results_tokens(
              "/-!\n## Main results\n\n- `Oka.In.thm`\n\n### A digression\n\n- `Oka.Out.thm`\n-/")],
          ["Oka.In.thm"])

    # Masking, with its control.  A `#print axioms` shown inside a docstring is how one documents
    # the convention, and `OkaTest/Axioms.lean` does exactly that in prose.
    guards = ("/-- info: 'A.b' depends on axioms: [propext] -/\n#guard_msgs in\n"
              "#print axioms A.b\n/-!\nRun `#print axioms C.d` yourself.\n"
              "\n    #print axioms E.f\n-/\n")
    check("a guard inside a docstring is not counted",
          [n for n, _ in guarded_names(guards)], ["A.b"])
    check("...and the unmasked regex does count it, so the fixture is not vacuous",
          PRINT_AXIOMS.findall(guards), ["A.b", "E.f"])
    check("a nested block comment closes correctly",
          [n for n, _ in guarded_names("/- a /- b -/ c -/\n#print axioms I.j\n")], ["I.j"])
    # A line comment is *not* an argument for the masking: `PRINT_AXIOMS` anchors at the start of
    # a line, so `-- #print axioms` never matched.  Indentation is allowed, though, and the two
    # differ by two characters — so both directions are pinned rather than one asserted.
    check("a line comment cannot fake a guard, masked or not",
          ([n for n, _ in guarded_names("-- #print axioms G.h\n")],
           PRINT_AXIOMS.findall("-- #print axioms G.h\n")), ([], []))
    check("...while an indented guard outside a comment is one",
          [n for n, _ in guarded_names("  #print axioms K.l\n")], ["K.l"])

    # The instance in this tree, and the reason the count was 471 twice: one name is 100
    # characters and does not fit after the command.
    wrapped = ("#guard_msgs (whitespace := lax) in\n#print axioms\n"
               "  A.very.long.name_of_isCoherent\n")
    check("a guard whose name is on the next line is read",
          [n for n, _ in guarded_names(wrapped)], ["A.very.long.name_of_isCoherent"])
    check("...and the same text read as one line per guard misses it, which is the defect",
          re.findall(r"^[ \t]*#print axioms[ \t]+(\S+)[ \t]*$", wrapped, re.M), [])
    # The tripwire, fired on a layout deliberately outside what `PRINT_AXIOMS` accepts.  A check
    # that has only ever been seen to pass is not evidence.
    check("a layout the extraction cannot read is counted and reported, not dropped",
          (guard_count("#print axioms\n\nM.n\n"),
           len(guarded_names("#print axioms\n\nM.n\n"))), (1, 0))
    check("...and the two agree on a layout it can read",
          (guard_count(wrapped), len(guarded_names(wrapped))), (1, 1))

    # The cone reader.  Written to a file rather than parsed from a string because that is what
    # it reads, and a reader tested on a different input than it consumes is not tested.
    fd, cone_path = tempfile.mkstemp(prefix="oka-guard-cone-fixture-", suffix=".txt")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        f.write("cone\tOka.Guarded.thm\naxiom\tpropext\nmissing\tOka.Vanished.thm\n"
                "cone\tOka.Unguarded.thm\n\nbadtag\tOka.Confusing.thm\ncone\n")
    try:
        got_cone, got_axioms, got_missing, got_unread = read_cone(cone_path)
    finally:
        os.unlink(cone_path)
    check("the cone dump's three row kinds are read into three buckets",
          (sorted(got_cone), sorted(got_axioms), got_missing),
          (["Oka.Guarded.thm", "Oka.Unguarded.thm"], ["propext"], ["Oka.Vanished.thm"]))
    check("a row kind this reader does not know is reported, not dropped",
          got_unread, ["badtag\tOka.Confusing.thm", "cone"])
    # The control on the classification itself.  `covered` and `uncovered` are a set difference
    # in `report`, so what is worth pinning is that a name absent from the dump lands in the
    # second bucket rather than nowhere — the failure that would make every gap look closed.
    unguarded_fixture = {"Oka.Unguarded.thm", "Oka.NotInAnyCone.thm"}
    check("an advertised name absent from the cone is uncovered, not silently dropped",
          (sorted(n for n in unguarded_fixture if n in got_cone),
           sorted(n for n in unguarded_fixture if n not in got_cone)),
          (["Oka.Unguarded.thm"], ["Oka.NotInAnyCone.thm"]))
    check("an axiom outside the three every guard records is reported",
          sorted({"propext", "sorryAx"} - STANDARD_AXIOMS), ["sorryAx"])

    print("self-test FAILED" if failures else "self-test passed")
    return 1 if failures else 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Report the declarations advertised as main results that nothing guards.")
    ap.add_argument("--dump", metavar="FILE",
                    help="reuse a `scripts/DumpOkaDecls.lean` dump instead of building one")
    ap.add_argument("--env-dump", metavar="FILE",
                    help="a `scripts/DumpEnvNames.lean` dump, to tell a Mathlib name from a typo")
    ap.add_argument("--by-file", action="store_true",
                    help="list every file with a gap, and every unguarded name in it")
    ap.add_argument("--cone", metavar="FILE", nargs="?", const="", default=None,
                    help="split the unguarded names by whether some guard's `#print axioms` "
                         "already reaches them; runs `scripts/DumpGuardCone.lean` unless a dump "
                         "of its output is given")
    ap.add_argument("--self-test", action="store_true", help="check the extraction on fixtures")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    dump = args.dump or build_dump()
    try:
        report(read_decls(dump), read_env(args.env_dump) if args.env_dump else None, args.by_file,
               args.cone)
    finally:
        if not args.dump:
            os.unlink(dump)
    return 0


if __name__ == "__main__":
    sys.exit(main())

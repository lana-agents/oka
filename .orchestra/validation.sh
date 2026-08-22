#!/usr/bin/env bash
# Validation for the `oka` repository. Run it from anywhere:
#
#   bash .orchestra/validation.sh
#
# `.github/workflows/lean_action_ci.yml` runs the same checks in CI and the two must be kept in
# step; if you add a check here, add it there. What "lint" means is defined once, as
# `lintDriver` in `lakefile.toml`, so that at least that much cannot drift.
#
# Exits 0 only if every check below passes; the first failing check stops the script and
# exits non-zero.

set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

# Verify the worktree is clean.
if [ -n "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  git status --short
  exit 1
fi

# Verify the library is free of `sorry`. This runs before the build because it is instant and
# the build is not; it is a fast fail, not the only defence. **`lake build --wfail` below does
# catch a `sorry`** — measured 2026-08-20 by planting one under `OkaTest/` and watching
# `declaration uses \`sorry\`` become `error: build failed` — so the test library, which this
# grep does not cover, is not unguarded. (This comment previously said the build "would not fail
# on it", which is true of a bare `lake build` and false with `--wfail`.)
#
# Until 2026-08-20 that was true of this script and **not** of CI, which called
# `leanprover/lean-action` without `build-args` and so ran a bare `lake build`. CI now passes
# `--wfail` too; if the two ever diverge again, every build linter silently becomes
# local-only.
#
# The negative lookarounds keep `sorryAx`, `unsorry` and `sorry_foo` from matching. The bare word
# *does* match in comments and docstrings, so prose under `Oka/` should avoid it. This mirrors
# the check in `.github/workflows/lean_action_ci.yml`.
if grep -rnP '(?<![A-Za-z_])sorry(?![A-Za-z_])' --include='*.lean' Oka Oka.lean; then
  echo 'Found a `sorry` in the library, at the location(s) listed above.'
  exit 1
fi

# Fetch build cache. Needed before the two steps below, both of which build Mathlib
# artifacts.
lake exe cache get || exit 1

# Verify all .lean files are imported by the root module `Oka.lean`.
lake exe mk_all --lib Oka --git --check || exit 1

# The same for the test library and `OkaTest.lean`. The test library used to be a glob with no
# root module, which is why `lake exe lint-style` below could not be pointed at it: that
# executable takes module names, so a library with no root is unreachable and `OkaTest/` was
# text-linted by nothing at all. The root exists to close that, and this check is what keeps it
# honest — without it a new test file would silently drop out of `lint-style`'s reach while
# still being built, since every `OkaTest.+` module is its own build target.
#
# Regenerate with `lake exe mk_all --lib OkaTest --git` rather than editing `OkaTest.lean`.
lake exe mk_all --lib OkaTest --git --check || exit 1

# Verify everything builds, and that it builds without warnings.
lake build --wfail || exit 1

# Verify Mathlib's environment linters are clean. These check the whole environment, not one
# file: missing docstrings on definitions, names that break the naming convention, `@[simp]`
# lemmas whose left-hand side is not in `simp` normal form, and about ten more. `lake build`
# sees none of it, which is how the project reached 2026-08-20 with 19 findings nobody had
# looked at.
#
# The linter and the module it runs on are configured once, as `lintDriver` in `lakefile.toml`,
# so that this script and the CI workflow cannot disagree about what "lint" means. Note that
# `#lint` in a scratch file that does nothing but `import Oka` is NOT a substitute: it only
# lints the current file's declarations and reports a green on an environment full of findings.
#
# Needs the oleans, so it has to come after the build; given those it takes a few seconds.
lake lint || exit 1

# Verify Mathlib's text-based style linter is clean. Until now it was enforced by nothing at
# all, despite being quoted in every pull request description on this project.
#
# It checks *less* than its name suggests. As of this Mathlib the whole list is: trailing
# whitespace, a space before a semicolon, Windows line endings, disallowed unicode and variant
# selectors, the string "Adaptation note", and module-name casing. Line length and copyright
# headers are *build* linters, caught by `lake build --wfail` above via
# `weak.linter.mathlibStandardSet`. Do not read a green `lint-style` as "Mathlib style has been
# checked"; it is disjoint from, and much narrower than, the environment linters.
#
# Both library root modules. `OkaTest` was absent here until 2026-08-20, not by choice but
# because `lake exe lint-style Oka OkaTest` failed with `no such file OkaTest.lean` — the test
# library had no root module — so half the tree was text-linted by nothing while every pull
# request quoted a green `lint-style` as evidence that style had been checked. The root module
# added above is what makes this line possible; the `mk_all --lib OkaTest` check above is what
# stops it from silently going stale again.
#
# The `nolints file could not be read` warning is harmless and always present.
lake exe lint-style Oka OkaTest || exit 1

# Verify that every backticked dotted name in a comment or docstring resolves to something.
#
# Nothing above looks inside a comment. `lake build --wfail` sees only elaborated terms, `lake
# lint` checks declaration *names*, `lint-style` checks whitespace and line length, `mk_all
# --check` checks imports, and the declaration-name diff that every pull request body runs
# compares declarations rather than the prose citing them. A backticked name in a `/-- … -/`
# block that names nothing at all passed every one of them until this line existed, and on
# 2026-08-20/21 that cost four separate findings in one day, each caught by a human who happened
# to be reading the file for another reason.
#
# `scripts/check_docstring_names.py` documents its own rules; the short version is that it is
# deliberately permissive — a name resolves if *any* declaration in the environment ends with
# it, or it is a module, or a file in the repository, or field notation — because a check that
# cries wolf is worse than none on a project that quotes a green `validation.sh` as evidence in
# every pull request body. `scripts/docstring-names-ignore.txt` is the escape hatch and is
# empty; prefer fixing a rule to growing it.
#
# It runs `lake env lean scripts/DumpEnvNames.lean` to read the environment, so it has to come
# after the build; given the oleans it takes about ten seconds, nine of them the import. It
# needs `python3`, which is the only thing in this script that does.
python3 scripts/check_docstring_names.py || exit 1

echo "Validation succeeded."

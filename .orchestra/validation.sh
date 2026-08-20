#!/usr/bin/env bash
# Validation for the `oka` repository. Run it from anywhere:
#
#   bash .orchestra/validation.sh
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

# Verify the library is free of `sorry`. Lean reports one as a warning rather than an
# error, so the build below would not fail on it. The negative lookarounds keep
# `sorryAx`, `unsorry` and `sorry_foo` from matching. The bare word *does* match in
# comments and docstrings, so prose under `Oka/` should avoid it. This mirrors the check
# in `.github/workflows/lean_action_ci.yml`.
if grep -rnP '(?<![A-Za-z_])sorry(?![A-Za-z_])' --include='*.lean' Oka Oka.lean; then
  echo 'Found a `sorry` in the library, at the location(s) listed above.'
  exit 1
fi

# Fetch build cache. Needed before the two steps below, both of which build Mathlib
# artifacts.
lake exe cache get || exit 1

# Verify all .lean files are imported by the root module `Oka.lean`.
lake exe mk_all --lib Oka --git --check || exit 1

# Verify everything builds, and that it builds without warnings.
lake build --wfail || exit 1

# Verify Mathlib's environment linters are clean. These check the whole environment, not one
# file: missing docstrings on definitions, names that break the naming convention, `@[simp]`
# lemmas whose left-hand side is not in `simp` normal form, and about ten more. `lake build`
# sees none of it, which is how the project reached 2026-08-20 with 19 findings nobody had
# looked at. Two things worth knowing before editing this line:
#
#   * the argument is the library *root module* `Oka`, not `Oka OkaTest`. The test library has
#     no root module, the same reason `lake exe lint-style Oka OkaTest` fails.
#   * `#lint` in a scratch file that does nothing but `import Oka` is NOT a substitute: it only
#     lints the current file's declarations and reports a green on an environment full of
#     findings.
#
# Needs the oleans, so it has to come after the build; given those it takes a few seconds.
lake exe batteries/runLinter Oka || exit 1

echo "Validation succeeded."

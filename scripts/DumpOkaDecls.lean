/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest

/-!
# Declaration dump with declaring modules, for `scripts/guard_coverage.py`

Writes every non-internal constant declared by a module of this repository — a module whose name
starts with `Oka` or `OkaTest` — as `module<TAB>name`, one per line, to the file named by the
environment variable `OKA_DECL_DUMP` (default `oka-decls.txt` in the working directory).

## Why this is not `scripts/DumpEnvNames.lean`

That file answers *"is this backticked token a name at all?"* and so dumps the whole environment,
Mathlib included, with no module attached. This one answers *"which declarations does this
repository own, and where does each one live?"*, which needs the module and needs Mathlib
excluded. Both questions have a consumer and neither dump can be derived from the other: adding a
module column to `DumpEnvNames.lean`'s output would change every line of a file
`scripts/check_docstring_names.py` reads as one name per line.

The declaring module is read from `env.header.moduleData`, which is the module's own list of the
constants it adds, rather than from a name prefix. A prefix test would be wrong in both
directions here: this repository declares into `AlgebraicGeometry`, `CategoryTheory` and
`Polynomial` from its mirror tree, and Mathlib declares into none of the namespaces that start
with `Oka`.

This file is deliberately **not** part of either library, for the same reason
`scripts/DumpEnvNames.lean` is not: it is run with `lake env lean` against the oleans the build
has already produced, and is reachable from neither `Oka.lean` nor `OkaTest.lean`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let path := (← IO.getEnv "OKA_DECL_DUMP").getD "oka-decls.txt"
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if (`Oka).isPrefixOf m || (`OkaTest).isPrefixOf m then
      for n in env.header.moduleData[i]!.constNames do
        unless n.isInternal do
          h.putStrLn s!"{m}\t{n}"

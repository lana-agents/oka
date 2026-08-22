/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest

/-!
# Environment name dump, for `scripts/check_docstring_names.py`

Writes every non-internal constant name and every imported module name in the environment of
`Oka` + `OkaTest`, one per line, to the file named by the environment variable
`OKA_ENV_NAME_DUMP` (default `env-names.txt` in the working directory).

This file is deliberately **not** part of either library: it is run with `lake env lean`, so it
is compiled fresh each time against the oleans the build has already produced, and it is not
reachable from `Oka.lean` or `OkaTest.lean`. Adding it to a library would make every build
elaborate a file whose only purpose is to write a temporary file.

Module names are dumped alongside constants because docstrings on this project cite modules —
`Oka.Weierstrass`, `Mathlib.RingTheory.Filtration` — in exactly the same backticked form as
declarations, and a checker that knew only about constants would report all of them.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let path := (← IO.getEnv "OKA_ENV_NAME_DUMP").getD "env-names.txt"
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for m in env.header.moduleNames do
    h.putStrLn m.toString
  for (n, _) in env.constants.toList do
    unless n.isInternal do
      h.putStrLn n.toString

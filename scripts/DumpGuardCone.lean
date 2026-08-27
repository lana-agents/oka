/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest

/-!
# The axiom cone of a set of guards, for `scripts/guard_coverage.py`

Reads a list of declaration names — in practice the names some `#print axioms` under
`OkaTest/Axioms/` guards — from the file named by `OKA_CONE_ROOTS` (default `guard-roots.txt`),
and writes to the file named by `OKA_CONE_OUT` (default `guard-cone.txt`) a two-column report:

    cone<TAB>Name      -- a constant of this repository that some root's `#print axioms` visits
    axiom<TAB>Name     -- an axiom reached from some root
    missing<TAB>Name   -- a root that is not a declaration in this environment

## The question it answers, which is not the one `guard_coverage.py` asked on its own

`#print axioms` is **transitive**: it reports the axioms of everything the named declaration's
proof term mentions, transitively, so a `sorry` anywhere below a guarded theorem turns that
theorem's guard red. A declaration in the cone of a guard is therefore already covered by the
regression test the guards exist to be, and a second `#print axioms` naming it directly would
fail at exactly the same times.

That distinction is what separates *this advertised result has no guard of its own* — which is
what `guard_coverage.py` counts, and which was read for two tranches as the size of the gap —
from *a `sorry` here would be caught by nothing*, which is the property anybody actually wants.
The two differ by a factor of five on this repository.

**A cone membership is weaker than a guard, and the difference is not academic.** A guard on `f`
keeps holding whatever else changes; `f`'s membership of `g`'s cone lasts exactly as long as
`g`'s proof goes on mentioning `f`. Refactor `g` and `f` can leave the cone in silence. What
makes that tolerable is that this is a *measurement* and is re-run: the file to which a name
belongs is not consulted anywhere, so a name that drops out of every cone reappears in
`guard_coverage.py --cone`'s uncovered column on the next run.

## Why the traversal is spelled out rather than delegated

`Lean.collectAxioms` computes exactly this reachability and then throws away everything except
the axioms. There is no version of it that keeps the visited set, so the traversal is written
out below — and it is written to be *the same traversal*, case for case: an `axiomInfo` is
recorded and its type visited, a `quotInfo` stops, a constructor and a recursor contribute
their type only, an inductive contributes its type and its constructors, and a definition, a
theorem and an `opaque` contribute type and value. A traversal that differed anywhere would
answer a question no `#print axioms` asks.

The first of those cases is the one worth checking against `Lean/Util/CollectAxioms.lean` rather
than against intuition: an axiom is a leaf of the *proof*, not of the traversal, and Lean does
descend into its type. On this repository the distinction is inert — replacing that case by
`pure ()` leaves the dump byte-identical, because the types of `propext`, `Classical.choice` and
`Quot.sound` mention nothing declared here — but it is inert only as a measured fact about this
tree, and the direction it would fail in is under-visiting, which can only over-report the
uncovered column.

The `axiom` rows are the check on that: the union of the axioms reached from every guarded name
must be `propext`, `Classical.choice` and `Quot.sound` and nothing else, because each of those
names sits under a `#guard_msgs` that the build already holds to exactly that list. A row naming
a fourth axiom means either a regression the guards somehow missed or — far more likely — that
this traversal is not the one `#print axioms` performs.

Like `scripts/DumpOkaDecls.lean` and `scripts/DumpEnvNames.lean` this file is part of neither
library, is reachable from neither root module, and is run with `lake env lean` against oleans
the build has already produced: it reads them, it does not produce them.
-/

open Lean

namespace OkaGuardCone

/-- The constants `#print axioms` visits, accumulated rather than discarded.

Case for case `Lean.collectAxioms`' traversal; see this file's module docstring for why it is
written out and what the `axiom` rows of the output check about it. -/
partial def collect (env : Environment) (c : Name) : StateM NameSet Unit := do
  unless (← get).contains c do
    modify fun s => s.insert c
    let collectExpr (e : Expr) : StateM NameSet Unit := e.getUsedConstants.forM (collect env)
    match env.find? c with
    | some (.axiomInfo v)  => collectExpr v.type
    | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
    | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
    | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
    | some (.quotInfo _)   => pure ()
    | some (.ctorInfo v)   => collectExpr v.type
    | some (.recInfo v)    => collectExpr v.type
    | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM (collect env)
    | none                 => pure ()

end OkaGuardCone

open Elab Command in
run_cmd do
  let env ← getEnv
  let rootsPath := (← IO.getEnv "OKA_CONE_ROOTS").getD "guard-roots.txt"
  let outPath := (← IO.getEnv "OKA_CONE_OUT").getD "guard-cone.txt"
  let roots := (← IO.FS.lines rootsPath).filterMap fun line =>
    let line := line.trimAscii
    if line.isEmpty then none else some line.toName
  let cone := ((roots.forM (OkaGuardCone.collect env)).run {}).2
  let h ← IO.FS.Handle.mk outPath IO.FS.Mode.write
  for r in roots do
    if (env.find? r).isNone then h.putStrLn s!"missing\t{r}"
  for c in cone.toList do
    if let some (.axiomInfo _) := env.find? c then h.putStrLn s!"axiom\t{c}"
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if (`Oka).isPrefixOf m || (`OkaTest).isPrefixOf m then
      for c in env.header.moduleData[i]!.constNames do
        if cone.contains c then
          h.putStrLn s!"cone\t{c}"

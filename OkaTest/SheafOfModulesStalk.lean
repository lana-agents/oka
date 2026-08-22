/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Algebra.Category.ModuleCat.Sheaf.Stalk
import Oka.AnalyticSpace.Relations

/-!
# `SheafOfModules.exact_of_stalk_exact` applies to the sheaves this development has

`Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean` is general theory with no consumer yet — its
consumer is the exactness half of GAGA. The risk with a general lemma is not that it is
degenerate but that it is **inapplicable**: it is stated for a sheaf of rings over
`Opens.grothendieckTopology X` with `X : TopCat`, and every sheaf of rings in this development
comes from `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`, whose site is spelled
`Opens.grothendieckTopology ↑Y.toPresheafedSpace`.

**The two spellings do not agree, and which one is passed matters.** These tests record that:

* with `TopCat.of ↑Y.toPresheafedSpace` the lemma applies — this is the first `example`;
* with `Y.toTopCat` it does not. The statement elaborates and then instance search fails to
  find `CategoryTheory.Functor.PreservesZeroMorphisms` for the stalk functor, which is the same
  discrimination-tree seam `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`'s docstring records
  for `Opens.map`. That failure is recorded here in prose rather than as a `#guard_msgs`,
  because it is a statement that does not elaborate rather than one that produces a message.

The second `example` instantiates at `complexSpace`, so that the applicability
is on record for the structure sheaf this development actually uses rather than only for a
variable.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

/-- The exactness criterion applies to sheaves of modules over the structure sheaf of any
locally ringed space, with the site spelled as `ringSheaf` spells it. -/
example (Y : LocallyRingedSpace.{u}) (S : ShortComplex (SheafOfModules.{u} Y.ringSheaf))
    (h : ∀ x : TopCat.of ↑Y.toPresheafedSpace,
      (S.map (SheafOfModules.stalkFunctor (X := TopCat.of ↑Y.toPresheafedSpace) x)).Exact) :
    S.Exact :=
  SheafOfModules.exact_of_stalk_exact S h

/-- The same at `ℂ^ι`, whose structure sheaf is the one the analytification comparison morphism
is about. -/
example (ι : Type u) [Fintype ι]
    (S : ShortComplex (SheafOfModules.{u} (complexSpace ι).ringSheaf))
    (h : ∀ x : TopCat.of ↑(complexSpace ι).toPresheafedSpace,
      (S.map (SheafOfModules.stalkFunctor
        (X := TopCat.of ↑(complexSpace ι).toPresheafedSpace) x)).Exact) :
    S.Exact :=
  SheafOfModules.exact_of_stalk_exact S h

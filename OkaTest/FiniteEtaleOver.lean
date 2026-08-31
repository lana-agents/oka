/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.FiniteMorphism

/-!
# Non-vacuity of the category of finite étale covers

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X` always has an object — the base over itself —
and that says nothing, because a category with one object and one morphism is a category. The
reading that would empty it is that **every** object is isomorphic to that one, in which case the
Riemann existence theorem would be about a point.

The witness below closes that at the punctured line, on the cover `z ↦ z²` that
`OkaTest/FiniteMorphism.lean` already built:

* `sqOver` is an object, by `ComplexAnalytic.isFiniteEtale_sq`;
* `not_iso_id_sqOver` says it is **not** isomorphic to
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id`, through
  `ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id` and `ComplexAnalytic.not_isIso_sq`.

So the category at that base has at least two isomorphism classes, and the object separating them
is a genuine two-sheeted cover rather than a formal one.

## What this does not witness

**Nothing about morphisms.** The category's morphisms are all morphisms over the base, and this
file exhibits none of them and computes no hom-set. In particular it says nothing about whether a
morphism between two objects is itself finite étale, which is the cancellation statement
`Oka/AnalyticSpace/FiniteEtaleOver.lean` names as absent.

**One collision met on the way, and it is recorded rather than fixed.** The base here has to be
spelled `ComplexAnalytic.punctured` and not `punctured`: `OkaTest/HolomorphicMapOpen.lean`
declares a root-namespace `punctured` and `OkaTest/FiniteMorphism.lean` declares
`ComplexAnalytic.punctured`, **both of them an `Opens` of
`ComplexAnalytic.AnalyticSpace.complexAffineSpace 1` and both of them `{z₀ ≠ 0}`** — one built as
a carrier with an openness proof, the other as
`ComplexAnalytic.AnalyticSpace.nonvanishing` of a coordinate — and each carries its own
`mem_punctured_iff`. Any file importing both meets an ambiguous term, which is what happened here.
That is a duplicate definition and not only a name clash, so which one survives is a decision this
branch does not take.

**Nothing about the trivial cover.** `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` at a
two-element index type is the other obvious second object, and separating *it* from the identity
needs a statement that `X ⨿ X ⟶ X` is not an isomorphism, which this repository does not have —
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` counts the fibres and nothing turns that into
a `¬ IsIso`. The witness here goes through a cover whose non-invertibility is already proved.
-/

open CategoryTheory ComplexAnalytic ComplexAnalytic.AnalyticSpace

universe u

noncomputable section

namespace OkaTest.FiniteEtaleOver

/-- **`z ↦ z²` on the punctured line, as an object of the category of finite étale covers.** -/
def sqOver : AnalyticSpace.FiniteEtaleOver.{u}
    ((AnalyticSpace.complexAffineSpace.{u} 1).restrict ComplexAnalytic.punctured.{u}) :=
  MorphismProperty.Over.mk _ ComplexAnalytic.sq.{u} ComplexAnalytic.isFiniteEtale_sq.{u}

/-- **It is not isomorphic to the base over itself**, so the category has more than one
isomorphism class at this base.

`ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id` turns such an isomorphism into `IsIso` of the
structure map, which is `ComplexAnalytic.sq`, and `ComplexAnalytic.not_isIso_sq` is what refutes
that — the squaring map of the punctured line is not injective. -/
theorem not_iso_id_sqOver :
    IsEmpty (sqOver.{u} ≅ AnalyticSpace.FiniteEtaleOver.id.{u}
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict ComplexAnalytic.punctured.{u})) :=
  ⟨fun e ↦ ComplexAnalytic.not_isIso_sq.{u} (AnalyticSpace.isIso_hom_of_iso_id.{u} e)⟩

end OkaTest.FiniteEtaleOver

end

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

**And it has infinitely many**, which is the second half of this file and does not go through a
`¬ IsIso` at all: `pairwise_not_iso_trivial` says the trivial `n`-sheeted covers of the punctured
line are pairwise non-isomorphic, one class for every `n`, by
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_eq_of_iso_trivial`. `degree_sqOver` records
what the degree of the first witness is, and it is `2`.

## What this does not witness

**Nothing about morphisms.** The category's morphisms are all morphisms over the base, and this
file exhibits none of them and computes no hom-set. In particular it says nothing about whether a
morphism between two objects is itself finite étale, which is the cancellation statement
`Oka/AnalyticSpace/FiniteEtaleOver.lean` names as absent.

**One name that has to be qualified here, and the duplicate behind it is decided elsewhere.** The
base has to be spelled `ComplexAnalytic.punctured` and not `punctured`, because
`OkaTest/HolomorphicMapOpen.lean` declares a root-namespace `punctured` and
`OkaTest/FiniteMorphism.lean` declares `ComplexAnalytic.punctured`, **both of them an `Opens` of
`ComplexAnalytic.AnalyticSpace.complexAffineSpace 1` and both of them `{z₀ ≠ 0}`** — one built as
a carrier with an openness proof, the other as
`ComplexAnalytic.AnalyticSpace.nonvanishing` of a coordinate — so with `ComplexAnalytic` open the
bare name is ambiguous.

**That is where this file's part ends, and an earlier version of this paragraph did not say so.**
`OkaTest/FiniteMorphism.lean`, which this file imports, already records the duplicate at length,
already proves the two are the same open set — `ComplexAnalytic.punctured_eq_punctured`, which is
`TopologicalSpace.Opens.ext` over the two `mem_punctured_iff`s — and already **takes** the
decision this paragraph used to describe as untaken: both stand, because each has a use the other
cannot discharge, and the retirement is priced there at a rename across four files. Nothing here
reopens it.

**The trivial cover is separated now, and not by the route this paragraph priced it at.** It said
that separating `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` at a two-element index
type from the identity *"needs a statement that `X ⨿ X ⟶ X` is not an isomorphism, which this
repository does not have"*. **No such statement was needed and none was proved.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id` compares two numbers — the
degrees, `Nat.card ι` and `1` — and it reaches them through
`ComplexAnalytic.AnalyticSpace.degree_sigmaFold`, which is proved from
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold`: **the very fibre count this paragraph named
as the thing that led nowhere.** What was missing was not a `¬ IsIso` but the statement that the
degree is constant on isomorphism classes,
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`.

**What is still not here is a separation of `sqOver` from the trivial two-sheeted cover.** They
have the same degree — `degree_sqOver` is `2` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial` at a two-element index type is `2`
— so the invariant below cannot tell them apart. The classical argument is that one total space
is connected and the other is not, and **this repository has one half of it**:
`ComplexAnalytic.preconnectedSpace_restrict_punctured` (`OkaTest/FiniteMorphism.lean`) is an
instance, so the source of `sqOver` is preconnected, while nothing anywhere says the disjoint
union of two copies of it is not — `not_preconnectedSpace_puncturedNodeSpace`
(`OkaTest/OpenSubspace.lean`) is this repository's only `¬ PreconnectedSpace` and is about a
different space. **This file does not claim the two objects are non-isomorphic**, and no sentence
in it should be read as though it did.
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

/-- **The first witness has degree two.**

`ComplexAnalytic.degree_sq` (`OkaTest/FiniteMorphism.lean`) read through
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`, which is that degree by definition. It is
recorded because a degree that is never computed on a non-formal object says nothing, and because
it is what makes the `## What this does not witness` paragraph about `sqOver` and the trivial
two-sheeted cover a measurement rather than a worry. -/
theorem degree_sqOver :
    AnalyticSpace.FiniteEtaleOver.degree.{u} sqOver.{u} = 2 :=
  ComplexAnalytic.degree_sq.{u}

/-- **The trivial covers of the punctured line are pairwise non-isomorphic**, one isomorphism class
for every number of sheets.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_eq_of_iso_trivial` at
`ι = ULift (Fin m)` and `κ = ULift (Fin n)`, where `Nat.card` is `m` and `n`. So the category at
this base does not have finitely many isomorphism classes, which is strictly more than
`not_iso_id_sqOver` above says and is proved without refuting an `IsIso` of anything.

**The base is the punctured line only because it is the one already in front of this file.** The
statement asks nothing of it beyond `[Nonempty _]`, and holds over every non-empty analytic space
for the same reason. -/
theorem pairwise_not_iso_trivial {m n : ℕ} (h : m ≠ n) :
    IsEmpty (AnalyticSpace.FiniteEtaleOver.trivial.{u} (ULift.{u} (Fin m))
        ((AnalyticSpace.complexAffineSpace.{u} 1).restrict ComplexAnalytic.punctured.{u}) ≅
      AnalyticSpace.FiniteEtaleOver.trivial.{u} (ULift.{u} (Fin n))
        ((AnalyticSpace.complexAffineSpace.{u} 1).restrict ComplexAnalytic.punctured.{u})) :=
  ⟨fun e ↦ h (by
    have := AnalyticSpace.FiniteEtaleOver.card_eq_of_iso_trivial.{u} e
    simpa using this)⟩

end OkaTest.FiniteEtaleOver

end

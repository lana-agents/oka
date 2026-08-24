/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.AnalytificationDistinguishedOpen

/-!
# Non-vacuity of the functorial form of the distinguished-open projection

`ComplexAnalytic.analytificationMap_localisationPresHom` identifies a morphism produced by the
universal property with a morphism produced by the functor. Both readings of that which would
make it empty are about the *morphism of presentations*: that it might be the identity, and that
its analytification might be an isomorphism. The checks below close both, on the node with
`f = z₀`, reusing the point and the image `OkaTest/AnalytificationDistinguishedOpen.lean` already
computed.

* **It is not an identity, and cannot be**: the source presentation has three variables and two
  equations and the target has two and one, so the two objects of
  `ComplexAnalytic.Presentation` are different and `PresHom.id` does not typecheck at this type.
  That is recorded by `presentation_ne` rather than left to the reader.
* **Its analytification is not an isomorphism.**
  `nodeOrigin_notMem_range_analytificationMap` says the origin of the node is not in the image of
  the *functor's* value on the structure map — which is
  `nodeOrigin_notMem_range_base_localisationProj` read
  through the identification, and is the statement that matters: the functor does not send this
  non-isomorphism of algebras to an isomorphism of spaces.
* **So the structure map is not an isomorphism of `ℂ`-algebras**:
  `not_isIso_nodeStructureHom`, which is the bullet above read back through the functor. It is
  the algebra statement and not a categorical shadow of one — a morphism of
  `ComplexAnalytic.Presentation` is a ring map together with a proposition, so an inverse to it
  is a ring inverse fixing the constants — and it strengthens the first bullet, where an
  identity would in particular be an isomorphism.
* **And it does what it should on points**: `base_analytificationMap_nodeLocPoint` sends
  `(1, 0, 1)` to `axisPoint 0`, again through the identification.

**What is not checked.** `ComplexAnalytic.localisationPresentedAlgebraEquiv` identifies the
target of the structure map as a localisation of its source, and **nothing here uses it**: every
statement below is about `ComplexAnalytic.localisationPresentation nodePres nodeX` as a tuple of
polynomials, which is how `Oka/Analytification/LocalisationFunctor.lean` states them too, and only
an edit to this file can falsify it. The geometric statement stays the one the gluing construction
will consume; the algebra statement is its corollary and not the other way round.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.LocalisationFunctor

/-- The presentation of `ℂ[z₀, z₁] ⧸ (z₀z₁)`, as an object of `ComplexAnalytic.Presentation`. -/
abbrev nodeObj : Presentation.{u} := ⟨2, 1, nodePres.{u}⟩

/-- The presentation of its localisation at `z₀`. -/
abbrev nodeLocObj : Presentation.{u} :=
  ⟨3, 2, localisationPresentation.{u} nodePres.{u} nodeX.{u}⟩

/-- **The structure map `A ⟶ A_{z₀}`**, as a morphism of the two objects above.

`ComplexAnalytic.localisationPresHom` on its own does not elaborate against `IsIso`: the category
spells `Hom P Q` as `ComplexAnalytic.PresHom P.g Q.g`, and nothing recovers the two objects from
the bare term. -/
abbrev nodeStructureHom : nodeLocObj.{u} ⟶ nodeObj.{u} :=
  localisationPresHom.{u} nodePres.{u} nodeX.{u}

/-- **The two presentations are different objects**, so the morphism between them is not an
identity in disguise: adjoining an inverse adds a variable and an equation. -/
theorem presentation_ne : nodeLocObj.{u} ≠ nodeObj.{u} := by
  intro hcon
  exact absurd (congrArg Presentation.n hcon) (by decide)

/-- **The origin of the node is not in the image of the analytification of the structure map.**

This is the non-vacuity that matters: the functor's value on `A ⟶ A_{z₀}` is not an isomorphism,
and the witness is a point of the node at which `z₀` vanishes. -/
theorem nodeOrigin_notMem_range_analytificationMap :
    nodeOrigin.{u} ∉ Set.range
      (analytificationMap.{u} (localisationPresHom.{u} nodePres.{u} nodeX.{u})).toLRSHom.base := by
  rw [analytificationMap_localisationPresHom]
  exact nodeOrigin_notMem_range_base_localisationProj.{u}

/-- **The structure map is not an isomorphism of `ℂ`-algebras.**

`ComplexAnalytic.analytificationFunctor` sends an isomorphism to an isomorphism and an isomorphism
of locally ringed spaces is a homeomorphism on points, so an inverse would put `nodeOrigin` in the
range that `nodeOrigin_notMem_range_analytificationMap` keeps it out of. That is the whole proof;
nothing about localisation enters it.

The statement is the algebraic one because a morphism of `ComplexAnalytic.Presentation` is a ring
map together with a proposition — `ComplexAnalytic.PresHom.ext` is equality of the ring maps — so
an inverse to `nodeStructureHom` is a ring inverse fixing the constants. -/
theorem not_isIso_nodeStructureHom : ¬ IsIso nodeStructureHom.{u} := by
  intro h
  have : IsIso (AnalyticSpace.forgetToLocallyRingedSpace.{u}.map
      (analytificationFunctor.{u}.map nodeStructureHom.{u})) := inferInstance
  have hsurj := (LocallyRingedSpace.homeoOfIso (asIso
    (AnalyticSpace.forgetToLocallyRingedSpace.{u}.map
      (analytificationFunctor.{u}.map nodeStructureHom.{u})))).surjective
  exact nodeOrigin_notMem_range_analytificationMap.{u} (hsurj nodeOrigin.{u})

/-- **The analytification of the structure map sends `(1, 0, 1)` to `(1, 0)`**, so the morphism
the functor produces is the projection on points as well as in the abstract. -/
theorem base_analytificationMap_nodeLocPoint :
    (analytificationMap.{u} (localisationPresHom.{u} nodePres.{u} nodeX.{u})).toLRSHom.base
        nodeLocPoint.{u} =
      axisPoint.{u} (ULift.up 0) := by
  rw [analytificationMap_localisationPresHom]
  exact base_localisationProj_nodeLocPoint.{u}

end OkaTest.LocalisationFunctor

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.Comparison
import Oka.Analytification.LocalisationIndependence

/-!
# `Spec` of the structure map `A ⟶ A_f` is an open immersion

`Oka/Analytification/LocalisationFunctor.lean` proves the analytic half of this:
`ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom` says the *analytification*
of the structure map is an open immersion, and its docstring says why it is stated in that
spelling — a glue data assembled out of `ComplexAnalytic.analytificationFunctor` holds its
morphisms in that form, and `AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `f_open` field is
checked against the morphism one actually has.

This file is the same statement for `ComplexAnalytic.specFunctor`. It is what a glue data on the
`Spec` side of the same cover will hold, and that glue datum is the *target* of the comparison
morphism `X^an ⟶ X` for a glued scheme: `ComplexAnalytic.comm_coverGlueData` and
`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` already produce a morphism out of
`X^an` into **any** locally ringed space, so what is missing on that line is the space on the
right and not the gluing.

## The proof is a triangle over `A`, and the file exists for its two ends

`ComplexAnalytic.localisationPresentedAlgebraEquiv` identifies `ℂ[x, t] ⧸ (g, t·f - 1)` with
`Localization.Away (mk f)`, and
`ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` says that identification
is an isomorphism **over `A`** — the structure map composed with it is
the localisation's own `algebraMap`. Mathlib knows `Spec` of that `algebraMap` is an open
immersion. So the content here is one commuting triangle and one rewrite, and everything else is
where the two halves live: `ComplexAnalytic.specFunctor` is in
`Oka/Analytification/Comparison.lean` and the compatibility is in
`Oka/Analytification/LocalisationIndependence.lean`, and **no file in this repository imports
both**. Hence a file rather than a section.

## Mathlib's scheme-level open immersions are available to this repository's glue data, and that
is worth more than the lemma

`AlgebraicGeometry.Spec.locallyRingedSpaceMap` — the spelling `ComplexAnalytic.specFunctor` is
built from, because a `GlueData` here is a locally-ringed-space object — is the same term as
`AlgebraicGeometry.Spec.map`'s underlying morphism: `(Spec.map φ).toLRSHom =
Spec.locallyRingedSpaceMap φ` is `rfl`, and `AlgebraicGeometry.IsOpenImmersion` is
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` of that. So every open immersion Mathlib
proves about `Spec.map` is one about the morphisms this repository glues with.

**Instance search does not cross that identity**, which is why it has to be written down:
`inferInstance` at
`LocallyRingedSpace.IsOpenImmersion (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap R
(Localization.Away f))))` fails, while `inferInstanceAs` at the scheme-level spelling succeeds.
Measured 2026-08-30. `ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom` below is
that crossing at the one place this development needs it, and its proof term is the scheme-level
theorem with no transport at all.

## Why not `AlgebraicGeometry.IsOpenImmersion.of_isLocalization`

Mathlib has exactly this statement for any `[IsLocalization.Away f S]`, which would make the proof
one line. It is not used, and the reason is a decision `Oka/Analytification/DistinguishedOpen.lean`
argues for in its own docstring: there is deliberately **no** `IsLocalization.Away` instance, and
no `Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance, on the localised presented algebra
— the identification is an isomorphism a consumer applies, not an instance keyed on a type this
development uses everywhere. Going through `ComplexAnalytic.specLocalisationRingIso` respects that
and costs three lines.

## Main definitions

- `ComplexAnalytic.specLocalisationRingIso`: `ComplexAnalytic.localisationPresentedAlgebraEquiv`,
  as an isomorphism in `CommRingCat` — the form `AlgebraicGeometry.Spec.map` consumes.

## Main results

- `ComplexAnalytic.localisationRingHom_comp_eq`: **the triangle over `A`**, in `CommRingCat`:
  the structure map followed by the identification is the localisation's own structure map into
  `Localization.Away`.
- `ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom`: **`Spec` of the structure map
  `A ⟶ A_f` is an open immersion**, at the scheme-level spelling, which is where Mathlib's API is.
- `ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom`: the same for
  `ComplexAnalytic.specFunctor`'s value on the structure map — the spelling a glue data on the
  `Spec` side will hold, and the mirror of
  `ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom`. The morphism of
  presentations it is taken at is named in the declaration's own docstring rather than here:
  it is a definition, and `## Main results` is a list of results.

## What is not here

* **The range of the morphism**, in either spelling, so nothing here says *which* open subset it
  is. That is the next thing the `Spec`-side glue data needs and it is not one line:
  `Set.range (Spec.map …).base = ↑(PrimeSpectrum.basicOpen (mk f))` does not elaborate as stated,
  because the ambient types `↥(Spec (CommRingCat.of (PresentedAlgebra n k g)))` and
  `PrimeSpectrum ↑(CommRingCat.of (PresentedAlgebra n k g))` are definitionally equal but the
  `Opens → Set` coercion does not unify them; and Mathlib's idiomatic
  `AlgebraicGeometry.Scheme.Hom.opensRange`, whose `Scheme.Hom.opensRange_localizationAway` is
  exactly the statement wanted, is declared in a section with `[IsOpenImmersion f]` and therefore
  needs the result below as an *instance*, which is a decision about instance shape that a file
  with one consumer should not make on its own.
* **The `Spec`-side glue data, and the comparison morphism `X^an ⟶ X`.** This is `f_open` and
  nothing else. The `hrange` hypothesis that construction also needs is a statement about ranges
  of maps on points, and unlike the cocycle equation it does not transport along a functor.
* **Anything analytic.** No morphism of analytic spaces appears below, and nothing in
  `Oka/Analytification/AffineCover.lean` changes.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The identification of the localised presentation, in `CommRingCat` -/

/-- **`ComplexAnalytic.localisationPresentedAlgebraEquiv` as an isomorphism in `CommRingCat`**:
`ℂ[x, t] ⧸ (g, t·f - 1)` and `Localization.Away (mk f)` are the same object of the category
`AlgebraicGeometry.Spec.map` is a functor out of.

A `≃ₐ[ℂ]` cannot be handed to `AlgebraicGeometry.Spec.map`, and the two rewrites below are about
composites of `CommRingCat` morphisms, so the bundled form is what both of them need. -/
def specLocalisationRingIso :
    CommRingCat.of (PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f)) ≅
      CommRingCat.of (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f)) :=
  (localisationPresentedAlgebraEquiv.{u} g f).toRingEquiv.toCommRingCatIso

/-- **The triangle over `A`**: the structure map `A ⟶ A_f`, followed by the identification of
`A_f` with the localisation, is the localisation's own `algebraMap`.

This is `ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` — the statement
that the identification is an isomorphism over `A` and not merely over `ℂ` — read in
`CommRingCat`, which is the only thing the two results below use it for. -/
theorem localisationRingHom_comp_eq :
    CommRingCat.ofHom (localisationRingHom.{u} g f) ≫ (specLocalisationRingIso.{u} g f).hom =
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))) :=
  CommRingCat.hom_ext (RingHom.ext (localisationPresentedAlgebraEquiv_localisationRingHom.{u} g f))

/-! ### The open immersion -/

/-- **`Spec` of the structure map `A ⟶ A_f` is an open immersion.**

The structure map is the localisation's `algebraMap` composed with an isomorphism, by the triangle
above; `AlgebraicGeometry.Spec.map` turns that into a composite of `Spec` of the `algebraMap` —
where Mathlib's `AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway` applies — with
an isomorphism, and open immersions absorb isomorphisms.

Stated at the scheme-level spelling because that is where Mathlib's API is; the locally ringed
space this repository glues with is the same term, which is the next declaration. -/
theorem isOpenImmersion_Spec_map_localisationRingHom :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (localisationRingHom.{u} g f))) := by
  have h : CommRingCat.ofHom (localisationRingHom.{u} g f) =
      CommRingCat.ofHom (algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f))) ≫
        (specLocalisationRingIso.{u} g f).inv := by
    rw [← localisationRingHom_comp_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Spec.map_comp]
  infer_instance

/-- **The functor's value on the structure map is an open immersion**, which is the form a glue
data on the `Spec` side of an affine cover holds its morphisms in.

Taken at `ComplexAnalytic.localisationHom`, which is the structure map read as a morphism of
*objects* of `ComplexAnalytic.Presentation` — `ComplexAnalytic.localisationPresHom` does not
elaborate against `Functor.map`, for the reason its own docstring gives.

The mirror of `ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom`, and the
proof is the theorem above **with no transport**: `ComplexAnalytic.specFunctor.map` is
`AlgebraicGeometry.Spec.locallyRingedSpaceMap` of the underlying ring map, which is
`(AlgebraicGeometry.Spec.map _).toLRSHom`, and `AlgebraicGeometry.IsOpenImmersion` of a scheme
morphism is `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` of that. Instance search does
not cross the identity — see this file's module docstring, where it is measured — so the
declaration is what makes the scheme-level API reachable from a locally-ringed-space glue data. -/
theorem isOpenImmersion_specFunctor_map_localisationHom :
    LocallyRingedSpace.IsOpenImmersion (specFunctor.{u}.map (localisationHom.{u} g f)) :=
  isOpenImmersion_Spec_map_localisationRingHom.{u} g f

end

end ComplexAnalytic

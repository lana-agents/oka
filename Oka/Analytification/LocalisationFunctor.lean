/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.DistinguishedOpen
import Oka.Analytification.Functor

/-!
# The projection of a distinguished open is the analytification of the localisation map

`Oka/Analytification/DistinguishedOpen.lean` builds `ComplexAnalytic.localisationProj`, the
morphism `(A_f)^an ⟶ X^an`, out of the universal property: it is `liftHom` applied to the first
`n` coordinates. That says nothing about where the morphism *comes from*, and the construction
that consumes it — gluing an analytic space out of an affine cover — needs it to be the value of
the **functor** on the localisation map, because the transition isomorphisms of a glue data are
produced from isomorphisms of `ℂ`-algebras and nothing else.

This file supplies that link: `ComplexAnalytic.analytificationMap_localisationPresHom` says
`localisationProj` is `ComplexAnalytic.analytificationMap` of the structure map `A ⟶ A_f`.

It is a separate file rather than a section of `Oka/Analytification/DistinguishedOpen.lean`
because that file imports only `Oka/AnalyticSpace/Nonvanishing.lean` and
`Oka/Analytification/UniversalProperty.lean`, and the functor lives two files further on; the
theorem below is the only thing there that needs it.

## Which way the arrows go

`ComplexAnalytic.PresHom g g'` carries a ring map `PresentedAlgebra g' →+* PresentedAlgebra g`
and induces `analytification g ⟶ analytification g'`, so a morphism *of presentations* out of the
localisation is an algebra map **into** it. That is why
`ComplexAnalytic.localisationPresHom` has type `PresHom (localisationPresentation g f) g` and its
ring map is `A ⟶ A_f`: the two directions are the same statement read in opposite categories.

## Nothing here is about localisation

The ring map is induced by `MvPolynomial.rename (localisationIncl n)`, and the only thing to
check is that it carries `presentationIdeal g` into `presentationIdeal (localisationPresentation
g f)` — which is `ComplexAnalytic.localisationPresentation_castSucc` and a `Submodule.span`
induction. **That `PresentedAlgebra (localisationPresentation g f)` is a localisation of
`PresentedAlgebra g` is not proved here or anywhere**; it is not needed, because a structure map
is all a `PresHom` wants. See `Oka/Analytification/DistinguishedOpen.lean` on the naming.

## Main definitions

- `ComplexAnalytic.localisationRingHom`: the `ℂ`-algebra map `A ⟶ A_f`, as a ring map of
  presented algebras.
- `ComplexAnalytic.localisationPresHom`: the same, as a morphism of presentations.

## Main results

- `ComplexAnalytic.analytificationMap_localisationPresHom` and
  `ComplexAnalytic.analytificationFunctor_map_localisationPresHom`: **the projection of a
  distinguished open is the analytification of the structure map**, as a bare morphism and as the
  functor's value.
- `ComplexAnalytic.localisationIso_inv_analytificationMap`: the inclusion of the open subspace,
  read through the functor — the form a glue data consumes.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The structure map `A ⟶ A_f`**, as a ring map of presented algebras.

It is `MvPolynomial.rename (localisationIncl n)` on representatives; the ideal obligation is
`ComplexAnalytic.localisationPresentation_castSucc`, since the old equations occur among the new
ones renamed. -/
def localisationRingHom :
    PresentedAlgebra.{u} n k g →+*
      PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))).comp
      (MvPolynomial.rename (localisationIncl.{u} n)).toRingHom)
    fun a ha ↦ by
      refine Submodule.span_induction (p := fun x _ ↦
        (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f)))
          (MvPolynomial.rename (localisationIncl.{u} n) x) = 0) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨j, rfl⟩
        refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j.castSucc, ?_⟩)
        exact localisationPresentation_castSucc.{u} g f j
      · simp
      · intro x y _ _ hx hy
        simp [hx, hy]
      · intro c x _ hx
        simp [hx]

/-- **The structure map as a morphism of presentations**, which by the direction convention of
`ComplexAnalytic.PresHom` points from the localisation to `A`. The commutation with the structure
maps is `MvPolynomial.rename_C`. -/
def localisationPresHom : PresHom.{u} (localisationPresentation.{u} g f) g where
  toRingHom := localisationRingHom.{u} g f
  commutes := by
    refine RingHom.ext fun c ↦ ?_
    change localisationRingHom.{u} g f
      (Ideal.Quotient.mk (presentationIdeal.{u} g) (MvPolynomial.C c)) = _
    change (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f)))
      (MvPolynomial.rename (localisationIncl.{u} n) (MvPolynomial.C c)) = _
    rw [MvPolynomial.rename_C]
    rfl

/-- **The tuple the morphism of presentations transports** is the tuple of old coordinates of
`(A_f)^an`, which is exactly the tuple `ComplexAnalytic.localisationProj` was built from. This is
the whole content of the identification below. -/
theorem transported_localisationPresHom (i : ULift.{u} (Fin n)) :
    transported.{u} (localisationPresHom.{u} g f) i =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationIncl.{u} n i) := by
  change quotientToGlobal.{u} (localisationPresentation.{u} g f)
    (localisationRingHom.{u} g f
      (Ideal.Quotient.mk (presentationIdeal.{u} g) (MvPolynomial.X i))) = _
  change quotientToGlobal.{u} (localisationPresentation.{u} g f)
    (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]
  exact polyToGlobal_X.{u} (localisationPresentation.{u} g f) (localisationIncl.{u} n i)

/-- **The projection of a distinguished open is the analytification of the structure map.**

Both sides are morphisms into `X^an`, so `ComplexAnalytic.hom_ext_analytification` reduces it to
the coordinates, where one side is `ComplexAnalytic.coordPullback_analytificationMap_comp` and the
other `ComplexAnalytic.coordPullback_localisationProj_comp`, and the two tuples agree by
`ComplexAnalytic.transported_localisationPresHom`. -/
theorem analytificationMap_localisationPresHom :
    analytificationMap.{u} (localisationPresHom.{u} g f) = localisationProj.{u} g f := by
  refine hom_ext_analytification.{u} g _ _ fun i ↦ ?_
  rw [coordPullback_analytificationMap_comp, coordPullback_localisationProj_comp,
    transported_localisationPresHom]

/-- **The same, as the functor's value on a morphism of `ComplexAnalytic.Presentation`.** This is
`ComplexAnalytic.analytificationMap_localisationPresHom`; `ComplexAnalytic.analytificationFunctor`
is `analytificationMap` on morphisms by definition. -/
theorem analytificationFunctor_map_localisationPresHom :
    analytificationFunctor.{u}.map
        (X := ⟨n + 1, k + 1, localisationPresentation.{u} g f⟩) (Y := ⟨n, k, g⟩)
        (localisationPresHom.{u} g f) =
      localisationProj.{u} g f :=
  analytificationMap_localisationPresHom.{u} g f

/-- **The inclusion of `D(f)` into `X^an`, read through the functor.**

`ComplexAnalytic.localisationIso_inv_localisationProj` says the inclusion is the inverse of the
comparison followed by the projection; with the identification above, the projection is the
analytification of an algebra map. So this exhibits `ofRestrict` — the open immersion, which is
not built from any algebra — as a composite of the comparison isomorphism with a morphism
produced by the functor from a `ℂ`-algebra map, and that is the form in which a glue data uses
it. -/
theorem localisationIso_inv_analytificationMap :
    (localisationIso.{u} g f).inv ≫ analytificationMap.{u} (localisationPresHom.{u} g f) =
      (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f) :=
  (congrArg (fun m ↦ (localisationIso.{u} g f).inv ≫ m)
      (analytificationMap_localisationPresHom.{u} g f)).trans
    (localisationIso_inv_localisationProj.{u} g f)

/-- **The ring map on representatives**: the class of `p` goes to the class of `p` with its
variables renamed. Stated because every consumer of
`ComplexAnalytic.localisationPresHom` that needs to compute with it needs this and nothing
else. -/
theorem localisationRingHom_mk (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    localisationRingHom.{u} g f (Ideal.Quotient.mk (presentationIdeal.{u} g) p) =
      Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
        (MvPolynomial.rename (localisationIncl.{u} n) p) :=
  rfl

end

end ComplexAnalytic

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringMap

/-!
# Finite étale morphisms cancel

If `f ≫ g` and `g` are finite étale then so is `f`. This is the statement a Galois-category
structure on `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` needs first — a morphism between two
covers of `Z` is itself a cover — and `Oka/AnalyticSpace/FiniteEtaleOver.lean` records its absence
as *the* gap of that file.

## What was left, and it was one of four halves

`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` has two fields and each has two halves, so
cancellation is four statements. Three of them were already here and none needed anything of this
repository's own:

* both halves of the local-isomorphism rung are
  `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` (`Oka/AnalyticSpace/LocalIso.lean`);
* the fibre half of the finite rung is `ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp`
  (`Oka/AnalyticSpace/Finite.lean`), which asks nothing whatever of `g`.

**The fourth is closedness of the underlying map of `f`**, and it is what this file supplies.

## Why the recorded obstruction does not apply, and it is a matter of which hypothesis is read

`Oka/AnalyticSpace/Finite.lean` and `Oka/AnalyticSpace/LocalIso.lean` both record that the closed
half does **not** cancel, with the line with two origins over the line as the witness, and both
say the classical repair factors `f` through its graph and needs a separatedness notion and fibre
products — neither of which exists here.

That is right, and it is right **at the hypothesis those passages consider, which is `g` finite**:
closed with finite fibres. The line with two origins is exactly that, and
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` (`OkaTest/FiniteEtaleCancel.lean`)
compiles a witness for the weakening — a weaker one, its second map not being a local
homeomorphism — so the
phenomenon is no longer only prose.

**At the hypothesis this file takes — `g` finite étale — no graph and no fibre product is needed.**
A finite étale morphism of analytic spaces with Hausdorff source has a covering map underneath it
(`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`), a covering map decomposes
the preimage of an evenly covered open into sheets on each of which it is **injective**, and
`IsCoveringMap.isClosedMap_of_comp` in `Oka/Topology/Covering/Basic.lean` is the cancellation that
injectivity gives. The line with two origins is not a counterexample to it because its two origins
lie in no common sheet: the fold map is a closed local homeomorphism with finite fibres and is not
a covering map.

So the obstruction those two files record was never about the finite étale case, and what removes
it is not a new construction but reading the hypothesis one rung further down.

## Where the Hausdorff hypothesis comes from, and where it sits

`[T2Space Y]` is asked of the **middle** space — the source of `g`, which is the total space of
the cover being cancelled against — and it is not this file's hypothesis to justify. It is
inherited verbatim from `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`, whose
`[T2Space]` is Mathlib's, used to separate the finitely many points of a fibre; nothing below adds
a separation hypothesis of its own, and `IsCoveringMap.isClosedMap_of_comp` uses none at all.

**It is a genuine hypothesis and not an instance that will be found.**
`Oka/AnalyticSpace/Basic.lean` imposes no separation axiom on `ComplexAnalytic.AnalyticSpace`, for
the reason `AlgebraicGeometry.Scheme` does not; `ComplexAnalytic.t2Space_restrict_punctured` in
`OkaTest/FiniteMorphism.lean` is the only such instance in this repository and it is about one
restriction of one space.

## What is not here

* **No Galois category.** `Oka/AnalyticSpace/FiniteEtaleOver.lean` names cancellation as the first
  obstacle to one, and this file is that obstacle and no more. The others that file records are
  untouched: there are **no fibre products of analytic spaces anywhere in this repository**, so
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` is not statable for
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale`, and there is no fibre functor.
* **Nothing is said about the category.** The statements below are about morphisms; that a
  morphism of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver Z` has finite étale underlying
  morphism is a reading of them that this file does not write down, because the `⊤` in that
  definition means a morphism of covers carries no such condition to be discharged.
* **The third position of two-out-of-three is not here** — concluding about `g` from `f` and
  `f ≫ g` — and `Oka/AnalyticSpace/LocalIso.lean` says why it should not be expected: both
  hypotheses see `g` only along the image of `f`.
* **No separatedness notion for `ComplexAnalytic.AnalyticSpace`, and no fibre products.** This
  file routes around both rather than supplying either, and the absence of both stays recorded
  where it was.
* **The Hausdorff hypothesis is not shown necessary**, only inherited. Whether the closed half
  cancels along a finite étale `g` with non-Hausdorff source is not asked here; the counterexample
  in `OkaTest/FiniteEtaleCancel.lean` is against dropping *finite étale* to *finite*, and says
  nothing about dropping `[T2Space Y]`.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_isFiniteEtale`: **finiteness cancels along a
  finite étale morphism with Hausdorff source** — if `f ≫ g` is finite and `g` is finite étale
  then `f` is finite. This is the half that was missing, and what it replaces is the injectivity
  hypothesis of the older cancellation lemma in `Oka/AnalyticSpace/Finite.lean` — which a cover is
  exactly what cannot supply.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`: **finite étale morphisms cancel** — if
  `f ≫ g` and `g` are finite étale then so is `f`.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **Finiteness cancels along a finite étale morphism with Hausdorff source**: if `f ≫ g` is
finite and `g` is finite étale, then `f` is finite.

The fibre half is `ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp`, which asks nothing of `g`.
The closed half is `IsCoveringMap.isClosedMap_of_comp` (`Oka/Topology/Covering/Basic.lean`)
applied to the covering map underneath `g`, which is
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` and is where `[T2Space Y]` is
spent; nothing here adds a separation hypothesis of its own.

**Compare `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp`**, which cancels along a
second factor whose underlying map is *injective*. That is the hypothesis a cover cannot supply —
`ComplexAnalytic.not_isIso_sq` is proved from the non-injectivity of `z ↦ z²` — and the two
statements are incomparable: neither hypothesis implies the other, since a closed embedding need
not be étale and a cover need not be injective.

The `rfl` identifying the underlying map of `f ≫ g` with the composite of the two underlying maps
is the one `ComplexAnalytic.AnalyticSpace.isFinite_comp` uses; it is stated rather than left to
unification because the `▸` below needs it in that direction.

**A `theorem` and not an `instance`**, for the reason
`ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp` gives: instance search would have to invent
`Z` and `g`, which the goal determines in no way. -/
theorem isFinite_of_comp_of_isFiniteEtale {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [T2Space Y] [IsFiniteEtale g] [IsFinite (f ≫ g)] : IsFinite f where
  isClosedMap := by
    have h : ((f ≫ g).toLRSHom.base : X → Z) = (g.toLRSHom.base : Y → Z) ∘ f.toLRSHom.base := rfl
    exact (isCoveringMap_base_of_isFiniteEtale g).isClosedMap_of_comp
      f.toLRSHom.base.hom.continuous (h ▸ IsFinite.isClosedMap (f := f ≫ g))
  finite_fiber y := finite_fiber_of_comp f g y

/-- **Finite étale morphisms cancel**: if `f ≫ g` and `g` are finite étale, then so is `f`.

This is the statement `Oka/AnalyticSpace/FiniteEtaleOver.lean` records as the first thing a
Galois-category structure on `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` would need, and it is
the two fields' cancellations put together:
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_isFiniteEtale` above and
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp`. Only the first uses `[T2Space Y]`, and only
through the covering rung.

**It does not make the category Galois**, and the same file says what else is wanted: no fibre
products, hence no base change, and no fibre functor. -/
theorem isFiniteEtale_of_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [T2Space Y] [IsFiniteEtale (f ≫ g)] [IsFiniteEtale g] : IsFiniteEtale f where
  isFinite := isFinite_of_comp_of_isFiniteEtale f g
  isLocalIso := isLocalIso_of_comp f g

end ComplexAnalytic.AnalyticSpace

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Relations
import Oka.Analytification.Presentation

/-!
# The analytification of a sheaf

For a presentation `g` of a finitely generated `ℂ`-algebra `A`, the comparison morphism
`ComplexAnalytic.analytificationToSpec g : X^an ⟶ Spec A` pulls sheaves of modules back:

```
ComplexAnalytic.analytificationSheaf g :
  SheafOfModules (Spec A).ringSheaf ⥤ SheafOfModules (X^an).ringSheaf
```

**This is the functor whose exactness on coherent sheaves is GAGA**, and it is the object that
every account of this development so far has described as missing.

## It was not missing, and there was no design question

`Oka/Analytification/Presentation.lean` and its siblings say that GAGA needs "the analytification
of a *sheaf*", and call it a construction with a design question in front of it — which
pullback, along what, in which category. **Mathlib has the functor.**
`SheafOfModules.pullback` is defined for any morphism of sheaves of rings over a continuous
functor of sites, as the left adjoint of `SheafOfModules.pushforward`, and
`AlgebraicGeometry.Scheme.Modules` uses exactly it to make sheaves of modules functorial for
schemes. Nothing in it is special to schemes.

The one thing that had to be supplied is
`AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom`, the morphism of sheaves of rings
attached to a morphism of locally ringed spaces. It is Mathlib's
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` verbatim, four lines. It is in
`Oka/AnalyticSpace/Relations.lean`, next to
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf`, because the two have to agree on how the site
is spelled.

## The obstacle really was a coercion

`ringSheaf`'s site used to be `Opens.grothendieckTopology ↑Y`, and
`TopologicalSpace.Opens.map f.base` produces `Opens.grothendieckTopology ↑Y.toPresheafedSpace`.
The two are definitionally equal and **instance search does not cross them**: Mathlib's
continuity instance for `Opens.map` is not found, and declaring it oneself in the other spelling
does not help, because the discrimination-tree key is built from the elaborated implicit
arguments. With the first spelling `toRingSheafHom` cannot be *stated*.

Re-spelling `ringSheaf` costs four sites and no proof changes; `ringSheaf`'s own docstring records
why it must stay that way.

## Main definitions

- `ComplexAnalytic.analytificationSheaf`: **the analytification of a sheaf of modules.**
- `ComplexAnalytic.analytificationSheafAdj`: it is left adjoint to pushforward along the
  comparison morphism, which is what determines it.
- `ComplexAnalytic.analytificationSheafUnitToUnit`: **the analytification of `𝒪_X` maps
  canonically to `𝒪_{X^an}`** — the map a comparison theorem between the two structure sheaves
  is a statement about.

## Main results

- `ComplexAnalytic.preservesColimits_analytificationSheaf`: **the analytification of a sheaf is
  right exact**, free from the adjunction. The half of exactness that is *not* free is
  preservation of finite limits, and that is where the flatness of the stalk maps has to be
  consumed — which is what makes this the useful thing to state before GAGA rather than after.

## What is not here

* **GAGA.** *Left* exactness of this functor on coherent sheaves is the theorem — right
  exactness is above and is free — and it is where the flatness of the stalk maps gets consumed.
  **Both halves of that flatness now exist**:
  `ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec` for the ambient case and
  `ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec` for the presented one, which is
  the one this functor's source is about. What is missing is no longer a flatness statement but a
  bridge to it: **nothing here computes this functor on stalks**, which is what an argument from
  flatness needs.
* **Coherence of the image.** That the analytification of a coherent sheaf is coherent is a
  separate statement; `ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf` gives it for the
  structure sheaf and nothing here extends that to the image of this functor.
* **Anything analytic.** Every line here is the `Γ`–`Spec` adjunction and category theory. The
  analytic content is upstream.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace ComplexAnalytic

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The analytification of a sheaf of modules on `Spec (ℂ[x] ⧸ I)`**: pullback along the
comparison morphism `X^an ⟶ Spec (ℂ[x] ⧸ I)`. -/
def analytificationSheaf :
    SheafOfModules.{u}
        (Spec.locallyRingedSpaceObj
          (CommRingCat.of
            (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf ⥤
      SheafOfModules.{u} (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.ringSheaf :=
  (analytificationToSpec.{u} g).pullbackModules

/-- **The analytification of a sheaf is left adjoint to pushforward along the comparison
morphism.** It is defined as that left adjoint, so this is the adjunction rather than a theorem
about it — and it is what determines the functor up to unique isomorphism. -/
def analytificationSheafAdj :
    analytificationSheaf.{u} g ⊣
      SheafOfModules.pushforward.{u} (analytificationToSpec.{u} g).toRingSheafHom :=
  (analytificationToSpec.{u} g).pullbackModulesAdj

/-- **The analytification of a sheaf is right exact**, and that half of GAGA's exactness costs
nothing: it is a left adjoint, and a left adjoint preserves colimits.

The half that is *not* free is preservation of finite limits — kernels — and that is exactly
where the flatness of the stalk maps has to be consumed. Stating the free half separately is what
makes the shape of the remaining work visible. -/
theorem preservesColimits_analytificationSheaf :
    Limits.PreservesColimits (analytificationSheaf.{u} g) :=
  (analytificationSheafAdj.{u} g).leftAdjoint_preservesColimits

/-- **The analytification of `𝒪_X` maps canonically to `𝒪_{X^an}`.**

This is what makes the structure sheaf of `X^an` an algebra over the analytification of the
structure sheaf of `X`, and it is the map a comparison theorem between the two is a statement
about. It needs no hypothesis: it is the adjunct of the unit map, which exists for any morphism
of locally ringed spaces. -/
def analytificationSheafUnitToUnit :
    (analytificationSheaf.{u} g).obj
        (SheafOfModules.unit
          (Spec.locallyRingedSpaceObj
            (CommRingCat.of
              (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf) ⟶
      SheafOfModules.unit
        (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.ringSheaf :=
  (analytificationToSpec.{u} g).pullbackModulesUnitToUnit

end ComplexAnalytic

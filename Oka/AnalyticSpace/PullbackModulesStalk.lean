/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Algebra.Category.ModuleCat.Sheaf.PullbackStalk
import Oka.AnalyticSpace.Relations

/-!
# The stalk of the pullback of `𝒪`-modules along a morphism of locally ringed spaces

**`(f^* M)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} M_{f x}`**, naturally in `M`, for `f : X ⟶ Y` a morphism of
locally ringed spaces — `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesStalkIso`.

This is the general theory of `Oka/Algebra/Category/ModuleCat/Sheaf/PullbackStalk.lean`
instantiated at a locally ringed space. It contains no analytic mathematics, and it lives under
`Oka/AnalyticSpace/` for the same reason
`AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModules` does: it has to agree with
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf` on how the site is spelled, and `ringSheaf`'s
docstring explains why that spelling is load-bearing. Its Mathlib destination is next to
`ringSheaf`'s, wherever that ends up.

## The three identifications, all `rfl`

Instantiating costs nothing because every piece of the general statement is *definitionally* what
the locally ringed space already has:

* `SheafOfModules.ofCommRingCat Y.presheaf _` is `Y.ringSheaf` — `ringSheaf_eq_ofCommRingCat`;
* `SheafOfModules.sheafRingHom f.c` is `f.toRingSheafHom` — `toRingSheafHom_eq_sheafRingHom`;
* `PresheafOfModules.ringStalkMap f.base f.c x` is `f.stalkMap x` — `ringStalkMap_eq_stalkMap`.

The third is the one worth stating rather than relying on. `PresheafOfModules.ringStalkMap` is
the composite `(stalkFunctor _).map φ ≫ stalkPushforward _ f _` for an **unbundled** pair
`(f, φ)`; Mathlib defines that same composite three times, once at each bundling level
(`AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`,
`AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap`, `AlgebraicGeometry.Scheme.Hom.stalkMap`),
and has no unbundled one — the only unbundled ingredient anywhere is
`TopCat.Presheaf.stalkPushforward`. So `ringStalkMap` is a fourth level rather than a second name,
and stating the agreement as a lemma is what makes it break if either side moves.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.stalkFunctor`: the stalk of a sheaf of `𝒪`-modules at a
  point, as a functor to modules over the stalk of the structure sheaf.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesStalkIso`: **the stalk of a pullback
  is the base change of the stalk.**

## Why this is the local input to GAGA and not GAGA

`ComplexAnalytic.analytificationSheaf` is `Hom.pullbackModules` along the comparison morphism, so
this computes it on stalks — which is the thing every account of the analytification line has said
was missing. **It consumes no flatness and needs none**: the base-change formula holds for an
arbitrary morphism of locally ringed spaces. Flatness is what turns the formula into *exactness*
of the pullback, and that is a separate theorem; the flatness it will consume is
`ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec`.
-/

open CategoryTheory TopologicalSpace Opposite Limits

universe u

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u})

/-- The structure presheaf of a locally ringed space is a sheaf of rings. -/
theorem isSheaf_ringSheaf :
    TopCat.Presheaf.IsSheaf (Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (forget₂ CommRingCat.{u} RingCat.{u}) Y.presheaf).1 Y.IsSheaf

/-- `AlgebraicGeometry.LocallyRingedSpace.ringSheaf` is `SheafOfModules.ofCommRingCat` of the
structure presheaf. Definitional, and stated so that it breaks if either side moves. -/
theorem ringSheaf_eq_ofCommRingCat :
    Y.ringSheaf = SheafOfModules.ofCommRingCat Y.presheaf Y.isSheaf_ringSheaf :=
  rfl

/-- **The stalk of a sheaf of `𝒪`-modules at a point, as a functor.** -/
def stalkFunctor (y : Y) :
    SheafOfModules.{u} Y.ringSheaf ⥤ ModuleCat.{u} (Y.presheaf.stalk y) :=
  SheafOfModules.stalkFunctor (hR := Y.isSheaf_ringSheaf) y

variable {Y}

/-- `AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom` is `SheafOfModules.sheafRingHom` of
the comorphism. Definitional. -/
theorem toRingSheafHom_eq_sheafRingHom {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f.toRingSheafHom = SheafOfModules.sheafRingHom
      (hS := Y.isSheaf_ringSheaf) (hR := X.isSheaf_ringSheaf) f.c :=
  rfl

/-- `PresheafOfModules.ringStalkMap` at the base map and the comorphism of `f` is
`AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap`. Definitional. -/
theorem ringStalkMap_eq_stalkMap {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    PresheafOfModules.ringStalkMap f.base f.c x = f.stalkMap x :=
  rfl

/-- **The stalk of the pullback of `𝒪`-modules along a morphism of locally ringed spaces is the
base change of the stalk**: `(f^* M)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} M_{f x}`, naturally in `M`. -/
def Hom.pullbackModulesStalkIso {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    f.pullbackModules ⋙ X.stalkFunctor x ≅
      Y.stalkFunctor (f.base x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom :=
  SheafOfModules.pullbackStalkIso
    (hS := Y.isSheaf_ringSheaf) (hR := X.isSheaf_ringSheaf) f.c x

end AlgebraicGeometry.LocallyRingedSpace

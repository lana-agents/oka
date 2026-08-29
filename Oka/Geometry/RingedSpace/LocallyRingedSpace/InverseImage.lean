/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify
import Oka.Topology.Sheaves.Stalks

/-!
# The inverse image of a locally ringed space along a continuous map

A continuous map `p : E ⟶ Y` into the space underlying a locally ringed space makes `E` a locally
ringed space, by giving it the inverse image `p⁻¹𝒪_Y` of the structure sheaf; the underlying map
of spaces becomes a morphism of locally ringed spaces `Y.inverseImage p ⟶ Y`, and **every one of
its stalk maps is an isomorphism**.

There is no analytic content here, so this file is a candidate for upstreaming; it lives in the
`Oka/Geometry/` mirror of the Mathlib directory tree for that reason. Mathlib has the sheaf-level
construction — `TopCat.Sheaf.pullback` — and none of the locally-ringed-space consequences.

## Why the stalks come out right, and why that is the whole file

`p⁻¹𝒪_Y` is a *sheafification*, so nothing about its sections over an open set is computable in
general. What is computable is its stalks, and they are all that a locally ringed space asks
about. Two Mathlib theorems do it and they compose:

* `TopCat.Presheaf.stalkPullbackIso` identifies the stalk of the **presheaf** inverse image at `e`
  with the stalk of `𝒪_Y` at `p e`, for an **arbitrary** continuous map — no openness and no
  injectivity;
* `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` says sheafification does not change a
  stalk.

**The second is easy to look for in the wrong place.** `Mathlib/Topology/Sheaves/Sheafify.lean`
opens with `assert_not_exists CommRingCat`, and the concrete `TopCat.Presheaf.sheafifyStalkIso`
that most of that file is about is `Type`-valued and unusable here. The statement used below is in
a second namespace block at the foot of the same file, is proved from the sheafification and
skyscraper adjunctions rather than from the explicit construction, and holds for any `C` with
colimits, a terminal object and `HasWeakSheafify` — all of which `CommRingCat` has.

## The morphism is built by hand, and that is deliberate

`AlgebraicGeometry.PresheafedSpace.Hom.stalkMap ⟨p, c⟩ e` is by definition
`(stalkFunctor _ (p e)).map c ≫ stalkPushforward _ p _ e`, and
`TopCat.Presheaf.stalkPullbackHom` is *the same expression* with `c` the unit of the **presheaf**
adjunction. So taking `c` to be that unit followed by the sheafification map, rather than the unit
of `TopCat.Sheaf.pullbackPushforwardAdjunction`, makes
`AlgebraicGeometry.LocallyRingedSpace.stalkMap_inverseImageHom` one rewrite with
`TopCat.Presheaf.stalkPushforward_naturality` (`Oka/Topology/Sheaves/Stalks.lean`) and no
unfolding of `CategoryTheory.Functor.sheafAdjunctionContinuous`. The sheaf-level unit would be the
tidier definition and it is built by `CategoryTheory.Adjunction.leftAdjointUniq` out of a
restriction of a composite adjunction, so relating it to the presheaf unit is a computation this
file does not need to do.

## The comparison morphism, and which adjunction it is built from

A morphism `q : Z ⟶ Y` factors through `q.base⁻¹Y`, by a morphism that is the identity on
carriers. **The input is the *presheaf* adjunction `TopCat.Presheaf.pullbackPushforwardAdjunction`
together with the universal property of sheafification, and not
`TopCat.Sheaf.pullbackPushforwardAdjunction`**, for the same reason the previous paragraph gives:
`AlgebraicGeometry.LocallyRingedSpace.inverseImageHom` is built from the presheaf unit, so an
adjunct taken on the same side of the sheafification makes
`AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp` one application of
`Equiv.apply_symm_apply`, and relating the two units is again a computation this file does not
need to do.

**The sheafification is not opened.** `CategoryTheory.sheafifyLift` is used through
`CategoryTheory.toSheafify_sheafifyLift` and nothing else, so the absence recorded below — that
no formula for the sections of `p⁻¹𝒪_Y` is stated here — costs nothing.

**No transport appears anywhere in the construction**, which is worth saying because a comparison
morphism into a space built by transporting structure usually carries one. The carrier of
`q.base⁻¹Y` is `Z`'s on the nose, and `(TopCat.Presheaf.pushforward CommRingCat (𝟙 _)).obj
Z.presheaf` is `Z.presheaf` on the nose, so the `c` field of a morphism with identity base is
literally a map `p⁻¹𝒪_Y ⟶ 𝒪_Z`.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.inverseImage`: the locally ringed space `p⁻¹Y`, whose
  underlying topological space is `E` on the nose.
- `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom`: the morphism `p⁻¹Y ⟶ Y`, whose
  underlying map is `p` on the nose.
- `AlgebraicGeometry.LocallyRingedSpace.toInverseImage`: **the comparison morphism `Z ⟶ q.base⁻¹Y`
  attached to a morphism `q : Z ⟶ Y`**, whose underlying map is the identity on the nose.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso`: **the stalk of the inverse image at
  `e` is the stalk of `Y` at `p e`.**
- `AlgebraicGeometry.LocallyRingedSpace.stalkMap_inverseImageHom`: **the stalk map of the morphism
  is that isomorphism**, so in particular it is one — which is what makes the morphism a morphism
  of *locally* ringed spaces at all, and is the form a consumer wants.
- `AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp`: **the comparison morphism factors
  `q` through `q.base⁻¹Y`**, which is what makes it a morphism over `Y`.
- `AlgebraicGeometry.LocallyRingedSpace.stalkMap_toInverseImage`: **its stalk map is `q`'s,
  preceded by the isomorphism above**.
- `AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_toInverseImage`: the consequence a consumer
  wants — **the comparison morphism is a stalkwise isomorphism wherever `q` is**.

## What is not here

* **No local homeomorphism, no covering map, and no even coverings.** Everything above is for an
  arbitrary continuous map, because that is what the two Mathlib inputs give; a hypothesis that is
  never used is one a reader has to check is never used.
* **Nothing about the sections of `p⁻¹𝒪_Y` over an open set.** For `p` an open map the *presheaf*
  inverse image is `V ↦ 𝒪_Y(p '' V)` — `IsOpenMap.pullbackObjIso` — and that presheaf is
  **not** a sheaf when `p` is not injective: over a `V` meeting two sheets of a double cover the
  sheaf condition asks for a pair of sections and the presheaf offers one. So the sheafification
  is doing real work and no formula for it is stated. Identifying the restriction of `p⁻¹𝒪_Y` to
  a sheet with `𝒪_Y` on its image is the next step and is a different issue.
* **No universal property, though its existence half is now here.**
  `AlgebraicGeometry.LocallyRingedSpace.toInverseImage` produces the factorisation of a morphism
  `q : Z ⟶ Y` through `q.base⁻¹Y` that a universal property would produce, and
  `AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp` is that it is a factorisation.
  **Uniqueness is not stated**: nothing below says that it is the only morphism over `Y` with
  identity base, although `CategoryTheory.sheafifyLift_unique` is what would prove it. Neither is
  naturality in `q`, and `AlgebraicGeometry.LocallyRingedSpace.inverseImage` is still not shown to
  be a left adjoint to anything — for which `TopCat.Sheaf.pullbackPushforwardAdjunction`, and not
  the presheaf adjunction used above, is where one would start.
* **No comparison with `AlgebraicGeometry.LocallyRingedSpace.restrict`.** For `p` the inclusion of
  an open subset both constructions are available and they should agree; that is not proved.
-/

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

noncomputable section

variable (Y : LocallyRingedSpace.{u}) {E : TopCat.{u}} (p : E ⟶ Y.toTopCat)

/-- **The inverse image of the structure sheaf**, as a sheaf of rings on `E`. -/
abbrev inverseImageSheaf : E.Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} p).obj Y.toSheafedSpace.sheaf

/-- **From the presheaf inverse image to the sheaf inverse image**: sheafify, then cross
`TopCat.Sheaf.pullbackIso`, which is the isomorphism between Mathlib's abstract sheaf pullback and
the sheafification of the presheaf one.

This map, rather than the unit of `TopCat.Sheaf.pullbackPushforwardAdjunction`, is what
`AlgebraicGeometry.LocallyRingedSpace.inverseImageHom` is built from; the module docstring says
why. -/
def toInverseImageSheaf :
    (TopCat.Presheaf.pullback CommRingCat.{u} p).obj Y.presheaf ⟶
      (inverseImageSheaf Y p).presheaf :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology E) _ ≫
    (TopCat.Sheaf.forget CommRingCat.{u} E).map
      ((TopCat.Sheaf.pullbackIso CommRingCat.{u} p).app Y.toSheafedSpace.sheaf).inv

/-- **Sheafification does not change a stalk**, packaged as the isomorphism induced by
`AlgebraicGeometry.LocallyRingedSpace.toInverseImageSheaf`.

The first factor is `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, the general
statement at the foot of `Mathlib/Topology/Sheaves/Sheafify.lean` rather than the `Type`-valued
`TopCat.Presheaf.sheafifyStalkIso` that file is mostly about; the second is a functor applied to
an isomorphism. -/
def stalkToInverseImageSheafIso (e : E) :
    ((TopCat.Presheaf.pullback CommRingCat.{u} p).obj Y.presheaf).stalk e ≅
      (inverseImageSheaf Y p).presheaf.stalk e := by
  haveI h : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} e).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology E)
        ((TopCat.Presheaf.pullback CommRingCat.{u} p).obj Y.presheaf))) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso e CommRingCat.{u}
      ((TopCat.Presheaf.pullback CommRingCat.{u} p).obj Y.presheaf)
  exact (@asIso _ _ _ _ _ h) ≪≫
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} e).mapIso
      ((TopCat.Sheaf.forget CommRingCat.{u} E).mapIso
        ((TopCat.Sheaf.pullbackIso CommRingCat.{u} p).app Y.toSheafedSpace.sheaf).symm)

@[simp]
theorem stalkToInverseImageSheafIso_hom (e : E) :
    (stalkToInverseImageSheafIso Y p e).hom =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} e).map (toInverseImageSheaf Y p) := by
  simp [stalkToInverseImageSheafIso, toInverseImageSheaf]

/-- **The stalk of the inverse image at `e` is the stalk of `Y` at `p e`.**

`TopCat.Presheaf.stalkPullbackIso` for the presheaf inverse image, then
`AlgebraicGeometry.LocallyRingedSpace.stalkToInverseImageSheafIso` for the sheafification. Neither
step needs anything of `p` beyond continuity. -/
def stalkInverseImageIso (e : E) :
    Y.presheaf.stalk (p e) ≅ (inverseImageSheaf Y p).presheaf.stalk e :=
  TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} p Y.presheaf e ≪≫
    stalkToInverseImageSheafIso Y p e

/-- **The inverse image of a locally ringed space along a continuous map.**

The carrier is `E` and the structure sheaf is `p⁻¹𝒪_Y`; the `isLocalRing` field is
`AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso` transported, since a ring isomorphic
to a local ring is local. -/
def inverseImage : LocallyRingedSpace.{u} where
  carrier := E
  presheaf := (inverseImageSheaf Y p).presheaf
  IsSheaf := (inverseImageSheaf Y p).property
  isLocalRing e := by
    have φ : Y.presheaf.stalk (p e) ≃+* (inverseImageSheaf Y p).presheaf.stalk e :=
      (stalkInverseImageIso Y p e).commRingCatIsoToRingEquiv
    haveI : Nontrivial ((inverseImageSheaf Y p).presheaf.stalk e) := φ.symm.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' φ.toRingHom φ.surjective

/-- **The underlying topological space of the inverse image is `E`**, on the nose. -/
@[simp]
theorem inverseImage_toTopCat : (inverseImage Y p).toTopCat = E := rfl

/-- **The structure sheaf of the inverse image is `p⁻¹𝒪_Y`**, on the nose. -/
@[simp]
theorem inverseImage_presheaf :
    (inverseImage Y p).presheaf = (inverseImageSheaf Y p).presheaf := rfl

/-- The morphism `p⁻¹Y ⟶ Y` of *presheafed* spaces: `p` downstairs, and upstairs the unit of the
presheaf inverse-image adjunction followed by
`AlgebraicGeometry.LocallyRingedSpace.toInverseImageSheaf`. -/
def inverseImageHomAux : (inverseImage Y p).toPresheafedSpace.Hom Y.toPresheafedSpace where
  base := p
  c := (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} p).unit.app Y.presheaf ≫
    (TopCat.Presheaf.pushforward CommRingCat.{u} p).map (toInverseImageSheaf Y p)

@[simp]
theorem inverseImageHomAux_base : (inverseImageHomAux Y p).base = p := rfl

@[simp]
theorem inverseImageHomAux_c :
    (inverseImageHomAux Y p).c =
      (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} p).unit.app Y.presheaf ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} p).map (toInverseImageSheaf Y p) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The stalk map of the projection is the identification of the two stalks.**

Both sides are `(stalkFunctor (p e)).map (unit) ≫ stalkPushforward ≫ (stalkFunctor e).map
(toInverseImageSheaf)` once `TopCat.Presheaf.stalkPushforward_naturality` has moved the second
factor of `c` past the pushforward; the left-hand side is that by the definition of
`AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`, and the right-hand side by the definition of
`TopCat.Presheaf.stalkPullbackHom`. -/
theorem stalkMap_inverseImageHomAux (e : E) :
    (inverseImageHomAux Y p).stalkMap e = (stalkInverseImageIso Y p e).hom := by
  change (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (p e)).map (inverseImageHomAux Y p).c ≫
      ((inverseImageSheaf Y p).presheaf).stalkPushforward CommRingCat.{u} p e = _
  rw [inverseImageHomAux_c, Functor.map_comp, Category.assoc,
    TopCat.Presheaf.stalkPushforward_naturality, stalkInverseImageIso, Iso.trans_hom,
    stalkToInverseImageSheafIso_hom]
  rfl

instance isIso_stalkMap_inverseImageHomAux (e : E) :
    IsIso ((inverseImageHomAux Y p).stalkMap e) := by
  rw [stalkMap_inverseImageHomAux]
  infer_instance

/-- **The morphism `p⁻¹Y ⟶ Y` of locally ringed spaces.**

The locality of the stalk maps is not a condition here: they are isomorphisms, by
`AlgebraicGeometry.LocallyRingedSpace.stalkMap_inverseImageHom`. -/
def inverseImageHom : inverseImage Y p ⟶ Y where
  toHom := inverseImageHomAux Y p
  prop e := isLocalHom_of_isIso ((inverseImageHomAux Y p).stalkMap e)

/-- **The underlying map of the projection is `p`**, on the nose. -/
@[simp]
theorem inverseImageHom_base : (inverseImageHom Y p).base = p := rfl

/-- **The stalk map of `p⁻¹Y ⟶ Y` at `e` is the identification of the stalk at `e` with the stalk
of `Y` at `p e`.** -/
theorem stalkMap_inverseImageHom (e : E) :
    (inverseImageHom Y p).stalkMap e = (stalkInverseImageIso Y p e).hom :=
  stalkMap_inverseImageHomAux Y p e

/-- **The projection is an isomorphism on every stalk.** -/
instance isIso_stalkMap_inverseImageHom (e : E) : IsIso ((inverseImageHom Y p).stalkMap e) :=
  isIso_stalkMap_inverseImageHomAux Y p e

end

noncomputable section

variable {Y Z : LocallyRingedSpace.{u}} (q : Z ⟶ Y)

/-- **The adjunct of the comparison map of a morphism**, at the level of presheaves: `q.c` is a
map `𝒪_Y ⟶ q_* 𝒪_Z`, and this is the map `q.base⁻¹𝒪_Y ⟶ 𝒪_Z` it corresponds to under
`TopCat.Presheaf.pullbackPushforwardAdjunction`.

**The presheaf adjunction and not `TopCat.Sheaf.pullbackPushforwardAdjunction`**, for the reason
the module docstring gives for `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom`: that
morphism is built from the *presheaf* unit, so an adjunct taken on the same side of the
sheafification makes `AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp` one application
of `Equiv.apply_symm_apply` and needs no comparison between the two units. -/
def inverseImageAdjunct :
    (TopCat.Presheaf.pullback CommRingCat.{u} q.base).obj Y.presheaf ⟶ Z.presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.base).homEquiv
    Y.presheaf Z.presheaf).symm q.toHom.c

/-- **The comparison map on structure sheaves**, `p⁻¹𝒪_Y ⟶ 𝒪_Z` for `p = q.base`: the presheaf
adjunct `AlgebraicGeometry.LocallyRingedSpace.inverseImageAdjunct`, extended over the
sheafification because `𝒪_Z` is a sheaf.

**The sheafification is used through its universal property and is not opened.** The module
docstring records that no formula for the sections of `p⁻¹𝒪_Y` is stated here; nothing below
needs one, because `CategoryTheory.sheafifyLift` is characterised by
`CategoryTheory.toSheafify_sheafifyLift` alone. -/
def inverseImageDesc : (inverseImageSheaf Y q.base).presheaf ⟶ Z.presheaf :=
  (TopCat.Sheaf.forget CommRingCat.{u} _).map
      ((TopCat.Sheaf.pullbackIso CommRingCat.{u} q.base).app Y.toSheafedSpace.sheaf).hom ≫
    CategoryTheory.sheafifyLift _ (inverseImageAdjunct q) Z.IsSheaf

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison map extends the presheaf adjunct**, which is the defining property of
`AlgebraicGeometry.LocallyRingedSpace.inverseImageDesc` and the only thing used about it below.

`AlgebraicGeometry.LocallyRingedSpace.toInverseImageSheaf` is the sheafification map followed by
the inverse of `TopCat.Sheaf.pullbackIso`, so composing it with the `hom` of that isomorphism
leaves `CategoryTheory.toSheafify_sheafifyLift`. -/
theorem toInverseImageSheaf_inverseImageDesc :
    toInverseImageSheaf Y q.base ≫ inverseImageDesc q = inverseImageAdjunct q := by
  rw [inverseImageDesc, toInverseImageSheaf, ← CategoryTheory.Functor.mapIso_inv,
    ← CategoryTheory.Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
    CategoryTheory.toSheafify_sheafifyLift]

/-- The comparison morphism `Z ⟶ q.base⁻¹Y` of *presheafed* spaces: the identity downstairs, and
`AlgebraicGeometry.LocallyRingedSpace.inverseImageDesc` upstairs.

**No transport appears in the type.** The carrier of `q.base⁻¹Y` is that of `Z` on the nose, and
`(TopCat.Presheaf.pushforward CommRingCat (𝟙 _)).obj Z.presheaf` is `Z.presheaf` on the nose, so
the field `c` of a morphism with identity base is literally a map `p⁻¹𝒪_Y ⟶ 𝒪_Z`. -/
def toInverseImageAux : Z.toPresheafedSpace.Hom (inverseImage Y q.base).toPresheafedSpace where
  base := 𝟙 Z.toTopCat
  c := inverseImageDesc q

@[simp]
theorem toInverseImageAux_base : (toInverseImageAux q).base = 𝟙 Z.toTopCat := rfl

@[simp]
theorem toInverseImageAux_c : (toInverseImageAux q).c = inverseImageDesc q := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison morphism of presheafed spaces is a factorisation of `q` through `q.base⁻¹Y`.**

Downstairs this is `Category.id_comp`. Upstairs, the composite's `c` is
`unit ≫ q.base_* (toInverseImageSheaf ≫ inverseImageDesc)`, which is
`unit ≫ q.base_* inverseImageAdjunct` by
`AlgebraicGeometry.LocallyRingedSpace.toInverseImageSheaf_inverseImageDesc` — and that is the
image of `inverseImageAdjunct` under the adjunction's `homEquiv`, hence `q.c`. -/
theorem toInverseImageAux_comp :
    (toInverseImageAux q ≫ inverseImageHomAux Y q.base :
      Z.toPresheafedSpace ⟶ Y.toPresheafedSpace) = q.toHom :=
  PresheafedSpace.ext _ _ (Category.id_comp _) (by
    simp only [eqToHom_refl, Functor.whiskerRight_id']
    change (inverseImageHomAux Y q.base).c ≫
      (TopCat.Presheaf.pushforward CommRingCat.{u} q.base).map (inverseImageDesc q) = _
    rw [inverseImageHomAux_c, Category.assoc, ← Functor.map_comp,
      toInverseImageSheaf_inverseImageDesc, inverseImageAdjunct]
    exact ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.base).homEquiv
      Y.presheaf Z.presheaf).apply_symm_apply q.toHom.c)

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison morphism `Z ⟶ q.base⁻¹Y` of locally ringed spaces.**

Its stalk maps are local because
`AlgebraicGeometry.LocallyRingedSpace.stalkMap_toInverseImage` writes each of them as `q`'s stalk
map preceded by an isomorphism. -/
def toInverseImage : Z ⟶ inverseImage Y q.base where
  toHom := toInverseImageAux q
  prop z := by
    have h : (toInverseImageAux q).stalkMap z =
        CategoryTheory.inv ((inverseImageHomAux Y q.base).stalkMap
          ((toInverseImageAux q).base z)) ≫
        PresheafedSpace.Hom.stalkMap
          (toInverseImageAux q ≫ inverseImageHomAux Y q.base :
            Z.toPresheafedSpace ⟶ Y.toPresheafedSpace) z := by
      rw [PresheafedSpace.stalkMap.comp, IsIso.inv_hom_id_assoc]
    rw [h, PresheafedSpace.stalkMap.congr_hom _ _ (toInverseImageAux_comp q) z]
    haveI : IsLocalHom (q.toHom.stalkMap z).hom := q.prop z
    repeat' apply +allowSynthFailures RingHom.isLocalHom_comp
    all_goals first
      | assumption
      | exact isLocalHom_of_isIso _

/-- **The underlying map of the comparison morphism is the identity**, on the nose. -/
@[simp]
theorem toInverseImage_base : (toInverseImage q).base = 𝟙 Z.toTopCat := rfl

/-- **The comparison morphism is a factorisation of `q` through `q.base⁻¹Y`**, which is what makes
it a morphism over `Y`. -/
theorem toInverseImage_comp : toInverseImage q ≫ inverseImageHom Y q.base = q :=
  Hom.ext' (toInverseImageAux_comp q)

set_option backward.isDefEq.respectTransparency false in
/-- **The stalk map of the comparison morphism is that of `q`, preceded by the identification of
the stalks of `q.base⁻¹Y` with those of `Y`.**

`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_inverseImageHom` is what makes the inverse
available; the content is
`AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp` read on stalks. -/
theorem stalkMap_toInverseImage (z : Z.toTopCat) :
    (toInverseImage q).stalkMap z =
      CategoryTheory.inv ((inverseImageHom Y q.base).stalkMap z) ≫ q.stalkMap z := by
  have h : q.stalkMap z =
      (inverseImageHom Y q.base).stalkMap z ≫ (toInverseImage q).stalkMap z := by
    have h0 := PresheafedSpace.stalkMap.congr_hom _ _ (toInverseImageAux_comp q) z
    rw [PresheafedSpace.stalkMap.comp] at h0
    simp only [eqToHom_refl, Category.id_comp] at h0
    exact h0.symm
  rw [h, IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison morphism is an isomorphism on a stalk wherever `q` is.**

This is the form taxis #1142 consumes: `q.base⁻¹Y ⟶ Y` is an isomorphism on *every* stalk, so the
stalk hypothesis of `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` for the
comparison morphism is a condition on `q` alone — and that hypothesis is an instance argument,
which is why this is one too.

The converse is the same equation read the other way and is not stated, because nothing needs
it. -/
instance isIso_stalkMap_toInverseImage (z : Z.toTopCat) [IsIso (q.stalkMap z)] :
    IsIso ((toInverseImage q).stalkMap z) := by
  rw [stalkMap_toInverseImage]
  infer_instance

end

end AlgebraicGeometry.LocallyRingedSpace

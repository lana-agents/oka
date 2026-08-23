/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
import Oka.Geometry.RingedSpace.OpenImmersion
import Oka.Topology.Sheaves.Stalks

/-!
# Open covers of a locally ringed space, and gluing morphisms out of one

Mathlib glues locally ringed *spaces* — `AlgebraicGeometry.LocallyRingedSpace.GlueData` in
`Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` — but it does not glue *morphisms* out
of one. `AlgebraicGeometry.Scheme.Cover.glueMorphisms` exists and is one of the most-used
pieces of the scheme API; the analogue for a locally ringed space is absent, and this file
supplies it. Material for `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`; see
`README.md` on the mirror tree.

## The shape of the argument, and why it is a port

`CategoryTheory.GlueData.glued` is a `Multicoequalizer`, so mapping *out* of a glued space is
`Multicoequalizer.desc` and is free. All the content is therefore in identifying `X` with the
gluing of the members of a cover of it, i.e. in `IsIso fromGlued`, and that argument is the
scheme-side one with the `Scheme` layer removed:

* `fromGlued` is injective on points, by `GlueData.ι_eq_iff` and the fact that the topological
  pullback computes the intersection;
* it is an isomorphism on stalks, because `ι i ≫ fromGlued = 𝒰.map i` and both of the others are
  open immersions;
* it is an open map, by `GlueData.isOpen_iff`;
* hence it is an open immersion (`IsOpenImmersion.of_stalk_iso`), and it is surjective, so it is
  an isomorphism (`IsOpenImmersion.to_iso`).

**Only the last two steps existed for `LocallyRingedSpace`.** `IsOpenImmersion.of_stalk_iso` and
`IsOpenImmersion.to_iso` are in `Mathlib/Geometry/RingedSpace/OpenImmersion.lean`, as are the
pullbacks of open immersions and their preservation by every forgetful functor in sight. What was
missing, and is supplied here, is the carrier-level API of a `LocallyRingedSpace.GlueData`:
`isoCarrier`, `ι_isoCarrier_inv`, `Rel`, `ι_eq_iff` and `isOpen_iff`, each of which exists for
`Scheme.GlueData` and for no other level of the hierarchy. Their proofs are the scheme-side ones
with one `Iso.trans` removed.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.GlueData.isoCarrier`: the underlying space of a gluing is
  the gluing of the underlying spaces.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover`: an open cover of a locally ringed space.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.gluedCover`: the glue data of an open cover.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.fromGlued`: the canonical morphism from the
  gluing of a cover of `X` to `X`, an isomorphism.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms`: the glued morphism.
- `AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens`: the open cover attached to a family of
  open subsets covering the space.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.opensRange`: the image of a member of a cover,
  as an open subset, with `…OpenCover.isoRestrict` identifying that member with the restriction
  to its image and `…OpenCover.restrictAlgMap` carrying an algebra structure across.
- `AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover`: the members of a glue data are an
  open cover of the glued space.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` and `…GlueData.isOpen_iff`: two points
  of a gluing are equal exactly when they are related in the evident way, and a subset of a
  gluing is open exactly when its preimage in every member is.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.isIso_fromGlued`: **a locally ringed space is
  the gluing of the members of any open cover of it.**
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.iSup_opensRange`: the images of the members of
  a cover cover the space, which is `OpenCover.covers` in the form the cover-indexed API asks
  for.
- `AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms`: **morphisms out of
  the members of an open cover which agree on the overlaps glue to a unique morphism out of the
  whole space**, with `ι_glueMorphisms` and `hom_ext` as the two halves.
- `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'`: the `f_open` field of a glue data
  built by `CategoryTheory.GlueData.ofGlueData'`, which is what makes that route to a
  `AlgebraicGeometry.LocallyRingedSpace.GlueData` cheaper than building one directly.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- The transition maps of the associated glue data of presheafed spaces are open immersions.

This is `PresheafedSpace.GlueData.f_open` of the derived glue data. It has to be restated as an
instance because instance search does not unfold the `abbrev` chain
`toSheafedSpaceGlueData ≫ toPresheafedSpaceGlueData` to find the field; without it, the
`PreservesLimit (cospan _ _) (PresheafedSpace.forget _)` instances that `GlueData.gluedIso`
needs are not found. `Mathlib/AlgebraicGeometry/Gluing.lean` restates the same instances one
level up for the same reason. -/
instance isOpenImmersion_toPresheafedSpaceGlueData_f (i j : D.J) :
    PresheafedSpace.IsOpenImmersion
      (D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f i j) :=
  D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f_open i j

local notation "D_" => TopCat.GlueData.toGlueData <|
  D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

set_option backward.isDefEq.respectTransparency false in
/-- **The underlying topological space of a gluing of locally ringed spaces is the gluing of the
underlying topological spaces.** -/
noncomputable def isoCarrier : 𝖣.glued.carrier ≅ (D_).glued := by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    CategoryTheory.GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, u} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  exact D.isoSheafedSpace

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ι_isoCarrier_inv (i : D.J) :
    (D_).ι i ≫ D.isoCarrier.inv = (𝖣.ι i).base := by
  delta isoCarrier
  rw [Iso.trans_inv, CategoryTheory.GlueData.ι_gluedIso_inv_assoc, Functor.mapIso_inv,
    Iso.trans_inv, Functor.mapIso_inv, SheafedSpace.forgetToPresheafedSpace_map,
    PresheafedSpace.forget_map, PresheafedSpace.forget_map, ← PresheafedSpace.comp_base,
    ← Category.assoc, D.toSheafedSpaceGlueData.ι_isoPresheafedSpace_inv i]
  dsimp
  rw [← PresheafedSpace.comp_base, ← InducedCategory.comp_hom, D.ι_isoSheafedSpace_inv i]
  rfl

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣.ι i x = 𝖣.ι j y`. -/
def Rel (a b : Σ i, ((D.U i).carrier : Type u)) : Prop :=
  ∃ x : (D.V (a.1, b.1)).carrier, (D.f _ _).base x = a.2 ∧ (D.t _ _ ≫ D.f _ _).base x = b.2

set_option backward.isDefEq.respectTransparency false in
theorem ι_eq_iff (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier) :
    (𝖣.ι i).base x = (𝖣.ι j).base y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  refine Iff.trans ?_ (TopCat.GlueData.ι_eq_iff_rel
    D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData i j x y)
  rw [← ((TopCat.mono_iff_injective D.isoCarrier.inv).mp ?_).eq_iff, ← ConcreteCategory.comp_apply]
  · simp_rw [← D.ι_isoCarrier_inv]
    rfl
  · infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem isOpen_iff (U : Set 𝖣.glued.carrier) : IsOpen U ↔ ∀ i, IsOpen ((𝖣.ι i).base ⁻¹' U) := by
  rw [← (TopCat.homeoOfIso D.isoCarrier.symm).isOpen_preimage, TopCat.GlueData.isOpen_iff]
  refine forall_congr' fun i ↦ ?_
  rw [← Set.preimage_comp, ← ι_isoCarrier_inv]
  rfl

end AlgebraicGeometry.LocallyRingedSpace.GlueData

namespace AlgebraicGeometry.LocallyRingedSpace

/-- An open cover of a locally ringed space. -/
structure OpenCover (X : LocallyRingedSpace.{u}) where
  /-- The index type of the cover. -/
  J : Type u
  /-- The locally ringed space covering `X` at the index `j`. -/
  obj : J → LocallyRingedSpace.{u}
  /-- The open immersion of the `j`-th member of the cover into `X`. -/
  map : ∀ j, obj j ⟶ X
  /-- For each point of `X`, an index whose member of the cover contains it. -/
  idx : X → J
  /-- The chosen member of the cover really does contain the point. -/
  covers : ∀ x, x ∈ Set.range (map (idx x)).base
  /-- Each member of the cover is an open immersion. -/
  [isOpen : ∀ j, IsOpenImmersion (map j)]

attribute [instance] OpenCover.isOpen

namespace OpenCover

variable {X : LocallyRingedSpace.{u}} (𝒰 : OpenCover X)

/-- (Implementation) the transition maps in the glue data associated with an open cover. -/
noncomputable def gluedCoverT' (x y z : 𝒰.J) :
    Limits.pullback (Limits.pullback.fst (𝒰.map x) (𝒰.map y))
        (Limits.pullback.fst (𝒰.map x) (𝒰.map z)) ⟶
      Limits.pullback (Limits.pullback.fst (𝒰.map y) (𝒰.map z))
        (Limits.pullback.fst (𝒰.map y) (𝒰.map x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_fst_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_fst_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_snd_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta gluedCoverT'; simp

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
theorem gluedCoverT'_snd_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta gluedCoverT'; simp

theorem glued_cover_cocycle_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp

theorem glued_cover_cocycle_snd (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

theorem glued_cover_cocycle (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ 𝒰.gluedCoverT' y z x ≫ 𝒰.gluedCoverT' z x y = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply glued_cover_cocycle_fst
  · apply glued_cover_cocycle_snd

/-- The glue data associated with an open cover. -/
@[simps]
noncomputable def gluedCover : GlueData.{u} where
  J := 𝒰.J
  U := 𝒰.obj
  V := fun ⟨x, y⟩ => pullback (𝒰.map x) (𝒰.map y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := 𝒰.gluedCoverT' x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  cocycle x y z := 𝒰.glued_cover_cocycle x y z
  f_open _ := inferInstance

/-- The canonical morphism from the gluing of an open cover of `X` into `X`. -/
noncomputable def fromGlued : 𝒰.gluedCover.toGlueData.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun x => 𝒰.map x
  rintro ⟨x, y⟩
  change pullback.fst _ _ ≫ _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ _
  simpa using! pullback.condition

@[simp, reassoc]
theorem ι_fromGlued (x : 𝒰.J) : 𝒰.gluedCover.toGlueData.ι x ≫ 𝒰.fromGlued = 𝒰.map x :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem fromGlued_injective : Function.Injective 𝒰.fromGlued.base := by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective y
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply] at h
  simp_rw [← LocallyRingedSpace.comp_base] at h
  rw [ι_fromGlued, ι_fromGlued] at h
  let e :=
    (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
      (isLimitOfHasPullbackOfPreservesLimit
        (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat)
        (𝒰.map i) (𝒰.map j))
  rw [𝒰.gluedCover.ι_eq_iff]
  refine ⟨e.hom ⟨⟨x, y⟩, h⟩, ?_, ?_⟩
  · erw [← ConcreteCategory.comp_apply e.hom,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]
    rfl
  · erw [← ConcreteCategory.comp_apply e.hom, pullbackSymmetry_hom_comp_fst,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance isIso_stalkMap_fromGlued (x : 𝒰.gluedCover.toGlueData.glued) :
    IsIso (𝒰.fromGlued.stalkMap x) := by
  obtain ⟨i, x, rfl⟩ := 𝒰.gluedCover.ι_jointly_surjective x
  have h := LocallyRingedSpace.stalkMap_congr_hom _ _ (𝒰.ι_fromGlued i) x
  rw [LocallyRingedSpace.stalkMap_comp, ← IsIso.eq_comp_inv] at h
  have heq : ((𝒰.gluedCover.toGlueData.ι i ≫ 𝒰.fromGlued).base) x = (𝒰.map i).base x := by
    rw [𝒰.ι_fromGlued i]
    rfl
  haveI := TopCat.Presheaf.isIso_stalkSpecializes_of_eq X.presheaf
    (specializes_of_eq heq.symm) heq
  rw [h]
  infer_instance

theorem base_map_eq (j : 𝒰.J) :
    ⇑(𝒰.map j).base = ⇑𝒰.fromGlued.base ∘ ⇑(𝒰.gluedCover.toGlueData.ι j).base := by
  rw [← 𝒰.ι_fromGlued j]
  rfl

theorem preimage_image_fromGlued (j : 𝒰.J) (U : Set 𝒰.gluedCover.toGlueData.glued) :
    ⇑(𝒰.map j).base ⁻¹' (⇑𝒰.fromGlued.base '' U) = ⇑(𝒰.gluedCover.toGlueData.ι j).base ⁻¹' U := by
  ext y
  simp only [Set.mem_preimage, Set.mem_image, 𝒰.base_map_eq j, Function.comp_apply]
  constructor
  · rintro ⟨z, hz, hzy⟩
    rwa [𝒰.fromGlued_injective hzy] at hz
  · exact fun hy ↦ ⟨_, hy, rfl⟩

theorem isOpenMap_fromGlued : IsOpenMap ⇑𝒰.fromGlued.base := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨⇑𝒰.fromGlued.base '' U ∩ Set.range ⇑(𝒰.map (𝒰.idx x)).base,
    Set.inter_subset_left, ?_, hx, 𝒰.covers x⟩
  rw [← Set.image_preimage_eq_inter_range, 𝒰.preimage_image_fromGlued]
  exact (𝒰.isOpen (𝒰.idx x)).base_open.isOpenMap _
    ((𝒰.gluedCover.isOpen_iff U).1 hU (𝒰.idx x))

theorem isOpenEmbedding_fromGlued : IsOpenEmbedding ⇑𝒰.fromGlued.base :=
  .of_continuous_injective_isOpenMap 𝒰.fromGlued.base.hom.continuous 𝒰.fromGlued_injective
    𝒰.isOpenMap_fromGlued

instance epi_base_fromGlued : Epi 𝒰.fromGlued.base := by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  exact ⟨(𝒰.gluedCover.toGlueData.ι (𝒰.idx x)).base y,
    (congrFun (𝒰.base_map_eq (𝒰.idx x)).symm y).trans hy⟩

instance isOpenImmersion_fromGlued : IsOpenImmersion 𝒰.fromGlued :=
  IsOpenImmersion.of_stalk_iso _ 𝒰.isOpenEmbedding_fromGlued

instance isIso_fromGlued : IsIso 𝒰.fromGlued :=
  IsOpenImmersion.to_iso _

/-- **Given an open cover of `X` and a morphism out of each member of the cover which agree on
the overlaps, they glue to a morphism out of `X`.** -/
noncomputable def glueMorphisms {Y : LocallyRingedSpace.{u}} (f : ∀ j, 𝒰.obj j ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y) :
    X ⟶ Y := by
  refine inv 𝒰.fromGlued ≫ ?_
  fapply Multicoequalizer.desc
  · exact fun i ↦ f i
  rintro ⟨i, j⟩
  change pullback.fst _ _ ≫ f _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ f _
  rw [pullbackSymmetry_hom_comp_fst]
  exact hf i j

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_glueMorphisms {Y : LocallyRingedSpace.{u}} (f : ∀ j, 𝒰.obj j ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y) (x : 𝒰.J) :
    𝒰.map x ≫ 𝒰.glueMorphisms f hf = f x := by
  rw [glueMorphisms, ← 𝒰.ι_fromGlued x, Category.assoc, IsIso.hom_inv_id_assoc]
  exact Multicoequalizer.π_desc _ _ _ _ _

theorem hom_ext {Y : LocallyRingedSpace.{u}} (f₁ f₂ : X ⟶ Y)
    (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂ := by
  rw [← cancel_epi 𝒰.fromGlued]
  refine Multicoequalizer.hom_ext _ _ _ fun x ↦ ?_
  change 𝒰.gluedCover.toGlueData.ι x ≫ 𝒰.fromGlued ≫ f₁ =
    𝒰.gluedCover.toGlueData.ι x ≫ 𝒰.fromGlued ≫ f₂
  rw [𝒰.ι_fromGlued_assoc, 𝒰.ι_fromGlued_assoc]
  exact h x

/-- **The glued morphism is the unique one restricting to the given ones on the cover.** -/
theorem existsUnique_glueMorphisms {Y : LocallyRingedSpace.{u}} (f : ∀ j, 𝒰.obj j ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y) :
    ∃! φ : X ⟶ Y, ∀ j, 𝒰.map j ≫ φ = f j :=
  ⟨𝒰.glueMorphisms f hf, 𝒰.ι_glueMorphisms f hf, fun _ hφ ↦
    𝒰.hom_ext _ _ fun j ↦ (hφ j).trans (𝒰.ι_glueMorphisms f hf j).symm⟩

/-! ### The members of a cover as open subspaces

An `OpenCover`'s members are arbitrary locally ringed spaces mapping into `X` by open immersions,
which is what a `GlueData` produces; the constructions that consume a cover — notably
`ComplexAnalytic.AnalyticSpace.ofOpens` — take a family of *opens* of `X` and restrict. The three
declarations below are the dictionary: the image of a member as an open subset, the fact that
those images cover, and the isomorphism between a member and the restriction to its image.

The isomorphism is `IsOpenImmersion.isoOfRangeEq` and the range equality is `range_ofRestrict`,
so nothing here is a computation; what it buys is that a property or a structure known on the
members can be transported to the restrictions, where the cover-indexed API lives.
-/

/-- **The image of the `j`-th member of an open cover, as an open subset of `X`.** -/
def opensRange (j : 𝒰.J) : Opens X :=
  ⟨Set.range (𝒰.map j).base, (𝒰.isOpen j).base_open.isOpen_range⟩

@[simp]
lemma coe_opensRange (j : 𝒰.J) : (𝒰.opensRange j : Set X) = Set.range (𝒰.map j).base :=
  rfl

/-- **The images of the members of an open cover cover `X`**, which is `OpenCover.covers` in the
form the cover-indexed API asks for. -/
lemma iSup_opensRange : ⨆ j, 𝒰.opensRange j = ⊤ :=
  Opens.ext <| Set.eq_univ_of_forall fun x ↦ by
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨𝒰.idx x, 𝒰.covers x⟩

/-- **A member of an open cover is the open subspace of `X` on its image.**

Both `𝒰.map j` and `X.ofRestrict (𝒰.opensRange j).isOpenEmbedding` are open immersions with the
same image — by `range_ofRestrict`, and for the second one that is a definitional unfolding of
`opensRange` — so `IsOpenImmersion.isoOfRangeEq` identifies their sources. -/
noncomputable def isoRestrict (j : 𝒰.J) :
    X.restrict (𝒰.opensRange j).isOpenEmbedding ≅ 𝒰.obj j :=
  IsOpenImmersion.isoOfRangeEq _ _ (X.range_ofRestrict (𝒰.opensRange j))

@[reassoc (attr := simp)]
lemma isoRestrict_hom_fac (j : 𝒰.J) :
    (𝒰.isoRestrict j).hom ≫ 𝒰.map j = X.ofRestrict (𝒰.opensRange j).isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- **An algebra structure on a member of the cover, carried to the open subspace of `X` on its
image.** This is `comapAlgMap` along `isoRestrict`, and it is what puts a family of structures
given on abstract members into the indexing `glueAlgMapRestrict` consumes. -/
noncomputable def restrictAlgMap {R : Type*} [NonAssocSemiring R] (j : 𝒰.J)
    (α : R →+* (𝒰.obj j).presheaf.obj (op ⊤)) :
    R →+* (X.restrict (𝒰.opensRange j).isOpenEmbedding).presheaf.obj (op ⊤) :=
  comapAlgMap (𝒰.isoRestrict j).hom α

/-- **If the structure on a member is pulled back from one on `X`, carrying it to the open
subspace gives the restriction of that structure.**

This is what makes the gluing of `ComplexAnalytic.AnalyticSpace.ofOpenCover` checkable: it turns
a family that came from an ambient structure back into the family of its restrictions, on which
compatibility is `isCompatible_map_le_top` and the gluing is `glueSection_map_le_top`. The proof
is `isoRestrict_hom_fac` read through `comapAlgMap_comp`; nothing is computed. -/
lemma restrictAlgMap_comapAlgMap {R : Type*} [NonAssocSemiring R] (j : 𝒰.J)
    (γ : R →+* X.presheaf.obj (op ⊤)) :
    𝒰.restrictAlgMap j (comapAlgMap (𝒰.map j) γ) = X.resAlgMap γ (𝒰.opensRange j) := by
  rw [restrictAlgMap, ← comapAlgMap_comp, isoRestrict_hom_fac, comapAlgMap_ofRestrict]

/-- **A family of structures pulled back from one on `X` is compatible on the overlaps**, so it
satisfies the hypothesis of `glueAlgMapRestrict` with nothing to check.

Every member of the carried family is a restriction of the single global section `γ c`, by
`restrictAlgMap_comapAlgMap`, and `isCompatible_map_le_top` is exactly that case. This is the
hypothesis-discharging half of `glueAlgMapRestrict_comapAlgMap` below, and it is
stated separately because a caller of `ComplexAnalytic.AnalyticSpace.ofOpenCover` needs it before
it can name the space the theorem is about. -/
theorem isCompatible_restrictAlgMap_comapAlgMap {R : Type*} [NonAssocSemiring R]
    (γ : R →+* X.presheaf.obj (op ⊤)) (c : R) :
    TopCat.Presheaf.IsCompatible X.presheaf
      (fun j ↦ (𝒰.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun j ↦ 𝒰.restrictAlgMap j (comapAlgMap (𝒰.map j) γ) c := by
  have key : (fun j ↦ 𝒰.restrictAlgMap j (comapAlgMap (𝒰.map j) γ) c) =
      fun j ↦ (X.presheaf.map (homOfLE (le_top :
        (𝒰.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤ ≤ ⊤)).op).hom (γ c) :=
    funext fun j ↦ congrArg (fun m : R →+* _ ↦ m c) (𝒰.restrictAlgMap_comapAlgMap j γ)
  rw [key]
  exact isCompatible_map_le_top _

/-- **Gluing the family a global structure induces on the members of a cover returns that
structure**: the round trip, in the `OpenCover` indexing.

`glueSection_map_le_top` is the same statement for a single section and is what this reduces to;
the content is `restrictAlgMap_comapAlgMap`, which says the carried family *is* the family of
restrictions. It is what identifies the output of `ComplexAnalytic.AnalyticSpace.ofOpenCover` on
a cover of a space that already carries a structure — and note that it makes no reference to the
members being restrictions, which is the point of the whole section. -/
theorem glueAlgMapRestrict_comapAlgMap {R : Type*} [CommRing R]
    (γ : R →+* X.presheaf.obj (op ⊤)) :
    glueAlgMapRestrict 𝒰.iSup_opensRange
        (fun j ↦ 𝒰.restrictAlgMap j (comapAlgMap (𝒰.map j) γ))
        (𝒰.isCompatible_restrictAlgMap_comapAlgMap γ) = γ :=
  RingHom.ext fun c ↦
    glueSection_eq ((iSup_isOpenEmbedding_obj_top _).trans 𝒰.iSup_opensRange) _
      (𝒰.isCompatible_restrictAlgMap_comapAlgMap γ c) (γ c)
      fun j ↦ (congrArg (fun m : R →+* _ ↦ m c) (𝒰.restrictAlgMap_comapAlgMap j γ)).symm

end OpenCover

/-- **A family of open subsets covering `X` is an open cover of `X`** by the corresponding open
subspaces. This is the form in which an open cover of a locally ringed space usually arises: the
members are restrictions of `X` itself rather than abstract spaces mapping into it. -/
noncomputable def openCoverOfOpens {X : LocallyRingedSpace.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) : OpenCover X where
  J := ι
  obj i := X.restrict (U i).isOpenEmbedding
  map _ := X.ofRestrict _
  idx x := (hU x).choose
  covers x := ⟨⟨x, (hU x).choose_spec⟩, rfl⟩
  isOpen _ := inferInstance

@[simp]
lemma openCoverOfOpens_obj {X : LocallyRingedSpace.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (i : ι) :
    (openCoverOfOpens U hU).obj i = X.restrict (U i).isOpenEmbedding :=
  rfl

@[simp]
lemma openCoverOfOpens_map {X : LocallyRingedSpace.{u}} {ι : Type u} (U : ι → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (i : ι) :
    (openCoverOfOpens U hU).map i = X.ofRestrict (U i).isOpenEmbedding :=
  rfl

/-- **The members of a glue data are an open cover of the glued space.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion` and
`…GlueData.ι_jointly_surjective` are Mathlib's; this packages them, and it is the form in which
a gluing is fed to anything that consumes a cover. It is the converse direction to
`OpenCover.gluedCover`, and unlike `OpenCover.isIso_fromGlued` it costs nothing.

The index of a point is *chosen*, so this definition is noncomputable and non-canonical in the
same way `openCoverOfOpens` is; nothing downstream depends on which index is picked. -/
noncomputable def GlueData.openCover (D : GlueData.{u}) : OpenCover D.toGlueData.glued where
  J := D.J
  obj := D.U
  map := D.toGlueData.ι
  idx x := (D.ι_jointly_surjective x).choose
  covers x := (D.ι_jointly_surjective x).choose_spec

section GlueOverOpens

/-- **Morphisms out of the members of a cover of `X` by open subsets, agreeing on the pairwise
intersections, glue** — and the glued morphism is unique.

`AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms` says the same thing
with the compatibility phrased on the *categorical pullback* of the two inclusions. That object
is opaque: to discharge the hypothesis one has to know what its points are, and the tools that
would discharge it — anything of the form "two morphisms out of this space with the same
so-and-so are equal" — are statements about spaces one can name. **So the hypothesis there is
not checkable by the machinery meant to check it**, which is why nothing has consumed that
theorem since it was proved.

Here the compatibility is an equation of morphisms out of `X.restrict (U i ⊓ U j)`, which is an
open subspace of `X` and therefore something the caller already understands — for a complex
analytic space, `ComplexAnalytic.AnalyticSpace.restrict` makes it an analytic space and
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` applies to it.

The identification is
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback`, which packages exactly that: the
pullback of two open immersions has as image the intersection of their images
(`…IsOpenImmersion.range_pullback_to_base_of_left`), so `…IsOpenImmersion.isoOfRangeEq` identifies
it with `X|(U ⊓ V)`. -/
theorem existsUnique_glueMorphisms_of_opens {X Y : LocallyRingedSpace.{u}} {ι : Type u}
    (U : ι → Opens X) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
    (hf : ∀ i j, X.restrictLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.restrictLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    ∃! φ : X ⟶ Y, ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ φ = f i := by
  refine (openCoverOfOpens U hU).existsUnique_glueMorphisms f fun i j ↦ ?_
  change pullback.fst (X.ofRestrict (U i).isOpenEmbedding)
      (X.ofRestrict (U j).isOpenEmbedding) ≫ f i =
    pullback.snd (X.ofRestrict (U i).isOpenEmbedding)
      (X.ofRestrict (U j).isOpenEmbedding) ≫ f j
  rw [← cancel_epi (X.restrictInfIsoPullback (U i) (U j)).hom, ← Category.assoc, ← Category.assoc,
    restrictInfIsoPullback_hom_fst, restrictInfIsoPullback_hom_snd]
  exact hf i j

end GlueOverOpens

section GlueDataPrime

/-- **The morphisms of the glue data `CategoryTheory.GlueData.ofGlueData'` builds are open
immersions as soon as the ones it was given are.**

`CategoryTheory.GlueData'` asks for the overlaps only when `i ≠ j` and discharges `f_id`, `t_id`
and the degenerate branches of `t'`, which is a large part of the obligations of a glue data and
exactly the part that is bookkeeping. What it does not carry is
`AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `f_open` field, and the morphism that field is
checked against is `CategoryTheory.GlueData'.f'`, a `dif` on `i = j`. This says the `dif` costs
nothing: on the diagonal `f'` is an `eqToHom`, hence an isomorphism, hence an open immersion; off
it, it is an `eqToHom` followed by the given morphism.

**Worth stating because `CategoryTheory.GlueData.ofGlueData'` has no call sites in Mathlib at
all** — `grep` finds it only in its own defining file — so it has no projection or `simp` lemmas
and a caller has no way to know in advance which of its fields are cheap to use. This one is; the
`V`, `t` and `t'` fields are not, and nothing in this repository looks at them, since
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` and hence
`ComplexAnalytic.AnalyticSpace.ofGlueData` read only `U`, `ι` and `glued`. -/
theorem isOpenImmersion_f' (D : CategoryTheory.GlueData' LocallyRingedSpace.{u})
    (h : ∀ i j hij, IsOpenImmersion (D.f i j hij)) (i j : D.J) :
    IsOpenImmersion (D.f' i j) := by
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs with hij
  · infer_instance
  · haveI := h i j hij
    infer_instance

end GlueDataPrime

end AlgebraicGeometry.LocallyRingedSpace

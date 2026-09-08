/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.PullbackGlue

/-!
# The lift of a competing cone into the glued fibre product

`Oka/AnalyticSpace/PullbackGlue.lean` glues the ambient pullbacks `Uᵢ ×_Z Y` into an analytic
space `ComplexAnalytic.AnalyticSpace.Pullback.glued` and produces the two projections
`ComplexAnalytic.AnalyticSpace.Pullback.p1`, `…p2` and the commuting square `…p_comm`. Its own
docstring lists what is missing, and the first item is *the lift*: **a competing cone has to be
factored through the gluing.** This file does that half, and the section
*What this does not do* below says what the other half still is.

## The shape Mathlib uses, and the one an open subspace makes available

`Mathlib/AlgebraicGeometry/Pullbacks.lean` covers the vertex of a competing cone `s` by the
fibre products `s.pt ×_X Uᵢ`, taken along `s.fst`, and its `gluedLiftPullbackMap` is a map out of
a pullback of two of those *over `s.pt`* — a fibre product of two fibre products. That shape is
forced there because the members of the cover it pulls back are arbitrary schemes mapping in, so
`s.fst ⁻¹' Uᵢ` is not available there as an object and has to be built.

**Here the members of the family are opens of `X` and nothing has to be built.** The preimage
`(TopologicalSpace.Opens.map s.fst.toLRSHom.base).obj (U i)` is an open of `s.pt`,
`ComplexAnalytic.AnalyticSpace.restrict` at it is the member, and
`AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens` turns the family of preimages into the
cover `ComplexAnalytic.AnalyticSpace.Pullback.coneCover` as soon as the `U i` cover `X`. The map
to the `i`-th piece of the gluing is then
`CategoryTheory.Limits.pullback.lift` of `ComplexAnalytic.AnalyticSpace.restrictHom` and of the
cone's second leg, which is `ComplexAnalytic.AnalyticSpace.Pullback.liftPiece`, and **no pullback
along `s.fst` occurs anywhere in this file.** `CategoryTheory.Limits.pullbackSymmetry`,
`…pullbackRightPullbackFstIso` and `…pullbackAssoc`, which Mathlib's `gluedLiftPullbackMap` and
`gluedLift` are built out of, are named by no proof below.

## The overlaps, and the one comparison that is not free

`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` asks for agreement over
`CategoryTheory.Limits.pullback (𝒰.map i) (𝒰.map j)` — a pullback taken in
`AlgebraicGeometry.LocallyRingedSpace`, of two open-subspace inclusions of `s.pt`. The overlap
this file computes with is the analytic double restriction
`(s.pt|_{s.fst ⁻¹' Uᵢ})|_{s.fst ⁻¹' Uⱼ}`, and
`ComplexAnalytic.AnalyticSpace.isPullback_map_ofRestrict` — which says the image of the
restriction square under `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is a pullback
square downstairs — read as a `CategoryTheory.IsPullback.isoPullback` is the isomorphism between
the two. **That is the only place below where a pullback taken in one of the two categories is
compared with a pullback taken in the other**, it occurs in one proof, and it is
`Oka/AnalyticSpace/PullbackOpen.lean`'s comparison and not a new one; the isomorphism is an
epimorphism, so the compatibility that has to be checked downstairs is discharged by checking it
upstairs.

Upstairs it is two `CategoryTheory.Limits.pullback.lift` computations and the glue condition:
`ComplexAnalytic.AnalyticSpace.Pullback.liftOverlap` is the map from the overlap to
`ComplexAnalytic.AnalyticSpace.Pullback.v`,
`ComplexAnalytic.AnalyticSpace.Pullback.liftOverlap_fV` and `…liftOverlap_t_fV` say that the two
restrictions of the two pieces factor through it along the two legs the glue datum's
`CategoryTheory.GlueData.glue_condition` relates, and that condition does
the rest. **No cocycle lemma of `Oka/AnalyticSpace/PullbackBlock.lean` is named below**, and the
only two facts about the swap that are used are
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_fst` and `…t_fst_snd`.

## Where the covering hypothesis enters, and it is here for the first time

`Oka/AnalyticSpace/PullbackBlock.lean` and `Oka/AnalyticSpace/PullbackGlue.lean` both say in their
headers that the index is a family of opens and not a cover, and neither asks the `U i` to cover
`X`. **`ComplexAnalytic.AnalyticSpace.Pullback.coneCover` is the first declaration of the three
files that does**, as the hypothesis `∀ x : X, ∃ i, x ∈ U i`, and every declaration below it
carries that hypothesis. The **seven** declarations before it —
`ComplexAnalytic.AnalyticSpace.Pullback.liftPiece` with its three factorisation lemmas, and
`…liftOverlap` with its two — do not, and are true of any family.

## The `ℂ`-linearity, which is where the analytic structure is used

`ComplexAnalytic.AnalyticSpace.glueMorphisms` glues morphisms of **analytic** spaces, and its last
argument asks each piece to be `ℂ`-linear for the structure the member inherits from `s.pt`. That
is `ComplexAnalytic.AnalyticSpace.Pullback.isCLinearHom_liftPiece_ι`, and both halves of it are
already stated: `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict` identifies the
structure a member of `ComplexAnalytic.AnalyticSpace.Pullback.coneCover` inherits with the one
`ComplexAnalytic.AnalyticSpace.restrict` gives it, so the first factor is the `isCLinear` field of
`ComplexAnalytic.AnalyticSpace.Pullback.liftPiece`; and
`ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap` says the glued structure
pulls back to the `i`-th member's along the inclusion, which is the second.
`ComplexAnalytic.IsCLinearHom.comp` joins them. **No sheaf argument is written here**; the ones
`Oka/AnalyticSpace/Glue.lean` wrote are what these two lemmas package.

## Main results

- `ComplexAnalytic.AnalyticSpace.Pullback.liftPiece`: **the `i`-th piece of the lift**, from the
  preimage of `U i` in the vertex of the cone to the `i`-th ambient pullback, with
  `…liftPiece_fst`, `…liftPiece_snd` and `…liftPiece_toBase` computing it.
- `ComplexAnalytic.AnalyticSpace.Pullback.liftOverlap`, `…liftOverlap_fV` and
  `…liftOverlap_t_fV`: **the two pieces agree over the overlap**, in the form the glue condition
  consumes.
- `ComplexAnalytic.AnalyticSpace.Pullback.coneCover`: **the cover of the vertex by the preimages**,
  which is where `∀ x : X, ∃ i, x ∈ U i` is used.
- `ComplexAnalytic.AnalyticSpace.Pullback.liftPiece_ι_compatible` and
  `…isCLinearHom_liftPiece_ι`: the two hypotheses
  `ComplexAnalytic.AnalyticSpace.glueMorphisms` asks for.
- `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift`: **the lift**, as a morphism of analytic
  spaces, with `…ofRestrict_gluedLift` saying what it restricts to on a member.
- `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_p1` and `…gluedLift_p2`: **it is a morphism of
  cones** — the two triangles commute.

## What this does not do

**It does not say the lift is unique, and it produces no limit cone.** There is no
`CategoryTheory.Limits.IsLimit` below, no
`CategoryTheory.Limits.HasPullback` and no
`CategoryTheory.Limits.HasPullbacks`; `#synth CategoryTheory.Limits.HasPullbacks
ComplexAnalytic.AnalyticSpace` fails at the commit that adds this file, with the category
**positional**, which is the form that asks about the class rather than about an object.

What uniqueness needs, and what no declaration here supplies, is a factorisation in the other
direction: a morphism `m` into the gluing whose composite with
`ComplexAnalytic.AnalyticSpace.Pullback.p1` lands in `U i` has to be recovered from a morphism
into the `i`-th member, and that asks for the image of
`CategoryTheory.GlueData.ι` to be the preimage of `U i` under
`ComplexAnalytic.AnalyticSpace.Pullback.p1`. **That is a statement about images of points, and no
declaration below states one**: the only points any statement of this file mentions are the points
of `X` in the covering hypothesis, which says nothing about the gluing.

`ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_p1` and `…gluedLift_p2` are, on their own,
existence and not a universal property, and no sentence below calls the gluing a fibre product.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic.AnalyticSpace.Pullback

variable {X Y Z : AnalyticSpace.{u}} {I : Type u} (U : I → X.Opens) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g]
variable (s : PullbackCone f g)

/-! ### The pieces of the lift, and their agreement over the overlaps -/

/-- **The `i`-th piece of the lift.**

On the preimage of `U i` the first leg of the cone factors through `U i`, and that factorisation is
`ComplexAnalytic.AnalyticSpace.restrictHom`; the second leg needs no factorisation. Together with
`CategoryTheory.Limits.PullbackCone.condition` they are a cone over the `i`-th ambient cospan, and
this is the induced map. **Mathlib builds the same morphism out of `s.pt ×_X Uᵢ` instead**, which
is why its version needs `CategoryTheory.Limits.pullbackSymmetry` and
`CategoryTheory.Limits.pullback.map` where this one needs neither. -/
noncomputable def liftPiece (i : I) :
    s.pt.restrict ((Opens.map s.fst.toLRSHom.base).obj (U i)) ⟶
      pullback (X.ofRestrict (U i) ≫ f) g :=
  pullback.lift (restrictHom s.fst (U i))
    (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i)) ≫ s.snd)
    (by rw [← Category.assoc, restrictHom_fac, Category.assoc, Category.assoc, s.condition])

/-- **Its first component is the factorisation of the cone's first leg through `U i`.** -/
@[reassoc (attr := simp)]
theorem liftPiece_fst (i : I) :
    liftPiece U f g s i ≫ pullback.fst _ _ = restrictHom s.fst (U i) :=
  pullback.lift_fst _ _ _

/-- **Its second component is the cone's second leg, restricted.** -/
@[reassoc (attr := simp)]
theorem liftPiece_snd (i : I) :
    liftPiece U f g s i ≫ pullback.snd _ _ =
      s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i)) ≫ s.snd :=
  pullback.lift_snd _ _ _

/-- **Composed with the map to the base it is the cone's first leg**, restricted.

This is `ComplexAnalytic.AnalyticSpace.Pullback.liftPiece_fst` followed by
`ComplexAnalytic.AnalyticSpace.restrictHom_fac`, and it is the form
`ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_p1` consumes:
`ComplexAnalytic.AnalyticSpace.Pullback.toBase` is what
`ComplexAnalytic.AnalyticSpace.Pullback.p1` restricts to on a member. -/
@[reassoc]
theorem liftPiece_toBase (i : I) :
    liftPiece U f g s i ≫ toBase U f g i =
      s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i)) ≫ s.fst := by
  rw [toBase, ← Category.assoc, liftPiece_fst, restrictHom_fac]

/-- **The map from the overlap of two members to the overlap of the glue datum.**

The source is the preimage of `s.fst ⁻¹' Uⱼ` in `s.pt|_{s.fst ⁻¹' Uᵢ}`, which is the analytic
overlap of the `i`-th and `j`-th members of
`ComplexAnalytic.AnalyticSpace.Pullback.coneCover`, and the target is
`ComplexAnalytic.AnalyticSpace.Pullback.v`. The two legs are the `i`-th piece of the lift and the
factorisation of the cone's first leg through `U j`, and the square they have to make commute is
`ComplexAnalytic.AnalyticSpace.restrictHom_fac` at the inclusion of one preimage into the other.

**This is what replaces Mathlib's `gluedLiftPullbackMap`**, whose source is a fibre product of two
fibre products; here it is a restriction of a restriction, and the proof is one `rw` chain out of
`ComplexAnalytic.AnalyticSpace.Pullback.liftPiece_toBase` and two
`ComplexAnalytic.AnalyticSpace.restrictHom_fac`s. -/
noncomputable def liftOverlap (i j : I) :
    (s.pt.restrict ((Opens.map s.fst.toLRSHom.base).obj (U i))).restrict
        ((Opens.map (s.pt.ofRestrict
            ((Opens.map s.fst.toLRSHom.base).obj (U i))).toLRSHom.base).obj
          ((Opens.map s.fst.toLRSHom.base).obj (U j))) ⟶ v U f g i j :=
  pullback.lift
    ((s.pt.restrict _).ofRestrict _ ≫ liftPiece U f g s i)
    (restrictHom (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))) _ ≫
      restrictHom s.fst (U j))
    (by
      rw [Category.assoc, liftPiece_toBase, Category.assoc, restrictHom_fac,
        ← Category.assoc, ← Category.assoc, restrictHom_fac])

/-- **The `i`-th piece, restricted to the overlap, factors through it along `fV i j`.**
One `CategoryTheory.Limits.pullback.lift_fst`. -/
@[reassoc]
theorem liftOverlap_fV (i j : I) :
    liftOverlap U f g s i j ≫ fV U f g i j =
      (s.pt.restrict _).ofRestrict _ ≫ liftPiece U f g s i :=
  pullback.lift_fst _ _ _

/-- **The `j`-th piece, restricted to the overlap, factors through it along the other leg** — the
one the glue datum's `CategoryTheory.GlueData.glue_condition` puts opposite
the first, namely `ComplexAnalytic.AnalyticSpace.Pullback.t` followed by `…fV j i`.

Checked on the two projections of the `j`-th ambient pullback. The first uses
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_fst`, which turns the composite into the second leg
of `ComplexAnalytic.AnalyticSpace.Pullback.liftOverlap`; the second uses `…t_fst_snd`, which turns
it into the first, and then the two second components of the pieces differ by exactly the square
`ComplexAnalytic.AnalyticSpace.restrictHom_fac` supplies. **These are the only two facts about the
swap that this file uses.** -/
@[reassoc]
theorem liftOverlap_t_fV (i j : I) :
    liftOverlap U f g s i j ≫ t U f g i j ≫ fV U f g j i =
      restrictHom (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))) _ ≫
        liftPiece U f g s j := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, t_fst_fst, liftOverlap, pullback.lift_snd,
      Category.assoc, liftPiece_fst]
  · rw [Category.assoc, Category.assoc, t_fst_snd, ← Category.assoc, liftOverlap,
      pullback.lift_fst, Category.assoc, liftPiece_snd, Category.assoc, liftPiece_snd,
      ← Category.assoc, ← Category.assoc, restrictHom_fac]

/-! ### The cover of the vertex, and the two hypotheses the gluing asks for -/

/-- **The cover of the vertex of the cone by the preimages of the members of the family.**

`AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens` at the preimages, whose covering
hypothesis is the covering hypothesis on the `U i` transported along the cone's first leg — a
point of `s.pt` lies over a point of `X`, and any member containing that point has a preimage
containing it. **This is the first declaration on this line to ask that the family cover `X`.** -/
noncomputable def coneCover (hU : ∀ x : X, ∃ i, x ∈ U i) :
    s.pt.toLocallyRingedSpace.OpenCover :=
  LocallyRingedSpace.openCoverOfOpens
    (fun i ↦ (Opens.map s.fst.toLRSHom.base).obj (U i)) fun _ ↦ hU _

omit [∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g] in
/-- **Its `i`-th member is the open subspace at the preimage.** -/
@[simp]
theorem coneCover_obj (hU : ∀ x : X, ∃ i, x ∈ U i) (i : I) :
    (coneCover U f g s hU).obj i =
      (s.pt.restrict ((Opens.map s.fst.toLRSHom.base).obj (U i))).toLocallyRingedSpace :=
  rfl

omit [∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g] in
/-- **And its `i`-th map is that subspace's inclusion**, read one category down, which is the
spelling `AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` states its hypotheses
in. -/
@[simp]
theorem coneCover_map (hU : ∀ x : X, ∃ i, x ∈ U i) (i : I) :
    (coneCover U f g s hU).map i =
      forgetToLocallyRingedSpace.map
        (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))) :=
  rfl

/-- **The pieces agree over the overlaps**, which is the hypothesis
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` asks for.

The equation is between morphisms out of a pullback taken in
`AlgebraicGeometry.LocallyRingedSpace`, and
`ComplexAnalytic.AnalyticSpace.isPullback_map_ofRestrict` identifies that pullback with the image
of the analytic double restriction. The identification is an isomorphism, hence an epimorphism, so
cancelling it leaves an equation between images of analytic morphisms, and there
`ComplexAnalytic.AnalyticSpace.Pullback.liftOverlap_fV` and `…liftOverlap_t_fV` put both sides on
the two ends of `CategoryTheory.GlueData.glue_condition`. **Nothing about
pullbacks is proved downstairs**; the comparison is the one
`Oka/AnalyticSpace/PullbackOpen.lean` already states. -/
theorem liftPiece_ι_compatible (i j : I) :
    pullback.fst
        (forgetToLocallyRingedSpace.map
          (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))))
        (forgetToLocallyRingedSpace.map
          (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U j)))) ≫
      forgetToLocallyRingedSpace.map (liftPiece U f g s i) ≫ (gluing U f g).toGlueData.ι i =
    pullback.snd _ _ ≫
      forgetToLocallyRingedSpace.map (liftPiece U f g s j) ≫ (gluing U f g).toGlueData.ι j := by
  have H := isPullback_map_ofRestrict
    (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i)))
    ((Opens.map s.fst.toLRSHom.base).obj (U j))
  rw [← cancel_epi H.isoPullback.hom, H.isoPullback_hom_fst_assoc,
    H.isoPullback_hom_snd_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← liftOverlap_fV, ← liftOverlap_t_fV, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, Category.assoc]
  exact congrArg _ ((gluing U f g).glue_condition i j).symm

/-- **Each piece is `ℂ`-linear**, which is the hypothesis
`ComplexAnalytic.AnalyticSpace.glueMorphisms` adds to the ones its locally-ringed-space analogue
asks for.

Two field projections joined by `ComplexAnalytic.IsCLinearHom.comp`.
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict` says the structure the member
inherits from `s.pt` along the inclusion is the one
`ComplexAnalytic.AnalyticSpace.restrict` puts on it, so the first factor is the `isCLinear` field
of `ComplexAnalytic.AnalyticSpace.Pullback.liftPiece`;
`ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap` says the glued structure
pulls back along the inclusion of a member to that member's, which with
`ComplexAnalytic.isCLinearHom_comapAlgMap` is the second. -/
theorem isCLinearHom_liftPiece_ι (i : I) :
    IsCLinearHom
      (forgetToLocallyRingedSpace.map (liftPiece U f g s i) ≫ (gluing U f g).toGlueData.ι i)
      (LocallyRingedSpace.comapAlgMap
        (forgetToLocallyRingedSpace.map
          (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i)))) s.pt.algebraMap)
      (glued U f g).algebraMap := by
  refine IsCLinearHom.comp (β := (pullback (X.ofRestrict (U i) ≫ f) g).algebraMap) ?_ ?_
  · have h : LocallyRingedSpace.comapAlgMap
        (forgetToLocallyRingedSpace.map
          (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i)))) s.pt.algebraMap =
        (s.pt.restrict ((Opens.map s.fst.toLRSHom.base).obj (U i))).algebraMap :=
      LocallyRingedSpace.comapAlgMap_ofRestrict _ _ _
    rw [h]
    exact (liftPiece U f g s i).isCLinear
  · rw [← comapAlgMap_ofGlueDataCLinear_algebraMap (gluing U f g) _
      (glueDataCLinear_gluing U f g) _ i]
    exact isCLinearHom_comapAlgMap _ _

/-! ### The lift, and the two triangles -/

/-- **The lift of a competing cone into the gluing**, as a morphism of analytic spaces.

`ComplexAnalytic.AnalyticSpace.glueMorphisms` at
`ComplexAnalytic.AnalyticSpace.Pullback.coneCover`, with the pieces
`ComplexAnalytic.AnalyticSpace.Pullback.liftPiece` followed into the gluing by the member
inclusions of the glue datum, and the two hypotheses supplied by
`ComplexAnalytic.AnalyticSpace.Pullback.liftPiece_ι_compatible` and `…isCLinearHom_liftPiece_ι`.
**It is not claimed to be the only such morphism**; nothing below is a uniqueness statement. -/
noncomputable def gluedLift (hU : ∀ x : X, ∃ i, x ∈ U i) : s.pt ⟶ glued U f g :=
  glueMorphisms (coneCover U f g s hU)
    (fun i ↦ forgetToLocallyRingedSpace.map (liftPiece U f g s i) ≫ (gluing U f g).toGlueData.ι i)
    (fun i j ↦ liftPiece_ι_compatible U f g s i j)
    (fun i ↦ isCLinearHom_liftPiece_ι U f g s i)

/-- **It restricts to the `i`-th piece on the `i`-th member of the cover**, which is what a caller
consumes and what both triangles below are checked with.

The statement is about the underlying morphisms of locally ringed spaces, for the reason
`ComplexAnalytic.AnalyticSpace.Pullback.ι_p1` is: the member inclusions of a glue datum are
morphisms of locally ringed spaces and the members are not objects of
`ComplexAnalytic.AnalyticSpace`. -/
@[reassoc]
theorem ofRestrict_gluedLift (hU : ∀ x : X, ∃ i, x ∈ U i) (i : I) :
    forgetToLocallyRingedSpace.map
          (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))) ≫
        (gluedLift U f g s hU).toLRSHom =
      forgetToLocallyRingedSpace.map (liftPiece U f g s i) ≫ (gluing U f g).toGlueData.ι i :=
  ι_glueMorphisms (coneCover U f g s hU) _ _ _ i

/-- **The first triangle commutes.**

Checked member by member: `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful,
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.hom_ext` reduces the equation to one on each
member of `ComplexAnalytic.AnalyticSpace.Pullback.coneCover`, and there
`ComplexAnalytic.AnalyticSpace.Pullback.ofRestrict_gluedLift` and `…ι_p1` turn the left side into
the image of `ComplexAnalytic.AnalyticSpace.Pullback.liftPiece_toBase`'s.

**The steps after the `rw` are terms and not tactics on purpose.** After
`ComplexAnalytic.AnalyticSpace.Pullback.ofRestrict_gluedLift` fires, the goal mentions
`CategoryTheory.GlueData.ι` at an index whose type is the datum's `J` and
whose value has type `I`; the two are definitionally equal but `rw` type-checks its target at
`instances` transparency and refuses, while `exact` checks at default transparency and does
not. -/
theorem gluedLift_p1 (hU : ∀ x : X, ∃ i, x ∈ U i) :
    gluedLift U f g s hU ≫ p1 U f g = s.fst := by
  have key : ∀ i : I,
      forgetToLocallyRingedSpace.map
            (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))) ≫
          (gluedLift U f g s hU ≫ p1 U f g).toLRSHom =
        forgetToLocallyRingedSpace.map
          (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))) ≫ s.fst.toLRSHom := by
    intro i
    change forgetToLocallyRingedSpace.map _ ≫
      (gluedLift U f g s hU).toLRSHom ≫ (p1 U f g).toLRSHom = _
    rw [← Category.assoc, ofRestrict_gluedLift]
    exact (Category.assoc _ _ _).trans
      ((congrArg (forgetToLocallyRingedSpace.map (liftPiece U f g s i) ≫ ·) (ι_p1 U f g i)).trans
        (congrArg forgetToLocallyRingedSpace.map (liftPiece_toBase U f g s i)))
  apply forgetToLocallyRingedSpace.map_injective
  exact (coneCover U f g s hU).hom_ext _ _ fun i ↦ key i

/-- **The second triangle commutes**, by the same reduction with
`ComplexAnalytic.AnalyticSpace.Pullback.ι_p2` and
`ComplexAnalytic.AnalyticSpace.Pullback.liftPiece_snd` in place of `…ι_p1` and
`…liftPiece_toBase`. -/
theorem gluedLift_p2 (hU : ∀ x : X, ∃ i, x ∈ U i) :
    gluedLift U f g s hU ≫ p2 U f g = s.snd := by
  have key : ∀ i : I,
      forgetToLocallyRingedSpace.map
            (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))) ≫
          (gluedLift U f g s hU ≫ p2 U f g).toLRSHom =
        forgetToLocallyRingedSpace.map
          (s.pt.ofRestrict ((Opens.map s.fst.toLRSHom.base).obj (U i))) ≫ s.snd.toLRSHom := by
    intro i
    change forgetToLocallyRingedSpace.map _ ≫
      (gluedLift U f g s hU).toLRSHom ≫ (p2 U f g).toLRSHom = _
    rw [← Category.assoc, ofRestrict_gluedLift]
    exact (Category.assoc _ _ _).trans
      ((congrArg (forgetToLocallyRingedSpace.map (liftPiece U f g s i) ≫ ·) (ι_p2 U f g i)).trans
        (congrArg forgetToLocallyRingedSpace.map (liftPiece_snd U f g s i)))
  apply forgetToLocallyRingedSpace.map_injective
  exact (coneCover U f g s hU).hom_ext _ _ fun i ↦ key i

end ComplexAnalytic.AnalyticSpace.Pullback

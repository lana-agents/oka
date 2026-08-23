/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Glue
import OkaTest.AnalyticSpaceLocal

/-!
# `AnalyticSpace.ofOpenCover` is applied to a cover whose members are not open subsets

`ComplexAnalytic.AnalyticSpace.ofOpenCover` would be `…ofOpensCompatible` wearing a hat if the
only covers it were ever applied to had members of the form `X.restrict U` mapping in by
`X.ofRestrict U`. **That is the degeneracy to rule out here**, and it is the live one: before
this file the only open cover the development constructed was
`AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens`, whose members are exactly restrictions
and whose maps are exactly the inclusions.

The cover below is the two punctured copies of `ℂ` of `OkaTest/AnalyticSpaceLocal.lean` — reused,
so that `cover_ne_top` continues to guard against a member being the whole space — with each
member presented as `(ℂ|Uᵢ)|⊤` rather than as `ℂ|Uᵢ`. It is of course *isomorphic* to `ℂ|Uᵢ`;
what matters is that it is not of the form `X.restrict V` — its carrier is a subtype of a
subtype — so `AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict` at it is a genuine
`isoOfRangeEq` between two different presentations, and the charts and the `ℂ`-algebra structure
have to be carried across it.

## What this does and does not rule out

It checks that a cover by abstract members is accepted and that the glued `ℂ`-algebra structure
is the one the members came from — a **round trip**, the same one
`OkaTest/AnalyticSpaceLocal.lean` runs for `ofOpensCompatible`. As recorded there, a round trip
is the strongest test available while every space in the development already carries a global
`ℂ`-algebra structure: on a sheaf, every compatible family over a cover of `⊤` *is* the
restriction family of a unique global section, so there is no independent input to feed in.

**The last section goes further**, and it is what the round trip cannot do on its own: it runs
`ComplexAnalytic.AnalyticSpace.ofGlueData` on the *glued* space of this cover — a
multicoequalizer, which is not a `restrict` of anything and carries no `ℂ`-algebra structure
until the gluing puts one there. The structures on the pieces are still pullbacks of a single
structure on that space, so it is still a round trip in the sense above; what is new is that the
space being given a structure is produced by the gluing rather than assumed.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.AnalyticSpaceGlue

open OkaTest.AnalyticSpaceLocal (a b a_ne_b cover iSup_cover cover_ne_top)

/-- `ℂ` as a locally ringed space, with no analytic structure attached: the space the cover below
covers, and the space the gluing produces a structure on. -/
abbrev line : LocallyRingedSpace.{u} := complexAffineSpace.{u} 1

/-- The constants of `ℂ`, which is the structure the round trip below has to return. -/
def constants : ℂ →+* (line.{u}).presheaf.obj (op ⊤) :=
  (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap

/-- The punctured plane `ℂ|Uᵢ`, indexed so that the index type lives in the universe an
`AlgebraicGeometry.LocallyRingedSpace.OpenCover` requires. -/
abbrev restrictedLine (i : ULift.{u} Bool) : LocallyRingedSpace.{u} :=
  line.{u}.restrict (cover.{u} i.down).isOpenEmbedding

/-- **The `i`-th member of the cover: the punctured plane, presented as `(ℂ|Uᵢ)|⊤`.**

This is the point of the test. It is isomorphic to `ℂ|Uᵢ` but is not *of the form* `ℂ|V` for a
`V : Opens ℂ`, so `ComplexAnalytic.AnalyticSpace.ofOpenCover` has to transport both the charts
and the `ℂ`-algebra structure across an isomorphism it computes itself. -/
abbrev member (i : ULift.{u} Bool) : LocallyRingedSpace.{u} :=
  (restrictedLine.{u} i).restrict (⊤ : Opens (restrictedLine.{u} i)).isOpenEmbedding

/-- The inclusion of the `i`-th member into `ℂ`, a composite of two open subspace inclusions. -/
abbrev memberMap (i : ULift.{u} Bool) : member.{u} i ⟶ line.{u} :=
  (restrictedLine.{u} i).ofRestrict _ ≫ line.{u}.ofRestrict (cover.{u} i.down).isOpenEmbedding

/-- **The image of the `i`-th member is the `i`-th punctured plane**, by
`range_ofRestrict_comp` and `Opens.isOpenEmbedding_obj_top`. -/
theorem range_memberMap (i : ULift.{u} Bool) :
    Set.range (memberMap.{u} i).base = (cover.{u} i.down : Set (line.{u})) :=
  (line.{u}.range_ofRestrict_comp (cover.{u} i.down) ⊤).trans
    (congrArg (fun V : Opens (line.{u}) ↦ (V : Set (line.{u})))
      (Opens.isOpenEmbedding_obj_top (cover.{u} i.down)))

open scoped Classical in
/-- **The two punctured planes, as an open cover of `ℂ` by abstract spaces.** -/
def coverOfMembers : line.{u}.OpenCover where
  J := ULift.{u} Bool
  obj := member.{u}
  map := memberMap.{u}
  idx x := ULift.up (if x = a.{u} then true else false)
  covers x := by
    rw [range_memberMap]
    by_cases h : x = a.{u}
    · simp only [if_pos h]
      exact fun hx ↦ a_ne_b.{u} (h ▸ hx)
    · simp only [if_neg h]
      exact h

@[simp]
lemma coverOfMembers_map (i : ULift.{u} Bool) : coverOfMembers.{u}.map i = memberMap.{u} i :=
  rfl

/-- **The images of the members are the punctured planes**, as opens rather than as sets. -/
theorem opensRange_eq_cover (i : ULift.{u} Bool) :
    coverOfMembers.{u}.opensRange i = cover.{u} i.down :=
  Opens.ext (range_memberMap.{u} i)

/-- **No member of the cover is the whole space**, which is what makes this a test of gluing
rather than of the identity. `OkaTest.AnalyticSpaceLocal.cover_ne_top` transported along the
images. -/
theorem opensRange_ne_top (i : ULift.{u} Bool) : coverOfMembers.{u}.opensRange i ≠ ⊤ := by
  rw [opensRange_eq_cover]
  exact cover_ne_top.{u} i.down

/-- The `ℂ`-algebra structure on the `i`-th member: the constants, pulled back along its
inclusion. -/
def memberAlg (i : ULift.{u} Bool) : ℂ →+* (member.{u} i).presheaf.obj (op ⊤) :=
  LocallyRingedSpace.comapAlgMap (memberMap.{u} i) constants.{u}

/-- The structure on a member, read as the twice-restricted structure — which is the spelling
`HasLocalModels.restrict` produces. Two applications of `comapAlgMap_ofRestrict`. -/
theorem memberAlg_eq (i : ULift.{u} Bool) :
    memberAlg.{u} i = (restrictedLine.{u} i).resAlgMap
      (line.{u}.resAlgMap constants.{u} (cover.{u} i.down)) ⊤ := by
  rw [memberAlg, LocallyRingedSpace.comapAlgMap_comp,
    LocallyRingedSpace.comapAlgMap_ofRestrict, LocallyRingedSpace.comapAlgMap_ofRestrict]

/-- **Each member has local models**, by restricting `ℂ`'s twice. -/
theorem hasLocalModels_member (i : ULift.{u} Bool) :
    HasLocalModels (member.{u} i) (memberAlg.{u} i) := by
  rw [memberAlg_eq]
  exact ((AnalyticSpace.complexAffineSpace.{u} 1).hasLocalModels.restrict
    (cover.{u} i.down)).restrict ⊤

/-- **Carrying a member's structure onto the open subspace on its image returns the restriction
of the constants.** This is `restrictAlgMap_comapAlgMap`, and it is what makes the compatibility
hypothesis dischargeable: the carried family is a family of restrictions of one global
section. -/
theorem restrictAlgMap_memberAlg (i : ULift.{u} Bool) :
    coverOfMembers.{u}.restrictAlgMap i (memberAlg.{u} i) =
      line.{u}.resAlgMap constants.{u} (coverOfMembers.{u}.opensRange i) := by
  rw [memberAlg, ← coverOfMembers_map]
  exact LocallyRingedSpace.OpenCover.restrictAlgMap_comapAlgMap coverOfMembers.{u} i
    constants.{u}

theorem isCompatible_memberAlg (c : ℂ) :
    TopCat.Presheaf.IsCompatible line.{u}.presheaf
      (fun i ↦ (coverOfMembers.{u}.opensRange i).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun i ↦ coverOfMembers.{u}.restrictAlgMap i (memberAlg.{u} i) c := by
  have key : (fun i ↦ coverOfMembers.{u}.restrictAlgMap i (memberAlg.{u} i) c) =
      fun i ↦ (line.{u}.presheaf.map (homOfLE (le_top :
        (coverOfMembers.{u}.opensRange i).isOpenEmbedding.isOpenMap.functor.obj ⊤ ≤ ⊤)).op).hom
          (constants.{u} c) :=
    funext fun i ↦ congrArg (fun m : ℂ →+* _ ↦ m c) (restrictAlgMap_memberAlg.{u} i)
  rw [key]
  exact LocallyRingedSpace.isCompatible_map_le_top _

/-- **`ℂ`, assembled from a cover whose members are not open subsets of it.** -/
def assembled : AnalyticSpace.{u} :=
  AnalyticSpace.ofOpenCover coverOfMembers.{u} memberAlg.{u} isCompatible_memberAlg.{u}
    hasLocalModels_member.{u}

example : assembled.{u}.toLocallyRingedSpace = line.{u} :=
  AnalyticSpace.ofOpenCover_toLocallyRingedSpace coverOfMembers.{u} memberAlg.{u}
    isCompatible_memberAlg.{u} hasLocalModels_member.{u}

/-- **The glued `ℂ`-algebra structure is the one the members came from**: the round trip.

The uniqueness half of the sheaf condition does it — the constants restrict to the carried
family on every member, and `glueSection_eq` says nothing else does. -/
theorem algebraMap_assembled : assembled.{u}.algebraMap = constants.{u} :=
  RingHom.ext fun c ↦
    LocallyRingedSpace.glueSection_eq
      ((LocallyRingedSpace.iSup_isOpenEmbedding_obj_top _).trans
        coverOfMembers.{u}.iSup_opensRange)
      _ (isCompatible_memberAlg.{u} c) (constants.{u} c)
      fun i ↦ (congrArg (fun m : ℂ →+* _ ↦ m c) (restrictAlgMap_memberAlg.{u} i)).symm

/-- **Pulling the glued structure back to a member returns that member's structure**, which is
the projection lemma `ofOpenCover` comes with, checked here on the cover above rather than in the
abstract. -/
example (i : ULift.{u} Bool) :
    LocallyRingedSpace.comapAlgMap (coverOfMembers.{u}.map i) assembled.{u}.algebraMap =
      memberAlg.{u} i :=
  AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap coverOfMembers.{u} memberAlg.{u}
    isCompatible_memberAlg.{u} hasLocalModels_member.{u} i

/-! ### `HasLocalModels.of_iso` at an isomorphism that is not an identity

The cover above exercises `of_iso` through `isoRestrict`. This is the cheapest direct instance:
`ℂ` and `ℂ|⊤` are isomorphic, the isomorphism is `restrictTopIso`, and its inverse is `ℂ`-linear
for the restricted structure by `isCLinearHom_restrictTopIso_inv`. Transporting *back* along it
recovers the global structure from the restricted one, which is the direction `HasLocalModels.
restrict` does not give.
-/

example : HasLocalModels line.{u} constants.{u} :=
  HasLocalModels.of_iso line.{u}.restrictTopIso.symm
    (isCLinearHom_restrictTopIso_inv line.{u} constants.{u})
    ((AnalyticSpace.complexAffineSpace.{u} 1).hasLocalModels.restrict ⊤)

/-! ### `ofGlueData` at the gluing of this cover

The cover above is a cover of `ℂ`, a space that carries the constants to begin with. This section
runs `ComplexAnalytic.AnalyticSpace.ofGlueData` on the **glued** space of the same cover — a
multicoequalizer, which carries nothing at all until something puts a structure on it, and which
is not a `restrict` of anything.

What is still a round trip, stated precisely: the structures on the pieces are the pullbacks of
one structure on the glued space, namely the constants pulled back along `fromGlued`. That is
unavoidable for the reason `OkaTest/AnalyticSpaceLocal.lean` records — on a sheaf every
compatible family over a cover of `⊤` is the restriction family of a unique global section — and
the thing this section adds over that one is that **the space carrying the glued structure is
produced by the gluing** rather than given in advance.
-/

/-- The glue data of the cover above; its glued space is a multicoequalizer. -/
abbrev gluedData : LocallyRingedSpace.GlueData.{u} := coverOfMembers.{u}.gluedCover

/-- The `ℂ`-algebra structure the glued space is given: the constants of `ℂ`, pulled back along
`fromGlued`. -/
def gluedConstants : ℂ →+* (gluedData.{u}.toGlueData.glued).presheaf.obj (op ⊤) :=
  LocallyRingedSpace.comapAlgMap coverOfMembers.{u}.fromGlued constants.{u}

/-- **On each piece, that structure is the piece's own structure**, because
`ι j ≫ fromGlued = 𝒰.map j`. Pure `comapAlgMap_comp`; nothing about the glued space's sheaf is
computed. -/
theorem comapAlgMap_gluedConstants (j : gluedData.{u}.J) :
    LocallyRingedSpace.comapAlgMap (gluedData.{u}.openCover.map j) gluedConstants.{u} =
      memberAlg.{u} j := by
  rw [gluedConstants, ← LocallyRingedSpace.comapAlgMap_comp]
  exact congrArg (fun f ↦ LocallyRingedSpace.comapAlgMap f constants.{u})
    (coverOfMembers.{u}.ι_fromGlued j)

theorem hasLocalModels_gluedPiece (j : gluedData.{u}.J) :
    HasLocalModels (gluedData.{u}.openCover.obj j)
      (LocallyRingedSpace.comapAlgMap (gluedData.{u}.openCover.map j) gluedConstants.{u}) := by
  rw [comapAlgMap_gluedConstants]
  exact hasLocalModels_member.{u} j

/-- **The gluing of the two punctured planes, as a complex analytic space.** The first use of
`ofGlueData`, and the first analytic space in the development whose underlying locally ringed
space is not a restriction of one that was already there. -/
def gluedAnalytic : AnalyticSpace.{u} :=
  AnalyticSpace.ofGlueData gluedData.{u}
    (fun j ↦ LocallyRingedSpace.comapAlgMap (gluedData.{u}.openCover.map j) gluedConstants.{u})
    (gluedData.{u}.openCover.isCompatible_restrictAlgMap_comapAlgMap gluedConstants.{u})
    hasLocalModels_gluedPiece.{u}

example : gluedAnalytic.{u}.toLocallyRingedSpace = gluedData.{u}.toGlueData.glued :=
  AnalyticSpace.ofGlueData_toLocallyRingedSpace gluedData.{u}
    (fun j ↦ LocallyRingedSpace.comapAlgMap (gluedData.{u}.openCover.map j) gluedConstants.{u})
    (gluedData.{u}.openCover.isCompatible_restrictAlgMap_comapAlgMap gluedConstants.{u})
    hasLocalModels_gluedPiece.{u}

/-- **The structure the gluing produces on the glued space is the one the pieces came from.** -/
theorem algebraMap_gluedAnalytic : gluedAnalytic.{u}.algebraMap = gluedConstants.{u} :=
  AnalyticSpace.algebraMap_ofOpenCover_comapAlgMap gluedData.{u}.openCover gluedConstants.{u}
    hasLocalModels_gluedPiece.{u}

end OkaTest.AnalyticSpaceGlue

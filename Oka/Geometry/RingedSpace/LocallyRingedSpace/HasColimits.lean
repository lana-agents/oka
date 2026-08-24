/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# The coproduct of locally ringed spaces is covered by its inclusions

Material for two Mathlib files and not one; see `README.md` on the mirror tree, which asks for the
split by destination.

**The cover goes to `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`**, because it is
stated in terms of `AlgebraicGeometry.LocallyRingedSpace.OpenCover`, and Mathlib has no such
structure: this repository's is in `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`, proposed
for the Mathlib file of that name, and that file is *not* in the closure of the one below.
`scripts/import_cost.py` prices it there at **3** modules (`Mathlib.CategoryTheory.GlueData`,
`Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing`, `Mathlib.Topology.Gluing`), while the
dependency in the other direction costs **0** — so upstream the cover sits beside `OpenCover` and
nothing pays anything. It is in this file rather than in the gluing one only because that file is
an import of this one.

**Everything else goes to `Mathlib/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean` at
cost 0**: it is this file's own import, and the `SheafedSpace` results the proofs run through are
already in its closure.

Mathlib builds the coproduct of locally ringed spaces in that file and never says that the
inclusions are open immersions. It says it one level below, for `SheafedSpace` over a category
with strict terminal objects
(`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion`), and one level above,
for `AlgebraicGeometry.Scheme` — where `Mathlib/AlgebraicGeometry/Limits.lean` has the whole
sigma API: `AlgebraicGeometry.sigmaOpenCover`, `AlgebraicGeometry.sigmaι_eq_iff`,
`AlgebraicGeometry.disjoint_opensRange_sigmaι`, `AlgebraicGeometry.sigmaMk`. Only the middle level
is missing, and

    example (i : Discrete ι) : LocallyRingedSpace.IsOpenImmersion (colimit.ι F i) := by
      infer_instance

fails to synthesise. Everything here is the transport across
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace`, which preserves these colimits.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.sigma_ι_isOpenImmersion`: **the inclusion of a member of
  a coproduct is an open immersion.**
- `AlgebraicGeometry.LocallyRingedSpace.exists_colimit_ι_base_eq`: **every point of a coproduct
  is in the image of some inclusion.**
- `AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover`: the two together, as an
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover`.
- `AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover`: **the images of two
  distinct members are disjoint**, so the index of a point of the coproduct is unique.
- `AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_eq_iff`: the two together — two points of the
  members have the same image exactly when they are the same point of the same member.

## How the index of a point is recovered, and the route this file does not take

The disjointness is the half that looks hard, and it is hard along the obvious route. Mathlib's
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty` gets it one level down by
pushing a point through `CategoryTheory.preservesColimitIso`, then
`CategoryTheory.Limits.HasColimit.isoOfNatIso` at `CategoryTheory.Discrete.natIsoFunctor`, then
`TopCat.sigmaIsoSigma`, landing in a `Sigma` type where the index is a projection. Transporting
that here **does not go through by `rw` or by `simp`**: the middle step is blocked on
`(F ⋙ G).obj k` against `G.obj (F.obj k)`, which is definitional and not syntactic, and `simp`
unfolds the composite functor's action into `CategoryTheory.InducedCategory.homMk` before the
rewrite can fire. Mathlib runs that chain under
`set_option backward.isDefEq.respectTransparency false`, and no such `set_option` appears here.

**It is not needed, because that route computes more than the statement does.**
`TopCat.sigmaIsoSigma` identifies the whole coproduct space with a `Sigma` type; disjointness
needs only that the index of a point is well defined, and a *map* to the index type suffices for
that — it never has to be a homeomorphism. So `AlgebraicGeometry.LocallyRingedSpace.indexCocone`
gives the index type the discrete topology and descends the constant-index maps through the
universal property, and `AlgebraicGeometry.LocallyRingedSpace.eq_of_colimit_ι_base_eq` reads two
of its factorisations against each other. Nothing is inverted, so nothing has to be rewritten
across `CategoryTheory.Discrete.natIsoFunctor`.

## What is not here

**No analogue of `AlgebraicGeometry.sigmaMk`**: the index map built below is not shown to be part
of a homeomorphism onto a `Sigma` type, only to exist. That statement is true and would need
exactly the `TopCat.sigmaIsoSigma` chain described above; nothing in this repository asks for it.

## Implementation notes

The index type is taken in `Type u` throughout rather than in a general universe with `Small`,
because `AlgebraicGeometry.LocallyRingedSpace.OpenCover.J` is a `Type u` and the cover is the
point of the file. The two lemmas are stated for a `CategoryTheory.Limits.colimit` of a functor
out of `CategoryTheory.Discrete`, which is what the `SheafedSpace` results are stated for, and the
cover is built for a family, which is the shape `Mathlib/AlgebraicGeometry/Limits.lean` states
its `AlgebraicGeometry.Scheme` version in, and what a consumer has.

Two seams, both recorded because neither is visible from the statements.

**The composition instance has to be handed over positionally.** After rewriting the goal along
`CategoryTheory.ι_preservesColimitIso_inv`, the `colimit.ι` appearing in it carries a
different `CategoryTheory.Limits.HasColimit` instance path from the one a freshly elaborated
`inferInstance` produces. The two terms are definitionally equal and not syntactically equal, and
instance synthesis is syntactic — so `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp` is not
found even with the first factor's instance in context, and is supplied with `@`.

**`AlgebraicGeometry.SheafedSpace` is itself an induced category.** A `SheafedSpace` morphism
needs one `CategoryTheory.InducedCategory.Hom.hom` more than a `LocallyRingedSpace` one before
its `base` can be projected, so the underlying map of the comparison isomorphism is `.hom.hom.base`
where the underlying map of `colimit.ι` at this level is `.base`.

**Those `AlgebraicGeometry` names are in the root namespace, not under
`AlgebraicGeometry.Scheme`.** This file's docstring previously said the sigma API could not be
named here because the repository does not import `Mathlib/AlgebraicGeometry/Limits.lean`. That
is false — it is in the `Oka` closure and `scripts/check_docstring_names.py` resolves all four
names above. What had failed was the spelling: those declarations were being cited under
`AlgebraicGeometry.Scheme`, where none of them lives. The name cannot be repeated here to show
what was wrong with it, because a name that resolves to nothing is what the checker rejects.

**The composite forgetful functor is not found by `infer_instance` at its own spelling, and the
reason is not that the instance is missing.**
`AlgebraicGeometry.LocallyRingedSpace.forgetToTop` is *by definition*
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace` followed by
`AlgebraicGeometry.SheafedSpace.forget`; both factors preserve these colimits, and
`CategoryTheory.Limits.comp_preservesColimitsOfShape` covers the composite and **is** an instance.
What blocks it is that `forgetToTop` is a `def` rather than an `abbrev`, so at the reducible
transparency instance search runs at the goal is never seen as a composite and that instance is
never tried. Two controls settle it, both against
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits` alone: `inferInstanceAs` at the
spelled-out composite succeeds where bare `infer_instance` fails, and an `abbrev` whose body is
the same composite is found by bare `infer_instance`. Handing the instance over is one line, and
is the move `Mathlib/AlgebraicGeometry/Limits.lean` makes for the `AlgebraicGeometry.Scheme`
version, there by `inferInstanceAs` at the unfolded type.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

variable {ι : Type u} (F : Discrete ι ⥤ LocallyRingedSpace.{u})

/-- **The inclusion of a member of a coproduct of locally ringed spaces is an open immersion.**

`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion` transported along
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace`, which preserves coproducts. -/
instance sigma_ι_isOpenImmersion (i : Discrete ι) :
    LocallyRingedSpace.IsOpenImmersion (colimit.ι F i) := by
  have h := ι_preservesColimitIso_inv forgetToSheafedSpace.{u} F i
  change SheafedSpace.IsOpenImmersion (forgetToSheafedSpace.map (colimit.ι F i))
  rw [← h]
  have h1 : SheafedSpace.IsOpenImmersion (colimit.ι (F ⋙ forgetToSheafedSpace.{u}) i) :=
    inferInstance
  exact @SheafedSpace.IsOpenImmersion.comp _ _ _ _ _ _ _ h1 _

/-- **Every point of a coproduct of locally ringed spaces is in the image of some inclusion.**

`AlgebraicGeometry.SheafedSpace.colimit_exists_rep` for the coproduct of the underlying sheafed
spaces, moved across the comparison isomorphism — which is an isomorphism, hence injective on
points, which is what turns a representative there into one here. -/
theorem exists_colimit_ι_base_eq (x : (colimit F : LocallyRingedSpace.{u})) :
    ∃ (i : Discrete ι) (y : F.obj i), (colimit.ι F i).base y = x := by
  set e := preservesColimitIso forgetToSheafedSpace.{u} F with he
  obtain ⟨i, y, hy⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace.{u})
    (e.hom.hom.base x)
  refine ⟨i, y, ?_⟩
  have hcomp := ι_preservesColimitIso_hom forgetToSheafedSpace.{u} F i
  have key : e.hom.hom.base ((colimit.ι F i).base y) = e.hom.hom.base x := by
    rw [← hy, ← hcomp]
    rfl
  have : IsIso ((SheafedSpace.forget CommRingCat.{u}).map e.hom) := inferInstance
  exact (TopCat.homeoOfIso (asIso ((SheafedSpace.forget CommRingCat.{u}).map e.hom))).injective key

variable (f : ι → LocallyRingedSpace.{u})

/-- **The inclusion of a member of a coproduct is an open immersion**, for a family rather than
for a functor out of `CategoryTheory.Discrete`.

Stated separately because instance search does not see through
`CategoryTheory.Limits.Sigma.ι` to `CategoryTheory.Limits.colimit.ι`, so the cover below cannot
find its `isOpen` field from the functor-indexed instance. -/
instance sigmaι_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (Sigma.ι f i) :=
  sigma_ι_isOpenImmersion (Discrete.functor f) ⟨i⟩

/-- **Every point of a coproduct of locally ringed spaces is in the image of some inclusion**, for
a family rather than for a functor out of `CategoryTheory.Discrete`. -/
theorem exists_sigma_ι_base_eq (x : (∐ f : LocallyRingedSpace.{u})) :
    ∃ (i : ι) (y : f i), (Sigma.ι f i).base y = x := by
  obtain ⟨i, y, hy⟩ := exists_colimit_ι_base_eq (Discrete.functor f) x
  exact ⟨i.as, y, hy⟩

/-- **The members of a coproduct of locally ringed spaces are an open cover of it.**

The analogue of the `AlgebraicGeometry.Scheme` version in
`Mathlib/AlgebraicGeometry/Limits.lean`. The index of a point is chosen by
`Exists.choose` from `AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq`; the members
are disjoint, so the choice is in fact forced, but nothing below needs that. -/
noncomputable def sigmaOpenCover : (∐ f : LocallyRingedSpace.{u}).OpenCover where
  J := ι
  obj := f
  map := Sigma.ι f
  idx x := (exists_sigma_ι_base_eq f x).choose
  covers x := (exists_sigma_ι_base_eq f x).choose_spec

/-! ### The index of a point is unique

The members of a coproduct do not overlap, so the index that
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.idx` chooses above is in fact forced. The proof is
the one described in the header: descend a map to the index type, do not build an isomorphism
with a `Sigma` type. -/

/-- **The underlying space of a coproduct of locally ringed spaces is the coproduct of the
underlying spaces**, in the only form used below: that
`AlgebraicGeometry.LocallyRingedSpace.forgetToTop` preserves these colimits.

Both factors of it do, and `CategoryTheory.Limits.comp_preservesColimitsOfShape` is an instance
that covers the composite — but `AlgebraicGeometry.LocallyRingedSpace.forgetToTop` is a `def`, so
the goal does not present as a composite at reducible transparency and that instance is never
tried. Hence the explicit term rather than `inferInstance`; see the implementation notes in the
header. -/
noncomputable instance preservesColimitsOfShape_discrete_forgetToTop :
    PreservesColimitsOfShape (Discrete ι) forgetToTop.{u} :=
  Limits.comp_preservesColimitsOfShape _ _

/-- **The cocone that remembers which member a point came from**: the index type carried by the
*discrete* topology, with the `i`-th member mapping to the constant `i`.

This is the whole of the disjointness argument. A cocone under `F ⋙ forgetToTop` factors uniquely
through the coproduct, so the factorisation is a continuous map assigning an index to every point
of the coproduct, and two members whose images met would force their indices equal.

**Nothing below uses discreteness, and the topology is not forced.** A constant map is continuous
into any space, so `continuous_const` discharges the whole obligation whatever topology `ι`
carries, and the argument reads off an equality of *points* of `ι` and never names an open set of
it: substituting `⊤` for `⊥` here leaves
`AlgebraicGeometry.LocallyRingedSpace.eq_of_colimit_ι_base_eq` and the disjointness below it
compiling word for word, and `⊤` is provably not discrete. `⊥` is chosen because it is the
canonical topology on an index type. Note also that "every map into it is continuous" is the
property of the *indiscrete* topology, not of this one — into a discrete codomain continuity is
local constancy, which is a real condition. What *is* forced is that some topology be supplied,
and that it be supplied by `letI` rather than by a `TopologicalSpace` instance, because
`TopCat.ofHom` resolves the codomain's instance by search and would not see through a definition
that fixed it. -/
noncomputable def indexCocone : Cocone (F ⋙ forgetToTop.{u}) :=
  letI : TopologicalSpace ι := ⊥
  { pt := TopCat.of ι
    ι := Discrete.natTrans fun i ↦ TopCat.ofHom ⟨fun _ ↦ i.as, continuous_const⟩ }

/-- **Two members of a coproduct whose images meet are the same member.**

The two factorisations of `AlgebraicGeometry.LocallyRingedSpace.indexCocone` through the colimit,
read against each other at the two points: each says that the descended map takes the value of the
index there, and the hypothesis says the two points have the same image. -/
theorem eq_of_colimit_ι_base_eq {i j : Discrete ι} {x : F.obj i} {y : F.obj j}
    (h : (colimit.ι F i).base x = (colimit.ι F j).base y) : i = j := by
  have hc := isColimitOfPreserves forgetToTop.{u} (colimit.isColimit F)
  have hi := ConcreteCategory.congr_hom (hc.fac (indexCocone F) i) x
  have hj := ConcreteCategory.congr_hom (hc.fac (indexCocone F) j) y
  simp only [Functor.mapCocone_ι_app, ConcreteCategory.comp_apply] at hi hj
  exact Discrete.ext (hi.symm.trans
    ((congrArg (ConcreteCategory.hom (hc.desc (indexCocone F))) h).trans hj))

/-- **Two members of a coproduct whose images meet are the same member**, for a family rather than
for a functor out of `CategoryTheory.Discrete`. -/
theorem eq_of_sigmaι_base_eq {i j : ι} {x : f i} {y : f j}
    (h : (Sigma.ι f i).base x = (Sigma.ι f j).base y) : i = j :=
  congrArg Discrete.as (eq_of_colimit_ι_base_eq (Discrete.functor f) h)

/-- **The inclusion of a member of a coproduct is injective on points**, which is its being an
open immersion and hence an open embedding. -/
theorem sigmaι_base_injective (i : ι) : Function.Injective (Sigma.ι f i).base :=
  (sigmaι_isOpenImmersion f i).base_open.injective

/-- **Two points of the members of a coproduct have the same image exactly when they are the same
point of the same member.**

The analogue of the `AlgebraicGeometry.Scheme` statement in `Mathlib/AlgebraicGeometry/Limits.lean`
— whose proof is no guide, running as it does through a locally directed cover, which does not
exist at this level. Here the two directions are the two lemmas above:
`AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq` for the index and
`AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_injective` for the point. -/
theorem sigmaι_base_eq_iff (i j : ι) (x : f i) (y : f j) :
    (Sigma.ι f i).base x = (Sigma.ι f j).base y ↔
      (Sigma.mk i x : (i : ι) × (f i).toTopCat) = Sigma.mk j y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain rfl := eq_of_sigmaι_base_eq f h
    exact congrArg _ (sigmaι_base_injective f i h)
  · rintro ⟨⟩
    rfl

/-- **The images of two distinct members of a coproduct are disjoint.** -/
theorem disjoint_range_sigmaι {i j : ι} (h : i ≠ j) :
    Disjoint (Set.range (Sigma.ι f i).base) (Set.range (Sigma.ι f j).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact h (eq_of_sigmaι_base_eq f hy).symm

/-- **Two distinct members of the open cover of a coproduct have disjoint images**, as open
subsets of the coproduct.

The analogue of `AlgebraicGeometry.disjoint_opensRange_sigmaι`, and the form a gluing argument
consumes: `Disjoint` unfolds by `disjoint_iff` to the meet being `⊥`, which is what makes a
compatibility hypothesis on the pairwise intersections of the members vacuous for `i ≠ j`. -/
theorem disjoint_opensRange_sigmaOpenCover {i j : ι} (h : i ≠ j) :
    Disjoint ((sigmaOpenCover f).opensRange i) ((sigmaOpenCover f).opensRange j) := by
  rw [disjoint_iff, ← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_inf,
    TopologicalSpace.Opens.coe_bot, OpenCover.coe_opensRange, OpenCover.coe_opensRange]
  exact Set.disjoint_iff_inter_eq_empty.mp (disjoint_range_sigmaι f h)

end AlgebraicGeometry.LocallyRingedSpace

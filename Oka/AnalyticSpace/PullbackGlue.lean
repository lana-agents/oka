/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Glue
import Oka.AnalyticSpace.PullbackBlock

/-!
# The fibre product glued out of a family of opens, and its two projections

`Oka/AnalyticSpace/PullbackBlock.lean` builds the transition data of the gluing that
`Mathlib/AlgebraicGeometry/Pullbacks.lean` uses to make a fibre product of schemes — the overlaps
`ComplexAnalytic.AnalyticSpace.Pullback.v`, the swap
`ComplexAnalytic.AnalyticSpace.Pullback.t`, the triple-overlap map
`ComplexAnalytic.AnalyticSpace.Pullback.t'` and the cocycle law — and stops there. Its own
docstring says what it does not do: *"It does not build an
`AlgebraicGeometry.LocallyRingedSpace.GlueData` and it does not make
`ComplexAnalytic.AnalyticSpace` a category with pullbacks."*

**This file does the first of those two.** It assembles the block into an
`AlgebraicGeometry.LocallyRingedSpace.GlueData`, promotes the gluing to a complex analytic space
through `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear`, and produces the two projections and
the square they make commute. **It does not do the second**, and the last section below says
exactly what is still missing.

## Why the datum is stated one category down

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` takes an
`AlgebraicGeometry.LocallyRingedSpace.GlueData`, and **this repository declares no glue-datum type
— not over `ComplexAnalytic.AnalyticSpace` and not over anything else — while every glue datum it
builds is a term of one of Mathlib's.** Both halves are one walk of the environment at `487ea43`,
over the declarations whose declaring module begins `Oka`, taking the head of the codomain under
`Lean.Meta.forallTelescopeReducing`: of the **sixteen** inductive types declared, not one is a glue
datum, and of the **twenty-one** declarations whose codomain is one, **thirteen** are under `Oka/` —
ten into `AlgebraicGeometry.LocallyRingedSpace.GlueData`, this file's own
`ComplexAnalytic.AnalyticSpace.Pullback.gluing` among them, and three into
`CategoryTheory.GlueData'` — with the other eight under `OkaTest/`.
`ComplexAnalytic.GlueDataCLinear` is a `def` into `Prop` **on** a locally-ringed-space datum and
not a datum of its own.

**The instrument is the codomain and not the name**, because a `GlueData` in a declaration's name
says nothing about what that declaration is. `scripts/DumpOkaDecls.lean` at `487ea43` attributes
**seventy-five** names containing `GlueData` to modules under `Oka/`, spread over fourteen of
them — twenty in `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`, twelve in
`Oka/AnalyticSpace/Glue.lean`, eleven in
`Oka/Geometry/RingedSpace/PresheafedSpace/Double.lean` and ten in
`Oka/CategoryTheory/GlueData.lean`, which is named for a glue datum and declares ten theorems and
no type — and every one of the seventy-five is a theorem or a definition. Which of them *build* a
datum, and into which type, is a question about codomains, and that is the question
`Lean.Meta.forallTelescopeReducing` was pointed at. So the datum here has
`AlgebraicGeometry.LocallyRingedSpace` objects and morphisms throughout, and every field of it is
the image under `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` of something the block
already built:

* `U` and `V` are the images of the ambient pullbacks and of
  `ComplexAnalytic.AnalyticSpace.Pullback.v`;
* `f` is the image of `ComplexAnalytic.AnalyticSpace.Pullback.fV`, and its `f_open` field is
  `ComplexAnalytic.AnalyticSpace.Pullback.isOpenImmersion_map_fV`. That is stated as an instance
  there, though **not for this field** — its own docstring gives the reason as the elaboration of
  `ComplexAnalytic.AnalyticSpace.Pullback.isoPullbackFV`'s and `…t'Map`'s types — and the field
  takes it either way;
* `t` is the image of `ComplexAnalytic.AnalyticSpace.Pullback.t`, and `t_id` is
  `ComplexAnalytic.AnalyticSpace.Pullback.t_id` carried across by
  `CategoryTheory.Functor.map_id`;
* `t'` is `ComplexAnalytic.AnalyticSpace.Pullback.t'Map` **on the nose** and `cocycle` is
  `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_cocycle` **on the nose**. The datum's `t'` field
  has type `pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)` in
  `AlgebraicGeometry.LocallyRingedSpace`, and that is the type `…t'Map` was given; nothing is
  transported here that was not transported there.

**Three fields are supplied by neither the block nor a projection of it, and instance search
finds all three**: `f_mono` and `f_hasPullback` from `f_open`, and `f_id` from
`CategoryTheory.Functor.map_isIso` applied to an isomorphism instance search already finds
upstairs. The remaining field is `t_fac`, and it is the subject of the next section.

## The one field that needed a lemma, and where it splits

`t_fac` — `t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j` — is the only field that is
neither a projection of the block nor an instance. Mathlib proves its analogue inline inside
`gluing`; here it splits in two, and the split is the point:

* `ComplexAnalytic.AnalyticSpace.Pullback.t'_fac` is that equation **upstairs**, between morphisms
  of analytic spaces, and its proof is Mathlib's inline one unchanged — two
  `CategoryTheory.Limits.pullback.hom_ext`s and the same six factorisation lemmas, three for
  `ComplexAnalytic.AnalyticSpace.Pullback.t'` and three for `…t`.
* `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_fac` carries it down, and it is where the
  conjugation is discharged. `…t'Map_snd` rewrites the left-hand side into
  `…isoPullbackFV`'s inverse followed by the image of the analytic composite; `t'_fac` rewrites
  that composite; and what remains is `CategoryTheory.IsPullback.isoPullback_inv_fst`, which
  cancels the surviving conjugation against the pullback projection it was built from.

**So the datum owes no new mathematics about pullbacks and one lemma about the comparison**, and
that is the shape `Oka/AnalyticSpace/PullbackBlock.lean` predicted when it said its `t'Map_snd`
is *"the side of that equation which the conjugation touches; the other side is untouched"*.

## The projections, and why they are glued rather than descended

`ComplexAnalytic.AnalyticSpace.Pullback.p1` and `…p2` are
`ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` at the families
`ComplexAnalytic.AnalyticSpace.Pullback.toBase` and `CategoryTheory.Limits.pullback.snd`. Mathlib
builds its `p1` and `p2` by `CategoryTheory.Limits.Multicoequalizer.desc` on the datum's diagram
instead; both routes exist here, and `…glueMorphismsOfGlueData` is taken because it returns a
**morphism of analytic spaces** rather than a morphism of locally ringed spaces. Its two
hypotheses are discharged from the block: the compatibility from
`ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_toBase`, which is
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_fst` together with
`CategoryTheory.Limits.pullback.condition` at the overlap, and `…fV_comp_snd`, which is
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_snd` alone; and the `ℂ`-linearity from the
`isCLinear` field the morphisms carry.

**The `ℂ`-linearity of the datum is free for the same reason.**
`ComplexAnalytic.GlueDataCLinear` is supplied by `ComplexAnalytic.glueDataCLinear_of_isCLinearHom`
from linearity of the legs and of the transitions, and both are field projections of analytic
morphisms — `ComplexAnalytic.AnalyticSpace.Hom` carries `ComplexAnalytic.IsCLinearHom` in a field.
This is the use `Oka/AnalyticSpace/Glue.lean` states that lemma for.

## The index is a family of opens and not a cover

**No declaration below asks the `U i` to cover `X`**, and that is inherited from the block rather
than decided here: the gluing of a family of opens is an analytic space whatever the family is.
Joint surjectivity is what would make `ComplexAnalytic.AnalyticSpace.Pullback.glued` the fibre
product, and nothing below claims that it is.

## Main results

- `ComplexAnalytic.AnalyticSpace.Pullback.t'_fac` and
  `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_fac`: the `t_fac` law, upstairs and downstairs.
- `ComplexAnalytic.AnalyticSpace.Pullback.gluing`: **the glue datum**, over
  `AlgebraicGeometry.LocallyRingedSpace`.
- `ComplexAnalytic.AnalyticSpace.Pullback.glueDataCLinear_gluing`: its transitions are
  `ℂ`-linear.
- `ComplexAnalytic.AnalyticSpace.Pullback.glued`: **the gluing, as a complex analytic space**, and
  `…glued_toLocallyRingedSpace`: its underlying locally ringed space is the datum's own gluing, so
  every statement of `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` about the gluing of a
  datum is a statement about it.
- `ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_toBase` and `…fV_comp_snd`: the compatibility
  the two projections are glued from.
- `ComplexAnalytic.AnalyticSpace.Pullback.p1` and `…p2`: **the two projections, as morphisms of
  analytic spaces**, with `…ι_p1` and `…ι_p2` saying what each restricts to on a member.
- `ComplexAnalytic.AnalyticSpace.Pullback.toBase_comp`: the ambient pullback square's own
  commutation, which is `CategoryTheory.Limits.pullback.condition` at the cospan the family
  presents.
- `ComplexAnalytic.AnalyticSpace.Pullback.p_comm`: **the square commutes** — `p1 ≫ f = p2 ≫ g`.

## What this does not do

**It does not make `ComplexAnalytic.AnalyticSpace` a category with pullbacks, and nothing below
claims it does.** `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` does not
synthesise at the commit that adds this file. What is missing, in Mathlib's order:

* **The lift.** `gluedLiftPullbackMap`, `gluedLift` and `pullbackP1Iso`, which take a competing
  cone and factor it through the gluing. None of it is here and none of it is priced here.
* **`gluedIsLimit`**, which needs the lift and the uniqueness, and needs the `U i` to **cover**
  `X`: the family below is not asked to.
* **`hasPullback_of_cover`**, and then the reduction of an arbitrary cospan to one where the base
  change is known — which needs covering `Y` and `Z` as well, and whose length is not measured
  anywhere in this repository.

`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s bullet on base change is **not** falsified by this
file: base change of the class `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` across a general
square is a statement about a class and does not follow from a fibre product existing, and no
fibre product over a general cospan is produced below.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace.Pullback

variable {X Y Z : AnalyticSpace.{u}} {I : Type u} (U : I → X.Opens) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g]

/-! ### The factorisation law the glue datum's `t_fac` field asks for -/

/-- **The `t_fac` law upstairs.**

Mathlib's proof of the `t_fac` field of `AlgebraicGeometry.Scheme.Pullback.gluing`, taken out of
the datum and stated on its own so that the transport downstairs has something to rewrite with.
The two `CategoryTheory.Limits.pullback.hom_ext`s and the six factorisation lemmas are Mathlib's
unchanged. -/
theorem t'_fac (i j k : I) :
    t' U f g i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t U f g i j := by
  apply pullback.hom_ext
  on_goal 1 => apply pullback.hom_ext
  all_goals
    simp only [t'_snd_fst_fst, t'_snd_fst_snd, t'_snd_snd, t_fst_fst, t_fst_snd, t_snd,
      Category.assoc]

/-- **The `t_fac` law downstairs**, which is the field
`AlgebraicGeometry.LocallyRingedSpace.GlueData` asks for.

`ComplexAnalytic.AnalyticSpace.Pullback.t'Map_snd` turns the left-hand side into a conjugating
isomorphism followed by the image of an analytic composite;
`ComplexAnalytic.AnalyticSpace.Pullback.t'_fac` rewrites that composite; and
`CategoryTheory.IsPullback.isoPullback_inv_fst` cancels the conjugation that is left against the
projection it was built from. **No square is reproved downstairs**, which is what the second half
of `Oka/AnalyticSpace/PullbackBlock.lean` exists to make true. -/
theorem t'Map_fac (i j k : I) :
    t'Map U f g i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ forgetToLocallyRingedSpace.map (t U f g i j) := by
  rw [t'Map_snd, t'_fac]
  simp only [Functor.map_comp, isoPullbackFV, IsPullback.isoPullback_inv_fst_assoc]

/-! ### The glue datum, and the analytic space it glues to -/

/-- **The glue datum of the fibre product**, over `AlgebraicGeometry.LocallyRingedSpace`.

Every field is the image under `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` of a
declaration of `Oka/AnalyticSpace/PullbackBlock.lean`, except `t'` and `cocycle`, which are
`ComplexAnalytic.AnalyticSpace.Pullback.t'Map` and `…t'Map_cocycle` on the nose, and `t_fac`,
which is `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_fac`. The datum is stated one category down
because `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` is, and because there is no glue datum
over `ComplexAnalytic.AnalyticSpace` in this repository. -/
noncomputable def gluing : LocallyRingedSpace.GlueData.{u} where
  J := I
  U i := forgetToLocallyRingedSpace.obj (pullback (X.ofRestrict (U i) ≫ f) g)
  V ij := forgetToLocallyRingedSpace.obj (v U f g ij.1 ij.2)
  f i j := forgetToLocallyRingedSpace.map (fV U f g i j)
  f_open i j := isOpenImmersion_map_fV U f g i j
  f_id i := by
    have : IsIso (fV U f g i i) := inferInstance
    infer_instance
  t i j := forgetToLocallyRingedSpace.map (t U f g i j)
  t_id i := by rw [t_id]; exact forgetToLocallyRingedSpace.map_id _
  t' i j k := t'Map U f g i j k
  t_fac i j k := t'Map_fac U f g i j k
  cocycle i j k := t'Map_cocycle U f g i j k

/-- **The transitions of the datum are `ℂ`-linear.**

`ComplexAnalytic.glueDataCLinear_of_isCLinearHom` asks for linearity of the legs and of the
transitions, and both are field projections: the members carry the `ℂ`-algebra structures of the
analytic spaces they are the images of, and `ComplexAnalytic.AnalyticSpace.Hom` carries
`ComplexAnalytic.IsCLinearHom` in a field. So no analytic input is needed here, and that is the
use `Oka/AnalyticSpace/Glue.lean` states that lemma for. -/
theorem glueDataCLinear_gluing :
    ComplexAnalytic.GlueDataCLinear (gluing U f g)
      (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).algebraMap) :=
  glueDataCLinear_of_isCLinearHom _ _ (fun p ↦ (v U f g p.1 p.2).algebraMap)
    (fun i j ↦ (fV U f g i j).isCLinear) (fun i j ↦ (Pullback.t U f g i j).isCLinear)

/-- **The gluing, as a complex analytic space.**

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` at the datum, with the `HasLocalModels`
hypothesis discharged member by member from
`ComplexAnalytic.AnalyticSpace.hasLocalModels`. **This is not claimed to be the fibre product**:
the family of opens is not asked to cover `X`, and nothing below produces a limit cone. -/
noncomputable def glued : AnalyticSpace.{u} :=
  ofGlueDataCLinear (gluing U f g) _ (glueDataCLinear_gluing U f g)
    (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).hasLocalModels)

/-- **Its underlying locally ringed space is the one glued one category down**, so every statement
of `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` about the datum is a statement about
this space. -/
@[simp]
theorem glued_toLocallyRingedSpace :
    (glued U f g).toLocallyRingedSpace = (gluing U f g).toGlueData.glued := rfl

/-! ### The two projections, and the square they make commute -/

/-- **The member maps agree over the overlaps, for the first projection.**

`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_fst` read as a statement about the member maps of
the datum, which is the hypothesis
`ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` asks for. -/
theorem fV_comp_toBase (i j : I) :
    fV U f g i j ≫ toBase U f g i = t U f g i j ≫ fV U f g j i ≫ toBase U f g j := by
  simp [toBase, t_fst_fst_assoc, ← pullback.condition]

/-- **The member maps agree over the overlaps, for the second projection**, which is
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_snd` read the same way. -/
theorem fV_comp_snd (i j : I) :
    fV U f g i j ≫ pullback.snd (X.ofRestrict (U i) ≫ f) g =
      t U f g i j ≫ fV U f g j i ≫ pullback.snd (X.ofRestrict (U j) ≫ f) g := by
  simp [t_fst_snd]

/-- **The first projection**, `glued ⟶ X`, glued out of
`ComplexAnalytic.AnalyticSpace.Pullback.toBase`.

`ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` rather than
`CategoryTheory.Limits.Multicoequalizer.desc`, which is what Mathlib uses, because it returns a
morphism of **analytic spaces**. -/
noncomputable def p1 : glued U f g ⟶ X :=
  glueMorphismsOfGlueData (gluing U f g) _ (glueDataCLinear_gluing U f g)
    (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).hasLocalModels)
    (fun j ↦ forgetToLocallyRingedSpace.map (toBase U f g j))
    (fun i j ↦ by
      have h := congrArg forgetToLocallyRingedSpace.map (fV_comp_toBase U f g i j)
      simp only [Functor.map_comp] at h
      exact h)
    (fun j ↦ (toBase U f g j).isCLinear)

/-- **The second projection**, `glued ⟶ Y`, glued out of the second projections of the ambient
pullbacks. -/
noncomputable def p2 : glued U f g ⟶ Y :=
  glueMorphismsOfGlueData (gluing U f g) _ (glueDataCLinear_gluing U f g)
    (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).hasLocalModels)
    (fun j ↦ forgetToLocallyRingedSpace.map (pullback.snd (X.ofRestrict (U j) ≫ f) g))
    (fun i j ↦ by
      have h := congrArg forgetToLocallyRingedSpace.map (fV_comp_snd U f g i j)
      simp only [Functor.map_comp] at h
      exact h)
    (fun j ↦ (pullback.snd (X.ofRestrict (U j) ≫ f) g).isCLinear)

/-- **The ambient square commutes**, which is
`CategoryTheory.Limits.pullback.condition` at the cospan the `j`-th member presents, composed with
the open-subspace inclusion. -/
theorem toBase_comp (j : I) :
    toBase U f g j ≫ f = pullback.snd (X.ofRestrict (U j) ≫ f) g ≫ g := by
  simp [toBase, pullback.condition]

/-- **The first projection restricts to `…toBase` on the `j`-th member.**

The statement is about the underlying morphism of locally ringed spaces because that is where the
member inclusion `ι j` lives — the members of a glue datum are locally ringed spaces and are not
objects of `ComplexAnalytic.AnalyticSpace`, which is the reason
`ComplexAnalytic.AnalyticSpace.ι_glueMorphismsOfGlueData` is stated there. -/
theorem ι_p1 (j : I) :
    (gluing U f g).toGlueData.ι j ≫ (p1 U f g).toLRSHom =
      forgetToLocallyRingedSpace.map (toBase U f g j) :=
  ι_glueMorphismsOfGlueData (gluing U f g) _ (glueDataCLinear_gluing U f g) _
    (fun j ↦ forgetToLocallyRingedSpace.map (toBase U f g j)) _ _ j

/-- **The second projection restricts to the ambient second projection on the `j`-th member.** -/
theorem ι_p2 (j : I) :
    (gluing U f g).toGlueData.ι j ≫ (p2 U f g).toLRSHom =
      forgetToLocallyRingedSpace.map (pullback.snd (X.ofRestrict (U j) ≫ f) g) :=
  ι_glueMorphismsOfGlueData (gluing U f g) _ (glueDataCLinear_gluing U f g) _
    (fun j ↦ forgetToLocallyRingedSpace.map (pullback.snd (X.ofRestrict (U j) ≫ f) g)) _ _ j

/-- **The square commutes.**

Checked member by member: `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful,
`AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext` reduces an equation on the gluing to one
on each member, and there the two sides are the images of the two sides of
`ComplexAnalytic.AnalyticSpace.Pullback.toBase_comp`. **This is a statement about morphisms of
analytic spaces**; the reduction to locally ringed spaces is the proof and not the statement. -/
theorem p_comm : p1 U f g ≫ f = p2 U f g ≫ g := by
  apply forgetToLocallyRingedSpace.map_injective
  refine (gluing U f g).hom_ext _ _ fun j ↦ ?_
  change (gluing U f g).toGlueData.ι j ≫ (p1 U f g).toLRSHom ≫ _ =
    (gluing U f g).toGlueData.ι j ≫ (p2 U f g).toLRSHom ≫ _
  rw [← Category.assoc, ← Category.assoc, ι_p1, ι_p2]
  have h := congrArg forgetToLocallyRingedSpace.map (toBase_comp U f g j)
  simp only [Functor.map_comp] at h
  exact h

end ComplexAnalytic.AnalyticSpace.Pullback

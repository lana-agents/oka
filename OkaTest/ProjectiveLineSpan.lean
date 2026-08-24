/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.ProjectiveLine

/-!
# The overlap of the two charts of `ℙ¹`, as a span

`OkaTest/LocalisationChain.lean` writes down the diagram a `trans_comp` law is a claim about — a
chain of three — and says in terms that the other law of a locally directed cover wants a
different one:

> the two laws want two different diagrams: `trans_comp` wants a **chain** of three, which is this
> file, and `directed` wants a **cospan** of three, which is not.

**The word in that quotation is wrong** — the diagram it points at is a span, for the reason the
next section gives — and the sentence is quoted as it stands on `master` rather than repaired
here.

This file is that other diagram, at `ℙ¹`: the two charts and their overlap, as a functor out of
`CategoryTheory.Limits.WalkingSpan`, together with its analytification.

## It is a span and not a cospan, and the word decides the shape

In `ComplexAnalytic.Presentation` a morphism runs in the direction of a morphism of *spaces*:
`ComplexAnalytic.localisationHom g f` goes from the presentation of the distinguished open to the
presentation it was cut out of, so an arrow means *"is a distinguished open of"*. The overlap is a
distinguished open of **both** charts, so it is the apex and both arrows point out of it.
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/Cospan.lean` is where the two words are fixed:
`CategoryTheory.Limits.span` takes two arrows out of a common source and
`CategoryTheory.Limits.cospan` takes two into a common target.

That is also what the law asks for. `directed` asks, for a point of an overlap `𝒰ᵢ ×_X 𝒰ⱼ`, for a
member `k` together with arrows `k ⟶ i` and `k ⟶ j` — `k` **below** both, arrows **out** of `k`.
A cospan would be the assertion that some member is above both, which is not what a cover gives
and not what `ℙ¹` has.

## The functor law is free here, and that is the whole structural difference from the chain

`OkaTest/LocalisationChain.lean` needed `OkaTest.LocalisationChain.ofThree` because `Fin 3` has a
composable pair of non-identity arrows, so `map_comp` at `0 ≤ 1 ≤ 2` was a theorem and had to be
kept from being true by definition.

**`CategoryTheory.Limits.WalkingSpan` has no composable pair of non-identity arrows at all.** Its
two non-identity arrows both leave the apex, and nothing leaves either foot, so every instance of
`map_comp` has an identity on one side and is forced by `map_id`. `CategoryTheory.Limits.span` is
therefore already a functor and `OkaTest.ProjectiveLineSpan.lineSpan` costs one line and proves
nothing by existing. A reader looking for the analogue of
`OkaTest.LocalisationChain.chainFunctor`'s coherence hypothesis will not find one, and should not:
there is no coherence to discharge on this shape.

The content is therefore entirely in what the objects and the arrows are.

## What carries the content instead

* **The two feet are the same object, and that cannot be repaired.** The chain's non-vacuity was
  `OkaTest.LocalisationChain.chainFunctor_obj_injective`, three pairwise distinct objects
  separated by `ComplexAnalytic.Presentation.n`. The corresponding statement is **false** here:
  `OkaTest/ProjectiveLine.lean`'s `ComplexAnalytic.lineCoverObj` is `fun _ ↦ ⟨1, 0, lineRel⟩`, so
  both feet are `𝔸¹` on the nose. That is what `ℙ¹` is, not a defect of the diagram.
* **So the non-vacuity is about the arrows.**
  `OkaTest.ProjectiveLineSpan.lineSpanFst_ne_lineSpanSnd` — and, on the diagram itself,
  `OkaTest.ProjectiveLineSpan.lineSpan_map_fst_ne_map_snd` — say the two legs are different
  morphisms between the same pair of objects. The reason is
  `OkaTest.ProjectiveLineSpan.lineSpanFst_apply` and
  `OkaTest.ProjectiveLineSpan.lineSpanSnd_apply`: the coordinate `z` of the chart is pulled back
  to `z` down one leg and to `1/z` down the other, and
  `ComplexAnalytic.mk_X_one_ne_mk_X_zero` separates those two elements of `ℂ[z, t] ⧸ (t z - 1)`.
  This is exactly the fact `OkaTest/AffineCover.lean` cannot state about its own transition, whose
  `glue` is `Iso.refl`.
* **The apex is a third object and not a foot under another name.**
  `OkaTest.ProjectiveLineSpan.lineSpan_obj_zero_ne_obj_left` says so as a statement about the
  diagram, separating the objects by the number of variables.
  `ComplexAnalytic.localisationOpen_lineRel_ne_top` says the open `D(z)` that the apex presents is
  not the whole chart, and `ComplexAnalytic.localisationOpen_lineRel_ne_bot` says it is not empty.
  Those two are statements about that **open subset of one chart**, and that is all that is drawn
  from them here: the apex is a proper, non-empty part of each foot, so the span really has three
  objects to be a span of, which is what a two-object diagram cannot supply.

  **Neither lemma says that neither chart is a distinguished open of the other.** That is a
  stronger claim about the two feet's relation to each other, it would need an argument of its
  own, and nothing in this repository proves it.

## What is not here

**No `directed` law is stated**, and not because it could not be. The pullback the law quantifies
over exists at this level:
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left` and
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_right` are instances giving
the pullback of two morphisms one of which is an open immersion, which is all `directed` ever
sees, and `AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback` identifies the
pullback of two inclusions of a glue data with the overlap `V` that datum carries. Stating and
proving the law is separate work and is not done here.

**No analytic analogue of the `LocallyDirected` class**, and no import of
`Mathlib/AlgebraicGeometry/Cover/Directed.lean`. `OkaTest/LocalisationChain.lean` declined both
for the same reason and the reason is unchanged: a single diagram is what tells you whether such a
class would have anything to quantify over, and defining one is a design decision.

**No claim that these are the only two legs**, or that they are canonical. The span records two
arrows out of the apex and says they differ; it says nothing about a third.

**No claim that the diagram is a limit or a colimit of anything.** In particular nothing here says
the apex is the pullback of the two feet over the glued space.
`AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback`, cited above, is about the `V` field
of a glue data — for `ℙ¹` that is `ComplexAnalytic.projectiveLineGlueData` — and it is not
connected to this diagram anywhere below.

**Nothing about `ℙ¹` that `OkaTest/ProjectiveLine.lean` does not already say.** That file is
explicit that nothing in it shows the glued space is `ℙ¹`: it is not shown compact and not shown
to differ from the analytification of a single presentation. This file adds no such statement and
inherits that disclaimer whole.
-/

open CategoryTheory CategoryTheory.Limits ComplexAnalytic MvPolynomial

universe u

namespace OkaTest.ProjectiveLineSpan

noncomputable section

/-! ### The two legs -/

/-- **The first leg: the overlap is a distinguished open of the first chart**, by the polynomial
`ComplexAnalytic.lineZ` that cuts it out, with no transition applied.

The source is `ComplexAnalytic.linePres`, which is `localisationPresentation lineRel lineZ`, and
`OkaTest/ProjectiveLine.lean` records by `rfl` that this is the presentation
`ComplexAnalytic.coverOverlap` produces for **both** ordered pairs of charts. -/
def lineSpanFst : (⟨2, 1, linePres.{u}⟩ : Presentation.{u}) ⟶ ⟨1, 0, lineRel.{u}⟩ :=
  localisationHom.{u} lineRel.{u} lineZ.{u}

/-- **The second leg: the same overlap is a distinguished open of the second chart**, read through
the transition `ComplexAnalytic.lineSwapIso`.

The two descriptions of the overlap are the same presentation, which is what lets the transition
be an automorphism and what lets this composite typecheck at the same pair of objects as
`OkaTest.ProjectiveLineSpan.lineSpanFst`. -/
def lineSpanSnd : (⟨2, 1, linePres.{u}⟩ : Presentation.{u}) ⟶ ⟨1, 0, lineRel.{u}⟩ :=
  (lineSwapIso.{u} ⟨0⟩ ⟨1⟩).hom ≫ localisationHom.{u} lineRel.{u} lineZ.{u}

/-! ### The diagram -/

/-- **The two charts of `ℙ¹` and their overlap, as a functor out of the walking span.**

One line, and deliberately so: `CategoryTheory.Limits.WalkingSpan` has no composable pair of
non-identity arrows, so there is no functor law to discharge and nothing here is a theorem. See
the header. -/
def lineSpan : WalkingSpan ⥤ Presentation.{u} := span lineSpanFst.{u} lineSpanSnd.{u}

/-- The apex of the span is the overlap. -/
theorem lineSpan_obj_zero : lineSpan.{u}.obj WalkingSpan.zero = ⟨2, 1, linePres.{u}⟩ := rfl

/-- The left foot of the span is the affine line. -/
theorem lineSpan_obj_left : lineSpan.{u}.obj WalkingSpan.left = ⟨1, 0, lineRel.{u}⟩ := rfl

/-- The right foot of the span is the affine line **as well** — the two feet are the same object,
which is why the non-vacuity below is about the arrows and not about the objects. -/
theorem lineSpan_obj_right : lineSpan.{u}.obj WalkingSpan.right = ⟨1, 0, lineRel.{u}⟩ := rfl

/-- **The apex is neither foot**, so the diagram really has three objects to be a span of and not
two. One statement covers both feet, since
`OkaTest.ProjectiveLineSpan.lineSpan_obj_left` and `OkaTest.ProjectiveLineSpan.lineSpan_obj_right`
are the same object.

It separates them by `ComplexAnalytic.Presentation.n`, the number of variables — two for the
overlap and one for a chart — and that is the **syntactic** half of what the header claims. The
geometric half is `ComplexAnalytic.localisationOpen_lineRel_ne_top` and
`ComplexAnalytic.localisationOpen_lineRel_ne_bot`, which say the open subset the apex presents is
a proper non-empty part of the chart; those are statements about that open subset and are not what
this proof uses. **Neither half replaces the other**: a presentation on more variables need not
cut out a smaller space, and a smaller space need not be presented on more variables. -/
theorem lineSpan_obj_zero_ne_obj_left :
    lineSpan.{u}.obj WalkingSpan.zero ≠ lineSpan.{u}.obj WalkingSpan.left := by
  intro h
  exact absurd (congrArg Presentation.n h) (by decide)

/-- **The analytification of the span**: two copies of the affine line, their overlap, and the two
maps between them, as a diagram of complex analytic spaces.

Those two maps are open immersions, but only the first of them is on the record:
`ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom` is exactly the first leg,
and the second is that composed with the isomorphism `ComplexAnalytic.lineSwapIso`, a composite
nothing here states. So the word is used of the first leg and inferred for the second, and no
statement below is about either.

One line, because `ComplexAnalytic.analytificationFunctor` is a functor on the nose. It is the
step that makes the exercise about analytic spaces rather than about algebra, which is the same
reason `OkaTest.LocalisationChain.analyticChain` is there. -/
def analyticLineSpan : WalkingSpan ⥤ AnalyticSpace.{u} :=
  lineSpan.{u} ⋙ analytificationFunctor.{u}

/-! ### The two legs are different, which is the whole content

The coordinate `z` of a chart is pulled back to `z` down one leg and to `1/z` down the other. Both
computations are on the ring map, and `ComplexAnalytic.mk_X_one_ne_mk_X_zero` separates the two
answers. -/

/-- **The first leg carries `z` to `z`**: no transition is applied, and
`ComplexAnalytic.localisationIncl` keeps the old coordinate as the variable `0`. -/
theorem lineSpanFst_apply :
    lineSpanFst.{u}.toRingHom
        (Ideal.Quotient.mk (presentationIdeal.{u} lineRel.{u}) (X (ULift.up 0))) =
      Ideal.Quotient.mk (presentationIdeal.{u} linePres.{u}) (X (ULift.up 0)) := by
  simp [lineSpanFst, localisationHom, localisationPresHom, localisationIncl]

/-- **The second leg carries `z` to `t`**, which is `1/z` on the overlap: the transition
`ComplexAnalytic.lineSwapIso` exchanges the two variables of `ℂ[z, t] ⧸ (t z - 1)`.

The composition of `ComplexAnalytic.PresHom` is contravariant on the underlying ring maps, so
`(ψ ≫ χ).toRingHom` is `ψ.toRingHom.comp χ.toRingHom` with the factors in that order. `hc` is
`rfl`, and what it buys is the **spelling**: the goal presents the composite as `≫`, which `rw`
cannot match against `RingHom.comp`, so the rewrites need a hypothesis that states it in the
`RingHom.comp` form. A `show` is not the obstacle — it is a definitional-equality check, it sees
through the `Category` instance, and the same proof goes through with the `have` replaced by a
`show` at that form. -/
theorem lineSpanSnd_apply :
    lineSpanSnd.{u}.toRingHom
        (Ideal.Quotient.mk (presentationIdeal.{u} lineRel.{u}) (X (ULift.up 0))) =
      Ideal.Quotient.mk (presentationIdeal.{u} linePres.{u}) (X (ULift.up 1)) := by
  have hc : lineSpanSnd.{u}.toRingHom =
      (lineSwapIso.{u} ⟨0⟩ ⟨1⟩).hom.toRingHom.comp lineSpanFst.{u}.toRingHom := rfl
  rw [hc, RingHom.comp_apply, lineSpanFst_apply, lineSwapIso_hom_toRingHom_mk_X,
    lineSwap_up_zero]

/-- **The two legs are different morphisms.**

They have the same source and the same target — the two feet of this span are one object — so
nothing about the endpoints separates them, and the separation has to come from what they do. It
comes from the coordinate: `z` down one leg and `1/z` down the other. This is the statement that
`OkaTest/AffineCover.lean` has no analogue of, its transition being `Iso.refl`. -/
theorem lineSpanFst_ne_lineSpanSnd : lineSpanFst.{u} ≠ lineSpanSnd.{u} := by
  intro hcon
  refine mk_X_one_ne_mk_X_zero.{u} ?_
  rw [← lineSpanSnd_apply, ← hcon, lineSpanFst_apply]

/-- **The same statement about the diagram rather than about the two morphisms it was built
from**: the images of the walking span's two non-identity arrows are different.

The proof is `OkaTest.ProjectiveLineSpan.lineSpanFst_ne_lineSpanSnd` unchanged, because
`CategoryTheory.Limits.span` puts the two legs on those two arrows definitionally — so what this
adds is not an argument but the identification, checked by the elaborator rather than assumed.
Without it the previous theorem would be a fact about two definitions that
`OkaTest.ProjectiveLineSpan.lineSpan` might not have used. -/
theorem lineSpan_map_fst_ne_map_snd :
    lineSpan.{u}.map WalkingSpan.Hom.fst ≠ lineSpan.{u}.map WalkingSpan.Hom.snd :=
  lineSpanFst_ne_lineSpanSnd.{u}

end

end OkaTest.ProjectiveLineSpan

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.ProjectiveLine

/-!
# A refinement of the two-chart cover of `ℙ¹` that actually refines something

`Oka/Analytification/RefineDatumUnitFamily.lean` builds the analytic space of a refined cover
datum at an injective index map and a refining family that is a unit on each overlap, taking the
original datum's three laws and nothing else. **This file meets all of that at a cover datum whose
three laws are proved**, so the resulting `ComplexAnalytic.AnalyticSpace` has no open hypothesis
at all.

The cover is `OkaTest/ProjectiveLine.lean`'s: two copies of `𝔸¹`, every overlap cut out by the
coordinate `z`, transition `z ↦ 1/z`. The index map is `id` on `ComplexAnalytic.pair`, which is
injective and — by `ComplexAnalytic.not_isConstant_id` — not constant. The refining family is `z`
itself, and `ComplexAnalytic.lineCoverPoly` is the constant family `z`, so the hypothesis that the
family be a unit on each overlap is `ComplexAnalytic.isUnit_mk_rename_localisationIncl` verbatim:
the polynomial that was inverted is a unit upstairs.

## Why this is not either degeneracy the board has already been caught by

`ComplexAnalytic.refineDatumObj obj σ fam b` is the distinguished open `D(fam b)` of the member
`σ b`, so what the refining family is decides whether a "refinement" refines anything. **That step
is a theorem here and not a composition left to the reader** —
`ComplexAnalytic.refineDatumObj_lineRefineFam` identifies the refined member with the chart
localised at the family, and `ComplexAnalytic.range_base_localisationProj_lineRefineFam` puts it
in the chart as `D(z)` — which is what makes the two non-degeneracy statements below statements
about *this refinement* rather than about an open of its chart:

* `Oka/Analytification/RefineDatumWitness.lean`'s witness takes `fam ≡ 1`, where `D(1)` is the
  whole member and the refined cover is the original one reindexed;
* `OkaTest/CoverRefinement.lean` exists because this project accepted `fam ≡ 0` once, where
  `D(0)` is empty and every overlap with it.

Here `D(z)` is **neither**, and both halves are quotations of the non-degeneracy statements
`OkaTest/ProjectiveLine.lean` proves for its own cover:
`ComplexAnalytic.localisationOpen_lineRefineFam_ne_top` and `…_ne_bot`.

## What this instance is *not* evidence about, and it is both range conditions

**At two members both adopted range conditions are vacuous**, since each is quantified over a
triple of pairwise different indices of `ComplexAnalytic.pair` and there is none
(`ComplexAnalytic.pair_no_distinct_triple`) — the same reason
`OkaTest/ProjectiveLine.lean`'s module docstring gives for `hrange` and `hcocycle` there. So what
this instance exercises is the **choice** conditions and the cross-member `glue` at a family that
is not `1`, and nothing else; the two range conditions are discharged at every index type by
`ComplexAnalytic.refineDatumRangeCross_poly` and
`ComplexAnalytic.refineDatumRangeEq_of_injective`, which is where the evidence for them is.

A proper refinement at **three** members — `OkaTest/AffineCover.lean`'s `nodeCover` at `σ = id`
and the family `nodeX`, whose `ComplexAnalytic.nodeCoverPoly` is constant in the same way — would
exercise `RefineDatumRangeCross` as well, and is not built here.

## And it does not meet the covering condition, which is what refining costs

`Oka/Analytification/RefineDatumCover.lean` asks a refining family to **cover**
(`ComplexAnalytic.RefineDatumCovers`): every point of every member of the original cover must lie
in a refined member lying over that member. **This refinement does not**, and the reason is the
same fact that makes it a refinement at all. Its index map is the identity, so that file's
`ComplexAnalytic.not_refineDatumCovers_id_of_ne_top` applies with nothing in between, and its
hypothesis is `ComplexAnalytic.localisationOpen_lineRefineFam_ne_top` — the statement already
proved above that `D(z)` is a *proper* open of its chart. So the theorem below is the two
non-degeneracy statements read once more, in the vocabulary of the condition: **a family that cuts
a member down cannot cover it.**

**That does not by itself say the refinement fails to cover**, and no sentence here should be read
as though it did. `ComplexAnalytic.RefineDatumCovers` is a *sufficient* condition for the morphism
down to be surjective and `ComplexAnalytic.dupStrict` is exactly the theorem that it is not a
necessary one, so a datum that fails the condition may still have a surjection down. **The two
questions are answered separately below and they happen to agree**, which they were under no
obligation to do.

## And it does not cover, which is the second question and needed the first's answer for nothing

`ComplexAnalytic.lineRefineToBase` is `ComplexAnalytic.refineDatumUnitFamToBase`
(`Oka/Analytification/RefineDatumCover.lean`) at this refinement;
`ComplexAnalytic.not_surjective_base_lineRefineToBase` says it is **not surjective**.
So the refined space does not map onto the space it refines, and this is the first statement on
this board about a refining family that cuts its members down rather than about `fam ≡ 1`.

The route is `ComplexAnalytic.surjective_base_refineDatumUnitFamToBase_iff` — surjective exactly
when the images of the refined members are everything — spent in the negative direction, which is
the direction `Oka/Analytification/RefineDatumCover.lean` says a caller arguing the other way has
and which had no consumer until now. **The point that is missed is the origin of the first
chart**, and the two cases are the two ways it could have been reached: through the first chart,
where
`ComplexAnalytic.isOpenImmersion_lineIota`'s open embedding is injective and
`ComplexAnalytic.lineOrigin_notMem_localisationOpen` finishes it, and through the second, which is
`ComplexAnalytic.lineOrigin_notMem_range_ι` with the point of the first member left arbitrary.

**What this is not is a statement about `ℙ¹`.** `OkaTest/ProjectiveLine.lean` says in terms that
nothing there shows the glued space *is* `ℙ¹` — it is not shown compact and not distinguished from
the analytification of a single presentation. So what is missed is **the origin of the first
chart** and not *the point `0` of the projective line*, and nothing here says whether the second
chart's origin is the same point of the gluing or a different one: one missed point is what the
theorem below produces and one is all it claims.

## Main definitions

- `ComplexAnalytic.lineRefineFam`: **the refining family**, the coordinate `z` on each chart.
- `ComplexAnalytic.lineRefinement`: **the analytic space of the refined cover**, with no
  hypothesis left open.
- `ComplexAnalytic.lineRefineToBase`: **the morphism down to the cover it refines**, out of
  `ComplexAnalytic.lineRefinement` and into `ComplexAnalytic.projectiveLineSpace`. It is
  `ComplexAnalytic.refineDatumUnitFamToBase` at this refinement — ten arguments where this file
  once spelled `ComplexAnalytic.refineDatumToBase` at fifteen — and both of its ends are
  definitionally one of those two objects, so its type names them.

## Main results

- `ComplexAnalytic.isUnit_lineRefineFam`: **the family is a unit on each overlap**, which is the
  one hypothesis of the construction that is about the family.
- `ComplexAnalytic.refineDatumObj_lineRefineFam`: **the refined member is the chart localised at
  the family**, and `ComplexAnalytic.range_base_localisationProj_lineRefineFam`: **its image in
  the chart is `D(z)`.** These two are what the next two statements are read through.
- `ComplexAnalytic.localisationOpen_lineRefineFam_ne_top`: **each refined member is a proper open
  of its chart**, so this refines and does not reindex.
- `ComplexAnalytic.localisationOpen_lineRefineFam_ne_bot`: **and is not empty**, so it is not
  `OkaTest/CoverRefinement.lean`'s degenerate family either.
- `ComplexAnalytic.not_isConstant_id_pair`: **the index map is not constant**, which is
  `ComplexAnalytic.not_isConstant_id` at this instance and is what makes this a witness at a
  non-constant `σ` rather than only at an injective one.
- `ComplexAnalytic.not_refineDatumCovers_lineRefineFam`: **and this refinement does not cover in
  the sense the refining condition asks**, because a proper open is not the whole member. It is a
  statement about the condition and not about any morphism.
- `ComplexAnalytic.not_surjective_base_lineRefineToBase`: **and the morphism down really is not
  surjective**, which is the other question and does not follow from the one above — the origin of
  the first chart is in the image of neither refined member.
- `ComplexAnalytic.not_isIso_lineRefineToBase`: **so the morphism down is not an isomorphism**,
  which is the first such statement on this board about a refinement that refines. It is a
  statement about this morphism and **not** about whether the two spaces are isomorphic; see this
  file's `## What is not here`.

## What is not here

* **No claim that the refined space is `ℙ¹`, or that it is not.** It is the gluing of two copies
  of `𝔸¹ ∖ {0}` along `D(z)` in each. **What that gluing is has since been identified**, and this
  bullet said nothing about it: the `D(z)` the two copies are glued along is the *whole* of each of
  them, so `ComplexAnalytic.isoLineRefineGlued` (`OkaTest/RefineDatumUnitFamilyNode.lean`) says the
  glued space is one copy of `𝔸¹ ∖ {0}`. **The comparison with `ℙ¹` is still absent** — that would
  need the two spaces to be told apart, which nothing here does.

  **This bullet used to say that no morphism relates the refined space to
  `ComplexAnalytic.projectiveLineSpace` in either direction, and that there was no comparison
  morphism here at all.** Both were true when they were written and stopped being true when
  `ComplexAnalytic.lineRefineToBase` was declared below: that morphism goes out of
  `ComplexAnalytic.lineRefinement` and into `ComplexAnalytic.projectiveLineSpace`, and
  `ComplexAnalytic.not_isIso_lineRefineToBase` says it is not an isomorphism. **What is absent is
  the comparison of the two *spaces*, not of nothing at all**, and the two are different claims:
  refuting `IsIso` for one morphism leaves open that some other morphism is one.
  `ComplexAnalytic.not_isIso_refineToBase` (`Oka/Analytification/CoverRefinement.lean`) still does
  not apply here, but not for want of a morphism — it is about
  `ComplexAnalytic.refineToBase`, a refinement of a *single presentation* at an empty family, which
  is a different construction from `ComplexAnalytic.refineDatumToBase` at a cover datum.
* **Nothing about the refined overlaps being the geometric ones**, which is
  `Oka/Analytification/CrossMemberDatumGlue.lean`'s absence and is about the construction rather
  than about any input to it.
* **Nothing about the morphism down beyond its image missing one point.** The refined space does
  not map onto the space it refines, and that is all: **no fibre, no injectivity, no claim that the
  image is exactly the complement of two points**, and nothing about the refined members forming an
  open cover of anything.

  **This bullet used to say that `ComplexAnalytic.lineRefineToBase`'s body is spelled here at
  fifteen arguments because nothing in `Oka/` names the morphism at the unit family, that a
  `refineDatumUnitFamToBase` there would be the better shape, and that it would cost
  `Oka/Analytification/RefineDatumUnitFamily.lean` and
  `Oka/Analytification/RefineDatumToBase.lean` an import edge between two siblings.** All three
  were true when they were written and none is now. `ComplexAnalytic.refineDatumUnitFamToBase`
  (`Oka/Analytification/RefineDatumCover.lean`) names it, the body below **is** that definition at
  ten arguments, and **the edge that bullet priced is not the edge that was paid**: that route was
  measured at `+5` `Oka` modules and `+2` Mathlib roots and declined for the file where the trivial
  family's counterpart already lives, which costs `+1` and `+0`. Nothing in this file spells
  fifteen arguments any more, and citing the definition by name costs no import — this file already
  reaches it.
* **No axiom guards.** Declarations of the test library carry none —
  `ComplexAnalytic.nodeCoverObj` and `ComplexAnalytic.lineCoverObj` are the precedent — and
  `OkaTest/Axioms.lean`'s placement rule is about `Oka/`.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The refining family, and it is the coordinate -/

/-- **The refining family**: the coordinate `z` on each of the two charts.

It is written against `id` rather than against nothing because the construction indexes a family
by `b : B` at the member `σ b`, and here `B = J = pair` with `σ = id`. -/
abbrev lineRefineFam : ∀ b : pair.{u},
    MvPolynomial (ULift.{u} (Fin (lineCoverObj.{u} (id b)).n)) ℂ := fun _ ↦ lineZ.{u}

/-- **The family is a unit on each overlap**, which is
`ComplexAnalytic.refineDatumUnitFamAnalytification`'s one hypothesis about the family.

`ComplexAnalytic.lineCoverPoly` is the constant family `z`, so the polynomial the class is taken
in is the one being asserted invertible and this is
`ComplexAnalytic.isUnit_mk_rename_localisationIncl` with nothing in between. **That is what makes
this cover the cheap instance**: a family which is a unit on the overlap without being the
overlap's own polynomial would need an argument here. -/
theorem isUnit_lineRefineFam (a b : pair.{u}) (_h : id a ≠ id b) :
    IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (lineCoverObj.{u} (id a)).g (lineCoverPoly.{u} (id a) (id b))))
      (MvPolynomial.rename (localisationIncl.{u} (lineCoverObj.{u} (id a)).n)
        (lineRefineFam.{u} a))) :=
  isUnit_mk_rename_localisationIncl.{u} (lineCoverObj.{u} a).g lineZ.{u}

/-! ### The refinement -/

/-- **The analytic space of the refined cover**, and it has no open hypothesis.

`ComplexAnalytic.refineDatumUnitFamAnalytification` at `OkaTest/ProjectiveLine.lean`'s cover
datum, `σ = id`, and the coordinate as the refining family: the three laws are
`ComplexAnalytic.hsymm_lineCover`, `ComplexAnalytic.hrange_lineCover` and
`ComplexAnalytic.hcocycle_lineCover`, the injectivity is `Function.injective_id`, and the family's
hypothesis is the theorem above. -/
def lineRefinement : AnalyticSpace.{u} :=
  refineDatumUnitFamAnalytification.{u} lineCoverObj.{u} lineCoverPoly.{u} id lineRefineFam.{u}
    lineSwapIso.{u} isUnit_lineRefineFam.{u} hsymm_lineCover.{u} hrange_lineCover.{u}
    Function.injective_id hcocycle_lineCover.{u}

/-! ### And it refines -/

/-- **The refined member at `b` is the chart localised at the family.**

Definitionally: the `g` of `ComplexAnalytic.refineDatumObj obj σ fam b` *is*
`ComplexAnalytic.localisationPresentation (obj (σ b)).g (fam b)`, and here `σ = id`. The `g` and
not the member — `ComplexAnalytic.refineDatumObj` returns a `ComplexAnalytic.Presentation`, whose
other two fields are the variable and relation counts — which is why the statement below is the
one it is, and not an equation between presentations. **It is stated because the two properness
theorems below are about the localisation and the sentences around them are about the refined
member**, and until this theorem existed a reader had to make
that identification themselves — the shape `Oka/Analytification/RefineDatumWitness.lean`'s own
absence bullet was written against. -/
theorem refineDatumObj_lineRefineFam (b : pair.{u}) :
    (refineDatumObj.{u} lineCoverObj.{u} (id : pair.{u} → pair.{u}) lineRefineFam.{u} b).g =
      localisationPresentation.{u} (lineCoverObj.{u} b).g (lineRefineFam.{u} b) :=
  rfl

/-- **And it sits inside its chart as `D(z)`.**

`ComplexAnalytic.range_base_localisationProj` at this family: the image of the refined member's
projection into the chart is the distinguished open the two theorems below are statements about.
**This is what turns them into statements about the refinement** rather than about an open of the
chart that a reader is left to connect to it. -/
theorem range_base_localisationProj_lineRefineFam (b : pair.{u}) :
    Set.range (localisationProj.{u} (lineCoverObj.{u} b).g (lineRefineFam.{u} b)).toLRSHom.base =
      (localisationOpen.{u} (lineCoverObj.{u} b).g (lineRefineFam.{u} b) :
        Set (AnalyticSpace.analytification.{u} (lineCoverObj.{u} b).g)) :=
  range_base_localisationProj.{u} _ _

/-- **Each refined member is a proper open of its chart.**

`ComplexAnalytic.localisationOpen_lineRel_ne_top`, which `OkaTest/ProjectiveLine.lean` proves from
the origin lying off `D(z)`. The two theorems above are what make it a statement about the refined
member: by `ComplexAnalytic.refineDatumObj_lineRefineFam` that member is the chart localised at
`z`, and by `ComplexAnalytic.range_base_localisationProj_lineRefineFam` it sits in the chart as
exactly this open. So this says the refinement is not
`Oka/Analytification/RefineDatumWitness.lean`'s reindexing, where `fam ≡ 1` and `D(1)` is the
whole member. -/
theorem localisationOpen_lineRefineFam_ne_top (b : pair.{u}) :
    localisationOpen.{u} (lineCoverObj.{u} b).g (lineRefineFam.{u} b) ≠ ⊤ :=
  localisationOpen_lineRel_ne_top.{u}

/-- **And it is not empty**, so this is not the other degeneracy: `OkaTest/CoverRefinement.lean`
exists because a family constantly `0` was accepted once, and there every overlap is empty.
`ComplexAnalytic.localisationOpen_lineRel_ne_bot`, from the point `z = 1`, read as a statement
about the refined member through the same two theorems. -/
theorem localisationOpen_lineRefineFam_ne_bot (b : pair.{u}) :
    localisationOpen.{u} (lineCoverObj.{u} b).g (lineRefineFam.{u} b) ≠ ⊥ :=
  localisationOpen_lineRel_ne_bot.{u}

/-- **The index map of this refinement is not constant.**

`ComplexAnalytic.refineDatumUnitFamAnalytification` asks for an *injective* `σ` and the absence
five files recorded is worded about a *non-constant* one, so the two have to be joined at the
instance rather than left to a reader. `ComplexAnalytic.not_isConstant_id` at
`ComplexAnalytic.pair`, which is `Nontrivial`. -/
theorem not_isConstant_id_pair :
    ¬ ∃ j : pair.{u}, ∀ b : pair.{u}, (id : pair.{u} → pair.{u}) b = j :=
  not_isConstant_id.{u}

/-! ### And it does not meet the covering condition -/

/-- **This refinement does not meet the refining condition.**

`ComplexAnalytic.not_refineDatumCovers_id_of_ne_top` at the first chart, whose hypothesis is
`ComplexAnalytic.localisationOpen_lineRefineFam_ne_top` — `D(z)` is a proper open of its chart. The
index map being the identity is what makes the general theorem apply with nothing in between: at
`σ = id` the condition is one equation per member, and this family fails it at every member rather
than only at the one named here.

**Nothing about surjectivity follows.** `ComplexAnalytic.RefineDatumCovers` is sufficient for the
morphism down to be surjective and `ComplexAnalytic.dupStrict` says it is not necessary, so this
refutes the condition and leaves the morphism untouched; that question is not asked in this file at
all. -/
theorem not_refineDatumCovers_lineRefineFam :
    ¬ RefineDatumCovers.{u} lineCoverObj.{u} (id : pair.{u} → pair.{u}) lineRefineFam.{u} :=
  not_refineDatumCovers_id_of_ne_top.{u} lineCoverObj.{u} lineRefineFam.{u} (ULift.up 0)
    (localisationOpen_lineRefineFam_ne_top.{u} (ULift.up 0))

/-! ### And it does not cover: the morphism down is not surjective -/

/-- **The morphism down to the cover this refinement refines.**

`ComplexAnalytic.refineDatumUnitFamToBase` (`Oka/Analytification/RefineDatumCover.lean`) at this
refinement, which is **ten** arguments: the cover datum, its polynomials, the index map, the
refining family, the transition isomorphism, `ComplexAnalytic.isUnit_lineRefineFam`, the two laws
and `Function.injective_id`, then the cocycle law.

**This body was `ComplexAnalytic.refineDatumToBase` at fifteen**, spelled out because nothing in
`Oka/` named the morphism at a family that is a unit on each overlap — the four cross-member
choices written at this refinement, and the two range conditions
`ComplexAnalytic.refineDatumRangeCross_poly` and `ComplexAnalytic.refineDatumRangeEq_of_injective`
discharged here. **Those are now that definition's own arguments and not this file's**, which is
what naming it was for; the term is the same one, since the definition is
`ComplexAnalytic.refineDatumToBase` at exactly those fifteen and unfolds to it at default
transparency.

**A `def` and not a `have` inside the theorem below**, because the source and target are worth
being able to name — which the type above does, since **each end is one of this file's named
objects on the nose** and neither is a gluing:

* the source **is** `ComplexAnalytic.lineRefinement`, and not an analytification that definition is
  built from. `ComplexAnalytic.lineRefinement` is
  `ComplexAnalytic.refineDatumUnitFamAnalytification` at these arguments, which is also what
  `ComplexAnalytic.refineDatumUnitFamToBase`'s type says its source is — so the ascription is now
  the definition's own and not a claim this file has to make. That definition
  (`Oka/Analytification/RefineDatumUnitFamily.lean:341`) is itself
  `ComplexAnalytic.refineDatumAnalytificationOfLaws` at the same auxiliary polynomial family, the
  same four unit-family choices, the same two range conditions and the same three laws, in that
  order.
* the target **is** `ComplexAnalytic.projectiveLineSpace`, an analytic space, and not that space's
  gluing. `OkaTest/ProjectiveLine.lean:462` defines it as `ComplexAnalytic.coverAnalytification`
  at these arguments verbatim; the gluing is a different object, which the theorem below reaches
  through `ComplexAnalytic.toLRSHom_coverIota` and this type does not mention at all.

**Those two unfoldings are the whole content of the short type**, which is why they are cited
rather than left to a reader: no bridge and no transport enters the term, and the body is a term
application with no `rw` and no `unfold`, so nothing is generated. -/
def lineRefineToBase : lineRefinement.{u} ⟶ projectiveLineSpace.{u} :=
  refineDatumUnitFamToBase.{u} lineCoverObj.{u} lineCoverPoly.{u} id lineRefineFam.{u}
    lineSwapIso.{u} isUnit_lineRefineFam.{u} hsymm_lineCover.{u} hrange_lineCover.{u}
    Function.injective_id hcocycle_lineCover.{u}

/-- **The refined space does not map onto the space it refines.**

`ComplexAnalytic.surjective_base_refineDatumUnitFamToBase_iff` in the negative direction — the
direction `Oka/Analytification/RefineDatumCover.lean` says a caller arguing the other way has, and
which had no consumer until this one. **That equivalence is
`ComplexAnalytic.surjective_base_refineDatumToBase_iff` read at the unit family**, which is what
this proof spelled at fifteen placeholders before it existed and now spells at ten; the statement
proved is the same one either way. The point that is missed is **the origin of the first chart**,
in the glued space, and the two cases are the two members it could have been reached through:

* through the first, where `ComplexAnalytic.isOpenImmersion_lineIota`'s open embedding is injective
  — `LocallyRingedSpace.IsOpenImmersion` unfolds to a structure whose `base_open` field is an
  `IsOpenEmbedding`, and `exact?` does not find this — so the point of `D(z)` mapping to it would
  *be* the origin, which `ComplexAnalytic.lineOrigin_notMem_localisationOpen` forbids;
* through the second, which is `ComplexAnalytic.lineOrigin_notMem_range_ι` with the point of the
  first member left arbitrary, so `D(z)` being a subset of the chart costs nothing.

`ComplexAnalytic.toLRSHom_coverIota` is `rfl`, so no bridge between the analytic space and the glue
datum's gluing appears in the term.

**This does not follow from `ComplexAnalytic.not_refineDatumCovers_lineRefineFam` and is not
implied by it**: `ComplexAnalytic.dupStrict` is the theorem that the condition can fail where the
surjectivity holds. The two are measured separately and agree. -/
theorem not_surjective_base_lineRefineToBase :
    ¬ Function.Surjective lineRefineToBase.{u}.toLRSHom.base := by
  intro hsurj
  have hcon := (surjective_base_refineDatumUnitFamToBase_iff.{u} _ _ _ _ _ _ _ _ _ _).1 hsurj
  have hmem : (lineIota.{u} (ULift.up 0)).toLRSHom.base lineOrigin.{u} ∈
      ⋃ b : pair.{u}, (coverIota.{u} lineCoverObj.{u} lineCoverPoly.{u} lineSwapIso.{u}
          hrange_lineCover.{u} hsymm_lineCover.{u} hcocycle_lineCover.{u} (id b)).toLRSHom.base ''
        (localisationOpen.{u} (lineCoverObj.{u} (id b)).g (lineRefineFam.{u} b) :
          Set (AnalyticSpace.analytification.{u} (lineCoverObj.{u} (id b)).g)) := by
    rw [hcon]
    trivial
  obtain ⟨b, z, hz, hbz⟩ := Set.mem_iUnion.1 hmem
  obtain ⟨b⟩ := b
  fin_cases b
  · exact lineOrigin_notMem_localisationOpen.{u}
      ((isOpenImmersion_lineIota.{u} (ULift.up 0)).base_open.injective hbz ▸ hz)
  · exact lineOrigin_notMem_range_ι.{u} (ULift.up 1) (ULift.up 0) (by decide) ⟨z, hbz⟩

/-- **So the morphism down is not an isomorphism**, and this refinement is the first on this board
that a `¬ IsIso` is available for.

`ComplexAnalytic.AnalyticSpace.surjective_base_of_isIso` against the theorem above. **The whole
content is that the theorem above is about the same morphism**, which the type of
`ComplexAnalytic.lineRefineToBase` now says: it goes out of `ComplexAnalytic.lineRefinement` and
into `ComplexAnalytic.projectiveLineSpace`, so this is a statement about the comparison between the
refinement and the cover it refines.

**Why the other `¬ IsIso` on this line does not give it.**
`ComplexAnalytic.not_isIso_refineToBase` (`Oka/Analytification/CoverRefinement.lean`) is about
`ComplexAnalytic.refineToBase`, which refines a *single presentation* by a family of opens and is
stated at an empty one — where the refined space has no points at all. That is a different
construction from `ComplexAnalytic.refineDatumToBase` at a cover datum, and it is a degenerate
instance of it; **here the refinement refines, by a proper non-empty open of each member**, which
is `ComplexAnalytic.localisationOpen_lineRefineFam_ne_top` and `…_ne_bot` above.

**This does not say the two spaces are non-isomorphic**, and no sentence in this file should be
read as though it did: it refutes `IsIso` for *this* morphism, and two spaces can be isomorphic by
a morphism other than the one in hand. `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base`
(`Oka/AnalyticSpace/Sigma.lean`) carries the same caveat for the same reason, and the `ℙ¹`
comparison this file's `## What is not here` records as absent stays absent. -/
theorem not_isIso_lineRefineToBase : ¬ IsIso lineRefineToBase.{u} := fun _ ↦
  not_surjective_base_lineRefineToBase.{u} (AnalyticSpace.surjective_base_of_isIso.{u} _)

end

end ComplexAnalytic

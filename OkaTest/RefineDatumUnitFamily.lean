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

**This says nothing about whether the refinement's morphism down is surjective**, and no sentence
here should be read as though it did. `ComplexAnalytic.RefineDatumCovers` is a *sufficient*
condition for that surjectivity and `ComplexAnalytic.dupStrict` is exactly the theorem that it is
not a necessary one, so a datum that fails the condition may still have a surjection down. What
surjectivity is equivalent to is `ComplexAnalytic.surjective_base_refineDatumToBase_iff`, this file
does not instantiate it, and the morphism `ComplexAnalytic.refineDatumToBase` appears nowhere
below.

## Main definitions

- `ComplexAnalytic.lineRefineFam`: **the refining family**, the coordinate `z` on each chart.
- `ComplexAnalytic.lineRefinement`: **the analytic space of the refined cover**, with no
  hypothesis left open.

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

## What is not here

* **No claim that the refined space is `ℙ¹`, or that it is not.** It is the gluing of two copies
  of `𝔸¹ ∖ {0}` along `D(z)` in each, and no morphism relates it to
  `ComplexAnalytic.projectiveLineSpace` in either direction. The only statement on this board
  about a refinement's comparison morphism is `ComplexAnalytic.not_isIso_refineToBase`
  (`Oka/Analytification/CoverRefinement.lean`), and there is no such morphism here to apply it
  to. **What that gluing is has since been identified**, and this bullet said nothing about it:
  the `D(z)` the two copies are glued along is the *whole* of each of them, so
  `ComplexAnalytic.isoLineRefineGlued` (`OkaTest/RefineDatumUnitFamilyNode.lean`) says the glued
  space is one copy of `𝔸¹ ∖ {0}`. **The comparison with `ℙ¹` is still absent** — that would need
  the two spaces to be told apart, which nothing here does.
* **Nothing about the refined overlaps being the geometric ones**, which is
  `Oka/Analytification/CrossMemberDatumGlue.lean`'s absence and is about the construction rather
  than about any input to it.
* **Nothing about the morphism down, and in particular no surjectivity.**
  `ComplexAnalytic.refineDatumToBase` is not spelled at this refinement — at the unit family it
  would take the four choices of `Oka/Analytification/RefineDatumUnitFamily.lean` and the two range
  conditions explicitly, and nothing in `Oka/` shortens that — so whether this refinement's space
  maps **onto** the glued space is untouched here in both directions. The theorem about
  `ComplexAnalytic.RefineDatumCovers` below is not evidence either way, for the reason its own
  paragraph gives.
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

/-! ### And it does not cover -/

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

end

end ComplexAnalytic

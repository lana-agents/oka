/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumCover
import OkaTest.AffineCover

/-!
# The cross-member witness at a cover datum whose three laws are proved

`Oka/Analytification/RefineDatumWitness.lean` builds a refined cover datum **for every cover datum
and every index map**, taking the original datum's `hsymm`, `hrange` and `hcocycle` and nothing
else, and states separately that `id` is not constant on a `Nontrivial` type. Neither statement is
instantiated there, and neither can be: every concrete cover datum in this repository lives under
`OkaTest/`, which `Oka/` cannot import. So *"there is a refined cover datum at a non-constant
`σ`"* was, until this file, the composition of a construction whose hypotheses might be unmet with
a fact about `id`.

**This file makes the composition.** `ComplexAnalytic.nodeCoverObj`, `nodeCoverPoly` and
`nodeCoverGlue` — three copies of the node glued along the punctured axis — have all three laws
proved in `OkaTest/AffineCover.lean`, and their index type `ComplexAnalytic.triple` is
`ULift (Fin 3)`, which is `Nontrivial`. At `B = J = triple` and `σ = id`:

* `OkaTest.RefineDatumWitness.nodeRefineOneAnalytification` is an
  `ComplexAnalytic.AnalyticSpace` **with no hypothesis left open at all**;
* `OkaTest.RefineDatumWitness.not_isConstant_id_triple` says its index map is not constant.

## Why a witness needs more than existing, and what is checked

`OkaTest/CoverRefinement.lean` exists because a construction can be non-vacuous and still
degenerate: at a refining family constantly `0` every refined member is empty and every law holds
of nothing. The family here is constantly `1`, which is the opposite extreme, and the two checks
that separate this from *both* degeneracies are about the refined overlaps.

* `OkaTest.RefineDatumWitness.coverOpen_nodeRefineOne_eq`: **the refined overlap is the preimage
  of the original overlap** along the projection of the refined member — so the refined cover
  overlaps exactly where the node cover does and the cross-member `glue` is an isomorphism of the
  original overlaps read upstairs. This is the statement `Oka/Analytification/CrossMemberGlue.lean`
  records as absent *in general*; it is proved here **only at this data**, where the caller's
  cutting polynomial is the original datum's own, and it says nothing about the general
  construction.
* `..._ne_bot` and `..._ne_top`: every refined overlap is **non-empty** and is **not the whole
  refined member**, so nothing here is glued along nothing and nothing along everything. Both come
  from `OkaTest.RefineDatumWitness.surjective_base_localisationProj_one`, which is
  `ComplexAnalytic.range_base_localisationProj` at `ComplexAnalytic.localisationOpen_one`: at a
  refining family constantly `1` the projection of a refined member onto its original member is
  **onto**, and that is the precise sense in which this refinement refines nothing.

## And the space it glues to is not one of its members

The two checks above are about the *overlaps*. This one is about the **gluing**, which is what
`OkaTest/AffineCover.lean` spends its second half on for the unrefined cover and which is the
difference between "the construction is non-vacuous" and "it built something".

`OkaTest.RefineDatumWitness.exists_ι_nodeRefineOne_ne` says the three refined copies stay distinct
in the refined gluing, **with no hypothesis left**. It is `ComplexAnalytic.ι_nodeOrigin_ne`'s
argument for the *unrefined* node cover carried upstairs by
`OkaTest.RefineDatumWitness.coverOpen_nodeRefineOne_eq`: a point of a refined overlap lies over a
point of the original overlap, and the origin is not one. The ingredient it needs at the refined
datum — a reading of the glue data's `f` — is `ComplexAnalytic.f_coverGlueData_of_ne`, which holds
at **every** cover datum and so at this one, with the `CategoryTheory.GlueData'` solved from the
goal.

**The point comes from `OkaTest.RefineDatumWitness.surjective_base_localisationProj_one` and that
is where the family being `1` is spent** — it is what puts a point of the refined member over
`nodeOrigin`. Whether that is a defect of this witness or of the alternatives is
the subject of the last bullet below.

## And it maps down to the cover it refines

`Oka/Analytification/RefineDatumToBase.lean` builds `ComplexAnalytic.refineDatumToBase`, the
morphism from a cross-member refined cover datum's analytic space to the analytification of the
cover it refines, at an arbitrary datum and an arbitrary index map. **Its argument list is met
here with nothing left over**, so `OkaTest.RefineDatumWitness.nodeRefineOneToBase` exists by
naming this file's data and the node cover's three laws, and
`OkaTest.RefineDatumWitness.coverIota_comp_nodeRefineOneToBase` says it restricts on each refined
member to that member's projection followed by the member's inclusion.

**Nothing is built and that is the point.** What a concrete instance adds to the general
construction is that its arguments can be supplied at once, by data rather than by hypotheses:
this is the first instantiation of `ComplexAnalytic.refineDatumToBase` at data, and
until it existed the morphism was a construction whose inputs might never have been met together.
It is the same service `OkaTest.RefineDatumWitness.nodeRefineOneAnalytification` does for the
refined datum itself.

**It is not claimed to be an isomorphism**, although the shape of this data makes that the obvious
next question — see the second bullet of `## What this is not`, which records what an answer would
need, says which part of that is now a theorem elsewhere, and compiles none of it here.

## What this is not

* **It is not a proper refinement.** Every refined member is the whole of its original member —
  that is what the surjectivity above says — so what this exhibits is the node cover **reindexed
  along `id`**, not a cover cut down. What makes it a witness rather than a restatement is that
  `σ = id` is injective on a three-element type, so `σ a ≠ σ b` at every pair of distinct indices
  and `ComplexAnalytic.refineDatumGlue` takes its **cross-member** branch — the one that reads the
  original datum's own `glue` through `ComplexAnalytic.refineDatumCrossAlgEquiv` — at every pair.
  A witness at a family that is not a unit is still open, and
  `ComplexAnalytic.exists_refineDatumCross_of_isUnit` says what one would need of its family.
* **It is not a *proper* refinement whose gluing is not one member, and no such thing is on
  record.** The statement above is at a family constantly `1`, and what makes its gluing more than
  one member is that the refined overlaps are the node cover's **own** overlaps — proper, by
  `..._ne_top`. At the two refinements on this line whose *members* are proper, the refined
  overlaps are `⊤` and the gluing **is** one member: `ComplexAnalytic.coverOpen_nodeRefine_eq_top`
  with `ComplexAnalytic.isoNodeRefineGlued`, and `ComplexAnalytic.coverOpen_lineRefine_eq_top`
  with `ComplexAnalytic.isoLineRefineGlued`, both in `OkaTest/RefineDatumUnitFamilyNode.lean`.

  **So the analogue of this file's theorem at either of those is not unattempted — it is false**,
  and the reason is that file's third degeneracy. **Both constructions on this line fix the
  caller's `q` to be the original datum's own `poly`** — `ComplexAnalytic.refineDatumOneGlueData`,
  which this file instantiates, and `ComplexAnalytic.refineDatumUnitFamGlueData`, which those two
  do — so the refined member is `D(fam)` and the refined overlap is `D(poly) ⊓ D(fam)` inside it,
  and **the two conditions pull against each other**: the hypothesis on the family is that it is a
  unit on the overlap, which is `D(poly) ≤ D(fam)`, while the collapse is `D(fam) ≤ D(poly)`. Both
  landed proper instances take `fam` to *be* `poly`, where the two meet and the refined overlap is
  `⊤`; this file takes `fam ≡ 1`, where `D(fam)` is everything and the refined overlap is
  `D(poly)`, proper.

  **So proper members and a gluing that is not one member have so far been mutually exclusive
  here**, and a witness with both would need a family with `D(poly) < D(fam) < ⊤` — a unit on the
  overlap, as the construction demands, but not the overlap's own polynomial. **That is a
  different remainder from the first bullet's**, which is a family that is *not* a unit and so
  fails `ComplexAnalytic.refineDatumUnitFamGlueData`'s hypothesis outright;
  `ComplexAnalytic.exists_refineDatumCross_of_isUnit` is what that one would have to supply.
  Neither has a witness in this repository and the containments above are the whole of why.
* **No claim that `OkaTest.RefineDatumWitness.nodeRefineOneToBase` is an isomorphism**, and the
  question is a live one rather than an idle one: by the first bullet above this refinement is the
  node cover **reindexed along `id`**, every refined member being the whole of its original member,
  so a reader meeting the morphism will ask. **Nothing below answers it in either direction.**

  What an answer would need, recorded so that it is not re-derived:
  `ComplexAnalytic.coverAnalytificationIso` (`Oka/Analytification/CoverIndependence.lean`) turns a
  member-matched comparison into an isomorphism, and at `σ = id` that is the shape of
  `OkaTest.RefineDatumWitness.coverIota_comp_nodeRefineOneToBase` above.

  **This bullet said it would suffice that `ComplexAnalytic.localisationProj (nodeCoverObj b).g 1`
  is an isomorphism, and that is not so** — which is worth stating rather than deleting, because
  the statement it names is now a theorem and the route still does not close.
  `ComplexAnalytic.isIso_localisationProj_one`
  (`Oka/Analytification/DistinguishedOpen.lean`) says exactly that, and it is not what
  `ComplexAnalytic.coverAnalytificationIso` consumes: that construction takes an isomorphism of
  each member **in `ComplexAnalytic.Presentation`**, feeds it to
  `ComplexAnalytic.coverMapPart` as a `ComplexAnalytic.PresHom` and pushes it through
  `ComplexAnalytic.analytificationFunctor`, and an isomorphism of analytic spaces supplies none of
  that. Nothing in this repository closes the gap in general either: no statement anywhere says
  that functor is full, faithful, or reflects isomorphisms, and
  `OkaTest/ProjectiveLineDirected.lean` records the same absence from the other side — it needs
  `ComplexAnalytic.analytificationFunctor` to be faithful on a pair of legs and says in terms that
  nothing here supplies it.

  **So the sufficient condition for this route is one category down**: that
  `ComplexAnalytic.localisationHom (nodeCoverObj b).g 1`
  (`Oka/Analytification/LocalisationFunctor.lean`) is an isomorphism, which is a statement about
  presented algebras rather than about spaces. **This bullet said that condition was unproved,
  unpriced and not claimed; it is now a theorem** — `ComplexAnalytic.isIso_localisationHom_one`
  (`Oka/Analytification/LocalisationIndependence.lean`), an `instance`, stated in general in the
  base's equations and so available at `(nodeCoverObj b).g` with nothing to instantiate.

  **The route still does not close and nothing below runs it, which is the half a reader will
  otherwise supply.** `ComplexAnalytic.coverAnalytificationIso` takes an isomorphism of each
  member matched by index **and two commutation hypotheses** — each a `∀ i j, i ≠ j →` square
  relating a member's inclusion into an overlap to the datum's transition morphism — and the
  theorem above supplies only the first, and only once it is known that the refining family is
  the original member's localisation at `1` member by member. Both of those are questions about
  this file's own `OkaTest.RefineDatumWitness.nodeRefineOneObj` and
  `OkaTest.RefineDatumWitness.nodeRefineOnePoly`, and neither is opened here. **What
  changed is that the ingredient this bullet named as absent is no longer absent**, not that the
  question above it is answered.

  **The step this bullet recorded as missing is no longer missing**, and it is the reason
  `ComplexAnalytic.isIso_localisationProj_one` exists:
  `ComplexAnalytic.localisationIso` identifies the localised presentation's analytification with
  `X^an` restricted to `D(f)`, `ComplexAnalytic.localisationOpen_one` says `D(1) = ⊤`, and
  `ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ` inverts the inclusion of such an
  open. **This file still neither states that step nor uses it**, which is what this bullet said
  before and is still true of the step; `ComplexAnalytic.localisationOpen_one` it does use, in
  `OkaTest.RefineDatumWitness.surjective_base_localisationProj_one` below. The open question this
  bullet flagged — whether the two statements line up without a transport — is answered: they do,
  in eight lines and with no transport, and lining up was not what the route was short of.

  **`ComplexAnalytic.not_isIso_refineToBase` bears on none of this in either direction.** It is a
  *negative* about the one-member comparison at a constant `σ`, a different morphism, and
  `Oka/Analytification/RefineDatumToBase.lean` says in terms that nothing on that line inherits
  from it.
* **The statement that the refined datum covers `ComplexAnalytic.nodeTripleSpace` is now here**,
  and this bullet said it was not: `OkaTest.RefineDatumWitness.surjective_base_nodeRefineOneToBase`
  below says the base map is surjective, by
  `ComplexAnalytic.surjective_base_refineDatumOneToBase`
  (`Oka/Analytification/RefineDatumCover.lean`) at `Function.surjective_id`. **What made it cheap
  is that this refinement is a reindexing** — `D(1)` is the whole member, which is
  `OkaTest.RefineDatumWitness.surjective_base_localisationProj_one`'s fact one level up — so it is
  no evidence about a refinement that cuts a member down.
  `Oka/Analytification/CrossMemberDatum.lean`'s *"No statement that the refined data cover
  anything"* is narrowed there by the same branch, and the half of it that survives — that the
  refined datum *refines* the original space, which is a statement about
  `ComplexAnalytic.refineDatumPoly` — is untouched here and by this.
* **No `admissible`, no scheme and no comparison functor**, as in the files this one sits beside.

## Main definitions

- `OkaTest.RefineDatumWitness.nodeRefineOneGlueData` and `nodeRefineOneAnalytification`: **the glue
  data and the analytic space of the node cover refined at `σ = id` and a trivial refining
  family**, with every hypothesis discharged.
- `OkaTest.RefineDatumWitness.nodeRefineOneToBase`: **the morphism from that space down to the
  cover it refines**, which is `ComplexAnalytic.refineDatumToBase` at this data and is the first
  instantiation of it at data rather than at variables.

## Main results

- `OkaTest.RefineDatumWitness.not_isConstant_id_triple`: **the index map of that witness is not
  constant.**
- `OkaTest.RefineDatumWitness.nodeRefineOneAnalytification_toLocallyRingedSpace`: **the space is
  that glue data's gluing**, with no transport.
- `OkaTest.RefineDatumWitness.coverOpen_nodeRefineOne_eq`: **the refined overlap is the preimage of
  the original one.**
- `OkaTest.RefineDatumWitness.coverOpen_nodeRefineOne_ne_bot` and `..._ne_top`: **it is non-empty
  and proper.**
- `OkaTest.RefineDatumWitness.f_nodeRefineOneGlueData` and
  `OkaTest.RefineDatumWitness.range_f_subset_nodeRefineOneGlueData`: **the inclusion of a refined
  member into the refined gluing off the diagonal, and that its image is in the refined overlap.**
- `OkaTest.RefineDatumWitness.ι_nodeRefineOne_ne`: **two refined copies are distinct in the
  gluing** at a point over `nodeOrigin`, and
  `OkaTest.RefineDatumWitness.exists_ι_nodeRefineOne_ne`: **so the refined gluing is not one of
  its members**, with no hypothesis.
- `OkaTest.RefineDatumWitness.coverIota_comp_nodeRefineOneToBase`: **the morphism down restricts on
  each refined member to that member's projection followed by the member's inclusion**, which is
  what says it is the intended morphism and not merely one of the right type.
- `OkaTest.RefineDatumWitness.surjective_base_nodeRefineOneToBase`: **and it is onto** — the node
  cover refined at three members covers `ComplexAnalytic.nodeTripleSpace`.
-/

open MvPolynomial CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace OkaTest.RefineDatumWitness

open ComplexAnalytic

noncomputable section

/-! ### The data -/

/-- **The refined members**: the node localised at `1`, one for each of the three indices. An
`abbrev` so that `ComplexAnalytic.refineDatumPoly_of_ne` rewrites underneath it. -/
abbrev nodeRefineOneObj : triple.{u} → Presentation.{u} :=
  refineDatumObj.{u} nodeCoverObj.{u} (id : triple.{u} → triple.{u}) (fun _ ↦ 1)

/-- **The refined cutting polynomials**, at the caller's `q` taken to be the original datum's own
`poly`. Off the diagonal this is `z₀ · z₀` renamed into the localised member. -/
abbrev nodeRefineOnePoly (a : triple.{u}) (b : triple.{u}) :
    MvPolynomial (ULift.{u} (Fin (nodeRefineOneObj.{u} a).n)) ℂ :=
  refineDatumPoly.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (id : triple.{u} → triple.{u})
    (fun _ ↦ 1) (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) a b

/-- **The glue data of the node cover refined along `id` at a trivial refining family**, and it
takes no hypothesis: the three the construction asks for are `OkaTest/AffineCover.lean`'s three
theorems. -/
def nodeRefineOneGlueData : LocallyRingedSpace.GlueData.{u} :=
  refineDatumOneGlueData.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (id : triple.{u} → triple.{u})
    nodeCoverGlue.{u} hsymm_nodeCover.{u} hrange_nodeCover.{u} hcocycle_nodeCover.{u}

/-- **The analytic space it glues to**, and this is the object five files said did not exist:
a cross-member refined cover datum at an index map that is not constant, with nothing left for a
caller to supply. -/
def nodeRefineOneAnalytification : AnalyticSpace.{u} :=
  refineDatumOneAnalytification.{u} nodeCoverObj.{u} nodeCoverPoly.{u}
    (id : triple.{u} → triple.{u}) nodeCoverGlue.{u} hsymm_nodeCover.{u} hrange_nodeCover.{u}
    hcocycle_nodeCover.{u}

/-- **That space has that glue data's gluing underneath it**, with no transport —
`ComplexAnalytic.refineDatumAnalytificationOfLaws_toLocallyRingedSpace` here, so that the two
definitions above are not two well-typed objects with no recorded relation. -/
theorem nodeRefineOneAnalytification_toLocallyRingedSpace :
    nodeRefineOneAnalytification.{u}.toLocallyRingedSpace =
      nodeRefineOneGlueData.{u}.toGlueData.glued :=
  refineDatumAnalytificationOfLaws_toLocallyRingedSpace.{u} nodeCoverObj.{u} nodeCoverPoly.{u}
    (id : triple.{u} → triple.{u}) (fun _ ↦ 1) (fun x y ↦ nodeCoverPoly.{u} (id x) (id y))
    nodeCoverGlue.{u} (refineDatumOneR.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    (refineDatumOneU.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    (refineDatumOneCrossEq.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    (refineDatumOneCrossUnit.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    hrange_nodeCover.{u}
    (refineDatumOneRangeCross.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u}
      hrange_nodeCover.{u})
    (refineDatumOneRangeEq.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    hsymm_nodeCover.{u} hcocycle_nodeCover.{u}

/-- **And the index map is not constant.** `ComplexAnalytic.not_isConstant_id` at
`ComplexAnalytic.triple`, which is `ULift (Fin 3)` and so `Nontrivial`. Everything above is at
`σ = id`, and this is the whole of what makes it a witness *at a non-constant `σ`*: the library's
construction is stated at an arbitrary `σ`, and an arbitrary `σ` includes the constant ones. -/
theorem not_isConstant_id_triple :
    ¬ ∃ j : triple.{u}, ∀ b : triple.{u}, (id : triple.{u} → triple.{u}) b = j :=
  not_isConstant_id.{u}

/-! ### The refined overlaps, which is where a degenerate witness would show -/

/-- **The projection of a refined member onto its original member is onto.**

`ComplexAnalytic.range_base_localisationProj` says the range is `D(1)`, and
`ComplexAnalytic.localisationOpen_one` says that is the whole space. **This is the precise sense in
which a refining family constantly `1` refines nothing**, and it is what carries both statements
below: a point of the node is a point of the refined member, so no question about the refined
overlaps needs a point of a double localisation to be written down.

**`ComplexAnalytic.isIso_localisationProj_one` is about the same morphism and is a stronger
statement about it**, and this proof does not go through it: that one says the morphism is an
isomorphism of analytic spaces, this one says its base map is onto. Whether the second now follows
from the first is **not checked here** — it would need the base map of an isomorphism of
`ComplexAnalytic.AnalyticSpace` to be surjective, which no statement in this repository records —
so the two are kept separate rather than one being rewritten in terms of the other on an untested
claim. -/
theorem surjective_base_localisationProj_one :
    Function.Surjective (localisationProj.{u} nodePres.{u} 1).toLRSHom.base := by
  intro y
  have hy : y ∈ Set.range (localisationProj.{u} nodePres.{u} 1).toLRSHom.base := by
    rw [range_base_localisationProj.{u}, localisationOpen_one.{u}]
    trivial
  exact hy

/-- **The refined overlap is the preimage of the original overlap**, at every pair of distinct
indices.

At `σ = id` distinct indices lie over distinct members, so
`ComplexAnalytic.refineDatumPoly_of_ne` applies and the refined polynomial is `poly · q` renamed —
here `z₀ · z₀`, since the caller's `q` is the original datum's own `poly`. Then
`ComplexAnalytic.localisationOpen_rename` turns the open upstairs into the preimage of the one
downstairs and `ComplexAnalytic.localisationOpen_mul` with `inf_idem` removes the square.

**The square is why this is worth stating rather than reading off.** `D(z₀ · z₀)` is `D(z₀)` and
not something smaller, so the caller's extra factor cuts nothing away here — which is what makes
the refined cover overlap exactly where the node cover does. -/
theorem coverOpen_nodeRefineOne_eq (a b : triple.{u}) (h : a ≠ b) :
    coverOpen.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} a b =
      (Opens.map (localisationProj.{u} nodePres.{u} 1).toLRSHom.base).obj
        (coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} a b) := by
  change localisationOpen.{u} (localisationPresentation.{u} nodePres.{u} 1)
      (refineDatumPoly.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (id : triple.{u} → triple.{u})
        (fun _ ↦ 1) (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) a b) = _
  rw [refineDatumPoly_of_ne.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (id : triple.{u} → triple.{u})
      (fun _ ↦ 1) (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) h,
    localisationOpen_rename.{u} nodePres.{u} 1, localisationOpen_mul.{u}, inf_idem]

/-- **No refined overlap is empty**, so this is not the degeneracy `OkaTest/CoverRefinement.lean`
was written against: at a refining family constantly `0` every overlap is empty and every law of
the construction holds of nothing.

The point is the one that file uses, `ComplexAnalytic.axisPoint (ULift.up 0)` — the point of the
node with `z₀ = 1` — lifted through the surjection above. -/
theorem coverOpen_nodeRefineOne_ne_bot (a b : triple.{u}) (h : a ≠ b) :
    coverOpen.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} a b ≠ ⊥ := by
  obtain ⟨w, hw⟩ := surjective_base_localisationProj_one.{u} (axisPoint.{u} (ULift.up 0))
  intro hcon
  have hmem : w ∈ coverOpen.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} a b := by
    rw [coverOpen_nodeRefineOne_eq.{u} a b h]
    change (localisationProj.{u} nodePres.{u} 1).toLRSHom.base w ∈
      coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} a b
    rw [hw]
    exact (mem_localisationOpen_iff.{u} nodePres.{u} nodeX.{u}).2 (by
      rw [MvPolynomial.eval_X, axisPoint_coord, if_pos rfl]
      exact one_ne_zero)
  rw [hcon] at hmem
  exact hmem

/-- **Nor is any of them the whole refined member**, so this is not the other degeneracy either:
the members are glued along something smaller than themselves and the gluing is not three
identifications of three whole copies.

The point is `nodeOrigin` — declared in the root namespace by `OkaTest/OpenSubspace.lean` —
at which `z₀` vanishes, lifted through the same surjection. -/
theorem coverOpen_nodeRefineOne_ne_top (a b : triple.{u}) (h : a ≠ b) :
    coverOpen.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} a b ≠ ⊤ := by
  obtain ⟨w, hw⟩ := surjective_base_localisationProj_one.{u} (nodeOrigin.{u})
  intro hcon
  have hmem : w ∈ coverOpen.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} a b := by
    rw [hcon]
    trivial
  rw [coverOpen_nodeRefineOne_eq.{u} a b h] at hmem
  have horigin : nodeOrigin.{u} ∈ coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} a b := hw ▸ hmem
  exact (mem_localisationOpen_iff.{u} nodePres.{u} nodeX.{u}).1 horigin (MvPolynomial.eval_X _)

/-! ### The gluing is not one member -/

/-- **The inclusion of a refined member into the refined gluing, off the diagonal.**

`ComplexAnalytic.f_coverGlueData_of_ne` at this datum and nothing else. That lemma is
hypothesis-free and `OkaTest.RefineDatumWitness.nodeRefineOneGlueData` is
`ComplexAnalytic.coverGlueData` at the refined arguments, so the `CategoryTheory.GlueData'` it
reads is solved from the goal — which is what
`Oka/Analytification/CoverGlueTop.lean`'s docstring says of a refined datum in terms.

**This is stated through the general lemma rather than through
`CategoryTheory.GlueData.ofGlueData'_f_of_ne` directly**, which would also close it: the file
above exists so that no datum has to spell that unfolding out again, and going round it here
would leave the general statement with one fewer consumer than it has. -/
theorem f_nodeRefineOneGlueData (i j : triple.{u}) (hij : i ≠ j) :
    nodeRefineOneGlueData.{u}.toGlueData.f i j =
      eqToHom (dif_neg hij) ≫ coverIncl.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} i j :=
  f_coverGlueData_of_ne.{u} _ _ _ _ _ _ hij

/-- **Its image lies in the refined overlap**, which is what the point below needs.

`ComplexAnalytic.range_f_subset_nodeTripleGlueData` at the refined datum, and the proof is that
one's: rewrite by the inclusion above and read the range of an open subspace's `ofRestrict`. -/
theorem range_f_subset_nodeRefineOneGlueData (i j : triple.{u}) (hij : i ≠ j) :
    Set.range (nodeRefineOneGlueData.{u}.toGlueData.f i j).base ⊆
      (coverOpen.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} i j :
        Set (coverSpace.{u} nodeRefineOneObj.{u} i)) := by
  rintro _ ⟨z, rfl⟩
  rw [f_nodeRefineOneGlueData.{u} i j hij]
  exact ((coverSpace.{u} nodeRefineOneObj.{u} i).range_ofRestrict
    (coverOpen.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} i j)).le ⟨_, rfl⟩

/-- **The three refined copies are distinct in the refined gluing**, at any point of a refined
member lying over `nodeOrigin`.

The unrefined argument is `ComplexAnalytic.ι_nodeOrigin_ne`'s: two members' points agree in the
gluing only if they come from a point of the overlap, and the origin is not on the punctured axis.
What carries it upstairs is `OkaTest.RefineDatumWitness.coverOpen_nodeRefineOne_eq` — the refined
overlap is the *preimage* of the original one, so a point of the refined overlap lies over a point
of the original overlap and the contradiction is downstairs. -/
theorem ι_nodeRefineOne_ne (i j : triple.{u}) (hij : i ≠ j)
    (w : coverSpace.{u} nodeRefineOneObj.{u} i)
    (hw : (localisationProj.{u} nodePres.{u} 1).toLRSHom.base w = nodeOrigin.{u}) :
    (nodeRefineOneGlueData.{u}.toGlueData.ι i).base w ≠
      (nodeRefineOneGlueData.{u}.toGlueData.ι j).base w := by
  rw [Ne, LocallyRingedSpace.GlueData.ι_eq_iff]
  rintro ⟨z, hz, -⟩
  have hmem : w ∈ coverOpen.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u} i j :=
    range_f_subset_nodeRefineOneGlueData.{u} i j hij ⟨z, hz⟩
  rw [coverOpen_nodeRefineOne_eq.{u} i j hij] at hmem
  have horigin : nodeOrigin.{u} ∈
      coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j := hw ▸ hmem
  exact (mem_localisationOpen_iff.{u} nodePres.{u} nodeX.{u}).1 horigin (MvPolynomial.eval_X _)

/-- **The refined gluing is not one of its members**, with no hypothesis left.

The point is produced rather than assumed:
`OkaTest.RefineDatumWitness.surjective_base_localisationProj_one` lifts `nodeOrigin` into the
refined member, and that surjectivity is available **because the refining family is `1`**. At a
family that cuts the member down there need be no point of it over the origin at all, and at the
one such family this repository has there is none — see this file's `## What this is not`. -/
theorem exists_ι_nodeRefineOne_ne (i j : triple.{u}) (hij : i ≠ j) :
    ∃ w, (nodeRefineOneGlueData.{u}.toGlueData.ι i).base w ≠
      (nodeRefineOneGlueData.{u}.toGlueData.ι j).base w := by
  obtain ⟨w, hw⟩ := surjective_base_localisationProj_one.{u} (nodeOrigin.{u})
  exact ⟨w, ι_nodeRefineOne_ne.{u} i j hij w hw⟩

/-! ### The morphism down to the cover it refines -/

/-- **The refined cover's analytic space maps down to the cover it refines**, with nothing left
for a caller to supply.

`ComplexAnalytic.refineDatumToBase` (`Oka/Analytification/RefineDatumToBase.lean`) at the
arguments `OkaTest.RefineDatumWitness.nodeRefineOneAnalytification_toLocallyRingedSpace` already
writes out, together with the node cover's three laws. **Nothing is built here**: the source is
`ComplexAnalytic.refineDatumAnalytificationOfLaws` at the one-family arguments, by definition of
`ComplexAnalytic.refineDatumOneAnalytification`, and the target is
`ComplexAnalytic.coverAnalytification` at the node cover, by definition of
`ComplexAnalytic.nodeTripleSpace` — so the general morphism applies on the nose and the content is
that this file's data meets its argument list.

**This is the first instantiation of `ComplexAnalytic.refineDatumToBase` at data.** Outside its
own file that name occurs only in prose and in `OkaTest/Axioms/Analytification.lean`'s
`#print axioms` command; inside it, it is applied only at that file's own section variables, in
`ComplexAnalytic.coverIota_comp_refineDatumToBase` and
`ComplexAnalytic.refineDatumToBase_unique`. What this adds to the general construction is that the
argument list can in fact be met — every argument here is data these two files already carry, or a
general theorem applied to it, and none of them leaves a hypothesis open — so the morphism exists
at a cover datum a reader can point at.

**It is not claimed to be an isomorphism.** See this file's `## What this is not` for what such a
claim would need and for why the shape of this data makes the question a live one. -/
noncomputable def nodeRefineOneToBase :
    nodeRefineOneAnalytification.{u} ⟶ nodeTripleSpace.{u} :=
  ComplexAnalytic.refineDatumToBase.{u} nodeCoverObj.{u} nodeCoverPoly.{u}
    (id : triple.{u} → triple.{u}) (fun _ ↦ 1)
    (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) nodeCoverGlue.{u}
    (refineDatumOneR.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    (refineDatumOneU.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    (refineDatumOneCrossEq.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    (refineDatumOneCrossUnit.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    hsymm_nodeCover.{u} hrange_nodeCover.{u}
    (refineDatumOneRangeCross.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u}
      hrange_nodeCover.{u})
    (refineDatumOneRangeEq.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
    hcocycle_nodeCover.{u}

/-- **It restricts on the `b`-th refined member to that member's projection followed by the `b`-th
inclusion**, which is what says the definition above is the intended morphism rather than a
well-typed one.

`ComplexAnalytic.coverIota_comp_refineDatumToBase` with every argument solved from the goal. **The
statement is worth writing out here even though the proof is one name**, because the `glue` the
left-hand `ComplexAnalytic.coverIota` takes is the *refined* datum's and does not solve: it has to
be spelled `ComplexAnalytic.refineDatumGlue` at the one-family arguments, while the `hrange`,
`hsymm` and `hcocycle` beside it do solve and are left as `_`. A caller who has to rediscover that
spelling has paid more than reading it.

**`ComplexAnalytic.localisationProj (nodeCoverObj b).g 1` is the projection of the refined member
onto the member it lies over**, and it is onto — which is
`OkaTest.RefineDatumWitness.surjective_base_localisationProj_one` above, the same fact that makes
this refinement a reindexing rather than a cutting-down. -/
theorem coverIota_comp_nodeRefineOneToBase (b : triple.{u}) :
    coverIota.{u} nodeRefineOneObj.{u} nodeRefineOnePoly.{u}
        (refineDatumGlue.{u} nodeCoverObj.{u} (id : triple.{u} → triple.{u}) (fun _ ↦ 1)
          nodeCoverPoly.{u} (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) nodeCoverGlue.{u}
          (refineDatumOneR.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
          (refineDatumOneU.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
          (refineDatumOneCrossEq.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u})
          (refineDatumOneCrossUnit.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeCoverGlue.{u}))
        _ _ _ b ≫ nodeRefineOneToBase.{u} =
      localisationProj.{u} (nodeCoverObj.{u} b).g 1 ≫
        coverIota.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} hrange_nodeCover.{u}
          hsymm_nodeCover.{u} hcocycle_nodeCover.{u} b :=
  ComplexAnalytic.coverIota_comp_refineDatumToBase.{u} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b

/-- **And it is onto**: the node cover refined at three members covers
`ComplexAnalytic.nodeTripleSpace`.

`ComplexAnalytic.surjective_base_refineDatumOneToBase`
(`Oka/Analytification/RefineDatumCover.lean`) at `Function.surjective_id`, every other argument
solved from the goal. **The whole content is that `σ` here is `id` and that `D(1)` is the whole
member** — the second being
`OkaTest.RefineDatumWitness.surjective_base_localisationProj_one`'s fact one level up — so this is
a covering because the refinement is a reindexing, and it is not evidence about a refinement that
cuts a member down.

**It says nothing about the morphism being injective or an isomorphism**, and the bullet in this
file's `## What is not here` that declines that is untouched. -/
theorem surjective_base_nodeRefineOneToBase :
    Function.Surjective (nodeRefineOneToBase.{u}).toLRSHom.base :=
  ComplexAnalytic.surjective_base_refineDatumOneToBase.{u} _ _ _ _ _ _ _ Function.surjective_id

end

end OkaTest.RefineDatumWitness

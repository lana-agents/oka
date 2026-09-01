/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.RefineDatumWitness
import OkaTest.RefineDatumUnitFamily

/-!
# A proper refinement at **three** members, and what both proper refinements glue to

`Oka/Analytification/RefineDatumUnitFamily.lean` builds a refined cover datum at an injective
index map and a refining family that is a unit on each overlap, discharging both conditions
`Oka/Analytification/RefineDatumGlueData.lean` adopts. `OkaTest/RefineDatumUnitFamily.lean`
instantiates it at the two-chart cover of `ℙ¹`, where **both** those conditions are vacuous:
each is quantified over a triple of pairwise different indices and
`ComplexAnalytic.pair` has none (`ComplexAnalytic.pair_no_distinct_triple`).

**This file is the instance at three members**, `OkaTest/AffineCover.lean`'s three copies of the
node at `σ = id` and the refining family `z₀`, and it is the first term for which
`ComplexAnalytic.refineDatumRangeCross_poly` is spent at a triple that exists —
`ComplexAnalytic.exists_distinct_triple` below is that statement, and it is the exact converse of
the `ℙ¹` file's excuse. The family's hypothesis is free for the same reason it was there:
`ComplexAnalytic.nodeCoverPoly` is constant, so the family **is** the overlap's own polynomial and
`ComplexAnalytic.isUnit_mk_rename_localisationIncl` closes it with nothing in between.

## And then what it glues to, which is the question the instance was for

`ComplexAnalytic.refineDatumObj obj σ fam b` is `D(fam b)` inside the member `σ b`, so the two
properness statements below say this is neither of the degeneracies the board has names for:
`D(z₀)` is a proper open of the node (`ComplexAnalytic.localisationOpen_nodeRefineFam_ne_top`,
so this is not `Oka/Analytification/RefineDatumWitness.lean`'s reindexing at `fam ≡ 1`) and it is
not empty (`…_ne_bot`, so it is not `OkaTest/CoverRefinement.lean`'s `fam ≡ 0`).

**It is nevertheless degenerate, in a third way that had no name, and the reason is the
refinement's own cutting polynomial rather than its family.** The construction takes the caller's
`q` to be the original datum's own `poly`, so off the diagonal the refined polynomial is
`poly · poly` renamed upstairs; and `D(z₀ · z₀) = D(z₀)`, which is the *whole* of the refined
member because the refined member is already `D(z₀)`. So every off-diagonal overlap of the refined
cover is `⊤` — `ComplexAnalytic.coverOpen_nodeRefine_eq_top` — and
`Oka/Analytification/CoverGlueTop.lean` turns that into
`ComplexAnalytic.isoNodeRefineGlued`: **the refined space is one of its members.**

**The same happens at `ℙ¹`**, and it is stated here rather than left as a remark, because the
argument is four lines once the general theorem exists and a fact about a landed instance that
this file knows and does not say is the failure mode this line has already had twice.
`ComplexAnalytic.isoLineRefineGlued` says `ComplexAnalytic.lineRefinement` is one chart's
`D(z)` as well. Neither statement contradicts anything either file claims — neither claims
anything about its glued space — and both are why the *third* degeneracy deserves a name.

## What this is and is not evidence about

* **It is evidence that `ComplexAnalytic.refineDatumRangeCross_poly` is instantiable at a triple
  of pairwise different indices at a family that is not `1`**, which no previous term on this line
  was. `ComplexAnalytic.refineDatumRangeEq_of_injective` remains vacuous here, as it is at every
  injective index map.
* **It is not evidence that this refinement is "more proper" than `ℙ¹`'s.** Both cut a member down
  to a proper non-empty open; what is different is only which of the two adopted conditions has
  content.
* **It says nothing about a family that is not a unit on the overlap**, which is
  `Oka/Analytification/RefineDatumUnitFamily.lean`'s standing absence and the real remainder on
  this line. The collapse below is a consequence of `hfam` being met the only way anyone has met
  it — at `fam = poly` — and a family that contained the overlap *strictly* would not collapse for
  this reason. **Nothing here exhibits one and this is not a sizing of one.**
* **Nothing about `ComplexAnalytic.exists_refineDatumCross`**, in either direction.
* **No scheme, no `admissible`, no comparison functor**, and no morphism from either refined space
  to the space its cover came from.

## Main definitions

- `ComplexAnalytic.nodeRefineFam`: **the refining family**, the coordinate `z₀` on each of the
  three copies.
- `ComplexAnalytic.nodeRefinement`: **the analytic space of the refined cover**, with no
  hypothesis left open.

## Main results

- `ComplexAnalytic.isUnit_nodeRefineFam`: **the family is a unit on each overlap.**
- `ComplexAnalytic.exists_distinct_triple`: **there is a triple of pairwise different indices**, so
  neither range condition is vacuous for the reason the two-chart instance's are.
- `ComplexAnalytic.localisationOpen_nodeRefineFam_ne_top` and
  `ComplexAnalytic.localisationOpen_nodeRefineFam_ne_bot`: **each refined member is a proper
  non-empty open of its copy of the node.**
- `ComplexAnalytic.nodeRefinement_toLocallyRingedSpace`: **the space is the glue data's gluing**,
  with no transport.
- `ComplexAnalytic.coverOpen_nodeRefine_eq_top`: **every off-diagonal overlap of the refined cover
  is the whole refined member.**
- `ComplexAnalytic.isoNodeRefineGlued` and `ComplexAnalytic.isoLineRefineGlued`: **so both proper
  refinements this development has glue to one of their own members.**
-/

open MvPolynomial CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The refining family, and it is the overlap's own polynomial -/

/-- **The refining family**: the coordinate `z₀` on each of the three copies of the node.

Written against `id` because the construction indexes a family by `b : B` at the member `σ b`, and
here `B = J = ComplexAnalytic.triple` with `σ = id`. -/
abbrev nodeRefineFam : ∀ b : triple.{u},
    MvPolynomial (ULift.{u} (Fin (nodeCoverObj.{u} (id b)).n)) ℂ := fun _ ↦ nodeX.{u}

/-- **The family is a unit on each overlap**, which is
`ComplexAnalytic.refineDatumUnitFamAnalytification`'s one hypothesis about the family.

`ComplexAnalytic.nodeCoverPoly` is the constant family `z₀`, so the polynomial the class is taken
in is the one being asserted invertible and this is
`ComplexAnalytic.isUnit_mk_rename_localisationIncl` with nothing in between — the same shape as
`ComplexAnalytic.isUnit_lineRefineFam` at the other test cover, and for the same reason. **A
family that were a unit on the overlap without being the overlap's own polynomial would need an
argument here**, and no cover in this repository supplies one. -/
theorem isUnit_nodeRefineFam (a b : triple.{u}) (_h : id a ≠ id b) :
    IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u}
      (nodeCoverObj.{u} (id a)).g (nodeCoverPoly.{u} (id a) (id b))))
      (MvPolynomial.rename (localisationIncl.{u} (nodeCoverObj.{u} (id a)).n)
        (nodeRefineFam.{u} a))) :=
  isUnit_mk_rename_localisationIncl.{u} (nodeCoverObj.{u} a).g nodeX.{u}

/-! ### The refinement -/

/-- **The glue data of the node cover refined along `id` at the family `z₀`**, and it takes no
hypothesis: the three the construction asks for are `OkaTest/AffineCover.lean`'s theorems and the
injectivity is `Function.injective_id`. -/
def nodeRefineGlueData : LocallyRingedSpace.GlueData.{u} :=
  refineDatumUnitFamGlueData.{u} nodeCoverObj.{u} nodeCoverPoly.{u} id nodeRefineFam.{u}
    nodeCoverGlue.{u} isUnit_nodeRefineFam.{u} hsymm_nodeCover.{u} hrange_nodeCover.{u}
    Function.injective_id hcocycle_nodeCover.{u}

/-- **The analytic space it glues to**, and this is the first refined cover datum at a family that
is not `1` whose index type has a triple of pairwise different indices. -/
def nodeRefinement : AnalyticSpace.{u} :=
  refineDatumUnitFamAnalytification.{u} nodeCoverObj.{u} nodeCoverPoly.{u} id nodeRefineFam.{u}
    nodeCoverGlue.{u} isUnit_nodeRefineFam.{u} hsymm_nodeCover.{u} hrange_nodeCover.{u}
    Function.injective_id hcocycle_nodeCover.{u}

/-- **That space has that glue data's gluing underneath it**, with no transport.

`ComplexAnalytic.refineDatumAnalytificationOfLaws_toLocallyRingedSpace` at the same arguments,
spelled out. **Without it the two definitions above are two well-typed objects with no recorded
relation**, and every statement below about the gluing would say nothing about
`ComplexAnalytic.nodeRefinement`. -/
theorem nodeRefinement_toLocallyRingedSpace :
    nodeRefinement.{u}.toLocallyRingedSpace = nodeRefineGlueData.{u}.toGlueData.glued :=
  refineDatumAnalytificationOfLaws_toLocallyRingedSpace.{u} nodeCoverObj.{u} nodeCoverPoly.{u}
    (id : triple.{u} → triple.{u}) nodeRefineFam.{u}
    (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) nodeCoverGlue.{u}
    (refineDatumUnitFamR.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeRefineFam.{u}
      nodeCoverGlue.{u} isUnit_nodeRefineFam.{u})
    (refineDatumUnitFamU.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeRefineFam.{u}
      nodeCoverGlue.{u} isUnit_nodeRefineFam.{u})
    (refineDatumUnitFamCrossEq.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeRefineFam.{u}
      nodeCoverGlue.{u} isUnit_nodeRefineFam.{u})
    (refineDatumUnitFamCrossUnit.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeRefineFam.{u}
      nodeCoverGlue.{u} isUnit_nodeRefineFam.{u})
    hrange_nodeCover.{u}
    (refineDatumRangeCross_poly.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeRefineFam.{u}
      nodeCoverGlue.{u} _ _ _ _ hrange_nodeCover.{u})
    (refineDatumRangeEq_of_injective.{u} nodeCoverObj.{u} nodeCoverPoly.{u} _ nodeRefineFam.{u} _
      nodeCoverGlue.{u} _ _ _ _ Function.injective_id)
    hsymm_nodeCover.{u} hcocycle_nodeCover.{u}

/-! ### It refines, and there is a triple to refine at -/

/-- **Each refined member is a proper open of its copy of the node**, so this is not
`Oka/Analytification/RefineDatumWitness.lean`'s reindexing: there `fam ≡ 1` and `D(1)` is the whole
member. `localisationOpen_nodePres_ne_top`, from the origin lying off `D(z₀)`. -/
theorem localisationOpen_nodeRefineFam_ne_top (b : triple.{u}) :
    localisationOpen.{u} (nodeCoverObj.{u} b).g (nodeRefineFam.{u} b) ≠ ⊤ :=
  localisationOpen_nodePres_ne_top.{u}

/-- **And it is not empty**, so this is not the other named degeneracy either:
`OkaTest/CoverRefinement.lean` exists because a family constantly `0` was accepted once.
`localisationOpen_nodePres_ne_bot`, from the point of the axis with `z₀ = 1`. -/
theorem localisationOpen_nodeRefineFam_ne_bot (b : triple.{u}) :
    localisationOpen.{u} (nodeCoverObj.{u} b).g (nodeRefineFam.{u} b) ≠ ⊥ :=
  localisationOpen_nodePres_ne_bot.{u}

/-- **There is a triple of pairwise different indices**, which is what makes the two adopted range
conditions non-vacuous here.

This is the exact converse of `ComplexAnalytic.pair_no_distinct_triple`, which is why
`OkaTest/RefineDatumUnitFamily.lean`'s `ℙ¹` instance is evidence about neither condition. Both are
still *discharged* at every index type, by
`ComplexAnalytic.refineDatumRangeCross_poly` and `ComplexAnalytic.refineDatumRangeEq_of_injective`;
what is new here is that the first of the two is spent on a configuration that exists. -/
theorem exists_distinct_triple : ∃ i j k : triple.{u}, i ≠ j ∧ i ≠ k ∧ j ≠ k :=
  ⟨ULift.up 0, ULift.up 1, ULift.up 2, by decide, by decide, by decide⟩

/-! ### The third degeneracy: every refined overlap is the whole refined member -/

/-- **The refined members**, the node localised at `z₀`, one for each of the three indices. An
`abbrev` so that `ComplexAnalytic.refineDatumPoly_of_ne` rewrites underneath it. -/
abbrev nodeRefineObj : triple.{u} → Presentation.{u} :=
  refineDatumObj.{u} nodeCoverObj.{u} (id : triple.{u} → triple.{u}) nodeRefineFam.{u}

/-- **The refined cutting polynomials**, at the caller's `q` taken to be the original datum's own
`poly`. Off the diagonal this is `z₀ · z₀` renamed into the localised member. -/
abbrev nodeRefinePoly (a b : triple.{u}) :
    MvPolynomial (ULift.{u} (Fin (nodeRefineObj.{u} a).n)) ℂ :=
  refineDatumPoly.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (id : triple.{u} → triple.{u})
    nodeRefineFam.{u} (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) a b

/-- **Every off-diagonal overlap of the refined cover is the whole refined member.**

`ComplexAnalytic.refineDatumPoly_of_ne` makes the polynomial `z₀ · z₀` renamed upstairs,
`ComplexAnalytic.localisationOpen_rename` turns the open into the preimage of the one downstairs,
and `ComplexAnalytic.localisationOpen_mul` with `inf_idem` removes the square. What is left is the
preimage of `D(z₀)` along the projection of the localisation **at `z₀`**, and
`ComplexAnalytic.range_base_localisationProj_subset` says every point of that localisation lands
in `D(z₀)` — so the preimage is everything.

**This is where the family being the overlap's own polynomial shows.** At `fam ≡ 1`
(`OkaTest/RefineDatumWitness.lean`) the same computation leaves the preimage of `D(z₀)` along the
projection at `1`, which is `D(z₀)` and proper. The refinement is proper *as a cover of members*
and trivial *as a gluing*, and those are the two different questions this file keeps apart. -/
theorem coverOpen_nodeRefine_eq_top (a b : triple.{u}) (h : a ≠ b) :
    coverOpen.{u} nodeRefineObj.{u} nodeRefinePoly.{u} a b = ⊤ := by
  change localisationOpen.{u} (localisationPresentation.{u} nodePres.{u} nodeX.{u})
      (refineDatumPoly.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (id : triple.{u} → triple.{u})
        nodeRefineFam.{u} (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) a b) = _
  rw [refineDatumPoly_of_ne.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (id : triple.{u} → triple.{u})
      nodeRefineFam.{u} (fun x y ↦ nodeCoverPoly.{u} (id x) (id y)) h,
    localisationOpen_rename.{u} nodePres.{u} nodeX.{u}, localisationOpen_mul.{u}, inf_idem]
  refine Opens.ext (Set.eq_univ_of_forall fun w ↦ ?_)
  exact range_base_localisationProj_subset.{u} nodePres.{u} nodeX.{u} ⟨w, rfl⟩

/-- **Each member's inclusion into the refined gluing is surjective.**

`ComplexAnalytic.surjective_ι_coverGlueData` at the theorem above. Every argument is an underscore
because `ComplexAnalytic.refineDatumUnitFamGlueData` unfolds to `ComplexAnalytic.coverGlueData` at
the refined data, so the elaborator solves them from the goal. -/
theorem surjective_ι_nodeRefine (i : triple.{u}) :
    Function.Surjective (nodeRefineGlueData.{u}.toGlueData.ι i).base :=
  surjective_ι_coverGlueData.{u} _ _ _ _ _ _ coverOpen_nodeRefine_eq_top.{u} i

/-- **The refined space is one of its own members.**

`ComplexAnalytic.isoCoverGlued` at `ComplexAnalytic.coverOpen_nodeRefine_eq_top`, transported
to `ComplexAnalytic.nodeRefinement` through
`ComplexAnalytic.nodeRefinement_toLocallyRingedSpace`.

**This is the third degeneracy and it is not one of the two the board had names for.** The family
is neither `1` nor `0`, every refined member is a proper non-empty open of its copy of the node,
and the gluing is still a single copy of `D(z₀)` — because the members overlap in the whole of
themselves, which is a statement about the refinement's *cutting polynomial* and not about its
family. `ComplexAnalytic.ι_nodeOrigin_ne` is the corresponding statement for the *unrefined* node
cover, in the opposite direction. -/
def isoNodeRefineGlued (i : triple.{u}) :
    nodeRefineGlueData.{u}.toGlueData.U i ≅ nodeRefinement.{u}.toLocallyRingedSpace :=
  (isoCoverGlued.{u} _ _ _ _ _ _ coverOpen_nodeRefine_eq_top.{u} i).trans
    (eqToIso nodeRefinement_toLocallyRingedSpace.{u}).symm

/-! ### And the same at `ℙ¹`

`OkaTest/RefineDatumUnitFamily.lean`'s instance is the same construction at the two-chart cover,
and the computation above used nothing about the node beyond `ComplexAnalytic.nodeCoverPoly` being
constant — which `ComplexAnalytic.lineCoverPoly` also is. So it collapses too, and saying so is
four declarations rather than a remark.
-/

/-- The refined members of `ℙ¹`'s cover: the affine line localised at `z`. -/
abbrev lineRefineObj : pair.{u} → Presentation.{u} :=
  refineDatumObj.{u} lineCoverObj.{u} (id : pair.{u} → pair.{u}) lineRefineFam.{u}

/-- Their cutting polynomials, at the caller's `q` taken to be the datum's own `poly`. -/
abbrev lineRefinePoly (a b : pair.{u}) :
    MvPolynomial (ULift.{u} (Fin (lineRefineObj.{u} a).n)) ℂ :=
  refineDatumPoly.{u} lineCoverObj.{u} lineCoverPoly.{u} (id : pair.{u} → pair.{u})
    lineRefineFam.{u} (fun x y ↦ lineCoverPoly.{u} (id x) (id y)) a b

/-- **The refined charts of `ℙ¹` overlap in the whole of themselves too**, by the same computation
as `ComplexAnalytic.coverOpen_nodeRefine_eq_top` with `z` for `z₀`. -/
theorem coverOpen_lineRefine_eq_top (a b : pair.{u}) (h : a ≠ b) :
    coverOpen.{u} lineRefineObj.{u} lineRefinePoly.{u} a b = ⊤ := by
  change localisationOpen.{u} (localisationPresentation.{u} lineRel.{u} lineZ.{u})
      (refineDatumPoly.{u} lineCoverObj.{u} lineCoverPoly.{u} (id : pair.{u} → pair.{u})
        lineRefineFam.{u} (fun x y ↦ lineCoverPoly.{u} (id x) (id y)) a b) = _
  rw [refineDatumPoly_of_ne.{u} lineCoverObj.{u} lineCoverPoly.{u} (id : pair.{u} → pair.{u})
      lineRefineFam.{u} (fun x y ↦ lineCoverPoly.{u} (id x) (id y)) h,
    localisationOpen_rename.{u} lineRel.{u} lineZ.{u}, localisationOpen_mul.{u}, inf_idem]
  refine Opens.ext (Set.eq_univ_of_forall fun w ↦ ?_)
  exact range_base_localisationProj_subset.{u} lineRel.{u} lineZ.{u} ⟨w, rfl⟩

/-- The glue data behind `ComplexAnalytic.lineRefinement`. -/
def lineRefineGlueData : LocallyRingedSpace.GlueData.{u} :=
  refineDatumUnitFamGlueData.{u} lineCoverObj.{u} lineCoverPoly.{u} id lineRefineFam.{u}
    lineSwapIso.{u} isUnit_lineRefineFam.{u} hsymm_lineCover.{u} hrange_lineCover.{u}
    Function.injective_id hcocycle_lineCover.{u}

/-- **`ComplexAnalytic.lineRefinement`'s gluing is one chart's `D(z)`.**

The `ℙ¹` instance is a proper refinement of a cover of `ℙ¹` and its glued space is a single copy
of `𝔸¹ ∖ {0}`. **Nothing in `OkaTest/RefineDatumUnitFamily.lean` says otherwise** — that file
records that it makes no claim about its glued space in either direction — and this is why the
absence it records is worth the space it takes. -/
def isoLineRefineGlued (i : pair.{u}) :
    lineRefineGlueData.{u}.toGlueData.U i ≅ lineRefineGlueData.{u}.toGlueData.glued :=
  isoCoverGlued.{u} _ _ _ _ _ _ coverOpen_lineRefine_eq_top.{u} i

end

end ComplexAnalytic

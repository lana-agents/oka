/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
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

## What this is not

* **It is not a proper refinement.** Every refined member is the whole of its original member —
  that is what the surjectivity above says — so what this exhibits is the node cover **reindexed
  along `id`**, not a cover cut down. What makes it a witness rather than a restatement is that
  `σ = id` is injective on a three-element type, so `σ a ≠ σ b` at every pair of distinct indices
  and `ComplexAnalytic.refineDatumGlue` takes its **cross-member** branch — the one that reads the
  original datum's own `glue` through `ComplexAnalytic.refineDatumCrossAlgEquiv` — at every pair.
  A witness at a family that is not a unit is still open, and
  `ComplexAnalytic.exists_refineDatumCross_of_isUnit` says what one would need of its family.
* **Nothing here says the glued space is not one member, and nothing has attempted it.**
  `ComplexAnalytic.ι_nodeOrigin_ne` proves that for the *unrefined* node cover, by exhibiting three
  distinct points of the gluing. **This bullet used to give the obstacle as
  `ComplexAnalytic.ι_nodeOrigin_ne`'s proof reading `CategoryTheory.GlueData'.f'` off the
  unrefined datum, with "no such reading of the refined datum" existing. Both halves of that were
  wrong.** That proof reads `CategoryTheory.GlueData.f` and not `GlueData'.f'`, through
  `OkaTest/AffineCover.lean`'s `ComplexAnalytic.f_nodeTripleGlueData`, which is
  `CategoryTheory.GlueData.ofGlueData'_f_of_ne`; and the general form of exactly that is
  `ComplexAnalytic.f_coverGlueData_of_ne` (`Oka/Analytification/CoverGlueTop.lean`), which is
  hypothesis-free and applies **here** — `OkaTest.RefineDatumWitness.nodeRefineOneGlueData` is
  `ComplexAnalytic.coverGlueData` at the refined arguments, so the `CategoryTheory.GlueData'` it
  needs is solved from the goal, as that file's docstring says in terms. Compiled as a check
  rather than read off the two docstrings.

  **What is genuinely absent is the rest of the argument, not its first ingredient**: the analogue
  of `ComplexAnalytic.range_f_subset_nodeTripleGlueData` at this datum, and a point of a refined
  member lying off the refined overlap. Neither is attempted here and neither is priced. **The two
  checks above are about the overlaps and not about the gluing**, which is weaker, and the
  difference is what `OkaTest/AffineCover.lean` spends its second half on.
* **No `admissible`, no scheme and no comparison functor**, as in the files this one sits beside.

## Main definitions

- `OkaTest.RefineDatumWitness.nodeRefineOneGlueData` and `nodeRefineOneAnalytification`: **the glue
  data and the analytic space of the node cover refined at `σ = id` and a trivial refining
  family**, with every hypothesis discharged.

## Main results

- `OkaTest.RefineDatumWitness.not_isConstant_id_triple`: **the index map of that witness is not
  constant.**
- `OkaTest.RefineDatumWitness.nodeRefineOneAnalytification_toLocallyRingedSpace`: **the space is
  that glue data's gluing**, with no transport.
- `OkaTest.RefineDatumWitness.coverOpen_nodeRefineOne_eq`: **the refined overlap is the preimage of
  the original one.**
- `OkaTest.RefineDatumWitness.coverOpen_nodeRefineOne_ne_bot` and `..._ne_top`: **it is non-empty
  and proper.**
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
overlaps needs a point of a double localisation to be written down. -/
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

end

end OkaTest.RefineDatumWitness

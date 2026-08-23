/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.AnalytificationDistinguishedOpen

/-!
# Non-vacuity of the glue data of an affine cover

`ComplexAnalytic.coverGlueData` takes five inputs and produces an
`AlgebraicGeometry.LocallyRingedSpace.GlueData`. Two things could be wrong with it and neither is
visible from its type: the hypotheses `hrange` and `hcocycle` could be unsatisfiable except in
degenerate cases, and the glued space could be one member rather than several. This file rules
both out, on **three copies of the node glued along the punctured axis**, which is the smallest
input that exercises `t'` and the cocycle condition at all — with two members there are no
triples of distinct indices and both are vacuous.

* **The transition data is computed, not merely assumed.**
  `ComplexAnalytic.coverTransition_hom_nodeCover` and `ComplexAnalytic.coverTriple_nodeCover`
  say the transition and its restriction to triple overlaps are the identity here, which is what
  makes `hrange` and `hcocycle` provable and is a check that the definitions are what they are
  meant to be rather than accidentally something else.
* **The overlap is a proper, nonempty open subset**, by
  `localisationOpen_nodePres_ne_top` and `localisationOpen_nodePres_ne_bot` in
  `OkaTest/AnalytificationDistinguishedOpen.lean` — both in the root namespace, as that file has
  them. So this is not three copies glued along
  everything — which would return one copy — nor along nothing.
* **The three copies are genuinely distinct in the gluing.**
  `ComplexAnalytic.ι_nodeOrigin_ne`: the origin of the node lies off the punctured axis, so its
  three images in the glued space are three different points. With
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` this says the glued space
  is covered by three copies of the node and is not any one of them. **This is the check that
  stops `coverGlueData` from being satisfied by a construction that quietly returns its first
  member.**

**What is not checked here.** Nothing says the glued space is not the analytification of *some*
presentation — the node with a tripled origin is intuitively not affine, but proving it needs an
invariant nothing in this repository computes. Nor is there an analytic structure on the gluing:
that is `ComplexAnalytic.AnalyticSpace.ofGlueData`, which needs the compatibility of the algebra
structures on the glued space and is a separate step. And the transition here is the identity, so
nothing in *this* file exercises a non-trivial algebra isomorphism between the two descriptions of
an overlap; `OkaTest/ProjectiveLine.lean` is the example that does, gluing two copies of `𝔸¹`
along `D(z)` by `z ↦ 1/z`. The two files are complementary and neither replaces the other: with
two members there is no triple of distinct indices, so `t'` and the cocycle are vacuous there and
have content only here.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### Three copies of the node -/

/-- The index type of the cover: three copies. Two would make the cocycle condition vacuous. -/
abbrev triple : Type u := ULift.{u} (Fin 3)

/-- Every member is the node. -/
abbrev nodeCoverObj : triple.{u} → Presentation.{u} := fun _ ↦ ⟨2, 1, nodePres.{u}⟩

/-- Every overlap is cut out by `z₀`, so every one of them is the punctured axis. -/
abbrev nodeCoverPoly :
    ∀ i : triple.{u}, triple.{u} → MvPolynomial (ULift.{u} (Fin (nodeCoverObj.{u} i).n)) ℂ :=
  fun _ _ ↦ nodeX.{u}

/-- Every transition is the identity. The two presentations of an overlap are literally the same
presentation here, so `Iso.refl` typechecks; a cover with a *non-trivial* transition needs an
isomorphism of presented algebras, which is what `ℙ¹` would require. -/
abbrev nodeCoverGlue (i j : triple.{u}) :
    coverOverlap.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j ≅
      coverOverlap.{u} nodeCoverObj.{u} nodeCoverPoly.{u} j i :=
  Iso.refl _

/-! ### The hypotheses, computed -/

/-- The analytified transition is the identity, since `Functor.mapIso` of an identity is one. -/
theorem coverGlueIso_nodeCover (i j : triple.{u}) :
    coverGlueIso.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} i j = Iso.refl _ := by
  rw [coverGlueIso, Functor.mapIso_refl, Functor.mapIso_refl]
  rfl

/-- **The transition on the overlap is the identity**, because the two comparison isomorphisms it
is conjugated by are the same isomorphism. This is the computation that makes the two hypotheses
below provable. -/
theorem coverTransition_hom_nodeCover (i j : triple.{u}) :
    (coverTransition.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} i j).hom = 𝟙 _ := by
  have h : coverOverlapIso.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j =
      coverOverlapIso.{u} nodeCoverObj.{u} nodeCoverPoly.{u} j i := rfl
  rw [coverTransition, Iso.trans_hom, Iso.trans_hom, coverGlueIso_nodeCover, Iso.refl_hom,
    Iso.symm_hom, Category.id_comp, h, Iso.inv_hom_id]

/-- The triple overlap maps into the ambient member by its own inclusion. -/
theorem coverTripleIncl_comp_nodeCover (i j k : triple.{u}) :
    coverTripleIncl.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j k ≫
        coverTransitionHom.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} i j =
      (coverSpace.{u} nodeCoverObj.{u} i).ofRestrict
        (coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j ⊓
          coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i k).isOpenEmbedding := by
  rw [coverTransitionHom, coverTransition_hom_nodeCover, Category.id_comp]
  exact LocallyRingedSpace.restrictLE_fac _ _

/-- The range hypothesis, with equality rather than containment: the transition carries the triple
overlap onto the triple overlap. -/
theorem hrange_nodeCover (i j k : triple.{u}) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k) :
    Set.range (coverTripleIncl.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j k ≫
        coverTransitionHom.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} i j).base ⊆
      ((coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} j k ⊓
          coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} j i :
        Opens (coverSpace.{u} nodeCoverObj.{u} j)) :
          Set (coverSpace.{u} nodeCoverObj.{u} j)) := by
  rw [coverTripleIncl_comp_nodeCover]
  exact le_of_eq (LocallyRingedSpace.range_ofRestrict _ _)

/-- **The transition on triple overlaps is the identity**, by the uniqueness of a factorisation
through an open subspace. -/
theorem coverTriple_nodeCover (i j k : triple.{u}) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coverTriple.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} hrange_nodeCover.{u}
        i j k hij hik hjk = 𝟙 _ := by
  rw [coverTriple]
  exact (LocallyRingedSpace.liftRestrict_uniq _ _ _ (𝟙 _)
    (by rw [Category.id_comp, coverTripleIncl_comp_nodeCover])).symm

/-- The symmetry hypothesis. -/
theorem hsymm_nodeCover (i j : triple.{u}) :
    nodeCoverGlue.{u} j i = (nodeCoverGlue.{u} i j).symm :=
  (Iso.refl_symm _).symm

/-- The cocycle hypothesis, which is where three members rather than two earns its keep: this
statement is about a triple of *distinct* indices and there is no such triple in a two-member
cover. -/
theorem hcocycle_nodeCover (i j k : triple.{u}) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coverTriple.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} hrange_nodeCover.{u}
        i j k hij hik hjk ≫
      coverTriple.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} hrange_nodeCover.{u}
        j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} hrange_nodeCover.{u}
        k i j hik.symm hjk.symm hij = 𝟙 _ := by
  rw [coverTriple_nodeCover, coverTriple_nodeCover, coverTriple_nodeCover, Category.id_comp,
    Category.id_comp]

/-! ### The gluing -/

/-- The `CategoryTheory.GlueData'` behind the gluing, named because
`CategoryTheory.GlueData'.f'` below cannot be stated with a `_` for it. With `_` in its place the
index `j` is checked against the expected type `GlueData'.J ?D`, a projection applied to a
metavariable, which the elaborator will not solve for `?D`, so the application is rejected:

```
error: Application type mismatch: The argument
  j
has type
  triple
but is expected to have type
  GlueData'.J ?m.24
```

**It fails at once and nothing diverges** — measured, at four seconds for this whole file, with
that as the only error. An earlier version of this docstring said the unifier *unfolds forever*;
the conclusion was right and the mechanism was not. -/
abbrev nodeTripleGlueData' : GlueData' LocallyRingedSpace.{u} :=
  coverGlueData'.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} hrange_nodeCover.{u}
    hsymm_nodeCover.{u} hcocycle_nodeCover.{u}

/-- **Three copies of the node, glued along the punctured axis.** -/
def nodeTripleGlueData : LocallyRingedSpace.GlueData.{u} :=
  coverGlueData.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} hrange_nodeCover.{u}
    hsymm_nodeCover.{u} hcocycle_nodeCover.{u}

/-- The members are the node, on the nose. -/
example (i : triple.{u}) :
    nodeTripleGlueData.{u}.U i = (AnalyticSpace.node.{u}).toLocallyRingedSpace := rfl

/-- The overlaps are proper open subsets: this is not three copies glued along everything. -/
example : coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (ULift.up 0) (ULift.up 1) ≠ ⊤ :=
  localisationOpen_nodePres_ne_top.{u}

/-- Nor along nothing. -/
example : coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} (ULift.up 0) (ULift.up 1) ≠ ⊥ :=
  localisationOpen_nodePres_ne_bot.{u}

/-- **The inclusion of a member into the gluing is `CategoryTheory.GlueData'.f'` off the
diagonal**, which is an `eqToHom` followed by the inclusion of the overlap.

`eqToHom` appears here because `CategoryTheory.GlueData'.f'` is *defined* with one, and the `dite`
it sits in is dependent — `rw [dif_neg]` reports *motive is not type correct*, so the branch has
to be taken with `split_ifs`. -/
theorem f_nodeTripleGlueData (i j : triple.{u}) (hij : i ≠ j) :
    nodeTripleGlueData.{u}.toGlueData.f i j =
      eqToHom (dif_neg hij) ≫ coverIncl.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j := by
  change CategoryTheory.GlueData'.f' nodeTripleGlueData'.{u} i j = _
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs with h
  · exact absurd h hij
  · rfl

/-- The image of that inclusion lies in the overlap, which is what the point below needs. -/
theorem range_f_subset_nodeTripleGlueData (i j : triple.{u}) (hij : i ≠ j) :
    Set.range (nodeTripleGlueData.{u}.toGlueData.f i j).base ⊆
      (coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j :
        Set (coverSpace.{u} nodeCoverObj.{u} i)) := by
  rintro _ ⟨z, rfl⟩
  rw [f_nodeTripleGlueData i j hij]
  exact ((coverSpace.{u} nodeCoverObj.{u} i).range_ofRestrict
    (coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j)).le ⟨_, rfl⟩

/-- **The three copies are distinct in the gluing.**

The origin of the node is not on the punctured axis, so it is glued to nothing: by
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` two members' points agree in the gluing
only if they come from a point of the overlap, and the image of the overlap misses the origin.

This is what stops `ComplexAnalytic.coverGlueData` from being satisfied by a construction that
returns one member and ignores the rest, and it is the reason the cover is by three copies of one
space rather than by one space. -/
theorem ι_nodeOrigin_ne (i j : triple.{u}) (hij : i ≠ j) :
    (nodeTripleGlueData.{u}.toGlueData.ι i).base nodeOrigin.{u} ≠
      (nodeTripleGlueData.{u}.toGlueData.ι j).base nodeOrigin.{u} := by
  rw [Ne, LocallyRingedSpace.GlueData.ι_eq_iff]
  rintro ⟨z, hz, -⟩
  have hmem : nodeOrigin.{u} ∈ localisationOpen.{u} nodePres.{u} nodeX.{u} :=
    range_f_subset_nodeTripleGlueData i j hij ⟨z, hz⟩
  exact (mem_localisationOpen_iff.{u} nodePres.{u} nodeX.{u}).1 hmem (MvPolynomial.eval_X _)

/-- Each member is an open subspace of the gluing; with `ι_jointly_surjective` and
`ι_nodeOrigin_ne`, the glued space is covered by three copies of the node and is none of them. -/
example (i : triple.{u}) :
    LocallyRingedSpace.IsOpenImmersion (nodeTripleGlueData.{u}.toGlueData.ι i) :=
  coverGlueData_ι_isOpenImmersion.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u}
    hrange_nodeCover.{u} hsymm_nodeCover.{u} hcocycle_nodeCover.{u} i

end

end ComplexAnalytic

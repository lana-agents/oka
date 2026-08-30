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
* **And they are distinct as points of the analytic space**, which is a different statement and
  is the one `Oka/Analytification/AffineCover.lean` needs.
  `ComplexAnalytic.base_nodeIota_nodeOrigin_ne` says it of `ComplexAnalytic.nodeTripleSpace` and
  `ComplexAnalytic.nodeIota`; `ComplexAnalytic.isOpenImmersion_nodeIota` says each copy is an
  open subspace of it. **This file is the non-vacuity of
  `ComplexAnalytic.coverAnalytification`**, and it is the three-member one, so unlike
  `OkaTest/ProjectiveLine.lean`'s it exercises both triple-overlap hypotheses — which
  `ComplexAnalytic.GlueShape.hRange_of_no_three` and
  `ComplexAnalytic.GlueShape.hCocycle_of_no_three` make vacuous below three members.

**What is not checked here.** Nothing says the glued space is not the analytification of *some*
presentation — the node with a tripled origin is intuitively not affine, but proving it needs an
invariant nothing in this repository computes — and `ComplexAnalytic.nodeTripleSpace` below does
not change that: an analytic structure is a statement about the sheaves and says nothing about
affineness. **Nor does anything here relate the input to a scheme.** And the transition here is
the identity, so
nothing in *this* file exercises a non-trivial algebra isomorphism between the two descriptions of
an overlap; `OkaTest/ProjectiveLine.lean` is the example that does, gluing two copies of `𝔸¹`
along `D(z)` by `z ↦ 1/z`. The two files are complementary and neither replaces the other: with
two members there is no triple of distinct indices, so `t'` and the cocycle are vacuous there and
have content only here.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

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

/-- The range hypothesis. The transition carries the triple overlap onto the triple overlap
`D(f_jk) ⊓ D(f_ji)` — with equality, not merely containment — and the hypothesis asks only for the
`D(f_jk)` half of that, so the proof is the equality followed by `inf_le_left`. -/
theorem hrange_nodeCover (i j k : triple.{u}) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k) :
    Set.range (coverTripleIncl.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j k ≫
        coverTransitionHom.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} i j).base ⊆
      (coverOpen.{u} nodeCoverObj.{u} nodeCoverPoly.{u} j k :
        Set (coverSpace.{u} nodeCoverObj.{u} j)) := by
  rw [coverTripleIncl_comp_nodeCover]
  exact (le_of_eq (LocallyRingedSpace.range_ofRestrict _ _)).trans inf_le_left

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

`eqToHom` appears here because `CategoryTheory.GlueData'.f'` is *defined* with one. The `dite` it
sits in is dependent, so the branch cannot be taken with `rw [dif_neg]`, which reports *motive is
not type correct*; `AlgebraicGeometry.LocallyRingedSpace`'s glue data is not special in this and
the unfolding is now `CategoryTheory.GlueData.ofGlueData'_f_of_ne`, in the mirror tree. -/
theorem f_nodeTripleGlueData (i j : triple.{u}) (hij : i ≠ j) :
    nodeTripleGlueData.{u}.toGlueData.f i j =
      eqToHom (dif_neg hij) ≫ coverIncl.{u} nodeCoverObj.{u} nodeCoverPoly.{u} i j :=
  CategoryTheory.GlueData.ofGlueData'_f_of_ne nodeTripleGlueData'.{u} hij

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

/-! ### The analytic structure on the gluing

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` needs the transitions to be `ℂ`-linear
(`ComplexAnalytic.GlueDataCLinear`), which reads `D.f` and `D.t` — and for a glue datum built by
`CategoryTheory.GlueData.ofGlueData'` those are dependent `dite`s.
`ComplexAnalytic.glueDataCLinear_coverGlueData` discharges that hypothesis once and for all glue
data this construction builds, using `Oka/CategoryTheory/GlueData.lean`'s unfolding lemmas to get
past the `dite`s; without them this section could not be written. -/

/-- The `ℂ`-algebra structure each member of the cover carries: the analytification's own. -/
abbrev nodeAlg (j : triple.{u}) :
    ℂ →+* ((nodeTripleGlueData.{u}).U j).presheaf.obj (op ⊤) :=
  (AnalyticSpace.analytification.{u} (nodeCoverObj.{u} j).g).algebraMap

/-- **The transitions are `ℂ`-linear**, by `ComplexAnalytic.glueDataCLinear_coverGlueData`.

Nothing here is special to this cover. That lemma discharges the hypothesis for **every** glue
datum `ComplexAnalytic.coverGlueData` builds, because every morphism
`ComplexAnalytic.coverTransition` is assembled from is a morphism of *analytic* spaces and carries
its `ℂ`-linearity as a field; the
`dite`s of `CategoryTheory.GlueData.ofGlueData'` are got past inside it, once, rather than here.
`OkaTest/ProjectiveLine.lean` applies the same lemma at a glue datum whose transition is **not**
the identity. -/
theorem glueDataCLinear_nodeTripleGlueData :
    GlueDataCLinear.{u} nodeTripleGlueData.{u} nodeAlg.{u} :=
  glueDataCLinear_coverGlueData.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u}
    hrange_nodeCover.{u} hsymm_nodeCover.{u} hcocycle_nodeCover.{u}

/-- **Each member has local models**: it *is* an analytification, and the structure it carries is
that analytification's own. -/
theorem hasLocalModels_nodeTripleGlueData (j : triple.{u}) :
    HasLocalModels.{u} ((nodeTripleGlueData.{u}).U j) (nodeAlg.{u} j) :=
  (AnalyticSpace.analytification.{u} (nodeCoverObj.{u} j).g).local_model

/-- **Three copies of the node, glued along the punctured axis, as a complex analytic space.**

This is the first analytic space in this repository glued out of more than one piece.
`ComplexAnalytic.ι_nodeOrigin_ne` above says its three copies of the origin are three distinct
points, and `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` says the three
members cover it.

**It is not shown to be non-affine**, and no statement below says so: that it is not the
analytification of *some* presentation is a much stronger claim needing an invariant nothing here
computes, and `Oka/Analytification/AffineCover.lean` records the same about it. -/
def nodeTripleSpace : AnalyticSpace.{u} :=
  coverAnalytification.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u}
    hrange_nodeCover.{u} hsymm_nodeCover.{u} hcocycle_nodeCover.{u}

/-- **The general construction and the `ofGlueDataCLinear` call this file used to make are the
same space**, on the nose.

Kept as an `example` rather than dropped: it is the whole content of quoting
`ComplexAnalytic.coverAnalytification` here instead of rebuilding, and if the two ever stop
agreeing this is what says so. -/
example : nodeTripleSpace.{u} =
    AnalyticSpace.ofGlueDataCLinear.{u} nodeTripleGlueData.{u} nodeAlg.{u}
      glueDataCLinear_nodeTripleGlueData.{u} hasLocalModels_nodeTripleGlueData.{u} := rfl

/-- Its underlying locally ringed space is the gluing, on the nose. -/
example : (nodeTripleSpace.{u}).toLocallyRingedSpace =
    nodeTripleGlueData.{u}.toGlueData.glued := rfl

/-- **The `i`-th copy of the node, as a morphism of analytic spaces into the glued space.**

`ComplexAnalytic.coverIota` at this cover. Named so that the two statements below are about
`ComplexAnalytic.nodeTripleSpace` and morphisms into it, rather than about a glue datum. -/
def nodeIota (i : triple.{u}) :
    AnalyticSpace.analytification.{u} (nodeCoverObj.{u} i).g ⟶ nodeTripleSpace.{u} :=
  coverIota.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u} hrange_nodeCover.{u}
    hsymm_nodeCover.{u} hcocycle_nodeCover.{u} i

/-- **The three copies of the origin are three distinct points of the analytic space.**

`ComplexAnalytic.ι_nodeOrigin_ne` says this of the glue datum's gluing;
`ComplexAnalytic.toLRSHom_coverIota` is what carries it to `ComplexAnalytic.nodeTripleSpace` and
`ComplexAnalytic.nodeIota`. **Its content is that bridge and no new geometry** — the two statements
are equal after unfolding, and the reason to have both is that everything proved about the gluing
reaches `X^an` only through `ComplexAnalytic.coverAnalytification_toLocallyRingedSpace` and this
lemma.

It is what makes a three-member instance of `ComplexAnalytic.coverAnalytification` evidence rather
than a type-check: at two members `ComplexAnalytic.GlueShape.hRange_of_no_three` and
`ComplexAnalytic.GlueShape.hCocycle_of_no_three` make both triple-overlap hypotheses vacuous, so
`OkaTest/ProjectiveLine.lean`'s instance exercises neither. -/
theorem base_nodeIota_nodeOrigin_ne (i j : triple.{u}) (hij : i ≠ j) :
    (nodeIota.{u} i).toLRSHom.base nodeOrigin.{u} ≠
      (nodeIota.{u} j).toLRSHom.base nodeOrigin.{u} := by
  rw [nodeIota, nodeIota, toLRSHom_coverIota, toLRSHom_coverIota]
  exact ι_nodeOrigin_ne.{u} i j hij

/-- **Each copy is an open subspace of the analytic space**, by
`ComplexAnalytic.isOpenImmersion_coverIota`. -/
theorem isOpenImmersion_nodeIota (i : triple.{u}) :
    LocallyRingedSpace.IsOpenImmersion (nodeIota.{u} i).toLRSHom :=
  isOpenImmersion_coverIota.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u}
    hrange_nodeCover.{u} hsymm_nodeCover.{u} hcocycle_nodeCover.{u} i

/-- **The three copies, as an open cover of the space they glue to.**

`ComplexAnalytic.coverAnalytificationOpenCover` at this cover, named for the same reason
`ComplexAnalytic.nodeIota` is: so that the two `example`s below are about
`ComplexAnalytic.nodeTripleSpace` and not about a glue datum.

This is the non-vacuity of that definition, and it is the **three**-member instance deliberately:
`ComplexAnalytic.GlueShape.hRange_of_no_three` and
`ComplexAnalytic.GlueShape.hCocycle_of_no_three` make both triple-overlap hypotheses vacuous below
three members, so `OkaTest/ProjectiveLine.lean`'s two-member cover would exercise neither. -/
noncomputable def nodeTripleOpenCover :
    LocallyRingedSpace.OpenCover.{u} (nodeTripleSpace.{u}).toLocallyRingedSpace :=
  coverAnalytificationOpenCover.{u} nodeCoverObj.{u} nodeCoverPoly.{u} nodeCoverGlue.{u}
    hrange_nodeCover.{u} hsymm_nodeCover.{u} hcocycle_nodeCover.{u}

/-- **Its maps are `ComplexAnalytic.nodeIota`**, on the nose — which is the check that the cover
is by the three copies of the node and not by three objects of the glue datum that happen to be
them. -/
example (i : triple.{u}) :
    (nodeTripleOpenCover.{u}).map i = (nodeIota.{u} i).toLRSHom := rfl

/-- **And its members are their analytifications**, on the nose. -/
example (i : triple.{u}) :
    (nodeTripleOpenCover.{u}).obj i =
      (AnalyticSpace.analytification.{u} (nodeCoverObj.{u} i).g).toLocallyRingedSpace := rfl

/-- **The glued `ℂ`-algebra structure restricts on each member to the one that member was
given** — the check that the construction is the intended one rather than merely well-typed. -/
example (j : triple.{u}) :
    LocallyRingedSpace.comapAlgMap (nodeTripleGlueData.{u}.toGlueData.ι j)
      (nodeTripleSpace.{u}).algebraMap = nodeAlg.{u} j :=
  AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap.{u} _ _
    glueDataCLinear_nodeTripleGlueData.{u} hasLocalModels_nodeTripleGlueData.{u} j

end

end ComplexAnalytic

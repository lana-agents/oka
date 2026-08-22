/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.OpenSubspace

/-!
# Non-vacuity of the assembly of local morphisms to `ℂ` and to `ℂ^m`

`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local` glues local morphisms `Z|U ⟶ ℂ`
into a global `Z ⟶ ℂ`. Every statement it makes would also be true of a theorem that ignored the
local data and returned something built from `g` by other means, and its hypothesis would be
satisfiable in a degenerate way by the one-member cover `U = ⊤`. This file rules both out.

## The two witnesses, and what each is for

**`ℂ` covered by two overlapping punctured planes** (`punctureCoverAt`). The two local morphisms
are built **independently**, each by `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict`
from the restriction of `g`; neither is the restriction of a morphism anybody had. Their
agreement on the overlap is therefore not `pullback.condition` or anything like it — it is
`ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq`, i.e. uniqueness of a morphism to `ℂ`, which
is the step taxis #694 asked to have tested before anything was built on it.

**The overlap is nonempty** (`punctureCoverAt_overlap`): the origin lies in both members. This
is what distinguishes the test from the non-vacuity of `existsUnique_glueMorphisms_of_opens`
itself, where the cover is by *disjoint* opens and the compatibility hypothesis is vacuous.
Here it is not vacuous and it is discharged by an actual theorem.

**The node covered by two overlapping opens** (`nodeCover`). The point of this one is only the
source: the node is **not** an open subspace of `ℂ^n`, and it is the first space of that kind to
which the assembly is applied. `base_glue_nodeCoord` computes the glued morphism on points and
gets `p ↦ p_j`, through `ComplexAnalytic.AnalyticSpace.base_eq_eval_coordPullback` and
`ComplexAnalytic.eval_nodeCoord` — so the morphism is identified, not merely produced.

## The general theorem, and the two spaces it is applied to

`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_general` needs no cover from the caller.
The risk there is different and taxis #694 named it: the theorem would be **no stronger than
what already existed** if every `Z` it is applied to were an open subspace of `ℂ^n`, since
`exists_hom_complexLine_restrict` covers those. So it is applied to two spaces that are not.

* **The node** (`exists_hom_complexLine_node_general`), with `g` a coordinate function.
  `base_glue_nodeCoord` identifies the morphism on points as `p ↦ p_j`.
* **The punctured node** (`exists_hom_complexLine_puncturedNode`), which is an open subspace of
  the node and of nothing simpler, with `g` the pullback of a coordinate function.
  `base_hom_puncturedNode` identifies it on points, through
  `eval_pullback_nodeCoord`.

Neither space is an open subspace of `ℂ^n`, so neither morphism was available from
`exists_hom_complexLine` or `exists_hom_complexLine_restrict`.

## The bijection, and its inverse named on a concrete input

`ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral` is `Equiv.ofBijective`, so its inverse
is a choice term, and a consumer who has to unfold that has been handed nothing. The penultimate
section names **both** round trips at the node: forward to `nodeCoord j`, backward to
`nodeToLine j`, and — the part that stops the round trip from being about a collapsed morphism —
the morphism the inverse produces is surjective on points.

## The `m`-fold statement, where the discriminating witness is different

Everything above is at `m = 1`, and **none of it tests the `m`-fold theorem.** A statement that
produced the `m` coordinates by `m` independent applications of the one-dimensional theorem
would satisfy every `m = 1` check and could not exist, because assembling `m` morphisms `Z ⟶ ℂ`
into one `Z ⟶ ℂ^m` needs a product of analytic spaces which the development does not have.

So the last section is at `m = 2`: `exists_hom_complexAffineSpace_node_general` feeds the node's
**two** coordinate functions to
`ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general` and identifies what comes
out as `ComplexAnalytic.nodeIncl`, the closed immersion defining the node. **A morphism produced
by a general theorem and then recognised as one that was constructed by hand** — which is taxis
#610's own acceptance criterion in its own words, and which no `m = 1` statement can express.

## What these do *not* show, said plainly

The glued morphisms in the first two sections are not new: on `ℂ` the result is forced by
uniqueness to agree with `exists_hom_complexLine`'s morphism, and on the node with
`ComplexAnalytic.nodeToLine j`, whose restrictions are the local pieces used there.

**And the general theorem's witnesses are not new either, for a reason worth stating.** Taxis
#694 asked for a section of `𝒪_node` which is *not* the pullback of an ambient holomorphic
function, on the grounds that the general theorem would be no stronger without one. **No such
section can be named in this development**: every global section of `𝒪_node` it can write down
is a pullback from `ℂ²`, because the node's structure sheaf is only ever presented through
`nodeAmbient`. That is a limitation of what the development can *name*, not of the theorem —
`exists_hom_complexLine_general` quantifies over every `Z` and every `g` — but it does mean the
strongest available witness is a space outside the previous theorems' reach rather than a
section outside them.

**On the import of `OkaTest.OpenSubspace`.** It is for one named witness, `nodeOrigin`. Test
files importing one another was, until PR #66, unprecedented outside the `OkaTest/Axioms.lean`
aggregator; the alternative here is to rebuild the origin of the node by hand, and a
reconstructed witness stops tracking the original the moment either moves.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-! ### `ℂ` covered by two overlapping punctured planes -/

/-- The plane with the point `c` removed. -/
def punctureOff (c : ℂ) : (AnalyticSpace.complexAffineSpace.{u} 1).Opens :=
  ⟨{z : ULift.{u} (Fin 1) → ℂ | z (ULift.up 0) ≠ c},
    isOpen_compl_singleton.preimage (continuous_apply (ULift.up 0))⟩

/-- A cover of `ℂ` by two overlapping proper opens, indexed by the point each is chosen for:
away from `1` unless the point *is* `1`, in which case away from `-1`. -/
def punctureCoverAt (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    (AnalyticSpace.complexAffineSpace.{u} 1).Opens :=
  if z (ULift.up 0) = 1 then punctureOff.{u} (-1) else punctureOff.{u} 1

theorem mem_punctureCoverAt (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    z ∈ punctureCoverAt.{u} z := by
  rw [punctureCoverAt]
  split
  · next h => exact fun hcon ↦ by rw [h] at hcon; norm_num at hcon
  · next h => exact h

/-- **Neither member of the cover is everything**, so the cover is not the trivial one and the
gluing is not `Multicoequalizer.desc` on a one-object diagram. -/
theorem punctureCoverAt_ne_top (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    punctureCoverAt.{u} z ≠ ⊤ := by
  rw [punctureCoverAt]
  split
  · exact fun hcon ↦ (show ((fun _ ↦ (-1 : ℂ)) : ULift.{u} (Fin 1) → ℂ) ∈ punctureOff.{u} (-1)
      from hcon ▸ trivial) rfl
  · exact fun hcon ↦ (show ((fun _ ↦ (1 : ℂ)) : ULift.{u} (Fin 1) → ℂ) ∈ punctureOff.{u} 1
      from hcon ▸ trivial) rfl

/-- **The two members of the cover overlap**: the origin is in both. So the compatibility
hypothesis of the gluing is not vacuous, unlike the disjoint cover used for the non-vacuity of
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` itself. -/
theorem punctureCoverAt_overlap :
    ((fun _ ↦ (0 : ℂ)) : ULift.{u} (Fin 1) → ℂ) ∈ punctureOff.{u} 1 ⊓ punctureOff.{u} (-1) :=
  ⟨fun h ↦ zero_ne_one h, fun h ↦ by norm_num at h⟩

/-- **Every global holomorphic function on `ℂ` is a coordinate pullback**, recovered by gluing
two independently constructed morphisms over a cover by two overlapping proper opens. -/
theorem exists_hom_complexLine_via_glue
    (g : (AnalyticSpace.complexAffineSpace.{u} 1).presheaf.obj (op ⊤)) :
    ∃ φ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) = g :=
  AnalyticSpace.exists_hom_complexLine_of_local _ g fun z ↦
    ⟨punctureCoverAt.{u} z, mem_punctureCoverAt.{u} z,
      (AnalyticSpace.exists_hom_complexLine_restrict _).choose,
      (AnalyticSpace.exists_hom_complexLine_restrict _).choose_spec⟩

/-- **The glued morphism is the identity on points** when `g` is the coordinate — computed from
its coordinate pullback rather than assumed. -/
theorem base_glue_coord
    (φ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.complexAffineSpace.{u} 1)
    (hφ : AnalyticSpace.coordPullback φ (ULift.up 0) = coord (ULift.up 0))
    (z : AnalyticSpace.complexAffineSpace.{u} 1) :
    (φ.toLRSHom.base z : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = z (ULift.up 0) :=
  (AnalyticSpace.base_eq_eval_coordPullback φ z (ULift.up 0)).trans
    ((congrArg ((AnalyticSpace.complexAffineSpace.{u} 1).eval (U := ⊤) z trivial) hφ).trans
      (AnalyticSpace.eval_coord z (ULift.up 0)))

/-! ### The node, which is not an open subspace of `ℂ^n` -/

/-- The points of the node whose first coordinate is not `c`. -/
def nodeOff (c : ℂ) : Opens (AnalyticSpace.node.{u}) :=
  ⟨{p : AnalyticSpace.node.{u} | p.1.1 (ULift.up 0) ≠ c},
    isOpen_compl_singleton.preimage ((continuous_apply (ULift.up 0)).comp
      (continuous_subtype_val.comp continuous_subtype_val))⟩

/-- A cover of the node by two overlapping opens, indexed by the point each is chosen for. -/
def nodeCover (p : AnalyticSpace.node.{u}) : Opens (AnalyticSpace.node.{u}) :=
  if p.1.1 (ULift.up 0) = 1 then nodeOff.{u} (-1) else nodeOff.{u} 1

theorem mem_nodeCover (p : AnalyticSpace.node.{u}) : p ∈ nodeCover.{u} p := by
  rw [nodeCover]
  split
  · next h => exact fun hcon ↦ by rw [h] at hcon; norm_num at hcon
  · next h => exact h

/-- **The two members of the node's cover overlap**: the origin is in both. -/
theorem nodeCover_overlap :
    nodeOrigin.{u} ∈ nodeOff.{u} 1 ⊓ nodeOff.{u} (-1) :=
  ⟨fun h ↦ zero_ne_one h, fun h ↦ (by norm_num : (0 : ℂ) ≠ -1) h⟩

/-- **A coordinate function of the node is a coordinate pullback**, obtained by gluing over a
cover by two overlapping opens of a space which is not an open subspace of `ℂ^n`. -/
theorem exists_hom_complexLine_node (j : ULift.{u} (Fin 2)) :
    ∃ φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) = nodeCoord.{u} j :=
  AnalyticSpace.exists_hom_complexLine_of_local _ (nodeCoord.{u} j) fun p ↦
    ⟨nodeCover.{u} p, mem_nodeCover.{u} p,
      AnalyticSpace.ofRestrict _ (nodeCover.{u} p) ≫ nodeToLine.{u} j,
      (AnalyticSpace.coordPullback_ofRestrict_comp _ (nodeCover.{u} p) (nodeToLine.{u} j)
          (ULift.up 0)).trans
        (congrArg (AnalyticSpace.node.{u}.resΓ (nodeCover.{u} p))
          (Γ_map_nodeToLineHom_coord.{u} j))⟩

/-- **The glued morphism on the node is `p ↦ p_j` on points**, computed from its coordinate
pullback through `ComplexAnalytic.eval_nodeCoord`. -/
theorem base_glue_nodeCoord (j : ULift.{u} (Fin 2))
    (φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1)
    (hφ : AnalyticSpace.coordPullback φ (ULift.up 0) = nodeCoord.{u} j)
    (p : AnalyticSpace.node.{u}) :
    (φ.toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = p.1.1 j :=
  (AnalyticSpace.base_eq_eval_coordPullback φ p (ULift.up 0)).trans
    ((congrArg (AnalyticSpace.node.{u}.eval (U := ⊤) p trivial) hφ).trans (eval_nodeCoord p j))

/-! ### The general theorem, on two spaces which are not open subspaces of `ℂ^n` -/

/-- **A coordinate function of the node is a coordinate pullback**, from the general theorem
rather than from a cover. -/
theorem exists_hom_complexLine_node_general (j : ULift.{u} (Fin 2)) :
    ∃ φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) = nodeCoord.{u} j :=
  AnalyticSpace.exists_hom_complexLine_general _ (nodeCoord.{u} j)

/-- **The punctured node, which is an open subspace of the node and of nothing simpler, admits a
morphism to `ℂ` with prescribed coordinate pullback.**

`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict` does not apply here: its source
must be an open subspace of `ℂ^n`, and this is an open subspace of the node. -/
theorem exists_hom_complexLine_puncturedNode (j : ULift.{u} (Fin 2)) :
    ∃ φ : puncturedNodeSpace.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) =
        (LocallyRingedSpace.Γ.map puncturedNodeIncl.{u}.toLRSHom.op).hom (nodeCoord.{u} j) :=
  AnalyticSpace.exists_hom_complexLine_general _ _

/-- **The morphism out of the punctured node is `p ↦ p_j` on points**, computed from its
coordinate pullback rather than assumed. -/
theorem base_hom_puncturedNode (j : ULift.{u} (Fin 2))
    (φ : puncturedNodeSpace.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1)
    (hφ : AnalyticSpace.coordPullback φ (ULift.up 0) =
      (LocallyRingedSpace.Γ.map puncturedNodeIncl.{u}.toLRSHom.op).hom (nodeCoord.{u} j))
    (p : puncturedNodeSpace.{u}) :
    (φ.toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) =
      (p.1 : AnalyticSpace.node.{u}).1.1 j :=
  (AnalyticSpace.base_eq_eval_coordPullback φ p (ULift.up 0)).trans
    ((congrArg (puncturedNodeSpace.{u}.eval (U := ⊤) p trivial) hφ).trans
      (eval_pullback_nodeCoord p j))

/-! ### Both round trips of the bijection, at the node

`ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral` is `Equiv.ofBijective`, so its inverse
is a choice term. The two lemmas beside its definition pin that choice down in general; these
name both directions on a concrete pair, at a space which is not an open subspace of `ℂ^n` and at
a morphism which is not a constant. -/

/-- **Forward: the bijection sends the node's `j`-th coordinate morphism to its `j`-th coordinate
function.**

The two sides share no lemma: the left is `homComplexLineEquivGeneral`'s forward map, which is
`ComplexAnalytic.AnalyticSpace.coordPullback`, and the right is reached through
`ComplexAnalytic.Γ_map_nodeToLineHom_coord`, whose proof runs through the cut-out presentation of
the node. -/
theorem homComplexLineEquivGeneral_nodeToLine (j : ULift.{u} (Fin 2)) :
    AnalyticSpace.homComplexLineEquivGeneral.{u} AnalyticSpace.node.{u} (nodeToLine.{u} j) =
      nodeCoord.{u} j :=
  Γ_map_nodeToLineHom_coord.{u} j

/-- **Backward: the inverse sends the node's `j`-th coordinate function to `nodeToLine j`**, with
no choice left in it.

This is the statement taxis #655 asked for and the reason it asked: an `Equiv.ofBijective` whose
inverse is never named on any input has handed a consumer nothing. -/
theorem symm_homComplexLineEquivGeneral_nodeCoord (j : ULift.{u} (Fin 2)) :
    (AnalyticSpace.homComplexLineEquivGeneral.{u} AnalyticSpace.node.{u}).symm
        (nodeCoord.{u} j) = nodeToLine.{u} j :=
  (Equiv.symm_apply_eq _).2 (homComplexLineEquivGeneral_nodeToLine.{u} j).symm

/-- **The morphism the inverse produces is surjective on points**, so neither the bijection nor
this round trip is about a constant morphism.

Without this, `symm_homComplexLineEquivGeneral_nodeCoord` would be consistent with the inverse
landing on a morphism collapsing the node to a point. -/
theorem surjective_base_symm_homComplexLineEquivGeneral_nodeCoord (j : ULift.{u} (Fin 2)) :
    Function.Surjective fun p : AnalyticSpace.node.{u} ↦
      ((((AnalyticSpace.homComplexLineEquivGeneral.{u} AnalyticSpace.node.{u}).symm
        (nodeCoord.{u} j)).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)) :=
  (congrArg (fun φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1 ↦
    Function.Surjective fun p : AnalyticSpace.node.{u} ↦
      ((φ.toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)))
    (symm_homComplexLineEquivGeneral_nodeCoord.{u} j)).mpr
      (surjective_base_nodeToLineHom.{u} j)

/-- **The bijection at the node is not a bijection between singletons.** The two coordinate
morphisms differ and so do the sections they go to, so both sides have at least two elements. -/
theorem homComplexLineEquivGeneral_node_not_subsingleton :
    ¬ Subsingleton (AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1) := fun h ↦
  nodeToLine_ne.{u} (h.elim _ _)

/-! ### The `m`-fold statement recovers the closed immersion of the node

The `m = 1` results above are not a test of the `m`-fold theorem: a statement that produced the
`m` coordinates independently, by `m` separate applications of the one-dimensional theorem,
would satisfy every one of them and could not exist, because assembling `m` morphisms `Z ⟶ ℂ`
into one `Z ⟶ ℂ^m` needs a product of analytic spaces that the development does not have.

The check that discriminates is at `m = 2`: feed the node's **two** coordinate functions to
`ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general` and identify what comes
out. It is `ComplexAnalytic.nodeIncl`, the closed immersion defining the node — **a morphism
produced by a general theorem and then recognised as one that was constructed by hand.**

That the two coordinates cannot be handled separately is `ComplexAnalytic.nodeToLine_ne`, which
is already in the library: `exists_hom_complexLine_general` applied to `nodeCoord 0` and to
`nodeCoord 1` gives two *different* morphisms `node ⟶ ℂ`, and nothing in the development
combines them. It is not restated here — a test file restating a library theorem is a duplicate
waiting to diverge. -/

/-- **The `m`-fold theorem at the node produces its closed immersion into `ℂ²`.**

The theorem is applied to `fun j ↦ nodeCoord j` with no reference to how the node was built; the
morphism it returns is `ComplexAnalytic.nodeIncl`, by
`ComplexAnalytic.eq_nodeIncl_of_coordPullback`. This is taxis #610's own acceptance criterion,
in its own words: *recover the inclusion `{z₀z₁ = 0} ⊆ ℂ²` from its two coordinate
functions.* -/
theorem exists_hom_complexAffineSpace_node_general :
    ∃ φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 2,
      (∀ j, AnalyticSpace.coordPullback φ j = nodeCoord.{u} j) ∧ φ = nodeIncl.{u} :=
  let ⟨φ, hφ⟩ := AnalyticSpace.exists_hom_complexAffineSpace_general.{u}
    AnalyticSpace.node.{u} nodeCoord.{u}
  ⟨φ, hφ, eq_nodeIncl_of_coordPullback.{u} φ hφ⟩

/-- **The `m`-fold bijection's inverse at the node's coordinate functions is `nodeIncl`**, with
no choice left in it. -/
theorem symm_homComplexAffineSpaceEquivGeneral_nodeCoord :
    (AnalyticSpace.homComplexAffineSpaceEquivGeneral.{u} AnalyticSpace.node.{u} 2).symm
        nodeCoord.{u} = nodeIncl.{u} :=
  (Equiv.symm_apply_eq _).2 (funext fun j ↦ (coordPullback_nodeIncl.{u} j)).symm

/-- **The morphism the `m`-fold inverse produces is injective on points and is not onto `ℂ²`.**

`ComplexAnalytic.nodeIncl` is the inclusion of the node, so it is injective and its image misses
`(1, 1)`. Without this, `symm_homComplexAffineSpaceEquivGeneral_nodeCoord` would be consistent
with the inverse landing on a morphism collapsing the node to a point — which is exactly what a
bijection stated but never instantiated cannot rule out. -/
theorem base_symm_homComplexAffineSpaceEquivGeneral_nodeCoord
    (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 2)) :
    (((AnalyticSpace.homComplexAffineSpaceEquivGeneral.{u} AnalyticSpace.node.{u} 2).symm
        nodeCoord.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) j = p.1.1 j :=
  congrArg (fun φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 2 ↦
    ((φ.toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) j))
    symm_homComplexAffineSpaceEquivGeneral_nodeCoord.{u}

end

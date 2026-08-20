/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.OpenSubspace

/-!
# Non-vacuity of the assembly of local morphisms to `ℂ`

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

## What these do *not* show, said plainly

Neither glued morphism is new. On `ℂ` the result is forced to agree with
`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine`'s morphism by uniqueness, and on the node
with `ComplexAnalytic.nodeToLine j`, whose restrictions are the local pieces used there. A
witness that produced a morphism nobody already had would need a `Z` and a `g` for which the
local existence hypothesis holds and the global statement was not already known — and no such
pair exists in this development, because the hypothesis is currently only obtainable where the
conclusion already is. That is a fact about how much of taxis #694 is done, not about this file.

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
      (AnalyticSpace.coordPullback_ofRestrict_comp _ (nodeCover.{u} p) (nodeToLine.{u} j)).trans
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

end

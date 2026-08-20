/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the morphisms built from holomorphic maps

`Oka/AnalyticSpace/HolomorphicMap.lean` turns a family of entire functions into a morphism of
complex analytic spaces. Every statement it proves would also hold if the construction produced
only identities and constants, and until it landed the development had no morphism of analytic
spaces other than identities, isomorphisms and the closed immersions defining local models. So
the checks that matter are that the morphisms produced are **named functions** which are visibly
neither constant nor the identity, and that the pullback map on global sections is not zero.

* `eq_sq_okaMapFun` names the underlying map of a morphism `ℂ ⟶ ℂ` on the nose: `z ↦ z²`. An
  analyticity-and-locality argument that silently produced a linear map would pass every other
  criterion here.
* `okaMap_sq_ne_id` turns that into the statement that the morphism of analytic spaces is not the
  identity, which is the specific degeneracy the construction could have.
* `eq_coord_base_nodeToLine` does the same for the node, whose ambient space it is *not*: the
  underlying map of `nodeToLine j` is `p ↦ p_j`, and `nodeToLine_ne` exhibits the two coordinate
  morphisms as different.
* `Γ_map_nodeToLine_ne_zero` is the check on the sheaf side rather than the space side: the
  pullback of the coordinate along `nodeToLine j` is a **nonzero** section of `𝒪_node`, so the
  morphism does not factor through a point.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-- The entire function `z ↦ z²` on `ℂ`, as a one-element family. -/
def sqFamily : ULift.{u} (Fin 1) → OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  fun _ ↦ coord (ULift.up 0) * coord (ULift.up 0)

/-- **The underlying map of the morphism attached to `sqFamily` is `z ↦ z²`**, named on the nose
rather than exhibited at two points. -/
theorem eq_sq_okaMapFun :
    okaMapFun sqFamily.{u} = fun z _ ↦ (z (ULift.up 0)) ^ 2 := by
  refine funext fun z ↦ funext fun l ↦ ?_
  rw [okaMapFun_apply, sqFamily, map_mul, evalHom_coord, sq]

/-- **The morphism of analytic spaces `ℂ ⟶ ℂ` attached to `z ↦ z²` is not the identity.**

This is the degeneracy `Oka/AnalyticSpace/HolomorphicMap.lean` has to rule out: a construction
which quietly forgot `u` and returned `𝟙` would satisfy every other statement in that file
except `Γ_map_okaMapHom_coord`. -/
theorem okaMap_sq_ne_id :
    AnalyticSpace.okaMap sqFamily.{u} ≠ 𝟙 (AnalyticSpace.complexAffineSpace.{u} 1) := by
  intro hcon
  have h := congrArg (fun φ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶
      AnalyticSpace.complexAffineSpace.{u} 1 ↦
    (φ.toLRSHom.base (fun _ ↦ (2 : ℂ)) : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)) hcon
  rw [show ((AnalyticSpace.okaMap sqFamily.{u}).toLRSHom.base
      (fun _ ↦ (2 : ℂ)) : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) =
    okaMapFun sqFamily.{u} (fun _ ↦ (2 : ℂ)) (ULift.up 0) from rfl, eq_sq_okaMapFun,
    show ((AnalyticSpace.Hom.toLRSHom
        (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1))).base
      (fun _ ↦ (2 : ℂ)) : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = 2 from rfl] at h
  norm_num at h

/-- **The `j`-th coordinate morphism out of the node has underlying map `p ↦ p_j`.**

The node is not `ℂ^n`, so this is the check that the construction survives composition with a
closed immersion. -/
theorem eq_coord_base_nodeToLine (j : ULift.{u} (Fin 2)) :
    (fun p : AnalyticSpace.node.{u} ↦
      ((nodeToLine.{u} j).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ)) =
        fun p _ ↦ p.1.1 j :=
  funext fun p ↦ funext fun l ↦ base_nodeToLineHom j p l

/-- **The two coordinate morphisms out of the node are different**, so `nodeToLine` is not a
constant construction. The point exhibited is `(1, 0)`, which lies on the node. -/
theorem nodeToLine_ne : nodeToLine.{u} (ULift.up 0) ≠ nodeToLine.{u} (ULift.up 1) := by
  classical
  have hne : (ULift.up 0 : ULift.{u} (Fin 2)) ≠ ULift.up 1 := fun hcon ↦ by
    simpa using congrArg ULift.down hcon
  set x : ULift.{u} (Fin 2) → ℂ := fun l ↦ if l = ULift.up 0 then 1 else 0 with hx
  have hx0 : x (ULift.up 0) * x (ULift.up 1) = 0 := by
    rw [hx]
    dsimp only
    rw [if_neg hne.symm, mul_zero]
  set p : AnalyticSpace.node.{u} :=
    ⟨⟨x, trivial⟩, (mem_zeroLocus_nodeSection_iff _).2 hx0⟩ with hp
  intro hcon
  have h := congrArg (fun φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1 ↦
    (φ.toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)) hcon
  rw [show ((nodeToLine.{u} (ULift.up 0)).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ)
      (ULift.up 0) = x (ULift.up 0) from base_nodeToLineHom _ p _,
    show ((nodeToLine.{u} (ULift.up 1)).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ)
      (ULift.up 0) = x (ULift.up 1) from base_nodeToLineHom _ p _, hx] at h
  dsimp only at h
  rw [if_pos rfl, if_neg hne.symm] at h
  exact one_ne_zero h

/-- **The pullback of the coordinate along `nodeToLine j` is a nonzero section of `𝒪_node`.**

The check on the sheaf side: a morphism to `ℂ` which factored through a point would pull the
coordinate back to a constant, and this one pulls it back to `nodeCoord j`, which is not zero
(`ComplexAnalytic.nodeCoord_ne_zero`) while the product of the two is
(`ComplexAnalytic.nodeCoord_mul`). -/
theorem Γ_map_nodeToLine_ne_zero (j : ULift.{u} (Fin 2)) :
    (LocallyRingedSpace.Γ.map (nodeToLine.{u} j).toLRSHom.op).hom (coord (ULift.up 0)) ≠ 0 :=
  (Γ_map_nodeToLineHom_coord j).symm ▸ nodeCoord_ne_zero j

/-- **Every global section of `𝒪_{ℂ^n}` really is recovered**, on a concrete section which is not
a constant: the pullback of the coordinate along the morphism attached to `sqFamily` is `z ↦ z²`
again. -/
theorem Γ_map_okaMap_sqFamily :
    (LocallyRingedSpace.Γ.map (AnalyticSpace.okaMap sqFamily.{u}).toLRSHom.op).hom
        (coord (ULift.up 0)) =
      coord (ULift.up 0) * coord (ULift.up 0) :=
  Γ_map_okaMapHom_coord sqFamily.{u} (ULift.up 0)

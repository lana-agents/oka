/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the continuity of evaluation

`ComplexAnalytic.AnalyticSpace.continuous_eval` says that the value of a section of `𝒪_Z` is a
continuous function on its domain. A continuity statement is empty if the functions it is about
are all constant, and constant functions are continuous for reasons that have nothing to do with
this file's argument. So the check that matters is a **non-constant** example on a space which is
not `ℂ^n`.

The node `{z ∈ ℂ² | z₀ z₁ = 0}` supplies one: `lemma continuous_eval_nodeCoord` below is the
continuity of the coordinate function `z_j` restricted to the node, and
`eq_coord_nodeCoord` identifies that function with `p ↦ p_j` on the nose, so it is visibly
non-constant — `ne_of_eval_nodeCoord` exhibits two points of the node with different values.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-- **The value of a coordinate function on the node is continuous.** The node is a complex
analytic space which is not a manifold, and `nodeCoord j` is a section of its structure sheaf
which is not in the image of the constants. -/
theorem continuous_eval_nodeCoord (j : ULift.{u} (Fin 2)) :
    Continuous fun p : AnalyticSpace.node.{u} ↦
      (AnalyticSpace.node.{u}).eval (U := ⊤) p trivial (nodeCoord.{u} j) :=
  (AnalyticSpace.node.{u}).continuous_eval_top _

/-- The continuous function of `continuous_eval_nodeCoord` is the `j`-th coordinate, so the
statement is about a function that is manifestly not constant. -/
theorem eq_coord_nodeCoord (j : ULift.{u} (Fin 2)) :
    (fun p : AnalyticSpace.node.{u} ↦
      (AnalyticSpace.node.{u}).eval (U := ⊤) p trivial (nodeCoord.{u} j)) =
        fun p ↦ p.1.1 j :=
  funext fun p ↦ eval_nodeCoord p j

/-- Two points of the node at which the coordinate function `z₀` takes different values: the
origin and `(1, 0)`. -/
theorem ne_of_eval_nodeCoord :
    ∃ p q : AnalyticSpace.node.{u},
      (AnalyticSpace.node.{u}).eval (U := ⊤) p trivial (nodeCoord.{u} (ULift.up 0)) ≠
        (AnalyticSpace.node.{u}).eval (U := ⊤) q trivial (nodeCoord.{u} (ULift.up 0)) := by
  classical
  have hne : (ULift.up 0 : ULift.{u} (Fin 2)) ≠ ULift.up 1 := fun hcon ↦ by
    simpa using congrArg ULift.down hcon
  refine ⟨⟨⟨fun _ ↦ 0, trivial⟩, (mem_zeroLocus_nodeSection_iff _).2 (by simp)⟩,
    ⟨⟨fun l ↦ if l = ULift.up 0 then 1 else 0, trivial⟩,
      (mem_zeroLocus_nodeSection_iff _).2 ?_⟩, ?_⟩
  · dsimp only
    rw [if_neg hne.symm, mul_zero]
  · rw [eval_nodeCoord, eval_nodeCoord]
    simp

end

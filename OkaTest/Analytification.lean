/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# The analytification of `ℂ[x, y]/(xy)` is the node

`Oka/Analytification/Presentation.lean` builds, from a tuple of polynomials, an analytic space
and a comparison morphism to `Spec` of the quotient algebra. Every statement there is general in
the tuple, so on its own it says nothing about any particular space; this file instantiates it
at the one presentation the development already has a name for.

Three things are checked, and they fail in different ways.

* **The construction reproduces the node, definitionally.** `ComplexAnalytic.analytification_nodeG`
  is a `rfl`, which is the strongest available statement that the general definition has not
  drifted from `ComplexAnalytic.AnalyticSpace.node`, on which everything else in the
  development is built.
* **The description of the points is right**, checked against
  `ComplexAnalytic.mem_zeroLocus_nodeSection_iff`, which reaches the same set through
  `ComplexAnalytic.nodeSection` and shares only `mem_zeroLocus_restrict_complexSpace_iff` with
  the general proof. And the description is not vacuous in either direction: the origin and
  `(1, 0)` lie on the node and `(1, 1)` does not.
* **The comparison morphism is not constant and has not swapped the two coordinates.** This is
  the check the other two cannot make. At the origin the prime underneath contains both
  coordinates; at `(1, 0)` it contains `y` and **not** `x`. A morphism that collapsed the node
  to a point, or that read the coordinates in the wrong order, satisfies everything above and
  fails `ComplexAnalytic.notMem_analytificationToSpec_base_asIdeal_nodePtX_X0`.

The images of the two points are then distinct — proved from the coordinate computation rather
than from `ComplexAnalytic.analytificationToSpec_base_injective`, so that the two are
independent checks on each other.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The presentation `ℂ[x, y] / (xy)` -/

/-- The one-element tuple of polynomials presenting the node: `x y`. -/
def nodeG : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ := fun _ ↦ nodePoly.{u}

/-- The ideal `nodeG` generates is `(xy)`, so the algebra being analytified is
`ℂ[x, y]/(xy)`. -/
theorem presentationIdeal_nodeG :
    presentationIdeal nodeG.{u} = Ideal.span {nodePoly.{u}} :=
  congrArg Ideal.span (Set.range_const (ι := Fin 1) (c := nodePoly.{u}))

/-- **The analytification of `ℂ[x, y]/(xy)` is the node**, definitionally.

This is the check that `ComplexAnalytic.AnalyticSpace.analytification` agrees with the
construction the rest of the development is built on. That it is a `rfl` is the point: nothing
had to be transported, so the two definitions are the same definition. -/
theorem analytification_nodeG :
    AnalyticSpace.analytification nodeG.{u} = AnalyticSpace.node.{u} :=
  rfl

/-! ### The points -/

/-- The point `(1, 0)` of `ℂ²`, which lies on the node but is not the origin. -/
def nodePtX : ULift.{u} (Fin 2) → ℂ := fun i ↦ if i.down = 0 then 1 else 0

@[simp] theorem nodePtX_zero : nodePtX.{u} (ULift.up 0) = 1 := rfl

@[simp] theorem nodePtX_one : nodePtX.{u} (ULift.up 1) = 0 := rfl

/-- **The general description of the points reproves the node's.**

`ComplexAnalytic.mem_zeroLocus_nodeSection_iff` reaches the same set through
`ComplexAnalytic.nodeSection`; the two proofs share only
`mem_zeroLocus_restrict_complexSpace_iff`, so an error in either is visible here. -/
theorem forall_eval_nodeG_iff (y : complexAffineSpaceTop.{u} 2) :
    (∀ j, MvPolynomial.eval (y.1 : ULift.{u} (Fin 2) → ℂ) (nodeG.{u} j) = 0) ↔
      y.1 (ULift.up 0) * y.1 (ULift.up 1) = 0 :=
  (mem_zeroLocus_polySection_iff nodeG.{u} y).symm.trans (mem_zeroLocus_nodeSection_iff.{u} y)

/-- The points of the analytification of `ℂ[x, y]/(xy)`, spelled as the union of the two
coordinate axes. -/
theorem mem_zeroLocus_polySection_nodeG_iff (y : complexAffineSpaceTop.{u} 2) :
    y ∈ (complexAffineSpaceTop.{u} 2).zeroLocus (polySection nodeG.{u}) ↔
      y.1 (ULift.up 0) * y.1 (ULift.up 1) = 0 :=
  (mem_zeroLocus_polySection_iff nodeG.{u} y).trans (forall_eval_nodeG_iff.{u} y)

/-- The origin lies on the analytification. -/
theorem origin_mem_zeroLocus_polySection_nodeG :
    (⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩ : complexAffineSpaceTop.{u} 2) ∈
      (complexAffineSpaceTop.{u} 2).zeroLocus (polySection nodeG.{u}) :=
  (mem_zeroLocus_polySection_nodeG_iff _).2 (by simp)

/-- The point `(1, 0)` lies on the analytification. -/
theorem nodePtX_mem_zeroLocus_polySection_nodeG :
    (⟨nodePtX.{u}, trivial⟩ : complexAffineSpaceTop.{u} 2) ∈
      (complexAffineSpaceTop.{u} 2).zeroLocus (polySection nodeG.{u}) :=
  (mem_zeroLocus_polySection_nodeG_iff _).2 (by simp)

/-- **The analytification is not all of `ℂ²`**: `(1, 1)` does not lie on it. Without this the
description of the points would be consistent with the zero locus being everything. -/
theorem notMem_zeroLocus_polySection_nodeG_one :
    (⟨(1 : ULift.{u} (Fin 2) → ℂ), trivial⟩ : complexAffineSpaceTop.{u} 2) ∉
      (complexAffineSpaceTop.{u} 2).zeroLocus (polySection nodeG.{u}) := fun h ↦ by
  simpa using (mem_zeroLocus_polySection_nodeG_iff.{u} _).1 h

/-- The origin, as a point of the analytification of `ℂ[x, y]/(xy)`. -/
def originNode : AnalyticSpace.analytification nodeG.{u} :=
  ⟨⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩, origin_mem_zeroLocus_polySection_nodeG.{u}⟩

/-- The point `(1, 0)`, as a point of the analytification of `ℂ[x, y]/(xy)`. -/
def ptXNode : AnalyticSpace.analytification nodeG.{u} :=
  ⟨⟨nodePtX.{u}, trivial⟩, nodePtX_mem_zeroLocus_polySection_nodeG.{u}⟩

theorem originNode_ne_ptXNode : originNode.{u} ≠ ptXNode.{u} := by
  intro h
  have : (0 : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) = nodePtX.{u} (ULift.up 0) :=
    congrArg (fun y : AnalyticSpace.analytification nodeG.{u} ↦
      (y.1.1 : ULift.{u} (Fin 2) → ℂ) (ULift.up 0)) h
  simp at this

/-! ### The comparison morphism is the classical one

The three statements below are what a comparison morphism that was constant, or that read the
coordinates in the wrong order, would fail. -/

/-- At the origin, the prime of `Spec (ℂ[x, y]/(xy))` underneath contains `x`. -/
theorem mem_analytificationToSpec_base_asIdeal_origin_X0 :
    Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 0)) ∈
      ((analytificationToSpec nodeG.{u}).base originNode.{u}).asIdeal :=
  (mem_analytificationToSpec_base_asIdeal_iff nodeG.{u} originNode.{u} _).2 (by simp [originNode])

/-- At the origin, the prime of `Spec (ℂ[x, y]/(xy))` underneath contains `y`. -/
theorem mem_analytificationToSpec_base_asIdeal_origin_X1 :
    Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 1)) ∈
      ((analytificationToSpec nodeG.{u}).base originNode.{u}).asIdeal :=
  (mem_analytificationToSpec_base_asIdeal_iff nodeG.{u} originNode.{u} _).2 (by simp [originNode])

/-- At `(1, 0)`, the prime underneath contains `y`. -/
theorem mem_analytificationToSpec_base_asIdeal_nodePtX_X1 :
    Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 1)) ∈
      ((analytificationToSpec nodeG.{u}).base ptXNode.{u}).asIdeal :=
  (mem_analytificationToSpec_base_asIdeal_iff nodeG.{u} ptXNode.{u} _).2 (by simp [ptXNode])

/-- **At `(1, 0)`, the prime underneath does not contain `x`.**

This is the statement that fails for a comparison morphism which is constant on points, and the
one that fails if the two coordinates have been exchanged. -/
theorem notMem_analytificationToSpec_base_asIdeal_nodePtX_X0 :
    Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 0)) ∉
      ((analytificationToSpec nodeG.{u}).base ptXNode.{u}).asIdeal := by
  rw [mem_analytificationToSpec_base_asIdeal_iff]
  simp [ptXNode]

/-- **The two points have distinct images**, so the comparison morphism does not collapse the
node.

Proved from the coordinate computations above rather than from
`ComplexAnalytic.analytificationToSpec_base_injective`, so that the general injectivity
statement and this instance are independent of each other. -/
theorem analytificationToSpec_base_origin_ne_ptX :
    (analytificationToSpec nodeG.{u}).base originNode.{u} ≠
      (analytificationToSpec nodeG.{u}).base ptXNode.{u} := fun h ↦
  notMem_analytificationToSpec_base_asIdeal_nodePtX_X0.{u}
    (h ▸ mem_analytificationToSpec_base_asIdeal_origin_X0.{u})

end

end ComplexAnalytic

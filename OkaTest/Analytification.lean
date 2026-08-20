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

Four things are checked, and they fail in different ways.

* **The construction reproduces the node, definitionally.** `ComplexAnalytic.analytification_nodeG`
  is a `rfl`, which is the strongest available statement that the general definition has not
  drifted from `ComplexAnalytic.AnalyticSpace.node`, on which everything else in the
  development is built.
* **The description of the points is right**, checked against
  `ComplexAnalytic.mem_zeroLocus_nodeSection_iff`, which reaches the same set through
  `ComplexAnalytic.nodeSection`. The two proofs share `mem_zeroLocus_restrict_complexSpace_iff`
  **and** `OkaRing.evalHom_ofMvPolynomial`, so this is not an independent computation of the
  set; what it does catch is a mismatch in the `Fin 1` quantification or a `nodeG` that is not
  `X₀ X₁`, which is what a general statement instantiated at a named special case is for. And
  the description is not vacuous in either direction: the origin and `(1, 0)` lie on the node
  and `(1, 1)` does not.
* **The comparison morphism is not constant and has not swapped the two coordinates.** This is
  the check the other two cannot make. At the origin the prime underneath contains both
  coordinates; at `(1, 0)` it contains `y` and **not** `x`. A morphism that collapsed the node
  to a point, or that read the coordinates in the wrong order, satisfies everything above and
  fails `ComplexAnalytic.notMem_analytificationToSpec_base_asIdeal_nodePtX_X0`.

* **The compatibility square is load-bearing rather than decorative.**
  `ComplexAnalytic.analytificationToSpec_comp_specMk` had no consumer anywhere; on this project
  a theorem with no consumer has three times turned out to be unusable rather than merely
  unused. `ComplexAnalytic.mem_base_asIdeal_via_square` and
  `ComplexAnalytic.mem_and_notMem_base_asIdeal_ptXNode` use it, in opposite directions, and the
  second computes one prime by two routes that share none of their named intermediates. See
  that section's own docstring for exactly how far the independence goes — it is not all the
  way down and the docstring says so.

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
`ComplexAnalytic.nodeSection`. The two proofs are not independent — both go through
`mem_zeroLocus_restrict_complexSpace_iff` and `OkaRing.evalHom_ofMvPolynomial` — so what this
catches is a mismatch between the general statement and the special one, not an error in the
lemmas they share. For a genuinely independent computation of a point of `X^an` see
`ComplexAnalytic.mem_base_asIdeal_ptXNode_iff` below. -/
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

/-! ### The compatibility square, used

`ComplexAnalytic.analytificationToSpec_comp_specMk` says the comparison morphism of `X^an` is
the restriction of the comparison morphism of `ℂ^n`. Stated and never applied it is decoration;
the two theorems below apply it, in opposite directions.

**What that buys, stated exactly.** `ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff`
is proved through `ComplexAnalytic.AnalyticSpace.mem_toΓSpec_base_asIdeal_iff` and
`ComplexAnalytic.eval_polyToGlobal`; the route here goes through functoriality of `Spec`,
`AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality` and
`mem_complexSpaceToSpec_base_asIdeal_iff` in `Oka/Analytification/AffineSpace.lean`. **Those
named intermediates are disjoint. The two are not independent all the way down** — both end at
`AlgebraicGeometry.LocallyRingedSpace.notMem_prime_iff_unit_in_stalk` and at the fact that a
germ of a holomorphic function is a unit exactly when its value is nonzero, which is where any
description of a prime of `Spec Γ` has to end. What a disagreement between them would catch is
an error in the square, in `analytificationToSpec`, or in either point description — which is
the whole of what is new here — and not an error in the shared foundation. -/

/-- **The map on points of `analytificationToSpec`, derived from the compatibility square
instead.**

This is `ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff` again, for an arbitrary
tuple of polynomials, reached by pushing the point down into `Spec ℂ[x]` along the square and
reading it off with `mem_complexSpaceToSpec_base_asIdeal_iff`. The two agree. -/
theorem mem_base_asIdeal_via_square {n k : ℕ}
    (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (y : AnalyticSpace.analytification.{u} g) (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    Ideal.Quotient.mk (presentationIdeal g) p ∈
        ((analytificationToSpec g).base y).asIdeal ↔
      MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) p = 0 := by
  have hsq := congrArg (fun m : (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) ℂ)) ↦
    (m.base y).asIdeal) (analytificationToSpec_comp_specMk g)
  refine Iff.trans ?_ (mem_complexSpaceToSpec_base_asIdeal_iff
    (ι := ULift.{u} (Fin n)) (y.1.1 : ULift.{u} (Fin n) → ℂ) p)
  exact Iff.of_eq (congrArg (fun I ↦ p ∈ I) hsq)

/-- **The prime of `Spec ℂ[x, y]` underneath a point of the node, computed through the square.**

The same equivalence read the other way: this one is about the image of `y` in `Spec ℂ[x, y]`
rather than in `Spec (ℂ[x, y]/(xy))`, and it is proved from
`ComplexAnalytic.analytificationToSpec_comp_specMk` together with
`ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff`. -/
theorem mem_base_asIdeal_ptXNode_iff (p : MvPolynomial (ULift.{u} (Fin 2)) ℂ) :
    p ∈ ((complexSpaceToSpec (ULift.{u} (Fin 2))).base
        ((analytificationIncl nodeG.{u}).base ptXNode.{u})).asIdeal ↔
      MvPolynomial.eval (nodePtX.{u}) p = 0 := by
  have hsq := congrArg (fun m : (AnalyticSpace.analytification.{u} nodeG.{u}).toLocallyRingedSpace ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) ℂ)) ↦
    (m.base ptXNode.{u}).asIdeal) (analytificationToSpec_comp_specMk nodeG.{u})
  rw [show ((complexSpaceToSpec (ULift.{u} (Fin 2))).base
      ((analytificationIncl nodeG.{u}).base ptXNode.{u})).asIdeal = _ from hsq.symm]
  exact mem_analytificationToSpec_base_asIdeal_iff nodeG.{u} ptXNode.{u} p

/-- **One number, two routes, and they meet.**

The positive half is computed through the compatibility square and
`ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff`; the negative half through
`mem_complexSpaceToSpec_base_asIdeal_iff` directly, touching nothing in
`Oka/Analytification/Presentation.lean` at all. Because the two halves are about the *same*
prime, this is a single statement that fails if the routes disagree, rather than two separate
proofs of one theorem placed side by side. See the section docstring for how far the
independence goes.

The number is the one that discriminates: at `(1, 0)` the prime of `Spec ℂ[x, y]` underneath
contains `y` and does not contain `x`. -/
theorem mem_and_notMem_base_asIdeal_ptXNode :
    MvPolynomial.X (ULift.up 1) ∈ ((complexSpaceToSpec (ULift.{u} (Fin 2))).base
        ((analytificationIncl nodeG.{u}).base ptXNode.{u})).asIdeal ∧
      MvPolynomial.X (ULift.up 0) ∉ ((complexSpaceToSpec (ULift.{u} (Fin 2))).base
        ((analytificationIncl nodeG.{u}).base ptXNode.{u})).asIdeal := by
  refine ⟨(mem_base_asIdeal_ptXNode_iff.{u} _).2 (by simp), fun h ↦ ?_⟩
  -- The other route: `complexSpaceToSpec`'s own description of the prime underneath a point.
  simpa using (mem_complexSpaceToSpec_base_asIdeal_iff (nodePtX.{u})
    (MvPolynomial.X (ULift.up 0))).1 h

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

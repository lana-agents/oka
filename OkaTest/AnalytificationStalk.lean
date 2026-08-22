/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.PresentationStalk
import OkaTest.Analytification

/-!
# Non-vacuity of the stalk map of `X^an ⟶ Spec (ℂ[x] ⧸ I)`

`Oka/Analytification/PresentationStalk.lean` identifies the stalk of `Spec (ℂ[x] ⧸ I)` under a
point of `X^an` as a localisation, and the stalk map as the lift of
`ComplexAnalytic.quotientToGerm`. Two things could make that a restatement of the ambient case
`Oka/Analytification/AffineSpace.lean` already had, and this file rules out both, at the node
`ℂ[x, y] ⧸ (x y)` — the presentation whose ideal is not zero and whose space is not smooth.

* **The criterion for a germ to be invertible could have been constantly true or constantly
  false.** It is neither, and the *point* is what decides: the class of `x` has a non-invertible
  germ at the origin and an invertible one at `(1, 0)`. Both are points of the same space and
  both computations run through `ComplexAnalytic.isUnit_quotientToGerm_iff`, so this is the
  statement that the identification sees the point.
* **The ideal could have been zero**, in which case everything here would be the ambient case in
  disguise. `ComplexAnalytic.quotientToGerm_ptXNode_X1_eq_zero`: **the germ of `y` at `(1, 0)` on
  the node is zero**, because near that point the node is the `x`-axis and the other branch is
  invisible. On `ℂ²` that germ is not zero, so this is a statement the ambient case cannot make.

The second is deduced from the first together with `x y = 0` in `ℂ[x, y] ⧸ (x y)`, which is the
right shape: the witness is a *consequence* of the ideal being nonzero rather than an extra
analytic input.

**What is still not tested here**, and is worth saying rather than leaving to be discovered:
that the germs of `x` and `y` at the *origin* are both nonzero — so that the node's stalk there
is not a domain. That is a statement about the target stalk `𝒪_{X^an, y}` and needs its
identification with the germ ring modulo `I`, which is the outstanding half; see
`Oka/Analytification/PresentationStalk.lean`'s `## What is not here`.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic

noncomputable section

/-- The class of `x y` is zero in `ℂ[x, y] ⧸ (x y)`. -/
theorem mk_nodePoly_eq_zero_nodeG :
    Ideal.Quotient.mk (presentationIdeal nodeG.{u}) nodePoly.{u} = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩)

/-- **At the origin the class of `x` has no invertible germ**: it vanishes there. -/
theorem not_isUnit_quotientToGerm_origin_X0 :
    ¬ IsUnit (quotientToGerm nodeG.{u} originNode.{u}
      (Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 0)))) :=
  fun h ↦ (isUnit_quotientToGerm_iff nodeG.{u} originNode.{u} _).1 h
    mem_analytificationToSpec_base_asIdeal_origin_X0.{u}

/-- **At `(1, 0)` the class of `x` does have an invertible germ.**

Together with the previous statement this rules out a criterion that is constantly true or
constantly false: the same class, on the same space, at two different points. -/
theorem isUnit_quotientToGerm_ptXNode_X0 :
    IsUnit (quotientToGerm nodeG.{u} ptXNode.{u}
      (Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 0)))) :=
  (isUnit_quotientToGerm_iff nodeG.{u} ptXNode.{u} _).2
    notMem_analytificationToSpec_base_asIdeal_nodePtX_X0.{u}

/-- **The germ of `y` at `(1, 0)` on the node is zero** — the branch `x = 0` is invisible from a
point of the other branch, because near `(1, 0)` the node *is* the `x`-axis.

This is the statement that rules out the identification being a restatement of the ambient case:
on `ℂ²` the germ of `y` at `(1, 0)` is very far from zero. It is forced by two facts this file
has already established at that point — `x y` is zero in `ℂ[x, y] ⧸ (x y)` and the germ of `x`
is a unit there — so it is a consequence of the ideal being nonzero rather than an extra input,
which is exactly what makes it the right witness. -/
theorem quotientToGerm_ptXNode_X1_eq_zero :
    quotientToGerm nodeG.{u} ptXNode.{u}
        (Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 1))) = 0 := by
  obtain ⟨v, hv⟩ := isUnit_quotientToGerm_ptXNode_X0.{u}
  have hprod : quotientToGerm nodeG.{u} ptXNode.{u}
      (Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 0))) *
      quotientToGerm nodeG.{u} ptXNode.{u}
        (Ideal.Quotient.mk (presentationIdeal nodeG.{u}) (MvPolynomial.X (ULift.up 1))) = 0 := by
    rw [← map_mul, ← map_mul, ← nodePoly, mk_nodePoly_eq_zero_nodeG, map_zero]
  exact (IsUnit.mul_right_eq_zero ⟨v, hv⟩).1 hprod

/-- **The stalk map computes**: on the image of `ComplexAnalytic.PresentedAlgebra` it is
`ComplexAnalytic.quotientToGerm`, at an honest point of an honest node.

Without an instance of it, `ComplexAnalytic.stalkMap_analytificationToSpec_eq_lift` would be a
statement one could not evaluate anywhere. -/
theorem stalkMap_analytificationToSpec_algebraMap_origin
    (a : PresentedAlgebra.{u} 2 1 nodeG.{u}) :
    ((analytificationToSpec nodeG.{u}).stalkMap originNode.{u}).hom
        (algebraMap (PresentedAlgebra.{u} 2 1 nodeG.{u})
          (analytificationToSpecStalk nodeG.{u} originNode.{u}) a) =
      quotientToGerm nodeG.{u} originNode.{u} a := by
  rw [stalkMap_analytificationToSpec_eq_lift, IsLocalization.lift_eq]

end

end ComplexAnalytic

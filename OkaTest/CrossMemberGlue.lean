/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.LocalisationIndependence

/-!
# Non-vacuity of the cross-member glue

`ComplexAnalytic.refineCrossGlue` takes two members, an isomorphism of their original overlap, two
refining polynomials, two extra factors, an intermediate polynomial and a unit. All of that could
be jointly unsatisfiable at anything interesting, and then the file that declares it says nothing.
The reading that would empty it is the one that empties every statement of this shape: that its
only instances are at one member and at `AlgEquiv.refl`, where it identifies an object with itself.

The witness below is at the node presented **twice**, which is the fixture
`OkaTest/LocalisationIndependence.lean` built for the transport it is made of: `nodeTuple2` in two
variables and `nodeTuple3` in three, which `nodePres2_ne_nodePres3` separates by their variable
counts. Both members are refined by `D(z₀)`, and `D(z₀)` is also the original overlap, so the two
refined overlaps are the two localisations `nodeLocPresIso` identifies.

* **The isomorphism of the original overlap is reached the way a cover datum's consumer reaches
  it** — `crossE` is `ComplexAnalytic.Presentation.algEquivOfIso` of an isomorphism of
  presentations, not an algebra isomorphism supplied by hand. `crossE_eq` says that this lands on
  the nose on the transported equivalence, by `rfl`; that composite is what
  `ComplexAnalytic.Presentation.isoOfAlgEquiv_algEquivOfIso` was stated for.
* **The unit is not `1`, and that is a theorem here and not a remark.** On the second side the
  refined overlap is cut out by `z₀ · z₀` where the crossing produces `z₀`, and the two differ by
  the class of `z₀` read upstairs, which is a unit for the reason
  `ComplexAnalytic.isUnit_mk_rename_localisationIncl` gives — the polynomial one inverts is
  invertible upstairs. `crossU_ne_one` separates it from `1`, by evaluating at `crossPoint`,
  a point of that analytification where `z₀` takes the value `2`. So `crossHu` is an instance of
  the hypothesis with content and not of `x = 1 * x`.
* **And the two objects glued are not equal** — `nodeCrossGlue_ne` — so the isomorphism is not an
  identity in disguise and `Iso.refl` does not typecheck at that type. The same separator
  `localisationPresentation_node_ne` uses one level down: the variable counts differ.

## What this does not witness

**The extra factor on the first side is `1`.** `q = 1` there, so that side's refined overlap is
its whole refined member; the configuration exercised is the one where a refined member sits
inside the original overlap, which is the case a cover refinement meets when the refining open is
already contained in the overlap. A witness where both extra factors are proper is a larger
fixture — it needs two members whose overlap is a proper open of each — and nothing here claims
to be it.

**Nothing here is a cover datum.** There is no `σ`, no family, no `hsymm`, `hrange` or
`hcocycle`; this is one ordered pair, which is the unit
`ComplexAnalytic.refineCrossGlue` is stated at.
-/

open CategoryTheory MvPolynomial ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.CrossMemberGlue

open OkaTest.LocalisationIndependence

/-- **The isomorphism of the two original overlaps, as a consumer of a cover datum holds it.**

A cover datum's `glue` field is an isomorphism of `ComplexAnalytic.Presentation`, and
`ComplexAnalytic.refineCrossGlue` asks for an isomorphism of the presented algebras;
`ComplexAnalytic.Presentation.algEquivOfIso` is the way across and the `symm` is the direction
convention, since a `ComplexAnalytic.PresHom` carries its ring map backwards. -/
def crossE : PresentedAlgebra.{u} (2 + 1) (1 + 1)
      (localisationPresentation.{u} nodeTuple2.{u} (MvPolynomial.X (ULift.up 0))) ≃ₐ[ℂ]
    PresentedAlgebra.{u} (3 + 1) (2 + 1)
      (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))) :=
  (Presentation.algEquivOfIso.{u} nodeLocPresIso.{u}).symm

/-- **The consumer path lands on the transported equivalence on the nose.**

`nodeLocPresIso` is `ComplexAnalytic.localisationPresentationIsoOfAlgEquiv`, which is
`ComplexAnalytic.Presentation.isoOfAlgEquiv` of the transported equivalence; going back with
`ComplexAnalytic.Presentation.algEquivOfIso` returns it, which is
`ComplexAnalytic.Presentation.algEquivOfIso_isoOfAlgEquiv`. That both round trips are `rfl` is
what makes this `rfl` rather than a rewrite, and it is why the hypothesis below can be proved
about the transport rather than about an opaque composite. -/
theorem crossE_eq : crossE.{u} =
    localisationPresentedAlgebraEquivOfAlgEquiv.{u} nodeTuple2.{u} _ _
      (Presentation.algEquivOfIso.{u} nodePresIso.{u}).symm
      algEquivOfIso_nodePresIso_symm_mk_X0.{u} :=
  rfl

/-- **The class of `z₀` upstairs crosses to the class of `z₀` upstairs**, which is the hypothesis
`ComplexAnalytic.refineCrossGlue` needs on the first side.

`ComplexAnalytic.localisationRingHom_mk` reads the renamed polynomial as the structure map applied
to the class, `ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom`
moves the structure map across, and `algEquivOfIso_nodePresIso_symm_mk_X0` is what the isomorphism
of the *members* does to that class. The last step is a `congrArg` rather than a `rw` because the
implicit presentation of the target arrives spelled through `nodePres3`'s projections. -/
theorem crossHe :
    crossE.{u} (Ideal.Quotient.mk
        (presentationIdeal.{u}
          (localisationPresentation.{u} nodeTuple2.{u} (MvPolynomial.X (ULift.up 0))))
        (MvPolynomial.rename (localisationIncl.{u} 2)
          (1 * MvPolynomial.X (ULift.up 0)))) =
      Ideal.Quotient.mk
        (presentationIdeal.{u}
          (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))))
        (MvPolynomial.rename (localisationIncl.{u} 3) (MvPolynomial.X (ULift.up 0))) := by
  rw [one_mul, ← localisationRingHom_mk]
  change localisationPresentedAlgebraEquivOfAlgEquiv.{u} nodeTuple2.{u} _ _
    (Presentation.algEquivOfIso.{u} nodePresIso.{u}).symm
    algEquivOfIso_nodePresIso_symm_mk_X0.{u} (localisationRingHom.{u} nodeTuple2.{u} _ _) = _
  rw [localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom]
  exact congrArg (localisationRingHom.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0)))
    algEquivOfIso_nodePresIso_symm_mk_X0.{u}

/-- **The unit the second side corrects by**: the class of `z₀` read upstairs, which is invertible
because inverting `z₀` is what the localisation does. -/
def crossU : (PresentedAlgebra.{u} (3 + 1) (2 + 1)
    (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))))ˣ :=
  (isUnit_mk_rename_localisationIncl.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))).unit

/-- **The second side's cutting polynomial is a unit multiple of the one the crossing produces**,
and the unit is not `1`.

The crossing lands at `z₀` and the second refined overlap is cut out by `z₀ · z₀`; the difference
is one factor of `z₀`, which `crossU` is. This is the instance of
`ComplexAnalytic.localisationPresentationIsoOfUnitMul`'s hypothesis that
`ComplexAnalytic.refineCrossGlue` consumes. -/
theorem crossHu :
    Ideal.Quotient.mk
        (presentationIdeal.{u}
          (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))))
        (MvPolynomial.rename (localisationIncl.{u} 3)
          (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 0))) =
      (crossU.{u} : PresentedAlgebra.{u} (3 + 1) (2 + 1)
          (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0)))) *
        Ideal.Quotient.mk
          (presentationIdeal.{u}
            (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))))
          (MvPolynomial.rename (localisationIncl.{u} 3) (MvPolynomial.X (ULift.up 0))) := by
  change _ = ((isUnit_mk_rename_localisationIncl.{u} nodeTuple3.{u}
    (MvPolynomial.X (ULift.up 0))).unit : PresentedAlgebra.{u} (3 + 1) (2 + 1)
      (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0)))) * _
  rw [IsUnit.unit_spec, map_mul, map_mul]

/-- **A point of the analytification of the node in three variables localised at `z₀`**, where
`z₀` does not take the value `1`: `(2, 0, 0, 1/2)`.

The three relations vanish on it — `z₀z₁ = 2·0`, `z₂ = 0`, and `t·z₀ - 1 = ½·2 - 1` — which is
what makes evaluation at it a ring map killing the ideal, and `z₀` takes the value `2`, which is
what separates `crossU` from `1` below. -/
def crossPoint : ULift.{u} (Fin (3 + 1)) → ℂ :=
  fun i ↦ ![2, 0, 0, 1 / 2] i.down

/-- **Every relation of that localised presentation vanishes at `crossPoint`.** -/
theorem eval_crossPoint_localisationPresentation (j : Fin (2 + 1)) :
    MvPolynomial.eval crossPoint.{u}
      (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0)) j) = 0 := by
  refine Fin.lastCases ?_ ?_ j
  · rw [localisationPresentation_last]
    simp [crossPoint, localisationVar, localisationIncl]
  · intro j
    rw [localisationPresentation_castSucc]
    fin_cases j <;>
      simp [nodeTuple3, crossPoint, localisationIncl]

/-- **The unit is not `1`**, so `crossHu` is an instance of the hypothesis with content and not of
`x = 1 * x`.

Evaluation at `crossPoint` is a ring map killing the ideal, and it sends the class of `z₀` read
upstairs to `2`. This is the same argument `presentationIdeal_localisation_node_ne_top` makes one
localisation over, at a point rather than at a family. -/
theorem crossU_ne_one :
    (crossU.{u} : PresentedAlgebra.{u} (3 + 1) (2 + 1)
      (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0)))) ≠ 1 := by
  intro hcon
  have hle : presentationIdeal.{u}
      (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))) ≤
      RingHom.ker (MvPolynomial.eval crossPoint.{u}) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact RingHom.mem_ker.2 (eval_crossPoint_localisationPresentation.{u} j)
  have hmk : Ideal.Quotient.mk (presentationIdeal.{u}
      (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))))
      (MvPolynomial.rename (localisationIncl.{u} 3) (MvPolynomial.X (ULift.up 0))) = 1 := by
    rw [← hcon, crossU, IsUnit.unit_spec]
  have hsub := RingHom.mem_ker.1 (hle (Ideal.Quotient.eq.1
    (hmk.trans (map_one (Ideal.Quotient.mk _)).symm)))
  rw [map_sub, map_one] at hsub
  simp [crossPoint, localisationIncl] at hsub
  norm_num at hsub

/-- **The cross-member glue, at the node presented twice.**

The first member is the node in two variables refined by `D(z₀)` with no extra factor; the second
is the node in three variables refined by `D(z₀)` with the extra factor `z₀`. The original
overlap is `D(z₀)` on both sides and `crossE` identifies the two descriptions of it. -/
def nodeCrossGlue :
    (⟨2 + 1 + 1, 1 + 1 + 1, localisationPresentation.{u}
        (localisationPresentation.{u} nodeTuple2.{u} (MvPolynomial.X (ULift.up 0)))
        (MvPolynomial.rename (localisationIncl.{u} 2)
          (MvPolynomial.X (ULift.up 0) * 1))⟩ : Presentation.{u}) ≅
      ⟨3 + 1 + 1, 2 + 1 + 1, localisationPresentation.{u}
        (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0)))
        (MvPolynomial.rename (localisationIncl.{u} 3)
          (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 0)))⟩ :=
  refineCrossGlue.{u} nodeTuple2.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))
    (MvPolynomial.X (ULift.up 0)) 1 (MvPolynomial.X (ULift.up 0)) (MvPolynomial.X (ULift.up 0))
    (MvPolynomial.X (ULift.up 0)) (MvPolynomial.rename (localisationIncl.{u} 3)
      (MvPolynomial.X (ULift.up 0))) crossE.{u} crossHe.{u} crossU.{u} crossHu.{u}

/-- **The triangle at that instance**, which is
`ComplexAnalytic.refineCrossGlue_hom_comp` and not a restatement of an identity: its two sides are
morphisms between objects that `nodeCrossGlue_ne` separates. -/
theorem nodeCrossGlue_hom_comp :
    nodeCrossGlue.{u}.hom ≫ refineCrossProj.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0))
        (MvPolynomial.X (ULift.up 0)) (MvPolynomial.X (ULift.up 0)) =
      refineCrossProj.{u} nodeTuple2.{u} (MvPolynomial.X (ULift.up 0))
          (MvPolynomial.X (ULift.up 0)) 1 ≫
        (Presentation.isoOfAlgEquiv crossE.{u}.symm).hom :=
  refineCrossGlue_hom_comp.{u} nodeTuple2.{u} nodeTuple3.{u} _ _ _ _ _ _ _ crossE.{u} crossHe.{u}
    crossU.{u} crossHu.{u}

/-- **The two objects glued are not equal**, so the isomorphism is not an identity in disguise.

Their variable counts are `4` and `5`, which is the separator `localisationPresentation_node_ne`
uses one localisation down and `nodePres2_ne_nodePres3` uses two. -/
theorem nodeCrossGlue_ne :
    (⟨2 + 1 + 1, 1 + 1 + 1, localisationPresentation.{u}
        (localisationPresentation.{u} nodeTuple2.{u} (MvPolynomial.X (ULift.up 0)))
        (MvPolynomial.rename (localisationIncl.{u} 2)
          (MvPolynomial.X (ULift.up 0) * 1))⟩ : Presentation.{u}) ≠
      ⟨3 + 1 + 1, 2 + 1 + 1, localisationPresentation.{u}
        (localisationPresentation.{u} nodeTuple3.{u} (MvPolynomial.X (ULift.up 0)))
        (MvPolynomial.rename (localisationIncl.{u} 3)
          (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 0)))⟩ := by
  intro h
  exact absurd (congrArg Presentation.n h) (by decide)

end OkaTest.CrossMemberGlue

end

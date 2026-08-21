/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of presentation-independence: the node, presented in three variables

`Oka/Analytification/ChangeOfVariables.lean` proves that a `ℂ`-algebra map of presented algebras
induces a morphism of analytifications, functorially, and hence that two presentations of one
algebra have isomorphic analytifications. **Every statement there would be true and empty if the
only `ℂ`-algebra maps one could produce were identities**, and in particular a version that
secretly required the two presentations to use the same variables would satisfy all of it.

This file rules that out with the smallest example in which the two presentations genuinely
differ in the **number of variables**:

```
ℂ[x, y] ⧸ (x y)        against        ℂ[x, y, z] ⧸ (x y, z)
```

`n = 2, k = 1` against `n = 3, k = 2` — *both* indices differ, which is what makes it the right
witness: a theorem that had accidentally fixed either would fail to elaborate here. The two
algebras are isomorphic, by `z ↦ 0`, and `nodeIsoAnalytification3` is the resulting isomorphism
of analytifications. Since `AnalyticSpace.node` **is** the left-hand analytification
definitionally (`node_eq_analytification_nodeTuple2`), this exhibits the node as the
analytification of a presentation that embeds it in `ℂ³` rather than in `ℂ²`.

`ComplexAnalytic.analytificationIsoOfPresentationIdealEq`, in the universal-property file, is the
same statement for a change of *generators* and cannot reach this case: it requires one fixed
polynomial ring.

The two `ℂ`-algebra maps are built by `Ideal.Quotient.lift` of an `MvPolynomial.eval₂Hom`, which
is the only way to get a ring map out of a presented algebra, and the round trips are checked on
generators — including that the redundant variable `z` goes to `0` and back to `0`, which is the
step that would fail if the third variable were not actually killed.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology
open ComplexAnalytic

universe u

noncomputable section

/-- The node in two variables: `ℂ[x, y] ⧸ (x y)`. -/
def nodeTuple2 : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ := fun _ ↦ nodePoly.{u}

/-- The same algebra in **three** variables: `ℂ[x, y, z] ⧸ (x y, z)`. -/
def nodeTuple3 : Fin 2 → MvPolynomial (ULift.{u} (Fin 3)) ℂ :=
  ![MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1), MvPolynomial.X (ULift.up 2)]

/-- `x, y, 0` as elements of `ℂ[x, y] ⧸ (x y)`. -/
def vars32 : ULift.{u} (Fin 3) → PresentedAlgebra.{u} 2 1 nodeTuple2.{u} :=
  fun i ↦ ![Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 0)),
    Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 1)), 0] i.down

/-- `x, y` as elements of `ℂ[x, y, z] ⧸ (x y, z)`. -/
def vars23 : ULift.{u} (Fin 2) → PresentedAlgebra.{u} 3 2 nodeTuple3.{u} :=
  fun i ↦ ![Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 0)),
    Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 1))] i.down

theorem mk_nodePoly_eq_zero :
    Ideal.Quotient.mk (presentationIdeal.{u} nodeTuple2.{u}) nodePoly.{u} = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨0, rfl⟩)

theorem eval₂_nodeTuple3_vars32 (j : Fin 2) :
    MvPolynomial.eval₂ (presentedAlgebraMap.{u} nodeTuple2.{u}) vars32.{u}
      (nodeTuple3.{u} j) = 0 := by
  fin_cases j
  · change MvPolynomial.eval₂ _ vars32.{u}
      (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1)) = 0
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
    change (Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 0))) *
      (Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 1))) = 0
    rw [← map_mul]
    exact mk_nodePoly_eq_zero.{u}
  · change MvPolynomial.eval₂ _ vars32.{u} (MvPolynomial.X (ULift.up 2)) = 0
    rw [MvPolynomial.eval₂_X]
    rfl

theorem eval₂_nodeTuple2_vars23 (j : Fin 1) :
    MvPolynomial.eval₂ (presentedAlgebraMap.{u} nodeTuple3.{u}) vars23.{u}
      (nodeTuple2.{u} j) = 0 := by
  change MvPolynomial.eval₂ _ vars23.{u}
    (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1)) = 0
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
  change (Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 0))) *
    (Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 1))) = 0
  rw [← map_mul]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨0, rfl⟩)

/-- Dropping the third variable: `ℂ[x, y, z] ⧸ (x y, z) → ℂ[x, y] ⧸ (x y)`. -/
def presHom23 : PresHom.{u} nodeTuple2.{u} nodeTuple3.{u} where
  toRingHom := Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (presentedAlgebraMap.{u} nodeTuple2.{u}) vars32.{u})
    (fun _ hx ↦ RingHom.mem_ker.1
      (Ideal.span_le.2 (Set.range_subset_iff.2 eval₂_nodeTuple3_vars32.{u}) hx))
  commutes := RingHom.ext fun c ↦
    MvPolynomial.eval₂Hom_C (presentedAlgebraMap.{u} nodeTuple2.{u}) vars32.{u} c

/-- Adjoining a redundant variable: `ℂ[x, y] ⧸ (x y) → ℂ[x, y, z] ⧸ (x y, z)`. -/
def presHom32 : PresHom.{u} nodeTuple3.{u} nodeTuple2.{u} where
  toRingHom := Ideal.Quotient.lift _
    (MvPolynomial.eval₂Hom (presentedAlgebraMap.{u} nodeTuple3.{u}) vars23.{u})
    (fun _ hx ↦ RingHom.mem_ker.1
      (Ideal.span_le.2 (Set.range_subset_iff.2 eval₂_nodeTuple2_vars23.{u}) hx))
  commutes := RingHom.ext fun c ↦
    MvPolynomial.eval₂Hom_C (presentedAlgebraMap.{u} nodeTuple3.{u}) vars23.{u} c

theorem mk_X2_eq_zero :
    Ideal.Quotient.mk (presentationIdeal.{u} nodeTuple3.{u})
      (MvPolynomial.X (ULift.up 2)) = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨1, rfl⟩)

theorem presHom23_comp_presHom32 :
    (presHom23.{u}).toRingHom.comp (presHom32.{u}).toRingHom =
      RingHom.id (PresentedAlgebra.{u} 2 1 nodeTuple2.{u}) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
  · exact (congrArg (presHom23.{u}).toRingHom
      (MvPolynomial.eval₂Hom_C (presentedAlgebraMap.{u} nodeTuple3.{u}) vars23.{u} c)).trans
      (MvPolynomial.eval₂Hom_C (presentedAlgebraMap.{u} nodeTuple2.{u}) vars32.{u} c)
  · obtain ⟨i⟩ := i
    fin_cases i <;>
      simp [presHom23, presHom32, vars23, vars32, Ideal.Quotient.lift_mk]

theorem presHom32_comp_presHom23 :
    (presHom32.{u}).toRingHom.comp (presHom23.{u}).toRingHom =
      RingHom.id (PresentedAlgebra.{u} 3 2 nodeTuple3.{u}) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
  · exact (congrArg (presHom32.{u}).toRingHom
      (MvPolynomial.eval₂Hom_C (presentedAlgebraMap.{u} nodeTuple2.{u}) vars32.{u} c)).trans
      (MvPolynomial.eval₂Hom_C (presentedAlgebraMap.{u} nodeTuple3.{u}) vars23.{u} c)
  · obtain ⟨i⟩ := i
    fin_cases i
    · simp [presHom23, presHom32, vars23, vars32, Ideal.Quotient.lift_mk]
    · simp [presHom23, presHom32, vars23, vars32, Ideal.Quotient.lift_mk]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      refine Eq.trans ?_ mk_X2_eq_zero.{u}.symm
      simp [presHom23, presHom32, vars32, Ideal.Quotient.lift_mk]

/-- **The analytification of `ℂ[x, y] ⧸ (x y)` presented in two variables is isomorphic to its
analytification presented in three.** The node, reached from `ℂ³` instead of from `ℂ²`. -/
def nodeIsoAnalytification3 :
    AnalyticSpace.analytification.{u} nodeTuple2.{u} ≅
      AnalyticSpace.analytification.{u} nodeTuple3.{u} :=
  analytificationIsoOfPresHom.{u} presHom23.{u} presHom32.{u}
    presHom23_comp_presHom32.{u} presHom32_comp_presHom23.{u}

/-- The source of that isomorphism is the node, definitionally. -/
theorem node_eq_analytification_nodeTuple2 :
    AnalyticSpace.node.{u} = AnalyticSpace.analytification.{u} nodeTuple2.{u} := rfl

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the universal property of the analytification

`ComplexAnalytic.existsUnique_hom_analytification` says that a tuple of global sections of `𝒪_Z`
satisfying the equations `gⱼ(a) = 0` comes from exactly one morphism `Z ⟶ X^an`. **It would be
true and empty if its hypothesis held only in cases where the morphism was already available**,
or if the hom-sets it quantifies over were singletons. This file rules both out, at the node.

`OkaTest/Factorisation.lean` does the same job for
`ComplexAnalytic.IsCutOutBy.existsUnique_liftHom`, one level down, and the three tests below are
its three tests moved up a level. The difference is that the hypothesis being met here is an
**equation between polynomials and sections** rather than a vanishing of sheaf-map images, which
is the whole point of the substitution formula.

* `liftHom_nodeCoord_eq_id` runs the theorem where the answer is known. The node's own
  coordinates satisfy the node's equation, so they must come from *some* morphism
  `node ⟶ node`; it has to be the **identity**, and it is. If the construction produced the `n`
  coordinates independently rather than one morphism, this is what would fail.
* `axisIncl` runs it where the answer is **not** known. Its tuple is `(z, 0)` on `ℂ`, which
  satisfies `z₀ z₁ = 0` for the reason the node exists, and it is a factorisation of nothing.
  What comes back is the inclusion of a coordinate axis — a morphism `ℂ ⟶ node`.
* `axisIncl_ne` is what makes the `∃!` about something. The two axis inclusions are **different**
  morphisms `ℂ ⟶ node`, so `Hom(ℂ, node)` is not a singleton and "exactly one" is a real claim.
  Nonempty is not enough here and never has been on this project: a `∃!` over a subsingleton
  hom-set is free.
* `nodeIsoAnalytification'` exercises
  `ComplexAnalytic.analytificationIsoOfPresentationIdealEq` at two tuples of **different
  lengths** — `(z₀z₁)` and `(z₀z₁, z₀ · z₀z₁)` — which is the case a version assuming a common
  index type would miss. The two analytifications are not definitionally equal; the isomorphism
  between them is produced by the universal property and by nothing else in the development.

The first three declarations record that the node **is** an analytification, definitionally:
`AnalyticSpace.node` is `AnalyticSpace.analytification` at the one-element tuple `(z₀z₁)`,
`ComplexAnalytic.nodeIncl` is `ComplexAnalytic.analytificationInclHom` there, and
`ComplexAnalytic.nodeCoord` is `ComplexAnalytic.analytificationCoord` there.
All three are `rfl`, which is why the node can serve as the test case at all — nothing is being
transported.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology
open ComplexAnalytic

universe u

noncomputable section

/-- The node's presentation: the single polynomial `z₀ z₁`. -/
def nodeTuple : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ := fun _ ↦ nodePoly.{u}

theorem node_eq_analytification :
    AnalyticSpace.node.{u} = AnalyticSpace.analytification.{u} nodeTuple.{u} := rfl

theorem nodeIncl_eq_analytificationInclHom :
    nodeIncl.{u} = analytificationInclHom.{u} nodeTuple.{u} := rfl

theorem analytificationCoord_nodeTuple (j : ULift.{u} (Fin 2)) :
    analytificationCoord.{u} nodeTuple.{u} j = nodeCoord.{u} j := rfl

/-! ### Running the universal property where the answer is known -/

theorem eval₂_nodeCoord_nodeTuple (j : Fin 1) :
    MvPolynomial.eval₂ (AnalyticSpace.node.{u}).algebraMap nodeCoord.{u} (nodeTuple.{u} j) = 0 :=
  eval₂_analytificationCoord_eq_zero.{u} nodeTuple.{u} j

theorem coordPullback_id_comp_nodeIncl (i : ULift.{u} (Fin 2)) :
    AnalyticSpace.coordPullback (𝟙 (AnalyticSpace.analytification.{u} nodeTuple.{u}) ≫
      analytificationInclHom.{u} nodeTuple.{u}) i = nodeCoord.{u} i := by
  rw [Category.id_comp]
  rfl

theorem liftHom_nodeCoord_eq_id :
    liftHom.{u} nodeTuple.{u} AnalyticSpace.node.{u} nodeCoord.{u} eval₂_nodeCoord_nodeTuple.{u} =
      𝟙 (AnalyticSpace.analytification.{u} nodeTuple.{u}) :=
  (existsUnique_hom_analytification.{u} nodeTuple.{u} AnalyticSpace.node.{u} nodeCoord.{u}
      eval₂_nodeCoord_nodeTuple.{u}).unique
    (coordPullback_liftHom_comp.{u} nodeTuple.{u} _ _ _) coordPullback_id_comp_nodeIncl.{u}

/-! ### Running it where the answer is not known -/

open scoped Classical in
/-- The tuple `(z, 0)` of global sections of `𝒪_ℂ`, which satisfies the node's equation. -/
def axisTuple (l : ULift.{u} (Fin 2)) : ULift.{u} (Fin 2) →
    (AnalyticSpace.complexAffineSpace.{u} 1).presheaf.obj (op ⊤) :=
  fun j ↦ if j = l then coord (ULift.up 0) else 0

theorem eval₂_axisTuple (l : ULift.{u} (Fin 2)) (j : Fin 1) :
    MvPolynomial.eval₂ (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap (axisTuple.{u} l)
      (nodeTuple.{u} j) = 0 := by
  classical
  have hne : (ULift.up 0 : ULift.{u} (Fin 2)) ≠ ULift.up 1 := fun hcon ↦ by
    simpa using congrArg ULift.down hcon
  refine Eq.trans (MvPolynomial.eval₂_mul _ _) ?_
  rw [MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
  rcases eq_or_ne l (ULift.up 0) with rfl | hl
  · rw [show axisTuple.{u} (ULift.up 0) (ULift.up 1) = 0 from if_neg hne.symm, mul_zero]
  · rw [show axisTuple.{u} l (ULift.up 0) = 0 from if_neg fun h ↦ hl h.symm, zero_mul]

/-- **The inclusion of a coordinate axis of the node**, produced by the universal property from
a tuple of sections of `𝒪_ℂ` and not available before it. -/
def axisIncl (l : ULift.{u} (Fin 2)) :
    AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u} :=
  liftHom.{u} nodeTuple.{u} _ (axisTuple.{u} l) (eval₂_axisTuple.{u} l)

theorem coordPullback_axisIncl_comp (l j : ULift.{u} (Fin 2)) :
    AnalyticSpace.coordPullback (axisIncl.{u} l ≫ nodeIncl.{u}) j = axisTuple.{u} l j :=
  coordPullback_liftHom_comp.{u} nodeTuple.{u} _ _ _ j

theorem coord_ne_zero : coord (ULift.up 0) ≠ (0 : OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ))) :=
  fun hcon ↦ one_ne_zero (α := ℂ)
    ((evalHom_coord (z := fun _ ↦ (1 : ℂ)) (ULift.up 0)).symm.trans
      ((congrArg (OkaRing.evalHom (U := ⊤) (x := fun _ : ULift.{u} (Fin 1) ↦ (1 : ℂ)) trivial)
        hcon).trans (map_zero _)))

/-- **The two axis inclusions are different morphisms `ℂ ⟶ node`**, so the hom-set the universal
property produces its `∃!` inside is not a singleton. -/
theorem axisIncl_ne : axisIncl.{u} (ULift.up 0) ≠ axisIncl.{u} (ULift.up 1) := by
  classical
  have hne : (ULift.up 0 : ULift.{u} (Fin 2)) ≠ ULift.up 1 := fun hcon ↦ by
    simpa using congrArg ULift.down hcon
  refine fun hcon ↦ coord_ne_zero.{u} ?_
  have h0 := coordPullback_axisIncl_comp.{u} (ULift.up 0) (ULift.up 0)
  have h1 := coordPullback_axisIncl_comp.{u} (ULift.up 1) (ULift.up 0)
  rw [hcon] at h0
  refine Eq.trans ?_ (h0.symm.trans h1)
  exact (if_pos rfl).symm

/-! ### Independence of the chosen generators -/

/-- A second, longer presentation of the same ideal: `z₀ z₁` together with `z₀ · z₀ z₁`. -/
def nodeTuple' : Fin 2 → MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  ![nodePoly.{u}, MvPolynomial.X (ULift.up 0) * nodePoly.{u}]

theorem presentationIdeal_nodeTuple_eq :
    presentationIdeal.{u} nodeTuple.{u} = presentationIdeal.{u} nodeTuple'.{u} := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨0, rfl⟩
  · rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact Ideal.subset_span ⟨0, rfl⟩
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩)

/-- **The node is the analytification of its longer presentation too**, by an isomorphism which
the universal property produces and which no construction in the development supplies. -/
def nodeIsoAnalytification' :
    AnalyticSpace.node.{u} ≅ AnalyticSpace.analytification.{u} nodeTuple'.{u} :=
  analytificationIsoOfPresentationIdealEq.{u} presentationIdeal_nodeTuple_eq.{u}

/-! ### The crossing the universal property rests on, as a check rather than a sentence -/

/-- **A polynomial section crosses `restrictTopIso` definitionally.**

`Oka/Analytification/UniversalProperty.lean`'s `## The two inputs, and the seam between them that
turned out not to exist` says that the crossing between
`ComplexAnalytic.AnalyticSpace.complexAffineSpace` and its `restrict ⊤` presentation is free
because *"a section whose presentation does not mention the open it lives on crosses
definitionally"*, and
`ComplexAnalytic.c_app_toAmbient_polySection`'s docstring names the instance of it that the
factorisation hypothesis needs: `ComplexAnalytic.polySection g j` **is** the pullback of
`OkaRing.ofMvPolynomial ⊤ (g j)` along `restrictTopIso.hom`. That is what makes
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply` applicable there and is why nothing in
that file carries a transport.

**It is stated here because the general equation is not definitional and the contrast is the
content.** `TopologicalSpace.Opens.isOpenEmbedding_obj_top` is a `@[simp]` lemma and not a `rfl` —
taxis #702 established that, and it holds even at `⊤` and even over `ℂ^n` — so *"this crossing is
free"* is a claim about the section and not about the opens, and a claim of that shape is worth a
check that fails if it stops being true. -/
theorem polySection_eq_Γ_map_restrictTopIso_hom {n k : ℕ}
    (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) (j : Fin k) :
    polySection.{u} g j =
      (LocallyRingedSpace.Γ.map
        (AnalyticSpace.complexAffineSpace.{u} n).restrictTopIso.hom.op).hom
          (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) (g j)) :=
  rfl

end

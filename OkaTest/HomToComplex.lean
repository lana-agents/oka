/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the rigidity of morphisms to `ℂ^n`

`Oka/AnalyticSpace/HomToComplex.lean` proves that a morphism of complex analytic spaces
`Z ⟶ ℂ^n` is determined by the pullbacks of the coordinate functions, and that for `Z = ℂ^n`
the pullback of the coordinate is a bijection onto `Γ(ℂ^n, 𝒪)`. Both statements would be true
and empty if the hom-sets involved were singletons, and both would be true and weaker than they
look if their hypotheses were redundant. This file rules out each of those.

* `okaMap_coord_eq_id` is the check that the uniqueness theorem *does work*. The morphism
  attached to the family `(z ↦ z)` and the identity of `ℂ` are not the same term and are not
  equal by `rfl`; they pull the coordinate back to the same section, so the theorem forces them
  equal.
* `evalStalk_nodeToLine` instantiates the naturality of evaluation at a **non-identity morphism
  between two different analytic spaces**, `ComplexAnalytic.nodeToLine j : node ⟶ ℂ`, and
  `eval_nodeCoord_via_nodeToLine` uses it to compute the value of `nodeCoord j` at a point of
  the node. That value is already known by a route sharing no lemma with this one
  (`ComplexAnalytic.eval_nodeCoord`, through `eval_ofCutOut`), so the two agreeing is a check on
  both.
* `two_distinct_homs` records that the hom-set the uniqueness theorem is about is not a
  singleton. The evidence that rigidity is *productive* rather than merely satisfiable is
  `ComplexAnalytic.nodeCoord_ne`, which is in the library because it is a new fact about the
  node rather than a check on this file: `nodeToLine_ne` is a statement about base maps, and
  rigidity converts it into one about **sections**, which neither `nodeCoord_mul` nor
  `nodeCoord_ne_zero` gives.
* `hcoord_not_redundant` shows the hypothesis of `ComplexAnalytic.okaStalk_ringHom_ext` that the
  two maps agree on the coordinates cannot be dropped: `α ∘ evalHom`, the constant with the
  value at the point, is a local `ℂ`-algebra endomorphism of the stalk fixing every constant
  and killing every coordinate.
* `endomorphism_eq_id` and `stalkCoord_mem_maximalIdeal` are the two checks that the hypotheses
  of `okaStalk_ringHom_ext` are simultaneously satisfiable and that
  `maximalIdeal_stalk_eq_span_stalkCoord` is not the trivial statement with `⊤` on both sides.
  That the span is not `0` either is `ComplexAnalytic.stalkCoord_ne_zero`, in the library.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry IsLocalRing ComplexAnalytic

universe u

noncomputable section

variable {ι : Type u} [Fintype ι]

/-! ### The uniqueness theorem does work -/

/-- **The morphism of analytic spaces attached to the coordinate function is the identity.**

Neither side is the other by `rfl`: the left is built from a family of entire functions through
`ComplexAnalytic.okaMapC`, and the right is the categorical identity. They agree because they
pull the coordinate back to the same section, which is exactly what
`ComplexAnalytic.AnalyticSpace.hom_ext_complexLine` is for. -/
theorem okaMap_coord_eq_id :
    AnalyticSpace.okaMap (fun _ : ULift.{u} (Fin 1) ↦ coord (ULift.up 0)) =
      𝟙 (AnalyticSpace.complexAffineSpace.{u} 1) := by
  have hid : (LocallyRingedSpace.Γ.map (AnalyticSpace.Hom.toLRSHom
        (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1))).op).hom (coord (ULift.up 0)) =
      coord (ULift.up 0) := by
    rw [show AnalyticSpace.Hom.toLRSHom (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1)) =
      𝟙 (AnalyticSpace.complexAffineSpace.{u} 1).toLocallyRingedSpace from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  exact AnalyticSpace.hom_ext_complexLine _ _ ((Γ_map_okaMapHom_coord _ (ULift.up 0)).trans
    hid.symm)

/-- **The bijection `Hom(ℂ^n, ℂ) ≃ Γ(ℂ^n, 𝒪)`, named on the whole of its image**: the morphism
attached to a family of entire functions goes to that family's only member. Naming the function
rather than exhibiting two of its values is what rules out a bijection which is secretly
constant. -/
theorem homComplexLineEquiv_okaMap {n : ℕ}
    (u : ULift.{u} (Fin 1) → OkaRing (⊤ : Opens (ULift.{u} (Fin n) → ℂ))) :
    AnalyticSpace.homComplexLineEquiv.{u} n (AnalyticSpace.okaMap u) = u (ULift.up 0) :=
  Γ_map_okaMapHom_coord u (ULift.up 0)

/-- **The hom-set is not a singleton**, so the uniqueness theorem is about something: the two
coordinate morphisms out of the node differ, and so do the sections they produce. -/
theorem two_distinct_homs :
    ∃ φ ψ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      φ ≠ ψ ∧ (LocallyRingedSpace.Γ.map φ.toLRSHom.op).hom (coord (ULift.up 0)) ≠
        (LocallyRingedSpace.Γ.map ψ.toLRSHom.op).hom (coord (ULift.up 0)) :=
  ⟨nodeToLine.{u} (ULift.up 0), nodeToLine.{u} (ULift.up 1), nodeToLine_ne.{u}, fun hcon ↦
    nodeCoord_ne.{u} ((Γ_map_nodeToLineHom_coord (ULift.up 0)).symm.trans
      (hcon.trans (Γ_map_nodeToLineHom_coord (ULift.up 1))))⟩

/-- **The inverse of the bijection, named.** `homComplexLineEquiv` is built by
`Equiv.ofBijective`, so its inverse is a choice term; this says that on the sections which come
from a family of entire functions it is `okaMap`, with no choice left in it. -/
theorem symm_homComplexLineEquiv_okaMap {n : ℕ}
    (u : ULift.{u} (Fin 1) → OkaRing (⊤ : Opens (ULift.{u} (Fin n) → ℂ))) :
    (AnalyticSpace.homComplexLineEquiv.{u} n).symm (u (ULift.up 0)) =
      AnalyticSpace.okaMap u :=
  (Equiv.symm_apply_eq _).2 (Γ_map_okaMapHom_coord u (ULift.up 0)).symm

/-! ### Naturality of evaluation, at a non-identity morphism -/

/-- **Naturality of evaluation, instantiated at `nodeToLine j`**, a morphism between two
*different* complex analytic spaces which is neither an identity nor a constant. -/
theorem evalStalk_nodeToLine (j : ULift.{u} (Fin 2)) (p : AnalyticSpace.node.{u})
    (a : (AnalyticSpace.complexAffineSpace.{u} 1).presheaf.stalk
      ((nodeToLine.{u} j).toLRSHom.base p)) :
    (AnalyticSpace.node.{u}).evalStalk p (((nodeToLine.{u} j).toLRSHom.stalkMap p).hom a) =
      (AnalyticSpace.complexAffineSpace.{u} 1).evalStalk _ a :=
  AnalyticSpace.evalStalk_stalkMap_hom (nodeToLine.{u} j) p a

/-- **The value of `nodeCoord j` at a point of the node, computed through `nodeToLine j`.**

`ComplexAnalytic.eval_nodeCoord` gives the same value through `ComplexAnalytic.eval_ofCutOut`,
which shares no lemma with this route: the two agreeing checks the base map of `nodeToLine`, the
pullback computation `Γ_map_nodeToLineHom_coord`, and the naturality of evaluation against each
other. -/
theorem eval_nodeCoord_via_nodeToLine (j : ULift.{u} (Fin 2)) (p : AnalyticSpace.node.{u}) :
    (AnalyticSpace.node.{u}).eval (U := ⊤) p trivial (nodeCoord.{u} j) = p.1.1 j := by
  refine Eq.trans ?_ (base_nodeToLineHom j p (ULift.up 0))
  rw [← Γ_map_nodeToLineHom_coord j]
  refine Eq.trans (AnalyticSpace.eval_c_app (Z := AnalyticSpace.node.{u})
    (W := AnalyticSpace.complexAffineSpace.{u} 1) (nodeToLine.{u} j).toLRSHom
    (nodeToLine.{u} j).isCLinear (U := ⊤) p trivial (coord (ULift.up 0))) ?_
  exact AnalyticSpace.eval_coord _ (ULift.up 0)

/-! ### The hypotheses of `okaStalk_ringHom_ext` -/

/-- **A local `ℂ`-algebra endomorphism of a germ ring on `ℂ^ι` fixing the coordinates is the
identity.** The hypotheses of `ComplexAnalytic.okaStalk_ringHom_ext` are satisfiable — the
identity satisfies them — and its instance requirements are met by the germ ring itself. -/
theorem endomorphism_eq_id {y : ι → ℂ}
    (θ : (okaCommPresheaf ι).stalk y →+* (okaCommPresheaf ι).stalk y) [IsLocalHom θ]
    (hconst : ∀ c : ℂ, θ (((okaCommPresheaf ι).germ ⊤ y trivial).hom
        (algebraMap ℂ (OkaRing ⊤) c)) =
      ((okaCommPresheaf ι).germ ⊤ y trivial).hom (algebraMap ℂ (OkaRing ⊤) c))
    (hcoord : ∀ i : ι, θ (((okaCommPresheaf ι).germ ⊤ y trivial).hom
        (OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X i))) =
      ((okaCommPresheaf ι).germ ⊤ y trivial).hom
        (OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X i))) :
    θ = RingHom.id _ :=
  okaStalk_ringHom_ext hconst hcoord

/-- The generators really are in the maximal ideal, so the span statement is not the trivial
one with `⊤` on both sides: a normalised coordinate germ vanishes at the point. -/
theorem stalkCoord_mem_maximalIdeal (y : ι → ℂ) (i : ι) :
    stalkCoord y i ∈ maximalIdeal ((okaCommPresheaf ι).stalk y) := by
  rw [maximalIdeal_stalk_eq_span_stalkCoord]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- **The hypothesis `hcoord` of `ComplexAnalytic.okaStalk_ringHom_ext` cannot be dropped.**

As soon as `ι` is nonempty there is a non-identity local `ℂ`-algebra endomorphism of the stalk
fixing every constant: `α ∘ evalHom`, the germ of the constant function with the value at `y`.
It is local because it sends the maximal ideal to `0`
(`IsLocalRing.IsCoefficientField.isLocalHom_comp_evalHom`), and it kills every normalised
coordinate germ, which is nonzero by `ComplexAnalytic.stalkCoord_ne_zero`. -/
theorem hcoord_not_redundant (y : ι → ℂ) (i : ι) :
    ∃ θ : (okaCommPresheaf ι).stalk y →+* (okaCommPresheaf ι).stalk y,
      IsLocalHom θ ∧
      (∀ c : ℂ, θ ((((okaCommPresheaf ι).germ ⊤ y trivial).hom.comp
          (algebraMap ℂ (OkaRing ⊤))) c) =
        (((okaCommPresheaf ι).germ ⊤ y trivial).hom.comp (algebraMap ℂ (OkaRing ⊤))) c) ∧
      θ ≠ RingHom.id _ := by
  set h := isCoefficientField_germ_algebraMap (U := ⊤) (y := y) trivial with hh
  refine ⟨_, h.isLocalHom_comp_evalHom, fun c ↦ by
    rw [RingHom.comp_apply, h.evalHom_const], fun hid ↦ ?_⟩
  have hmem : stalkCoord y i ∈ maximalIdeal ((okaCommPresheaf ι).stalk y) :=
    stalkCoord_mem_maximalIdeal y i
  have hval := congrArg (fun f ↦ f (stalkCoord y i)) hid
  simp only [RingHom.comp_apply, h.evalHom_eq_zero_iff.2 hmem, map_zero, RingHom.id_apply] at hval
  exact stalkCoord_ne_zero y i hval.symm

end

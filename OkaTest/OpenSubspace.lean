/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of `AnalyticSpace.restrict`

`ComplexAnalytic.AnalyticSpace.restrict X U` is a complex analytic space for every `X` and every
`U`. **At `U = ⊤` that is empty**: the restriction is `X` again up to the identification of `⊤`
with the whole space, and the chart produced at each point is the chart `X` already had. So the
instantiation that tests it has to be a *proper* open subspace of a space that is not `ℂ^n`.

The witness here is **the node minus the origin** — `puncturedNode` — which is the case the
issue asked for rather than the fallback of an open subset of `ℂ^n`:

* it really is the node minus the origin (`mem_puncturedNode_iff`) and is a proper open subspace
  (`puncturedNode_ne_top`, the origin being a point that really is on the node);
* the point removed is the one at which the two axes meet, which is where the node fails to be
  a manifold — that last clause is the reason for the choice and is **not** formalised, here or
  anywhere in this development;
* and it is **disconnected** (`not_preconnectedSpace_puncturedNodeSpace`), which `ℂ^n` is not.

Two further checks: `eval_pullback_nodeCoord` evaluates a section on the punctured node through
the analytic-space structure the restriction produced, and gets the number `eval_nodeCoord`
gives on the node — so the structure is usable and not merely well typed; and
`injective_base_puncturedNodeIncl` says the inclusion is injective and **not** surjective on
points, which is properness at the level of the morphism rather than of the open set.

The disconnectedness is proved, not asserted. It is the two punctured axes: each is open, they
are disjoint because a point of the node has `z₀ z₁ = 0` so cannot have both coordinates
nonzero, they cover the punctured node by definition, and each contains a point.

**What this file does not claim.** That the node itself is connected — which would sharpen the
contrast — is not proved here. Nor is it proved that the node is not a complex manifold, which
is the geometric statement the two axes meeting at the origin is evidence for.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-! ### The node minus the origin -/

/-- The points of the node at which the `j`-th coordinate does not vanish: the `j`-th axis with
the origin removed. -/
def nodeAxis (j : ULift.{u} (Fin 2)) : Opens (AnalyticSpace.node.{u}) :=
  ⟨{p : AnalyticSpace.node.{u} | p.1.1 j ≠ 0},
    isOpen_compl_singleton.preimage ((continuous_apply j).comp
      (continuous_subtype_val.comp continuous_subtype_val))⟩

/-- **The node minus the origin**, as the union of the two punctured axes. Writing it this way
rather than as the complement of a point keeps every statement about it pointwise in the two
coordinates, and it is the decomposition that disconnects it. -/
def puncturedNode : Opens (AnalyticSpace.node.{u}) :=
  nodeAxis.{u} (ULift.up 0) ⊔ nodeAxis.{u} (ULift.up 1)

/-- The origin, as a point of the node. -/
def nodeOrigin : AnalyticSpace.node.{u} :=
  ⟨⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩, origin_mem_zeroLocus_nodeSection.{u}⟩

/-- **`puncturedNode` is the node minus the origin**, which is what its name says and what the
union of the two punctured axes is not obviously equal to. Without this the name is a claim
about the object that only the definition's shape supports. -/
theorem mem_puncturedNode_iff (p : AnalyticSpace.node.{u}) :
    p ∈ puncturedNode.{u} ↔ p ≠ nodeOrigin.{u} := by
  constructor
  · rintro (h | h) rfl <;> exact h rfl
  · intro hne
    by_contra hcon
    refine hne (Subtype.ext (Subtype.ext (funext fun l ↦ ?_)))
    rcases l with ⟨l⟩
    fin_cases l
    · exact not_not.1 fun h ↦ hcon (Or.inl h)
    · exact not_not.1 fun h ↦ hcon (Or.inr h)

/-- **The origin is a point of the node outside `puncturedNode`**, so this is a proper open
subspace and `AnalyticSpace.restrict` is not being instantiated at `⊤`, for which it is
trivial. The point removed is one the *subspace* had, not merely one of the ambient `ℂ²`. -/
theorem puncturedNode_ne_top : puncturedNode.{u} ≠ ⊤ := by
  intro hcon
  exact (mem_puncturedNode_iff nodeOrigin.{u}).1 (hcon ▸ trivial) rfl

/-- **The node minus the origin is a complex analytic space.** -/
def puncturedNodeSpace : AnalyticSpace.{u} :=
  AnalyticSpace.node.{u}.restrict puncturedNode.{u}

/-- The inclusion of the node minus the origin into the node, as a morphism of complex analytic
spaces — the development's first morphism out of an open subspace. -/
def puncturedNodeIncl : puncturedNodeSpace.{u} ⟶ AnalyticSpace.node.{u} :=
  AnalyticSpace.ofRestrict _ _

/-! ### It is disconnected -/

/-- The point of the node whose `j`-th coordinate is `1` and whose other coordinate is `0`: a
point of the `j`-th axis other than the origin. -/
def axisPoint (j : ULift.{u} (Fin 2)) : AnalyticSpace.node.{u} := by
  classical
  refine ⟨⟨fun l ↦ if l = j then 1 else 0, trivial⟩, (mem_zeroLocus_nodeSection_iff _).2 ?_⟩
  dsimp only
  rcases eq_or_ne (ULift.up 0 : ULift.{u} (Fin 2)) j with h | h
  · rw [if_neg (fun hcon : (ULift.up 1 : ULift.{u} (Fin 2)) = j ↦ by
      simpa using congrArg ULift.down (h.trans hcon.symm)), mul_zero]
  · rw [if_neg h, zero_mul]

lemma axisPoint_coord (j l : ULift.{u} (Fin 2)) :
    (axisPoint.{u} j).1.1 l = if l = j then 1 else 0 := rfl

lemma axisPoint_mem (j : ULift.{u} (Fin 2)) : axisPoint.{u} j ∈ puncturedNode.{u} := by
  have key : (axisPoint.{u} j).1.1 j ≠ 0 := by
    rw [axisPoint_coord, if_pos rfl]
    exact one_ne_zero
  rcases j with ⟨j⟩
  fin_cases j
  · exact Or.inl key
  · exact Or.inr key

/-- **The node minus the origin is disconnected.**

The first punctured axis is clopen in it: open because it is `{z₀ ≠ 0}`, and closed because on
the punctured node its complement is `{z₁ ≠ 0}` — a point with `z₀ = 0` must have `z₁ ≠ 0` to be
in the punctured node, and a point with `z₁ ≠ 0` must have `z₀ = 0` because `z₀ z₁ = 0` on the
node. It is neither empty nor everything: `(1, 0)` is in it and `(0, 1)` is not.

This is what makes the punctured node worth having beyond witnessing that
`AnalyticSpace.restrict` is not vacuous: it is an analytic space with a two-element open cover
by *disjoint* nonempty opens, so a pair of morphisms out of the two pieces is subject to no
compatibility condition at all. Whether some other analytic space already in this development
has that property is not investigated. -/
theorem not_preconnectedSpace_puncturedNodeSpace :
    ¬ PreconnectedSpace puncturedNodeSpace.{u} := by
  intro hconn
  set S : Set puncturedNodeSpace.{u} :=
    {q | (q.1 : AnalyticSpace.node.{u}).1.1 (ULift.up 0) ≠ 0} with hS
  have hcompl : Sᶜ = {q : puncturedNodeSpace.{u} |
      (q.1 : AnalyticSpace.node.{u}).1.1 (ULift.up 1) ≠ 0} := by
    ext q
    have hmul : (q.1 : AnalyticSpace.node.{u}).1.1 (ULift.up 0) *
        (q.1 : AnalyticSpace.node.{u}).1.1 (ULift.up 1) = 0 :=
      (mem_zeroLocus_nodeSection_iff _).1 q.1.2
    constructor
    · intro h0
      rcases q.2 with h | h
      · exact absurd (not_not.1 h0) h
      · exact h
    · intro h1 h0
      exact h1 ((mul_eq_zero.1 hmul).resolve_left h0)
  have hopen : IsOpen S :=
    isOpen_compl_singleton.preimage ((continuous_apply (ULift.up 0)).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  have hopen' : IsOpen Sᶜ := by
    rw [hcompl]
    exact isOpen_compl_singleton.preimage ((continuous_apply (ULift.up 1)).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  have hclopen : IsClopen S := ⟨isOpen_compl_iff.1 hopen', hopen⟩
  have hne : S.Nonempty :=
    ⟨⟨axisPoint.{u} (ULift.up 0), axisPoint_mem _⟩, by
      change (axisPoint.{u} (ULift.up 0)).1.1 (ULift.up 0) ≠ 0
      rw [axisPoint_coord, if_pos rfl]
      exact one_ne_zero⟩
  have hmem : (⟨axisPoint.{u} (ULift.up 1), axisPoint_mem _⟩ : puncturedNodeSpace.{u}) ∈ S := by
    rw [hclopen.eq_univ hne]
    trivial
  refine hmem ?_
  change (axisPoint.{u} (ULift.up 1)).1.1 (ULift.up 0) = 0
  rw [axisPoint_coord, if_neg]
  intro hcon
  simpa using congrArg ULift.down hcon

/-! ### The structure is usable, not merely well typed -/

/-- **A section of `𝒪` on the punctured node has the value it should.**

`AnalyticSpace.restrict` produces a `local_model` field, which is a `Prop`, so it cannot be
"wrong" the way a construction can — but it is what
`ComplexAnalytic.AnalyticSpace.residueFieldEquiv` and hence `AnalyticSpace.eval` are built from,
so until something evaluates a section on `puncturedNodeSpace` the space is only well typed.
This computes the value of the pullback of `nodeCoord j` at a point, through the analytic-space
structure the restriction produced, and gets the coordinate of the point — the same number
`ComplexAnalytic.eval_nodeCoord` gives on the node itself. -/
theorem eval_pullback_nodeCoord (p : puncturedNodeSpace.{u}) (j : ULift.{u} (Fin 2)) :
    puncturedNodeSpace.{u}.eval (U := ⊤) p trivial
        ((LocallyRingedSpace.Γ.map puncturedNodeIncl.{u}.toLRSHom.op).hom (nodeCoord.{u} j)) =
      (p.1 : AnalyticSpace.node.{u}).1.1 j := by
  refine Eq.trans (AnalyticSpace.eval_c_app (Z := puncturedNodeSpace.{u})
    (W := AnalyticSpace.node.{u}) puncturedNodeIncl.{u}.toLRSHom puncturedNodeIncl.{u}.isCLinear
    (U := ⊤) p trivial (nodeCoord.{u} j)) ?_
  exact eval_nodeCoord _ j

/-! ### The inclusion is the honest inclusion -/

/-- **The inclusion of the punctured node into the node is injective on points and not
surjective.** Injectivity says the morphism is not collapsing the subspace; non-surjectivity —
the origin is not in the image — says the subspace really is proper, at the level of the
*morphism* rather than of the open set it was built from. -/
theorem injective_base_puncturedNodeIncl :
    Function.Injective (puncturedNodeIncl.{u}).toLRSHom.base ∧
      ¬ Function.Surjective (puncturedNodeIncl.{u}).toLRSHom.base := by
  refine ⟨fun a b h ↦ Subtype.ext (by exact h), fun hsurj ↦ ?_⟩
  obtain ⟨q, hq⟩ := hsurj nodeOrigin.{u}
  have hq' : (q.1 : AnalyticSpace.node.{u}) = nodeOrigin.{u} := hq
  exact (mem_puncturedNode_iff _).1 q.2 hq'

end

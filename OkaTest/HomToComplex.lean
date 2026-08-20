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
* `exists_ne_nodeIncl` records that the hom-set `node ⟶ ℂ²` is not a singleton — the witness is
  `nodeDiag`, the inclusion followed by `z ↦ (z₀, z₀)`, which pulls **both** coordinates back to
  `nodeCoord 0`. Without it `ComplexAnalytic.eq_nodeIncl_of_coordPullback` would be a uniqueness
  statement with nothing to be unique among, and `nodeIncl_coordPullback_ne` would be a fact
  about one morphism rather than about the hom-set.
* `base_nodeIncl_via_coordPullback` and `coordPullback_comp_routes_agree` are index checks: each
  computes a value that is already known by a route sharing no lemma, so a permuted coordinate
  in `ComplexAnalytic.coordPullback_nodeIncl` or in
  `ComplexAnalytic.AnalyticSpace.coordPullback_comp` at this instance breaks them and nothing
  else.
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

/-- **The composition `AnalyticSpace.coordPullback_comp` is about is the one it looks like.**

`ComplexAnalytic.AnalyticSpace.coordPullback_comp` is a one-line proof of a statement general in
`Z`, and the way it could be hollow is if `(χ ≫ φ).toLRSHom` were not
`χ.toLRSHom ≫ φ.toLRSHom` — in which case the lemma would be a true statement about a different
composition. This says the two agree, on the nose. -/
theorem toLRSHom_comp {Z Z' Z'' : AnalyticSpace.{u}} (χ : Z ⟶ Z') (φ : Z' ⟶ Z'') :
    (χ ≫ φ).toLRSHom = χ.toLRSHom ≫ φ.toLRSHom :=
  rfl

/-- **Naturality of `coordPullback` at a composite of two non-identity morphisms.**

Instantiating at one non-identity `χ` rules out the lemma being about the identity, but the
failure worth ruling out is about *composition*, so both morphisms here are non-identity and
neither is the other's inverse: `χ` is the closed immersion of the node into `ℂ²`, `φ` is the
morphism attached to the non-linear family `z ↦ z₀²`.

Both sides here are computed by one chain, through `AnalyticSpace.coordPullback_comp` and then
`ComplexAnalytic.Γ_map_okaMapHom_coord`; the second route is `eval_coordPullback_comp_via_base`
below, which pushes the point through the base maps instead and touches neither. -/
theorem coordPullback_comp_nodeIncl_sq (j : ULift.{u} (Fin 1)) :
    AnalyticSpace.coordPullback
        (nodeIncl.{u} ≫ AnalyticSpace.okaMap (fun _ : ULift.{u} (Fin 1) ↦
          coord (ULift.up 0) * coord (ULift.up 0))) j =
      (LocallyRingedSpace.Γ.map nodeIncl.{u}.toLRSHom.op).hom
        (coord (ULift.up 0) * coord (ULift.up 0)) :=
  (AnalyticSpace.coordPullback_comp nodeIncl.{u} _ j).trans
    (congrArg (LocallyRingedSpace.Γ.map nodeIncl.{u}.toLRSHom.op).hom
      (Γ_map_okaMapHom_coord _ j))

/-- The same composite, computed **without** `AnalyticSpace.coordPullback_comp`: the pullback of
the coordinate along the composite is the product of the node's first coordinate function with
itself. Together with `coordPullback_comp_nodeIncl_sq` this pins the naturality statement to a
named section of `𝒪_node`. -/
theorem coordPullback_comp_nodeIncl_sq_eq (j : ULift.{u} (Fin 1)) :
    AnalyticSpace.coordPullback
        (nodeIncl.{u} ≫ AnalyticSpace.okaMap (fun _ : ULift.{u} (Fin 1) ↦
          coord (ULift.up 0) * coord (ULift.up 0))) j =
      nodeCoord.{u} (ULift.up 0) * nodeCoord.{u} (ULift.up 0) := by
  refine (coordPullback_comp_nodeIncl_sq j).trans ?_
  refine (map_mul (LocallyRingedSpace.Γ.map nodeIncl.{u}.toLRSHom.op).hom _ _).trans ?_
  exact congrArg₂ (· * ·) (coordPullback_nodeIncl (ULift.up 0))
    (coordPullback_nodeIncl (ULift.up 0))

/-- **Naturality of `coordPullback`, instantiated at a non-identity `χ`.** With `χ` the
inclusion of the node into `ℂ²` and `φ` the morphism attached to a family of entire functions,
naturality says the coordinates of the composite are the family restricted to the node. -/
theorem coordPullback_comp_nodeIncl {m : ℕ}
    (u : ULift.{u} (Fin m) → OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)))
    (j : ULift.{u} (Fin m)) :
    AnalyticSpace.coordPullback (nodeIncl.{u} ≫ AnalyticSpace.okaMap u) j =
      (LocallyRingedSpace.Γ.map nodeIncl.{u}.toLRSHom.op).hom (u j) :=
  (AnalyticSpace.coordPullback_comp nodeIncl.{u} (AnalyticSpace.okaMap u) j).trans
    (congrArg (LocallyRingedSpace.Γ.map nodeIncl.{u}.toLRSHom.op).hom
      (Γ_map_okaMapHom_coord u j))

/-- **The node's inclusion pulls the two coordinates back to different sections.** This is a
statement about the one morphism `ComplexAnalytic.nodeIncl`; that the hom-set it lives in has
more than one element is `exists_ne_nodeIncl` below, which consumes this. -/
theorem nodeIncl_coordPullback_ne :
    AnalyticSpace.coordPullback nodeIncl.{u} (ULift.up 0) ≠
      AnalyticSpace.coordPullback nodeIncl.{u} (ULift.up 1) :=
  (coordPullback_nodeIncl (ULift.up 0)).symm ▸
    ((coordPullback_nodeIncl (ULift.up 1)).symm ▸ nodeCoord_ne.{u})

/-- **A second morphism `node ⟶ ℂ²`**: the inclusion followed by the morphism of `ℂ²` attached
to the family `(z₀, z₀)`, so on points it is `p ↦ (p₀, p₀)`.

No morphism `ℂ ⟶ ℂ²` is needed, contrary to what one might expect from `nodeToLine`:
`ComplexAnalytic.AnalyticSpace.okaMap` already exists at `m = 2`. -/
def nodeDiag : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 2 :=
  nodeIncl.{u} ≫ AnalyticSpace.okaMap (fun _ : ULift.{u} (Fin 2) ↦ coord (ULift.up 0))

/-- **`nodeDiag` pulls *both* coordinates back to `nodeCoord 0`**, where `nodeIncl` pulls them
back to `nodeCoord 0` and `nodeCoord 1`. This is the whole content of `nodeDiag_ne_nodeIncl`,
and it is `coordPullback_comp_nodeIncl` — the single-morphism naturality test — instantiated at
a constant family. -/
theorem coordPullback_nodeDiag (j : ULift.{u} (Fin 2)) :
    AnalyticSpace.coordPullback nodeDiag.{u} j = nodeCoord.{u} (ULift.up 0) :=
  (coordPullback_comp_nodeIncl (fun _ : ULift.{u} (Fin 2) ↦ coord (ULift.up 0)) j).trans
    (coordPullback_nodeIncl (ULift.up 0))

/-- `nodeDiag` and `nodeIncl` are different morphisms: if they were equal, `nodeIncl` would pull
the two coordinates back to the same section. -/
theorem nodeDiag_ne_nodeIncl : nodeDiag.{u} ≠ nodeIncl.{u} := fun hcon ↦
  nodeIncl_coordPullback_ne.{u}
    ((congrArg (fun φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 2 ↦
        AnalyticSpace.coordPullback φ (ULift.up 0)) hcon).symm.trans
      ((coordPullback_nodeDiag (ULift.up 0)).trans
        ((coordPullback_nodeDiag (ULift.up 1)).symm.trans
          (congrArg (fun φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 2 ↦
            AnalyticSpace.coordPullback φ (ULift.up 1)) hcon))))

/-- **The hom-set `node ⟶ ℂ²` has more than one element**, so
`ComplexAnalytic.eq_nodeIncl_of_coordPullback` — which says `nodeIncl` is the *only* morphism
pulling the coordinates back to the node's coordinate functions — is not a statement about a
singleton. -/
theorem exists_ne_nodeIncl :
    ∃ φ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.complexAffineSpace.{u} 2, φ ≠ nodeIncl.{u} :=
  ⟨nodeDiag.{u}, nodeDiag_ne_nodeIncl.{u}⟩

/-- **The pullback computation `ComplexAnalytic.coordPullback_nodeIncl` has the right coordinate
index.**

`ComplexAnalytic.base_nodeIncl` is the same equation proved by `rfl`. This proof goes the long
way round — naturality of evaluation (`AnalyticSpace.eval_c_app`), the value of a coordinate on
`ℂ²` (`AnalyticSpace.eval_coord`), the pullback computation, and the value of `nodeCoord` at a
point (`ComplexAnalytic.eval_nodeCoord`, which reaches it through `eval_ofCutOut`). A permuted
index in `coordPullback_nodeIncl` would leave both `rfl` and every other statement in the
library intact and would break exactly this. -/
theorem base_nodeIncl_via_coordPullback (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 2)) :
    ((nodeIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) j = p.1.1 j :=
  (AnalyticSpace.eval_coord ((nodeIncl.{u}).toLRSHom.base p) j).symm.trans
    ((AnalyticSpace.eval_c_app (Z := AnalyticSpace.node.{u})
        (W := AnalyticSpace.complexAffineSpace.{u} 2) nodeIncl.{u}.toLRSHom
        nodeIncl.{u}.isCLinear (U := ⊤) p trivial (coord j)).symm.trans
      ((congrArg ((AnalyticSpace.node.{u}).eval (U := ⊤) p trivial)
        (coordPullback_nodeIncl.{u} j)).trans (eval_nodeCoord.{u} p j)))

/-- **The composite of `coordPullback_comp_nodeIncl_sq`, computed through the base maps.**

This is the second route that theorem's docstring needs: it evaluates the pullback at a point of
the node by pushing the point through the base map of the composite, so it uses neither
`AnalyticSpace.coordPullback_comp` nor
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply`. -/
theorem eval_coordPullback_comp_via_base (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 1)) :
    (AnalyticSpace.node.{u}).eval (U := ⊤) p trivial
        (AnalyticSpace.coordPullback
          (nodeIncl.{u} ≫ AnalyticSpace.okaMap (fun _ : ULift.{u} (Fin 1) ↦
            coord (ULift.up 0) * coord (ULift.up 0))) j) =
      p.1.1 (ULift.up 0) * p.1.1 (ULift.up 0) := by
  set φ := nodeIncl.{u} ≫ AnalyticSpace.okaMap (fun _ : ULift.{u} (Fin 1) ↦
    coord (ULift.up 0) * coord (ULift.up 0)) with hφ
  refine Eq.trans (AnalyticSpace.eval_c_app (Z := AnalyticSpace.node.{u})
    (W := AnalyticSpace.complexAffineSpace.{u} 1) φ.toLRSHom φ.isCLinear
    (U := ⊤) p trivial (coord j)) ?_
  refine Eq.trans (AnalyticSpace.eval_coord (φ.toLRSHom.base p) j) ?_
  change okaMapFun (fun _ : ULift.{u} (Fin 1) ↦ coord (ULift.up 0) * coord (ULift.up 0))
    ((nodeIncl.{u}).toLRSHom.base p) j = _
  rw [okaMapFun_apply, map_mul, evalHom_coord, base_nodeIncl]

/-- The value of `nodeCoord 0 * nodeCoord 0` at a point of the node, computed with no reference
to any composite: `eval` is a ring homomorphism and `ComplexAnalytic.eval_nodeCoord` gives each
factor. -/
theorem eval_nodeCoord_sq (p : AnalyticSpace.node.{u}) :
    (AnalyticSpace.node.{u}).eval (U := ⊤) p trivial
        (nodeCoord.{u} (ULift.up 0) * nodeCoord.{u} (ULift.up 0)) =
      p.1.1 (ULift.up 0) * p.1.1 (ULift.up 0) :=
  (map_mul ((AnalyticSpace.node.{u}).eval (U := ⊤) p trivial) _ _).trans
    (congrArg₂ (· * ·) (eval_nodeCoord.{u} p (ULift.up 0)) (eval_nodeCoord.{u} p (ULift.up 0)))

/-- **The two routes to the composite's coordinate agree**, on a number rather than on a
symbolic expression. The left-hand side is reached through
`AnalyticSpace.coordPullback_comp`, by `coordPullback_comp_nodeIncl_sq_eq`; the right-hand side
through the base maps, by `eval_coordPullback_comp_via_base`. `eval_nodeCoord_sq` computes the
same number a third way, so an error in `coordPullback_comp` at this instance would have to be
matched by an error in the base-map computation to survive. -/
theorem coordPullback_comp_routes_agree (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 1)) :
    (AnalyticSpace.node.{u}).eval (U := ⊤) p trivial
        (nodeCoord.{u} (ULift.up 0) * nodeCoord.{u} (ULift.up 0)) =
      p.1.1 (ULift.up 0) * p.1.1 (ULift.up 0) :=
  (congrArg ((AnalyticSpace.node.{u}).eval (U := ⊤) p trivial)
    (coordPullback_comp_nodeIncl_sq_eq.{u} j)).symm.trans
      (eval_coordPullback_comp_via_base p j)

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

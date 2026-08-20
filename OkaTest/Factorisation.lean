/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the mapping property of `IsCutOutBy`, in both categories

`ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` says that a `ℂ`-linear morphism killing the
sections which cut out a subspace factors uniquely through that subspace, as a morphism of
complex analytic spaces. **It would be true and empty if its hypotheses held only at the
identity**, or if the `∃!` were about a hom-set with one element for a reason having nothing to
do with the theorem. This file rules that out at the node.

* `c_app_nodeSection_eq_zero` shows the hypothesis `hφ` is **the node's equation**: the
  pullbacks of the two coordinates multiply to zero (`ComplexAnalytic.nodeCoord_mul`), and that
  is literally what `φ.c.app ⊤ (nodeSection j) = 0` says once `nodePoly` is expanded. So the
  hypothesis is not a technical side condition; it is `z₀ z₁ = 0`.
* `eq_id_of_comp_zeroLocusSubspaceι` runs the theorem where the answer is known: the node's own
  closed immersion factors through the node, and the factorisation has to be the **identity**.
  If it came out as anything else the theorem would be about the wrong morphism.
* `exists_liftHom` records that the factorisation the theorem produces really does compose back
  to `φ`, which is the half of `∃!` that uniqueness cannot supply.
* `existsUnique_axisIncl` runs the theorem where the answer is **not** known. Its `φ` is the map
  `z ↦ (z, 0)` of `ℂ ⟶ ℂ²`, assembled from two global sections of `𝒪_ℂ` by
  `ComplexAnalytic.AnalyticSpace.okaMap`; its source is not the node and it is a factorisation
  of nothing. What comes back is the inclusion of one axis — the first morphism `ℂ ⟶ node` in
  the development. `base_axisIncl` **computes** its base map from the equation it satisfies
  rather than unfolding `lift`, and `not_const_axisIncl` rules out the remaining degeneracy.
  `base_axisIncl_pair` states both coordinates of the image together, so that *"it is the
  inclusion of the first axis"* is one proposition rather than two theorems and a sentence, and
  `image_axisIncl_on_node` says the image satisfies the node's equation arithmetically rather
  than only by having the right type.

**What this does not check.** That `existsUnique_liftHom` is applied to a `φ` built from global
sections on a *general* `Z`; that needs the general-`Z` half of taxis #654, which does not
exist. The case `Z = ℂ^n` is available today through `ComplexAnalytic.AnalyticSpace.okaMap` and
is done below.

**What is still open, and should not be quietly absorbed.** Whether `Hom(node, node)` has more
than one element. `eq_id_of_comp_zeroLocusSubspaceι` and `exists_liftHom` would *both* hold if
it did not: the second is the first's `∃!` read for existence, and `𝟙` witnesses it through
`Category.id_comp`. Nothing in the development builds a second endomorphism of the node, and
`existsUnique_axisIncl`'s source is `ℂ` rather than the node, so it does not settle it either.

The last section does the same for the **locally ringed space** form,
`ComplexAnalytic.IsCutOutBy.existsUnique_lift`, and for
`ComplexAnalytic.IsCutOutBy.uniqueIso`. Neither is instantiated by anything above — the
analytic-space theorem is assembled from `lift`, `lift_comp` and `hom_ext` rather than from
`existsUnique_lift`, and `uniqueIso` does not appear there at all — so they are tested
separately.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-- The hypothesis `hφ` of `existsUnique_liftHom`, at the node's own closed immersion, **is the
node's equation** `z₀ z₁ = 0` — reached through `ComplexAnalytic.nodeCoord_mul`, a statement
about the two coordinate *functions* on the node, rather than through
`IsCutOutBy.c_app_eq_zero`, which is the generic reason. -/
theorem c_app_nodeSection_eq_zero (j : Fin 1) :
    (((nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}).c.app (op ⊤)).hom
      (nodeSection.{u} j)) = 0 := by
  refine Eq.trans ?_ nodeCoord_mul.{u}
  refine Eq.trans (congrArg
    ((LocallyRingedSpace.Γ.map (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}).op).hom)
    (show nodeSection.{u} j =
        OkaRing.ofMvPolynomial _ (MvPolynomial.X (ULift.up 0)) *
          OkaRing.ofMvPolynomial _ (MvPolynomial.X (ULift.up 1)) from
      (map_mul (OkaRing.ofMvPolynomial _) _ _))) ?_
  exact map_mul _ _ _

/-- The analytic space the mapping property produces for the node's own cut-out family **is**
the node. Stated separately because it is a `rfl` that the elaborator will not find while it is
also solving for `n`, `k` and `V`. -/
theorem ofCutOut_nodeSection_eq_node :
    AnalyticSpace.ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}) =
      AnalyticSpace.node.{u} :=
  rfl

/-- The mapping property, instantiated at the node: its own closed immersion factors through it.
The `∃!` is recorded here once so that the two consequences below do not each pay for
elaborating it.

`n`, `k`, `V` and `W` are supplied explicitly. Left to unification the elaborator does not
finish inside the default heartbeat budget: it has to solve `?V.isOpenEmbedding` against
`nodeAmbient`'s `⊤.isOpenEmbedding` while simultaneously matching `constantsAlgMap ?n ?V`
against `constantsAlgMap 2 ⊤` in `hlin`. Naming them costs four annotations and takes the
elaboration from a timeout to a second. -/
theorem existsUnique_liftHom_node :
    ∃! ψ : AnalyticSpace.node.{u} ⟶
        AnalyticSpace.ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}),
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} =
        nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} :=
  IsCutOutBy.existsUnique_liftHom (W := AnalyticSpace.node.{u}) (n := 2) (k := 1) (V := ⊤)
    (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u})
    (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u})
    isCLinearHom_zeroLocusSubspaceι_nodeSection.{u} c_app_nodeSection_eq_zero.{u}

/-- **The node's own closed immersion factors through the node, and the factorisation is the
identity.** This is the theorem run where the answer is known independently: a factorisation
that came out as anything else would mean the theorem is about the wrong morphism. -/
theorem eq_id_of_comp_zeroLocusSubspaceι
    (ψ : AnalyticSpace.node.{u} ⟶
      AnalyticSpace.ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}))
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} =
      nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}) :
    ψ = 𝟙 AnalyticSpace.node.{u} :=
  (existsUnique_liftHom_node.{u}.unique hψ (Category.id_comp _))

/-- The existence half, which uniqueness cannot supply: the factorisation composes back to the
morphism it factors. -/
theorem exists_liftHom :
    ∃ ψ : AnalyticSpace.node.{u} ⟶
        AnalyticSpace.ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}),
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} =
        nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} :=
  existsUnique_liftHom_node.{u}.exists

/-! ### A `φ` which is not already a factorisation, and the first morphism `ℂ ⟶ node`

Everything above runs the mapping property where the answer is forced. This section runs it
where it is not: `axisPhi` is the morphism `z ↦ (z, 0)` of `ℂ ⟶ ℂ²`, assembled from two global
sections of `𝒪_ℂ` by `ComplexAnalytic.okaMapHom`, and the morphism `existsUnique_liftHom`
returns for it is the inclusion of one axis of the node.

**The one obstacle, recorded so that nobody rediscovers it.**
`LocallyRingedSpace.Γ.map ((complexAffineSpace 2).restrictTopIso.inv).op` is an `eqToHom`, not a
`rfl`: it is what bridges the two presentations of `ℂ²` that this development uses — the
`complexAffineSpace 2` that `okaMapHom` maps into, and the `nodeAmbient = ℂ²|⊤` that
`IsCutOutBy` and `existsUnique_liftHom` demand. It is not even a `rfl` that fails, because the
two global-section rings are different types. The route below does not compute it at all:
`nodeSection` is rewritten as a pullback along `restrictTopIso.hom`, which *is* a `rfl`, and the
pair then collapses through `inv_hom_id` and `LocallyRingedSpace.Γ_map_comp_apply`.
-/

/-- The family `(z, 0)` of two entire functions on `ℂ¹`, which is the morphism `ℂ ⟶ ℂ²` onto
the first coordinate axis. -/
def axisFamily : ULift.{u} (Fin 2) → OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  fun j ↦ if j = ULift.up 0 then coord (ULift.up 0) else 0

/-- The morphism `z ↦ (z, 0)` of `ℂ ⟶ ℂ²`, landing in the `restrict ⊤` presentation of `ℂ²`
that `IsCutOutBy` uses. -/
def axisPhi : (AnalyticSpace.complexAffineSpace.{u} 1).toLocallyRingedSpace ⟶ nodeAmbient.{u} :=
  okaMapHom axisFamily.{u} ≫ (complexAffineSpace.{u} 2).restrictTopIso.inv

/-- The inverse of `restrictTopIso` is `ℂ`-linear. No transport is needed: it is `ℂ`-linear
because its composite with `ofRestrict` is the identity, which is
`ComplexAnalytic.IsCLinearHom.of_comp`. -/
theorem isCLinearHom_restrictTopIso_inv :
    IsCLinearHom ((complexAffineSpace.{u} 2).restrictTopIso.inv)
      (Algebra.algebraMap ℂ (OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ))))
      (constantsAlgMap 2 ⊤) :=
  IsCLinearHom.of_comp (q := (complexAffineSpace.{u} 2).ofRestrict
      (⊤ : Opens (complexAffineSpace.{u} 2)).isOpenEmbedding)
    ((complexAffineSpace.{u} 2).restrictTopIso.inv_hom_id)
    (IsCLinearHom.id _) (isCLinearHom_ofRestrict_complexSpace ⊤)

theorem isCLinearHom_axisPhi :
    IsCLinearHom axisPhi.{u}
      (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap (constantsAlgMap 2 ⊤) :=
  (isCLinearHom_okaMapHom axisFamily.{u}).comp isCLinearHom_restrictTopIso_inv.{u}

/-- `nodeSection` is the pullback of the polynomial `z₀ z₁` along `restrictTopIso.hom`, on the
nose. This is the equation that makes the `eqToHom` above avoidable. -/
theorem nodeSection_eq (j : Fin 1) :
    nodeSection.{u} j =
      (LocallyRingedSpace.Γ.map ((complexAffineSpace.{u} 2).restrictTopIso.hom).op).hom
          (OkaRing.ofMvPolynomial ⊤ nodePoly.{u}) :=
  rfl

/-- Crossing `restrictTopIso` in both directions is the identity on global sections — proved
without computing either direction, from `inv_hom_id` alone. -/
theorem Γ_map_restrictTopIso_inv_hom (P : OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ))) :
    (LocallyRingedSpace.Γ.map ((complexAffineSpace.{u} 2).restrictTopIso.inv).op).hom
        ((LocallyRingedSpace.Γ.map ((complexAffineSpace.{u} 2).restrictTopIso.hom).op).hom P) =
      P :=
  (LocallyRingedSpace.Γ_map_comp_apply ((complexAffineSpace.{u} 2).restrictTopIso.inv)
      ((complexAffineSpace.{u} 2).restrictTopIso.hom) P).symm.trans
    ((congrArg (fun m : complexAffineSpace.{u} 2 ⟶ complexAffineSpace.{u} 2 ↦
        (LocallyRingedSpace.Γ.map m.op).hom P)
      ((complexAffineSpace.{u} 2).restrictTopIso.inv_hom_id)).trans
      (LocallyRingedSpace.Γ_map_id_apply (complexAffineSpace.{u} 2) P))

/-- **The morphism `z ↦ (z, 0)` of `ℂ ⟶ ℂ²` kills the node's equation `z₀ z₁`**, so it satisfies
the hypothesis `hφ` of the mapping property. The second coordinate of the family is `0`, and
that is the whole content. -/
theorem c_app_axisPhi_nodeSection (j : Fin 1) :
    ((axisPhi.{u}).c.app (op ⊤)).hom (nodeSection.{u} j) = 0 :=
  (congrArg ((LocallyRingedSpace.Γ.map (axisPhi.{u}).op).hom) (nodeSection_eq.{u} j)).trans
    ((LocallyRingedSpace.Γ_map_comp_apply (okaMapHom axisFamily.{u})
        ((complexAffineSpace.{u} 2).restrictTopIso.inv) _).trans
      ((congrArg ((LocallyRingedSpace.Γ.map (okaMapHom axisFamily.{u}).op).hom)
          ((Γ_map_restrictTopIso_inv_hom.{u} _).trans
            (map_mul (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)))
              (MvPolynomial.X (ULift.up 0)) (MvPolynomial.X (ULift.up 1))))).trans
        ((map_mul ((LocallyRingedSpace.Γ.map (okaMapHom axisFamily.{u}).op).hom)
            (coord (ULift.up 0)) (coord (ULift.up 1))).trans
          ((congrArg₂ (· * ·) (Γ_map_okaMapHom_coord axisFamily.{u} (ULift.up 0))
              (Γ_map_okaMapHom_coord axisFamily.{u} (ULift.up 1))).trans
            ((congrArg (axisFamily.{u} (ULift.up 0) * ·)
                (show axisFamily.{u} (ULift.up 1) = 0 from if_neg (by simp))).trans
              (mul_zero _))))))

/-- **The mapping property applied to a `φ` which is not already a factorisation.** `axisPhi` is
built from two global sections of `𝒪_ℂ` by `ComplexAnalytic.okaMapHom`, its source is `ℂ` rather
than the node, and it factors nothing. The target elaborates as `AnalyticSpace.node` itself,
which is `ofCutOut_nodeSection_eq_node` used rather than stated. -/
theorem existsUnique_axisIncl :
    ∃! ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u},
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u} :=
  IsCutOutBy.existsUnique_liftHom (W := AnalyticSpace.complexAffineSpace.{u} 1)
    (n := 2) (k := 1) (V := ⊤)
    (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}) axisPhi.{u}
    isCLinearHom_axisPhi.{u} c_app_axisPhi_nodeSection.{u}

/-- **Where the factorisation sends a point, recovered from the equation it satisfies.** This is
the load-bearing check of the section: it does not unfold `lift`, it reads the base map off
`hψ`, so an error anywhere in the mapping property's construction would show up here. -/
theorem base_axisIncl (ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u})
    (z : ULift.{u} (Fin 1) → ℂ) (l : ULift.{u} (Fin 2)) :
    ((ψ.toLRSHom.base z).1.1 l) = okaMapFun axisFamily.{u} z l :=
  congrArg
    (fun m : (AnalyticSpace.complexAffineSpace.{u} 1).toLocallyRingedSpace ⟶ nodeAmbient.{u} ↦
      ((m.base z : nodeAmbient.{u}).1 l)) hψ

/-- The first coordinate of the axis map is `z`. -/
theorem okaMapFun_axisFamily_zero (z : ULift.{u} (Fin 1) → ℂ) :
    okaMapFun axisFamily.{u} z (ULift.up 0) = z (ULift.up 0) :=
  (okaMapFun_apply axisFamily.{u} z (ULift.up 0)).trans
    ((congrArg (OkaRing.evalHom (U := ⊤) (x := z) trivial)
      (show axisFamily.{u} (ULift.up 0) = coord (ULift.up 0) from if_pos rfl)).trans
        (evalHom_coord (ULift.up 0)))

/-- The second coordinate of the axis map is `0`, which is why its image lies on the node. -/
theorem okaMapFun_axisFamily_one (z : ULift.{u} (Fin 1) → ℂ) :
    okaMapFun axisFamily.{u} z (ULift.up 1) = 0 :=
  (okaMapFun_apply axisFamily.{u} z (ULift.up 1)).trans
    ((congrArg (OkaRing.evalHom (U := ⊤) (x := z) trivial)
      (show axisFamily.{u} (ULift.up 1) = 0 from if_neg (by simp))).trans (map_zero _))

/-- **The morphism the mapping property produced is not constant**: `0` and `1` go to two
different points of the node. With `base_axisIncl` this identifies it as the inclusion of the
first axis. -/
theorem not_const_axisIncl (ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u}) :
    ψ.toLRSHom.base (fun _ ↦ (0 : ℂ)) ≠ ψ.toLRSHom.base (fun _ ↦ (1 : ℂ)) := by
  intro hcon
  have h0 := (base_axisIncl ψ hψ (fun _ ↦ (0 : ℂ)) (ULift.up 0)).symm.trans
    (congrArg (fun p : AnalyticSpace.node.{u} ↦ p.1.1 (ULift.up 0)) hcon)
  rw [base_axisIncl ψ hψ (fun _ ↦ (1 : ℂ)) (ULift.up 0), okaMapFun_axisFamily_zero,
    okaMapFun_axisFamily_zero] at h0
  exact zero_ne_one h0

/-- **A non-constant morphism of complex analytic spaces `ℂ ⟶ node` exists**, and it is the one
the mapping property produced.

`not_const_axisIncl` is a statement about an arbitrary `ψ` satisfying `hψ`, so on its own it
could be about nothing. This is the `⟨_, proof₁, proof₂⟩` shape: one existential whose witness is
fixed by the first component and consumed by the second, so the factorisation equation and the
non-constancy are provably about the same morphism. -/
theorem exists_nonconstant_hom_complexLine_node :
    ∃ ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u},
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u} ∧
        ψ.toLRSHom.base (fun _ ↦ (0 : ℂ)) ≠ ψ.toLRSHom.base (fun _ ↦ (1 : ℂ)) :=
  ⟨_, existsUnique_axisIncl.{u}.exists.choose_spec,
    not_const_axisIncl _ existsUnique_axisIncl.{u}.exists.choose_spec⟩

/-- **The image of the axis inclusion lies on the node**, computed rather than inferred from
the type.

That `ψ` lands in `AnalyticSpace.node` is forced by its type and so says nothing about the
construction. This says the same thing arithmetically: the second coordinate of the image is
`0`, so the product of the two coordinates — which is the node's equation — is `0`. It is what
gives `okaMapFun_axisFamily_one` a consumer; without it that theorem records a number nothing
reads. -/
theorem image_axisIncl_on_node
    (ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u})
    (z : ULift.{u} (Fin 1) → ℂ) :
    (ψ.toLRSHom.base z).1.1 (ULift.up 0) * (ψ.toLRSHom.base z).1.1 (ULift.up 1) = 0 := by
  rw [base_axisIncl ψ hψ z (ULift.up 1), okaMapFun_axisFamily_one, mul_zero]

/-- **Both coordinates of the image, named together: `z ↦ (z, 0)`.**

`base_axisIncl` is symbolic in `okaMapFun axisFamily`, and the two coordinate computations are
separate theorems, so nothing until now states the sentence *"the factorisation is the inclusion
of the first axis"* as one proposition. This does. -/
theorem base_axisIncl_pair
    (ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u})
    (z : ULift.{u} (Fin 1) → ℂ) :
    (ψ.toLRSHom.base z).1.1 (ULift.up 0) = z (ULift.up 0) ∧
      (ψ.toLRSHom.base z).1.1 (ULift.up 1) = 0 :=
  ⟨(base_axisIncl ψ hψ z (ULift.up 0)).trans (okaMapFun_axisFamily_zero z),
    (base_axisIncl ψ hψ z (ULift.up 1)).trans (okaMapFun_axisFamily_one z)⟩

/-! ### The locally ringed space form, which is a different statement

`ComplexAnalytic.IsCutOutBy.existsUnique_lift` and `ComplexAnalytic.IsCutOutBy.uniqueIso` are
still theorems of `Oka/AnalyticSpace/Factorisation.lean`, one category lower, and nothing above
instantiates either of them: `existsUnique_liftHom` is built from `lift`, `lift_comp` and
`hom_ext`, not from `existsUnique_lift`, and `uniqueIso` is not mentioned there at all. So they
need non-vacuity of their own, and it is here.
-/

variable {X Y : LocallyRingedSpace.{u}} {i : X ⟶ Y} {k : ℕ}
  {f : Fin k → Y.presheaf.obj (op ⊤)}

/-- **The factorisation of `i` through itself is the identity.** The construction is not merely
*some* morphism with the right source and target: on the one instance where the answer is
forced, it gives the right answer.

This is `eq_id_of_comp_zeroLocusSubspaceι` above with the node replaced by an arbitrary cut-out,
and neither implies the other: the analytic-space version fixes the space, and it pins the
*hypothetical* factorisation rather than the constructed one. -/
theorem lift_self (hcut : IsCutOutBy i f) : hcut.lift i hcut.c_app_eq_zero = 𝟙 X :=
  hcut.hom_ext _ _ (by rw [hcut.lift_comp, Category.id_comp])

/-- The mapping property at the node `{z ∈ ℂ² | z₀ z₁ = 0}`, a complex analytic space which is
not a manifold: a morphism of *locally ringed spaces* into `ℂ²` killing `z₀ z₁` factors uniquely
through the node. This is the one place `existsUnique_lift` itself is instantiated. -/
example (Z : LocallyRingedSpace.{u}) (φ : Z ⟶ nodeAmbient.{u})
    (hφ : ∀ j, φ.c.app (op ⊤) (nodeSection.{u} j) = 0) :
    ∃! ψ : Z ⟶ nodeAmbient.{u}.zeroLocusSubspace nodeSection.{u},
      ψ ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = φ :=
  (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}).existsUnique_lift φ hφ

/-- **Two presentations of the same subspace are canonically isomorphic**, and the isomorphism
is over `Y`. Instantiated at a genuinely different pair: `X'` here is any space isomorphic to
`X`, cut out by the same sections through the transported immersion
(`ComplexAnalytic.IsCutOutBy.comp_iso`). -/
example {X' : LocallyRingedSpace.{u}} (hcut : IsCutOutBy i f) (e : X' ≅ X) :
    (hcut.uniqueIso (hcut.comp_iso e)).hom ≫ (e.hom ≫ i) = i :=
  hcut.uniqueIso_hom_comp (hcut.comp_iso e)

/-- The other half, which never had an instantiation: the inverse of that isomorphism is over
`Y` too. Together with the previous example this says `uniqueIso` is an isomorphism **in the
slice over `Y`**, which is the content of "canonically". -/
example {X' : LocallyRingedSpace.{u}} (hcut : IsCutOutBy i f) (e : X' ≅ X) :
    (hcut.uniqueIso (hcut.comp_iso e)).inv ≫ i = e.hom ≫ i :=
  hcut.uniqueIso_inv_comp (hcut.comp_iso e)

end

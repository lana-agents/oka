/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the mapping property for morphisms of analytic spaces

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

**What this does not check.** That `existsUnique_liftHom` is ever applied to a `φ` which is not
already a factorisation — the interesting case for analytification is a morphism `Z ⟶ ℂ^n` built
from `n` global sections, which needs the existence half of taxis #654 and does not exist yet.
So this file tests that the theorem computes correctly, not that it is used.
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

end

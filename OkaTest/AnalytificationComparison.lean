/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.AnalytificationFunctor

/-!
# Non-vacuity of the naturality of `X^an ⟶ X`

`Oka/Analytification/Comparison.lean` makes the comparison morphism a natural transformation. A
naturality statement whose only instance is an identity morphism proves nothing, and a
transformation whose components nobody can compute is inert. This file rules out both, at the
node.

The witness is the one `OkaTest/AnalytificationChangeOfVariables.lean` already carries — the node
presented in two variables against the node presented in three, so that **both** indices of the
presentation differ — and the morphism used is `presHom23`, which is not an
identity and is not even an endomorphism.

What is checked:

* `analytificationToSpec_nodeTuple2_eq` — **the comparison morphism of the two-variable
  presentation is recovered from that of the three-variable one.** That is what naturality buys
  and it is not something the two constructions share by definition: the two spaces are
  analytifications of different tuples in different numbers of variables, and the two spectra are
  spectra of different quotients of different polynomial rings.
* `analytificationFGAlgToSpec_app_nodeAlg` — the algebra-level transformation has a computable
  component at the node's algebra, through `ComplexAnalytic.analytificationFGAlgToSpec_app`.
-/

open CategoryTheory Opposite AlgebraicGeometry
open ComplexAnalytic

universe u

noncomputable section

/-- The natural transformation's component at the node's two-variable presentation is the
comparison morphism that `Oka/Analytification/Presentation.lean` built. -/
theorem analytificationToSpecNatTrans_app_nodePres2 :
    analytificationToSpecNatTrans.{u}.app nodePres2.{u} =
      analytificationToSpec.{u} nodeTuple2.{u} :=
  rfl

/-- **The comparison morphism of the node's two-variable presentation is recovered from the
three-variable one**, by naturality at `presHom23` and its inverse.

Neither side of this is definitionally the other: the sources are the analytifications of
`nodeTuple2` and `nodeTuple3`, and the targets are the spectra of `ℂ[x, y] ⧸ (x y)` and
`ℂ[x, y, z] ⧸ (x y, z)`. -/
theorem analytificationToSpec_nodeTuple2_eq :
    analytificationToSpec.{u} nodeTuple2.{u} =
      (analytificationMap.{u} presHom23.{u}).toLRSHom ≫
        analytificationToSpec.{u} nodeTuple3.{u} ≫
          Spec.locallyRingedSpaceMap (CommRingCat.ofHom presHom32.{u}.toRingHom) := by
  rw [← Category.assoc, analytificationToSpec_naturality.{u} presHom23.{u}, Category.assoc,
    ← Spec.locallyRingedSpaceMap_comp]
  have h : CommRingCat.ofHom presHom32.{u}.toRingHom ≫
      CommRingCat.ofHom presHom23.{u}.toRingHom = 𝟙 _ :=
    CommRingCat.hom_ext presHom23_comp_presHom32.{u}
  rw [h, Spec.locallyRingedSpaceMap_id, Category.comp_id]

/-- The algebra-level transformation has a component at the node's algebra, and it is computed by
`ComplexAnalytic.analytificationFGAlgToSpec_app` rather than left opaque. -/
theorem analytificationFGAlgToSpec_app_nodeAlg :
    analytificationFGAlgToSpec.{u}.app (toFGAlg.{u}.obj nodePres2.{u}) =
      analytificationToSpec.{u}
          (toFGAlg.{u}.asEquivalence.inverse.obj (toFGAlg.{u}.obj nodePres2.{u})).g ≫
        (toCommRingCatOp.{u} ⋙ Spec.toLocallyRingedSpace.{u}).map
          (toFGAlg.{u}.asEquivalence.counitIso.hom.app (toFGAlg.{u}.obj nodePres2.{u})) :=
  analytificationFGAlgToSpec_app.{u} _

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.AnalytificationChangeOfVariables

/-!
# Non-vacuity of the analytification functor: the node, with no presentation in the statement

`Oka/Analytification/Functor.lean` bundles the analytification as a functor twice over — on
presentations, and then on finitely generated `ℂ`-algebras, where the presentation has been
removed by an equivalence of categories. **Both would be true and empty if the only morphisms of
presentations were identities**, and the second would be true and useless if nothing connected
`ComplexAnalytic.analytificationFGAlg` back to a concrete space.

This file rules out both, reusing the witness of
`OkaTest/AnalytificationChangeOfVariables.lean`: the node presented in two variables against the
node presented in three,

```
ℂ[x, y] ⧸ (x y)        against        ℂ[x, y, z] ⧸ (x y, z)
```

so that **both indices of the presentation differ** — a category structure that had accidentally
fixed either would fail to elaborate here.

What is checked:

* `nodePresIso` — the two presentations are isomorphic *as objects of the category*, from the two
  `ComplexAnalytic.PresHom`s already built, so the category is not discrete;
* `nodeAlgIso` — hence the two *algebras* are isomorphic in `CommAlgCat ℂ`, which is what makes
  the second functor applicable to one and the same object;
* `nodeIsoAnalytificationFGAlg` — **the analytification of the algebra is the node**, a statement
  whose left-hand side names no presentation at all, obtained from
  `ComplexAnalytic.analytificationFGAlgObjIso`. This is the test that the equivalence-based
  definition is not inert.

`AnalyticSpace.node` is `ComplexAnalytic.AnalyticSpace.analytification nodeTuple2` definitionally
(`node_eq_analytification_nodeTuple2`, in the file this one imports), which is why the node can
appear on the right of these isomorphisms without a transport.

The identity test at the node deliberately does **not** go through
`ComplexAnalytic.hom_ext_analytification`: at this concrete instance that route times out `whnf`
at 200000 heartbeats, because it goes through `cancel_mono` and hence typeclass search. Every
identity below comes from `ComplexAnalytic.PresHom.ext` at the level of ring maps instead, where
the two composition identities were already proved.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open ComplexAnalytic

universe u

noncomputable section

/-- The node, presented in two variables. -/
def nodePres2 : Presentation.{u} := ⟨2, 1, nodeTuple2.{u}⟩

/-- The node, presented in three. -/
def nodePres3 : Presentation.{u} := ⟨3, 2, nodeTuple3.{u}⟩

/-- The two presentations are different objects: they do not even have the same number of
variables. Without this the isomorphism below could be one of an object with itself. -/
theorem nodePres2_ne_nodePres3 : nodePres2.{u} ≠ nodePres3.{u} := by
  intro h
  exact absurd (congrArg Presentation.n h) (by decide)

/-- Dropping the third variable, as a morphism of presentations. -/
def nodePresHom : nodePres2.{u} ⟶ nodePres3.{u} := presHom23.{u}

/-- Adjoining it again. -/
def nodePresInv : nodePres3.{u} ⟶ nodePres2.{u} := presHom32.{u}

/-- **The two presentations are isomorphic in the category of presentations.**

Both round trips are `ComplexAnalytic.PresHom.ext` applied to the ring-map identities of
`OkaTest/AnalytificationChangeOfVariables.lean`; no space is mentioned. -/
def nodePresIso : nodePres2.{u} ≅ nodePres3.{u} where
  hom := nodePresHom.{u}
  inv := nodePresInv.{u}
  hom_inv_id := PresHom.ext presHom23_comp_presHom32.{u}
  inv_hom_id := PresHom.ext presHom32_comp_presHom23.{u}

/-- **The two presented algebras are isomorphic as objects of `CommAlgCat ℂ`.**

This is what lets the analytification of *the algebra* be spoken of at all: the two presentations
give one object for `ComplexAnalytic.analytificationFGAlg` to be applied to. -/
def nodeAlgIso : toFGAlg.{u}.obj nodePres2.{u} ≅ toFGAlg.{u}.obj nodePres3.{u} :=
  toFGAlg.{u}.mapIso nodePresIso.{u}

/-- The functor on presentations sends this isomorphism to the one
`OkaTest/AnalytificationChangeOfVariables.lean` built by hand. -/
theorem analytificationFunctor_mapIso_nodePresIso :
    (analytificationFunctor.{u}.mapIso nodePresIso.{u}).hom =
      nodeIsoAnalytification3.{u}.hom :=
  rfl

/-- **The analytification of the `ℂ`-algebra `ℂ[x, y] ⧸ (x y)` is the node.**

The left-hand side names no presentation: `ComplexAnalytic.analytificationFGAlg` is defined
through the inverse of an equivalence, so the presentation it uses is whatever essential
surjectivity produced. `ComplexAnalytic.analytificationFGAlgObjIso` is what identifies the result
with the analytification of the presentation in hand, and this is that identification at the
smallest space in the development which is not a manifold. -/
def nodeIsoAnalytificationFGAlg :
    analytificationFGAlg.{u}.obj (toFGAlg.{u}.obj nodePres2.{u}) ≅ AnalyticSpace.node.{u} :=
  analytificationFGAlgObjIso.{u} nodePres2.{u}

/-- **And the same for the three-variable presentation**, whose analytification is therefore the
node as well — reached through the functor of algebras rather than by comparing two subspaces. -/
def nodeIsoAnalytificationFGAlg3 :
    analytificationFGAlg.{u}.obj (toFGAlg.{u}.obj nodePres3.{u}) ≅ AnalyticSpace.node.{u} :=
  (analytificationFGAlg.{u}.mapIso nodeAlgIso.{u}).symm ≪≫ nodeIsoAnalytificationFGAlg.{u}

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the mapping property of `IsCutOutBy`

`ComplexAnalytic.IsCutOutBy.existsUnique_lift` says that a morphism killing the sections which
cut out `X` factors uniquely through `i`. Two things could make that empty: nothing might
satisfy `IsCutOutBy`, and — subtler — no interesting `φ` might satisfy the hypothesis
`φ.c.app ⊤ (f j) = 0`.

Neither happens. `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι` supplies a
witness for any family of global sections on any locally ringed space, and the node
`{z ∈ ℂ² | z₀ z₁ = 0}` instantiates it at a singular complex analytic space. And `i` itself
always satisfies the hypothesis (`ComplexAnalytic.IsCutOutBy.c_app_eq_zero`), so the mapping
property always has at least one non-degenerate instance — on which, as `lift_self` below
checks, the factorisation comes out as the identity rather than as some unrelated map.
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

variable {X Y : LocallyRingedSpace.{u}} {i : X ⟶ Y} {k : ℕ}
  {f : Fin k → Y.presheaf.obj (op ⊤)}

/-- **The factorisation of `i` through itself is the identity.** The construction is not merely
*some* morphism with the right source and target: on the one instance where the answer is
forced, it gives the right answer. -/
theorem lift_self (hcut : IsCutOutBy i f) : hcut.lift i hcut.c_app_eq_zero = 𝟙 X :=
  hcut.hom_ext _ _ (by rw [hcut.lift_comp, Category.id_comp])

/-- The mapping property at the node `{z ∈ ℂ² | z₀ z₁ = 0}`, a complex analytic space which is
not a manifold: a morphism into `ℂ²` killing `z₀ z₁` factors uniquely through the node. -/
example (Z : LocallyRingedSpace.{u}) (φ : Z ⟶ nodeAmbient.{u})
    (hφ : ∀ j, φ.c.app (op ⊤) (nodeSection.{u} j) = 0) :
    ∃! ψ : Z ⟶ nodeAmbient.{u}.zeroLocusSubspace nodeSection.{u},
      ψ ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = φ :=
  (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}).existsUnique_lift φ hφ

/-- The hypothesis is satisfiable at the node by something other than the zero morphism: the
inclusion of the node itself kills `z₀ z₁`. -/
example : ∀ j, (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}).c.app (op ⊤)
    (nodeSection.{u} j) = 0 :=
  (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}).c_app_eq_zero

/-- The node is not the empty space, so the isomorphism below and the mapping property above
are not statements about `∅`: the origin lies on it. -/
example : Nonempty (nodeAmbient.{u}.zeroLocusSpace nodeSection.{u}) :=
  ⟨⟨⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩, origin_mem_zeroLocus_nodeSection.{u}⟩⟩

/-- **Two presentations of the same subspace are canonically isomorphic**, and the isomorphism
is over `Y`. Instantiated at a genuinely different pair: `X'` here is any space isomorphic to
`X`, cut out by the same sections through the transported immersion
(`ComplexAnalytic.IsCutOutBy.comp_iso`). -/
example {X' : LocallyRingedSpace.{u}} (hcut : IsCutOutBy i f) (e : X' ≅ X) :
    (hcut.uniqueIso (hcut.comp_iso e)).hom ≫ (e.hom ≫ i) = i :=
  hcut.uniqueIso_hom_comp (hcut.comp_iso e)

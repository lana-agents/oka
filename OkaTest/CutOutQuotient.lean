/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of `i_* 𝒪_X ≅ 𝒪_Y ⧸ (f)`

`ComplexAnalytic.IsCutOutBy.pushforwardIso` would be true and useless twice over: if nothing
satisfied `IsCutOutBy`, and if the two sheaves it relates were both the zero sheaf. This file
rules out both.

The first is `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`, which
produces a witness for *any* family of global sections on *any* locally ringed space, and the
node `{z ∈ ℂ² | z₀ z₁ = 0}` which instantiates it at a genuinely singular complex analytic
space.

The second is the point of `nontrivial_stalk_quotientSheafify` below: at every point of the
zero locus the stalk of `𝒪_Y ⧸ (f)` is a **nonzero** ring. It is proved by transporting the
nontriviality of the stalk of the structure sheaf of the zero locus — which holds because that
stalk is a local ring — backwards along the isomorphism, so it is a statement about the
isomorphism and not merely alongside it.
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

variable {Y : LocallyRingedSpace.{u}} {k : ℕ} (g : Fin k → Y.presheaf.obj (op ⊤))

/-- **At a point of the zero locus, the stalk of `𝒪_Y ⧸ (f)` is not the zero ring.**

So `ComplexAnalytic.IsCutOutBy.pushforwardIso` is not an isomorphism between zero sheaves. -/
theorem nontrivial_stalk_quotientSheafify (z : Y.zeroLocusSpace g) :
    Nontrivial ((Y.quotientSheafify g).stalk (Y.zeroLocusι g z)) := by
  have hcut := Y.isCutOutBy_zeroLocusSubspaceι g
  haveI : IsIso ((Y.zeroLocusPresheaf g).stalkPushforward CommRingCat.{u}
      (Y.zeroLocusι g) z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat.{u}
      (Y.isClosedEmbedding_zeroLocusι g).isInducing _ z
  have hb₁ := ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (Y.zeroLocusι g z)).map
      hcut.pushforwardIso.hom)
  have hb₂ := ConcreteCategory.bijective_of_isIso
    ((Y.zeroLocusPresheaf g).stalkPushforward CommRingCat.{u} (Y.zeroLocusι g) z)
  exact (hb₂.surjective.comp hb₁.surjective).nontrivial

/-- The general witness: the zero locus of any family of global sections, on any locally ringed
space, has `i_* 𝒪_X ≅ 𝒪_Y ⧸ (f)`. -/
example : Y.quotientSheafify g ≅
    (Y.zeroLocusSubspaceι g).base _* (Y.zeroLocusSubspace g).presheaf :=
  (Y.isCutOutBy_zeroLocusSubspaceι g).pushforwardIso

/-- The node `{z ∈ ℂ² | z₀ z₁ = 0}`, a complex analytic space that is not a manifold: its
structure sheaf, pushed forward to `ℂ²`, is `𝒪_{ℂ²} ⧸ (z₀ z₁)`. -/
example : nodeAmbient.{u}.quotientSheafify nodeSection.{u} ≅
    (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}).base _*
      (nodeAmbient.{u}.zeroLocusSubspace nodeSection.{u}).presheaf :=
  (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}).pushforwardIso

/-- The node is not empty, so the isomorphism above is not a statement about the empty space:
the origin lies on it, and there the quotient sheaf has a nonzero stalk. -/
example : Nontrivial ((nodeAmbient.{u}.quotientSheafify nodeSection.{u}).stalk
    (nodeAmbient.{u}.zeroLocusι nodeSection.{u}
      ⟨⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩, origin_mem_zeroLocus_nodeSection.{u}⟩)) :=
  nontrivial_stalk_quotientSheafify _ _

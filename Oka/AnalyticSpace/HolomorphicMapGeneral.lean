/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.HolomorphicMapOpen
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Assembling a morphism `Z ⟶ ℂ` out of local ones

For a complex analytic space `Z` and a global section `g` of `𝒪_Z`, the goal is a morphism of
complex analytic spaces `Z ⟶ ℂ` pulling the coordinate back to `g`. Uniqueness
(`ComplexAnalytic.AnalyticSpace.hom_ext_complexLine`) has been general in `Z` since taxis #653;
existence is known for `Z = ℂ^n` and for `Z = ℂ^n|V`, and this file supplies **the step from
local to global**:

```
ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local :
  (∀ z : Z, ∃ U ∋ z, ∃ ψ : Z|U ⟶ ℂ, coordPullback ψ 0 = g|U) →
    ∃ φ : Z ⟶ ℂ, coordPullback φ 0 = g
```

## What this does and does not give

**It does not close the general case.** Its hypothesis is *local existence*, and producing that
from a chart is a separate construction which is not here; see `## What remains` below. What it
does close is the step that three sessions of this project called "the gluing" and treated as
the blocker.

## The three things the assembly needs, and where each comes from

* **The overlaps must be analytic spaces**, so that uniqueness applies to them. That is
  `ComplexAnalytic.AnalyticSpace.restrict` (taxis #664), and it is why
  `AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` (taxis #693) rather
  than the pullback-form gluing is the theorem used: the categorical pullback of two open
  subspace inclusions is not an analytic space, so the compatibility hypothesis of the older
  lemma cannot be met by the tool meant to meet it.
* **The compatibility itself is uniqueness, not a computation.** Two local morphisms restricted
  to an overlap have the same coordinate pullback there — both are `g` restricted — so
  `ComplexAnalytic.AnalyticSpace.hom_ext_complexLine` says they are equal. That is
  `ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq`, and it is the step whose viability the
  issue behind this file asked to be tested before anything was built on it. It works, and it
  makes `ComplexAnalytic.AnalyticAt.dslope_comp` — built for an independence-of-lifts argument
  the original plan needed — still unused.
* **The glued morphism must be recognised as a morphism of *analytic* spaces**, and its
  coordinate pullback must be recognised as `g`. Both are equalities of global sections that
  hold on each member of the cover, so both are
  `AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover`. `ℂ`-linearity is a condition on
  global sections only (`ComplexAnalytic.IsCLinearHom`), which is what makes this work.

## What remains, stated precisely

`ComplexAnalytic.AnalyticSpace.exists_local_hom_of_chartLift` reduces the hypothesis to a
statement in which no morphism to `ℂ` appears at all: it is enough that every point of `Z` has a
neighbourhood `W`, a chart `c : Z|W ⟶ ℂ^n|V`, and a section `s` of `𝒪_{ℂ^n|V}` with
`Γ.map c.op s = g|W`. So the whole of the general case now rests on

```
∀ z : Z, ∃ (W : Z.Opens) (_ : z ∈ W) (n : ℕ) (V : Opens (ℂ^n))
  (c : Z|W ⟶ ℂ^n|V) (s : Γ(ℂ^n|V, 𝒪)), Γ.map c.op s = g|W
```

which is `AlgebraicGeometry.LocallyRingedSpace.exists_localLift` applied to a chart, plus the
bookkeeping that turns its output into that shape. It is not proved here.

## Main results

- `ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq`: **two local morphisms to `ℂ` with the same
  coordinate pullback agree on the overlap.**
- `ComplexAnalytic.AnalyticSpace.coordPullback_ofRestrict_comp`: restricting a global morphism
  to `ℂ` supplies the local data, with the section restricted along.
- `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local`: **a global section which is
  locally a coordinate pullback is globally one.**
- `ComplexAnalytic.AnalyticSpace.exists_local_hom_of_chartLift`: a chart on which the section
  lifts supplies the local morphism, which is what reduces the remaining work to a statement
  about charts alone.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

/-- **Restricting a local morphism to a smaller open subspace restricts its coordinate
pullback.** -/
theorem coordPullback_restrictLE_comp (Z : AnalyticSpace.{u}) (g : Z.presheaf.obj (op ⊤))
    {V W : Z.Opens} (h : V ≤ W) (ψ : Z.restrict W ⟶ AnalyticSpace.complexAffineSpace.{u} 1)
    (hψ : AnalyticSpace.coordPullback ψ (ULift.up 0) = Z.resΓ W g) :
    AnalyticSpace.coordPullback (Z.restrictLE h ≫ ψ) (ULift.up 0) = Z.resΓ V g :=
  (AnalyticSpace.coordPullback_comp (Z.restrictLE h) ψ (ULift.up 0)).trans
    ((congrArg (fun a ↦ (LocallyRingedSpace.Γ.map
        (Z.toLocallyRingedSpace.restrictLE h).op).hom a) hψ).trans (Z.resΓ_restrictLE h g))

/-- **Restricting a global morphism to `ℂ` supplies the local data**, with the local section
being the restriction of the global one.

This is `ComplexAnalytic.AnalyticSpace.coordPullback_comp` for the inclusion of an open
subspace, and it is what makes the hypothesis of
`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local` satisfiable at any cover of a
`Z` for which the conclusion is already known — which is how the assembly is tested. -/
theorem coordPullback_ofRestrict_comp (Z : AnalyticSpace.{u}) (U : Z.Opens)
    (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1) :
    AnalyticSpace.coordPullback (Z.ofRestrict U ≫ φ) (ULift.up 0) =
      Z.resΓ U (AnalyticSpace.coordPullback φ (ULift.up 0)) :=
  AnalyticSpace.coordPullback_comp (Z.ofRestrict U) φ (ULift.up 0)

/-- **Two local morphisms to `ℂ` whose coordinate pullbacks are the restrictions of one global
section agree on the overlap.**

This is the compatibility hypothesis of
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens`, and it is discharged
by *uniqueness*: both restricted morphisms pull the coordinate back to `g` restricted to
`V ⊓ W`, and `ComplexAnalytic.AnalyticSpace.hom_ext_complexLine` applies because `Z|(V ⊓ W)` is
an analytic space. No agreement of the two morphisms is assumed and none is computed. -/
theorem restrictLE_comp_eq (Z : AnalyticSpace.{u}) (g : Z.presheaf.obj (op ⊤))
    {V W : Z.Opens} (ψV : Z.restrict V ⟶ AnalyticSpace.complexAffineSpace.{u} 1)
    (ψW : Z.restrict W ⟶ AnalyticSpace.complexAffineSpace.{u} 1)
    (hV : AnalyticSpace.coordPullback ψV (ULift.up 0) = Z.resΓ V g)
    (hW : AnalyticSpace.coordPullback ψW (ULift.up 0) = Z.resΓ W g) :
    Z.restrictLE (inf_le_left : V ⊓ W ≤ V) ≫ ψV =
      Z.restrictLE (inf_le_right : V ⊓ W ≤ W) ≫ ψW :=
  AnalyticSpace.hom_ext_complexLine _ _
    ((Z.coordPullback_restrictLE_comp g inf_le_left ψV hV).trans
      (Z.coordPullback_restrictLE_comp g inf_le_right ψW hW).symm)

/-- **A global section of `𝒪_Z` which is locally the coordinate pullback of a morphism to `ℂ` is
globally one.**

The cover is indexed by the points of `Z`, each point contributing the neighbourhood the
hypothesis supplies for it; that is a `Type u` because the carrier is, which is what
`existsUnique_glueMorphisms_of_opens` requires of its index type.

The glued morphism arrives as a morphism of *locally ringed* spaces. Both remaining obligations
— that it is `ℂ`-linear, and that its coordinate pullback is `g` — are equalities of global
sections which hold after restriction to each member of the cover, so both are
`AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover`. `ℂ`-linearity being a condition on
global sections *only* is what makes the first of those an instance of the second. -/
theorem exists_hom_complexLine_of_local (Z : AnalyticSpace.{u}) (g : Z.presheaf.obj (op ⊤))
    (hloc : ∀ z : Z, ∃ (U : Z.Opens) (_ : z ∈ U)
      (ψ : Z.restrict U ⟶ AnalyticSpace.complexAffineSpace.{u} 1),
      AnalyticSpace.coordPullback ψ (ULift.up 0) = Z.resΓ U g) :
    ∃ φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) = g := by
  choose U hzU ψ hψ using hloc
  have hcover : ∀ x : Z.toLocallyRingedSpace, ∃ i, x ∈ U i := fun x ↦ ⟨x, hzU x⟩
  obtain ⟨φ₀, hφ₀, -⟩ := LocallyRingedSpace.existsUnique_glueMorphisms_of_opens U hcover
    (fun i ↦ (ψ i).toLRSHom) fun i j ↦ congrArg
      (fun m : Z.restrict (U i ⊓ U j) ⟶ AnalyticSpace.complexAffineSpace.{u} 1 ↦ m.toLRSHom)
      (Z.restrictLE_comp_eq g (ψ i) (ψ j) (hψ i) (hψ j))
  -- pulling a section back along `φ₀` and restricting to `U i` is pulling it back along `ψ i`
  have key : ∀ (i : Z) (a : (AnalyticSpace.complexAffineSpace.{u} 1).presheaf.obj (op ⊤)),
      (LocallyRingedSpace.Γ.map
          (Z.toLocallyRingedSpace.ofRestrict (U i).isOpenEmbedding).op).hom
            ((LocallyRingedSpace.Γ.map φ₀.op).hom a) =
        (LocallyRingedSpace.Γ.map (ψ i).toLRSHom.op).hom a := fun i a ↦
    (LocallyRingedSpace.Γ_map_comp_apply _ φ₀ a).symm.trans
      (congrArg (fun m : Z.toLocallyRingedSpace.restrict (U i).isOpenEmbedding ⟶
          (AnalyticSpace.complexAffineSpace.{u} 1).toLocallyRingedSpace ↦
        (LocallyRingedSpace.Γ.map m.op).hom a) (hφ₀ i))
  have hclin : IsCLinearHom φ₀ Z.algebraMap
      (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap := fun c ↦
    LocallyRingedSpace.section_ext_of_cover Z.toLocallyRingedSpace U hcover _ _ fun i ↦
      (key i _).trans (((ψ i).isCLinear c).trans
        (isCLinearHom_ofRestrict Z.toLocallyRingedSpace Z.algebraMap (U i) c).symm)
  exact ⟨⟨φ₀, hclin⟩,
    LocallyRingedSpace.section_ext_of_cover Z.toLocallyRingedSpace U hcover _ _ fun i ↦
      (key i _).trans (hψ i)⟩

/-- **A chart on which the section lifts supplies the local morphism.**

Composing the chart with the morphism `ℂ^n|V ⟶ ℂ` that
`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict` builds from `s`, and using
naturality of `ComplexAnalytic.AnalyticSpace.coordPullback`, gives the hypothesis of
`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local` at that point. Nothing about
`c` is used beyond its being a morphism of analytic spaces — it need not be a closed immersion,
and no cut-out data enters. -/
theorem exists_local_hom_of_chartLift (Z : AnalyticSpace.{u}) (g : Z.presheaf.obj (op ⊤))
    {W : Z.Opens} {n : ℕ} {V : TopologicalSpace.Opens (complexAffineSpace.{u} n)}
    (c : Z.restrict W ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V)
    (s : ((AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.obj (op ⊤))
    (hs : (LocallyRingedSpace.Γ.map c.toLRSHom.op).hom s = Z.resΓ W g) :
    ∃ ψ : Z.restrict W ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback ψ (ULift.up 0) = Z.resΓ W g := by
  obtain ⟨φ, hφ⟩ := AnalyticSpace.exists_hom_complexLine_restrict s
  exact ⟨c ≫ φ, ((AnalyticSpace.coordPullback_comp c φ (ULift.up 0)).trans
    (congrArg (fun a ↦ (LocallyRingedSpace.Γ.map c.toLRSHom.op).hom a) hφ)).trans hs⟩

end ComplexAnalytic.AnalyticSpace

end

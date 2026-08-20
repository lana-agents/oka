/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.HolomorphicMapOpen
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# `Hom(Z, ℂ) ≃ Γ(Z, 𝒪_Z)` for every complex analytic space

For a complex analytic space `Z` and a global section `g` of `𝒪_Z`, a morphism of complex
analytic spaces `Z ⟶ ℂ` pulling the coordinate back to `g`:

```
ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_general (Z : AnalyticSpace) (g : Γ(Z, 𝒪_Z)) :
  ∃ φ : Z ⟶ ℂ, coordPullback φ 0 = g
```

Uniqueness (`ComplexAnalytic.AnalyticSpace.hom_ext_complexLine`) has been general in `Z` since
taxis #653, so this makes `ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral` a bijection
`Hom(Z, ℂ) ≃ Γ(Z, 𝒪_Z)` for an arbitrary complex analytic space — taxis #628. Existence was
previously known only for `Z = ℂ^n` and for `Z = ℂ^n|V`.

## The three steps

1. **The chart step** — `exists_chartLift`. Near each point, `g` is the pullback of a section of
   `𝒪_{ℂ^n|V}` along a chart. The chart comes from `AnalyticSpace.local_model`; the section from
   `AlgebraicGeometry.LocallyRingedSpace.exists_localLift`, applied not to the chart `i` itself
   but to `i` **composed with the inclusion of its target into `ℂ^n`** — which is what makes the
   lifted section live on an open of `ℂ^n` rather than on an open of `ℂ^n|V`, removing one of
   the three seams below before it appears.
2. **The local morphism** — `exists_local_hom_of_chartLift`: compose the chart with the morphism
   `ℂ^n|V ⟶ ℂ` that `exists_hom_complexLine_restrict` builds from that section.
3. **The gluing** — `exists_hom_complexLine_of_local`.

## What the gluing needs, and where each part comes from

* **The overlaps must be analytic spaces**, so that uniqueness applies to them. That is
  `ComplexAnalytic.AnalyticSpace.restrict` (taxis #664), and it is why
  `AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` (taxis #693) rather
  than the pullback-form gluing is the theorem used: the categorical pullback of two open
  subspace inclusions is not an analytic space, so the compatibility hypothesis of the older
  lemma cannot be met by the tool meant to meet it.
* **The compatibility itself is uniqueness, not a computation.** Two local morphisms restricted
  to an overlap have the same coordinate pullback there — both are `g` restricted — so
  `ComplexAnalytic.AnalyticSpace.hom_ext_complexLine` says they are equal. That is
  `ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq`. **It is also why the two
  independence-of-choices arguments the original plan for this theorem called for are not
  needed**, and why `ComplexAnalytic.AnalyticAt.dslope_comp`, built for one of them, is still
  consumed by nothing.
* **The glued morphism must be recognised as a morphism of *analytic* spaces**, and its
  coordinate pullback must be recognised as `g`. Both are equalities of global sections that
  hold on each member of the cover, so both are
  `AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover`. `ℂ`-linearity is a condition on
  global sections only (`ComplexAnalytic.IsCLinearHom`), which is what makes this work.

## What the chart step needs, and the seam that made it hard

`exists_localLift` produces a section over an open subset `A` of the chart target and, in
general, over nothing larger. Two seams follow, and they are not symmetric.

* **The source open lives in `Z|U₀`, not in `Z`.** `X|U|W` and `X|W'`, for `W'` the image of `W`,
  are two open immersions into `X` with the same image, so `IsOpenImmersion.lift` produces the
  comparison morphism and `AlgebraicGeometry.LocallyRingedSpace.Γ_map_over_ambient` computes its
  action on sections. No isomorphism is needed — only a morphism over `X`.
* **The chart's sheaf map has to be evaluated on a section that does not extend.**
  `restrictHom_fac` computes `Γ.map (restrictHom i A).op` only on sections pulled back from the
  global sections of the chart target, and `restrictHom` is an `IsOpenImmersion.lift`, so its
  sheaf map is not otherwise computable. `ComplexAnalytic.Γ_map_restrictHom_toRestrictΓ` is what
  closes this, entirely on stalks.

**Neither needed an equation of opens.** The obvious plan is to prove
`U.isOpenEmbedding.isOpenMap.functor.obj ⊤ = U` and transport along it. That is never necessary:
`AlgebraicGeometry.LocallyRingedSpace.germ_res_apply` moves a germ across a `≤`, and the two
inequalities one needs — `functor.obj O ≤ U` and `O ≤ (Opens.map ι).obj (functor.obj O)` — are
one-line `rintro`s. Every predicted transport evaporates.

## Main results

- `ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq`: **two local morphisms to `ℂ` with the same
  coordinate pullback agree on the overlap.**
- `ComplexAnalytic.AnalyticSpace.coordPullback_ofRestrict_comp`: restricting a global morphism
  to `ℂ` supplies the local data, with the section restricted along.
- `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local`: **a global section which is
  locally a coordinate pullback is globally one.**
- `ComplexAnalytic.AnalyticSpace.exists_local_hom_of_chartLift`: a chart on which the section
  lifts supplies the local morphism.
- `ComplexAnalytic.AnalyticSpace.exists_chartLift`: **near each point, a global section of
  `𝒪_Z` is the pullback of a section of `𝒪_{ℂ^n|V}` along a chart.**
- `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_general`: **every global section of
  `𝒪_Z` is the pullback of the coordinate along a morphism `Z ⟶ ℂ`.**
- `ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral`: **`Hom(Z, ℂ) ≃ Γ(Z, 𝒪_Z)`.**
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

/-- **Near each point, a global section of `𝒪_Z` is the pullback of a section of `𝒪_{ℂ^n|V}`
along a chart.**

Nothing is claimed about the chart beyond its being a morphism of analytic spaces: it need not
be a closed immersion, and no cut-out data appears in the statement. `IsCutOutBy` is used only
inside the proof, for the stalk-surjectivity that `exists_localLift` needs.

**The chart is composed with the inclusion of its target into `ℂ^n` before the lift is taken.**
That is the one design choice that matters: `exists_localLift` then produces its section over an
open of `ℂ^n` rather than over an open of `ℂ^n|V`, so the chart target of the conclusion can be
that open itself and no comparison of `ℂ^n|V|A` with `ℂ^n|A'` is ever needed. The composite is
still surjective on stalks, because the inclusion of an open subspace is an isomorphism on
stalks. -/
theorem exists_chartLift (Z : AnalyticSpace.{u}) (g : Z.presheaf.obj (op ⊤)) (z : Z) :
    ∃ (W : Z.Opens) (_ : z ∈ W) (n : ℕ)
      (V : TopologicalSpace.Opens (_root_.complexAffineSpace.{u} n))
      (c : Z.restrict W ⟶ (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{u} n).restrict V)
      (s : ((ComplexAnalytic.AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.obj
        (op ⊤)),
      (LocallyRingedSpace.Γ.map c.toLRSHom.op).hom s = Z.resΓ W g := by
  obtain ⟨U₀, n, k, V, i, f, hcut, hlin⟩ := Z.local_model z
  have hsurj : ∀ x : Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding,
      Function.Surjective
        (((i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).stalkMap x).hom) :=
      fun x c ↦ by
    obtain ⟨b, rfl⟩ := hcut.surjective_stalkMap x c
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (((_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).stalkMap
        (i.base x))).surjective b
    refine ⟨a, ?_⟩
    rw [LocallyRingedSpace.stalkMap_comp]
    exact ConcreteCategory.comp_apply _ _ a
  obtain ⟨A, hA, u, B', hB'top, hB'A, hxB', heq⟩ :=
    LocallyRingedSpace.exists_localLift
      (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding) hsurj (B := ⊤)
      (Z.resΓ U₀.1 g) (⟨z, U₀.2⟩ : Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) trivial
  have hW : U₀.1.isOpenEmbedding.isOpenMap.functor.obj B' ≤
      U₀.1.isOpenEmbedding.isOpenMap.functor.obj
        ((Opens.map (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict
          V.isOpenEmbedding).base).obj A) :=
    LocallyRingedSpace.functor_mono U₀.1 hB'A
  have hr1 := LocallyRingedSpace.range_ofRestrict Z.toLocallyRingedSpace
    (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B')
  have hr2 := LocallyRingedSpace.range_ofRestrict_comp Z.toLocallyRingedSpace U₀.1
    ((Opens.map (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).base).obj A)
  have hrange : Set.range ((Z.toLocallyRingedSpace.ofRestrict
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B').isOpenEmbedding).base) ⊆
      Set.range (((Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).ofRestrict
        ((Opens.map (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict
          V.isOpenEmbedding).base).obj A).isOpenEmbedding ≫
        Z.toLocallyRingedSpace.ofRestrict U₀.1.isOpenEmbedding).base) :=
    (hr1.subset.trans hW).trans hr2.symm.subset
  refine ⟨U₀.1.isOpenEmbedding.isOpenMap.functor.obj B',
    ⟨⟨z, U₀.2⟩, hxB', rfl⟩, n, A,
    ⟨LocallyRingedSpace.IsOpenImmersion.lift _ _ hrange ≫
      restrictHom (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding) A, ?_⟩,
    (_root_.complexAffineSpace.{u} n).toRestrictΓ A u, ?_⟩
  · exact IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange)
      (isCLinearHom_ofRestrict Z.toLocallyRingedSpace Z.algebraMap _)
      ((isCLinearHom_ofRestrict (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) _ _).comp
        (isCLinearHom_ofRestrict Z.toLocallyRingedSpace Z.algebraMap U₀.1))
      |>.comp (isCLinearHom_restrictHom (hlin.comp (isCLinearHom_ofRestrict_constants n V)) A)
  · refine Eq.trans (LocallyRingedSpace.Γ_map_comp_apply _ _ _) ?_
    refine Eq.trans (congrArg
      (fun b ↦ (LocallyRingedSpace.Γ.map
        (LocallyRingedSpace.IsOpenImmersion.lift _ _ hrange).op).hom b)
      (Γ_map_restrictHom_toRestrictΓ _ A u)) ?_
    refine Eq.trans (LocallyRingedSpace.Γ_map_over_ambient Z.toLocallyRingedSpace U₀.1 _ _ hW _
      (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange) _) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'))
      (LocallyRingedSpace.restrict_map_apply Z.toLocallyRingedSpace U₀.1 hB'A hW _).symm) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B')) heq) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'))
      (LocallyRingedSpace.restrict_map_apply Z.toLocallyRingedSpace U₀.1 hB'top
        (LocallyRingedSpace.functor_mono U₀.1 hB'top) _)) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'))
      (congrArg (fun b ↦ (Z.toLocallyRingedSpace.presheaf.map
          (homOfLE (LocallyRingedSpace.functor_mono U₀.1 hB'top)).op).hom b)
        (LocallyRingedSpace.Γ_map_ofRestrict_apply Z.toLocallyRingedSpace U₀.1 g))) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'))
      (LocallyRingedSpace.map_map_apply Z.toLocallyRingedSpace _ le_top le_top g)) ?_
    exact (LocallyRingedSpace.map_map_apply Z.toLocallyRingedSpace _ le_top le_top g).trans
      (LocallyRingedSpace.Γ_map_ofRestrict_apply Z.toLocallyRingedSpace _ g).symm

/-- **Every global section of `𝒪_Z` is the pullback of the coordinate along a morphism of complex
analytic spaces `Z ⟶ ℂ`, for every complex analytic space `Z`.**

This is the existence half of taxis #628, and the last of it that was open. -/
theorem exists_hom_complexLine_general (Z : AnalyticSpace.{u}) (g : Z.presheaf.obj (op ⊤)) :
    ∃ φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) = g :=
  exists_hom_complexLine_of_local Z g fun z ↦ by
    obtain ⟨W, hzW, n, V, c, s, hs⟩ := exists_chartLift Z g z
    obtain ⟨ψ, hψ⟩ := exists_local_hom_of_chartLift Z g c s hs
    exact ⟨W, hzW, ψ, hψ⟩

/-- **`Hom(Z, ℂ) ≃ Γ(Z, 𝒪_Z)` for every complex analytic space `Z`**, the correspondence being
the pullback of the coordinate.

Injectivity is `ComplexAnalytic.AnalyticSpace.hom_ext_complexLine`, which has been general in `Z`
since taxis #653; surjectivity is `exists_hom_complexLine_general`. As with the `ℂ^n` and
`ℂ^n|V` versions this is `Equiv.ofBijective`, so the inverse is a choice term; the forward map is
`ComplexAnalytic.AnalyticSpace.coordPullback` and is the thing to state results about. -/
noncomputable def homComplexLineEquivGeneral (Z : AnalyticSpace.{u}) :
    (Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1) ≃ Z.presheaf.obj (op ⊤) :=
  Equiv.ofBijective (fun φ ↦ AnalyticSpace.coordPullback φ (ULift.up 0))
    ⟨fun _ _ h ↦ AnalyticSpace.hom_ext_complexLine _ _ h, exists_hom_complexLine_general Z⟩

/-- `ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral` is the pullback of the
coordinate. -/
@[simp]
lemma homComplexLineEquivGeneral_apply (Z : AnalyticSpace.{u})
    (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1) :
    homComplexLineEquivGeneral Z φ = AnalyticSpace.coordPullback φ (ULift.up 0) :=
  rfl

end ComplexAnalytic.AnalyticSpace

end

/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.Covering.BranchedDiscData
import Oka.Analytification.RET.ES.CurveSetup
import Oka.Analytification.RET.ES.SmoothLocus
import Oka.Analytification.RET.Connected
import Oka.Analytification.RET.Separated

/-!
# The fundamental group of a smooth affine curve with a branched coordinate

Let `V` be an affine scheme of finite type over `ℂ`, smooth of relative dimension one, and
`z ∈ Γ(V, 𝒪_V)` a function making `Γ(V, 𝒪_V)` a finite `ℂ[z]`-algebra (given as
`s : ℂ[X₀] → Γ(V, 𝒪_V)`) which is étale over `𝔸¹ ∖ S` for a finite `S ⊆ ℂ`, i.e. after inverting
`∏_{a ∈ S} (z - a)`. Then `z^an : V^an → ℂ` is a finite branched covering of the plane in the
sense of `Oka/Topology/Covering/BranchedDiscData.lean`:

* `ComplexAnalytic.SchemeLFTℂ.exists_etale_affineLine`: a scheme smooth of relative dimension one
  over `ℂ` is locally étale over `𝔸¹`;
* `ComplexAnalytic.exists_chart_analytification`: hence every point of `V^an` lies in the source
  of a chart `V^an ⇀ ℂ`;
* `ComplexAnalytic.isClosedMap_coordFun`, `ComplexAnalytic.finite_coordFun_fiber`: `z^an` is
  closed with finite fibres (`s` finite,
  `ComplexAnalytic.isFinite_analytification_map_of_isFinite`);
* `ComplexAnalytic.isLocalHomeomorphOn_coordFun`: `z^an` is a local homeomorphism outside
  `(z^an)⁻¹(S)` (étale morphisms analytify to local isomorphisms).

Hence (`ComplexAnalytic.exists_fundamentalGroup_analytification_mulEquiv_freeGroup`), for `V`
connected, **`π₁(V^an)` is free of rank `d (|S| - 1) + 1 - #(z^an)⁻¹(S)`**, `d` the number of
points of a fibre of `z^an` over `ℂ ∖ S`. For `V = X ∖ D` and `z` a Belyi function with pole set
exactly `D` (`S = {0, 1}`) this is the free group of rank `d + 1 - c₀ - c₁`, which equals
`2g + |D| - 1` by Riemann–Hurwitz.
-/

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

namespace SchemeLFTℂ

/-- **A scheme smooth of relative dimension one over `ℂ` is locally étale over `𝔸¹`.** -/
theorem exists_etale_affineLine (Y : SchemeLFTℂ.{u}) [SmoothOfRelativeDimension 1 Y.obj.hom]
    (y : Y.obj.left) :
    ∃ (V : Y.obj.left.Opens) (_ : y ∈ V) (f : Y.restrict V ⟶ affineSpace.{u} 1),
      Etale f.hom.left := by
  obtain ⟨U', hU', V, hV, hyV, e, hst⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := Y.obj.hom) y
  obtain rfl : U' = ⊤ := eq_top_iff.mpr fun z _ ↦ by
    rw [show z = Y.obj.hom y from Subsingleton.elim _ _]
    exact e hyV
  haveI : IsAffine (Y.restrict V).obj.left := hV
  let φ : ULift.{u} ℂ →+* Γ(Y.obj.left, V) :=
    ((Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv ≫ Y.obj.hom.appLE ⊤ V e).hom
  have hφ : φ.IsStandardSmoothOfRelativeDimension 1 :=
    ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)).cancel_left_isIso
      (Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv _).2 hst
  obtain ⟨g, hgC, hg⟩ := hφ.exists_etale_mvPolynomial
  let s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ((Y.restrict V).obj.left, ⊤) :=
    V.topIso.inv.hom.comp g
  have key : Y.obj.hom.appLE ⊤ V e ≫ V.topIso.inv = (V.ι ≫ Y.obj.hom).appTop := by
    rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Hom.appLE, Scheme.Opens.topIso,
      Category.assoc, Functor.mapIso_inv]
    erw [← Functor.map_comp]
    rfl
  have hs : s.comp MvPolynomial.C = (Y.restrict V).constMap := by
    refine RingHom.ext fun r ↦ ?_
    have h1 : g (MvPolynomial.C r) = φ r := RingHom.congr_fun hgC r
    change V.topIso.inv.hom (g (MvPolynomial.C r)) =
      ((Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv ≫ (V.ι ≫ Y.obj.hom).appTop).hom r
    rw [h1, ← key]
    rfl
  exact ⟨V, hyV, toAffineSpace s hs, etale_toAffineSpace s hs
    (RingHom.Etale.respectsIso.1 g V.topIso.symm.commRingCatIsoToRingEquiv hg)⟩

end SchemeLFTℂ

/-- The coordinate of `ℂ¹`, as a homeomorphism with `ℂ`. -/
def coordHomeomorph : AnalyticSpace.complexAffineSpace.{u} 1 ≃ₜ ℂ where
  toFun := ProjectiveLine.coord
  invFun := ProjectiveLine.ofCoord
  left_inv := ProjectiveLine.ofCoord_coord
  right_inv := ProjectiveLine.coord_ofCoord
  continuous_toFun := ProjectiveLine.continuous_coord
  continuous_invFun := ProjectiveLine.continuous_ofCoord

/-- **Charts on the analytification of a smooth curve**: if `Y` is smooth of relative dimension
one over `ℂ`, every point of `Y^an` lies in the source of a partial homeomorphism `Y^an ⇀ ℂ`
with open source and target. -/
theorem exists_chart_analytification (Y : SchemeLFTℂ.{u}) [SmoothOfRelativeDimension 1 Y.obj.hom]
    (v : analytification.obj Y) :
    ∃ φ : OpenPartialHomeomorph (analytification.obj Y) ℂ, v ∈ φ.source := by
  obtain ⟨U, hxU, f, hf⟩ := SchemeLFTℂ.exists_etale_affineLine Y ((analytificationπLRS Y).base v)
  haveI := isLocalIso_analytification_map_of_etale f
  haveI := isLocalIso_of_isIso (analytificationAffineSpaceIso.{u} 1).hom
  let g := analytification.map f ≫ (analytificationAffineSpaceIso.{u} 1).hom
  have hg : IsLocalHomeomorph (coordHomeomorph ∘ g.toLRSHom.base) :=
    coordHomeomorph.isLocalHomeomorph.comp (IsLocalIso.isLocalHomeomorph (f := g))
  have hj := isOpenEmbedding_analytification_map_restrictι Y U
  have hv : v ∈ Set.range (analytification.map (Y.restrictι U)).toLRSHom.base := by
    rw [range_analytification_map_restrictι]
    exact hxU
  obtain ⟨z, rfl⟩ := hv
  haveI : Nonempty (analytification.obj (Y.restrict U)) := ⟨z⟩
  obtain ⟨ψ, hzψ, hψ⟩ := hg z
  set J := hj.toOpenPartialHomeomorph _
  have hz : J.symm (J z) = z := J.left_inv (by
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]; trivial)
  refine ⟨J.symm.trans ψ, ?_, ?_⟩
  · change J z ∈ J.target
    exact J.map_source (by rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]; trivial)
  · change J.symm (J z) ∈ ψ.source
    rw [hz]
    exact hzψ

variable {V : SchemeLFTℂ.{u}} (s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤))
  (hs : s.comp MvPolynomial.C = V.constMap)

/-- The function `z = s(X₀)` on `V^an`, with values in `ℂ`. -/
def coordFun : C(analytification.obj V, ℂ) :=
  ⟨fun v ↦ ProjectiveLine.coord ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base v),
    ProjectiveLine.continuous_coord.comp (SchemeLFTℂ.anToAffine s hs).toLRSHom.base.hom.continuous⟩

lemma affineEval_one (w : AnalyticSpace.complexAffineSpace.{u} 1)
    (p : MvPolynomial (Fin 1) (ULift.{u} ℂ)) :
    affineEval 1 w p = (MvPolynomial.eval (fun _ ↦ ProjectiveLine.coord w)
      (MvPolynomial.map ULift.ringEquiv.toRingHom p)) := by
  rw [affineEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_map]
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  rfl

/-- The value of `s(p)` at a point of `V^an` is `p` evaluated at the coordinate. -/
lemma evalPoint_eq_eval_coordFun (v : analytification.obj V)
    (p : MvPolynomial (Fin 1) (ULift.{u} ℂ)) :
    evalPoint V v (s p) = MvPolynomial.eval (fun _ ↦ coordFun s hs v)
      (MvPolynomial.map ULift.ringEquiv.toRingHom p) := by
  rw [evalPoint_eq_affineEval s hs, affineEval_one]
  rfl

/-- The polynomial `∏_{a ∈ S} (X₀ - a)`. -/
def branchPoly (S : Finset ℂ) : MvPolynomial (Fin 1) (ULift.{u} ℂ) :=
  ∏ a ∈ S, (MvPolynomial.X 0 - MvPolynomial.C ⟨a⟩)

lemma evalPoint_branchPoly (S : Finset ℂ) (v : analytification.obj V) :
    evalPoint V v (s (branchPoly S)) = ∏ a ∈ S, (coordFun s hs v - a) := by
  rw [evalPoint_eq_eval_coordFun s hs, branchPoly, map_prod, map_prod]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  simp only [map_sub, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X,
    MvPolynomial.eval_C]
  rfl

section Finite

variable [IsAffine V.obj.left] (hsfin : s.Finite)
include hsfin

theorem isFinite_anToAffine : AnalyticSpace.IsFinite (SchemeLFTℂ.anToAffine s hs) := by
  haveI : AlgebraicGeometry.IsFinite (SchemeLFTℂ.toAffineSpace s hs).hom.left :=
    isFinite_toAffineSpace hs hsfin
  haveI := isFinite_analytification_map_of_isFinite (SchemeLFTℂ.toAffineSpace s hs)
  haveI := isFinite_of_isIso (analytificationAffineSpaceIso.{u} 1).hom
  exact isFinite_comp _ _

/-- `z^an` is a closed map. -/
theorem isClosedMap_coordFun : IsClosedMap (coordFun s hs) := by
  haveI := isFinite_anToAffine s hs hsfin
  exact coordHomeomorph.isClosedMap.comp
    (AnalyticSpace.IsFinite.isClosedMap (f := SchemeLFTℂ.anToAffine s hs))

/-- `z^an` has finite fibres. -/
theorem finite_coordFun_fiber (c : ℂ) : (coordFun s hs ⁻¹' {c}).Finite := by
  haveI := isFinite_anToAffine s hs hsfin
  have := AnalyticSpace.IsFinite.finite_fiber (f := SchemeLFTℂ.anToAffine s hs)
    (ProjectiveLine.ofCoord c)
  refine (Set.toFinite ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base ⁻¹'
    {ProjectiveLine.ofCoord c})).subset fun v hv ↦ ?_
  change (SchemeLFTℂ.anToAffine s hs).toLRSHom.base v = ProjectiveLine.ofCoord c
  rw [← (hv : ProjectiveLine.coord _ = c)]
  exact (ProjectiveLine.ofCoord_coord _).symm

end Finite

/-- **`z^an` is a local homeomorphism over `ℂ ∖ S`** if `Γ(V, 𝒪_V)` is étale over `ℂ[z]` after
inverting `∏_{a ∈ S} (z - a)`. -/
theorem isLocalHomeomorphOn_coordFun [IsAffine V.obj.left] (S : Finset ℂ)
    (het : ((algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, V.obj.left.basicOpen
      (s (branchPoly S)))).comp s).Etale) :
    IsLocalHomeomorphOn (coordFun s hs) {v | coordFun s hs v ∉ S} := by
  set U := V.obj.left.basicOpen (s (branchPoly S))
  haveI := etale_restrictι_comp_toAffineSpace s hs (s (branchPoly S)) het
  haveI := isLocalIso_analytification_map_of_etale
    (V.restrictι U ≫ SchemeLFTℂ.toAffineSpace s hs)
  haveI := isLocalIso_of_isIso (analytificationAffineSpaceIso.{u} 1).hom
  let j := analytification.map (V.restrictι U)
  have hjU : IsLocalHomeomorph j.toLRSHom.base :=
    (isOpenEmbedding_analytification_map_restrictι V U).isLocalHomeomorph
  have hc : IsLocalHomeomorph (coordFun s hs ∘ j.toLRSHom.base) := by
    have e : coordFun s hs ∘ j.toLRSHom.base = coordHomeomorph ∘
        (analytification.map (V.restrictι U ≫ SchemeLFTℂ.toAffineSpace s hs) ≫
          (analytificationAffineSpaceIso.{u} 1).hom).toLRSHom.base := by
      rw [Functor.map_comp]
      rfl
    rw [e]
    exact coordHomeomorph.isLocalHomeomorph.comp (IsLocalIso.isLocalHomeomorph
      (f := analytification.map (V.restrictι U ≫ SchemeLFTℂ.toAffineSpace s hs) ≫
        (analytificationAffineSpaceIso.{u} 1).hom))
  have h : IsLocalHomeomorphOn (coordFun s hs) (j.toLRSHom.base '' Set.univ) :=
    hc.isLocalHomeomorphOn.of_comp_right hjU.isLocalHomeomorphOn
  refine h.mono fun v hv ↦ ?_
  rw [Set.image_univ, range_analytification_map_restrictι]
  refine mem_basicOpen_of_evalPoint_ne_zero V v _ ?_
  rw [evalPoint_branchPoly s hs, Finset.prod_ne_zero_iff]
  intro a ha h0
  rw [sub_eq_zero] at h0
  exact hv (h0 ▸ ha)

/-- **`π₁` of a smooth connected affine curve with a branched coordinate is free.** Let `V` be
affine, connected and smooth of relative dimension one over `ℂ`, and `s : ℂ[X₀] → Γ(V, 𝒪_V)`
finite and étale after inverting `∏_{a ∈ S}(z - a)`, `z = s(X₀)`. Then for every point `e₀` of
`V^an` with `z(e₀) ∉ S`, `π₁(V^an, e₀)` is free of rank `d (|S| - 1) + 1 - #(z^an)⁻¹(S)`, `d`
the number of points of `V^an` with `z = z(e₀)`. -/
theorem exists_fundamentalGroup_analytification_mulEquiv_freeGroup [IsAffine V.obj.left]
    [ConnectedSpace V.obj.left] [SmoothOfRelativeDimension 1 V.obj.hom] (hsfin : s.Finite)
    (S : Finset ℂ)
    (het : ((algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, V.obj.left.basicOpen
      (s (branchPoly S)))).comp s).Etale)
    (e₀ : analytification.obj V) (he₀ : coordFun s hs e₀ ∉ S) :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (FundamentalGroup (analytification.obj V) e₀ ≃* FreeGroup ι) ∧
      Nat.card ι + Nat.card (coordFun s hs ⁻¹' {coordFun s hs e₀}) +
          Nat.card {P : analytification.obj V // coordFun s hs P ∈ S} =
        Nat.card (coordFun s hs ⁻¹' {coordFun s hs e₀}) * S.card + 1 := by
  haveI := t2Space_analytification_of_isAffine V
  haveI := connectedSpace_analytification V
  haveI := BranchedCover.locallyPathConnectedSpace_of_charts (exists_chart_analytification V)
  exact BranchedCover.exists_fundamentalGroup_mulEquiv_freeGroup_of_charts
    (isClosedMap_coordFun s hs hsfin) (finite_coordFun_fiber s hs hsfin)
    (isLocalHomeomorphOn_coordFun s hs S het)
    (fun P _ ↦ exists_chart_analytification V P) e₀ he₀

end

end ComplexAnalytic

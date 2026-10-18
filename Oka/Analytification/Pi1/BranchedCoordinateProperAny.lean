/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Analytification.Pi1.BranchedCoordinateProper
import Oka.Topology.Covering.BranchedSurfaceAny

/-!
# The fundamental group of a compact curve with a finite coordinate having one pole

The analogue of `Oka/Analytification/Pi1/BranchedCoordinateProper.lean` for a coordinate which
is étale over `𝔸¹ ∖ S` for an arbitrary finite nonempty `S ⊆ ℂ` (instead of `S = {0, 1}`):
`π₁(Y^an) ≃* Π_{g,0}` with `2g + ∑_{a ∈ S} c_a + d = d |S| + 1`
(`ComplexAnalytic.exists_fundamentalGroup_analytification_specLFT_mulEquiv_surfaceGroup_of_finset`),
by `BranchedCover.Gen.exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_finset`.
-/

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

variable {Y : SchemeLFTℂ.{u}}

/-- **`π₁` of a compact curve with a finite coordinate having one pole**, any finite branch
locus: `A` a finitely generated `ℂ`-algebra which is a domain, smooth of relative dimension one,
`ι : Spec A ⟶ Y` an open immersion with image `Y ∖ {p}`, `Y` connected, smooth of relative
dimension one, `Y^an` compact Hausdorff, `z ∈ A` with `ℂ[z] → A` finite and étale after
inverting `∏_{a ∈ S} (z - a)`, `S` finite nonempty. Then for every `c ∈ ℂ ∖ S` and every
`y ∈ Y^an`, `π₁(Y^an, y) ≃* Π_{g,0}` with `2g + ∑_{a ∈ S} c_a + d = d |S| + 1`, `d`, `c_a` the
numbers of maximal ideals of `A` containing `z - c`, `z - a`. -/
theorem exists_fundamentalGroup_analytification_specLFT_mulEquiv_surfaceGroup_of_finset
    {A : Type u} [CommRing A] [Algebra (ULift.{u} ℂ) A] [Algebra.FiniteType (ULift.{u} ℂ) A]
    [IsDomain A]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A)))]
    (ι : specLFT A ⟶ Y) [IsOpenImmersion ι.hom.left] [ConnectedSpace Y.obj.left]
    [SmoothOfRelativeDimension 1 Y.obj.hom]
    [T2Space (analytification.obj Y)] [CompactSpace (analytification.obj Y)]
    (p : Y.obj.left) (hp : Set.range ι.hom.left.base = {p}ᶜ)
    (z : A) (hfin : (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).Finite)
    (S : Finset ℂ) (hSne : S.Nonempty)
    (het : ((algebraMap A (Localization.Away
      (MvPolynomial.aeval (R := ULift.{u} ℂ) (fun _ : Fin 1 ↦ z) (branchPoly S)))).comp
        (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).toRingHom).Etale)
    {c : ℂ} (hc : c ∉ S) (y : analytification.obj Y) :
    ∃ g : ℕ, Nonempty (FundamentalGroup (analytification.obj Y) y ≃* Pi1.SurfaceGroup g 0) ∧
      2 * g + ∑ a ∈ S, fiberCard A z a + fiberCard A z c = fiberCard A z c * S.card + 1 := by
  let s := specCoord z
  have hs := specCoord_comp_C z
  haveI : ConnectedSpace (specLFT A).obj.left :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of A)))
  have hsfin : s.Finite := by
    refine RingHom.Finite.comp ?_ hfin
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have het' := etale_specCoord z _ het
  haveI := t2Space_analytification_of_isAffine (specLFT A)
  haveI : SmoothOfRelativeDimension 1 (specLFT A).obj.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A))))
  haveI := connectedSpace_analytification (specLFT A)
  haveI := BranchedCover.locallyPathConnectedSpace_of_charts
    (exists_chart_analytification (specLFT A))
  have hfib := finite_coordFun_fiber s hs hsfin
  have hfinS : {P | coordFun s hs P ∈ S}.Finite := by
    have : {P | coordFun s hs P ∈ S} = ⋃ a ∈ S, coordFun s hs ⁻¹' {a} := by ext; simp
    rw [this]
    exact S.finite_toSet.biUnion fun a _ ↦ hfib a
  obtain ⟨D⟩ := BranchedCover.nonempty_discData (isClosedMap_coordFun s hs hsfin) hfinS
    (fun P _ ↦ exists_chart_analytification (specLFT A) P)
  haveI : Nonempty (BranchedCover.Punct (coordFun s hs) S) :=
    (BranchedCover.isConnected_punct D).nonempty.to_subtype
  obtain ⟨e₀, he₀⟩ := BranchedCover.exists_eq_of_notMem (isClosedMap_coordFun s hs hsfin) hfib
    (isLocalHomeomorphOn_coordFun s hs _ het') hc
  have hj := isOpenEmbedding_analytification_map ι
  obtain ⟨q, -, hq⟩ := exists_range_analytification_map_eq ι p hp
  let j : C(analytification.obj (specLFT A), analytification.obj Y) :=
    ⟨_, (analytification.map ι).toLRSHom.base.hom.continuous⟩
  obtain ⟨g, ⟨Φ⟩, hcard⟩ :=
    BranchedCover.Gen.exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_finset (j := j) S hSne
      (isClosedMap_coordFun s hs hsfin) hfib (isLocalHomeomorphOn_coordFun s hs _ het')
      (fun P _ ↦ exists_chart_analytification (specLFT A) P) hj hq
      (exists_chart_analytification Y q) e₀ (he₀ ▸ hc)
  haveI := connectedSpace_analytification Y
  haveI := BranchedCover.locallyPathConnectedSpace_of_charts (exists_chart_analytification Y)
  haveI : PathConnectedSpace (analytification.obj Y) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  refine ⟨g, ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath
    (PathConnectedSpace.somePath y _)).trans Φ⟩, ?_⟩
  rw [he₀, BranchedCover.nat_card_mem_eq_sum hfib] at hcard
  have hf : ∀ a, Nat.card (coordFun s hs ⁻¹' {a}) = fiberCard A z a :=
    nat_card_coordFun_specCoord_fiber z
  simp only [hf] at hcard
  exact hcard

end ComplexAnalytic

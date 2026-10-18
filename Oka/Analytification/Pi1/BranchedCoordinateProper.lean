/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Analytification.Pi1.BranchedCoordinateSpec
import Oka.Analytification.GAGA.OpenImmersion
import Oka.Topology.Covering.BranchedSurface

/-!
# The fundamental group of a compact curve with a Belyi coordinate and one pole

Let `Y` be a scheme locally of finite type over `ℂ`, smooth of relative dimension one, with
`Y^an` compact Hausdorff, and `ι : V ⟶ Y` an open immersion of an affine connected `V` whose
image is `Y ∖ {p}` for a single point `p`. Let `z = s(X₀) ∈ Γ(V, 𝒪_V)` make `Γ(V, 𝒪_V)` a finite
`ℂ[z]`-algebra, étale over `𝔸¹ ∖ {0, 1}`. (This is the situation of a compact curve with a
Belyi map `Y → ℙ¹` with a single point `p` over `∞` and `V = Y ∖ {p}`.)

Then `π₁(Y^an)` is the closed surface group `Π_{g,0}`, with `2g + #(z^an)⁻¹{0, 1} + d = 2d + 1`
for `d` the number of points of a fibre of `z^an` over `ℂ ∖ {0, 1}`
(`ComplexAnalytic.exists_fundamentalGroup_analytification_mulEquiv_surfaceGroup`).

## Proof

`z^an : V^an → ℂ` is a branched covering of the plane
(`Oka/Analytification/Pi1/BranchedCoordinate.lean`), `ι^an` is an open embedding onto
`Y^an ∖ {p^an}` (the points of `Y^an` are the closed points of `Y`,
`ComplexAnalytic.range_analytificationπ_base`), and `p^an` has a chart. Compactness of `Y^an`
and properness of `z^an` give the disc data at infinity (`BranchedCover.nonempty_inftyData`), so
`BranchedCover.exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_charts` applies.
-/

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

/-- A chart at `e a` pulls back along an open embedding `e` to a chart at `a`. -/
theorem exists_chart_of_isOpenEmbedding {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [Nonempty A] {e : A → B} (he : IsOpenEmbedding e) (a : A)
    (h : ∃ φ : OpenPartialHomeomorph B ℂ, e a ∈ φ.source) :
    ∃ φ : OpenPartialHomeomorph A ℂ, a ∈ φ.source := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(he.toOpenPartialHomeomorph e).trans φ, ?_⟩
  rw [OpenPartialHomeomorph.trans_source, IsOpenEmbedding.toOpenPartialHomeomorph_source]
  exact ⟨trivial, hφ⟩

variable {V Y : SchemeLFTℂ.{u}} (ι : V ⟶ Y) [IsOpenImmersion ι.hom.left]

/-- If the open immersion `ι` has image `Y ∖ {p}`, then `ι^an` has image `Y^an ∖ {p^an}` for the
unique point `p^an` of `Y^an` over `p`. -/
theorem exists_range_analytification_map_eq (p : Y.obj.left)
    (hp : Set.range ι.hom.left.base = {p}ᶜ) :
    ∃ q : analytification.obj Y, (analytificationπ Y).left.base q = p ∧
      Set.range (analytification.map ι).toLRSHom.base = {q}ᶜ := by
  have hcl : IsClosed {p} := by
    rw [← isOpen_compl_iff, ← hp]
    exact ι.hom.left.isOpenEmbedding.isOpen_range
  obtain ⟨q, hq⟩ := (mem_range_analytificationπ_base_iff Y p).2 hcl
  refine ⟨q, hq, ?_⟩
  rw [range_analytification_map]
  ext y
  change (analytificationπ Y).left.base y ∈ Set.range ι.hom.left.base ↔ y ∈ ({q}ᶜ : Set _)
  rw [hp]
  change ¬ ((analytificationπ Y).left.base y = p) ↔ ¬ (y = q)
  rw [← hq]
  exact not_congr (analytificationπ_base_injective Y).eq_iff

variable [IsAffine V.obj.left] (s : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ(V.obj.left, ⊤))
  (hs : s.comp MvPolynomial.C = V.constMap)

/-- **`π₁` of a compact curve with a Belyi coordinate having one pole is a closed surface
group.** Let `ι : V ⟶ Y` be an open immersion with image `Y ∖ {p}`, `V` affine and connected, `Y`
smooth of relative dimension one over `ℂ` with `Y^an` compact Hausdorff, and
`s : ℂ[X₀] → Γ(V, 𝒪_V)` finite and étale after inverting `z (z - 1)`, `z = s(X₀)`. Then for every
`e₀ ∈ V^an` with `z(e₀) ∉ {0, 1}`, `π₁(Y^an, ι(e₀)) ≃* Π_{g,0}` with
`2g + #(z^an)⁻¹{0, 1} + d = 2d + 1`, `d` the number of points of `V^an` with `z = z(e₀)`. -/
theorem exists_fundamentalGroup_analytification_mulEquiv_surfaceGroup
    [ConnectedSpace V.obj.left] [SmoothOfRelativeDimension 1 Y.obj.hom]
    [T2Space (analytification.obj Y)] [CompactSpace (analytification.obj Y)]
    (p : Y.obj.left) (hp : Set.range ι.hom.left.base = {p}ᶜ) (hsfin : s.Finite)
    (het : ((algebraMap Γ(V.obj.left, ⊤) Γ(V.obj.left, V.obj.left.basicOpen
      (s (branchPoly ({0, 1} : Finset ℂ))))).comp s).Etale)
    (e₀ : analytification.obj V) (he₀ : coordFun s hs e₀ ∉ ({0, 1} : Finset ℂ)) :
    ∃ g : ℕ, Nonempty (FundamentalGroup (analytification.obj Y)
        ((analytification.map ι).toLRSHom.base e₀) ≃* Pi1.SurfaceGroup g 0) ∧
      2 * g + Nat.card {P : analytification.obj V // coordFun s hs P ∈ ({0, 1} : Finset ℂ)} +
          Nat.card (coordFun s hs ⁻¹' {coordFun s hs e₀}) =
        2 * Nat.card (coordFun s hs ⁻¹' {coordFun s hs e₀}) + 1 := by
  have hj := isOpenEmbedding_analytification_map ι
  haveI : Nonempty (analytification.obj V) := ⟨e₀⟩
  haveI : T2Space (analytification.obj V) := hj.isEmbedding.t2Space
  haveI := connectedSpace_analytification V
  have hchart : ∀ P : analytification.obj V, ∃ φ : OpenPartialHomeomorph _ ℂ, P ∈ φ.source :=
    fun P ↦ exists_chart_of_isOpenEmbedding hj P (exists_chart_analytification Y _)
  haveI := BranchedCover.locallyPathConnectedSpace_of_charts hchart
  obtain ⟨q, -, hq⟩ := exists_range_analytification_map_eq ι p hp
  let j : C(analytification.obj V, analytification.obj Y) :=
    ⟨_, (analytification.map ι).toLRSHom.base.hom.continuous⟩
  obtain ⟨φ, hφ⟩ := exists_chart_analytification Y q
  obtain ⟨I⟩ := BranchedCover.nonempty_inftyData (j := j) (isClosedMap_coordFun s hs hsfin)
    (finite_coordFun_fiber s hs hsfin) hj hq φ hφ
  exact BranchedCover.exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_charts
    (isClosedMap_coordFun s hs hsfin) (finite_coordFun_fiber s hs hsfin)
    (isLocalHomeomorphOn_coordFun s hs _ het) (fun P _ ↦ hchart P) hj.isEmbedding hq I e₀ he₀

/-- **`π₁` of a compact curve with a Belyi coordinate having one pole**, ring-theoretic form:
`A` a finitely generated `ℂ`-algebra which is a domain, smooth of relative dimension one,
`ι : Spec A ⟶ Y` an open immersion with image `Y ∖ {p}`, `Y` connected, smooth of relative
dimension one, `Y^an` compact Hausdorff, `z ∈ A` with `ℂ[z] → A` finite and étale after
inverting `z (z - 1)`. Then for every `c ∈ ℂ ∖ {0, 1}` and every `y ∈ Y^an`,
`π₁(Y^an, y) ≃* Π_{g,0}` with `2g + (c₀ + c₁) + d = 2d + 1`, `d`, `c₀`, `c₁` the numbers of
maximal ideals of `A` containing `z - c`, `z`, `z - 1`. -/
theorem exists_fundamentalGroup_analytification_specLFT_mulEquiv_surfaceGroup
    {A : Type u} [CommRing A] [Algebra (ULift.{u} ℂ) A] [Algebra.FiniteType (ULift.{u} ℂ) A]
    [IsDomain A]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A)))]
    (ι : specLFT A ⟶ Y) [IsOpenImmersion ι.hom.left] [ConnectedSpace Y.obj.left]
    [SmoothOfRelativeDimension 1 Y.obj.hom]
    [T2Space (analytification.obj Y)] [CompactSpace (analytification.obj Y)]
    (p : Y.obj.left) (hp : Set.range ι.hom.left.base = {p}ᶜ)
    (z : A) (hfin : (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).Finite)
    (het : ((algebraMap A (Localization.Away
      (MvPolynomial.aeval (R := ULift.{u} ℂ) (fun _ : Fin 1 ↦ z)
        (branchPoly ({0, 1} : Finset ℂ))))).comp
        (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).toRingHom).Etale)
    {c : ℂ} (hc : c ∉ ({0, 1} : Finset ℂ)) (y : analytification.obj Y) :
    ∃ g : ℕ, Nonempty (FundamentalGroup (analytification.obj Y) y ≃* Pi1.SurfaceGroup g 0) ∧
      2 * g + (fiberCard A z 0 + fiberCard A z 1) + fiberCard A z c =
        2 * fiberCard A z c + 1 := by
  let s := specCoord z
  have hs := specCoord_comp_C z
  haveI : ConnectedSpace (specLFT A).obj.left :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of A)))
  have hsfin : s.Finite := by
    refine RingHom.Finite.comp ?_ hfin
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have het' := etale_specCoord z _ het
  -- a base point over `c`
  haveI := t2Space_analytification_of_isAffine (specLFT A)
  haveI : SmoothOfRelativeDimension 1 (specLFT A).obj.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A))))
  haveI := connectedSpace_analytification (specLFT A)
  haveI := BranchedCover.locallyPathConnectedSpace_of_charts
    (exists_chart_analytification (specLFT A))
  have hfib := finite_coordFun_fiber s hs hsfin
  have hfinS : {P | coordFun s hs P ∈ ({0, 1} : Finset ℂ)}.Finite := by
    have : {P | coordFun s hs P ∈ ({0, 1} : Finset ℂ)} =
        ⋃ a ∈ ({0, 1} : Finset ℂ), coordFun s hs ⁻¹' {a} := by ext; simp
    rw [this]
    exact Finset.finite_toSet _ |>.biUnion fun a _ ↦ hfib a
  obtain ⟨D⟩ := BranchedCover.nonempty_discData (isClosedMap_coordFun s hs hsfin) hfinS
    (fun P _ ↦ exists_chart_analytification (specLFT A) P)
  haveI : Nonempty (BranchedCover.Punct (coordFun s hs) ({0, 1} : Finset ℂ)) :=
    (BranchedCover.isConnected_punct D).nonempty.to_subtype
  obtain ⟨e₀, he₀⟩ := BranchedCover.exists_eq_of_notMem (isClosedMap_coordFun s hs hsfin) hfib
    (isLocalHomeomorphOn_coordFun s hs _ het') hc
  obtain ⟨g, ⟨Φ⟩, hcard⟩ := exists_fundamentalGroup_analytification_mulEquiv_surfaceGroup ι s hs
    p hp hsfin het' e₀ (he₀ ▸ hc)
  -- change of base point in `Y^an`
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
  rw [Finset.sum_pair (by norm_num)] at hcard
  exact hcard

end ComplexAnalytic

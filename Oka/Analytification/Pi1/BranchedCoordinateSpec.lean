/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Analytification.Pi1.BranchedCoordinate

/-!
# `π₁` of a smooth affine curve over `ℂ` with a branched coordinate, ring-theoretic form

This file restates `ComplexAnalytic.exists_fundamentalGroup_analytification_mulEquiv_freeGroup`
for `V = Spec A`, `A` a finitely generated `ℂ`-algebra which is a domain, with all hypotheses on
the ring `A` and an element `z ∈ A`:

* `ℂ[X₀] → A`, `X₀ ↦ z`, is finite;
* it is étale after inverting `∏_{a ∈ S} (z - a)`;
* `Spec A → Spec ℂ` is smooth of relative dimension one.

Then for every `c ∈ ℂ ∖ S` and every base point `x ∈ (Spec A)^an`, `π₁((Spec A)^an, x)` is free of
rank `d (|S| - 1) + 1 - ∑_{a ∈ S} c_a`, where `d` and `c_a` are the numbers of maximal ideals of
`A` containing `z - c` and `z - a` (`ComplexAnalytic.fiberCard`)
(`ComplexAnalytic.exists_fundamentalGroup_analytification_specLFT_mulEquiv_freeGroup`).

The fibres of `z^an` over `ℂ ∖ S` are nonempty (`BranchedCover.exists_eq_of_notMem`): the image
of the covering `X ∖ f⁻¹(S) → ℂ ∖ S` is open and closed.
-/

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace BranchedCover

variable {X : Type u} [TopologicalSpace X] {f : C(X, ℂ)} {S : Finset ℂ}

/-- **The fibres of a branched covering over `ℂ ∖ S` are nonempty** (if `X ∖ f⁻¹(S)` is). -/
theorem exists_eq_of_notMem [T2Space X] [Nonempty (Punct f S)] (hcl : IsClosedMap f)
    (hfib : ∀ z, (f ⁻¹' {z}).Finite) (hloc : IsLocalHomeomorphOn f {y | f y ∉ S}) {c : ℂ}
    (hc : c ∉ S) : ∃ e, f e = c := by
  have cov := isCoveringMap_punctMap hcl hfib hloc
  let x : Complex.PuncturedPlane.Region Set.univ S := ⟨c, trivial, hc⟩
  haveI := (Complex.PuncturedPlane.loopStatement S.card Set.univ isOpen_univ convex_univ S
    (Set.subset_univ _) rfl x).1
  have hcl' : IsClosedMap (punctMap f S) := by
    let g : ({z | z ∉ S} : Set ℂ) ≃ₜ Complex.PuncturedPlane.Region Set.univ S :=
      { toFun := fun z ↦ ⟨z.1, trivial, z.2⟩
        invFun := fun z ↦ ⟨z.1, z.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact g.isClosedMap.comp (hcl.restrictPreimage {z | z ∉ S})
  have hclopen : IsClopen (Set.range (punctMap f S)) :=
    ⟨hcl'.isClosed_range, cov.isOpenMap.isOpen_range⟩
  obtain ⟨e₀⟩ := (inferInstance : Nonempty (Punct f S))
  have huniv := hclopen.eq_univ ⟨_, Set.mem_range_self e₀⟩
  obtain ⟨e, he⟩ := huniv ▸ Set.mem_univ x
  exact ⟨e.1, congrArg Subtype.val he⟩

/-- The points over a finite set, counted fibre by fibre. -/
theorem nat_card_mem_eq_sum (hfib : ∀ z, (f ⁻¹' {z}).Finite) :
    Nat.card {P : X // f P ∈ S} = ∑ a ∈ S, Nat.card (f ⁻¹' {a}) := by
  classical
  haveI : ∀ a : S, Finite (f ⁻¹' {a.1}) := fun a ↦ (hfib a).to_subtype
  haveI : ∀ a : S, Fintype (f ⁻¹' {a.1}) := fun a ↦ Fintype.ofFinite _
  let F : {P : X // f P ∈ S} ≃ Σ a : S, f ⁻¹' {a.1} :=
    { toFun := fun P ↦ ⟨⟨f P.1, P.2⟩, P.1, rfl⟩
      invFun := fun p ↦ ⟨p.2.1, by rw [show f p.2.1 = p.1.1 from p.2.2]; exact p.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := by
        rintro ⟨⟨a, ha⟩, P, hP⟩
        dsimp only at hP
        subst hP
        rfl }
  rw [Nat.card_congr F, Nat.card_sigma, ← Finset.sum_coe_sort S]

end BranchedCover

namespace ComplexAnalytic

open AnalyticSpace

noncomputable section

variable (A : Type u) [CommRing A] [Algebra (ULift.{u} ℂ) A] [Algebra.FiniteType (ULift.{u} ℂ) A]

/-- `Spec A`, for a finitely generated `ℂ`-algebra `A`, as a scheme locally of finite type over
`ℂ`. -/
abbrev specLFT : SchemeLFTℂ.{u} :=
  SchemeLFTℂ.spec (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A))
    (RingHom.finiteType_algebraMap.2 inferInstance)

/-- The number of maximal ideals of `A` containing `z - c`. -/
def fiberCard (z : A) (c : ℂ) : ℕ :=
  Nat.card {M : MaximalSpectrum A // z - algebraMap (ULift.{u} ℂ) A ⟨c⟩ ∈ M.asIdeal}

instance : IsAffine (specLFT A).obj.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

variable {A}

/-- Maximal ideals containing an element, transported along a ring isomorphism. -/
def maximalSpectrumMemEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (a : R) :
    {M : MaximalSpectrum R // a ∈ M.asIdeal} ≃ {M : MaximalSpectrum S // e a ∈ M.asIdeal} where
  toFun M := ⟨⟨M.1.asIdeal.comap e.symm.toRingHom, Ideal.comap_isMaximal_of_equiv e.symm⟩, by
    change e.symm (e a) ∈ M.1.asIdeal
    rw [e.symm_apply_apply]
    exact M.2⟩
  invFun M := ⟨⟨M.1.asIdeal.comap e.toRingHom, Ideal.comap_isMaximal_of_equiv e⟩, M.2⟩
  left_inv M := by
    ext x
    change e.symm (e x) ∈ M.1.asIdeal ↔ x ∈ M.1.asIdeal
    rw [e.symm_apply_apply]
  right_inv M := by
    ext x
    change e (e.symm x) ∈ M.1.asIdeal ↔ x ∈ M.1.asIdeal
    rw [e.apply_symm_apply]

/-- The function `z`, as a map `ℂ[X₀] → Γ(Spec A, ⊤)`. -/
def specCoord (z : A) : MvPolynomial (Fin 1) (ULift.{u} ℂ) →+* Γ((specLFT A).obj.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp
    (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).toRingHom

lemma specCoord_comp_C (z : A) :
    (specCoord z).comp MvPolynomial.C = (specLFT A).constMap := by
  refine RingHom.ext fun c ↦ ?_
  have h := congrArg (fun φ ↦ φ.hom c) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A)))
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (MvPolynomial.aeval (fun _ : Fin 1 ↦ z) (MvPolynomial.C c)) =
    (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℂ))).inv.hom c)
  rw [MvPolynomial.aeval_C]
  exact h

/-- The points of `(Spec A)^an` over `c` are the maximal ideals of `A` containing `z - c`. -/
theorem nat_card_coordFun_specCoord_fiber (z : A) (c : ℂ) :
    Nat.card (coordFun (specCoord z) (specCoord_comp_C z) ⁻¹' {c}) = fiberCard A z c := by
  have he : (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
      (specCoord z (MvPolynomial.X 0 - MvPolynomial.C ⟨c⟩)) =
        z - algebraMap (ULift.{u} ℂ) A ⟨c⟩ := by
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom _) = _
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    simp [MvPolynomial.aeval_X]
  exact Nat.card_congr ((coordFunFiberEquiv (specCoord z) (specCoord_comp_C z) c).trans
    ((maximalSpectrumMemEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
      _).trans (Equiv.subtypeEquivRight fun M ↦ by rw [he])))

/-- `z` is étale over `𝔸¹ ∖ S` on `Spec A`, in the form used by
`ComplexAnalytic.isLocalHomeomorphOn_coordFun`. -/
theorem etale_specCoord (z : A) (S : Finset ℂ)
    (het : ((algebraMap A (Localization.Away
      (MvPolynomial.aeval (R := ULift.{u} ℂ) (fun _ : Fin 1 ↦ z) (branchPoly S)))).comp
        (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).toRingHom).Etale) :
    ((algebraMap Γ((specLFT A).obj.left, ⊤) Γ((specLFT A).obj.left,
      (specLFT A).obj.left.basicOpen (specCoord z (branchPoly S)))).comp (specCoord z)).Etale := by
  let eA := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  let h := MvPolynomial.aeval (R := ULift.{u} ℂ) (fun _ : Fin 1 ↦ z) (branchPoly S)
  let B := Γ((specLFT A).obj.left, (specLFT A).obj.left.basicOpen (specCoord z (branchPoly S)))
  haveI hloc₀ : IsLocalization.Away (specCoord z (branchPoly S)) B :=
    (isAffineOpen_top (specLFT A).obj.left).isLocalization_basicOpen _
  letI : Algebra A B := ((algebraMap Γ((specLFT A).obj.left, ⊤) B).comp eA.symm.toRingHom).toAlgebra
  haveI : IsLocalization (Submonoid.powers h) B := by
    have := IsLocalization.isLocalization_of_base_ringEquiv
      (Submonoid.powers (specCoord z (branchPoly S))) B eA
    have he : Submonoid.map eA (Submonoid.powers (specCoord z (branchPoly S))) =
        Submonoid.powers h := by
      rw [Submonoid.map_powers]
      change Submonoid.powers (eA (eA.symm h)) = _
      rw [RingEquiv.apply_symm_apply]
    convert this <;> first | exact he.symm | rfl
  let φ := IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h) B
  have e : (algebraMap Γ((specLFT A).obj.left, ⊤) B).comp (specCoord z) =
      φ.toRingEquiv.toRingHom.comp ((algebraMap A (Localization.Away h)).comp
        (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).toRingHom) :=
    RingHom.ext fun p ↦ (φ.commutes _).symm
  rw [e]
  exact RingHom.Etale.respectsIso.1 _ φ.toRingEquiv het

/-- **`π₁` of a smooth affine curve over `ℂ` with a branched coordinate**, ring-theoretic form:
for `A` a finitely generated `ℂ`-algebra which is a domain, smooth of relative dimension one,
and `z ∈ A` with `ℂ[z] → A` finite and étale after inverting `∏_{a ∈ S} (z - a)`, for every
`c ∈ ℂ ∖ S` and every point `x` of `(Spec A)^an`, `π₁((Spec A)^an, x)` is free of rank
`d (|S| - 1) + 1 - ∑_{a ∈ S} c_a`, `d`, `c_a` the numbers of maximal ideals containing `z - c`,
`z - a`. -/
theorem exists_fundamentalGroup_analytification_specLFT_mulEquiv_freeGroup [IsDomain A]
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A)))]
    (z : A) (hfin : (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).Finite)
    (S : Finset ℂ)
    (het : ((algebraMap A (Localization.Away
      (MvPolynomial.aeval (R := ULift.{u} ℂ) (fun _ : Fin 1 ↦ z) (branchPoly S)))).comp
        (MvPolynomial.aeval (R := ULift.{u} ℂ) fun _ : Fin 1 ↦ z).toRingHom).Etale)
    {c : ℂ} (hc : c ∉ S) (x : analytification.obj (specLFT A)) :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (FundamentalGroup (analytification.obj (specLFT A)) x ≃* FreeGroup ι) ∧
      Nat.card ι + fiberCard A z c + ∑ a ∈ S, fiberCard A z a =
        fiberCard A z c * S.card + 1 := by
  let s := specCoord z
  have hs := specCoord_comp_C z
  haveI : SmoothOfRelativeDimension 1 (specLFT A).obj.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) A))))
  haveI : ConnectedSpace (specLFT A).obj.left :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of A)))
  -- finiteness
  have hsfin : s.Finite := by
    refine RingHom.Finite.comp ?_ hfin
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have het' := etale_specCoord z S het
  -- the base point over `c`
  haveI := t2Space_analytification_of_isAffine (specLFT A)
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
    (isLocalHomeomorphOn_coordFun s hs S het') hc
  obtain ⟨ι, hι, ⟨Φ⟩, hcard⟩ := exists_fundamentalGroup_analytification_mulEquiv_freeGroup s hs
    hsfin S het' e₀ (he₀ ▸ hc)
  haveI : PathConnectedSpace (analytification.obj (specLFT A)) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  refine ⟨ι, hι, ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath
    (PathConnectedSpace.somePath x e₀)).trans Φ⟩, ?_⟩
  rw [he₀, BranchedCover.nat_card_mem_eq_sum hfib] at hcard
  have hf : ∀ a, Nat.card (coordFun s hs ⁻¹' {a}) = fiberCard A z a :=
    nat_card_coordFun_specCoord_fiber z
  simp only [hf] at hcard
  exact hcard

end

end ComplexAnalytic

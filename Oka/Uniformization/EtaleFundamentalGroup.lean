/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Uniformization.FundamentalGroup
import Oka.Analytification.SchemeAffine
import Oka.Analytification.Pi1.General
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# The étale fundamental group of a once-punctured elliptic curve over `ℂ`

For an elliptic curve `W` over `ℂ`, let `E ∖ O = Spec ℂ[x, y] ⧸ (W(x, y))`
(`Uniformization.oncePunctured W`, a scheme locally of finite type over `ℂ`). Then for every
point `x` of its analytification, with `ξₓ` the geometric point at `x`,

  `π₁ᵉᵗ(E ∖ O, ξₓ) ≃ₜ* F̂₂`   (`Uniformization.nonempty_etaleFundamentalGroup_equiv`),

the profinite completion of the free group on two generators, i.e. of the surface group
`Π_{1,1} = ⟨a, b, c | [a, b] c = 1⟩ ≅ F(a, b)`. This is the case `(g, r) = (1, 1)` of the
comparison `π₁ᵉᵗ(X) ≅ Π̂_{g,r}` for hyperbolic curves over `ℂ`.

Ingredients:
* the comparison theorem `ComplexAnalytic.etaleFundamentalGroupEquivCompletion`:
  `π₁ᵉᵗ(X, ξₓ) ≃ₜ* π₁(X^an, x)^`;
* `ComplexAnalytic.analytificationSpecIso`: `(E ∖ O)^an` is the zero locus of `W(x, y)` in `ℂ²`,
  i.e. homeomorphic to the affine points `V W` (`Uniformization.analytificationHomeomorph`);
* `Uniformization.IsUniformization.fundamentalGroupEquiv`: `π₁(V W, x) ≃* F₂`
  (uniformisation by `ℍ` and ping-pong);
* `ℂ[x, y] ⧸ (W(x, y)) ≅ ℂ[W]` is a domain, so `E ∖ O` is connected.
-/

open CategoryTheory AlgebraicGeometry ComplexAnalytic Topology ProfiniteGrp.ProfiniteCompletion

namespace Uniformization

/-! ### The coordinate ring -/

/-- `Polynomial (Polynomial ℂ) → ℂ[x₀, x₁]`, `X ↦ x₀`, `Y ↦ x₁`. -/
noncomputable def toMv : Polynomial (Polynomial ℂ) →+* MvPolynomial (ULift.{0} (Fin 2)) ℂ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X ⟨0⟩))
    (MvPolynomial.X ⟨1⟩)

/-- `ℂ[x₀, x₁] → Polynomial (Polynomial ℂ)`, `x₀ ↦ X`, `x₁ ↦ Y`. -/
noncomputable def ofMv : MvPolynomial (ULift.{0} (Fin 2)) ℂ →+* Polynomial (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    fun i ↦ if i.down = 0 then Polynomial.C Polynomial.X else Polynomial.X

lemma ofMv_toMv : ofMv.comp toMv = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a; simp [toMv, ofMv]
    · simp [toMv, ofMv]
  · simp [toMv, ofMv]

lemma toMv_ofMv : toMv.comp ofMv = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [toMv, ofMv]
  · rintro ⟨i⟩
    fin_cases i <;> simp [toMv, ofMv]

/-- `Polynomial (Polynomial ℂ) ≃ ℂ[x₀, x₁]`. -/
noncomputable def mvEquiv : Polynomial (Polynomial ℂ) ≃+* MvPolynomial (ULift.{0} (Fin 2)) ℂ :=
  RingEquiv.ofRingHom toMv ofMv toMv_ofMv ofMv_toMv

lemma eval_toMv (y : ULift.{0} (Fin 2) → ℂ) (P : Polynomial (Polynomial ℂ)) :
    MvPolynomial.eval y (toMv P) = P.evalEval (y ⟨0⟩) (y ⟨1⟩) := by
  have : (MvPolynomial.eval y).comp toMv = Polynomial.evalEvalRingHom (y ⟨0⟩) (y ⟨1⟩) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a; simp [toMv]
      · simp [toMv]
    · simp [toMv]
  exact congrArg (fun f : Polynomial (Polynomial ℂ) →+* ℂ ↦ f P) this

variable (W : WeierstrassCurve ℂ)

/-- The Weierstrass polynomial of `W` in the coordinates `x₀ = x`, `x₁ = y`. -/
noncomputable def weierstrassMv : Fin 1 → MvPolynomial (ULift.{0} (Fin 2)) ℂ :=
  ![toMv W.toAffine.polynomial]

lemma span_weierstrassMv :
    Ideal.span (Set.range (weierstrassMv W)) =
      (Ideal.span {W.toAffine.polynomial}).map (mvEquiv : Polynomial (Polynomial ℂ) →+* _) := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 1
  simp [weierstrassMv, mvEquiv]

lemma isDomain_quotient :
    IsDomain (MvPolynomial (ULift.{0} (Fin 2)) ℂ ⧸ Ideal.span (Set.range (weierstrassMv W))) := by
  have e := Ideal.quotientEquiv (Ideal.span {W.toAffine.polynomial})
    (Ideal.span (Set.range (weierstrassMv W))) mvEquiv (span_weierstrassMv W)
  haveI : IsDomain (Polynomial (Polynomial ℂ) ⧸ Ideal.span {W.toAffine.polynomial}) :=
    (inferInstance : IsDomain W.toAffine.CoordinateRing)
  exact e.symm.toMulEquiv.isDomain

lemma eval_weierstrassMv_iff (y : ULift.{0} (Fin 2) → ℂ) :
    (∀ j, MvPolynomial.eval y (weierstrassMv W j) = 0) ↔ W.toAffine.Equation (y ⟨0⟩) (y ⟨1⟩) := by
  simp [weierstrassMv, eval_toMv, WeierstrassCurve.Affine.Equation]

/-! ### The scheme `E ∖ O` and its analytification -/

/-- **The once-punctured elliptic curve** `E ∖ O = Spec ℂ[x, y] ⧸ (W(x, y))`, as a scheme locally
of finite type over `ℂ`. -/
noncomputable abbrev oncePunctured : SchemeLFTℂ.{0} :=
  SchemeLFTℂ.specPresentation (weierstrassMv W)

instance : ConnectedSpace (oncePunctured W).obj.left := by
  haveI := isDomain_quotient W
  change ConnectedSpace (PrimeSpectrum (PresentedAlgebra 2 1 (weierstrassMv W)))
  infer_instance

/-- The zero locus of `W(x, y)` in `ℂ²` is the set `V W` of affine points. -/
noncomputable def zeroLocusHomeomorph :
    AnalyticSpace.analytification (weierstrassMv W) ≃ₜ V W where
  toFun y := ⟨(y.1.1 ⟨0⟩, y.1.1 ⟨1⟩), (eval_weierstrassMv_iff W _).1
    ((mem_zeroLocus_polySection_iff _ _).1 y.2)⟩
  invFun p := ⟨⟨fun i ↦ if i.down = 0 then p.1.1 else p.1.2, trivial⟩,
    (mem_zeroLocus_polySection_iff _ _).2 ((eval_weierstrassMv_iff W _).2 (by
      have hp : W.toAffine.Equation p.1.1 p.1.2 := p.2
      simpa using hp))⟩
  left_inv y := by
    apply Subtype.ext; apply Subtype.ext
    funext ⟨i⟩
    fin_cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine Continuous.prodMk ?_ ?_ <;>
      exact (continuous_apply _).comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    refine continuous_pi fun i ↦ ?_
    split_ifs
    · exact continuous_fst.comp continuous_subtype_val
    · exact continuous_snd.comp continuous_subtype_val

/-- **`(E ∖ O)^an` is homeomorphic to the affine points `V W ⊆ ℂ²` of `W`.** -/
noncomputable def analytificationHomeomorph :
    analytification.obj (oncePunctured W) ≃ₜ V W :=
  (LocallyRingedSpace.homeoOfIso
    (AnalyticSpace.forgetToLocallyRingedSpace.mapIso (analytificationSpecIso (weierstrassMv W)))
    ).trans (zeroLocusHomeomorph W)

/-! ### Fundamental groups -/

/-- Homeomorphic spaces have isomorphic fundamental groups. -/
noncomputable def fundamentalGroupMulEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MonoidHom.toMulEquiv (FundamentalGroup.map (e : C(X, Y)) x)
    (FundamentalGroup.mapOfEq (e.symm : C(Y, X)) (e.symm_apply_apply x))
    (by
      ext p
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, FundamentalGroup.mapOfEq_apply]
      induction p using Quotient.inductionOn with
      | h γ =>
        change (⟦((γ.map e.continuous).map e.symm.continuous).cast _ _⟧ :
          Path.Homotopic.Quotient x x) = ⟦γ⟧
        congr 1
        ext t
        exact e.symm_apply_apply (γ t))
    (by
      ext p
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      induction p using Quotient.inductionOn with
      | h γ =>
        rw [FundamentalGroup.mapOfEq_apply]
        change (⟦(((γ.map e.symm.continuous).cast _ _).map e.continuous)⟧ :
          Path.Homotopic.Quotient (e x) (e x)) = ⟦γ⟧
        congr 1
        ext t
        simp)

/-- A group isomorphism induces an isomorphism of profinite completions. -/
noncomputable def completionCongr {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    completion (GrpCat.of G) ≃ₜ* completion (GrpCat.of H) :=
  let i := ProfiniteGrp.profiniteCompletion.mapIso
    (MulEquiv.toGrpIso (X := GrpCat.of G) (Y := GrpCat.of H) e)
  { toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp
    map_mul' := map_mul i.hom.hom
    continuous_toFun := i.hom.hom.continuous
    continuous_invFun := i.inv.hom.continuous }

/-- **`π₁(E(ℂ) ∖ {O}) ≅ F₂`**, on the analytification of the scheme `E ∖ O`. -/
theorem nonempty_fundamentalGroup_analytification_mulEquiv [W.IsElliptic]
    (x : analytification.obj (oncePunctured W)) :
    Nonempty (FundamentalGroup (analytification.obj (oncePunctured W)) x ≃*
      FreeGroup (Fin 2)) := by
  obtain ⟨e⟩ := nonempty_fundamentalGroup_mulEquiv W (analytificationHomeomorph W x)
  exact ⟨(fundamentalGroupMulEquiv (analytificationHomeomorph W) x).trans e⟩

/-- **The étale fundamental group of a once-punctured elliptic curve over `ℂ` is the profinite
completion of the free group of rank two**, `π₁ᵉᵗ(E ∖ O, ξₓ) ≃ₜ* F̂₂ ≅ Π̂_{1,1}`. -/
theorem nonempty_etaleFundamentalGroup_equiv [W.IsElliptic]
    (x : analytification.obj (oncePunctured W)) :
    Nonempty (Aut (FiniteEtale.fiber (geometricPoint (oncePunctured W) x)) ≃ₜ*
      completion (GrpCat.of (FreeGroup (Fin 2)))) := by
  obtain ⟨e⟩ := nonempty_fundamentalGroup_analytification_mulEquiv W x
  exact ⟨(etaleFundamentalGroupEquivCompletion x).trans (completionCongr e)⟩

end Uniformization

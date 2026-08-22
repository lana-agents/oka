/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.UniversalProperty

/-!
# Presentation-independence of the analytification

`Oka/Analytification/UniversalProperty.lean` proves that for polynomials `g₁, …, g_k` in `n`
variables, morphisms `Z ⟶ X^an` correspond to tuples of `n` global sections of `𝒪_Z` satisfying
the equations, and deduces that `X^an` depends only on the **ideal** the `gⱼ` generate. That is
independence of the *generators*, inside one fixed polynomial ring.

**This file removes the fixed polynomial ring.** A `ℂ`-algebra map `ℂ[y] ⧸ J → ℂ[x] ⧸ I` induces a
morphism of analytifications the other way (`ComplexAnalytic.analytificationMap`), functorially,
**with no relation assumed between the two numbers of variables or the two numbers of equations**.
So two presentations of the same finitely generated `ℂ`-algebra — in different numbers of
variables, with different numbers of relations — have isomorphic analytifications:
`ComplexAnalytic.analytificationIsoOfPresHom`.

Together with the universal property this is presentation-independence of the analytification on
objects: `X^an` depends only on the algebra `ℂ[x] ⧸ I`, not on how it was presented.

## How little there is to it, and why that is the surprise

The route one expects — compare two subspaces of two different `ℂ^n`, transport along a change of
coordinates — is not taken and is not needed. **The universal property does all the work**, and
the mechanism is one lemma:

```
ComplexAnalytic.eval₂Hom_transported :
  MvPolynomial.eval₂Hom (analytification g).algebraMap (transported ψ)
    = ((quotientToGlobal g).comp ψ.toRingHom).comp (Ideal.Quotient.mk (presentationIdeal g'))
```

Substituting the *transported* tuple into a polynomial of the target presentation is applying the
`ℂ`-algebra map to its class. Once that is known, `g' j ↦ 0` because `g' j` is in the ideal being
quotiented, so the transported tuple satisfies the target equations and
`ComplexAnalytic.liftHom` produces the morphism. `n` and `n'` never meet.

Both sides of that identity are ring homomorphisms out of `MvPolynomial`, so it is
`MvPolynomial.ringHom_ext` — the same tool as the substitution formula it rests on. On a constant
it is `ComplexAnalytic.quotientToGlobal_mk_C`; on a variable it is `rfl`.

## Functoriality, and what it buys

`ComplexAnalytic.analytificationMap_id` and `ComplexAnalytic.analytificationMap_comp` are proved
from `ComplexAnalytic.hom_ext_analytification` and the naturality of
`ComplexAnalytic.quotientToGlobal` along the induced morphism
(`ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal`). They are what turn an
isomorphism of presented algebras into an isomorphism of analytifications, which is the point.

## What is still not here

* **A functor.** `ComplexAnalytic.analytificationMap` is contravariant, identity-preserving and
  composition-preserving, so the data of one exists, but nothing here is stated as a
  `CategoryTheory.Functor` and the assignment on objects still takes a *tuple* rather than a
  finitely presented `ℂ`-algebra. That is `Oka/Analytification/Functor.lean`, which bundles
  `ComplexAnalytic.PresHom` as a category and this file's two functoriality lemmas as
  `ComplexAnalytic.analytificationFunctor`, and then removes the presentation from the source.
  The presentation is not *constructed* there — the earlier version of this paragraph said it
  would have to be — but chosen, by the inverse of an equivalence of categories.
* **The comparison with `Spec`.** `ComplexAnalytic.analytificationToSpec` is not shown natural in
  the presentation.
* **Anything analytic.** Every proof here is `MvPolynomial.ringHom_ext` and category-theoretic
  bookkeeping; the analytic content is upstream, in the universal property.

## Main definitions

- `ComplexAnalytic.PresHom`: a `ℂ`-algebra map between two presented algebras, spelled as a ring
  map plus the commutation it must satisfy — **there is no `Algebra ℂ` instance on these
  quotients and none is manufactured.**
- `ComplexAnalytic.transported`: the tuple of sections of `𝒪_{X^an}` that a `PresHom` names.
- `ComplexAnalytic.analytificationMap`: **the induced morphism of analytifications.**
- `ComplexAnalytic.analytificationIsoOfPresHom`: **two presentations of one algebra have
  isomorphic analytifications**, with no relation between their numbers of variables.

## Main results

- `ComplexAnalytic.eval₂Hom_transported`: substituting the transported tuple is applying the
  `ℂ`-algebra map.
- `ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal`: `quotientToGlobal` is natural
  along the induced morphism.
- `ComplexAnalytic.analytificationMap_id` and `ComplexAnalytic.analytificationMap_comp`:
  **functoriality.**

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n n' n'' k k' k'' : ℕ}

/-! ### Constants -/

/-- **A constant of `ℂ[x] ⧸ I`, read as a global section of `𝒪_{X^an}`, is that constant.**

`ComplexAnalytic.quotientToGlobal` was built in `Oka/Analytification/Presentation.lean` before
the analytification had a `ℂ`-linear structure map named beside it; this is the compatibility,
and it is `ComplexAnalytic.polyToGlobal_eq_eval₂Hom` at a constant. Both halves of this file need
it. -/
theorem quotientToGlobal_mk_C (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) (c : ℂ) :
    quotientToGlobal.{u} g (Ideal.Quotient.mk (presentationIdeal.{u} g) (MvPolynomial.C c)) =
      (AnalyticSpace.analytification.{u} g).algebraMap c :=
  (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) (MvPolynomial.C c)).trans
    (MvPolynomial.eval₂Hom_C _ _ c)

/-- **A variable of `ℂ[x] ⧸ I`, read as a global section of `𝒪_{X^an}`, is the corresponding
coordinate of `X^an`.** The companion of `ComplexAnalytic.quotientToGlobal_mk_C`. -/
theorem quotientToGlobal_mk_X (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (i : ULift.{u} (Fin n)) :
    quotientToGlobal.{u} g (Ideal.Quotient.mk (presentationIdeal.{u} g) (MvPolynomial.X i)) =
      analytificationCoord.{u} g i :=
  (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) (MvPolynomial.X i)).trans
    (MvPolynomial.eval₂Hom_X' _ _ i)

/-! ### `ℂ`-algebra maps of presented algebras -/

/-- A `ℂ`-algebra map between two presented algebras, spelled as a ring map together with the
commutation it has to satisfy. -/
structure PresHom (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ) where
  /-- The underlying ring map, which goes the other way from the induced morphism of spaces. -/
  toRingHom : PresentedAlgebra.{u} n' k' g' →+* PresentedAlgebra.{u} n k g
  /-- It fixes the constants. -/
  commutes : toRingHom.comp (presentedAlgebraMap.{u} g') = presentedAlgebraMap.{u} g

variable {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
  {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}
  {g'' : Fin k'' → MvPolynomial (ULift.{u} (Fin n'')) ℂ}

/-- Two `ℂ`-algebra maps of presented algebras with the same underlying ring map are equal: the
commutation is a proposition. -/
@[ext]
theorem PresHom.ext {ψ χ : PresHom.{u} g g'} (h : ψ.toRingHom = χ.toRingHom) : ψ = χ := by
  cases ψ; cases χ; simp_all

/-- The identity `ℂ`-algebra map. -/
def PresHom.id (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) : PresHom.{u} g g :=
  ⟨RingHom.id _, RingHom.id_comp _⟩

/-- Composition, in the order the induced morphisms of spaces compose. -/
def PresHom.comp (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g'') : PresHom.{u} g g'' :=
  ⟨ψ.toRingHom.comp χ.toRingHom, by
    rw [RingHom.comp_assoc, χ.commutes, ψ.commutes]⟩

/-! ### The induced morphism of analytifications -/

/-- The `n'` global sections of `𝒪_{X^an_g}` that a `PresHom` names: the images of the variables
of the target presentation. -/
def transported (ψ : PresHom.{u} g g') :
    ULift.{u} (Fin n') → (AnalyticSpace.analytification.{u} g).presheaf.obj (op ⊤) :=
  fun i ↦ quotientToGlobal.{u} g (ψ.toRingHom
    (Ideal.Quotient.mk (presentationIdeal.{u} g') (MvPolynomial.X i)))

/-- **Substituting the transported tuple into a polynomial of the target presentation is applying
the `ℂ`-algebra map to its class.**

This is the whole mechanism of this file. Both sides are ring homomorphisms out of
`MvPolynomial`, so `MvPolynomial.ringHom_ext` reduces it to constants — where it is
`ComplexAnalytic.quotientToGlobal_mk_C` fed by the `PresHom`'s commutation — and variables, where
it is `rfl` by the definition of `ComplexAnalytic.transported`.

Nothing here relates the two numbers of variables, which is why a change of variables costs no
more than a change of generators. -/
theorem eval₂Hom_transported (ψ : PresHom.{u} g g') :
    MvPolynomial.eval₂Hom (AnalyticSpace.analytification.{u} g).algebraMap
        (transported.{u} ψ) =
      ((quotientToGlobal.{u} g).comp ψ.toRingHom).comp
        (Ideal.Quotient.mk (presentationIdeal.{u} g')) := by
  refine (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)).symm
  · refine Eq.trans ?_ (MvPolynomial.eval₂Hom_C
      (AnalyticSpace.analytification.{u} g).algebraMap (transported.{u} ψ) c).symm
    exact (congrArg (quotientToGlobal.{u} g) (RingHom.congr_fun ψ.commutes c)).trans
      (quotientToGlobal_mk_C.{u} g c)
  · exact Eq.trans rfl (MvPolynomial.eval₂Hom_X'
      (AnalyticSpace.analytification.{u} g).algebraMap (transported.{u} ψ) i).symm

/-- **The transported tuple satisfies the target equations.**

Immediate from `ComplexAnalytic.eval₂Hom_transported`: `g' j` lies in the ideal being quotiented,
so its class is zero and any ring map out of the quotient kills it. This is the hypothesis
`ComplexAnalytic.liftHom` needs, and it is the only thing that had to be checked. -/
theorem eval₂_transported_eq_zero (ψ : PresHom.{u} g g') (j : Fin k') :
    MvPolynomial.eval₂ (AnalyticSpace.analytification.{u} g).algebraMap
      (transported.{u} ψ) (g' j) = 0 :=
  (RingHom.congr_fun (eval₂Hom_transported.{u} ψ) (g' j)).trans
    ((congrArg ((quotientToGlobal.{u} g).comp ψ.toRingHom)
      ((Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨j, rfl⟩))).trans (map_zero _))

/-- **A `ℂ`-algebra map of presented algebras induces a morphism of analytifications**, in the
opposite direction, with no relation assumed between the two numbers of variables. -/
def analytificationMap (ψ : PresHom.{u} g g') :
    AnalyticSpace.analytification.{u} g ⟶ AnalyticSpace.analytification.{u} g' :=
  liftHom.{u} g' _ (transported.{u} ψ) (eval₂_transported_eq_zero.{u} ψ)

/-- The coordinate pullbacks of the induced morphism are the transported tuple: the defining
property of `ComplexAnalytic.analytificationMap`. -/
theorem coordPullback_analytificationMap_comp (ψ : PresHom.{u} g g') (i : ULift.{u} (Fin n')) :
    AnalyticSpace.coordPullback
        (analytificationMap.{u} ψ ≫ analytificationInclHom.{u} g') i = transported.{u} ψ i :=
  coordPullback_liftHom_comp.{u} g' _ _ _ i

/-! ### Functoriality -/

/-- **Pulling a section of `𝒪_{X^an_{g'}}` back along the induced morphism is applying the
`ℂ`-algebra map**: `quotientToGlobal` is natural. -/
theorem Γ_map_analytificationMap_comp_quotientToGlobal (ψ : PresHom.{u} g g') :
    (LocallyRingedSpace.Γ.map (analytificationMap.{u} ψ).toLRSHom.op).hom.comp
        (quotientToGlobal.{u} g') =
      (quotientToGlobal.{u} g).comp ψ.toRingHom := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
  · refine Eq.trans (congrArg (LocallyRingedSpace.Γ.map
      (analytificationMap.{u} ψ).toLRSHom.op).hom (quotientToGlobal_mk_C.{u} g' c)) ?_
    refine Eq.trans ((analytificationMap.{u} ψ).isCLinear c) ?_
    exact (quotientToGlobal_mk_C.{u} g c).symm.trans
      (congrArg (quotientToGlobal.{u} g) (RingHom.congr_fun ψ.commutes c).symm)
  · refine Eq.trans (congrArg (LocallyRingedSpace.Γ.map
      (analytificationMap.{u} ψ).toLRSHom.op).hom (quotientToGlobal_mk_X.{u} g' i)) ?_
    refine Eq.trans (AnalyticSpace.coordPullback_comp (analytificationMap.{u} ψ)
      (analytificationInclHom.{u} g') i).symm ?_
    exact coordPullback_analytificationMap_comp.{u} ψ i

/-- The tuple transported along a composite is the tuple transported along the second map, pulled
back along the morphism induced by the first. This is
`ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal` at one element, and it is what
makes functoriality an application of `ComplexAnalytic.hom_ext_analytification`. -/
theorem transported_comp (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g'')
    (i : ULift.{u} (Fin n'')) :
    transported.{u} (ψ.comp χ) i =
      (LocallyRingedSpace.Γ.map (analytificationMap.{u} ψ).toLRSHom.op).hom
        (transported.{u} χ i) :=
  (RingHom.congr_fun (Γ_map_analytificationMap_comp_quotientToGlobal.{u} ψ)
    (χ.toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g'') (MvPolynomial.X i)))).symm

/-- **The identity `ℂ`-algebra map induces the identity morphism.** -/
@[simp]
theorem analytificationMap_id :
    analytificationMap.{u} (PresHom.id.{u} g) = 𝟙 (AnalyticSpace.analytification.{u} g) :=
  hom_ext_analytification.{u} g _ _ fun i ↦
    (coordPullback_analytificationMap_comp.{u} (PresHom.id.{u} g) i).trans
      ((quotientToGlobal_mk_X.{u} g i).trans
        (congrArg (fun m ↦ AnalyticSpace.coordPullback m i)
          (Category.id_comp (analytificationInclHom.{u} g)).symm))

/-- **The induced morphism of a composite is the composite of the induced morphisms**, in the
opposite order — the assignment is contravariant. -/
@[simp]
theorem analytificationMap_comp (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g'') :
    analytificationMap.{u} (ψ.comp χ) =
      analytificationMap.{u} ψ ≫ analytificationMap.{u} χ :=
  hom_ext_analytification.{u} g'' _ _ fun i ↦
    (coordPullback_analytificationMap_comp.{u} (ψ.comp χ) i).trans
      ((transported_comp.{u} ψ χ i).trans
        (((congrArg (LocallyRingedSpace.Γ.map (analytificationMap.{u} ψ).toLRSHom.op).hom
            (coordPullback_analytificationMap_comp.{u} χ i)).symm.trans
          (AnalyticSpace.coordPullback_comp (analytificationMap.{u} ψ)
            (analytificationMap.{u} χ ≫ analytificationInclHom.{u} g'') i).symm).trans
          (congrArg (fun m ↦ AnalyticSpace.coordPullback m i)
            (Category.assoc _ _ _).symm)))

/-- **Two presentations of the same `ℂ`-algebra have isomorphic analytifications**, with no
relation assumed between their numbers of variables or their numbers of equations.

This is presentation-independence: `ComplexAnalytic.analytificationIsoOfPresentationIdealEq`
covers a change of *generators* inside one polynomial ring, and this covers a change of
*variables* as well. -/
def analytificationIsoOfPresHom (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g)
    (h₁ : ψ.toRingHom.comp χ.toRingHom = RingHom.id (PresentedAlgebra.{u} n k g))
    (h₂ : χ.toRingHom.comp ψ.toRingHom = RingHom.id (PresentedAlgebra.{u} n' k' g')) :
    AnalyticSpace.analytification.{u} g ≅ AnalyticSpace.analytification.{u} g' where
  hom := analytificationMap.{u} ψ
  inv := analytificationMap.{u} χ
  hom_inv_id :=
    (analytificationMap_comp.{u} ψ χ).symm.trans
      ((congrArg analytificationMap.{u} (PresHom.ext.{u} (g := g) (g' := g) h₁)).trans
        analytificationMap_id.{u})
  inv_hom_id :=
    (analytificationMap_comp.{u} χ ψ).symm.trans
      ((congrArg analytificationMap.{u} (PresHom.ext.{u} (g := g') (g' := g') h₂)).trans
        analytificationMap_id.{u})

end

end ComplexAnalytic

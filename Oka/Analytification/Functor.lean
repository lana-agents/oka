/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Oka.Analytification.ChangeOfVariables

/-!
# The analytification as a functor

`Oka/Analytification/ChangeOfVariables.lean` proves that a `ℂ`-algebra map between two presented
algebras induces a morphism of analytifications, that identities go to identities and composites
to composites. That is the *data* of a functor. This file bundles it as one, and then removes the
presentation from the source.

The two steps are different in kind. Bundling is bookkeeping: a `Category` instance on
presentations whose three laws are `ComplexAnalytic.PresHom.ext` applied to the corresponding
`RingHom` laws. Removing the presentation is the step every previous account of this development
described as *"choosing a presentation for each algebra, which is a construction this file does
not perform"* — and the point of this file is that **it is not a construction and should not be
one.**

## Do not choose a presentation

`ComplexAnalytic.toFGAlg`, sending a presentation to the algebra it presents, is **fully
faithful** — a `ComplexAnalytic.PresHom` *is* a `ℂ`-algebra map of the presented algebras, with
both round trips `rfl` — and **essentially surjective** onto the finitely generated `ℂ`-algebras,
which is `ComplexAnalytic.exists_presentation`. So it is an equivalence, and
`CategoryTheory.Functor.asEquivalence` supplies the inverse. The presentation attached to an
algebra is then whatever `Classical.choice` picks out of essential surjectivity, and nothing
depends on which one it is, because any two are related by the equivalence.

The only mathematical content in essential surjectivity is **Hilbert's basis theorem**: a
finitely *generated* `ℂ`-algebra is a quotient of a polynomial ring in finitely many variables,
and the kernel is finitely generated because that polynomial ring is Noetherian. That is why
"finitely generated" and "finitely presented" are the same condition here, and it is the whole
reason a presentation exists to be chosen.

## The price of the choice, and why the comparison isomorphism is not optional

`analytificationFGAlg.obj (op A)` is **not** definitionally `AnalyticSpace.analytification g` for
a presentation `g` of `A`; it is the analytification of whichever presentation choice produced.
`ComplexAnalytic.analytificationFGAlgCompIso` is what connects the two, and without it the
functor would be a definition nothing can be computed from.

## Main definitions

- `ComplexAnalytic.Presentation`: a finite presentation `(n, k, g)`, bundled so that it can be the
  object of a category. Morphisms are `ComplexAnalytic.PresHom`, which run in the direction of the
  induced morphisms of spaces, so this category is the *opposite* of the category of presented
  algebras.
- `ComplexAnalytic.analytificationFunctor : Presentation ⥤ AnalyticSpace`: **the analytification,
  as a functor on presentations.**
- `ComplexAnalytic.isFiniteType`: finite type, as a property of an object of `CommAlgCat ℂ`.
- `ComplexAnalytic.toFGAlg : Presentation ⥤ (isFiniteType.FullSubcategory)ᵒᵖ`: a presentation,
  read as the finitely generated `ℂ`-algebra it presents.
- `ComplexAnalytic.analytificationFGAlg`: **the analytification of a finitely generated
  `ℂ`-algebra, as a functor**, with no presentation in its statement.
- `ComplexAnalytic.analytificationFGAlgCompIso`, `ComplexAnalytic.analytificationFGAlgObjIso`: the
  comparison with the presentation-level construction.

## Main results

- `ComplexAnalytic.toFGAlgFullyFaithful`: a `ℂ`-algebra map of presented algebras is the same
  thing as a morphism of presentations.
- `ComplexAnalytic.exists_presentation`: **every finitely generated `ℂ`-algebra is a presented
  algebra.**
- `ComplexAnalytic.instIsEquivalenceToFGAlg`: presentations *are* finitely generated
  `ℂ`-algebras.
- `ComplexAnalytic.analytificationFGAlgObjIso_hom`: the comparison isomorphism is the functor
  applied to the inverse of the unit — the only content in it, and what lets a consumer compose
  with it.

## What is not here

* **Naturality of the comparison with `Spec`** is not here, and is no longer missing: it is
  `Oka/Analytification/Comparison.lean`, which makes `ComplexAnalytic.analytificationToSpec` a
  natural transformation on presentations and then, along the equivalence below, one on the
  finitely generated `ℂ`-algebras themselves. That is what makes `X^an ⟶ X` part of the
  structure rather than a separate construction per presentation. It stays in a separate file
  because this one is about the *source* category and that one is about the target.
* **Anything non-affine.** A functor on schemes locally of finite type would be built from this
  one by gluing, and nothing here glues.
* **Anything analytic.** Every proof in this file is category-theoretic bookkeeping or
  commutative algebra; the analytic content is upstream, in the universal property.

## Design notes

**Why the full subcategory of `CommAlgCat ℂ` and not `AlgCat ℂ`, `Under (CommRingCat.of ℂ)` or
`Scheme`.** The analytification is defined only for commutative algebras, so `CommAlgCat` rather
than `AlgCat`; and `Algebra.FiniteType` is *exactly* the essential image of `Presentation` by
`ComplexAnalytic.exists_presentation`, so cutting the category down to it is not an arbitrary
restriction but the precise statement of what the construction covers. Affine schemes are one
`Spec` away and are a separate step, not a different foundation.

**Why a bespoke `Presentation` rather than a general presentation type.** `ComplexAnalytic.PresHom`
and `ComplexAnalytic.analytificationMap` are stated for a tuple
`g : Fin k → MvPolynomial (ULift (Fin n)) ℂ`; this structure is that tuple with its two indices,
and nothing more. It exists so that `PresHom` has a category to live in.

**And it is not the subject of `Oka/Analytification/Presentation.lean`.**
`ComplexAnalytic.Presentation` here is the bundled triple `(n, k, g)` that gives
`ComplexAnalytic.PresHom` a category to live in; `Oka/Analytification/Presentation.lean` is a
different thing — the construction of `X^an` from one such tuple, which this file's objects
index.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### Presentations as a category -/

/-- A finite presentation of a `ℂ`-algebra: `n` variables, `k` relations, and the relations. -/
structure Presentation where
  /-- The number of variables. -/
  n : ℕ
  /-- The number of relations. -/
  k : ℕ
  /-- The relations. -/
  g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ

/-- The `ℂ`-algebra a presentation presents. -/
abbrev Presentation.alg (P : Presentation.{u}) : Type u :=
  PresentedAlgebra.{u} P.n P.k P.g

/-- **Presentations form a category**, with `ComplexAnalytic.PresHom` as its morphisms.

Those run in the direction of the induced morphisms of analytic spaces rather than of the
underlying `ℂ`-algebra maps, so this is the *opposite* of the category of presented algebras —
which is why `ComplexAnalytic.analytificationFunctor` below is covariant and
`ComplexAnalytic.toFGAlg` lands in an opposite category.

All three laws are `ComplexAnalytic.PresHom.ext` applied to the corresponding `RingHom` law: the
commutation with the structure map is a proposition, so a morphism is its ring map. -/
instance : Category Presentation.{u} where
  Hom P Q := PresHom.{u} P.g Q.g
  id P := PresHom.id.{u} P.g
  comp ψ χ := PresHom.comp.{u} ψ χ
  id_comp _ := PresHom.ext (RingHom.comp_id _)
  comp_id _ := PresHom.ext (RingHom.id_comp _)
  assoc _ _ _ := PresHom.ext (RingHom.comp_assoc _ _ _).symm

/-- **The analytification, as a functor on presentations.**

Nothing is proved here: `ComplexAnalytic.analytificationMap_id` and
`ComplexAnalytic.analytificationMap_comp` are the two functor laws on the nose. -/
def analytificationFunctor : Presentation.{u} ⥤ AnalyticSpace.{u} where
  obj P := AnalyticSpace.analytification.{u} P.g
  map ψ := analytificationMap.{u} ψ
  map_id _ := analytificationMap_id.{u}
  map_comp ψ χ := analytificationMap_comp.{u} ψ χ

/-! ### Presentations are the finitely generated `ℂ`-algebras -/

/-- A `ComplexAnalytic.PresHom`, as a `ℂ`-algebra map. The commutation it carries *is* the
`AlgHom` field `commutes'`, so this is a repackaging and not a construction. -/
def PresHom.toAlgHom {n k n' k' : ℕ} {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
    {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ} (ψ : PresHom.{u} g g') :
    PresentedAlgebra.{u} n' k' g' →ₐ[ℂ] PresentedAlgebra.{u} n k g :=
  { ψ.toRingHom with commutes' := fun c ↦ RingHom.congr_fun ψ.commutes c }

/-- Being of finite type, as a property of an object of `CommAlgCat ℂ`. By
`ComplexAnalytic.exists_presentation` this is exactly the essential image of
`ComplexAnalytic.toFGAlg`. -/
abbrev isFiniteType : ObjectProperty (CommAlgCat.{u} ℂ) := fun A ↦ Algebra.FiniteType ℂ A

instance (P : Presentation.{u}) : Algebra.FiniteType ℂ P.alg :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ (presentationIdeal.{u} P.g))
    Ideal.Quotient.mk_surjective

/-- **A presentation, read as the finitely generated `ℂ`-algebra it presents.**

The target is an opposite category because `ComplexAnalytic.PresHom` already runs in the
direction of spaces; see the `Category` instance above. -/
def toFGAlg : Presentation.{u} ⥤ (isFiniteType.{u}.FullSubcategory)ᵒᵖ where
  obj P := .op ⟨CommAlgCat.of ℂ P.alg, inferInstance⟩
  map ψ := (ObjectProperty.homMk (P := isFiniteType.{u})
    (CommAlgCat.ofHom (PresHom.toAlgHom ψ))).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **A `ℂ`-algebra map of presented algebras is the same thing as a morphism of presentations.**

Both round trips are `rfl`: a `ComplexAnalytic.PresHom` is a ring map plus a commutation, an
`AlgHom` is a ring map plus a commutation, and they are the same commutation. -/
def toFGAlgFullyFaithful : toFGAlg.{u}.FullyFaithful where
  preimage {P Q} f := ⟨(f.unop.hom.hom : Q.alg →ₐ[ℂ] P.alg).toRingHom,
    RingHom.ext fun c ↦ (f.unop.hom.hom).commutes c⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : toFGAlg.{u}.Full := toFGAlgFullyFaithful.{u}.full

instance : toFGAlg.{u}.Faithful := toFGAlgFullyFaithful.{u}.faithful

open MvPolynomial in
/-- **Every finitely generated `ℂ`-algebra is a presented algebra.**

This is the essential surjectivity that lets a presentation be *chosen* rather than constructed,
and the only content in it is **Hilbert's basis theorem**: finite type gives a surjection from a
polynomial ring in finitely many variables, and its kernel is finitely generated because that
polynomial ring is Noetherian. Everything else is reindexing — `MvPolynomial.renameEquiv` to move
from `Fin n` to `ULift (Fin n)` variables, and `Finset.equivFin` to index the relations by
`Fin k`. -/
theorem exists_presentation (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] :
    ∃ P : Presentation.{u}, Nonempty (P.alg ≃ₐ[ℂ] A) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let e : MvPolynomial (ULift.{u} (Fin n)) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
    renameEquiv ℂ Equiv.ulift
  set F : MvPolynomial (ULift.{u} (Fin n)) ℂ →ₐ[ℂ] A := f.comp e.toAlgHom with hF
  have hFs : Function.Surjective F := hf.comp e.surjective
  obtain ⟨s, hs⟩ : (RingHom.ker F.toRingHom).FG := IsNoetherian.noetherian _
  refine ⟨⟨n, s.card, fun i ↦ s.equivFin.symm i⟩, ⟨?_⟩⟩
  have hrange : Set.range (fun i : Fin s.card ↦ ((s.equivFin.symm i : s) :
      MvPolynomial (ULift.{u} (Fin n)) ℂ)) = (s : Set (MvPolynomial (ULift.{u} (Fin n)) ℂ)) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ (s.equivFin.symm i).2,
      fun hx ↦ ⟨s.equivFin ⟨x, hx⟩, congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨x, hx⟩)⟩⟩
  have h : presentationIdeal.{u} (fun i : Fin s.card ↦ (s.equivFin.symm i : _)) =
      RingHom.ker F.toRingHom :=
    (congrArg Ideal.span hrange).trans hs
  exact (Ideal.quotientEquivAlgOfEq ℂ h).trans (Ideal.quotientKerAlgEquivOfSurjective hFs)

instance : toFGAlg.{u}.EssSurj where
  mem_essImage X := by
    obtain ⟨⟨A, hA⟩⟩ := X
    obtain ⟨P, ⟨e⟩⟩ := exists_presentation.{u} A
    exact ⟨P, ⟨(ObjectProperty.isoMk (P := isFiniteType.{u}) (CommAlgCat.isoMk e.symm)).op⟩⟩

/-- **Presentations *are* the finitely generated `ℂ`-algebras.** Fully faithful and essentially
surjective, so an equivalence; this is what makes the analytification a functor of the algebra
alone. -/
instance instIsEquivalenceToFGAlg : toFGAlg.{u}.IsEquivalence where

/-! ### The analytification of a finitely generated `ℂ`-algebra -/

/-- **The analytification of a finitely generated `ℂ`-algebra, as a functor.**

The presentation is gone from the statement. It is still there in the proof — the inverse of an
equivalence is built from essential surjectivity and so from `Classical.choice` — but nothing
depends on which presentation is chosen, because any two are related by the equivalence. That is
the whole content of presentation-independence, and it was proved on objects in
`Oka/Analytification/ChangeOfVariables.lean`. -/
def analytificationFGAlg : (isFiniteType.{u}.FullSubcategory)ᵒᵖ ⥤ AnalyticSpace.{u} :=
  toFGAlg.{u}.asEquivalence.inverse ⋙ analytificationFunctor.{u}

/-- **On a presentation, the functor of algebras agrees with the presentation-level
construction**, naturally.

This is not decoration. `ComplexAnalytic.analytificationFGAlg` is defined through the inverse of
an equivalence, so its value on an algebra is the analytification of *some* presentation and not
of the one in hand; this isomorphism is the only way back to the concrete construction, and
without it the functor would be a definition nothing can be computed from. -/
def analytificationFGAlgCompIso :
    toFGAlg.{u} ⋙ analytificationFGAlg.{u} ≅ analytificationFunctor.{u} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight toFGAlg.{u}.asEquivalence.unitIso.symm analytificationFunctor.{u} ≪≫
      analytificationFunctor.{u}.leftUnitor

/-- `ComplexAnalytic.analytificationFGAlgCompIso` at one presentation: the analytification of the
algebra a presentation presents is the analytification of that presentation. -/
def analytificationFGAlgObjIso (P : Presentation.{u}) :
    analytificationFGAlg.{u}.obj (toFGAlg.{u}.obj P) ≅ AnalyticSpace.analytification.{u} P.g :=
  analytificationFGAlgCompIso.{u}.app P

/-- **The comparison isomorphism is the functor applied to the inverse of the unit.**

Everything in `ComplexAnalytic.analytificationFGAlgCompIso` except this is associators and
unitors, so this is the only content in it, and it is what a consumer needs in order to compose
with it. The two identities are dropped by hand because the two spellings of the objects are
definitionally but not syntactically equal and `Category.id_comp` has to be told which category
it is in. -/
theorem analytificationFGAlgObjIso_hom (P : Presentation.{u}) :
    (analytificationFGAlgObjIso.{u} P).hom =
      analytificationFunctor.{u}.map (toFGAlg.{u}.asEquivalence.unitIso.inv.app P) := by
  simp only [analytificationFGAlgObjIso, analytificationFGAlgCompIso, NatIso.trans_app,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.id_obj,
    Functor.leftUnitor_hom_app]
  refine (Category.id_comp (obj := AnalyticSpace.{u}) _).trans
    (Category.comp_id (obj := AnalyticSpace.{u}) _)

end

end ComplexAnalytic

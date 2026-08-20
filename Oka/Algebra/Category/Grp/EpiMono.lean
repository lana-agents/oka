/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.MorphismProperty.Concrete

/-!
# Morphisms of abelian groups factor functorially as a surjection followed by an injection

`CategoryTheory.ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization` is the hypothesis
under which a morphism of sheaves valued in a concrete category factors as a locally surjective
morphism followed by a locally injective one, and hence — the reason one wants it — under which
**an epimorphism of sheaves is locally surjective**
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`, and for sheaves on a topological space
`TopCat.Sheaf.isLocallySurjective_iff_epi`).

Mathlib provides that instance only for `Type u`
(`Mathlib/CategoryTheory/MorphismProperty/Concrete.lean`), which is what makes those two
equivalences unavailable for sheaves of abelian groups, and therefore for sheaves of modules.
This file supplies it for `AddCommGrpCat`, by the evident factorization through the range.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib; it
lives in the `Oka/`-mirror of the Mathlib directory tree for that reason, next to
`Mathlib/Algebra/Category/Grp/EpiMono.lean`.

## Main definitions

- `AddCommGrpCat.arrowRangeFunctor`: the range of a morphism, as a functor on the arrow category.
- `AddCommGrpCat.functorialSurjectiveInjectiveFactorizationData`: the factorization of a morphism
  as the corestriction to its range followed by the inclusion of that range, functorially in the
  morphism; and the resulting instance.
-/

open CategoryTheory

universe u

namespace AddCommGrpCat

/-- The commutative square of an arrow morphism, applied to an element. -/
lemma arrow_w_apply {f g : Arrow AddCommGrpCat.{u}} (φ : f ⟶ g) (x : f.left) :
    (Hom.hom φ.right) ((Hom.hom f.hom) x) = (Hom.hom g.hom) ((Hom.hom φ.left) x) := by
  have h := congrArg (fun (u : f.left ⟶ g.right) => (Hom.hom u) x) φ.w
  simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] using h.symm

/-- The range of a morphism of abelian groups, as a functor on the arrow category. A morphism of
arrows maps ranges to ranges precisely because its square commutes. -/
noncomputable def arrowRangeFunctor : Arrow AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} where
  obj f := AddCommGrpCat.of (AddMonoidHom.range (Hom.hom f.hom))
  map {f g} φ := AddCommGrpCat.ofHom
    (AddMonoidHom.codRestrict ((Hom.hom φ.right).comp (AddMonoidHom.range (Hom.hom f.hom)).subtype)
      _ (by
        rintro ⟨_, x, rfl⟩
        exact ⟨(Hom.hom φ.left) x, (arrow_w_apply φ x).symm⟩))
  map_id f := by ext ⟨y, hy⟩; rfl
  map_comp φ ψ := by ext ⟨y, hy⟩; rfl

/-- Any morphism of abelian groups factors functorially as the corestriction to its range,
which is surjective, followed by the inclusion of that range, which is injective. -/
noncomputable def functorialSurjectiveInjectiveFactorizationData :
    ConcreteCategory.FunctorialSurjectiveInjectiveFactorizationData AddCommGrpCat.{u} where
  Z := arrowRangeFunctor
  i := { app := fun f => AddCommGrpCat.ofHom (AddMonoidHom.rangeRestrict (Hom.hom f.hom))
         naturality := by
           intro f g φ
           ext x
           exact Subtype.ext (arrow_w_apply φ x).symm }
  p := { app := fun f => AddCommGrpCat.ofHom (AddMonoidHom.range (Hom.hom f.hom)).subtype
         naturality := by intro f g φ; ext ⟨y, hy⟩; rfl }
  fac := by ext f x; rfl
  hi f := (Hom.hom f.hom).rangeRestrict_surjective
  hp f := Subtype.val_injective

instance : ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization AddCommGrpCat.{u} where
  nonempty_functorialFactorizationData := ⟨functorialSurjectiveInjectiveFactorizationData⟩

end AddCommGrpCat

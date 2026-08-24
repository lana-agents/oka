/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# The forgetful functor on abelian groups preserves epimorphisms

`CategoryTheory.ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization` is the hypothesis
under which a morphism of sheaves valued in a concrete category factors as a locally surjective
morphism followed by a locally injective one, and hence — the reason one wants it — under which
**an epimorphism of sheaves is locally surjective**
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`, and for sheaves on a topological space
`TopCat.Sheaf.isLocallySurjective_iff_epi`).

Mathlib derives that class for any concrete category with strong epi–mono factorisations whose
forgetful functor preserves monomorphisms and epimorphisms
(`Mathlib/CategoryTheory/ConcreteCategory/EpiMono.lean:148`). For `AddCommGrpCat` all of those
hold, but `(forget AddCommGrpCat).PreservesEpimorphisms` is not registered; an epimorphism of
abelian groups is surjective, which is `AddCommGrpCat.epi_iff_surjective`, and that is all the
instance below needs. With it, the factorization class is `inferInstance`.

`Mathlib.Algebra.Category.Grp.Abelian` is imported for `HasStrongEpiMonoFactorisations`, which
comes from `AddCommGrpCat` being abelian and is otherwise not in scope — the same trap as
`Balanced (Sheaf J AddCommGrpCat)`, where the missing piece was also `Abelian AddCommGrpCat` and
the error message named the construction rather than the category.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib; it
lives in the `Oka/`-mirror of the Mathlib directory tree for that reason, next to
`Mathlib/Algebra/Category/Grp/EpiMono.lean`.

**That mirror path costs 544 modules, which is the largest price in this tree**, and the figure
was unstated here until taxis #935. `Mathlib/Algebra/Category/Grp/EpiMono.lean`'s transitive
closure is **637** Mathlib modules and `Mathlib.Algebra.Category.Grp.Abelian` is not in it;
adding it costs **544**, against the **96** `README.md` records as the figure that once made an
upstreaming judged too expensive. Measured with `scripts/import_cost.py`, not estimated.

**A cheaper destination exists and this file does not choose it.** The same instance priced into
`Mathlib/Algebra/Category/Grp/Abelian.lean` — which has the strong epi–mono factorisations
already — costs **2**. Whether a Mathlib reviewer would want an `AddCommGrpCat` epimorphism
instance in the abelian-structure file is a question about the declaration rather than about the
price, and it is taxis #935's to answer.

## Main results

- the forgetful functor `AddCommGrpCat ⥤ Type` preserves epimorphisms. The instance below is
  anonymous, so the name Lean generates for it is not one to cite; it is the
  `CategoryTheory.Functor.PreservesEpimorphisms` instance for `forget AddCommGrpCat`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AddCommGrpCat

/-- The forgetful functor from abelian groups to types preserves epimorphisms, because an
epimorphism of abelian groups is surjective. -/
instance : (forget AddCommGrpCat.{u}).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    rw [AddCommGrpCat.epi_iff_surjective] at hf
    exact (CategoryTheory.epi_iff_surjective _).2 hf

end AddCommGrpCat

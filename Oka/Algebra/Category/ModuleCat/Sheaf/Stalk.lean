/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Topology.Sheaves.Abelian

/-!
# Stalks of sheaves of modules on a topological space, and exactness

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/Stalk.lean`; see `README.md` on the
mirror tree. Mathlib's `Mathlib/Algebra/Category/ModuleCat/Stalk.lean` puts a
`Module (R.stalk x)` structure on the stalk of a presheaf of modules; this file is the other
half, the *functor* and what it detects.

**The mathematics here is Mathlib's.** `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` already
says that a short complex of sheaves of abelian groups on a space is exact exactly when it is
exact on every stalk. What this file adds is the transfer of that to sheaves of *modules*,
which is one step — `SheafOfModules.toSheaf` is faithful, and
`CategoryTheory.Functor.reflects_exact_of_faithful` needs nothing more than that.

## The seam this file exists to cross, and it costs one instance

`TopCat.Sheaf C X` is a `def` for `CategoryTheory.Sheaf (Opens.grothendieckTopology X) C`, and
`SheafOfModules.toSheaf` lands in the second spelling while every stalk lemma is stated in the
first. **The two `Category` instances are equal by `rfl`** — checked — but instance search does
not cross them, so `Abelian (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)`
is not found even though `Abelian (TopCat.Sheaf AddCommGrpCat X)` is, and without it
`SheafOfModules.toSheaf` has no `PreservesZeroMorphisms` and `ShortComplex.map` cannot be
applied to it.

`abelianSheafOpensGrothendieckTopology` below is that transport, by `inferInstanceAs`, and it
is the whole cost. This is the same shape as the site spelling recorded in
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf`'s docstring: **a definitional equality that
`rfl` sees and the discrimination tree does not.**

Two consequences worth knowing before using this file:

* the same transport is needed for `CategoryTheory.Functor.Additive` and for
  `CategoryTheory.Limits.PreservesFiniteLimits` of `TopCat.Sheaf.stalkFunctor`, and both are
  supplied here;
* at the point of use the site has to be spelled so that it matches. For an
  `AlgebraicGeometry.LocallyRingedSpace` `Y`, whose `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`
  lives over `Opens.grothendieckTopology ↑Y.toPresheafedSpace`, the space to pass is
  `TopCat.of ↑Y.toPresheafedSpace` and **not** `Y.toTopCat`; with `Y.toTopCat` the statement
  elaborates and then fails to find `PreservesZeroMorphisms`.
  `OkaTest/SheafOfModulesStalk.lean` records both.

## Main definitions

- `TopCat.Sheaf.stalkFunctor`: the stalk at `x` of a sheaf of abelian groups on `X`, as a
  functor, at the `CategoryTheory.Sheaf` spelling of the site.
- `SheafOfModules.stalkFunctor`: the stalk at `x` of a sheaf of modules on `X`, as a functor to
  `AddCommGrpCat`.

## Main results

- `TopCat.Sheaf.exact_iff_stalk_exact`: Mathlib's criterion at the other spelling of the site.
- `SheafOfModules.exact_of_stalk_exact`: **a short complex of sheaves of modules is exact if it
  is exact on every stalk.**

## What is not here

* **The converse of `SheafOfModules.exact_of_stalk_exact`.** It is true, and it needs
  `SheafOfModules.toSheaf` to be *right* exact as well as left exact. Mathlib has
  `PreservesFiniteLimits (SheafOfModules.toSheaf R)`
  (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean`) and **not**
  `CategoryTheory.Limits.PreservesFiniteColimits` — measured, `inferInstance` fails on both that
  and `CategoryTheory.Functor.PreservesHomology`. So the converse is a theorem someone has to
  prove and not a transfer. It is not needed by the intended consumer: an argument that a functor
  preserves kernels compares the canonical map with the kernel and checks it is an isomorphism,
  which needs the direction proved here plus `PreservesFiniteLimits`, both of which are present.
* **Isomorphism detected on stalks for sheaves of modules.**
  `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` plus `SheafOfModules.toSheaf` reflecting
  isomorphisms gives it, and the only obstacle met was naming the underlying presheaf morphism
  of a morphism of sheaves across the `TopCat.Sheaf` `def`: the `deriving Category` on that `def`
  makes it an `CategoryTheory.InducedCategory.Hom`, on which the `val` projection is not a
  field. It is left to whoever needs it, with that warning.
* **Anything analytic.** This file is general theory and imports nothing from this development.
-/

open CategoryTheory Limits TopologicalSpace TopCat

universe u

variable {X : TopCat.{u}} {R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- Sheaves of abelian groups on a space form an abelian category, at the
`CategoryTheory.Sheaf` spelling of the site.

Mathlib has this for `TopCat.Sheaf AddCommGrpCat X`, which is the same type by a `def`; instance
search does not cross the two, and this transport is what lets `SheafOfModules.toSheaf` — whose
codomain is spelled the other way — be used with `CategoryTheory.ShortComplex.map`. See the
module docstring. -/
noncomputable instance abelianSheafOpensGrothendieckTopology (X : TopCat.{u}) :
    Abelian (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  inferInstanceAs (Abelian (TopCat.Sheaf AddCommGrpCat.{u} X))

/-- **The stalk at `x`, as a functor on sheaves of abelian groups on `X`**, at the
`CategoryTheory.Sheaf` spelling of the site.

This is `TopCat.Sheaf.forget` followed by `TopCat.Presheaf.stalkFunctor`; it is an `abbrev` so
that the instances Mathlib proves about that composite remain visible. -/
noncomputable abbrev TopCat.Sheaf.stalkFunctor (X : TopCat.{u}) (x : X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

noncomputable instance (x : X) : (TopCat.Sheaf.stalkFunctor X x).Additive :=
  inferInstanceAs ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive)

noncomputable instance (x : X) : PreservesFiniteLimits (TopCat.Sheaf.stalkFunctor X x) :=
  inferInstanceAs (PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))

/-- **A short complex of sheaves of abelian groups on a space is exact exactly when it is exact
on every stalk.**

This is `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` with the site spelled
`CategoryTheory.Sheaf (Opens.grothendieckTopology X)` rather than `TopCat.Sheaf`. The proof is
the Mathlib lemma applied — the two statements are definitionally equal — but the restatement is
not decoration: a `rw` with the Mathlib lemma fails on a goal in this spelling, with
`did not find an occurrence of the pattern`. -/
theorem TopCat.Sheaf.exact_iff_stalk_exact
    (S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) :
    S.Exact ↔ ∀ x : X, (S.map (TopCat.Sheaf.stalkFunctor X x)).Exact :=
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S

/-- **The stalk at `x`, as a functor on sheaves of modules on `X`.**

Valued in `AddCommGrpCat` rather than in modules over the stalk of the sheaf of rings: the
module structure is `Mathlib/Algebra/Category/ModuleCat/Stalk.lean`'s and is available on the
object, but the functor to abelian groups is what detects exactness and is what this file is
for. -/
noncomputable abbrev SheafOfModules.stalkFunctor (x : X) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf R ⋙ TopCat.Sheaf.stalkFunctor X x

noncomputable instance (x : X) : PreservesFiniteLimits (SheafOfModules.stalkFunctor (R := R) x) :=
  comp_preservesFiniteLimits _ _

/-- **A short complex of sheaves of modules on a space is exact if it is exact on every stalk.**

The forgetful functor to sheaves of abelian groups is faithful, and a faithful functor between
abelian categories that preserves zero morphisms reflects exactness — that is
`CategoryTheory.Functor.reflects_exact_of_faithful`, and it is the whole proof once the site
spellings agree. **The converse is true and is not here**; see the module docstring for what it
needs and why the intended consumer does not. -/
theorem SheafOfModules.exact_of_stalk_exact (S : ShortComplex (SheafOfModules.{u} R))
    (h : ∀ x : X, (S.map (SheafOfModules.stalkFunctor x)).Exact) : S.Exact :=
  Functor.reflects_exact_of_faithful (SheafOfModules.toSheaf R) S
    ((TopCat.Sheaf.exact_iff_stalk_exact (S.map (SheafOfModules.toSheaf R))).mpr h)

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Oka.Algebra.Category.Grp.EpiMono

/-!
# An epimorphism of sheaves of abelian groups is locally surjective

`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'` says that a morphism of sheaves valued in a
concrete category is locally surjective exactly when it is an epimorphism, given three
hypotheses. For `AddCommGrpCat` two of them — `HasSheafCompose` and, via
`CategoryTheory.sheafIsAbelian`, `Balanced` — are already available, and the third,
`HasFunctorialSurjectiveInjectiveFactorization`, follows from Mathlib's generic instance for
concrete categories once `(forget AddCommGrpCat).PreservesEpimorphisms` is supplied, which
is what `Oka/Algebra/Category/Grp/EpiMono.lean` does. This file records the resulting
statement, which is
what one actually reaches for: **a section of the target of an epimorphism of sheaves of abelian
groups lifts on a covering sieve.**

The direction that is not formal is `epi → locally surjective`; the converse is Mathlib's
`CategoryTheory.Sheaf.epi_of_isLocallySurjective`.

The universe of `AddCommGrpCat` is kept independent of the universes of the site, as it is in
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`. Tying it to the morphism universe of `C`
would be enough for sheaves on a topological space but not for
`Oka/Algebra/Category/ModuleCat/Sheaf/LocallySurjective.lean`, where the universe of the
modules is a parameter of its own.

**Upstreaming it costs its target 57 modules**, and the figure was unstated here until taxis
#935: `Mathlib/CategoryTheory/Sites/LocallySurjective.lean`'s closure is **922** Mathlib modules,
`Mathlib.CategoryTheory.Sites.Abelian` adds **55** of them and
`Mathlib.CategoryTheory.Sites.EpiMono` the other **2**. Measured with `scripts/import_cost.py`.
**A cheaper destination exists and this file does not choose it**: priced into
`Mathlib/CategoryTheory/Sites/Abelian.lean` the same declarations cost **2**. That is taxis
#935's question. The `Oka` import below is priced by its own file's docstring, and that one is
the expensive half of this pair.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib; it
lives in the `Oka/`-mirror of the Mathlib directory tree for that reason, next to
`Mathlib/CategoryTheory/Sites/LocallySurjective.lean`.

## Main results

- `CategoryTheory.Sheaf.isLocallySurjective_iff_epi_addCommGrp`
- `CategoryTheory.Sheaf.isLocallySurjective_of_epi_addCommGrp`
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {F G : Sheaf J AddCommGrpCat.{w}}

/-- A morphism of sheaves of abelian groups is locally surjective exactly when it is an
epimorphism. -/
lemma isLocallySurjective_iff_epi_addCommGrp (f : F ⟶ G) :
    IsLocallySurjective f ↔ Epi f :=
  isLocallySurjective_iff_epi' (A := AddCommGrpCat.{w}) f

/-- An epimorphism of sheaves of abelian groups is locally surjective: every section of the
target is, on a covering sieve, in the image. -/
lemma isLocallySurjective_of_epi_addCommGrp (f : F ⟶ G) [Epi f] : IsLocallySurjective f :=
  (isLocallySurjective_iff_epi_addCommGrp f).2 ‹_›

end CategoryTheory.Sheaf

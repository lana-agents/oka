/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Oka.Algebra.Category.Grp.EpiMono

/-!
# An epimorphism of sheaves of abelian groups is locally surjective

`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'` says that a morphism of sheaves valued in a
concrete category is locally surjective exactly when it is an epimorphism, given three
hypotheses. For `AddCommGrpCat` two of them — `HasSheafCompose` and, via
`CategoryTheory.sheafIsAbelian`, `Balanced` — are already available, and the third,
`HasFunctorialSurjectiveInjectiveFactorization`, is supplied by
`Oka/Algebra/Category/Grp/EpiMono.lean`. This file records the resulting statement, which is
what one actually reaches for: **a section of the target of an epimorphism of sheaves of abelian
groups lifts on a covering sieve.**

The direction that is not formal is `epi → locally surjective`; the converse is Mathlib's
`CategoryTheory.Sheaf.epi_of_isLocallySurjective`.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib; it
lives in the `Oka/`-mirror of the Mathlib directory tree for that reason, next to
`Mathlib/CategoryTheory/Sites/LocallySurjective.lean`.

## Main results

- `CategoryTheory.Sheaf.isLocallySurjective_iff_epi_addCommGrp`
- `CategoryTheory.Sheaf.isLocallySurjective_of_epi_addCommGrp`
-/

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  {F G : Sheaf J AddCommGrpCat.{v}}

/-- A morphism of sheaves of abelian groups is locally surjective exactly when it is an
epimorphism. -/
lemma isLocallySurjective_iff_epi_addCommGrp (f : F ⟶ G) :
    IsLocallySurjective f ↔ Epi f :=
  isLocallySurjective_iff_epi' (A := AddCommGrpCat.{v}) f

/-- An epimorphism of sheaves of abelian groups is locally surjective: every section of the
target is, on a covering sieve, in the image. -/
lemma isLocallySurjective_of_epi_addCommGrp (f : F ⟶ G) [Epi f] : IsLocallySurjective f :=
  (isLocallySurjective_iff_epi_addCommGrp f).2 ‹_›

end CategoryTheory.Sheaf

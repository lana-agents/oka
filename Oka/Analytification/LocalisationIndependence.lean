/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.LocalisationFunctor
import Oka.RingTheory.Localization.Away.Basic

/-!
# The presentation of a distinguished open depends on the polynomial only up to a unique iso

`ComplexAnalytic.localisationPresentation g f` adjoins a variable and the equation `t·f - 1`, so
the polynomial `f` occurs in the *type* of everything built from it: two polynomials cutting out
the same distinguished open give two different objects of `ComplexAnalytic.Presentation` and two
different analytic spaces. This file says they are canonically the same one.

Two statements, and the second is the one with content:

* `ComplexAnalytic.localisationPresentationIsoOfDvdPow` — **the presentations of the localisation
  at `f` and at `f'` are isomorphic** whenever the images of `f` and `f'` in `A` each divide a
  power of the other, which is the algebraic form of *"`f` and `f'` cut out the same distinguished
  open"*.
* `ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` — **the identification
  with `Localization.Away` commutes with the structure map** `A ⟶ A_f`. This is what makes the
  first isomorphism canonical rather than merely available, and it is proved without an
  `Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance on the localised presented algebra:
  see *The shape this settles* below.

## Where this is needed

Taxis #996. `Mathlib/AlgebraicGeometry/Cover/Directed.lean`'s locally directed cover — the shape
a scheme actually supplies, and the one
`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean` instantiates for every scheme with no
hypotheses — indexes the members of a cover by a *category* and asks for a transition morphism per
**arrow**. An arrow of that index category is a proof of `∃ f, X.basicOpen f = U`, and it is
proof-irrelevant: the section `f` witnessing it is neither recoverable from it nor unique. On this
side the polynomial is in the type, so a transition built from a witness has to be shown
independent of the witness. That is the first statement above.

## The shape this settles, and it is a choice among two

Building the analytification of a locally directed cover can be done **choice-first** — pick a
presentation for each member and a witness for each arrow, then prove the functoriality laws up to
the coherence isomorphisms — or **choice-free**, building each member as a colimit over all its
presentations so that no choice is made and the laws hold on the nose.

**Choice-first, and the reason is stronger than "the choices are isomorphic".** The isomorphism
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow` is
`IsLocalization.algEquiv`, transported: it is not *an* isomorphism between the two localisations
but **the unique `A`-algebra map** between them, since both are localisations of `A` at the same
saturated submonoid. Uniqueness is what discharges a coherence law, and it is available here
because the second statement above puts the identification over `A` rather than only over `ℂ`. The
colimit construction would buy the same laws at the price of machinery this development has no
other use for.

## What is not here

**No transition morphism, and no locally directed cover.** Nothing below mentions
`AlgebraicGeometry.Scheme`, and the file adds no Mathlib import: `Cover/Directed.lean` is not
imported, so its declarations cannot even be named in a docstring here — which is why the two
Mathlib files above are cited by path.

**No composite of two localisations.** The second half of taxis #996 is that the witness of a
composite arrow is a third polynomial, and its algebra is `IsLocalization.Away.mul`, already in
Mathlib. What is missing is the transport of that statement to
`ComplexAnalytic.localisationPresentation`, and the obstruction is recorded in
`Oka/Analytification/DistinguishedOpen.lean`'s docstring for
`ComplexAnalytic.localisationPresentedAlgebraEquiv`: there is deliberately no
`Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance on the localised presented algebra,
so `IsLocalization.Away.mul` cannot be applied to it directly. The compatibility proved here is
what such a transport would be built from.
-/

open CategoryTheory MvPolynomial

namespace ComplexAnalytic

universe u

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f f' : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The identification is over `A`, not only over `ℂ` -/

/-- **The reindexing of the variables carries the structure map to `MvPolynomial.awayBaseHom`.**

Both sides send the class of `p` to the class of `MvPolynomial.rename some p`: on the left the
renaming is `ComplexAnalytic.localisationIncl` followed by
`ComplexAnalytic.localisationVarEquiv`, which is `some` by
`ComplexAnalytic.localisationVarEquiv_localisationIncl`. -/
theorem localisationRenameEquiv_localisationRingHom (x : PresentedAlgebra.{u} n k g) :
    localisationRenameEquiv.{u} g f (localisationRingHom.{u} g f x) =
      MvPolynomial.awayBaseHom (presentationIdeal.{u} g) f x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change localisationRenameEquiv.{u} g f
    ((PresHom.ofRename.{u} (localisationIncl.{u} n) _).toRingHom _) = _
  simp [localisationRenameEquiv, PresHom.ofRename, MvPolynomial.awayBaseHom,
    MvPolynomial.rename_rename, Function.comp_def]

/-- **`ComplexAnalytic.localisationPresentedAlgebraEquiv` commutes with the structure map**: the
identification of `ℂ[x, t] ⧸ (g, t·f - 1)` with `Localization.Away` is an isomorphism *over* `A`,
and not merely over `ℂ`.

This is the statement that lets a consumer use the universal property of the localisation on
anything built from `ComplexAnalytic.localisationRingHom` — for instance to see that two
descriptions of the same distinguished open agree over the member they sit in — without an
`Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance being introduced on the localised
presented algebra, which `Oka/Analytification/DistinguishedOpen.lean` deliberately avoids. -/
theorem localisationPresentedAlgebraEquiv_localisationRingHom (x : PresentedAlgebra.{u} n k g) :
    localisationPresentedAlgebraEquiv.{u} g f (localisationRingHom.{u} g f x) =
      algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f)) x := by
  change MvPolynomial.awayQuotientEquiv _ _ (localisationRenameEquiv.{u} g f _) = _
  rw [localisationRenameEquiv_localisationRingHom, MvPolynomial.awayQuotientEquiv_apply,
    MvPolynomial.awayLift_awayBaseHom]

/-! ### Two polynomials cutting out the same distinguished open -/

variable (h : ∃ N, Ideal.Quotient.mk (presentationIdeal.{u} g) f' ∣
    Ideal.Quotient.mk (presentationIdeal.{u} g) f ^ N)
  (h' : ∃ M, Ideal.Quotient.mk (presentationIdeal.{u} g) f ∣
    Ideal.Quotient.mk (presentationIdeal.{u} g) f' ^ M)

include h h' in
/-- **The two presented algebras are isomorphic**, when the images of `f` and `f'` in `A` each
divide a power of the other.

The middle step is `IsLocalization.Away.algEquivOfDvdPow`, which is an isomorphism over `A`; it is
restricted to `ℂ` only because `ComplexAnalytic.Presentation` is a category of `ℂ`-algebras. It is
the unique `A`-algebra map between the two localisations, so nothing about this isomorphism is
chosen. -/
noncomputable def localisationPresentedAlgebraEquivOfDvdPow :
    PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) ≃ₐ[ℂ]
      PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f') :=
  (localisationPresentedAlgebraEquiv.{u} g f).trans
    (((IsLocalization.Away.algEquivOfDvdPow _ _ h h').restrictScalars ℂ).trans
      (localisationPresentedAlgebraEquiv.{u} g f').symm)

include h h' in
/-- **The two presentations are isomorphic objects of `ComplexAnalytic.Presentation`**, hence have
isomorphic analytifications, by `ComplexAnalytic.analytificationFunctor`.

This is what says a transition morphism built from a *witness* that two members overlap in a
distinguished open does not depend on the witness. -/
noncomputable def localisationPresentationIsoOfDvdPow :
    (⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ : Presentation.{u}) ≅
      ⟨n + 1, k + 1, localisationPresentation.{u} g f'⟩ :=
  Presentation.isoOfAlgEquiv (localisationPresentedAlgebraEquivOfDvdPow.{u} g f f' h h').symm

end ComplexAnalytic

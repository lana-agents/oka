/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.StandardEtaleNotFinite

/-!
# The same morphism, restricted: finite étale over the punctured line

`OkaTest/StandardEtaleNotFinite.lean` proves that `ComplexAnalytic.condEtaleProj` — the
analytification of the square-root cover of the line, composed with the base's inclusion into
`ℂ¹` — is **not** finite, and so not finite étale. This file proves that the **same** morphism,
restricted over the complement of the origin, **is** finite étale.

`Oka/Analytification/StandardEtaleFiniteEtale.lean`'s `## What is not here` said this could not be
done:

> **Nothing about how large `V` is *here*.** … **It is not instantiated for *this* class**,
> because the second field needs a `StandardEtalePair` and **nothing exhibits the parabola as
> one**; so a reader should still not take the conclusion below as saying the morphism is finite
> étale over anything in particular.

**Something exhibits the parabola as one, and it did so two days before that bullet was
written.** It is `ComplexAnalytic.condPair` (`OkaTest/StandardEtaleCond.lean`), which is the
parabola of `Oka/Analytification/OpenBaseFiniteness.lean` at `n = 1` and `i = 0` written in the
other vocabulary. Nothing below is built; the file's whole content is that the two are the same
pair.

## The two vocabularies, and the one map between them

`ComplexAnalytic.hypersurfaceCommonZeroImage_parabola` is stated over
`MvPolynomial (ULift (Fin n)) ℂ` at `F = Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X i)` and
`G = Polynomial.X`; `ComplexAnalytic.condF` and `ComplexAnalytic.condG` are `X₁² - X₀` and `X₁`
in `MvPolynomial (ULift (Fin 2)) ℂ`. `ComplexAnalytic.lastVarPolyEquiv` is the map, and both
directions of it were already theorems:

* `ComplexAnalytic.lastVarPolyEquiv_symm_X` and `ComplexAnalytic.lastVarPolyEquiv_symm_C`
  (`Oka/Analytification/MonicHypersurface.lean`) take the polynomial form to the multivariate one,
  which is `ComplexAnalytic.lastVarPolyEquiv_symm_condPolyF` below;
* `ComplexAnalytic.condF_eq` and `ComplexAnalytic.condG_eq` (`OkaTest/StandardEtaleCond.lean`) run
  the **same** computation in the other direction, into the presented base, and are exactly the
  two lift hypotheses the theorem below consumes —
  `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl`
  (`Oka/Analytification/StandardEtaleFiniteEtale.lean`) — asks for.

**Nobody had read the two against each other**, which is the whole of why this was recorded as
absent. **The dates are worth stating because they are further apart than they look**:
`ComplexAnalytic.condPair` is `5ae9ed5` (2026-08-31 01:53Z), the parabola is `028808f`
(2026-09-02 01:44Z) and the theorem that consumes both is `868ed5f` (2026-09-02 00:30Z) — so the
pair predates the parabola by 1d 23h and the consuming theorem by 1d 22h, in a file that
theorem's own module cannot import.

## The placement is forced and not chosen

The statement reads `ComplexAnalytic.condPair` and `ComplexAnalytic.condEtaleProj`, both of which
are under `OkaTest/`. **No module under `Oka/` can hold this theorem**, because no module under
`Oka/` may import the test library. So there is no placement argument to have — unlike at
`Oka/Analytification/StandardEtaleFiniteEtale.lean`, which priced appending to
`Oka/Analytification/StandardEtaleFiniteness.lean` and declined it, and at
`Oka/Analytification/RefineDatumRange.lean`, which argues its own placement at length. Named
rather than counted.

## What the contrast is, and what it is not

`ComplexAnalytic.not_isFinite_condEtaleProj` and
`ComplexAnalytic.isFiniteEtale_restrictHom_condEtaleProj` are about one morphism and differ by the
restriction alone. That is the substance of the claim that the `V` hypothesis of
`Oka/Analytification/StandardEtaleFiniteness.lean`'s theorem is not decoration.

**Neither half is vacuous and the two witnesses are for different spaces**, which is the thing this
file got wrong first. `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` quantifies over the source, and
`ComplexAnalytic.AnalyticSpace.restrictHom f V` has the **preimage** of `V` for its source — so
`ComplexAnalytic.condGoodOpen_nonempty`, which is about the base, does not close the vacuity
reading and `ComplexAnalytic.nonempty_restrict_preimage_condGoodOpen` is what does.
`OkaTest/StandardEtaleNotFinite.lean` states the rule in terms at
`ComplexAnalytic.nonempty_analytification_etalePresentation_cond` — *"without this the theorems
below would be statements about a morphism out of an empty space, which both fields of
`ComplexAnalytic.AnalyticSpace.IsLocalIso` and both of `ComplexAnalytic.AnalyticSpace.IsFinite`
satisfy vacuously"* — and that is the very point this file reuses.

**It is not the formal statement of that claim**, and `OkaTest/StandardEtaleNotFinite.lean`'s
`## What is not checked here` says what would be: something relating
`ComplexAnalytic.AnalyticSpace.restrictHom` at `V = ⊤` to the morphism itself, which nothing in
this repository states. That bullet is **not** retired here and this file does not claim it is.

## Main definitions

- `ComplexAnalytic.condPolyF`: **`ComplexAnalytic.condF` in the polynomial vocabulary**, which is
  the parabola's `F` at `n = 1` and `i = 0`. An `abbrev`, so that
  `ComplexAnalytic.hypersurfaceCommonZeroImage_parabola` applies through it without a lemma.
- `ComplexAnalytic.condGoodOpen`: **the open subset of the base**, the complement of the bad set,
  which the theorems below identify as the punctured line.

## Main results

- `ComplexAnalytic.lastVarPolyEquiv_symm_condPolyF` and
  `ComplexAnalytic.lastVarPolyEquiv_symm_X_eq_condG`: **the parabola's pair is
  `ComplexAnalytic.condF` and `ComplexAnalytic.condG`**, which is the identification this file
  exists to make.
- `ComplexAnalytic.isFiniteEtale_restrictHom_condEtaleProj`: **the restricted morphism is finite
  étale.**
- `ComplexAnalytic.condGoodOpen_eq`, `ComplexAnalytic.condGoodOpen_nonempty` and
  `ComplexAnalytic.condGoodOpen_ne_univ`: **the open subset it is finite étale over is the
  punctured line**, and is therefore proper and non-empty — so the restriction removes something
  and leaves something.
- `ComplexAnalytic.nonempty_restrict_preimage_condGoodOpen`: **and the source of the restricted
  morphism is not empty**, which is what stops the theorem above holding vacuously. `V` being
  non-empty does *not* say this: `ComplexAnalytic.AnalyticSpace.restrictHom` restricts the source
  to the **preimage** of `V`, and that is the space both fields of
  `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` quantify over.

## Two things measured here that a reader would otherwise pay for

* **`open CategoryTheory` is load-bearing**, for the `≫` in `ComplexAnalytic.condEtaleProj`'s
  spelling. Removing it fails with `expected token` at the statement rather than with an
  elaboration error, which reads as a syntax problem and is not one.
* **`ComplexAnalytic.condGoodOpen_eq` needs a trailing `rfl` after its `rw`**, on a goal whose two
  sides print identically. It is the coercion `Oka/Analytification/OpenBaseFiniteness.lean`
  already records at `ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_nonempty`: the set is
  spelled at `ULift (Fin n) → ℂ` on one side and at
  `↑(ComplexAnalytic.AnalyticSpace.complexAffineSpace n).toTopCat` on the other. **It is not a
  sign that the statement is wrong.**

**No `rw` below names a definition.** `ComplexAnalytic.lastVarPolyEquiv_symm_condPolyF` unfolds
`ComplexAnalytic.condPolyF` by `change`, for the reason `OkaTest/StandardEtaleCond.lean` gives at
every one of its own unfoldings: naming a definition as a rewrite rule generates its equation
lemma into this module. **Stated without a numeral on purpose** — that file's own sentence said
*"here and in the four proofs below"* where `grep -n "^ *change "` returns six, and a first head
of this file copied the wrong figure across. The count is repaired there in the same commit and
is not restated here.

## What is not here

* **No `OkaTest/Axioms/` guard.** Every declaration here is in the test library, and
  `OkaTest/Axioms/` guards declarations of the `Oka` library —
  the rule `ComplexAnalytic.condPair` and `ComplexAnalytic.sqSubOnePair` are already unguarded
  under.
* **No claim that `ComplexAnalytic.condGoodOpen` is the image.**
  `OkaTest/StandardEtaleNotFinite.lean` declines to compute the image of
  `ComplexAnalytic.condEtaleProj`, and this file inherits that: `ComplexAnalytic.condGoodOpen` is
  a subset of the **base**, and that the image is exactly it is neither stated nor used.
* **Nothing at `k ≥ 1`.** `ComplexAnalytic.condBase` is the empty presentation, so everything here
  is `k = 0`, as at every file this one sits beside.
* **Nothing relating either vocabulary to `ComplexAnalytic.parabolaPunctured`.**
  `ComplexAnalytic.hypersurfaceCommonZeroImage_parabola`'s docstring records that
  `OkaTest/OpenBaseProjection.lean` carries the same geometry as
  `ComplexAnalytic.parabolaPunctured`, in a third vocabulary, and that nothing relates them. This
  file relates the parabola's spelling to `ComplexAnalytic.condF`'s and **not** either to that
  one; the third identification is still unmade.
* **No general statement about the size of `V`.** It remains a hypothesis on the pair `(F, G)`
  rather than a theorem, exactly as
  `Oka/Analytification/StandardEtaleFiniteness.lean` and
  `Oka/Analytification/StandardEtaleFiniteEtale.lean` say; what changes is that the finite-étale
  class now has one instance at which that hypothesis is met non-trivially.
-/

open CategoryTheory MvPolynomial Polynomial ComplexAnalytic

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The parabola's pair is this file's pair -/

/-- **`ComplexAnalytic.condF` in the polynomial vocabulary**: `X² − C x₀` over
`ℂ[x₀]`, which is `Oka/Analytification/OpenBaseFiniteness.lean`'s parabola at `n = 1` and
`i = 0`.

An `abbrev` and not a `def`, so that
`ComplexAnalytic.hypersurfaceCommonZeroImage_parabola` — stated at the written-out polynomial —
applies through it and the theorems below need no unfolding lemma. -/
abbrev condPolyF : Polynomial (MvPolynomial (ULift.{u} (Fin 1)) ℂ) :=
  Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X (ULift.up 0))

/-- **`ComplexAnalytic.condPolyF` is monic**, which is
`Oka/Analytification/StandardEtaleFiniteEtale.lean`'s one hypothesis on `F` and what makes the
complement of the bad set open. -/
theorem monic_condPolyF : condPolyF.{u}.Monic :=
  Polynomial.monic_X_pow_sub_C _ two_ne_zero

/-- **The parabola's `F` is `ComplexAnalytic.condF`.**

`ComplexAnalytic.lastVarPolyEquiv_symm_X` for the polynomial variable and
`ComplexAnalytic.lastVarPolyEquiv_symm_C` for the constant, which is
`ComplexAnalytic.condF_eq`'s computation read backwards — that theorem sends `condF` up into the
presented base, and this one sends the polynomial form down into `ℂ[x₀, x₁]`.

**The unfolding is a `change` and not a `rw [condPolyF]`**, for the reason
`OkaTest/StandardEtaleCond.lean` states at every one of its own: a `rw` at a definition asks Lean
to generate its equation lemma, which lands in this module under that definition's name. -/
theorem lastVarPolyEquiv_symm_condPolyF :
    (lastVarPolyEquiv.{u} 1).symm condPolyF.{u} = condF.{u} := by
  change (lastVarPolyEquiv.{u} 1).symm
    (Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X (ULift.up 0))) = _
  rw [map_sub, map_pow, lastVarPolyEquiv_symm_X, lastVarPolyEquiv_symm_C, MvPolynomial.rename_X]
  rfl

/-- **The parabola's `G` is `ComplexAnalytic.condG`.**

`ComplexAnalytic.lastVarPolyEquiv_symm_X` and nothing else: `condG` is
`MvPolynomial.X (localisationVar 1)` by `rfl`, which is the `h1` inside
`ComplexAnalytic.condF_eq`'s proof. -/
theorem lastVarPolyEquiv_symm_X_eq_condG :
    (lastVarPolyEquiv.{u} 1).symm Polynomial.X = condG.{u} :=
  lastVarPolyEquiv_symm_X.{u}

/-! ### The open subset of the base -/

/-- **The open subset of the base the morphism is finite étale over**: the complement of
`ComplexAnalytic.hypersurfaceCommonZeroImage`, which
`ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage` makes open at a monic `F`.

Stated as the complement rather than as the punctured line so that it is the `V` of
`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl` on the nose;
`ComplexAnalytic.condGoodOpen_eq` is what says which set it is. -/
abbrev condGoodOpen : TopologicalSpace.Opens (ULift.{u} (Fin 1) → ℂ) :=
  ⟨(hypersurfaceCommonZeroImage.{u} condPolyF.{u} Polynomial.X)ᶜ,
    (isClosed_hypersurfaceCommonZeroImage.{u} condPolyF.{u} Polynomial.X
      monic_condPolyF.{u}).isOpen_compl⟩

/-! ### The morphism is finite étale over it -/

/-- **The morphism `OkaTest/StandardEtaleNotFinite.lean` proves is not finite is finite étale once
restricted over the complement of the origin.**

`ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl` at
`ComplexAnalytic.condPair`, whose two lift hypotheses are
`ComplexAnalytic.condF_eq` and `ComplexAnalytic.condG_eq` carried across the two identifications
above. **Nothing is built**: the content is that `ComplexAnalytic.condPair` is the parabola.

The `rwa` is what brings the morphism to `ComplexAnalytic.condEtaleProj`'s spelling, which is the
one `ComplexAnalytic.not_isFinite_condEtaleProj` is about — without it the two theorems would be
about morphisms a reader has to check are the same. -/
theorem isFiniteEtale_restrictHom_condEtaleProj :
    AnalyticSpace.IsFiniteEtale
      (AnalyticSpace.restrictHom condEtaleProj.{u} condGoodOpen.{u}) := by
  have h := isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp_compl.{u}
    condBase.{u} condPolyF.{u} Polynomial.X monic_condPolyF.{u} condPair.{u}
    (by rw [lastVarPolyEquiv_symm_condPolyF]; exact condF_eq.{u})
    (by rw [lastVarPolyEquiv_symm_X_eq_condG]; exact condG_eq.{u})
  rwa [lastVarPolyEquiv_symm_condPolyF, lastVarPolyEquiv_symm_X_eq_condG] at h

/-! ### And that subset is the punctured line -/

/-- **The open subset is the line with the origin removed.**

`ComplexAnalytic.hypersurfaceCommonZeroImage_parabola` at `i = 0`, whose bad set is the coordinate
hyperplane `{w | w i = 0}` — at `n = 1` a single point.

**The unfolding step is a `change` and not a `show`**, and `lake build --wfail` is what says so:
the coercion out of `TopologicalSpace.Opens` moves the goal, and the `linter.style.show` linter
rejects a `show` that does. `lake env lean` on this file exits 0 either way, so a scratch run is
not evidence here.

**The trailing `rfl` is not redundant** and the goal it closes prints with both sides identical:
the set is spelled at `ULift (Fin 1) → ℂ` on one side and at
`↑(ComplexAnalytic.AnalyticSpace.complexAffineSpace 1).toTopCat` on the other, which is the same
coercion `ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_nonempty`'s own docstring records
as forcing its `Set.Nonempty` spelling. -/
theorem condGoodOpen_eq :
    (condGoodOpen.{u} : Set (ULift.{u} (Fin 1) → ℂ)) =
      {w : ULift.{u} (Fin 1) → ℂ | w (ULift.up 0) = 0}ᶜ := by
  change (hypersurfaceCommonZeroImage.{u} condPolyF.{u} Polynomial.X)ᶜ = _
  rw [hypersurfaceCommonZeroImage_parabola.{u} (ULift.up 0)]
  rfl

/-- **The open subset of the base is not empty** —
`ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_ne_univ` read through
`Set.nonempty_compl`.

**This is not what rules out vacuity, and an earlier head of this file said it was.**
`ComplexAnalytic.AnalyticSpace.restrictHom f V` goes
`A.restrict ((Opens.map f.base).obj V) ⟶ B.restrict V`, so both fields of
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` quantify over the **preimage** of `V` in the source,
and a non-empty `V` is consistent with that preimage being empty. The statement that closes it is
`ComplexAnalytic.nonempty_restrict_preimage_condGoodOpen` below, and the rule is the one
`OkaTest/StandardEtaleNotFinite.lean` states at
`ComplexAnalytic.nonempty_analytification_etalePresentation_cond`: *"without this the theorems
below would be statements about a morphism out of an empty space"*. What this lemma is for is the
other half — that the restriction removes something and is not the whole base, which is
`ComplexAnalytic.condGoodOpen_ne_univ`'s job, and that `V` itself is a real open set. -/
theorem condGoodOpen_nonempty :
    (condGoodOpen.{u} : Set (ULift.{u} (Fin 1) → ℂ)).Nonempty :=
  Set.nonempty_compl.2 (hypersurfaceCommonZeroImage_parabola_ne_univ.{u} (ULift.up 0))

/-- **And it is not everything**, so the restriction is doing work —
`ComplexAnalytic.hypersurfaceCommonZeroImage_parabola_nonempty` read through
`Set.compl_ne_univ`.

Together with `ComplexAnalytic.condGoodOpen_nonempty` and
`ComplexAnalytic.nonempty_restrict_preimage_condGoodOpen` this is what makes the contrast with
`ComplexAnalytic.not_isFinite_condEtaleProj` a contrast: the restriction removes a point of the
base, and the source it restricts to is not empty.

**It does not say the two would be inconsistent at `V = ⊤`, and that is deliberate.** They would
be, but deriving it needs `ComplexAnalytic.AnalyticSpace.restrictHom` at `V = ⊤` related to the
morphism itself, which is precisely the bridge `OkaTest/StandardEtaleNotFinite.lean`'s
`## What is not checked here` records as absent — so the sentence would be true and underivable
here, which is the shape this line keeps out of its docstrings. -/
theorem condGoodOpen_ne_univ :
    (condGoodOpen.{u} : Set (ULift.{u} (Fin 1) → ℂ)) ≠ Set.univ :=
  Set.compl_ne_univ.2 (hypersurfaceCommonZeroImage_parabola_nonempty.{u} (ULift.up 0))

/-! ### And the space the theorem is actually about is not empty -/

/-- **The source of the restricted morphism is not empty**, which is what stops
`ComplexAnalytic.isFiniteEtale_restrictHom_condEtaleProj` being a statement about a morphism out of
nothing.

**The space to exhibit a point of is the preimage and not the base.**
`ComplexAnalytic.AnalyticSpace.restrictHom f V` is
`A.restrict ((Opens.map f.base).obj V) ⟶ B.restrict V`, and both fields of
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` quantify over its source; `V` being non-empty says
nothing about that. An earlier head of this file glossed
`ComplexAnalytic.condGoodOpen_nonempty` as closing this and it does not.

**Nothing new is proved.** `ComplexAnalytic.nonempty_analytification_etalePresentation_cond`
supplies the point `(1, 1, 1)`, and `ComplexAnalytic.base_condEtaleProj_ne_zero` says of *every*
point of that source that its image has non-zero `0`-th coordinate — so the whole source lies in
the preimage, and `ComplexAnalytic.condGoodOpen_eq` is what turns that into membership. Both are
in `OkaTest/StandardEtaleNotFinite.lean`, which this file already imports for
`ComplexAnalytic.condEtaleProj`.

That the *whole* source lies in the preimage is stronger than this statement needs and is not
recorded as a theorem; only the one point is used. -/
theorem nonempty_restrict_preimage_condGoodOpen :
    Nonempty ((AnalyticSpace.analytification.{u}
      (etalePresentation.{u} condBase.{u} condF.{u} condG.{u})).restrict
        ((TopologicalSpace.Opens.map condEtaleProj.{u}.toLRSHom.base).obj condGoodOpen.{u})) := by
  obtain ⟨y⟩ := nonempty_analytification_etalePresentation_cond.{u}
  refine ⟨⟨y, ?_⟩⟩
  change (condEtaleProj.{u}.toLRSHom.base y : AnalyticSpace.complexAffineSpace.{u} 1) ∈
    (condGoodOpen.{u} : Set (ULift.{u} (Fin 1) → ℂ))
  rw [condGoodOpen_eq.{u}]
  exact base_condEtaleProj_ne_zero.{u} y

end

end ComplexAnalytic

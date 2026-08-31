/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Oka.AnalyticSpace.SigmaFiniteEtale

/-!
# The finite étale covers of an analytic space, as a category

`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is a property of a *morphism*. The Riemann existence
theorem is a statement about the *category* of such morphisms into a fixed base, and nothing in
this repository had made that category — `Oka/AnalyticSpace/CoveringSpace.lean` builds covering
spaces and compares them one at a time, and its `## What is not here` says nothing about morphisms
of covers because there was nothing to say it about. This file makes the category and says what a
morphism of covers is.

## The property is already a `MorphismProperty`, and the `def` below buys dot notation

`CategoryTheory.MorphismProperty C` is `∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop`, and
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is declared over the same telescope — `{X Y}` where
that is `⦃X Y⦄`, and **a binder annotation is not part of the type**, which is what the `@` below
discharges — so `@ComplexAnalytic.AnalyticSpace.IsFiniteEtale` **is** a morphism property with no
repackaging:
`example : MorphismProperty AnalyticSpace.{u} := @IsFiniteEtale.{u}` elaborates on the nose. This
is the same arrangement `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean` relies on, where
`@AlgebraicGeometry.IsFinite` — a class with the same `{X Y}` binders — is used as a morphism
property while remaining a class.

**What does not work is dot notation.** `(@IsFiniteEtale).Over ⊤ X` fails, because the elaborator
sees a function type and goes looking for a field of `Function`; the message names a declaration
under that namespace which does not exist. So `ComplexAnalytic.AnalyticSpace.isFiniteEtale` below
is a name for something that already existed, and it is worth being precise about that: it is not
a second notion, it is `@IsFiniteEtale` with a head symbol, and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff` is `Iff.rfl`.

## Why the morphisms are all morphisms over the base

`CategoryTheory.MorphismProperty.Over P Q X` takes two properties: `P` cuts out the objects by
their structure map, and `Q` cuts out the morphisms. **`Q` is `⊤` here**, so a morphism of covers
is any morphism of analytic spaces commuting with the two structure maps, and nothing more. That
is the definition the Riemann existence theorem needs, and it is *not* the same as asking the
morphism to be finite étale itself. The two agree in extension —
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` (`Oka/AnalyticSpace/LocalIso.lean`) says the
underlying morphism of a morphism of covers is finite étale whenever the *target* cover's total
space is Hausdorff — but `Q` is still `⊤`, and that is what makes the category cheap to form: an
object of it carries no condition to discharge on its morphisms. See `## What is not here`.

## The four instances, and none of them is needed to form the category

`CategoryTheory.MorphismProperty.Over P Q X` asks its conditions of `Q`, and `Q` is `⊤` here, so
the category below would exist with no instance on `P` at all. The four are stated because every
downstream use of the property — a fibre functor, a Galois-category structure, the comparison
functor taxis #1113 wants — asks for them, and because *finite étale morphisms compose and contain
the identities* is a single statement worth having under one name rather than as two instances
elaborated separately. Each is a quotation of a declaration that was already on `master`; nothing
is proved here. (Those three are named in the instances' own vicinity rather than in this
docstring, because `scripts/guard_coverage.py` reads every backticked repository name under a
`## Main results` heading as a result this file advertises, and they are another file's.)

## Main definitions

- `ComplexAnalytic.AnalyticSpace.isFiniteEtale`: **finite étale as a
  `CategoryTheory.MorphismProperty`**, which is the class with a head symbol.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`: **the category of finite étale covers of a
  fixed analytic space**, with all morphisms over it.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial`: **two objects of it** — the base over
  itself, and the trivial `ι`-sheeted cover for a finite `ι`.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff`: membership is the class, by `Iff.rfl`.
- `ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id`: **an object isomorphic to the base over
  itself has an invertible structure map.** This is what turns a `¬ IsIso` statement about one
  cover into the statement that the category has an object the identity is not, and it is how the
  non-vacuity in `OkaTest/FiniteEtaleOver.lean` is stated.

## What is not here

* **Cancellation — this is no longer absent, and it is not in this file.** *"If `g` and `f ≫ g`
  are finite étale then `f` is"* is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` in
  `Oka/AnalyticSpace/LocalIso.lean`, for a `[T2Space]` middle space. **This is what a
  Galois-category structure on the category below needs first**, and taxis #1114's report
  identifies the same statement as the difficulty of essential surjectivity; what that structure
  still lacks is in the two bullets below, and cancellation is no longer among it.

  **What it does not do is make a morphism of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X`
  carry a condition.** `Q` is `⊤` in the definition above and stays `⊤`; the cancellation says
  that the underlying morphism of every such morphism *is* finite étale, not that the category
  asks it to be. Nothing below reads it that way and nothing needs to.

  **The bullet was retired in three steps and the last one is the interesting one.** It first said
  the two classes are stated as stability under composition only and that Mathlib is in the same
  position one level down; both halves of that were wrong, and taxis #1312 measured how. It then
  said one topological statement was left, to be got at by a covering-map argument. That statement
  is proved, and it turned out not to be about covering maps: what was missing was a separation
  axiom on the middle space and nothing else — see the third sub-bullet.

  * `ComplexAnalytic.AnalyticSpace.IsFinite` **does** have a cancellation lemma —
    `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp`, which concludes `IsFinite f` from
    `IsFinite (f ≫ i)`. What it asks in place of `IsFinite i` is
    `Function.Injective i.toLRSHom.base`, and the `i` here is the structure map of a cover, which
    is exactly what is not injective: `OkaTest/FiniteEtaleOver.lean`'s separating object is
    `ComplexAnalytic.sq`, whose `ComplexAnalytic.not_isIso_sq` is proved *from*
    non-injectivity. So the lemma exists and its hypothesis is the one a cover cannot supply,
    which is a route where "nothing exists" offered none.
  * `ComplexAnalytic.AnalyticSpace.IsLocalIso` **cancels outright** —
    `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp`, in `Oka/AnalyticSpace/LocalIso.lean` beside
    the `ComplexAnalytic.AnalyticSpace.isLocalIso_comp` it is the companion of — and it was free
    from Mathlib rather than hard: `IsLocalHomeomorph.of_comp` is its topological half and asks
    only that `f` be continuous, which a morphism's base map is, and
    `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` with two-out-of-three is the stalk half.
    Those are the two steps that proof takes and it takes no others; the sentence was written here
    before the theorem existed, and what changed is that it now describes something.
    `Mathlib/Topology/Covering/Basic.lean` really does have no composition or cancellation lemma
    for `IsCoveringMap`, only conjugation by a homeomorphism — but that is the wrong file for this
    class, and the earlier version of this bullet carried that negative across from taxis #1114's
    report without noticing.
  * **Closedness of `f` was the last one, and the recorded obstruction to it named the wrong
    thing.** `Oka/AnalyticSpace/Finite.lean`'s cancellation section and
    `Oka/AnalyticSpace/LocalIso.lean`'s `## What is not here` both gave the real line with two
    origins as the shape, and both said the classical repair needs a separatedness notion and
    fibre products — which this category cannot state, for the same reason as the base-change
    bullet below. **What that example exhibits is a middle space with two points no open set
    separates, and the second factor is not what makes it work**: at a Hausdorff middle space the
    closed half cancels along an arbitrary second factor, by Mathlib's `isProperMap_of_comp_of_t2`
    and the properness of a finite morphism, which is
    `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` in
    `Oka/AnalyticSpace/Finite.lean`. So no separatedness notion and no fibre product was ever
    needed, and the hypothesis that was missing is a separation axiom rather than a construction.
    The counterexample is now compiled as
    `TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` in `OkaTest/FiniteEtaleCancel.lean`,
    where it is the witness that the separation axiom cannot be dropped.
* **No fibre functor and no Galois category.** The fibre functor of a Galois category — declared
  in `Mathlib/CategoryTheory/Galois/Basic.lean`, whose namespace is not in this repository's
  import closure and so cannot be cited by name here — lands in `FintypeCat`, and the fibre of a
  finite étale morphism is finite by
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` — which asks `[T2Space]` of the
  source, a hypothesis lana-agents/oka#222's review measured is not free for a constructed cover.
  Nothing below builds the functor.
* **No pullbacks, so no base change.** `ComplexAnalytic.AnalyticSpace` has no `HasPullback`
  instance anywhere in this repository, so
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`
  is not even statable for `isFiniteEtale` here, and the pullback of a cover along a morphism of
  the base — which is how a Galois category's fibre functor is usually built — does not exist.
* **No degree on objects.** `ComplexAnalytic.AnalyticSpace.degree` is a function of a morphism and
  nothing below reads it off an object of the category.
* **No scheme side and no comparison functor.** Taxis #1113 wants a functor from finite étale
  covers of a presented affine `ℂ`-scheme to these; the source of that functor is
  `(@AlgebraicGeometry.IsFinite ⊓ @AlgebraicGeometry.IsEtale).Over ⊤ X` and is available in
  Mathlib immediately, but it mentions `AlgebraicGeometry.Scheme`, which this line of files does
  not have — three of them argue in titled sections that its absence is a result. **Nothing below
  mentions a scheme.**
-/

open CategoryTheory

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **Finite étale, as a `CategoryTheory.MorphismProperty`.**

This is `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` and not a second notion —
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff` is `Iff.rfl` — declared so that the dot notation
`isFiniteEtale.Over` resolves; the class itself has the binders of a morphism property but the
elaborator will not project a field from a function type. -/
def isFiniteEtale : MorphismProperty AnalyticSpace.{u} := @IsFiniteEtale.{u}

/-- **Membership in the property is the class**, by definition. -/
theorem isFiniteEtale_iff {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) :
    isFiniteEtale.{u} f ↔ IsFiniteEtale f :=
  Iff.rfl

instance : (isFiniteEtale.{u}).IsStableUnderComposition where
  comp_mem f g hf hg := @isFiniteEtale_comp.{u} _ _ _ f g hf hg

instance : (isFiniteEtale.{u}).ContainsIdentities where
  id_mem X := isFiniteEtale_id X

instance : (isFiniteEtale.{u}).IsMultiplicative where

instance : (isFiniteEtale.{u}).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    fun _ _ f (_ : IsIso f) ↦ isFiniteEtale_of_isIso f

/-- **The finite étale covers of `X`**, as a category: the objects are the finite étale morphisms
into `X` and the morphisms are all the morphisms of analytic spaces over `X`.

The second `⊤` is the property asked of the morphisms, and it is deliberate: a morphism of covers
commutes with the two structure maps and is asked for nothing else. -/
abbrev FiniteEtaleOver (X : AnalyticSpace.{u}) : Type _ :=
  (isFiniteEtale.{u}).Over ⊤ X

/-- **The base over itself**, which is an object because the identity is finite étale. -/
def FiniteEtaleOver.id (X : AnalyticSpace.{u}) : FiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _ (𝟙 X) (isFiniteEtale_id X)

/-- **The trivial `ι`-sheeted cover**, for a finite index type: `∐_{i : ι} X ⟶ X`.

`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold` is what makes it an object, and it asks
nothing of `X` — not Hausdorff, not connected, not non-empty. At `ι` a subsingleton this is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id` up to an isomorphism nothing below states. -/
noncomputable def FiniteEtaleOver.trivial (ι : Type u) [Finite ι] (X : AnalyticSpace.{u}) :
    FiniteEtaleOver.{u} X :=
  MorphismProperty.Over.mk _ (sigmaFold ι X) (isFiniteEtale_sigmaFold (ι := ι) X)

/-- **An object isomorphic to the base over itself has an invertible structure map.**

This is the lemma that lets a `¬ IsIso` statement about one cover — of which this repository has
one, for `z ↦ z²` on the punctured line — say that the category has an object the identity is
not. The proof is that the two forgetful functors carry the isomorphism to one of analytic spaces
whose morphism is `e.hom.left`, and that the triangle over `X` identifies `e.hom.left` with the
structure map, the other side of it being the identity.

**The last step is a term and not a `rw [Category.comp_id]`**: the composite displays as
`e.hom.left ≫ (FiniteEtaleOver.id X).hom` and `rw` works at `instances` transparency, which does
not unfold the `def` to reach the `𝟙 X` inside. `(Category.comp_id _).symm.trans` is the same
step at default transparency and is one line. -/
theorem isIso_hom_of_iso_id {X : AnalyticSpace.{u}} {A : FiniteEtaleOver.{u} X}
    (e : A ≅ FiniteEtaleOver.id.{u} X) : IsIso A.hom := by
  have h1 : IsIso e.hom.left :=
    ((MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).mapIso e).isIso_hom
  have h2 : e.hom.left = A.hom := by
    have hw : e.hom.left ≫ 𝟙 X = A.hom :=
      CategoryTheory.Over.w ((MorphismProperty.Over.forget _ ⊤ X).map e.hom)
    exact (Category.comp_id _).symm.trans hw
  rwa [h2] at h1

end ComplexAnalytic.AnalyticSpace

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Oka.AnalyticSpace.Degree

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
the category below would exist with no instance on `P` at all. The four are stated because the
downstream uses of the property — a Galois-category structure, the comparison functor taxis #1113
wants — ask for them, and because *finite étale morphisms compose and contain the identities* is a
single statement worth having under one name rather than as two instances elaborated separately.

Each is a quotation of a declaration that was already on `master`; nothing is proved here. (Those
three are named in the instances' own vicinity rather than in this docstring, because
`scripts/guard_coverage.py` reads every backticked repository name under a `## Main results`
heading as a result this file advertises, and they are another file's.)

**That list named a fibre functor, and that is now measurably wrong.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` below reads the structure map of an
object and the triangle of a morphism, and **none of the four instances**;
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor` reads one thing more — the
object's `prop` field — and reads it only for the finiteness of the values. That is why a fibre
would make sense at every `CategoryTheory.MorphismProperty.Over` and not only at this one.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.isFiniteEtale`: **finite étale as a
  `CategoryTheory.MorphismProperty`**, which is the class with a head symbol.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`: **the category of finite étale covers of a
  fixed analytic space**, with all morphisms over it.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial`: **two objects of it** — the base over
  itself, and the trivial `ι`-sheeted cover for a finite `ι`.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`: **the degree of a cover**, which is
  `ComplexAnalytic.AnalyticSpace.degree` of its structure map.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId`: **the trivial cover at one sheet
  is the base over itself**, as an isomorphism of objects.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber`: **the fibre of a cover over a point of
  the base**, as the preimage type.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor`: **the fibre functor at a
  point**, into `Type u` and into `FintypeCat` — the first functors out of this category declared
  here, and the second is the shape a Galois category asks for.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff`: membership is the class, by `Iff.rfl`.
- `ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id`: **an object isomorphic to the base over
  itself has an invertible structure map.** This is what turns a `¬ IsIso` statement about one
  cover into the statement that the category has an object the identity is not, and it is how the
  non-vacuity in `OkaTest/FiniteEtaleOver.lean` is stated.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`: **a morphism whose restriction
  over `⊤` is finite étale is finite étale** — the step that lets a `V` hypothesis be refuted
  rather than only left unproved, and the only place in this file where the property is read
  through an isomorphism rather than stated.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`: **the degree is an invariant of
  an object**, so `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne`
  separates isomorphism classes by a number.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_id` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial`: the two objects above have
  degrees `1` and `Nat.card ι`, over a non-empty base.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_eq_of_iso_trivial`: **the trivial covers of a
  non-empty base are pairwise non-isomorphic**, indexed by `Nat.card`, so the category there has
  as many isomorphism classes as there are values of that.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff`: **and the first of
  those is sharp** — over a non-empty base the trivial cover is the base over itself exactly when
  its index type has one point. The two directions are proved by different means and neither is
  the other read backwards: the degree separates and never produces an isomorphism.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preconnectedSpace_of_iso` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace`:
  **preconnectedness of the total space is an invariant of an object**, and separates objects the
  degree cannot.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_of_preconnectedSpace`: **the
  total space of a trivial cover with two distinct sheets is disconnected**, so **a cover with a
  preconnected total space is not a trivial one with two distinct sheets** — the separation that
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` is too coarse to make.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber`: **a fibre is finite, with no
  hypothesis at all** — not a separation axiom, not connectedness, nothing about the base. This is
  what the fibre functor into `FintypeCat` needs, and the `## What is not here` bullet that priced
  it at a `[T2Space]` was reading the hypothesis of a different theorem.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber`: **the fibre counts the degree**, over
  a preconnected base and a Hausdorff total space, which is where that `[T2Space]` does belong.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv`: **the two values of the fibre
  functor this file can compute** — a point over the base over itself, and `ι` over the trivial
  `ι`-sheeted cover, both as equivalences rather than as counts.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberEquivOfIso`: **isomorphic covers have
  equinumerous fibres**, which is `CategoryTheory.Functor.mapIso` at that functor.

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
* **The fibre functor is here and the Galois category is not.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor` below are the fibre at a
  point of the base, into `Type u` and into `FintypeCat`; the second is the shape a Galois category
  asks for, that definition being in `Mathlib/CategoryTheory/Galois/Basic.lean`, whose namespace is
  not in this repository's import closure and so cannot be cited by name here.

  **The reason this bullet gave for their absence was wrong, and saying how is the point.** It said
  the fibre of a finite étale morphism is finite by
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, which asks `[T2Space]` of the
  source — a hypothesis lana-agents/oka#222's review measured is not free for a constructed cover.
  That theorem says two fibres have the **same** `Nat.card`, which a morphism all of whose fibres
  are infinite satisfies; finiteness is a *field* of `ComplexAnalytic.AnalyticSpace.IsFinite` and
  costs nothing, which is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber` below. The
  `[T2Space]` buys **constancy** of the count, and constancy is what
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` needs and what a `FintypeCat`-valued
  functor does not.

  **What is absent is the Galois category itself**, whose axioms need the base change the
  **No pullbacks, so no base change** bullet below says this category has not, **and every
  statement about the functor beyond its two laws**: nothing proves it faithful or conservative,
  and nothing exhibits it as an equivalence onto anything.
* **No pullbacks, so no base change.** `ComplexAnalytic.AnalyticSpace` has no `HasPullback`
  instance anywhere in this repository, so
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`
  is not even statable for `isFiniteEtale` here, and the pullback of a cover along a morphism of
  the base — which is how a Galois category's fibre functor is usually built — does not exist.
  **The functor above is not built that way and is not evidence that this absence is harmless**:
  it reads the structure map at one point of the base directly, which is enough to *have* a fibre
  and is not enough to say anything about how it varies.
* **The degree on objects is here, it is coarse, and the second invariant that repairs that is
  here too.** This bullet said `ComplexAnalytic.AnalyticSpace.degree` is a function of a morphism
  and nothing below reads it off an object;
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` does, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso` is what makes that well defined
  on isomorphism classes. It said next that the invariant is coarse and that **nothing below can
  tell apart** the two degree-`2` covers of the punctured line — `OkaTest/FiniteEtaleOver.lean`'s
  `z ↦ z²` and the trivial two-sheeted cover — and that the classical separation, connectedness of
  the total space, was half present in this repository.

  **Both halves are present now and the separation is below.**
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_of_preconnectedSpace` is the
  statement, and what it needed was not a construction: the missing half was
  `ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma`
  (`Oka/AnalyticSpace/SigmaFiniteEtale.lean`), which is the clopen image of a member read as a
  separation, and the transport
  `ComplexAnalytic.AnalyticSpace.preconnectedSpace_of_surjective_base`
  (`Oka/AnalyticSpace/Basic.lean`), which is `DenseRange.preconnectedSpace` at a surjection.
  **The degree bullet's own claim is unchanged and is the point**: the degree still cannot
  separate those two objects, and it is a second invariant rather than a sharper first one that
  does.

  **What is still not here is any invariant that separates two *connected* covers, and the fibre
  functor above is not one.** As a bare finite set a fibre carries nothing the degree does not
  already carry — over a preconnected base and a Hausdorff total space its size *is* the degree,
  by `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` — and what separates is the
  monodromy *action* on it, which needs a fundamental group nothing here connects to a cover and
  the base change the **No pullbacks, so no base change** bullet above says this category has not.

  **What the witness in `OkaTest/FiniteEtaleOver.lean` settles is that the functor's values are
  not a complete invariant.** `OkaTest.FiniteEtaleOver.nonempty_fiber_equiv_trivial_sqOver` puts
  the fibres of `z ↦ z²` and of the trivial two-sheeted cover of the punctured line in bijection
  at every point of the base — the same pair that
  `OkaTest.FiniteEtaleOver.not_iso_trivial_sqOver` proves non-isomorphic. So two objects this
  category distinguishes have fibres it does not, at a base this repository exhibits, and that
  much is compiled rather than argued. **It needs neither `[T2Space]` nor `[PreconnectedSpace]`**,
  the finiteness of a fibre being unconditional.

  **What it does not settle is the sentence above, and the reason is the second member of its
  pair.** The trivial two-sheeted cover's total space is disconnected —
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial`, which is what
  `OkaTest.FiniteEtaleOver.not_iso_trivial_sqOver` reads and not what it proves — so the pair is a
  connected cover and a disconnected one, and a claim quantified over pairs of *connected* covers
  is untouched by it. **At a pair of connected covers this repository does exhibit, the values do
  separate**: `OkaTest.FiniteEtaleOver.sqOver` and the base over itself at the punctured line are
  both preconnected (`OkaTest.FiniteEtaleOver.preconnectedSpace_left_sqOver` and
  `ComplexAnalytic.preconnectedSpace_restrict_punctured`) and non-isomorphic
  (`OkaTest.FiniteEtaleOver.not_iso_id_sqOver`), and their fibres have two points and one —
  `OkaTest.FiniteEtaleOver.card_fiber_sqOver` and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId`. **That separation is the degree
  again** and is no evidence that the fibre sees more, which is the paragraph above read at an
  instance. So the sentence above stays an argument, and what would compile it is a pair of
  connected covers of the same degree — which is what the missing monodromy action would be
  needed to tell apart.
* **No scheme side and no comparison functor.** Taxis #1113 wants a functor from finite étale
  covers of a presented affine `ℂ`-scheme to these; the source of that functor is
  `(@AlgebraicGeometry.IsFinite ⊓ @AlgebraicGeometry.IsEtale).Over ⊤ X` and is available in
  Mathlib immediately, but it mentions `AlgebraicGeometry.Scheme`. **The reason given here until
  2026-09-02 was that "this line of files does not have" one, "three of them argue in titled
  sections that its absence is a result", and both halves of that have moved.** The appositive
  names the `Oka/Analytification/` line, since that is where those sections are, and
  `Oka/Analytification/SpecScheme.lean` put `ComplexAnalytic.specScheme` on it; and there are
  **two** of them, not three — `Oka/Analytification/Comparison.lean`'s, which is about that file's
  own statements, and `Oka/Analytification/AffineCover.lean`'s, which is about its input. No file
  under `Oka/AnalyticSpace/`, where this one lives, has such a section.
  **What survives is the shape of the obstruction and not its price**: `ComplexAnalytic.specScheme`
  is glued *from* a cover datum and is an output of one, where the functor above wants a scheme as
  its *input*, and nothing on either line passes from a scheme to a cover.
  `Oka/AnalyticSpace/Glue.lean`'s first bullet makes the same distinction for the same reason.
  **Nothing below mentions a scheme.**
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
nothing of `X` — not Hausdorff, not connected, not non-empty. At an inhabited subsingleton `ι`
this is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id` up to the isomorphism
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId` below, and over a non-empty base
those are the only index types at which it is
(`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff`). -/
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

/-! ### The degree of a cover -/

/-- **The degree of a cover**: `ComplexAnalytic.AnalyticSpace.degree` of its structure map.

`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso` below is what makes this a
function of the isomorphism class and not only of the object, which is the property the word
"invariant" is doing work for and the one a degree-preserving functor would be stated against.

**Dot notation does reach this name through the `abbrev`, and that was measured rather than
assumed.** `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` is an `abbrev` for
`CategoryTheory.MorphismProperty.Over`, so the expectation is that `A.degree` looks for a field of
the latter and fails; it does not — generalized field notation resolves against the head of the
type as the binder writes it, and `A.degree` elaborates. The statements below nevertheless spell
the name in full, because every declaration in this file carries an explicit universe annotation
and dot notation has nowhere to put one. -/
noncomputable def FiniteEtaleOver.degree {X : AnalyticSpace.{u}} (A : FiniteEtaleOver.{u} X) : ℕ :=
  AnalyticSpace.degree A.hom

/-- **Isomorphic covers have the same degree.**

An isomorphism `e` of covers is a triangle over `X`: `CategoryTheory.Over.w` says
`e.hom.left ≫ B.hom = A.hom`, and the two forgetful functors make `e.hom.left` an isomorphism of
analytic spaces, so `ComplexAnalytic.AnalyticSpace.degree_isIso_comp`
(`Oka/AnalyticSpace/Degree.lean`) applies. **Nothing finite étale is read**: the property appears
in the proof below only as the `_` of `CategoryTheory.MorphismProperty.Over.forget`, and neither
object's membership in it is ever opened — the degree of a cover is a fact about its structure map
and not about why that map is an object.

**The morphism is supplied by name rather than as a `_`, and that is a choice and not a
constraint.** `(e := e.hom.left)` says what the theorem is being applied at, which is worth the
two words in a proof whose whole content is that one application. It is not required:
`degree_isIso_comp _ _` compiles here — measured, by substituting that spelling into a copy of
this file and running `lake env lean` on the copy, which prints nothing.

**This paragraph said the `_` spelling was *forced*, and the failure it quoted belongs to the
draft below rather than to this proof.** With `rw [FiniteEtaleOver.degree,
FiniteEtaleOver.degree, ← hw]` in place of the `congrArg`, `exact degree_isIso_comp _ _` does
fail with *"failed to synthesize instance of type class `IsIso e.hom.left`"*, `haveI`
notwithstanding — both spellings were re-measured here, on copies of this file, and what changed
under the paragraph was the proof. **What distinguishes the two is not settled by that
measurement and nothing here claims it**; what is settled is that the constraint is the draft's
and the name here is a reader's convenience.

**No `rw` here names the definition, and the cost of the obvious one is a dump row.**
`rw [FiniteEtaleOver.degree, FiniteEtaleOver.degree, ← hw]` is the spelling this proof was written
in first, and naming a definition as a rewrite rule asks Lean to generate its equation lemma:
`scripts/DumpOkaDecls.lean` on that draft reports one extra row, the `.eq_1` of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`, measured rather than expected — and it is
a row this definition alone pays, because no other proof anywhere names it. (The cost is per
definition and not per proof: `Oka/AnalyticSpace/Degree.lean`'s
`ComplexAnalytic.AnalyticSpace.degree_comp_of_bijective_base` does write
`rw [degree, degree]` and adds nothing, `ComplexAnalytic.AnalyticSpace.degree.eq_1` having been
generated by that file already.) What
replaces it is `congrArg` and `Eq.trans` at the definition's own unfolding, which go through
definitional unfolding and generate nothing — the same cure, for the same defect, that
`Oka/Analytification/RefineDatumToBase.lean` states as a rule for its own file, and the reason
`Δdump` for this branch is the number of declarations it adds and no more. **A `show` reaches the
same goal and is equally free of the equation lemma, and is not what is written**: Mathlib's
`linter.style.show` warns on a `show` that **changed** the goal and asks for `change` in its
place, and a `show` unfolding this definition changes it. It is in `linter.mathlibStandardSet`,
which `lakefile.toml` enables weakly, so `lake build --wfail` — which `.orchestra/validation.sh`
runs — turns the warning into a failure. **This sentence described the rule as one about the
*first* tactic of a proof**, which is not what the linter does: a copy of this file carrying that
`show` as the proof's **third** tactic draws the warning all the same, *"this tactic invocation
changed the goal"*, measured here. The conclusion was right and the rule under it was not. -/
theorem FiniteEtaleOver.degree_eq_of_iso {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (e : A ≅ B) :
    FiniteEtaleOver.degree.{u} A = FiniteEtaleOver.degree.{u} B := by
  haveI : IsIso e.hom.left :=
    ((MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).mapIso e).isIso_hom
  have hw : e.hom.left ≫ B.hom = A.hom :=
    CategoryTheory.Over.w ((MorphismProperty.Over.forget _ ⊤ X).map e.hom)
  exact (congrArg (fun f : A.left ⟶ X ↦ AnalyticSpace.degree f) hw).symm.trans
    (degree_isIso_comp (e := e.hom.left) _)

/-- **Two covers of different degrees are not isomorphic.**

The contrapositive of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`, stated as
`IsEmpty` of the type of isomorphisms because that is the shape
`OkaTest/FiniteEtaleOver.lean`'s separations are written in. **This is the first invariant on this
category that separates objects by a computation** rather than by refuting an `IsIso` of one
particular morphism, and the two are genuinely different: a `¬ IsIso f` says nothing about the
existence of some *other* isomorphism, and this says there is none. -/
theorem FiniteEtaleOver.isEmpty_iso_of_degree_ne {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X}
    (h : FiniteEtaleOver.degree.{u} A ≠ FiniteEtaleOver.degree.{u} B) : IsEmpty (A ≅ B) :=
  ⟨fun e ↦ h (FiniteEtaleOver.degree_eq_of_iso.{u} e)⟩

/-- **The base over itself has degree one**, over a non-empty base.

`ComplexAnalytic.AnalyticSpace.degree_id` read through the definition; the `[Nonempty X]` is that
theorem's and is not decorative, the degree of any morphism out of or into the empty space being
`0` by the `iSup` convention `ComplexAnalytic.AnalyticSpace.degree` documents. -/
theorem FiniteEtaleOver.degree_id (X : AnalyticSpace.{u}) [Nonempty X] :
    FiniteEtaleOver.degree.{u} (FiniteEtaleOver.id.{u} X) = 1 :=
  AnalyticSpace.degree_id X

/-- **The trivial `ι`-sheeted cover has degree `Nat.card ι`**, over a non-empty base.

`ComplexAnalytic.AnalyticSpace.degree_sigmaFold` read through the definition. `[Finite ι]` is
asked here because `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` asks it, not because
the degree computation needs it — that theorem holds at every `ι`, with both sides `0` when `ι` is
infinite. -/
theorem FiniteEtaleOver.degree_trivial (ι : Type u) [Finite ι] (X : AnalyticSpace.{u})
    [Nonempty X] :
    FiniteEtaleOver.degree.{u} (FiniteEtaleOver.trivial.{u} ι X) = Nat.card ι :=
  AnalyticSpace.degree_sigmaFold ι X

/-- **The trivial `ι`-sheeted cover is not the base over itself unless `ι` has one point.**

The separation `OkaTest/FiniteEtaleOver.lean` records as missing: it says that separating the
trivial cover from the identity *"needs a statement that `X ⨿ X ⟶ X` is not an isomorphism, which
this repository does not have"*. It does not need one. The degree is `Nat.card ι` on one side and
`1` on the other, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne` closes it — no `¬ IsIso`
of any morphism is proved on the way, which is exactly why the route the absence was priced at is
not the route taken.

`Nat.card ι ≠ 1` is the honest hypothesis and is weaker than `1 < Nat.card ι`: it also covers the
empty `ι`, where the cover is the empty space and the degree is `0`. **And it is sharp** —
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff` at the end of this
file is this statement and its converse together. -/
theorem FiniteEtaleOver.isEmpty_iso_trivial_id (ι : Type u) [Finite ι] (X : AnalyticSpace.{u})
    [Nonempty X] (h : Nat.card ι ≠ 1) :
    IsEmpty (FiniteEtaleOver.trivial.{u} ι X ≅ FiniteEtaleOver.id.{u} X) :=
  FiniteEtaleOver.isEmpty_iso_of_degree_ne.{u} <| by
    rw [FiniteEtaleOver.degree_trivial, FiniteEtaleOver.degree_id]
    exact h

/-- **Two trivial covers of a non-empty base are isomorphic only if their index types have the same
cardinality.**

So the category over a non-empty base has an object of every degree in the range of `Nat.card` and
they are pairwise non-isomorphic — at `ι = ULift (Fin n)` that is one class for every `n`, which
is what turns *"at least two isomorphism classes"* into *"infinitely many"*.
`OkaTest/FiniteEtaleOver.lean` instantiates it.

Stated as an implication from an isomorphism rather than as an `IsEmpty`, because the two index
types are the data a caller has and the cardinality is what it wants back; the `IsEmpty` form is
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne` at the same two
objects. -/
theorem FiniteEtaleOver.card_eq_of_iso_trivial {ι κ : Type u} [Finite ι] [Finite κ]
    {X : AnalyticSpace.{u}} [Nonempty X]
    (e : FiniteEtaleOver.trivial.{u} ι X ≅ FiniteEtaleOver.trivial.{u} κ X) :
    Nat.card ι = Nat.card κ := by
  rw [← FiniteEtaleOver.degree_trivial ι X, ← FiniteEtaleOver.degree_trivial κ X]
  exact FiniteEtaleOver.degree_eq_of_iso.{u} e

/-! ### Connectedness of the total space, which the degree does not see -/

/-- **Isomorphic covers have homeomorphic total spaces, so preconnectedness passes between
them.**

The same triangle `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso` reads, and the
same first step: the two forgetful functors carry `e` to an isomorphism of analytic spaces whose
morphism is `e.hom.left`, so it is surjective on points and
`ComplexAnalytic.AnalyticSpace.preconnectedSpace_of_surjective_base`
(`Oka/AnalyticSpace/Basic.lean`) applies. **The triangle itself is not used here**, unlike in the
degree statement — nothing about the structure maps is read, only that the total spaces are
isomorphic, so this would hold in `CategoryTheory.Over X` with no property at all.

**Stated in one direction and used in both.** An isomorphism has a symm, so a caller wanting the
other direction applies this at `e.symm`;
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace` below is the
contrapositive and is the form the separations are written in. -/
theorem FiniteEtaleOver.preconnectedSpace_of_iso {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (e : A ≅ B) [PreconnectedSpace A.left] :
    PreconnectedSpace B.left := by
  haveI : IsIso e.hom.left :=
    ((MorphismProperty.Over.forget _ ⊤ X ⋙ CategoryTheory.Over.forget X).mapIso e).isIso_hom
  exact preconnectedSpace_of_surjective_base e.hom.left (surjective_base_of_isIso _)

/-- **A cover with a preconnected total space is not isomorphic to one without.**

The contrapositive of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preconnectedSpace_of_iso`, in
the `IsEmpty` shape `OkaTest/FiniteEtaleOver.lean`'s separations are written in. **This is the
second invariant on this category**, and the first that is not a number:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne` separates by a
computation and is blind to any two objects of equal degree, which the punctured line supplies at
degree `2`.

**The hypothesis is instance-implicit on `A` and explicit on `B`**, which is not a symmetry the
statement has to break and is where the two sides are actually used: the connected side is the one
a caller has an instance for — `ComplexAnalytic.preconnectedSpace_restrict_punctured` is one — and
the disconnected side is the one a caller has a *theorem* for, since `¬ PreconnectedSpace` is not
a class. -/
theorem FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} [PreconnectedSpace A.left] (h : ¬ PreconnectedSpace B.left) :
    IsEmpty (A ≅ B) :=
  ⟨fun e ↦ h (FiniteEtaleOver.preconnectedSpace_of_iso.{u} e)⟩

/-- **The total space of a trivial cover with two distinct sheets is not preconnected.**

`ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma`
(`Oka/AnalyticSpace/SigmaFiniteEtale.lean`) at the constant family, whose members are all `X`, so
the two points it asks for are both `Classical.arbitrary X` and `[Nonempty X]` supplies them.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial`'s total space is that disjoint union by
definition, and no lemma is needed to say so.

**`i ≠ j` and not `1 < Nat.card ι`.** The two are equivalent at a finite `ι`, and the numeral
version is what a degree statement would be phrased in — but the proof consumes two indices, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial` is the place where this file turns
an index type into a number. Asking for the indices keeps the cardinality arithmetic out of a
statement that does no counting. -/
theorem FiniteEtaleOver.not_preconnectedSpace_trivial (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) [Nonempty X] {i j : ι} (hij : i ≠ j) :
    ¬ PreconnectedSpace (FiniteEtaleOver.trivial.{u} ι X).left :=
  not_preconnectedSpace_sigma (fun _ : ι ↦ X) hij (Classical.arbitrary X) (Classical.arbitrary X)

/-- **A cover with a preconnected total space is not a trivial cover with two distinct sheets.**

The two statements above composed, and **the separation
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` cannot make**: at the punctured line
`OkaTest/FiniteEtaleOver.lean`'s `z ↦ z²` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` at a two-element index type both have
degree `2` — `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial` and that file's
`degree_sqOver` — so `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne` says
nothing about the pair. `OkaTest/FiniteEtaleOver.lean` instantiates this at exactly that pair.

**Nothing here is finite étale and nothing here is analytic.** Every step is topology — a clopen
image, a continuous surjection, and `isClopen_iff` — which is why the statement holds of any two
objects of `CategoryTheory.Over X` of these shapes and asks the property for nothing but the right
to say "cover".

**What it does not say.** A trivial cover with `Nat.card ι ≤ 1` is not covered, and correctly so:
at one sheet the fold map is an isomorphism
(`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId`) and the total space is `X` itself,
which may perfectly well be preconnected. The hypothesis is two *distinct* indices and there is no
weaker one. -/
theorem FiniteEtaleOver.isEmpty_iso_trivial_of_preconnectedSpace {X : AnalyticSpace.{u}}
    (A : FiniteEtaleOver.{u} X) [PreconnectedSpace A.left] (ι : Type u) [Finite ι] [Nonempty X]
    {i j : ι} (hij : i ≠ j) :
    IsEmpty (A ≅ FiniteEtaleOver.trivial.{u} ι X) :=
  FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace.{u}
    (FiniteEtaleOver.not_preconnectedSpace_trivial.{u} ι X hij)

/-! ### The restriction over `⊤` -/

/-- **A morphism whose restriction over `⊤` is finite étale is finite étale.**

`ComplexAnalytic.AnalyticSpace.restrictHom f V` has source `X|f⁻¹V` and target `Y|V`, so it is a
morphism between two *other* spaces and a property of it is not on its face a property of `f`. At
`V = ⊤` the two inclusions are isomorphisms
(`ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`) and
`ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top` exhibits `f` as the conjugate, so the
property transfers by `ComplexAnalytic.AnalyticSpace.isFiniteEtale`'s `RespectsIso` and
`IsMultiplicative` instances above. **Nothing is proved about finite étale morphisms here**: the
content is entirely in `Oka/AnalyticSpace/OpenSubspace.lean`, and this file supplies only the two
instances that make the conjugation a transfer.

**This is what makes a `V` hypothesis refutable rather than merely unproved.** A theorem of the
form *"restricted over `V` the morphism is finite étale"* says nothing on its own about whether
`V` can be `⊤`; with this, a morphism that is not finite étale gives
`¬ IsFiniteEtale (restrictHom f ⊤)` by contraposition, so such a theorem at `V = ⊤` would be
false. `OkaTest/StandardEtaleNotFinite.lean`'s `## What is not checked here` recorded the absence of
exactly this step — **at `IsFinite`, not here**; see the paragraph below.

**Nothing is said about `ComplexAnalytic.AnalyticSpace.IsLocalIso`.** The same conjugation would
run and no prose site asks for it, so it is declined rather than overlooked.

**The finiteness half of this is `ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top`**, in
the file that owns the vocabulary, and it is the one two `## What is not here` bullets elsewhere
were actually about — both name a *finiteness* theorem. It is not derived from this one and does
not derive it: `IsFinite` is not a `CategoryTheory.MorphismProperty` here, so it runs through
`ComplexAnalytic.AnalyticSpace.isFinite_comp` twice instead of through `RespectsIso`.

**What is not here is the converse.** `IsFiniteEtale f → IsFiniteEtale (restrictHom f ⊤)` follows
from the same conjugation read the other way and is not stated, because nothing asks for it; it is
the same three lines. Nor is anything said about `restrictHom f V` at a proper `V` — the whole
argument is that `⊤` makes the inclusions invertible, and at a proper `V` neither is. -/
theorem isFiniteEtale_of_restrictHom_top {A B : AnalyticSpace.{u}} (f : A ⟶ B)
    (hfe : IsFiniteEtale (restrictHom f (⊤ : B.Opens))) : IsFiniteEtale f := by
  set U : A.Opens := (TopologicalSpace.Opens.map f.toLRSHom.base).obj (⊤ : B.Opens) with hUdef
  have h : (U : Set A) = Set.univ := rfl
  have hB : ((⊤ : B.Opens) : Set B) = Set.univ := rfl
  haveI : IsIso (B.ofRestrict (⊤ : B.Opens)) := isIso_ofRestrict_of_eq_univ B ⊤ hB
  haveI : IsIso (liftTop A U h) := isIso_liftTop A U h
  have hp : isFiniteEtale.{u} (liftTop A U h ≫ restrictHom f ⊤ ≫ B.ofRestrict ⊤) :=
    (isFiniteEtale.{u}).comp_mem _ _ (isFiniteEtale_of_isIso _)
      ((isFiniteEtale.{u}).comp_mem _ _ hfe (isFiniteEtale_of_isIso _))
  rwa [liftTop_comp_restrictHom_top] at hp

/-! ### The fibre functor -/

/-- **The fibre of a cover over a point of the base**, as a type.

Spelled as the preimage set and not as the subtype `{a // A.hom.toLRSHom.base a = x}`. The two are
definitionally the same type — membership in `{x}` *is* that equation — and the preimage is the
spelling `Oka/AnalyticSpace/Degree.lean` states every fibre count in, which is what makes
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber` below the symmetric form of a theorem
there rather than a transport across an equivalence.

**Nothing finite étale is read here.** The definition mentions the structure map and nothing else,
so it would make sense at every object of `CategoryTheory.MorphismProperty.Over` whatever the
property is; what the property buys is the instance below and not the type. -/
def FiniteEtaleOver.fiber {X : AnalyticSpace.{u}} (x : X) (A : FiniteEtaleOver.{u} X) : Type u :=
  (A.hom.toLRSHom.base ⁻¹' {x} : Set A.left)

/-- **The fibre of a cover is finite, and nothing has to be assumed for that.**

Not a separation axiom, not connectedness, nothing about the base and nothing about the point.
`finite_fiber` is a *field* of `ComplexAnalytic.AnalyticSpace.IsFinite`
(`Oka/AnalyticSpace/Finite.lean`), `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` carries it through
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isFinite`, and an object of this category carries the
class in its `prop` field, so this is three projections and no proof.

**This corrects the pricing that stood in this file's `## What is not here` and is why the functor
below was not built earlier.** That bullet said the fibre of a finite étale morphism is finite *by*
`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, which asks `[T2Space]` of the
source. It is not: that theorem says two fibres have the **same** `Nat.card`, and `Nat.card` of an
infinite type is `0`, so it is satisfied by a morphism all of whose fibres are infinite and cannot
be where finiteness comes from — its own docstring says *"it does **not** say what that size is"*.
`[T2Space]` is the price of **constancy** of the count, through
`ComplexAnalytic.AnalyticSpace.nonempty_homeomorph_fiber_of_isFiniteEtale` and the covering-space
theory behind it, and constancy is not what a `FintypeCat`-valued functor asks of a fibre. -/
instance FiniteEtaleOver.finite_fiber {X : AnalyticSpace.{u}} (x : X) (A : FiniteEtaleOver.{u} X) :
    Finite (FiniteEtaleOver.fiber.{u} x A) :=
  (A.prop : IsFiniteEtale A.hom).isFinite.finite_fiber x

/-- **A morphism of covers carries the fibre over `x` into the fibre over `x`.**

The whole content is `CategoryTheory.MorphismProperty.Over.w f` — the triangle
`f.left ≫ B.hom = A.hom` — read at one point: if `a` lies over `x` for `A` then `f.left a` lies
over `x` for `B`, because the two structure maps agree along `f`.

**No property of `f` is used and none is available**, the category's second `⊤` being exactly the
statement that a morphism of covers carries no condition; the base map of a composite is the
composite of the base maps by `rfl`, which is what makes the two functor laws below `rfl` too. -/
def FiniteEtaleOver.fiberMap {X : AnalyticSpace.{u}} (x : X) {A B : FiniteEtaleOver.{u} X}
    (f : A ⟶ B) (a : FiniteEtaleOver.fiber.{u} x A) : FiniteEtaleOver.fiber.{u} x B :=
  ⟨f.left.toLRSHom.base a.1, by
    have hw : f.left ≫ B.hom = A.hom := MorphismProperty.Over.w f
    have h := congrArg (fun g ↦ (g.toLRSHom.base : A.left → X) a.1) hw
    exact h.trans a.2⟩

/-- **The fibre functor at a point of the base**, into `Type u`.

**The first functor out of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` declared in this
repository** — `CategoryTheory.MorphismProperty.Over.forget`, which the proofs above compose with,
is Mathlib's — and the first invariant here that is read on morphisms as well as on objects:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` is a number attached to an object and
preconnectedness of the total space is a proposition about one, while this carries every morphism
of covers to a map of finite sets.

**Both functor laws are `rfl`.** The underlying map of an identity of the comma category is the
identity and the underlying map of a composite is the composite, so there is nothing to prove and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap` is definitionally functorial.

**`TypeCat.ofHom` is not decoration.** A morphism of `Type u` in this Mathlib is a one-field
structure and not a function — `CategoryTheory.types` has `Hom := TypeCat.Hom` — so a bare
`fun a ↦ …` does not elaborate against `⟶` and the `map` field has to wrap it. -/
def FiniteEtaleOver.fiberFunctor {X : AnalyticSpace.{u}} (x : X) :
    FiniteEtaleOver.{u} X ⥤ Type u where
  obj A := FiniteEtaleOver.fiber.{u} x A
  map f := TypeCat.ofHom (FiniteEtaleOver.fiberMap.{u} x f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The fibre functor into `FintypeCat`**, which is the shape a Galois category asks for.

The same functor as
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor` with its values bundled with the
finiteness above; `Mathlib/CategoryTheory/Galois/Basic.lean` — whose namespace is not in this
repository's import closure and so cannot be cited by name here — asks for a functor into
`FintypeCat`, and this is one.

**It is computable, which is worth recording because the obvious expectation is otherwise.**
`FintypeCat.of` takes `[Finite X]` in this Mathlib and not `[Fintype X]`, so the instance above is
what it wants and no `Fintype.ofFinite` and no `noncomputable` appears.
**`Mathlib.CategoryTheory.FintypeCat` is the one import this file gains for it, and it costs one
module**: the transitive closure of this file was 3463 modules before and is 3464 after, the new
module being that one and nothing it depends on.

**What this does not make is a Galois category.** The axioms need base change and this repository
has no `CategoryTheory.Limits.HasPullback` instance for `ComplexAnalytic.AnalyticSpace`; see
`## What is not here`. -/
def FiniteEtaleOver.fintypeFiberFunctor {X : AnalyticSpace.{u}} (x : X) :
    FiniteEtaleOver.{u} X ⥤ FintypeCat.{u} where
  obj A := FintypeCat.of (FiniteEtaleOver.fiber.{u} x A)
  map f := FintypeCat.homMk (FiniteEtaleOver.fiberMap.{u} x f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Isomorphic covers have equinumerous fibres**, by an explicit equivalence.

`CategoryTheory.Functor.mapIso` at the fibre functor, read through `CategoryTheory.Iso.toEquiv`.
This is the equivalence behind the count in
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso`, which reaches the same
conclusion for `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` through
`ComplexAnalytic.AnalyticSpace.degree_isIso_comp` and without a fibre in sight; neither is derived
from the other and this one asks nothing of the total spaces. -/
def FiniteEtaleOver.fiberEquivOfIso {X : AnalyticSpace.{u}} (x : X) {A B : FiniteEtaleOver.{u} X}
    (e : A ≅ B) : FiniteEtaleOver.fiber.{u} x A ≃ FiniteEtaleOver.fiber.{u} x B :=
  ((FiniteEtaleOver.fiberFunctor.{u} x).mapIso e).toEquiv

/-- **The fibre functor computes the degree**, over a preconnected base and a Hausdorff total
space.

`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` (`Oka/AnalyticSpace/Degree.lean`) read at the
structure map of an object, which is why
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber` is spelled as a preimage: the two sides are
the same type on the nose and the proof is one `Eq.symm`.

**This is where `[T2Space]` genuinely enters**, and the contrast with
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber` above is the point: the fibre is
finite for free, and it is the statement that its size does not depend on the point that costs a
separation axiom on the source and preconnectedness of the base.

**The two `inferInstanceAs` lines are the comma category's and not this statement's.** In the type
of an object's structure map the total space appears through `CategoryTheory.Functor.id` and the
base through `CategoryTheory.Functor.fromPUnit`, applied to the two components of the object; both
are the space itself by `rfl` but **not reducibly so**, and instance search works up to reducible
unfolding, so the `[T2Space]` and `[PreconnectedSpace]` written above are not the instances
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` asks for until they are restated. That is
what the two `haveI`s do and there is no mathematical content in either. -/
theorem FiniteEtaleOver.card_fiber {X : AnalyticSpace.{u}} (A : FiniteEtaleOver.{u} X)
    [T2Space A.left] [PreconnectedSpace X] (x : X) :
    Nat.card (FiniteEtaleOver.fiber.{u} x A) = A.degree :=
  haveI : IsFiniteEtale A.hom := A.prop
  haveI : T2Space (((𝟭 AnalyticSpace.{u}).obj A.left : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (T2Space (A.left : Type u))
  haveI : PreconnectedSpace
      (((Functor.fromPUnit.{0} X).obj A.right : AnalyticSpace.{u}) : Type u) :=
    inferInstanceAs (PreconnectedSpace (X : Type u))
  (degree_eq_card_fiber A.hom x).symm

/-- **The fibre of the base over itself is a point.**

Stated as `Unique` rather than as a cardinality, so that it is the fibre functor's value and not a
count of it; `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_id` is the same fact read
through `Nat.card`, and it needs `[Nonempty X]` where this needs nothing — the point `x` is the
one that is there. -/
instance FiniteEtaleOver.uniqueFiberId {X : AnalyticSpace.{u}} (x : X) :
    Unique (FiniteEtaleOver.fiber.{u} x (FiniteEtaleOver.id.{u} X)) := by
  change Unique (((𝟙 X : X ⟶ X).toLRSHom.base : X → X) ⁻¹' {x} : Set X)
  have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = _root_.id := rfl
  rw [h, Set.preimage_id]
  infer_instance

/-- **The fibre of the trivial `ι`-sheeted cover is `ι`**, as an equivalence.

`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv` presents the fibre of a descent map as
`Σ i, (fibre of the i-th piece)` and every piece here is the identity, whose fibre is a point, so
`Equiv.sigmaUnique` collapses the sum. That is exactly the proof of
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` (`Oka/AnalyticSpace/SigmaFiniteEtale.lean`)
with the counting removed — **the equivalence is what that proof already had**, and that file's
`## The fibre is an equivalence and not a cardinality` section says so of itself.

`[Finite ι]` is here because `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` asks it in
order to be an object, and for no reason of this statement's own. -/
noncomputable def FiniteEtaleOver.fiberTrivialEquiv (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) (x : X) :
    FiniteEtaleOver.fiber.{u} x (FiniteEtaleOver.trivial.{u} ι X) ≃ ι :=
  haveI hu : ∀ _ : ι, Unique (((𝟙 X : X ⟶ X).toLRSHom.base ⁻¹' {x} : Set X)) := by
    intro _
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = _root_.id := rfl
    rw [h, Set.preimage_id]
    infer_instance
  (AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv (fun _ : ι ↦ X.toLocallyRingedSpace)
      (fun _ ↦ (𝟙 X : X ⟶ X).toLRSHom) x).symm.trans (@Equiv.sigmaUnique ι _ hu)

/-! ### The trivial cover at one sheet, where it is the base -/

/-- **The trivial cover at one sheet is the base over itself.**

The isomorphism the docstring of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial` said was
not stated. It is `ComplexAnalytic.AnalyticSpace.sigmaFoldIso`
(`Oka/AnalyticSpace/SigmaFiniteEtale.lean`) put over `X`: a morphism of this category is a
morphism of analytic spaces commuting with the two structure maps and nothing more — `Q` is `⊤`,
as the docstring above says — so the triangle is all there is to check, and it is
`Category.comp_id` at the identity structure map of
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id`.

**The triangle is a term and not a `simp`, for the reason
`ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id` gives above.** The goal displays as
`(sigmaFoldIso ι X).hom ≫ (FiniteEtaleOver.id X).hom = (FiniteEtaleOver.trivial ι X).hom`; both
`def`s have to be unfolded to see a `𝟙 X` and a `sigmaFold ι X`, which `rw` and `simp` do not do
at `instances` transparency, and `Category.comp_id _` is the same step at default transparency in
one line.

**`[Nonempty ι]` and `[Subsingleton ι]` and not `Nat.card ι = 1`**, which
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff` below converts for a
caller holding the numeral. The instances are what the construction consumes; a hypothesis it
would have to destructure is the wrong shape for a `def`, whose value would then depend on a
proof. -/
noncomputable def FiniteEtaleOver.trivialIsoId (ι : Type u) [Finite ι] [Nonempty ι]
    [Subsingleton ι] (X : AnalyticSpace.{u}) :
    FiniteEtaleOver.trivial.{u} ι X ≅ FiniteEtaleOver.id.{u} X :=
  MorphismProperty.Over.isoMk (sigmaFoldIso ι X) (Category.comp_id _)

/-- **So over a non-empty base the trivial cover is the base over itself exactly when its index
type has one point.**

The two directions are the two halves this file already had, joined:
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id` is the forward one and is
proved through the degree, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId` is the backward one and is proved
through the universal property of the disjoint union. **Neither direction is the other read
backwards**, and the degree cannot supply the backward one: it separates isomorphism classes and
never produces an isomorphism.

`[Nonempty X]` is where it is needed and not decorative — it is what
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_id` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial` ask for, the degree of a morphism
out of or into the empty space being `0` whatever the index type is. The backward direction needs
nothing of `X`.

**This is a classification of one isomorphism class and not of the category.** It says which
trivial covers are the identity; it says nothing about a non-trivial cover of degree `1`, and
`## What is not here` still records that no invariant here separates two *connected* covers. -/
theorem FiniteEtaleOver.nonempty_iso_trivial_id_iff (ι : Type u) [Finite ι]
    (X : AnalyticSpace.{u}) [Nonempty X] :
    Nonempty (FiniteEtaleOver.trivial.{u} ι X ≅ FiniteEtaleOver.id.{u} X) ↔ Nat.card ι = 1 := by
  refine ⟨fun he ↦ by_contra fun h ↦
    not_nonempty_iff.mpr (FiniteEtaleOver.isEmpty_iso_trivial_id ι X h) he, fun h ↦ ?_⟩
  obtain ⟨j, hj⟩ := Nat.card_eq_one_iff_exists.mp h
  haveI : Nonempty ι := ⟨j⟩
  haveI : Subsingleton ι := ⟨fun a b ↦ (hj a).trans (hj b).symm⟩
  exact ⟨FiniteEtaleOver.trivialIsoId ι X⟩

end ComplexAnalytic.AnalyticSpace

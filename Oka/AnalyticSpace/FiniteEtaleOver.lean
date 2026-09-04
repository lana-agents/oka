/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
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
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`: **the degree of a cover**, which is
  `ComplexAnalytic.AnalyticSpace.degree` of its structure map.

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
* **The degree on objects is here now, and what it does not do is separate a connected cover from
  a disconnected one.** This bullet said `ComplexAnalytic.AnalyticSpace.degree` is a function of a
  morphism and nothing below reads it off an object;
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree` does, and
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso` is what makes that well defined
  on isomorphism classes. **The invariant is coarse, and where that shows is recorded rather
  than hidden**: at the punctured line `OkaTest/FiniteEtaleOver.lean`'s `z ↦ z²` and the trivial
  two-sheeted cover both have degree `2`, so **nothing below can tell them apart**, and neither
  file claims they are non-isomorphic. The classical separation is by connectedness of the total
  space; `OkaTest/FiniteEtaleOver.lean` records which half of that this repository has and which
  it does not.
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
empty `ι`, where the cover is the empty space and the degree is `0`. -/
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

end ComplexAnalytic.AnalyticSpace

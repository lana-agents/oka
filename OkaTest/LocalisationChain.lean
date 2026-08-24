/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# A chain of three distinguished opens, as an actual diagram

`Oka/Analytification/LocalisationComposite.lean` proves the coherence triangle

    (localisationPresentationIsoMul g f f₁).hom ≫ localisationHom g (f₁ * f) =
      localisationHom (localisationPresentation g f) (rename (localisationIncl n) f₁) ≫
        localisationHom g f

and calls it a `trans_comp` law. **That is a claim about a diagram, and until this file there was
no diagram**: nobody had written down an index category and a functor out of it, so *"the shape
works"* was not yet a statement about anything. Grepping `⥤` over `Oka/Analytification/` and
`OkaTest/` before this file returns eleven occurrences — eight in a declaration's type, three in a
docstring — and **not one of them has a finite index category as its source**. Five name a functor
out of `ComplexAnalytic.Presentation`; two name one out of the opposite category of the
finite-type `ℂ`-algebras, `ComplexAnalytic.analytificationFGAlg` and
`ComplexAnalytic.toCommRingCatOp`; the remaining four name one out of a category of sheaves of
modules.

This file writes one down. The index category is the three-element chain `0 ⟶ 1 ⟶ 2`, which is
`Fin 3` with its own order, and the functor is
`OkaTest.LocalisationChain.chainFunctor`, which sends it to

    A_f localised at f₁   ⟶   A_f   ⟶   A .

`OkaTest.LocalisationChain.analyticChain` is its analytification, which is what makes the exercise
about analytic spaces rather than about algebra.

## Why a *chain*, and not the two-object poset that was originally asked for

`Mathlib/AlgebraicGeometry/Cover/Directed.lean` gives a locally directed cover six fields, and two
of them are what a test has to exercise: a `trans_comp` law and a `directed` law. **A two-object
index category can exercise neither.** With two objects there is at most one non-identity arrow,
so every composite has an identity on one side and `trans_comp` follows from `trans_id`; and
`directed` asks, for a point of an overlap `𝒰ᵢ ×_X 𝒰ⱼ`, for a *third* member below both, which two
members cannot supply unless one of them is below the other.

So the two laws want two different diagrams: `trans_comp` wants a **chain** of three, which is this
file, and `directed` wants a **span** of three, which is not — two arrows out of a common source,
because `directed` asks for a member *below* both. (This paragraph and the bullet in
`## What is not here` both said *cospan* until `OkaTest/ProjectiveLineSpan.lean` showed the word
was wrong; `CategoryTheory.Limits.cospan` is the shape with the two arrows the other way round,
and the correction is recorded here rather than made silently.) The span is the honest
re-expression of `ℙ¹`: `OkaTest/ProjectiveLine.lean` proves that the overlap is neither the whole
member nor empty (`ComplexAnalytic.localisationOpen_lineRel_ne_top` and
`ComplexAnalytic.localisationOpen_lineRel_ne_bot`), so the overlap is a third object and not
either member under another name. It is a separate test with disjoint content, and it is
`OkaTest/ProjectiveLineSpan.lean` and `OkaTest/ProjectiveLineDirected.lean`.

**That neither of the two members contains the other is a stronger statement**, it is what forces
`directed`'s third member to be a genuinely new object rather than one of the two, and the two
`localisationOpen` lemmas above do **not** prove it: they are about one member's open subset and
say nothing about the two members' images in the glued space. This paragraph asserted it and
attributed it to them until `OkaTest/ProjectiveLineDirected.lean` was written;
`OkaTest.ProjectiveLineDirected.not_range_ι_subset_range_ι` now proves it, from
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` and
`ComplexAnalytic.not_surjective_ι_projectiveLineGlueData`.

## The choice that makes this a test rather than a tautology

A functor out of a chain has to be given an image for the **composite** arrow `0 ⟶ 2`, and there
are two readings.

* Send it to the literal composite of the other two. Then `map_comp` is true by definition and the
  diagram says nothing.
* Send it to **the single localisation at the product**, which is what a cover indexed by *"is a
  distinguished open of"* actually hands you: the witness for a composite arrow is manufactured
  and is a third polynomial, neither of the two it is composed from. Then `map_comp` is a theorem,
  and the theorem is exactly the coherence triangle above.

**The second is taken here**, and `OkaTest.LocalisationChain.ofThree` is arranged so that the
choice is visible in the type: it takes the image of the composite arrow as an argument and the
functor law as a hypothesis, so there is nowhere for a definitional shortcut to hide.

## The answer, and it is a negative that was worth having

**No pseudo-functor is needed. The coherence isomorphism can sit on either arrow, and a strict
functor exists both ways.** Two are built here from the same helper:

* `OkaTest.LocalisationChain.chainFunctor` puts the doubly localised presentation at `0`, so the
  composite arrow's image is `localisationHom g (f₁ * f)` **read through**
  `ComplexAnalytic.localisationPresentationIsoMul`, and `map_comp` is the triangle verbatim.
* `OkaTest.LocalisationChain.productFunctor` puts the single localisation at `f₁ * f` there
  instead, so the composite arrow's image is `ComplexAnalytic.localisationHom g (f₁ * f)` **on the
  nose** — `OkaTest.LocalisationChain.productFunctor_map_zero_two` is `rfl` — and the isomorphism
  moves onto the arrow `0 ⟶ 1` instead, as
  `OkaTest.LocalisationChain.productTrans`.

The second is the shape a cover would produce and the first is the one whose objects cannot
degenerate; the difference between them is recorded below and is the reason both are here.

## What is not here

**The bridge to `ComplexAnalytic.coverGlueData`, which is the next issue and not this one.** The
gap is a shape mismatch and it is worth stating precisely, because it is what the next worker has
to close. `ComplexAnalytic.coverGlueData` takes `obj : J → ComplexAnalytic.Presentation`, a
polynomial `poly i j` **for each ordered pair**, an isomorphism `glue i j` for each ordered pair,
and `hrange`, `hsymm`, `hcocycle` quantified over pairs and triples of *indices*. A functor out of
a poset carries data on **arrows**, and an arrow `i ⟶ j` is a proposition — there is no `poly i j`
to read off it, and the diagram here supplies none. Going from one to the other means choosing,
for each ordered pair with an arrow between them, a witness polynomial. That is the choice
`ComplexAnalytic.localisationPresentationIsoOfDvdPow` controls — two witnesses each dividing a
power of the other give canonically isomorphic presentations — and it is not made anywhere yet.

**No `directed` law and no span**, for the reason above. Both are elsewhere:
`OkaTest/ProjectiveLineSpan.lean` is the diagram and `OkaTest/ProjectiveLineDirected.lean` is the
law, at `ℙ¹` in both cases.

**No analytic analogue of the `LocallyDirected` class.** This file is a single diagram, which is
what tells you whether such a class would have anything to quantify over; defining one is a design
decision and is not taken here. `OkaTest/ProjectiveLineDirected.lean` declines it too, and
measures what defining it would still be missing now that both laws have an instance.

**`OkaTest.LocalisationChain.ofThree` is not library API.** It is category theory with no analytic
content, so if it is ever wanted outside a test it belongs in the mirror tree and not in
`Oka/Analytification/`; nothing outside this file uses it, and it is here because the two functors
below differ only in their arguments to it.
-/

open CategoryTheory MvPolynomial ComplexAnalytic

universe v w u

namespace OkaTest.LocalisationChain

/-! ### A functor out of the three-element chain -/

/-- The three objects of a chain `0 ⟶ 1 ⟶ 2`, as a family indexed by `Fin 3`. No `Category`
instance is needed for the objects themselves, and the `unusedArguments` linter says so. -/
def ofThreeObj {C : Type v} (X₀ X₁ X₂ : C) : Fin 3 → C
  | ⟨0, _⟩ => X₀
  | ⟨1, _⟩ => X₁
  | ⟨2, _⟩ => X₂

/-- The morphisms of a chain `0 ⟶ 1 ⟶ 2`: the two consecutive arrows, the identities, and **a
chosen image `c` for the composite arrow `0 ⟶ 2`**, which is the datum this file exists to make
visible. The three pairs with no arrow between them are ruled out by the hypothesis. -/
def ofThreeMap {C : Type v} [Category.{w} C] {X₀ X₁ X₂ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₀ ⟶ X₂) :
    ∀ (i j : Fin 3), i ≤ j → (ofThreeObj X₀ X₁ X₂ i ⟶ ofThreeObj X₀ X₁ X₂ j)
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩, _ => a
  | ⟨0, _⟩, ⟨2, _⟩, _ => c
  | ⟨1, _⟩, ⟨1, _⟩, _ => 𝟙 _
  | ⟨1, _⟩, ⟨2, _⟩, _ => b
  | ⟨2, _⟩, ⟨2, _⟩, _ => 𝟙 _
  | ⟨1, _⟩, ⟨0, _⟩, h => absurd h (by simp)
  | ⟨2, _⟩, ⟨0, _⟩, h => absurd h (by simp)
  | ⟨2, _⟩, ⟨1, _⟩, h => absurd h (by simp)

/-- **A functor out of the three-element chain**, from two composable arrows and a chosen image
`c` for the composite arrow, together with the proof that the choice is compatible.

`h` is the whole content: it is `map_comp` at the single triple `0 ≤ 1 ≤ 2` that is not forced by
`map_id`, and every other case of `map_comp` has an identity on one side. Taking `c` as an
argument rather than defining it to be `a ≫ b` is what stops the functor law from being true by
definition. -/
def ofThree {C : Type v} [Category.{w} C] {X₀ X₁ X₂ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₀ ⟶ X₂) (h : c = a ≫ b) : Fin 3 ⥤ C where
  obj := ofThreeObj X₀ X₁ X₂
  map {i j} u := ofThreeMap a b c i j (leOfHom u)
  map_id i := by fin_cases i <;> rfl
  map_comp {i j l} u₁ u₂ := by
    have hij := leOfHom u₁
    have hjl := leOfHom u₂
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all [ofThreeMap]
    rfl

/-- **The composite arrow goes where it was told to go**, by definition and not up to anything.
The point of stating it is that the chosen `c` is what a consumer of the diagram reads off the
arrow `0 ⟶ 2`, so this is where the reading taken in the header becomes checkable. -/
theorem ofThree_map_zero_two {C : Type v} [Category.{w} C] {X₀ X₁ X₂ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₀ ⟶ X₂) (h : c = a ≫ b) :
    (ofThree a b c h).map (homOfLE (by simp : (0 : Fin 3) ≤ 2)) = c :=
  rfl

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f f₁ : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The chain of localisations, with the doubly localised presentation at the bottom -/

/-- **The chain `A_{f} localised at f₁ ⟶ A_f ⟶ A`, as a functor.**

The composite arrow is sent to `ComplexAnalytic.localisationHom g (f₁ * f)` — the single
localisation at the product, which is the witness a cover indexed by *"is a distinguished open
of"* manufactures — read through `ComplexAnalytic.localisationPresentationIsoMul`, which is the
only bridge between the two objects. `map_comp` is then
`ComplexAnalytic.localisationPresentationIsoMul_hom_comp` verbatim, and nothing else in the
functor is more than bookkeeping. -/
def chainFunctor : Fin 3 ⥤ Presentation.{u} :=
  ofThree (localisationHom.{u} (localisationPresentation.{u} g f)
      (MvPolynomial.rename (localisationIncl.{u} n) f₁))
    (localisationHom.{u} g f)
    ((localisationPresentationIsoMul.{u} g f f₁).hom ≫ localisationHom.{u} g (f₁ * f))
    (localisationPresentationIsoMul_hom_comp.{u} g f f₁)

/-- The image of the composite arrow under `OkaTest.LocalisationChain.chainFunctor`, spelled out.
-/
theorem chainFunctor_map_zero_two :
    (chainFunctor.{u} g f f₁).map (homOfLE (by simp : (0 : Fin 3) ≤ 2)) =
      (localisationPresentationIsoMul.{u} g f f₁).hom ≫ localisationHom.{u} g (f₁ * f) :=
  rfl

/-- **The three objects are pairwise distinct**, so no arrow of the diagram is an identity and the
chain does not collapse. The number of adjoined variables separates them: `n + 2`, `n + 1` and `n`.
It is the argument `OkaTest/LocalisationComposite.lean` makes, as `presentation_ne_mul`, for a
different pair of presentations.

Distinctness of the objects is **not** a claim that the arrows are not isomorphisms; two different
presentations can present isomorphic algebras, and nothing here rules that out. -/
theorem chainFunctor_obj_injective : Function.Injective (chainFunctor.{u} g f f₁).obj := by
  intro i j hij
  have h : ((chainFunctor.{u} g f f₁).obj i).n = ((chainFunctor.{u} g f f₁).obj j).n :=
    congrArg Presentation.n hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; simp only [chainFunctor, ofThree, ofThreeObj] at h; omega)

/-- **The analytification of the chain**: three complex analytic spaces and the two open
immersions between them, as a diagram.

This is one line because `ComplexAnalytic.analytificationFunctor` is a functor on the nose, and it
is the step that makes the exercise about analytic spaces. -/
def analyticChain : Fin 3 ⥤ AnalyticSpace.{u} :=
  chainFunctor.{u} g f f₁ ⋙ analytificationFunctor.{u}

/-! ### The same chain with the product presentation at the bottom -/

/-- **The transition `A_{f₁·f} ⟶ A_f`**, for the reading in which the bottom object of the chain
is the single localisation at the product rather than the double localisation.

There is no `ComplexAnalytic.localisationHom` of this shape — `f₁ * f` and `f` are two unrelated
polynomials in the same variables — so the transition has to be assembled, and
`ComplexAnalytic.localisationPresentationIsoMul` is what assembles it. -/
def productTrans :
    (⟨n + 1, k + 1, localisationPresentation.{u} g (f₁ * f)⟩ : Presentation.{u}) ⟶
      ⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ :=
  (localisationPresentationIsoMul.{u} g f f₁).inv ≫
    localisationHom.{u} (localisationPresentation.{u} g f)
      (MvPolynomial.rename (localisationIncl.{u} n) f₁)

/-- **The transition composes to the single localisation at the product**, on the nose.

The coherence triangle again, with the isomorphism moved from the composite arrow onto the first
one. That it comes out as an equation between morphisms rather than up to an isomorphism is the
reason `OkaTest.LocalisationChain.productFunctor` is a strict functor. -/
theorem productTrans_comp :
    productTrans.{u} g f f₁ ≫ localisationHom.{u} g f = localisationHom.{u} g (f₁ * f) := by
  rw [productTrans, Category.assoc, ← localisationPresentationIsoMul_hom_comp,
    Iso.inv_hom_id_assoc]

/-- **The chain again, with the single localisation at `f₁ · f` at the bottom.**

The composite arrow's image is now `ComplexAnalytic.localisationHom g (f₁ * f)` itself, with no
isomorphism in it, which is exactly the shape a cover hands over; the isomorphism has moved to the
arrow `0 ⟶ 1`. **This is a strict functor too**, which is the answer to whether the choice-first
shape needs a pseudo-functor: it does not. -/
def productFunctor : Fin 3 ⥤ Presentation.{u} :=
  ofThree (productTrans.{u} g f f₁) (localisationHom.{u} g f) (localisationHom.{u} g (f₁ * f))
    (productTrans_comp.{u} g f f₁).symm

/-- The composite arrow of `OkaTest.LocalisationChain.productFunctor` is the single localisation at
the product **on the nose**, which is the contrast with
`OkaTest.LocalisationChain.chainFunctor_map_zero_two`. -/
theorem productFunctor_map_zero_two :
    (productFunctor.{u} g f f₁).map (homOfLE (by simp : (0 : Fin 3) ≤ 2)) =
      localisationHom.{u} g (f₁ * f) :=
  rfl

/-- **And the price of that reading**: its bottom two objects can coincide, at `f₁ = 1`, where the
chain degenerates to a single arrow. So `OkaTest.LocalisationChain.productFunctor` has no analogue
of `OkaTest.LocalisationChain.chainFunctor_obj_injective`, and the two readings are not
interchangeable for a test — which is why both are here. -/
theorem productFunctor_obj_zero_eq_one :
    (productFunctor.{u} g f 1).obj 0 = (productFunctor.{u} g f 1).obj 1 :=
  congrArg (fun p ↦ (⟨n + 1, k + 1, localisationPresentation.{u} g p⟩ : Presentation.{u}))
    (one_mul f)

end

end OkaTest.LocalisationChain

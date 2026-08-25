/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.LocalisationChain

/-!
# The input shape of an ordered cover: the rigid reading is inconsistent, and the arity says so

`OkaTest/LocalisationChain.lean` writes down a chain of localisations as a functor and states, in
its `## What is not here`, the gap to `ComplexAnalytic.coverGlueData`: the glue data wants a
witness polynomial for each ordered pair of indices, a functor out of a poset carries data on
arrows, and an arrow of a poset is a proposition. Closing that gap means **choosing** a witness,
and the first question is what an ordered family of presentations may be assumed to look like.

**This file answers that question with a theorem rather than a preference.** The obvious reading —
that along each arrow the smaller member *is* the localisation of the larger — is not merely
inconvenient. It is **inconsistent as soon as the order has a chain of three**, and the argument is
the number of variables.

## The two readings

For `P : ComplexAnalytic.Presentation` and a witness `w`,
`OkaTest.LocalisationRigidity.localisationObj P w` is the presentation of the distinguished open
`D(w)`, on one more variable and one more relation. It is the shape
`ComplexAnalytic.coverOverlap` takes and the source of `ComplexAnalytic.localisationHom`.

* `OkaTest.LocalisationRigidity.IsRigid`: for every arrow `i < j` there is a witness `w` with
  `obj i = localisationObj (obj j) w`, **on the nose**.
* `OkaTest.LocalisationRigidity.IsRigidUpToIso`: the same with `≅` in place of `=`.

## The answer

`OkaTest.LocalisationRigidity.not_isRigid_of_lt_lt`: **no rigid family exists on an order with a
chain `i < j < l`.** Each arrow adds exactly one variable, so `(obj i).n` is `(obj l).n + 2`
through `j` and `(obj l).n + 1` directly, and the two arrows out of `i` disagree. The order is not
assumed to be anything beyond a `Preorder` and the presentations are arbitrary; the whole content
is `Presentation.n`.

The bound is sharp in both directions, which is what makes it a design answer rather than a
negative:

* **Two members are not enough to see it.** `OkaTest.LocalisationRigidity.isRigid_pairObj` builds a
  rigid family on `Fin 2` for any presentation and any witness, so the notion is satisfiable and
  the obstruction really does appear at three.
* **Three members are exactly enough, and the canonical three are an instance of the failure.**
  `OkaTest.LocalisationRigidity.not_isRigid_chainFunctor` says the objects of
  `OkaTest.LocalisationChain.chainFunctor` — the chain `A_f localised at f₁ ⟶ A_f ⟶ A`, which is
  the diagram this project already builds — admit no rigid reading, while
  `OkaTest.LocalisationRigidity.isRigidUpToIso_chainFunctor` says they do admit the relaxed one.

**The witness that makes the relaxed reading work on the composite arrow is `f₁ * f`, and the
isomorphism is `ComplexAnalytic.localisationPresentationIsoMul`** — the same lemma that supplies
`OkaTest.LocalisationChain.chainFunctor`'s `map_comp`. So the identification a cover has to
tolerate is one this repository already has, and it is needed for exactly the arrow that the arity
argument rules out: the other two arrows of that chain are rigid on the nose, and
`OkaTest.LocalisationRigidity.chainFunctor_obj_zero_ne_localisationObj` says the composite one is
not, at any witness.

That `Fin 2` and `Fin 3` behave differently here is worth putting beside the other place this
project has met the same boundary: `OkaTest/ProjectiveLine.lean` records that
`ComplexAnalytic.coverGlueData`'s `hcocycle` is **vacuous at two members**, and
`OkaTest/AffineCover.lean`'s three-member instance is the only place it has content. The two facts
are not the same and neither implies the other; what they share is that a two-member cover is the
wrong size to test anything about an ordered cover.

## What this says about the functor

An `Iso` in `ComplexAnalytic.Presentation` is a pair of `ComplexAnalytic.PresHom`s and does not act
on `MvPolynomial`, so once the identifications are isomorphisms rather than equations there is no
way to transport a witness along one. A `map_comp` law for a general index type therefore **cannot
be proved by unfolding**: the witness for `i < j` lives in `(obj j)`'s variables and the one for
`j < l` in `(obj l)`'s, and relating them would need `obj j` to be literally a localisation of
`obj l`.

**`not_isRigid_of_lt_lt` does not forbid that**, and the distinction is the whole of what it says.
What it forbids is the **conjunction** — every arrow of a chain being a one-step localisation *at
once*. A single arrow being one is not merely permitted, it is what the canonical chain does:
`OkaTest.LocalisationRigidity.chainFunctor_obj_one_eq_localisationObj` holds by `rfl`. So the
reason the identifications have to be isomorphisms is not the arity. It is that
`ComplexAnalytic.coverGlueData` asks for **one** witness polynomial per ordered pair, which forces
the composite arrow to be identified with a *single* localisation, and
`ComplexAnalytic.localisationPresentationIsoMul` is exactly that identification. The `## What is
not here` section below states the one-witness-per-pair demand; it is the premise, and the arity
theorem is what makes the identification non-trivial once the demand is granted.

**So the functor laws belong in the input, as fields, and not among the theorems about it.**
`OkaTest.LocalisationRigidity.ofPreorder` is what remains once they are: a functor out of a
preorder is an object family, a morphism for each comparable pair, and the two laws — and the
morphism may be given as a function of the *proof* `i ≤ j`, because proof irrelevance makes any
such function constant on it. `OkaTest.LocalisationChain.ofThree` is the `Fin 3` case of exactly
this, with the composite arrow's image taken as an argument and its law as a hypothesis, and the
two functors built from it are the worked instances.

## What is not here

**No `poly`, `glue`, `hrange`, `hsymm` or `hcocycle` for `ComplexAnalytic.coverGlueData`.** This
file is about the input shape, which is what has to be fixed before any of them can be produced,
and it deliberately stops there. Two things a reader should know before attempting them:

* a glue data's own diagram has **two levels of object** — members `U i` and overlaps `V (i, j)` —
  and its law is a cocycle on triple overlaps expressed with pullbacks. That is a different law on
  a different index shape from the `trans_comp` a chain exercises, so choosing witnesses does not
  turn one into the other and `hcocycle` should be expected **not** to follow;
* `ComplexAnalytic.coverGlueData` wants `poly i j` for **every** ordered pair, comparable or not,
  whereas everything here is indexed by arrows. Two indices with no arrow between them still have
  an overlap, and nothing in an ordered shape produces its witness.

**No claim that a general construction is impossible.** `not_isRigid_of_lt_lt` rules out one input
shape, the one an ordered cover invites; it says nothing about the relaxed shape, for which the
three-member instance below is positive evidence.

**And nothing about the *iterated* rigid reading, which is untried.** Everything here stipulates
**one** step per arrow, which is where the counting bites: `n` goes up by exactly one along each
arrow, so two routes round a chain disagree. Let the datum along an arrow be a finite *sequence* of
witnesses instead and the argument gives nothing — `(obj i).n - (obj j).n` is then a length rather
than a constant, and asking it to be additive along a chain is a condition one can simply meet.
The canonical chain already does, on the nose and with no isomorphism anywhere:
`OkaTest.LocalisationRigidity.chainFunctor_obj_zero_eq_localisationObj_localisationObj`. **This is
recorded as an alternative the file did not consider, not as a refutation of it** — the reason to
prefer the relaxed reading is `ComplexAnalytic.coverGlueData`'s one-witness-per-ordered-pair demand
below, which an iterated reading does not meet either, and nothing here is compiled beyond the two
equations named. A worker who wants the iterated notion has to define it.

**No new library API.** Nothing outside this file consumes any of it, and
`OkaTest.LocalisationChain.ofThree` is the precedent: category theory with no analytic content
stays in the test file until something wants it, and `Oka/Analytification/` is its home when
something does.

**Nothing about `ComplexAnalytic.localisationPresentationIsoOfDvdPow`.** Two witnesses each
dividing a power of the other give canonically isomorphic presentations, which is what makes a
*choice* of witness harmless; it is not what this file is about, since the failure here is of
arity and survives any choice.
-/

open CategoryTheory MvPolynomial ComplexAnalytic

universe v w u

namespace OkaTest.LocalisationRigidity

/-! ### A functor out of a preorder, which is `ofThree` with the index type freed -/

/-- **A functor out of a preorder**, from an object family, a morphism for each comparable pair,
and the two laws.

The morphism is given as a function of the *proof* that `i ≤ j`. That is not a weakening: an arrow
of a preorder is a proposition, so proof irrelevance makes any such function constant on it, and
there is correspondingly nothing a functor can carry that distinguishes two arrows `i ⟶ j`. It is
the reason a witness polynomial cannot be read off an arrow, which is the gap
`OkaTest/LocalisationChain.lean` states.

`OkaTest.LocalisationChain.ofThree` is the `Fin 3` case, with the two laws already reduced to the
single instance of `map_comp` that `map_id` does not force — its own docstring makes that
reduction — so it takes one hypothesis where this takes two. The point of stating the general form
is that **both laws are arguments at all**, which is where they have to be for an index type whose
identifications are isomorphisms. See the header. -/
def ofPreorder {J : Type*} [Preorder J] {C : Type v} [Category.{w} C] (obj : J → C)
    (map : ∀ i j : J, i ≤ j → (obj i ⟶ obj j))
    (hid : ∀ i, map i i le_rfl = 𝟙 (obj i))
    (hcomp : ∀ (i j l : J) (hij : i ≤ j) (hjl : j ≤ l),
      map i l (hij.trans hjl) = map i j hij ≫ map j l hjl) : J ⥤ C where
  obj := obj
  map {i j} u := map i j (leOfHom u)
  map_id i := hid i
  map_comp u₁ u₂ := hcomp _ _ _ (leOfHom u₁) (leOfHom u₂)

/-- The image of a comparable pair under `OkaTest.LocalisationRigidity.ofPreorder` is the morphism
it was given, by definition. Stated because it is what says the construction loses nothing. -/
theorem ofPreorder_map {J : Type*} [Preorder J] {C : Type v} [Category.{w} C] (obj : J → C)
    (map : ∀ i j : J, i ≤ j → (obj i ⟶ obj j)) (hid) (hcomp) {i j : J} (hij : i ≤ j) :
    (ofPreorder obj map hid hcomp).map (homOfLE hij) = map i j hij :=
  rfl

noncomputable section

/-! ### The two readings of an ordered family -/

/-- **The presentation of the distinguished open `D(w)` of `P`**: one more variable and one more
relation.

This is the shape `ComplexAnalytic.coverOverlap` takes for a member of a cover and its witness,
and it is the source of `ComplexAnalytic.localisationHom P.g w`. -/
def localisationObj (P : Presentation.{u}) (w : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    Presentation.{u} :=
  ⟨P.n + 1, P.k + 1, localisationPresentation.{u} P.g w⟩

/-- **No presentation is a one-step localisation of itself**, because the number of variables goes
up. One line, and it is the whole engine of this file: every other statement below is this
counting applied to a chain. -/
theorem ne_localisationObj_self (P : Presentation.{u})
    (w : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) : P ≠ localisationObj.{u} P w :=
  fun h ↦ by simpa [localisationObj] using congrArg Presentation.n h

variable {J : Type*} [Preorder J] (obj : J → Presentation.{u})

/-- **The rigid reading of an ordered family of presentations**: along every arrow, the smaller
member *is* the localisation of the larger at some witness, on the nose.

Stated on `<` rather than on `≤` because the reflexive case is already impossible —
`OkaTest.LocalisationRigidity.not_isRigid_le` — so a version on `≤` would be inconsistent for a
reason that has nothing to do with the one this file is about. -/
def IsRigid : Prop :=
  ∀ ⦃i j : J⦄, i < j → ∃ w, obj i = localisationObj.{u} (obj j) w

/-- **The relaxed reading**: the same up to isomorphism of presentations.

This is the shape a real cover has, and the isomorphism is not decoration — see
`OkaTest.LocalisationRigidity.isRigidUpToIso_chainFunctor`, where the composite arrow of the
canonical chain needs `ComplexAnalytic.localisationPresentationIsoMul` and nothing weaker. -/
def IsRigidUpToIso : Prop :=
  ∀ ⦃i j : J⦄, i < j → ∃ w, Nonempty (obj i ≅ localisationObj.{u} (obj j) w)

/-- The rigid reading implies the relaxed one, by `CategoryTheory.eqToIso`.

**Nothing below consumes this**, and it is here because the two readings are stated side by side
and a reader is entitled to see which way the implication runs. Said explicitly because the rest of
this file justifies each declaration by what reads it. -/
theorem isRigidUpToIso_of_isRigid (h : IsRigid.{u} obj) : IsRigidUpToIso.{u} obj :=
  fun _ _ hij ↦ (h hij).imp fun _ e ↦ ⟨eqToIso e⟩

/-- **The reflexive version of the rigid reading is inconsistent on any inhabited index type**,
by `OkaTest.LocalisationRigidity.ne_localisationObj_self` at the identity arrow.

This is why `OkaTest.LocalisationRigidity.IsRigid` quantifies over `<`. It is also the formal
version of *"an arrow carries no witness"*: the identity is an arrow, and there is no witness it
could be carrying.

**The name mentions `IsRigid` and the statement does not**, because there is no `≤`-quantified
predicate to name — this is the whole reason there is no such predicate, so defining one in order
to refute it would be a definition with exactly one use. The hypothesis is written out instead. -/
theorem not_isRigid_le (i : J)
    (h : ∀ ⦃a b : J⦄, a ≤ b → ∃ w, obj a = localisationObj.{u} (obj b) w) : False := by
  obtain ⟨w, hw⟩ := h (le_refl i)
  exact ne_localisationObj_self.{u} (obj i) w hw

/-- **No rigid family exists on an order with a chain of three.**

The two routes from `i` to `l` count differently: through `j` the number of variables goes up
twice, and along the arrow `i < l` it goes up once. Nothing about the presentations or about the
order is used beyond `ComplexAnalytic.Presentation.n` and transitivity of `<`.

This is the theorem the design question turns on. The order of a rigid family therefore has **no
chain of three members at all** — its chains have at most two — which no ordered cover of interest
satisfies.

**What it does not say**, and the header says why: that no *single* identification can be an
equation. It rules out having them all at once, one step each. That the identifications must be
isomorphisms follows from `ComplexAnalytic.coverGlueData` asking for one witness per ordered pair,
not from this counting. -/
theorem not_isRigid_of_lt_lt (h : IsRigid.{u} obj) {i j l : J} (hij : i < j) (hjl : j < l) :
    False := by
  obtain ⟨_, e₁⟩ := h hij
  obtain ⟨_, e₂⟩ := h hjl
  obtain ⟨_, e₃⟩ := h (hij.trans hjl)
  have h₁ : (obj i).n = (obj j).n + 1 := congrArg Presentation.n e₁
  have h₂ : (obj j).n = (obj l).n + 1 := congrArg Presentation.n e₂
  have h₃ : (obj i).n = (obj l).n + 1 := congrArg Presentation.n e₃
  omega

/-! ### Two members are not enough to see it -/

/-- A two-member ordered family: the distinguished open `D(w)` of `P` below `P`. -/
def pairObj (P : Presentation.{u}) (w : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    Fin 2 → Presentation.{u}
  | ⟨0, _⟩ => localisationObj.{u} P w
  | ⟨1, _⟩ => P

/-- **The rigid reading is satisfiable at two members**, for every presentation and every witness.

So `OkaTest.LocalisationRigidity.not_isRigid_of_lt_lt` is not the observation that the notion is
empty: it is sharp, and the obstruction appears exactly when a third member goes below. A
two-member instance therefore proves nothing about an ordered cover — which is the same size
warning `OkaTest/ProjectiveLine.lean` records for `ComplexAnalytic.coverGlueData`'s `hcocycle`, for
a different reason. -/
theorem isRigid_pairObj (P : Presentation.{u}) (w : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    IsRigid.{u} (pairObj.{u} P w) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact ⟨w, rfl⟩
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

/-! ### The canonical chain of three: relaxed yes, rigid no -/

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f f₁ : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The objects of `OkaTest.LocalisationChain.chainFunctor` admit the relaxed reading.**

Two of the three arrows are rigid — the chain is built out of `ComplexAnalytic.localisationHom`,
so consecutive members are localisations on the nose and the isomorphism is `Iso.refl`. **The
composite arrow is the one that needs either a second witness or an isomorphism**; taking the
isomorphism, its witness is the product `f₁ * f` and the identification is
`ComplexAnalytic.localisationPresentationIsoMul` — the same one that supplies that functor's
`map_comp`. So the relaxed reading costs exactly one identification and it is already on `master`.

**The two really are alternatives**, and the other one is an equation:
`OkaTest.LocalisationRigidity.chainFunctor_obj_zero_eq_localisationObj_localisationObj` says the
bottom object is the localisation of the top *twice*, on the nose. What picks the isomorphism over
the second witness is `ComplexAnalytic.coverGlueData`'s demand of one witness per ordered pair, not
anything about this chain. -/
theorem isRigidUpToIso_chainFunctor :
    IsRigidUpToIso.{u} (OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact ⟨MvPolynomial.rename (localisationIncl.{u} n) f₁, ⟨Iso.refl _⟩⟩
  · exact ⟨f₁ * f, ⟨localisationPresentationIsoMul.{u} g f f₁⟩⟩
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact ⟨f, ⟨Iso.refl _⟩⟩
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

/-- **The composite arrow is a one-step localisation of the top object at no witness at all**, and
not merely one whose proof happened to use an isomorphism: again by arity, `n + 2` against `n + 1`.

Taken with the two `Iso.refl`s in the proof above, this locates the failure exactly. It is what
`OkaTest.LocalisationRigidity.not_isRigid_chainFunctor` says globally, at the single arrow
responsible.

**`one-step` is doing work in that sentence and is not a hedge.** The bottom object *is* a
two-step localisation of the top on the nose —
`OkaTest.LocalisationRigidity.chainFunctor_obj_zero_eq_localisationObj_localisationObj` — so what
this refutes is the stipulation `OkaTest.LocalisationRigidity.IsRigid` makes, one step per arrow,
and not the idea that the composite arrow carries an equation. -/
theorem chainFunctor_obj_zero_ne_localisationObj
    (w : MvPolynomial (ULift.{u} (Fin ((OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj
      2).n)) ℂ) :
    (OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj 0 ≠
      localisationObj.{u} ((OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj 2) w :=
  fun h ↦ by
    have hn := congrArg Presentation.n h
    simp only [OkaTest.LocalisationChain.chainFunctor, OkaTest.LocalisationChain.ofThree,
      OkaTest.LocalisationChain.ofThreeObj, localisationObj] at hn
    omega

/-- **The middle object of the chain is the localisation of the top one at `f`, on the nose.**

This is the positive half of the header's correction, and it is the reason
`OkaTest.LocalisationRigidity.isRigidUpToIso_chainFunctor` can discharge that arrow with
`Iso.refl`. It is stated as a theorem because the file's standard is that a design claim gets one:
*a single arrow may be an equation* is a claim about what
`OkaTest.LocalisationRigidity.not_isRigid_of_lt_lt` does **not** forbid, and a sentence asserting
it would be exactly the species of unchecked prose this repository is auditing itself for. -/
theorem chainFunctor_obj_one_eq_localisationObj :
    (OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj 1 =
      localisationObj.{u} ((OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj 2) f :=
  rfl

/-- **The bottom object is the localisation of the top one twice, on the nose**, at `f` and then at
`f₁` renamed along `ComplexAnalytic.localisationIncl`.

The counterpart of `OkaTest.LocalisationRigidity.chainFunctor_obj_zero_ne_localisationObj`, which
says the same pair is not a **one-step** localisation at any witness. Together they say that what
the composite arrow refuses is the stipulation of one step per arrow, and not an equation as such —
the iterated reading the header's `## What is not here` names is satisfied here with no isomorphism
at all, which is why that section calls it untried rather than ruled out. -/
theorem chainFunctor_obj_zero_eq_localisationObj_localisationObj :
    (OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj 0 =
      localisationObj.{u}
        (localisationObj.{u} ((OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj 2) f)
        (MvPolynomial.rename (localisationIncl.{u} n) f₁) :=
  rfl

/-- **The same objects admit no rigid reading**, for every `g`, `f` and `f₁`.

`OkaTest.LocalisationRigidity.not_isRigid_of_lt_lt` at `0 < 1 < 2`. Taken with
`OkaTest.LocalisationRigidity.isRigidUpToIso_chainFunctor` this is the whole design answer on one
diagram: the relaxed reading holds and the rigid one is refuted, at the smallest chain that can
tell them apart, and the difference between them is a single named isomorphism. -/
theorem not_isRigid_chainFunctor :
    ¬ IsRigid.{u} (OkaTest.LocalisationChain.chainFunctor.{u} g f f₁).obj :=
  fun h ↦ not_isRigid_of_lt_lt _ h (by decide : (0 : Fin 3) < 1) (by decide : (1 : Fin 3) < 2)

end

end OkaTest.LocalisationRigidity

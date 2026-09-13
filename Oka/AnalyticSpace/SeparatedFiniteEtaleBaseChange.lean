/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.FiniteEtaleBaseChange
import Oka.AnalyticSpace.PullbackReduction
import Oka.AnalyticSpace.SeparatedFiniteEtale

/-!
# Base change of separated covers along a morphism of the base

`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` base-changes **one** finite étale morphism with
Hausdorff source along **one** morphism of the base, and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale` carries the class
across that one square. This file makes the construction a **functor**

    ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver X ⥤
      ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver X'

for `f : X' ⟶ X` and `[T2Space X]`, by supplying the one statement that was missing — that the
base change of a **separated** morphism is separated — and by reading the functoriality off
Mathlib.

**Every statement of this file is about the category of covers separated over the base**, which is
the category the `PreGaloisCategory` ladder of this repository is being built at; that class's
namespace is not in this repository's import closure, so the bare form is written here rather than
the dotted one, which is the spelling `Oka/AnalyticSpace/SeparatedFiniteEtale.lean` uses and for
the reason that file gives. **That is a run and not a convention**: at the commit that adds this
module, `#check` at the dotted name in a file importing `Oka` reports an unknown identifier, which
is the same instrument `Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` records for the same
claim.

## The separatedness half is Mathlib's, read at this tree's morphism property

`Mathlib/Topology/SeparatedMap.lean:106`, at the revision `lakefile.toml` pins (`v4.32.0`), is

```lean
open Function.Pullback in
theorem IsSeparatedMap.pullback {f : X → Y} (sep : IsSeparatedMap f) (g : A → Y) :
    IsSeparatedMap (@snd X Y A f g)
```

and `ComplexAnalytic.AnalyticSpace.base_baseChangeSnd` is **`rfl`**: the carrier of
`ComplexAnalytic.AnalyticSpace.baseChange` *is* `Function.Pullback` of the two base maps and its
projection *is* `Function.Pullback.snd`. So
`ComplexAnalytic.AnalyticSpace.isSeparatedMap_baseChangeSnd` below is that theorem applied and
nothing else — no transport, no topology of its own, and no hypothesis beyond the ones
`ComplexAnalytic.AnalyticSpace.baseChange` already carries.

**What is new is the class and not the identification.** That the base map is
`Function.Pullback.snd` is consumed already — `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`
pins base maps with it and `Oka/AnalyticSpace/MonoDirectSummand.lean` reads a point of the
self-product through it. **What no declaration of this repository stated before this file is that
a base change is separated**, and that is two measurements and not an account of what this tree's
separatedness statements are about.

**First, the declarations named after separatedness.** At `168ff30`, the commit this module is cut
from, `git grep -nE '^(theorem|lemma|def|instance|abbrev)' -- 'Oka/'` filtered on the token
`isSeparatedMap` returns **twenty-two header lines in three files** — ten in
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean`, eleven in `Oka/AnalyticSpace/SeparatedOver.lean`,
one in `Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`; eighteen named and four
anonymous `CategoryTheory.MorphismProperty` closure instances. **Not one of the twenty-two has a
fibre product, a base change or a pullback projection anywhere in its statement**, which is a
reading of the twenty-two statements the grep points at, one by one, and not a second grep. **The
filter is case-sensitive and both spellings of separatedness reach it through the header line**:
in the eighteen through the declaration name, and in the four anonymous instances through the
morphism property `ComplexAnalytic.AnalyticSpace.isSeparatedMap` written into the type. **That the
filter is on the header and not on either spelling is what makes it the right one here**: this
tree says *separated* in two ways — the morphism property, and Mathlib's `IsSeparatedMap` at a
morphism's base map, with `ComplexAnalytic.AnalyticSpace.isSeparatedMap_iff` the statement that
they agree — and the header filter is the one whose output is a set of declarations, which is what
a reading one by one needs. **It is not the wider instrument, and neither spelling-keyed grep sits
inside it.** At that commit `isSeparatedMap.{` matches eight lines under `Oka/`, and
`IsSeparatedMap` written with a root-namespace prefix four, both sets lying entirely inside
`Oka/AnalyticSpace/SeparatedFiniteEtale.lean`. Against the twenty-two, on `file:line` keys,
`comm -23` returns **all four** of the root-prefixed set and **four** of the eight: the
root-prefixed set is **disjoint** from the twenty-two, each of its hits being a continuation line
of a declaration whose header is among them — `:197` under `:196`, `:205` under `:204`, `:259`
under `:258`, `:358` under `:357` — and the four `isSeparatedMap.{` hits that fall outside,
`:205`, `:229`, `:246` and `:318`, are continuation or body lines in the same way. **Read at
declarations rather than at lines, the root-prefixed grep owns four and all four are among the
twenty-two, while `isSeparatedMap.{` owns eight of which seven are.** The one that is not is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver` itself, declared at `:245` with no
`isSeparatedMap` in its header and with the property in its body, which for an `abbrev` is its
statement: it is the `CategoryTheory.MorphismProperty.Over` of the meet of
`ComplexAnalytic.AnalyticSpace.isFiniteEtale` and `ComplexAnalytic.AnalyticSpace.isSeparatedMap`,
at `⊤` and at the base. **So the header filter has another blind spot
beside the one the paragraph opening *Second, and this is what that grep cannot see* is
about** — a declaration naming the property in its body rather than in its header — and **the
live case is the category this module's functor goes between**. Its statement carries no fibre
product, no base change and no pullback projection either, so the sentence opening *Not one of
the twenty-two* holds of twenty-three declarations and not only of the twenty-two the header
filter returns; I read it with them.

**Second, and this is what that grep cannot see, because it selects on the header line.** A `def`
can assert separatedness without saying so in its header, by discharging it as a field of the
object it builds. **Two on `master` do it for a base change, and they are the only two sites under
`Oka/` at which Mathlib's `IsSeparatedMap.pullback` is applied at all** — which is what bounds the
claim, that theorem being the only route from separatedness of a leg to separatedness of the
projection: the instrument is
`git grep -nE '\.pullback\b' -- 'Oka/'` at that commit, whose every hit I read, and exactly two of
them are applications of that theorem. Both apply it at
`ComplexAnalytic.AnalyticSpace.baseChangeSnd`:
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.selfProd`
(`Oka/AnalyticSpace/SeparatedFiniteEtale.lean:372`, the application at `:379`) and
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd`
(`Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean:240`, the application at `:246`), each written
`((isSeparatedMap_left i).pullback _).comp …`. **So the step is not new and only the name for it
is**: neither `def` states anything, both spend the same identification
`ComplexAnalytic.AnalyticSpace.base_baseChangeSnd` records — which is what lets Mathlib's theorem
land on a base map without transport — and
`ComplexAnalytic.AnalyticSpace.isSeparatedMap_baseChangeSnd` below is a name for a step this tree
has performed twice without one. **Having the name is what makes the functor's separatedness
obligation a single term** rather than the two-step `IsSeparatedMap.pullback`-then-`comp` those
two `def`s each write out.

**Both measurements above were first taken at `003e38f` and are re-derived at `168ff30` after a
re-cut rather than carried across it.** Ten commits separate the two bases and **four** of them
touch a file under `Oka/` — `Oka/AnalyticSpace/CoveringSpace.lean`,
`Oka/Topology/Covering/Basic.lean`, `Oka/Topology/IsLocalHomeomorph.lean` and
`Oka/Topology/Maps/Proper/Basic.lean`, by `git diff --name-only 003e38f 168ff30 -- 'Oka/'` — and
**none of the three files the twenty-two live in is among them**, which is why every figure, every
file split, every `comm` answer and every line number above is the same at the two commits. The
`.pullback` sweep is re-run too: **239** hits under `Oka/` at each of the two bases, the same two
of them applications of `IsSeparatedMap.pullback`, at the same two lines. **Nothing here is a
figure carried from a commit this module is no longer cut from.**

## The functoriality is free, and it is the *general* fibre product that makes it so

`CategoryTheory.Over.pullback` (`Mathlib/CategoryTheory/Comma/Over/Pullback.lean:63`) is the
functor `Over X ⥤ Over X'` induced by `f`, and it asks for
`CategoryTheory.Limits.HasPullbacksAlong f` — a fibre product at **every** cospan whose second leg
is `f`, with the first leg arbitrary. `ComplexAnalytic.AnalyticSpace.hasPullback_of_isFiniteEtale`
does not discharge that, and the failure is not a matter of unfolding: in a file importing
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and `Oka/AnalyticSpace/SeparatedFiniteEtale.lean`
and not `Oka/AnalyticSpace/PullbackReduction.lean`, asking for that functor is

```
failed to synthesize instance of type class
  Limits.HasPullbacksAlong g
```

— my own planted run. What discharges it is
`ComplexAnalytic.AnalyticSpace.hasPullbacks` (`Oka/AnalyticSpace/PullbackReduction.lean:268`), the
instance for a **general** cospan of analytic spaces, and the third import of this file is there
for that and for nothing else. **So this file is a consumer of that instance inside the covers**,
which is what makes the route available at all.

With it, `CategoryTheory.MorphismProperty.Comma.lift`
(`Mathlib/CategoryTheory/MorphismProperty/Comma.lean:360`) lifts that functor into the subcategory
cut out by the pair of morphism properties, and **`Functor.map_id` and `Functor.map_comp` are not
proof obligations of this file at all**: what `CategoryTheory.MorphismProperty.Comma.lift` asks for
is that each object's structure morphism is in the property — the two statements below — and that
each mapped morphism is in the morphism property of the comma category, which is `⊤` on both sides
here, exactly as `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver`'s own definition records.

## The one line the comma category costs

`CategoryTheory.MorphismProperty.Over`'s objects carry their structure morphism with the two
functors of the comma category still written, so `[T2Space A.left]` is **not** found for the
hypothesis of `ComplexAnalytic.AnalyticSpace.baseChange`. Planted and read back:

```
failed to synthesize instance of type class
  T2Space ↑↑((𝟭 AnalyticSpace).obj A.left).toPresheafedSpace
```

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` is stated at
`(A.left : Type u)`; the goal elaborates at the image of `A.left` under the identity functor. The
two are definitionally equal and instance search does not see it, so one `haveI` at the wrapped
spelling is written into the construction below. **It is not exported as an instance**: it is
needed in one lambda, and an instance keyed on the identity functor's value would be carried by
every later file for the sake of that lambda.

## Where `[T2Space X]` is spent

**In one place**, and it is the same place
`Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` spends the first of its two:
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` gives `[T2Space A.left]`,
which `ComplexAnalytic.AnalyticSpace.baseChange` asks of the source of its finite étale leg and
which `Oka/AnalyticSpace/CoveringMap.lean` records as not removable there. Nothing below asks
anything of `X'`, and the target category is formed with no hypothesis on its base — the
separatedness of the base-changed structure morphism comes from the object's own and not from a
separation axiom on `X'`.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.baseChangeFunctor`: **the base change
  functor between the categories of separated covers**, over a Hausdorff base.

## Main results

- `ComplexAnalytic.AnalyticSpace.isSeparatedMap_baseChangeSnd`: **the base change of a separated
  morphism is separated**, at the `ComplexAnalytic.AnalyticSpace.baseChangeSnd` spelling.
- `ComplexAnalytic.AnalyticSpace.isSeparatedMap_pullback_snd_of_isSeparatedMap`: **and at the
  `CategoryTheory.Limits.pullback.snd` spelling**, which is the one the functor consumes.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.baseChangeFunctor_obj_left` and
  `…SeparatedFiniteEtaleOver.baseChangeFunctor_obj_hom`: **the functor's value is the ambient
  fibre product with its second projection**, both `rfl`, so a reader need not unfold the lift.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.baseChangeFunctor_map_left_fst` and
  `…SeparatedFiniteEtaleOver.baseChangeFunctor_map_left_snd`: **the two triangles of a mapped
  morphism**.

## What is not here

* **This is not `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` for
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale`, and the bullets recording that absence are not
  narrowed.** That class quantifies over cospans whose finite étale leg may have a non-Hausdorff
  source, and `ComplexAnalytic.AnalyticSpace.doubledLineOver` is the standing witness that such a
  cospan exists. Every object below is an object of a category whose total spaces are Hausdorff by
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left`. The bullets in
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and `Oka/AnalyticSpace/FiniteEtaleOver.lean` say
  what they said before this file existed.
* **No `PreGaloisCategory` instance and no `FiberFunctor` one.** Neither class is in this
  repository's import closure at the commit that adds this module, by the `#check` the section
  opening *Every statement of this file* records, so neither can be cited by name in a statement
  here; and base change is not a field of either. What this file bears on is the shape in which
  those axioms are usually stated and not on any field of them.
* **No adjunction.** `CategoryTheory.Over.mapPullbackAdj` is Mathlib's adjunction between
  `CategoryTheory.Over.map` and `CategoryTheory.Over.pullback`; its left adjoint sends an object
  over `X'` to one over `X` by composition, and nothing here says that composition keeps a
  separated cover a separated cover — the composite of two finite étale morphisms is finite étale,
  but `f` is an arbitrary morphism of analytic spaces. **The statement is missing and so is the
  mathematics of one half of it**, and a push that wants the adjunction owes both.
* **Nothing identifying `baseChangeFunctor (𝟙 X)` with the identity, and no composition law.**
  `CategoryTheory.Over.pullbackId` and `CategoryTheory.Over.pullbackComp` are the ambient
  statements; neither is read through the lift here, and a functor's value is what this file
  states rather than how it composes.
* **No comparison with the fibre product of this category.**
  `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.fibreProd` of
  `Oka/AnalyticSpace/SeparatedFiniteEtaleLimits.lean` base-changes an object of this category
  along a morphism **of this category**, over a base that does not move; this functor moves the
  base and lands in a different category. **The two modules are siblings** — neither imports the
  other — and no statement below reads one of that file's declarations.
* **Nothing about the fibres or the degree.** The object is the ambient fibre product, whose
  carrier is `Function.Pullback` and whose fibres correspond by `Function.Pullback.fst`; no
  statement below mentions `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`.
* **The functor is not shown faithful, full or conservative**, and nothing below bears on the
  fibre functor `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor` or on the
  factorisation of it through a base change.
* **Nothing in this repository consumes this file at the commit that adds it**, which is the shape
  `OkaTest/Axioms.lean` asks a module to declare rather than leave to a reader: no module imports
  it but `Oka.lean` and its guards in `OkaTest/Axioms/Morphisms.lean`. What consumes it next is a
  fibre functor stated as a base change to a point, and the functoriality of the fibre of a cover
  in the base — neither of which exists here.
-/

open CategoryTheory Topology TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

variable {E B B' : AnalyticSpace.{u}} (q : E ⟶ B) (f : B' ⟶ B) [IsFiniteEtale q]
  [T2Space (E : Type u)]

/-! ### The base change of a separated morphism -/

/-- **The base change of a separated morphism is separated.**

`IsSeparatedMap.pullback` at the base maps, and it applies on the nose because
`ComplexAnalytic.AnalyticSpace.base_baseChangeSnd` is `rfl`: the base map of
`ComplexAnalytic.AnalyticSpace.baseChangeSnd` *is* `Function.Pullback.snd` at the two base maps.
**Nothing is asked of `B'`** — the separatedness of the base change is the separatedness of `q`
transported along the projection, and a separation axiom on the new base plays no part. -/
theorem isSeparatedMap_baseChangeSnd (hq : isSeparatedMap.{u} q) :
    isSeparatedMap.{u} (baseChangeSnd q f) :=
  hq.pullback _

/-- **The same in the `CategoryTheory.Limits.pullback` spelling.**

The two objects differ by `CategoryTheory.IsPullback.isoPullback` and separatedness crosses it
because an isomorphism of analytic spaces is injective on points, by
`ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso`, and because `IsSeparatedMap` is stable
under composition. **This is the spelling
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.baseChangeFunctor` consumes**, since
`CategoryTheory.Over.pullback` is written with `CategoryTheory.Limits.pullback.snd`. -/
theorem isSeparatedMap_pullback_snd_of_isSeparatedMap (hq : isSeparatedMap.{u} q) :
    isSeparatedMap.{u} (Limits.pullback.snd q f) := by
  rw [← (isPullback_baseChange q f).isoPullback_inv_snd]
  exact MorphismProperty.comp_mem _ _ _
    ((bijective_base_of_isIso (isPullback_baseChange q f).isoPullback.inv).injective.isSeparatedMap)
    (isSeparatedMap_baseChangeSnd q f hq)

namespace SeparatedFiniteEtaleOver

variable {X X' : AnalyticSpace.{u}} [T2Space (X : Type u)] (g : X' ⟶ X)

/-! ### The functor -/

/-- **Base change along a morphism of the base, as a functor of separated covers.**

`CategoryTheory.Over.pullback` composed with the forgetful functor of the comma category, lifted
back into it by `CategoryTheory.MorphismProperty.Comma.lift`. The two proof obligations of that
lift are the object's pair — that the second projection is finite étale, by
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale`, and that it is
separated, by `ComplexAnalytic.AnalyticSpace.isSeparatedMap_pullback_snd_of_isSeparatedMap` — and
the two morphism conditions, which are `⊤` on both sides and are discharged by the anonymous
constructor.

**`CategoryTheory.Functor.map_id` and `CategoryTheory.Functor.map_comp` are not proved here**:
they are the ambient functor's, and the lift does not restate them.

**The `haveI` is load-bearing**, for the reason the head of this file quotes an error for: the
`[T2Space]` hypothesis is asked at the image of `A.left` under the identity functor of the comma
category, where `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.t2Space_left` is stated at
`A.left` itself. -/
def baseChangeFunctor :
    SeparatedFiniteEtaleOver.{u} X ⥤ SeparatedFiniteEtaleOver.{u} X' :=
  MorphismProperty.Comma.lift
    (MorphismProperty.Over.forget _ _ X ⋙ CategoryTheory.Over.pullback g)
    (fun A ↦
      haveI := A.isFiniteEtale_hom
      haveI : T2Space ((((𝟭 AnalyticSpace.{u}).obj A.left) : AnalyticSpace.{u}) : Type u) :=
        t2Space_left A
      ⟨isFiniteEtale_pullback_snd_of_isFiniteEtale A.hom g,
        isSeparatedMap_pullback_snd_of_isSeparatedMap A.hom g A.isSeparatedMap_hom⟩)
    (fun _ ↦ ⟨⟩) (fun _ ↦ ⟨⟩)

variable (A : SeparatedFiniteEtaleOver.{u} X)

/-- **The total space of the base change is the ambient fibre product**, on the nose. -/
@[simp]
theorem baseChangeFunctor_obj_left :
    ((baseChangeFunctor g).obj A).left = Limits.pullback A.hom g :=
  rfl

/-- **And its structure morphism is the second projection**, on the nose.

Together with `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.baseChangeFunctor_obj_left`
this says that the functor adds nothing to the ambient fibre product except the two conditions
that make it an object of this category. -/
@[simp]
theorem baseChangeFunctor_obj_hom :
    ((baseChangeFunctor g).obj A).hom = Limits.pullback.snd A.hom g :=
  rfl

variable {A}

variable {B : SeparatedFiniteEtaleOver.{u} X}

/-- **The first triangle of a mapped morphism**: the base change of `i` followed by the projection
to the target's total space is the projection to the source's followed by `i`.

`CategoryTheory.Limits.pullback.lift_fst` at the lift `CategoryTheory.Over.pullback` is defined
by. -/
@[simp]
theorem baseChangeFunctor_map_left_fst (i : A ⟶ B) :
    ((baseChangeFunctor g).map i).left ≫ Limits.pullback.fst B.hom g
      = Limits.pullback.fst A.hom g ≫ i.left :=
  Limits.pullback.lift_fst _ _ _

/-- **The second triangle**, which is the statement that the mapped morphism is a morphism over
`X'`, read at the underlying morphisms. -/
@[simp]
theorem baseChangeFunctor_map_left_snd (i : A ⟶ B) :
    ((baseChangeFunctor g).map i).left ≫ Limits.pullback.snd B.hom g
      = Limits.pullback.snd A.hom g :=
  Limits.pullback.lift_snd _ _ _

end SeparatedFiniteEtaleOver

end ComplexAnalytic.AnalyticSpace

end

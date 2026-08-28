/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.LocalisationRigidity
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient

/-!
# The two-level index category of a glue data, and the four things a cover still has to supply

`OkaTest/LocalisationRigidity.lean` ends by naming the gap between an ordered family of
presentations and `ComplexAnalytic.coverGlueData`, and its `## What is not here` says what a
reader should know before attempting it:

> a glue data's own diagram has **two levels of object** — members `U i` and overlaps `V (i, j)` —
> and its law is a cocycle on triple overlaps expressed with pullbacks. That is a different law on
> a different index shape from the `trans_comp` a chain exercises, so choosing witnesses does not
> turn one into the other and `hcocycle` should be expected **not** to follow.

This file builds that two-level shape and settles, one at a time, which of
`ComplexAnalytic.coverGlueData`'s five inputs a functor out of it produces. Two of them are the
diagram's own data, one is a consequence of its single law, and the other two are not implied —
the last of those is a theorem here and not a prediction.

## The shape

`OkaTest.GlueShape.Shape J` has an object `OkaTest.GlueShape.mem i` for each member and an object
`OkaTest.GlueShape.ovl i j` for each **ordered** pair, generating arrows
`OkaTest.GlueShape.incl i j : ovl i j ⟶ mem i` and
`OkaTest.GlueShape.swap i j : ovl i j ⟶ ovl j i`, and one relation,
`OkaTest.GlueShape.swap_swap`. It is the free category on that quiver modulo that relation:
`CategoryTheory.Paths` and `CategoryTheory.Quotient`, which cost **two** Mathlib modules over the
closure this file already had.

**Going through the path category is what keeps `CategoryTheory.eqToHom` out of the file, and
that was the predicted expense.** Writing the hom-types by hand instead runs into the diagonal:
`ovl i i ⟶ mem i` has to have two elements, `incl i i` and `swap i i ≫ incl i i`, and the obvious
hand-written hom-type — a sum of two propositions saying `l = i` and `l = j` — has two elements
when `i ≠ j` and *also* two when `i = j`, but a functor out of it then has to produce a morphism
from a proof of `l = i ∨ l = j`, which is data from a `Prop`. The quotient of the path category
has neither problem and the whole construction is under a hundred lines.

**The shape is deliberately not thin.** `swap i i` is not forced to be the identity: the only
relation is that the two transitions of an overlap are inverse. Imposing `swap i i = 𝟙` would
exclude the inputs `ComplexAnalytic.coverGlueData` accepts, whose diagonal is filled in by
`CategoryTheory.GlueData.ofGlueData'` and not by the cover — see the `## What is not here`.

## What a cover has to supply, item by item

`ComplexAnalytic.coverGlueData` takes `obj`, `poly`, `glue`, `hrange`, `hsymm` and `hcocycle`.
Against the diagram:

| input | where it comes from |
|---|---|
| `obj` | the diagram at the members, `OkaTest.GlueShape.coverDiagram_obj_mem` |
| `poly` | the diagram at the overlaps, `OkaTest.GlueShape.coverDiagram_obj_ovl` |
| `glue` | the diagram at the transitions, `OkaTest.GlueShape.coverDiagram_map_swap` |
| `hsymm` | **follows**, `OkaTest.GlueShape.hsymm_of_hglue` |
| `hrange` | **does not follow**, `OkaTest.GlueShape.not_ctHRange` |
| `hcocycle` | not stateable without `hrange`; see below |

`hsymm` is the one that changes the interface. `ComplexAnalytic.coverGlueData` asks for
`glue j i = (glue i j).symm`, an equation of *isomorphisms*; the shape asks only that the two
transitions compose to the identity, which is what functoriality of any diagram gives
(`OkaTest.GlueShape.map_swap_comp`). Those are the same condition — a right inverse of an
isomorphism is its inverse — so a glue data of a cover takes one hypothesis
fewer than `ComplexAnalytic.coverGlueData` asks for, and
`OkaTest.GlueShape.coverGlueDataOfDiagram` is that reading of it.

`hcocycle` is a different case from `hrange` and the difference is worth stating precisely: it is
not that it fails to follow, it is that **it cannot be written down without `hrange`**. Its
statement is an equation between composites of `ComplexAnalytic.coverTriple`, and `hrange` is an
argument of `ComplexAnalytic.coverTriple`. So the question *"does `hcocycle` follow from the
diagram?"* has no formulation until `hrange` is granted, which is a stronger statement than the
one `OkaTest/LocalisationRigidity.lean` predicted.

## `hrange` really does not follow, and three members is where it is visible

`OkaTest.GlueShape.not_ctHRange` exhibits a three-member cover — every member the presentation of
a point, `ULift (Fin 0)` variables and no relations — with a witness polynomial for every ordered
pair and an isomorphism for every pair satisfying the shape's law, whose range hypothesis is
**false**. The configuration is `poly i j = 1` unless neither index is `0`, where it is `0`; then
`D(1) = ⊤` makes the triple overlap inside the zeroth member the whole space, and `D(0) = ⊥`
makes the open it is required to land in empty. The zeroth member has a point, so the range is
not empty and the containment fails.

Three is also the smallest index type that can see it, in both hypotheses:
`OkaTest.GlueShape.hRange_of_no_three` and `OkaTest.GlueShape.hCocycle_of_no_three` say that both
are automatic on any index type with no three pairwise distinct elements.
`OkaTest/ProjectiveLine.lean` records the two-member vacuity for `hcocycle`; **it holds for
`hrange` as well**, which is the same observation one hypothesis earlier and is not recorded
anywhere else.

## Main definitions

- `OkaTest.GlueShape.Shape`: the two-level index category of a glue data.
- `OkaTest.GlueShape.lift`: a functor out of it, from members, overlaps, inclusions and
  transitions with the one law.
- `OkaTest.GlueShape.coverDiagram`: the diagram of a cover with distinguished overlaps, as a
  functor to `ComplexAnalytic.Presentation`.
- `OkaTest.GlueShape.HRange` and `OkaTest.GlueShape.HCocycle`: the two triple-overlap hypotheses
  of `ComplexAnalytic.coverGlueData`, named so that they can be talked about.
- `OkaTest.GlueShape.coverGlueDataOfDiagram`: the glue data of a cover, out of its diagram and
  those two hypotheses and nothing else.

## Main results

- `OkaTest.GlueShape.lift_uniq`: **every functor out of the shape is the one its own data
  produces**, so the shape has no morphisms beyond those a glue-data diagram accounts for.
- `OkaTest.GlueShape.hsymm_of_hglue`: **the symmetry hypothesis is a consequence of the shape's
  law** and not an independent input.
- `OkaTest.GlueShape.not_ctHRange`: **the range hypothesis is not a consequence of the diagram.**
- `OkaTest.GlueShape.hRange_of_no_three` and `OkaTest.GlueShape.hCocycle_of_no_three`: neither
  triple-overlap hypothesis has content below three members.

## What is not here

**No `poly`, `glue`, `hrange` or `hcocycle` for an *ordered* cover.** The question
`OkaTest/LocalisationRigidity.lean` asks is what an ordered family of presentations may be assumed
to look like; this file answers a different one — what shape a glue data's diagram has — and the
two are related only in that the second is where the first was heading. Nothing here produces a
witness polynomial from an arrow of a preorder, and `OkaTest.LocalisationRigidity.ofPreorder` is
untouched.

**No two-level shape with the diagonal collapsed.** `CategoryTheory.GlueData` asks for `t i i =
𝟙` and `CategoryTheory.GlueData'` does not have `V (i, i)` at all;
`CategoryTheory.GlueData.ofGlueData'` is the bridge, and it fills the diagonal with `U i` behind a
`dif` on `i = j`. The shape here has the diagonal and does not collapse it, which is what makes
`OkaTest.GlueShape.coverDiagram` accept exactly the input `ComplexAnalytic.coverGlueData` accepts.
A variant shape with `swap i i = 𝟙` imposed would be a different category and is not built.

**Nothing about `AlgebraicGeometry.LocallyRingedSpace`.** The diagram lands in
`ComplexAnalytic.Presentation`; every statement about the glued space is
`ComplexAnalytic.coverGlueData`'s and is reached only through
`OkaTest.GlueShape.coverGlueDataOfDiagram`. In particular there is no claim here that the glued
space is anything, and no non-vacuity: `OkaTest/AffineCover.lean` and
`OkaTest/ProjectiveLine.lean` remain the two instances that check that.

**No new library API.** This is `OkaTest/LocalisationRigidity.lean`'s convention and its reason:
category theory with no analytic content stays in the test file until something consumes it, and
`Oka/Analytification/` is its home when something does. The successor issue — assembling `X^an`
for a non-affine scheme — is what would consume it, and moving a self-contained file is that
issue's business.
-/

universe v w u

open CategoryTheory MvPolynomial ComplexAnalytic

namespace OkaTest.GlueShape

/-- **The objects of the two-level shape**: one for each member of the cover, and one for each
**ordered** pair of members.

Ordered, and not a two-element set, because that is what `CategoryTheory.GlueData` asks for:
`V (i, j)` and `V (j, i)` are different objects with an isomorphism between them, and the whole
content of the transition is that the two readings of one overlap are identified. The diagonal
`ovl i i` is present and is not collapsed; see the module docstring. -/
inductive Obj (J : Type u) : Type u
  /-- A member of the cover. -/
  | mem (i : J) : Obj J
  /-- An overlap, read from the `i`-th member. -/
  | ovl (i j : J) : Obj J

variable (J : Type u)

/-- **The generating arrows**: an overlap includes into the member it is read from, and the two
readings of an overlap are exchanged.

There is no arrow between two members, which is the difference between this shape and the ordered
one `OkaTest.LocalisationRigidity.ofPreorder` is a functor out of — and it is why the counting
obstruction of `OkaTest.LocalisationRigidity.not_isRigid_of_lt_lt` never fires here. That theorem
rules out every arrow of a *chain* being a one-step localisation at once; this shape has no chain
of members to run it along, so a diagram in which every overlap is a one-step localisation of its
member is exactly what `ComplexAnalytic.coverGlueData` accepts. -/
inductive Gen : Obj J → Obj J → Type u
  /-- The inclusion of an overlap into the member it is read from. -/
  | incl (i j : J) : Gen (Obj.ovl i j) (Obj.mem i)
  /-- The transition between the two readings of an overlap. -/
  | swap (i j : J) : Gen (Obj.ovl i j) (Obj.ovl j i)

instance quiver : Quiver.{u} (Obj J) := ⟨Gen J⟩

/-- **The one relation**: exchanging the two readings of an overlap twice is the identity.

`ComplexAnalytic.coverGlueData`'s `hsymm` is this relation, and
`OkaTest.GlueShape.hsymm_of_hglue` is the proof that it is not weaker. Nothing says
`swap i i = 𝟙`; see the module docstring for why imposing it would exclude the inputs
`ComplexAnalytic.coverGlueData` accepts. -/
inductive Rel : HomRel (Paths (Obj J))
  /-- The two transitions of an overlap are inverse. -/
  | swap_swap (i j : J) :
      Rel ((Quiver.Hom.toPath (V := Obj J) (Gen.swap i j)).cons (Gen.swap j i))
        Quiver.Path.nil

/-- **The two-level index category of a glue data**: the free category on
`OkaTest.GlueShape.Gen` modulo `OkaTest.GlueShape.Rel`.

An `abbrev` rather than a `def` deliberately: `CategoryTheory.Quotient.lift_unique` and
`CategoryTheory.Quotient.functor` are stated about `CategoryTheory.Quotient` and a semireducible
wrapper puts the `CategoryTheory.Category` instances of the two spellings out of reach of
unification. -/
abbrev Shape : Type u := CategoryTheory.Quotient (Rel J)

/-- The quotient functor. -/
abbrev proj : Paths (Obj J) ⥤ Shape J := CategoryTheory.Quotient.functor (Rel J)

/-- The object of the shape at the `i`-th member. -/
abbrev mem (i : J) : Shape J := (proj J).obj (Obj.mem i)

/-- The object of the shape at the overlap of `i` with `j`. -/
abbrev ovl (i j : J) : Shape J := (proj J).obj (Obj.ovl i j)

/-- The inclusion of the overlap into the member it is read from. -/
def incl (i j : J) : ovl J i j ⟶ mem J i :=
  (proj J).map (Quiver.Hom.toPath (V := Obj J) (Gen.incl i j))

/-- The transition between the two readings of an overlap. -/
def swap (i j : J) : ovl J i j ⟶ ovl J j i :=
  (proj J).map (Quiver.Hom.toPath (V := Obj J) (Gen.swap i j))

/-- The two transitions of an overlap are inverse. -/
@[reassoc (attr := simp)]
theorem swap_swap (i j : J) : swap J i j ≫ swap J j i = 𝟙 (ovl J i j) := by
  rw [swap, swap, ← (proj J).map_comp, ← (proj J).map_id]
  exact CategoryTheory.Quotient.sound _ (Rel.swap_swap i j)

variable {J} {C : Type v} [Category.{w} C]

/-- **The prefunctor a glue-data diagram gives on the generators.**

The two `match`es are what makes this construction cheap: a generator determines its source and
target, so the object and morphism assignments are definitional and every computation lemma below
is `CategoryTheory.Paths.lift_toPath` or `rfl`. -/
def preLift (U : J → C) (V : J → J → C) (f : ∀ i j, V i j ⟶ U i)
    (t : ∀ i j, V i j ⟶ V j i) : Obj J ⥤q C where
  obj X := match X with
    | .mem i => U i
    | .ovl i j => V i j
  map {X Y} g := match X, Y, g with
    | _, _, .incl i j => f i j
    | _, _, .swap i j => t i j

/-- The one relation is respected. -/
theorem preLift_rel (U : J → C) (V : J → J → C) (f : ∀ i j, V i j ⟶ U i)
    (t : ∀ i j, V i j ⟶ V j i) (ht : ∀ i j, t i j ≫ t j i = 𝟙 (V i j)) :
    ∀ (x y : Paths (Obj J)) (p q : x ⟶ y), Rel J p q →
      (Paths.lift (preLift U V f t)).map p = (Paths.lift (preLift U V f t)).map q := by
  rintro _ _ _ _ ⟨i, j⟩
  rw [Paths.lift_cons, Paths.lift_toPath]
  exact ht i j

/-- **A functor out of the shape**, from members, overlaps, inclusions, transitions, and the one
law.

This is the two-level analogue of `OkaTest.LocalisationRigidity.ofPreorder`, and the comparison is
the point: there the laws had to be arguments because an arrow of a preorder carries no data, and
here there is exactly one law because the free category on two families of generators has exactly
one relation to impose. `OkaTest.GlueShape.lift_uniq` says nothing is lost. -/
def lift (U : J → C) (V : J → J → C) (f : ∀ i j, V i j ⟶ U i)
    (t : ∀ i j, V i j ⟶ V j i) (ht : ∀ i j, t i j ≫ t j i = 𝟙 (V i j)) :
    Shape J ⥤ C :=
  CategoryTheory.Quotient.lift _ (Paths.lift (preLift U V f t)) (preLift_rel U V f t ht)

variable (U : J → C) (V : J → J → C) (f : ∀ i j, V i j ⟶ U i) (t : ∀ i j, V i j ⟶ V j i)
  (ht : ∀ i j, t i j ≫ t j i = 𝟙 (V i j))

/-- The value at a member. -/
@[simp] theorem lift_obj_mem (i : J) : (lift U V f t ht).obj (mem J i) = U i := rfl

/-- The value at an overlap. -/
@[simp] theorem lift_obj_ovl (i j : J) : (lift U V f t ht).obj (ovl J i j) = V i j := rfl

/-- The value at an inclusion. -/
@[simp] theorem lift_map_incl (i j : J) : (lift U V f t ht).map (incl J i j) = f i j :=
  Paths.lift_toPath (preLift U V f t) (Gen.incl i j)

/-- The value at a transition. -/
@[simp] theorem lift_map_swap (i j : J) : (lift U V f t ht).map (swap J i j) = t i j :=
  Paths.lift_toPath (preLift U V f t) (Gen.swap i j)

/-- **The transitions of any functor out of the shape are inverse**, by functoriality alone.

This is the hypothesis `OkaTest.GlueShape.lift` asks for, read back off an arbitrary diagram, and
it is what makes `ComplexAnalytic.coverGlueData`'s `hsymm` a consequence rather than an input. -/
@[reassoc]
theorem map_swap_comp (D : Shape J ⥤ C) (i j : J) :
    D.map (swap J i j) ≫ D.map (swap J j i) = 𝟙 (D.obj (ovl J i j)) := by
  rw [← D.map_comp, swap_swap, D.map_id]

/-- **Every functor out of the shape is the one its own data produces.**

Together with the four computation lemmas above this says the shape is exactly right: a functor
out of it is *precisely* a family of members, a family of overlaps, an inclusion and a transition
for each ordered pair, and the one law — no more and no less. Without it `OkaTest.GlueShape.lift`
would only be a way of building some functors, and the claim that the shape is the index category
of a glue data would be a description rather than a theorem.

`CategoryTheory.Quotient.lift_unique` and `CategoryTheory.Paths.lift_unique` do the work; the two
remaining goals are `rfl` because `OkaTest.GlueShape.preLift` matches on the generators. -/
theorem lift_uniq (D : Shape J ⥤ C) :
    lift (fun i ↦ D.obj (mem J i)) (fun i j ↦ D.obj (ovl J i j))
      (fun i j ↦ D.map (incl J i j)) (fun i j ↦ D.map (swap J i j))
      (map_swap_comp D) = D := by
  have h : proj J ⋙ D =
      (Paths.lift (preLift (fun i ↦ D.obj (mem J i)) (fun i j ↦ D.obj (ovl J i j))
        (fun i j ↦ D.map (incl J i j)) (fun i j ↦ D.map (swap J i j))) :
          Paths (Obj J) ⥤ C) := by
    refine Paths.lift_unique _ _ ?_
    refine Prefunctor.ext (fun X ↦ ?_) (fun X Y g ↦ ?_)
    · cases X <;> rfl
    · cases g <;> rfl
  exact (CategoryTheory.Quotient.lift_unique _ _ _ D h).symm

/-- **A right inverse of an isomorphism is its inverse**, as an equation of isomorphisms rather
than of morphisms.

Stated in this form because `ComplexAnalytic.coverGlueData`'s `hsymm` is an equation of
`CategoryTheory.Iso`s, `glue j i = (glue i j).symm`, while what a diagram supplies is an equation
of morphisms. The two are the same condition and this is the step. -/
theorem symm_eq_of_hom_comp_hom {X Y : C} (e : X ≅ Y) (e' : Y ≅ X)
    (h : e.hom ≫ e'.hom = 𝟙 X) : e' = e.symm :=
  Iso.ext (by
    rw [Iso.symm_hom, ← Category.id_comp e'.hom, ← e.inv_hom_id, Category.assoc, h,
      Category.comp_id])

noncomputable section Cover

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hglue : ∀ i j : J, (glue i j).hom ≫ (glue j i).hom = 𝟙 (coverOverlap.{u} obj poly i j))

/-- **The diagram of a cover with distinguished overlaps**, as a functor to
`ComplexAnalytic.Presentation`.

The overlap at `(i, j)` is `ComplexAnalytic.coverOverlap`, the presentation of `D(f_ij)` inside
the `i`-th member, and the inclusion is `ComplexAnalytic.localisationHom`, its structure map. So
the *rigid* reading — every overlap literally a one-step localisation of its member — is what this
diagram records, and it is consistent here for the reason `OkaTest.GlueShape.Gen`'s docstring
gives. -/
def coverDiagram : Shape J ⥤ Presentation.{u} :=
  lift obj (coverOverlap.{u} obj poly) (fun i j ↦ localisationHom.{u} (obj i).g (poly i j))
    (fun i j ↦ (glue i j).hom) hglue

/-- The diagram's value at a member. -/
@[simp] theorem coverDiagram_obj_mem (i : J) :
    (coverDiagram obj poly glue hglue).obj (mem J i) = obj i := rfl

/-- The diagram's value at an overlap. -/
@[simp] theorem coverDiagram_obj_ovl (i j : J) :
    (coverDiagram obj poly glue hglue).obj (ovl J i j) = coverOverlap.{u} obj poly i j := rfl

/-- The diagram's value at an inclusion. -/
@[simp] theorem coverDiagram_map_incl (i j : J) :
    (coverDiagram obj poly glue hglue).map (incl J i j) =
      localisationHom.{u} (obj i).g (poly i j) :=
  lift_map_incl _ _ _ _ _ i j

/-- The diagram's value at a transition. -/
@[simp] theorem coverDiagram_map_swap (i j : J) :
    (coverDiagram obj poly glue hglue).map (swap J i j) = (glue i j).hom :=
  lift_map_swap _ _ _ _ _ i j

include hglue in
/-- **`ComplexAnalytic.coverGlueData`'s symmetry hypothesis is not an independent input**: it
follows from the one law of the shape.

This is the first of the five inputs to be settled, and it is the one that goes the good way. What
a diagram supplies is that the two transitions of an overlap compose to the identity; what
`ComplexAnalytic.coverGlueData` asks for is that each is the other's inverse as an isomorphism,
and `OkaTest.GlueShape.symm_eq_of_hom_comp_hom` is the whole distance between them. -/
theorem hsymm_of_hglue (i j : J) : glue j i = (glue i j).symm :=
  symm_eq_of_hom_comp_hom _ _ (hglue i j)

/-- **`ComplexAnalytic.coverGlueData`'s range hypothesis**, named.

It has to be named to be talked about: `OkaTest.GlueShape.not_ctHRange` is a statement *about* it
and `OkaTest.GlueShape.HCocycle` cannot be written without it. Its content is that the transition
from `i` to `j` carries the part of the overlap that also meets `k` into the part of `D(f_ji)`
that meets `k`. -/
abbrev HRange : Prop :=
  ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      ((coverOpen.{u} obj poly j k ⊓ coverOpen.{u} obj poly j i :
          TopologicalSpace.Opens (coverSpace.{u} obj j)) : Set (coverSpace.{u} obj j))

variable (hrange : HRange.{u} obj poly glue)

/-- **`ComplexAnalytic.coverGlueData`'s cocycle hypothesis**, named — and note that it takes the
range hypothesis as an argument.

That dependence is the answer to *"does the cocycle condition follow from the diagram?"*, and it
is a sharper answer than the expected one: the question has no formulation until the range
hypothesis is granted, because `ComplexAnalytic.coverTriple` — the morphism the three composites
are built from — is defined only in its presence. -/
abbrev HCocycle : Prop :=
  ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _

include hglue in
/-- **The glue data of a cover, out of its diagram and the two triple-overlap hypotheses.**

`ComplexAnalytic.coverGlueData` with one hypothesis fewer, and that is the whole benefit the shape
buys at this stage: `obj`, `poly` and `glue` are the diagram's own data, `hsymm` is
`OkaTest.GlueShape.hsymm_of_hglue`, and what is left over is exactly the two conditions that are
about triple overlaps in `AlgebraicGeometry.LocallyRingedSpace` rather than about the diagram. -/
def coverGlueDataOfDiagram (hcocycle : HCocycle.{u} obj poly glue hrange) :
    AlgebraicGeometry.LocallyRingedSpace.GlueData.{u} :=
  coverGlueData.{u} obj poly glue hrange (hsymm_of_hglue obj poly glue hglue) hcocycle

/-- **Fewer than three members cannot test the range hypothesis**: on an index type with no three
pairwise distinct elements it is automatic.

`OkaTest/ProjectiveLine.lean` records this for the cocycle hypothesis, where it is the reason a
two-member gluing proves nothing about it. It holds one hypothesis earlier as well, for the same
reason and by the same proof, and that does not seem to be recorded anywhere — so a two-member
instance is not evidence about either. -/
theorem hRange_of_no_three (h3 : ∀ i j k : J, i = j ∨ i = k ∨ j = k) :
    HRange.{u} obj poly glue := by
  intro i j k hij hik hjk
  rcases h3 i j k with h | h | h
  exacts [absurd h hij, absurd h hik, absurd h hjk]

/-- **Fewer than three members cannot test the cocycle hypothesis either.**

The `OkaTest/ProjectiveLine.lean` observation, in the form that quantifies over the index type
rather than over one gluing. -/
theorem hCocycle_of_no_three (h3 : ∀ i j k : J, i = j ∨ i = k ∨ j = k) :
    HCocycle.{u} obj poly glue hrange := by
  intro i j k hij hik hjk
  rcases h3 i j k with h | h | h
  exacts [absurd h hij, absurd h hik, absurd h hjk]

end Cover

/-! ### A three-member cover whose diagram is good and whose range hypothesis is false

Every member is the presentation of a point — no variables and no relations — so the analytic
side is as small as it can be and the only thing that varies is the witness polynomial. The
configuration is symmetric, so the transition isomorphisms are transports along an equality and
the shape's law holds; and it is chosen so that in `hrange 0 1 2` the source open is everything
and the target open is empty.
-/

noncomputable section Counterexample

/-- Every member is the presentation of a point. -/
def ctObj : Fin 3 → Presentation.{0} := fun _ ↦ ⟨0, 0, Fin.elim0⟩

/-- The witness polynomials: `1` unless neither index is `0`, and then `0`. -/
def ctPoly : ∀ i : Fin 3, Fin 3 → MvPolynomial (ULift.{0} (Fin (ctObj i).n)) ℂ :=
  fun i j ↦ if i = 0 ∨ j = 0 then 1 else 0

/-- The configuration is symmetric, which is what lets the transitions be transports. -/
theorem ctPoly_symm (i j : Fin 3) : ctPoly i j = ctPoly j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Out of the zeroth member every witness is `1`, so every overlap with it is the whole space. -/
theorem ctPoly_of_zero (j : Fin 3) : ctPoly 0 j = 1 := if_pos (Or.inl rfl)

/-- And into it. -/
theorem ctPoly_to_zero (i : Fin 3) : ctPoly i 0 = 1 := if_pos (Or.inr rfl)

/-- The one witness that is `0`, whose distinguished open is therefore empty. -/
theorem ctPoly_one_two : ctPoly 1 2 = 0 := if_neg (by decide)

/-- The two readings of an overlap are the same presentation. -/
theorem ctOverlap_eq (i j : Fin 3) :
    coverOverlap.{0} ctObj ctPoly i j = coverOverlap.{0} ctObj ctPoly j i := by
  simp only [coverOverlap, ctPoly_symm]
  rfl

/-- The transition isomorphisms, as transports along `OkaTest.GlueShape.ctOverlap_eq`. -/
def ctGlue (i j : Fin 3) :
    coverOverlap.{0} ctObj ctPoly i j ≅ coverOverlap.{0} ctObj ctPoly j i :=
  eqToIso (ctOverlap_eq i j)

set_option maxHeartbeats 1000000 in
/-- The shape's law holds, so these data really are a diagram of the shape. -/
theorem ctHglue (i j : Fin 3) :
    (ctGlue i j).hom ≫ (ctGlue j i).hom = 𝟙 (coverOverlap.{0} ctObj ctPoly i j) := by
  have h : (eqToIso (ctOverlap_eq i j)).hom ≫ (eqToIso (ctOverlap_eq j i)).hom =
      𝟙 (coverOverlap.{0} ctObj ctPoly i j) := by
    rw [eqToIso.hom, eqToIso.hom, eqToHom_trans, eqToHom_refl]
  exact h

/-- A point of the zeroth member: the origin of `ℂ^0`, on which no relation is imposed. -/
def ctPt : coverSpace.{0} ctObj 0 :=
  ⟨⟨(fun _ ↦ 0 : ULift.{0} (Fin 0) → ℂ), trivial⟩,
    (mem_zeroLocus_polySection_iff.{0} (ctObj 0).g _).2 (fun j ↦ j.elim0)⟩

set_option maxHeartbeats 1000000 in
/-- That point lies in the triple overlap of the zeroth member, because both witnesses there
are `1`. -/
theorem ctPt_mem : ctPt ∈ coverOpen.{0} ctObj ctPoly 0 1 ⊓ coverOpen.{0} ctObj ctPoly 0 2 :=
  ⟨(mem_localisationOpen_iff.{0} (ctObj 0).g (ctPoly 0 1)).2
      (by rw [ctPoly_of_zero, map_one]; exact one_ne_zero),
    (mem_localisationOpen_iff.{0} (ctObj 0).g (ctPoly 0 2)).2
      (by rw [ctPoly_of_zero, map_one]; exact one_ne_zero)⟩

set_option maxHeartbeats 1000000 in
/-- **The range hypothesis is not a consequence of the diagram.**

`OkaTest.GlueShape.ctObj`, `OkaTest.GlueShape.ctPoly` and `OkaTest.GlueShape.ctGlue` are a
three-member cover with a witness for every ordered pair and an isomorphism for every pair
satisfying the shape's one law — `OkaTest.GlueShape.ctHglue` — and the range hypothesis fails at
the triple `(0, 1, 2)`. Both witnesses out of the zeroth member are `1`, so the triple overlap
there is the whole space and `OkaTest.GlueShape.ctPt` is a point of it; the witness from the first
member to the second is `0`, so the open the image is required to lie in is empty.

This is what `OkaTest/LocalisationRigidity.lean` predicted for the cocycle condition, established
one hypothesis earlier and as a theorem rather than an expectation. It also fixes the smallest
index type at which the failure is visible: three, by
`OkaTest.GlueShape.hRange_of_no_three`. -/
theorem not_ctHRange : ¬ HRange.{0} ctObj ctPoly ctGlue := by
  intro h
  have hx := h 0 1 2 (by decide) (by decide) (by decide)
    ⟨(⟨ctPt, ctPt_mem⟩ : coverTriplePart.{0} ctObj ctPoly 0 1 2), rfl⟩
  have h3 := (mem_localisationOpen_iff.{0} (ctObj 1).g (ctPoly 1 2)).1 hx.1
  rw [ctPoly_one_two, map_zero] at h3
  exact h3 rfl

end Counterexample

end OkaTest.GlueShape

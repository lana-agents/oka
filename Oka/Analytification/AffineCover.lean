/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.LocalisationFunctor
import Oka.AnalyticSpace.Glue
import Oka.CategoryTheory.GlueData

/-!
# The glue data of an affine cover with distinguished overlaps

`Oka/Analytification/DistinguishedOpen.lean` identifies the analytification of `A_f` with the
distinguished open `D(f) ⊆ X^an`, **over `X^an`**, and `Oka/AnalyticSpace/Glue.lean` glues an
analytic space out of an `AlgebraicGeometry.LocallyRingedSpace.GlueData` whose pieces are
analytic. This file is the step between them: from a family of presentations, a distinguished
open of each for every other member, and a `ℂ`-algebra isomorphism identifying the two
descriptions of each overlap, it builds the glue data.

## The input, and why it is presentations rather than a scheme

**Nothing here turns an `AlgebraicGeometry.Scheme` into the data below, and the obstruction is
the arity of `poly`.** The `variable` line below declares it as `∀ i : J, J → MvPolynomial …`:
for each *ordered pair*, one polynomial, hence **one** distinguished open of the `i`-th member.
A scheme supplies less. `AlgebraicGeometry.exists_basicOpen_le_affine_inter` is stated at a
*point* of `U ⊓ V` and returns an open distinguished in both that contains it, so the
intersection of two affine members is a **union** of such opens, and nothing makes one of them
the whole of it. That is a claim about this file's own input, and **only an edit to this file can
falsify it** — which is the property the sentence it replaces lacked. That one counted
occurrences of `Scheme` across the whole tree at `master` = `31f5a2f` and concluded that every
scheme here is a `Spec`; `Oka/AlgebraicGeometry/Modules/Coherent.lean` carries
`AlgebraicGeometry.Scheme.isCoherentStructureSheaf`, a theorem about an arbitrary scheme, and has
falsified it since fourteen and a half hours after this file landed.

**What is missing is the construction, not the sentence**, which that measurement also got wrong:
the target is sayable, and needs nothing from this repository. With
`AlgebraicGeometry.Scheme.Over` in scope for the structure morphism, so that `↘` names it, and
`AlgebraicGeometry.LocallyOfFiniteType` asserted of that morphism, a well-formed target is

    noncomputable def analytificationOfScheme (X : Scheme.{0})
        [X.Over (Spec (CommRingCat.of ℂ))]
        [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of ℂ))] :
        ComplexAnalytic.AnalyticSpace.{0}

— note the universe, which is forced to `0` because `ℂ : Type` makes `Spec (CommRingCat.of ℂ)` a
`Scheme.{0}`. Everything else on this line is `{u}`-polymorphic and the scheme-level statement
cannot be.

So what this file takes is the cover **as data**: an index type `J`, a
`ComplexAnalytic.Presentation` for each index, a polynomial `poly i j` cutting out the part of the
`i`-th member that meets the `j`-th, and an isomorphism of the two presentations of the overlap.
The **members** lose nothing by that: `ComplexAnalytic.toFGAlg` is an equivalence onto the
finitely generated `ℂ`-algebras (`ComplexAnalytic.instIsEquivalenceToFGAlg`), so each of them is
an affine scheme locally of finite type over `ℂ`, transported. The **overlaps** are where the
general form differs, by the paragraph above, and what it would add is a comparison theorem —
that every such scheme arises this way, or that a cover of one can be refined until it does —
together with a choice among Mathlib's cover APIs. Neither is needed by anything downstream.
`Oka/Analytification/Comparison.lean` argues separately, in a titled section, that the absence of
`Scheme` from *its* statements is a result rather than an omission.

Only the **distinguished** case appears, and the reason is this repository's machinery rather
than the shape of a scheme's cover. `Oka/Analytification/DistinguishedOpen.lean` analytifies the
distinguished open `D(f)` and nothing else, and says in its own docstring that the
analytification of a general open immersion is neither proved nor wanted; a distinguished open
is therefore the only overlap this file has anything to build a transition from. That a scheme's
pairwise intersections are merely *covered by* opens distinguished in both is true, and is what
makes one open per pair a **restriction** rather than what licenses it — the paragraph above
says that of `poly`'s arity, and the one below names the Mathlib shape that carries the weaker
datum.

Mathlib does have a shape that carries what a scheme supplies at an overlap, and it is not the one
below: a **locally directed** cover, `Mathlib/AlgebraicGeometry/Cover/Directed.lean`. It indexes
the members by a category, gives a transition morphism for each arrow, and asks only that every
point of a pairwise overlap be hit by a third member mapping into both — so overlaps are not
chosen at all, they are covered by other members of the same family.
`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean` instantiates it for *every* scheme with
no hypotheses, indexed by the affine opens with an arrow `U ⟶ V` exactly when `U` is a
distinguished open of `V`, which is the data `Oka/Analytification/DistinguishedOpen.lean`
analytifies. Two things come with the shape and are the argument for it: the scheme is the colimit
of the family, and a morphism out of it glues from morphisms out of the members with compatibility
along the transition morphisms alone — no triple-overlap condition, where
`ComplexAnalytic.coverGlueData` below needs `hrange` and `hcocycle`. Adopting it here would
replace `poly`, `hrange` and `hcocycle` together, and would need the analytified transition
morphism to be functorial in composition of arrows, which is not in this repository. Nothing
downstream of this file needs any of it yet.

## The shape of the construction, and where the content is

The route is `CategoryTheory.GlueData'` — the variant that asks for the overlaps only when
`i ≠ j` — followed by `CategoryTheory.GlueData.ofGlueData'` and
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'` for the `f_open` field. `GlueData'`
discharges `f_id`, `t_id` and the three degenerate branches of `t'`, all of which are bookkeeping.

What is left is `t'` and the cocycle, and **the whole of the difficulty is that `t'` is a
morphism between categorical pullbacks**, which no tactic can compute with. That is what
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback` is for: it identifies
`pullback (f i j) (f i k)` with the open subspace `X_i|(D(f_ij) ⊓ D(f_ik))`, an object one can
name and restrict. With that identification:

* `t'` is `ComplexAnalytic.coverTriple` conjugated by two copies of it, and `t_fac` follows from
  the two factorisations of the identification together with the mono-ness of an open immersion;
* the **cocycle condition becomes exactly the hypothesis `hcocycle`**, because the conjugating
  isomorphisms cancel in pairs — the middle one of `t' i j k` is the same isomorphism as the
  first one of `t' j k i`, by construction.

So the two hypotheses this file asks the caller for, `hrange` and `hcocycle`, are statements
about morphisms of *open subspaces of the members*, which is the spelling a geometric input
arrives in and the one `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`'s module docstring
argues for.

## The diagonal

`poly` and `glue` are asked for at **every** pair, including `i = i`, but `hrange` and `hcocycle`
are required only at triples of *distinct* indices, which is all `CategoryTheory.GlueData'`
consumes. So the diagonal data is unused. It is not unconstrained: `hsymm` is quantified over
every pair and at `i = i` it says `glue i i = (glue i i).symm`, which a caller has to prove even
though nothing below reads it. That is weaker than `glue i i = Iso.refl` — it says only that the
transition is its own inverse — and `poly i i = 1` with `glue i i = Iso.refl` is the natural
choice, satisfies it, and is checked by nothing. Making `poly` partial instead would push a
`i ≠ j` argument through every definition below and into the type of every open subspace, which is
a much larger tax than one unused value per index.

## Main definitions

- `ComplexAnalytic.coverSpace`, `ComplexAnalytic.coverOpen`, `ComplexAnalytic.coverPart`: the
  `i`-th member `A_i^an`, the distinguished open `D(f_ij)` inside it, and that open as a space.
- `ComplexAnalytic.coverTransition`: the transition isomorphism `X_i|D(f_ij) ≅ X_j|D(f_ji)`,
  obtained from the given isomorphism of presentations by transporting it across
  `ComplexAnalytic.localisationIso` at each end.
- `ComplexAnalytic.coverTriple`: the transition on triple overlaps,
  `X_i|(D(f_ij) ⊓ D(f_ik)) ⟶ X_j|(D(f_jk) ⊓ D(f_ji))`, which is what `t'` is built from.
- `ComplexAnalytic.coverGlueData'` and `ComplexAnalytic.coverGlueData`: **the glue data.**

## Main results

- `ComplexAnalytic.coverGlueData_U` and `ComplexAnalytic.coverGlueData_ι_isOpenImmersion`: the
  members of the glue data are the analytifications one put in, and they are open subspaces of
  the gluing. Without the first, `coverGlueData` would be a well-typed object with no stated
  relation to its input.
- `ComplexAnalytic.glueDataCLinear_coverGlueData`: **the transitions are `ℂ`-linear**, for every
  input, so `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` applies and the gluing is an
  analytic space. The three lemmas it is built from —
  `ComplexAnalytic.comapAlgMap_coverOverlapIso`, `ComplexAnalytic.comapAlgMap_coverGlueIso` and
  `ComplexAnalytic.comapAlgMap_coverIncl_eq` — say where each factor of the transition gets its
  `ℂ`-linearity from.

## What is not here

* **The analytic space itself.** `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` turns this
  glue data into an analytic space, and `ComplexAnalytic.glueDataCLinear_coverGlueData` below
  supplies the half of its input that is about the gluing; what is still needed at a call site is
  that each member has local models, which is a statement about the member and not about this
  file's data. `OkaTest/AffineCover.lean` and `OkaTest/ProjectiveLine.lean` take that step.
* **Any statement that a gluing is not affine.** The two instances of this construction check
  different things and neither subsumes the other. `OkaTest/AffineCover.lean` glues three copies
  of the node along the punctured axis and shows that their three copies of the origin are three
  *distinct* points of the gluing, which is what rules out a construction quietly returning its
  first member. `OkaTest/ProjectiveLine.lean` glues two copies of the affine line along `D(z)` by
  `z ↦ 1/z` and shows that **neither member's inclusion is surjective**, so the glued space is
  equal to no one member; that is the stronger statement and it is proved only there. Neither
  exhibits a space that is not the analytification of *some* presentation, which is stronger
  again and needs an invariant nothing here computes.
* **`Localization.Away`.** Nothing here needs
  `ComplexAnalytic.PresentedAlgebra (localisationPresentation g f)` to *be* a localisation; it
  needs the structure map and its analytification, both of which
  `Oka/Analytification/LocalisationFunctor.lean` provides. See that file and
  `Oka/Analytification/DistinguishedOpen.lean`'s `## What is not here`.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)

/-! ### The members of the cover and their overlaps -/

/-- **The `i`-th member of the cover**, `A_i^an`, as a locally ringed space.

Everything in this file is spelled at the locally-ringed-space level, and deliberately:
`ComplexAnalytic.AnalyticSpace`'s `Category` instance defines composition through `toLRSHom`, so
unifying two composites of analytic morphisms forces it open and is expensive enough to exhaust
the heartbeat budget on a three-term `Iso.trans`. A glue data is a locally-ringed-space object
anyway. -/
abbrev coverSpace (i : J) : LocallyRingedSpace.{u} :=
  (AnalyticSpace.analytification.{u} (obj i).g).toLocallyRingedSpace

/-- **The part of the `i`-th member that meets the `j`-th**, as an open subset: `D(f_ij)`. -/
abbrev coverOpen (i j : J) : Opens (coverSpace.{u} obj i) :=
  localisationOpen.{u} (obj i).g (poly i j)

/-- **That open, as a space** — the object a glue data calls `V (i, j)`. -/
abbrev coverPart (i j : J) : LocallyRingedSpace.{u} :=
  (coverSpace.{u} obj i).restrict (coverOpen.{u} obj poly i j).isOpenEmbedding

/-- **Its inclusion into the `i`-th member** — the morphism a glue data calls `f i j`, and the
one its `f_open` field is about. -/
abbrev coverIncl (i j : J) : coverPart.{u} obj poly i j ⟶ coverSpace.{u} obj i :=
  (coverSpace.{u} obj i).ofRestrict (coverOpen.{u} obj poly i j).isOpenEmbedding

/-- **The presentation of the overlap, from the `i` side**: `(A_i)_{f_ij}`, presented by
`ComplexAnalytic.localisationPresentation`. This is the object the input isomorphism is between,
and it is where the *algebra* enters — everything else in this file is geometry. -/
abbrev coverOverlap (i j : J) : Presentation.{u} :=
  ⟨(obj i).n + 1, (obj i).k + 1, localisationPresentation.{u} (obj i).g (poly i j)⟩

/-- **The analytification of that presentation**, as a locally ringed space. -/
abbrev coverOverlapSpace (i j : J) : LocallyRingedSpace.{u} :=
  (AnalyticSpace.analytification.{u}
    (localisationPresentation.{u} (obj i).g (poly i j))).toLocallyRingedSpace

/-- **`ComplexAnalytic.localisationIso` at the locally-ringed-space level**: the analytification
of `(A_i)_{f_ij}` is the open subspace `D(f_ij)` of `A_i^an`.

Stated as a definition of its own rather than inlined into
`ComplexAnalytic.coverTransition` because the three-term `Iso.trans` there has to unify the
intermediate objects, and doing that against the *body* of a composite rather than against a
declared type is what runs the heartbeat budget out. Naming the two factors fixes it. -/
def coverOverlapIso (i j : J) :
    coverOverlapSpace.{u} obj poly i j ≅ coverPart.{u} obj poly i j :=
  AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso (localisationIso.{u} (obj i).g (poly i j))

variable (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)

/-- **The given isomorphism of presentations, analytified**, at the locally-ringed-space level.
Named for the same reason as `ComplexAnalytic.coverOverlapIso`. -/
def coverGlueIso (i j : J) :
    coverOverlapSpace.{u} obj poly i j ≅ coverOverlapSpace.{u} obj poly j i :=
  AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
    (analytificationFunctor.{u}.mapIso (glue i j))

/-- **The transition isomorphism `X_i|D(f_ij) ≅ X_j|D(f_ji)`** — the morphism a glue data calls
`t i j`.

It is the given algebra isomorphism read through `ComplexAnalytic.localisationIso` at each end.
This is the only place the input's algebraic content is used, and it is why the file needs
`Oka/Analytification/DistinguishedOpen.lean` rather than only the functor. -/
def coverTransition (i j : J) : coverPart.{u} obj poly i j ≅ coverPart.{u} obj poly j i :=
  (coverOverlapIso.{u} obj poly i j).symm ≪≫ coverGlueIso.{u} obj poly glue i j ≪≫
    coverOverlapIso.{u} obj poly j i

/-- **The transition, followed into the ambient `j`-th member.** This is the morphism the range
hypothesis below is about: where the overlap of `i` and `j` goes inside `A_j^an`. -/
def coverTransitionHom (i j : J) : coverPart.{u} obj poly i j ⟶ coverSpace.{u} obj j :=
  (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i

/-- **The transition isomorphisms are inverse to each other**, provided the input isomorphisms
are. `Functor.mapIso` commutes with `Iso.symm`, twice. -/
theorem coverGlueIso_symm (hsymm : ∀ i j : J, glue j i = (glue i j).symm) (i j : J) :
    coverGlueIso.{u} obj poly glue j i = (coverGlueIso.{u} obj poly glue i j).symm := by
  rw [coverGlueIso, coverGlueIso, hsymm i j, Functor.mapIso_symm, Functor.mapIso_symm]
  rfl

/-! ### Triple overlaps -/

/-- **The triple overlap `D(f_ij) ⊓ D(f_ik)` inside the `i`-th member**, as a space.

By `ComplexAnalytic.localisationOpen_mul` this is again a distinguished open of `A_i^an`, namely
`D(f_ij · f_ik)`; nothing below uses that, but it is the reason the classical construction works
and the reason that lemma exists. -/
abbrev coverTriplePart (i j k : J) : LocallyRingedSpace.{u} :=
  (coverSpace.{u} obj i).restrict
    (coverOpen.{u} obj poly i j ⊓ coverOpen.{u} obj poly i k).isOpenEmbedding

/-- **The inclusion of the triple overlap into the double overlap of `i` and `j`.** -/
abbrev coverTripleIncl (i j k : J) :
    coverTriplePart.{u} obj poly i j k ⟶ coverPart.{u} obj poly i j :=
  (coverSpace.{u} obj i).restrictLE (inf_le_left :
    coverOpen.{u} obj poly i j ⊓ coverOpen.{u} obj poly i k ≤ coverOpen.{u} obj poly i j)

variable (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
  Set.range (coverTripleIncl.{u} obj poly i j k ≫ coverTransitionHom.{u} obj poly glue i j).base ⊆
    ((coverOpen.{u} obj poly j k ⊓ coverOpen.{u} obj poly j i : Opens (coverSpace.{u} obj j)) :
      Set (coverSpace.{u} obj j)))

/-- **The transition on triple overlaps**, `X_i|(D(f_ij) ⊓ D(f_ik)) ⟶ X_j|(D(f_jk) ⊓ D(f_ji))`.

This is `t'` before it is conjugated into the pullbacks, and the hypothesis `hrange` is exactly
what says the classical statement — that the transition from `i` to `j` carries the part of the
overlap that also meets `k` into the part of `D(f_ji)` that meets `k` — holds. It is not implied
by anything: two members can be glued along an open without their glueings agreeing on triple
overlaps, and that is what `hrange` and `hcocycle` rule out. -/
def coverTriple (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coverTriplePart.{u} obj poly i j k ⟶ coverTriplePart.{u} obj poly j k i :=
  LocallyRingedSpace.liftRestrict
    (coverTripleIncl.{u} obj poly i j k ≫ coverTransitionHom.{u} obj poly glue i j) _
    (hrange i j k hij hik hjk)

/-- **`coverTriple` is a morphism over the ambient member**, which is the only property of it
anything consumes. -/
@[reassoc (attr := simp)]
theorem coverTriple_fac (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        (coverSpace.{u} obj j).ofRestrict
          (coverOpen.{u} obj poly j k ⊓ coverOpen.{u} obj poly j i).isOpenEmbedding =
      coverTripleIncl.{u} obj poly i j k ≫ coverTransitionHom.{u} obj poly glue i j :=
  LocallyRingedSpace.liftRestrict_fac _ _ _

/-! ### The glue data -/

/-- **The glue data of the cover, in the form that only asks for the overlaps when `i ≠ j`.**

`t'` is `ComplexAnalytic.coverTriple` conjugated by
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback` at each end, which is what turns a
morphism of open subspaces into a morphism of categorical pullbacks. Two consequences, and they
are the whole reason for going through that identification:

* `t_fac` reduces to an equation between two morphisms into `X_j|D(f_ji)`, which
  `AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict` turns into an equation over `X_j`, and
  there both sides are `coverTripleIncl ≫ coverTransitionHom` by `coverTriple_fac`;
* `cocycle` is `hcocycle` and nothing else: the second conjugating isomorphism of `t' i j k` is
  the *same* isomorphism as the first of `t' j k i`, so all six cancel in pairs. -/
def coverGlueData' (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    GlueData' LocallyRingedSpace.{u} where
  J := J
  U := coverSpace.{u} obj
  V i j _ := coverPart.{u} obj poly i j
  f i j _ := coverIncl.{u} obj poly i j
  t i j _ := (coverTransition.{u} obj poly glue i j).hom
  t' i j k hij hik hjk :=
    ((coverSpace.{u} obj i).restrictInfIsoPullback
      (coverOpen.{u} obj poly i j) (coverOpen.{u} obj poly i k)).inv ≫
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      ((coverSpace.{u} obj j).restrictInfIsoPullback
        (coverOpen.{u} obj poly j k) (coverOpen.{u} obj poly j i)).hom
  t_fac i j k hij hik hjk := by
    rw [Category.assoc, Category.assoc,
      LocallyRingedSpace.restrictInfIsoPullback_hom_snd, Iso.inv_comp_eq, ← Category.assoc,
      LocallyRingedSpace.restrictInfIsoPullback_hom_fst]
    refine LocallyRingedSpace.hom_ext_restrict _ _ _ ?_
    rw [Category.assoc, LocallyRingedSpace.restrictLE_fac, coverTriple_fac]
    rfl
  t_inv i j _ := by
    simp only [coverTransition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc, coverGlueIso_symm.{u} obj poly glue hsymm i j, Iso.symm_hom,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  cocycle i j k hij hik hjk := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hcocycle i j k hij hik hjk, Iso.inv_hom_id]

/-- **The glue data of an affine cover with distinguished overlaps.**

`CategoryTheory.GlueData.ofGlueData'` of `ComplexAnalytic.coverGlueData'`, with the `f_open`
field supplied by `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'` — whose hypothesis is
that each `f i j` is an open immersion, and each is `ofRestrict`.

Note which of the two open-immersion facts about a distinguished open this uses:
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict`, not
`ComplexAnalytic.isOpenImmersion_localisationProj`. The two are the same fact at the two
spellings of the overlap — as the open subspace, and as the analytification of the localisation —
and this file takes the first, because that is the spelling at which the range computations `t'`
needs are statements about `ComplexAnalytic.localisationOpen`. The algebraic description enters
only through `ComplexAnalytic.coverTransition`. -/
def coverGlueData (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    LocallyRingedSpace.GlueData.{u} where
  toGlueData :=
    GlueData.ofGlueData' (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)
  f_open i j :=
    LocallyRingedSpace.isOpenImmersion_f'
      (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)
      (fun _ _ _ ↦ LocallyRingedSpace.isOpenImmersion_ofRestrict _ _) i j

variable (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The members of the glue data are the analytifications one put in.**

`rfl`, and stated because without it `ComplexAnalytic.coverGlueData` is a well-typed object with
no recorded relation to its input: `CategoryTheory.GlueData.ofGlueData'` has no projection lemmas
in Mathlib, so nothing else says what `U` is. -/
@[simp]
theorem coverGlueData_U (i : J) :
    (coverGlueData.{u} obj poly glue hrange hsymm hcocycle).U i = coverSpace.{u} obj i :=
  rfl

/-- **The `i`-th member is an open subspace of the gluing.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion` at this glue data, and the
statement in which the construction is a *cover*: together with
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective`, the analytifications one
started from are an open cover of the space this builds. -/
theorem coverGlueData_ι_isOpenImmersion (i : J) :
    LocallyRingedSpace.IsOpenImmersion
      ((coverGlueData.{u} obj poly glue hrange hsymm hcocycle).toGlueData.ι i) :=
  inferInstance

/-! ### The transitions are `ℂ`-linear

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` turns a glue data of analytic pieces into an
analytic space provided its transitions are `ℂ`-linear (`ComplexAnalytic.GlueDataCLinear`). For a
glue data built here that hypothesis is **automatic**, and the reason is that every morphism in
sight is a morphism of *analytic* spaces, whose `ℂ`-linearity is a field rather than something to
prove: `ComplexAnalytic.coverOverlapIso` is `ComplexAnalytic.localisationIso` and
`ComplexAnalytic.coverGlueIso` is the given algebra isomorphism analytified, both read through
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`.

The work is therefore transport rather than algebra, and it is done in the three lemmas below:
each factor of `ComplexAnalytic.coverTransition` is recognised as an analytic morphism, and
`ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom` turns that into the equation of
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap`s the predicate is stated with.
-/

/-- **The overlap's own analytic structure is the one it inherits from the `i`-th member.**

`ComplexAnalytic.coverOverlapIso` followed by the inclusion of `D(f_ij)` is
`ComplexAnalytic.localisationProj` (`ComplexAnalytic.toLRSHom_localisationProj`), which is a
morphism of analytic spaces, so this is that morphism's `ℂ`-linearity field. -/
theorem comapAlgMap_coverOverlapIso (i j : J) :
    LocallyRingedSpace.comapAlgMap
        ((coverOverlapIso.{u} obj poly i j).hom ≫ coverIncl.{u} obj poly i j)
        (AnalyticSpace.analytification.{u} (obj i).g).algebraMap =
      (AnalyticSpace.analytification.{u} (coverOverlap.{u} obj poly i j).g).algebraMap := by
  rw [show (coverOverlapIso.{u} obj poly i j).hom ≫ coverIncl.{u} obj poly i j =
      (localisationProj.{u} (obj i).g (poly i j)).toLRSHom from
    (toLRSHom_localisationProj.{u} (obj i).g (poly i j)).symm]
  exact AnalyticSpace.comapAlgMap_toLRSHom _

/-- **The given algebra isomorphism, analytified, carries one overlap's structure to the
other's.**

This is where the input's algebraic content is used, and it is free: `glue i j` is an isomorphism
of *presentations*, so `ComplexAnalytic.analytificationFunctor` sends it to an isomorphism of
analytic spaces, and its `ℂ`-linearity is that morphism's own field. Nothing here computes with
the isomorphism. -/
theorem comapAlgMap_coverGlueIso (i j : J) :
    LocallyRingedSpace.comapAlgMap (coverGlueIso.{u} obj poly glue i j).hom
        (AnalyticSpace.analytification.{u} (coverOverlap.{u} obj poly j i).g).algebraMap =
      (AnalyticSpace.analytification.{u} (coverOverlap.{u} obj poly i j).g).algebraMap :=
  AnalyticSpace.comapAlgMap_toLRSHom (analytificationFunctor.{u}.map (glue i j).hom)

/-- **The two structures the overlap inherits agree**, before the `dite`s of
`CategoryTheory.GlueData.ofGlueData'` are in the way: from the `i`-th member directly, and from
the `j`-th through the transition.

Both are compared after `ComplexAnalytic.coverOverlapIso`, which is legitimate because
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_hom_injective` says pulling back along an
isomorphism loses nothing; there both sides become the overlap's own structure, by the two lemmas
above and the cancellation of `ComplexAnalytic.coverOverlapIso` against itself inside
`ComplexAnalytic.coverTransition`. -/
theorem comapAlgMap_coverIncl_eq (i j : J) :
    LocallyRingedSpace.comapAlgMap (coverIncl.{u} obj poly i j)
        (AnalyticSpace.analytification.{u} (obj i).g).algebraMap =
      LocallyRingedSpace.comapAlgMap
        ((coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i)
        (AnalyticSpace.analytification.{u} (obj j).g).algebraMap := by
  refine LocallyRingedSpace.comapAlgMap_hom_injective (coverOverlapIso.{u} obj poly i j) ?_
  dsimp only
  rw [← LocallyRingedSpace.comapAlgMap_comp, ← LocallyRingedSpace.comapAlgMap_comp,
    comapAlgMap_coverOverlapIso]
  have ht : (coverOverlapIso.{u} obj poly i j).hom ≫
      (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i =
        (coverGlueIso.{u} obj poly glue i j).hom ≫
          ((coverOverlapIso.{u} obj poly j i).hom ≫ coverIncl.{u} obj poly j i) := by
    simp [coverTransition]
  rw [ht, LocallyRingedSpace.comapAlgMap_comp, comapAlgMap_coverOverlapIso,
    comapAlgMap_coverGlueIso]

/-- **The transitions of the glue data of an affine cover are `ℂ`-linear**, for the structures the
members carry as analytifications. This is the hypothesis
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` asks for, so an affine cover with distinguished
overlaps produces an *analytic space* and not merely a locally ringed space.

The content is `ComplexAnalytic.comapAlgMap_coverIncl_eq`; the rest is getting past the `dite`s
that `CategoryTheory.GlueData.ofGlueData'` fills the diagonal with, by
`CategoryTheory.GlueData.ofGlueData'_f_of_ne` and
`CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne`.

Two places want a term rather than a rewrite and the second is not optional. The diagonal case is
an equation of *morphisms*, so `congrArg` disposes of it without touching the structures. Off the
diagonal both sides carry the same `eqToHom` prefix, and
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp` has to be applied **as a term**: the
corresponding `rw` reports *did not find an occurrence of the pattern
`comapAlgMap (?f ≫ ?g) ?γ`* against a goal that visibly has that shape, and it still does after
`dsimp only [CategoryTheory.GlueData.ofGlueData']`, so delta-reducing the projections in the goal
is not the remedy. **Why it fails is not established here** and no explanation should be read
into it; the contrast worth having is that
`ComplexAnalytic.comapAlgMap_coverIncl_eq` above rewrites with the same lemma twice and
successfully, at the same category, on a composite that has not come through
`CategoryTheory.GlueData.ofGlueData'_f_of_ne` carrying its `eqToHom`. -/
theorem glueDataCLinear_coverGlueData :
    GlueDataCLinear.{u} (coverGlueData.{u} obj poly glue hrange hsymm hcocycle)
      fun j ↦ (AnalyticSpace.analytification.{u} (obj j).g).algebraMap := by
  intro i j
  by_cases h : i = j
  · subst h
    refine congrArg (fun m ↦ LocallyRingedSpace.comapAlgMap m
      (AnalyticSpace.analytification.{u} (obj i).g).algebraMap) ?_
    change (CategoryTheory.GlueData.ofGlueData'
        (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).f i i =
      (CategoryTheory.GlueData.ofGlueData'
        (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).t i i ≫
        (CategoryTheory.GlueData.ofGlueData'
          (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).f i i
    rw [CategoryTheory.GlueData.ofGlueData'_f_self, CategoryTheory.GlueData.ofGlueData'_t_self]
    simp
  · change LocallyRingedSpace.comapAlgMap ((CategoryTheory.GlueData.ofGlueData'
        (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).f i j) _ =
      LocallyRingedSpace.comapAlgMap ((CategoryTheory.GlueData.ofGlueData'
        (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).t i j ≫
        (CategoryTheory.GlueData.ofGlueData'
          (coverGlueData'.{u} obj poly glue hrange hsymm hcocycle)).f j i) _
    rw [CategoryTheory.GlueData.ofGlueData'_f_of_ne _ h,
      CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne _ h]
    dsimp only [coverGlueData']
    exact (LocallyRingedSpace.comapAlgMap_comp _ _ _).trans
      ((congrArg (LocallyRingedSpace.comapAlgMap (eqToHom (dif_neg h)))
        (comapAlgMap_coverIncl_eq.{u} obj poly glue i j)).trans
          (LocallyRingedSpace.comapAlgMap_comp _ _ _).symm)

end

end ComplexAnalytic

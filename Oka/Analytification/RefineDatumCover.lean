/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CoverGlueTop
import Oka.Analytification.GlueShape
import Oka.Analytification.RefineDatumToBase
import Oka.Analytification.RefineDatumUnitFamily
import Oka.Analytification.RefineDatumWitness

/-!
# The refined cover's space maps onto the one it refines, when the refining family covers

`Oka/Analytification/RefineDatumToBase.lean` builds `ComplexAnalytic.refineDatumToBase`, the
morphism from a cross-member refinement's analytic space down to the cover it refines, and its own
`## What is not here` records what that does not say:

> * **Nothing that says the refined datum covers the original space.**
>   `Oka/Analytification/CrossMemberDatum.lean`'s *"No statement that the refined data cover
>   anything"* is untouched: a morphism down is not a covering, and the surjectivity of this one is
>   not proved, stated, or needed below.

**This file supplies the surjectivity**, under the condition that the refining family covers, and
computes the image with no condition at all. **It says nothing about injectivity and nothing about
either morphism being an isomorphism**; that bullet's neighbours in the same list are untouched.

## The image is a theorem and the covering is a hypothesis, and that split is the file

`ComplexAnalytic.coverIota_comp_refineDatumToBase` says the morphism restricts on the `b`-th
refined member to `ComplexAnalytic.localisationProj` followed by
`ComplexAnalytic.coverIota (σ b)`. Reading that at a point in both directions gives the image
outright:

`ComplexAnalytic.range_base_refineDatumToBase` — **the image is the union over `b` of the images of
`D(fam b)`, for every cross-member refinement, on no hypothesis beyond the ones the morphism
already takes.** Its `⊆` is the refined glue data's
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` and
`ComplexAnalytic.range_base_localisationProj_subset`; its `⊇` is
`ComplexAnalytic.range_base_localisationProj`, the *equality* — this is the one place on this line
where the containment is not enough, since a point of `D(fam b)` has to be produced from upstairs
rather than merely landed in.

Everything else here is a corollary of it, including the converse:
`ComplexAnalytic.surjective_base_refineDatumToBase_iff` is `Set.range_eq_univ` at that equation and
says what surjectivity is actually equivalent to.

## Why the condition is stated per member and not per point of the glued space

`ComplexAnalytic.RefineDatumCovers` asks that every point of every *member* of the original cover
lie in a refined member over that member. **The glued-space form — every point of `X^an` lies in
the image of some refined member — is strictly weaker and would make the sufficiency below almost
vacuous**, since the members are glued along their overlaps and a point of the `i`-th member can be
reached through a different one. What the union in `range_base_refineDatumToBase` being everything
says is the weak form; that is the equivalence, and it is why the sufficient condition is stated
separately rather than being read off the iff.

**That the two differ is a theorem here and not a design note**, and the section below is the
witness. This paragraph asserted the strictness with nothing behind it when the file landed, and a
non-implication asserted flatly is exactly what this line of files asks a branch not to do.

## The strictness, and the shape of the counterexample

`ComplexAnalytic.dupStrict`: **a cover datum, an index map and a refining family for which the
morphism down is surjective and `ComplexAnalytic.RefineDatumCovers` is false.** So the sufficient
condition is not necessary, and what surjectivity is equivalent to really is the weaker statement.

The mechanism is the one the paragraph above names, at its extreme: `ComplexAnalytic.dupObj` is
**two copies of one presentation glued along the whole of each**, so either member alone is the
whole gluing and the second is redundant, and `ComplexAnalytic.dupSigma` misses it. The general
reason is `ComplexAnalytic.mem_range_of_refineDatumCovers` — **the per-member condition forces the
index map to hit every index whose member has a point**, which is a demand the glued-space form
does not make, and it is why `ComplexAnalytic.refineDatumOneCovers` needs `Function.Surjective σ`
at all.

**Two of the three things this needed were already in the tree**, and grepping for them cost less
than the two lemmas it saved. `ComplexAnalytic.surjective_ι_coverGlueData` is the redundancy
argument, in the exact hypothesis shape a constant `poly` produces;
`ComplexAnalytic.GlueShape.hRange_of_no_three` and
`ComplexAnalytic.GlueShape.hCocycle_of_no_three` make two of the three cover-datum laws free below
three members. So the datum itself costs an `Iso.refl` and one `Iso.refl_symm`.

**Nothing in that section bears on `ComplexAnalytic.lineRefinement`**, in either direction: its
family is `fam ≡ 1`, which refines nothing.

The per-member form is also the one `Oka/Analytification/CoverRefinement.lean` names, in the
sentence `Oka/Analytification/RefineDatumToBase.lean` quotes when it declines to state it: *"what
would make a comparison an isomorphism is the condition … that the refining family covers"*.

**`ComplexAnalytic.coverSpaceHomOfEq` is what keeps the condition transport-free.** `fam b` is a
polynomial in the variables of `obj (σ b)` and the point is in the `i`-th member, so a naïve
spelling needs `h ▸ fam b` or `h ▸ y` along `h : σ b = i`;
`Oka/Analytification/RefineDatumRange.lean` declares that identification for exactly this problem,
records in its own docstring what the unascribed spelling costs, and it is already the vocabulary
`ComplexAnalytic.comm_refineDatumMapPart`'s equal branch is written in. Its two consumers here are
`ComplexAnalytic.coverSpaceHomOfEq_self`, in the sufficiency, and
`ComplexAnalytic.coverSpaceHomOfEq_refl`, in the instance.

## The instance, and it is what stops the condition from being empty

`ComplexAnalytic.refineDatumOneCovers`: at `Oka/Analytification/RefineDatumWitness.lean`'s trivial
refining family the condition holds as soon as `σ` is **surjective**, by
`ComplexAnalytic.localisationOpen_one` — `D(1)` is the whole member, so the only thing left to ask
is that some refined index lie over each original one. So
`ComplexAnalytic.surjective_base_refineDatumOneToBase`: that witness maps **onto** the cover it
refines, for every cover datum and every surjective index map. `OkaTest/RefineDatumWitness.lean`
instantiates it at `σ = id` on a three-element index type.

**`fam ≡ 1` is a reindexing and not a proper refinement**, which is what
`Oka/Analytification/RefineDatumWitness.lean` says of it in terms, so this instance is the trivial
end of the condition and not evidence about the other end. What it establishes is that
`ComplexAnalytic.RefineDatumCovers` is satisfiable, which nothing else here would say.

## Why a module of its own rather than a line in either file it imports

**Because the instance needs both imports and neither file imports the other.**
`Oka/Analytification/RefineDatumToBase.lean` and `Oka/Analytification/RefineDatumWitness.lean` both
sit directly on `Oka/Analytification/RefineDatumCocycle.lean`, and their `Oka`-closures are equal
except that each contains itself. So an append into either buys the other as a new import, and the
choice is one `Oka` module either way.

**The closure figures, quoted so the trade is visible rather than implied**, computed with
`scripts/import_cost.py`'s comment-stripping reader imported by path — neither of that script's CLI
forms prices an `Oka/Analytification/` module — and with
`Oka/Analytification/SpecRefinedChoice.lean` as the control, whose published **92 / 72**
reproduces. At the time this module was created its closure was **97** `Oka` modules and **71**
Mathlib roots, itself counted in, against **96** and **71** for either append: **one `Oka` module
and no Mathlib root**, which is the same trade
`Oka/Analytification/SpecRefinedChoice.lean` recorded making for its own existence. That figure
is the argument's and not this file's, and the argument is unchanged by what has been imported
since.

**What this file's closure is *now* is a different number and it had gone stale twice.** The
strictness counterexample added two import lines and
`### The instance at a family that is a unit on each overlap` below adds one more, so the
figure today is **100** `Oka` modules and **73** Mathlib roots. Both columns had
drifted — the paragraph above read 97 and 71 while the tree read 99 and 73 — and the Mathlib
column is *roots* and not the transitive closure, which is why 73 appears here where a branch
counting transitively wrote 3362. **Say which you are counting or the number means nothing**, and
re-measure rather than adding to what is written: that section's import cost **`+1` `Oka`
module and `+0` Mathlib roots** measured on the branch that added it, with
`Oka/Analytification/AffineCover.lean` — already in the closure — quoted as a control reading
`+0` on both columns, as it must.

**The `## Main results` bullet for `ComplexAnalytic.refineDatumToBase_base_coverIota` names a
theorem without citing it, and that is deliberate.** `scripts/guard_coverage.py` reads every
backticked repository name under a `## Main results` heading as a result *that* file advertises,
so citing
`ComplexAnalytic.coverIota_comp_refineDatumToBase` there would advertise another file's theorem
from this one — the live check whose figure has caught a defect on three separate branches.
`Oka/Analytification/AffineCover.lean` and `Oka/Analytification/CoverRefinement.lean` both record
the same workaround at bullets of their own: name the law, cite it from the prose above, and the
count stays a count of this file's results.

The tie is broken by what each candidate is for:

* `Oka/Analytification/RefineDatumToBase.lean` is **the file whose `## What is not here` bullet
  this retires**, and appending a retirement into the file that records the absence is the shape
  this board has repeatedly said reads worst — the bullet and its refutation would be forty lines
  apart in one docstring.
* `Oka/Analytification/RefineDatumWitness.lean` is a *witness* file. Its subject is the trivial
  family and the two adopted range conditions; the comparison morphism appears in it nowhere, and
  three of the five results below are about a general refinement with no witness in sight.

## And why the unit family's morphism is named here rather than beside the space it comes out of

**Because the trivial family's counterpart is already here, and the split is not arbitrary.**
`Oka/Analytification/RefineDatumWitness.lean` holds the trivial family's choices, its glue data and
its space; `ComplexAnalytic.refineDatumOneCovers` and
`ComplexAnalytic.surjective_base_refineDatumOneToBase` — the two statements about the *morphism
down* — are in this file. `Oka/Analytification/RefineDatumUnitFamily.lean` stands to the unit family
exactly as that witness file stands to the trivial one, so its morphism belongs where the other
one's is.

**And it is the cheaper edge, measured both ways.** This file already imports
`Oka/Analytification/RefineDatumToBase.lean`, so gaining
`Oka/Analytification/RefineDatumUnitFamily.lean` costs it **one** `Oka` module and no Mathlib root.
The other direction costs more than it looks: appending into
`Oka/Analytification/RefineDatumUnitFamily.lean` would buy
`Oka/Analytification/RefineDatumToBase.lean` for `+1`, but the equivalence needs *this* file's
`ComplexAnalytic.surjective_base_refineDatumToBase_iff` as well, and that edge takes that file's
closure from **95** to **100** — `+5` `Oka` modules and `+2` Mathlib roots — or else splits the two
declarations across two files and pays two edges instead of one.

## Main definitions

- `ComplexAnalytic.RefineDatumCovers`: **the refining family covers** — every point of every member
  of the original cover lies in a refined member lying over that member.
- `ComplexAnalytic.refineDatumUnitFamToBase`: **the morphism down at an injective index map and a
  family that is a unit on each overlap**, whose source is written as the space
  `ComplexAnalytic.refineDatumUnitFamAnalytification` and not as the fifteen arguments that space
  unfolds to.

## Main results

- `ComplexAnalytic.refineDatumToBase_base_coverIota`: **the morphism down, read at a point of a
  refined member** — the pointwise form of the restriction law the morphism's own file proves,
  which the two halves of the image computation spend in opposite directions.
- `ComplexAnalytic.range_base_refineDatumToBase`: **the image is the union of the images of the
  refined members**, on no hypothesis at all.
- `ComplexAnalytic.surjective_base_refineDatumToBase`: **so the morphism down is surjective when
  the refining family covers.**
- `ComplexAnalytic.surjective_base_refineDatumToBase_iff`: **and it is surjective exactly when that
  union is everything**, which is the converse the sufficient condition does not give.
- `ComplexAnalytic.refineDatumOneCovers`: **the trivial refining family covers at every surjective
  index map**, for every cover datum.
- `ComplexAnalytic.surjective_base_refineDatumOneToBase`: **so the trivial family's witness maps
  onto the cover it refines.**
- `ComplexAnalytic.mem_range_of_refineDatumCovers` and
  `ComplexAnalytic.not_refineDatumCovers_of_notMem_range`: **the condition forces the index map to
  hit every index whose member has a point**, and the contrapositive the witness spends.
- `ComplexAnalytic.dupSurjective_refine` and `ComplexAnalytic.dupNot_refineDatumCovers`: **at two
  copies of one presentation glued along the whole of each, the morphism down is surjective and the
  condition fails.**
- `ComplexAnalytic.dupStrict`: **so the condition is strictly stronger than surjectivity**, the two
  halves at one refining family.
- `ComplexAnalytic.dupPtStrict`: **and the witness is not vacuous** — at the presentation of a
  point, whose analytification has one.
- `ComplexAnalytic.mem_localisationOpen_of_refineDatumCovers_id` and
  `ComplexAnalytic.localisationOpen_eq_top_of_refineDatumCovers_id`: **at an index map that is the
  identity the condition puts every point of a member in `D(fam i)`, so each `D(fam i)` is the
  whole of its member.**
- `ComplexAnalytic.refineDatumCovers_id_of_forall_eq_top` and
  `ComplexAnalytic.refineDatumCovers_id_iff`: **and conversely, so at an identity index map the
  condition *is* that equation** — a biconditional, and not a collapse asserted in prose.
- `ComplexAnalytic.not_refineDatumCovers_id_of_ne_top`: **so one member the family cuts down
  refutes it outright**, which is what a refinement that refines fails on. **Kept as its own name
  though `ComplexAnalytic.refineDatumCovers_id_iff` now subsumes it**, for the reason the section
  header gives.
- `ComplexAnalytic.surjective_base_refineDatumUnitFamToBase_iff`: **and at a family that is a unit
  on each overlap the morphism down is surjective exactly when the images of the refined members
  are everything**, which is the equivalence above read at the arguments a proper refinement has,
  so that a caller does not spell fifteen of them to ask the question.

## What is not here

* **No injectivity, and no claim that anything is an isomorphism.** The image is computed and
  nothing below says a word about fibres. `Oka/Analytification/RefineDatumToBase.lean`'s *"No
  morphism in the other direction, and no claim that this one is an isomorphism"* is untouched in
  both of its halves, and `ComplexAnalytic.not_isIso_refineToBase` — a negative about the
  one-member comparison at a constant `σ` — bears on nothing here, in either direction, for the
  reason that file gives.
* **Nothing about a refining family that is not a unit, beyond the reading at `σ = id`.**
  `Oka/Analytification/RefineDatumUnitFamily.lean` builds the only refinement in this repository
  that cuts its members down. `### The condition at an index map that is the identity` below
  settles **one** of the two questions about it — it was the last section of this file when that
  sentence was written and is no longer, so it is named here rather than counted:
  its index map is the identity and its `D(z)` is a proper open of its chart, so
  `ComplexAnalytic.not_refineDatumCovers_id_of_ne_top` applies and that refinement does **not**
  meet `ComplexAnalytic.RefineDatumCovers`. `OkaTest/RefineDatumUnitFamily.lean` is where that is
  instantiated, and nothing here mentions it.
  **Whether that refinement's `ComplexAnalytic.refineDatumToBase` is surjective is a second
  question and the paragraph above is not evidence about it in either direction** —
  `ComplexAnalytic.dupStrict` is exactly the theorem that the condition is not necessary, so a
  datum that fails it may still have a surjection down. `OkaTest/RefineDatumUnitFamily.lean`
  answers that one too, separately and negatively, through
  `ComplexAnalytic.surjective_base_refineDatumToBase_iff` and a point of the glued space that is in
  the image of neither refined member. **Neither answer is derived from the other**, and nothing
  here is a statement about that refinement in either direction: what this file supplies is the
  general theorem the instance spends.
* **No open cover out of the refined members.** `ComplexAnalytic.coverAnalytificationOpenCover`
  presents the *original* datum's members as an
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover`; the same for the images of the refined members
  would need the `idx` choice and an open-immersion statement for the composite, and nothing below
  supplies either.
* **Nothing that says the refined datum *refines* the original space.**
  `Oka/Analytification/CrossMemberDatum.lean`'s remaining half — that the refined overlaps are cut
  out where `ComplexAnalytic.refineDatumPoly` says they are — is a statement about that definition
  and is not this one; a surjection down is not a refinement of covers.
* **No instance of `### The instance at a family that is a unit on each overlap`.**
  `ComplexAnalytic.refineDatumUnitFamToBase` and its
  equivalence are stated for every cover datum and are spent here at none;
  `OkaTest/RefineDatumUnitFamily.lean` still spells the morphism at fifteen arguments and re-writing
  it through this definition is a separate branch, for the reason the section header gives.
* **Nothing about `ComplexAnalytic.refineDatumUnitFamGlueData`.** That same section names the
  morphism and not the gluing; that the space sits over that glue data is
  `ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace`, which is stated where
  the space is and is quoted here rather than restated.
* **No `Spec` side, no scheme and no `admissible`**, as in the files this one sits beside.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)

/-! ### The condition -/

/-- **The refining family covers**: every point of every member of the original cover lies in a
refined member lying over that member.

**Per member and not per point of the glued space**, which is the design decision this file's
header argues: the members are glued along their overlaps, so a point of the `i`-th member can be
reached through a different member and the glued-space form is strictly weaker. What that weaker
form is equivalent to is `ComplexAnalytic.surjective_base_refineDatumToBase_iff`, and
**`ComplexAnalytic.dupStrict` is the datum at which the two come apart** — so *strictly* is proved
here and not asserted.

**`ComplexAnalytic.coverSpaceHomOfEq` is why no transport appears.** `fam b` is a polynomial in the
variables of `obj (σ b)` and the point is in the `i`-th member, so the containment cannot be stated
without identifying the two members somewhere; `Oka/Analytification/RefineDatumRange.lean` declares
that identification for exactly this problem. -/
def RefineDatumCovers : Prop :=
  ∀ (i : J) (y : coverSpace.{u} obj i), ∃ (b : B) (h : σ b = i)
    (z : coverSpace.{u} obj (σ b)),
      z ∈ localisationOpen.{u} (obj (σ b)).g (fam b) ∧
        (coverSpaceHomOfEq.{u} obj h).base z = y

/-- **The condition forces the index map to hit every index whose member has a point.**

This is the whole of what the per-member form asks beyond the glued-space one, and it is why
`ComplexAnalytic.refineDatumOneCovers` takes `Function.Surjective σ`: a point of the `i`-th member
has to be reached through a refined member lying over `i` itself, and the glued-space form is free
to reach it through any member at all. `ComplexAnalytic.dupStrict` is the datum where that
difference is realised. -/
theorem mem_range_of_refineDatumCovers (h : RefineDatumCovers.{u} obj σ fam) (i : J)
    (y : coverSpace.{u} obj i) : i ∈ Set.range σ :=
  (h i y).imp fun _ hb ↦ hb.fst

/-- **So a missed index with a nonempty member refutes the condition**, which is the form the
witness below spends. -/
theorem not_refineDatumCovers_of_notMem_range (i : J) (y : coverSpace.{u} obj i)
    (hi : i ∉ Set.range σ) : ¬ RefineDatumCovers.{u} obj σ fam :=
  fun h ↦ hi (mem_range_of_refineDatumCovers.{u} obj σ fam h i y)

variable (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (rr : ∀ _ b : B, MvPolynomial (ULift.{u} (Fin ((obj (σ b)).n + 1))) ℂ)
  (uu : ∀ a b : B, (PresentedAlgebra.{u} ((obj (σ b)).n + 1) ((obj (σ b)).k + 1)
    (localisationPresentation.{u} (obj (σ b)).g (poly (σ b) (σ a))))ˣ)
  (he : ∀ a b : B, ∀ _ : σ a ≠ σ b,
    RefineDatumCrossEq.{u} obj σ fam poly q glue a b (rr a b))
  (hu : ∀ a b : B, ∀ _ : σ a ≠ σ b,
    RefineDatumCrossUnit.{u} obj σ fam poly q a b (rr a b) (uu a b))
  (hsym : ∀ i j : J, glue j i = (glue i j).symm)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hq : RefineDatumRangeCross.{u} obj poly σ fam q glue rr uu he hu)
  (hf : RefineDatumRangeEq.{u} obj poly σ fam q glue rr uu he hu)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-! ### The image -/

/-- **The morphism down, read at a point of the `b`-th refined member.**

`ComplexAnalytic.coverIota_comp_refineDatumToBase` with a point applied, which is
`congrArg (fun m ↦ m.toLRSHom.base w)` and nothing else — both `AnalyticSpace`'s composition and
`AnalyticSpace.Hom.toLRSHom` of it are definitional, so no rewrite is involved and none is
available: the equation is between morphisms of `ComplexAnalytic.AnalyticSpace`, and a `simp only`
naming `AlgebraicGeometry.LocallyRingedSpace.comp_base` does not fire on it because the composite
is not syntactically one of that category's.

**A declaration and not a `have` inside the theorem below**, because that theorem spends it once in
each direction and the two occurrences are three lines apart in different branches of an `ext`. -/
theorem refineDatumToBase_base_coverIota (b : B)
    (w : AnalyticSpace.analytification.{u}
      (localisationPresentation.{u} (obj (σ b)).g (fam b))) :
    (refineDatumToBase.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
        hcocycle).toLRSHom.base
        ((coverIota.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q)
          (refineDatumGlue.{u} obj σ fam poly q glue rr uu he hu)
          (refineDatumHrange.{u} obj poly σ fam q glue rr uu he hu hrange hq hf)
          (refineDatumGlue_symm.{u} obj σ fam poly q glue rr uu hsym he hu)
          (refineDatumHcocycle.{u} obj poly σ fam q glue rr uu he hu hrange hq hf hsym hcocycle)
          b).toLRSHom.base w) =
      (coverIota.{u} obj poly glue hrange hsym hcocycle (σ b)).toLRSHom.base
        ((localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom.base w) :=
  congrArg (fun m : AnalyticSpace.analytification.{u}
      (localisationPresentation.{u} (obj (σ b)).g (fam b)) ⟶
        coverAnalytification.{u} obj poly glue hrange hsym hcocycle ↦
      (ConcreteCategory.hom (AnalyticSpace.Hom.toLRSHom m).base) w)
    (coverIota_comp_refineDatumToBase.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
      hcocycle b)

/-- **The image of the morphism down is the union of the images of the refined members**, on no
hypothesis beyond the ones the morphism itself takes — the refining family is arbitrary and the
original datum's laws are read only through the morphism.

`⊆` is `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` at the **refined** glue
data, which puts an arbitrary point of the source in some refined member, followed by
`ComplexAnalytic.range_base_localisationProj_subset`.

`⊇` is `ComplexAnalytic.range_base_localisationProj`, the **equality** and not the containment, and
this is the only place on this line that needs it: a point of `D(fam b)` has to be produced from
the refined member upstairs, which is what the containment cannot do. -/
theorem range_base_refineDatumToBase :
    Set.range (refineDatumToBase.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
        hcocycle).toLRSHom.base =
      ⋃ b : B, (coverIota.{u} obj poly glue hrange hsym hcocycle (σ b)).toLRSHom.base ''
        (localisationOpen.{u} (obj (σ b)).g (fam b) :
          Set (AnalyticSpace.analytification.{u} (obj (σ b)).g)) := by
  ext x
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨b, w, rfl⟩ := (refineDatumGlueDataOfLaws.{u} obj poly σ fam q glue rr uu he hu hrange
      hq hf hsym hcocycle).ι_jointly_surjective v
    exact ⟨b, (localisationProj.{u} (obj (σ b)).g (fam b)).toLRSHom.base w,
      range_base_localisationProj_subset.{u} (obj (σ b)).g (fam b) ⟨w, rfl⟩,
      (refineDatumToBase_base_coverIota.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
        hcocycle b w).symm⟩
  · rintro ⟨b, z, hz, rfl⟩
    obtain ⟨w, rfl⟩ :=
      (Set.ext_iff.1 (range_base_localisationProj.{u} (obj (σ b)).g (fam b)) z).2 hz
    exact ⟨_, refineDatumToBase_base_coverIota.{u} obj poly σ fam q glue rr uu he hu hsym hrange
      hq hf hcocycle b w⟩

/-! ### Surjectivity -/

/-- **The morphism down is surjective when the refining family covers.**

The image above is everything: an arbitrary point of the glued space is in some member by
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective`, the hypothesis puts it in a
refined member over that member, and `ComplexAnalytic.coverSpaceHomOfEq_self` discharges the
identification the hypothesis is stated across once `subst` has eliminated the index.

**The hypothesis enters here and nowhere else**; everything above holds of every refinement. -/
theorem surjective_base_refineDatumToBase (hcov : RefineDatumCovers.{u} obj σ fam) :
    Function.Surjective
      (refineDatumToBase.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
        hcocycle).toLRSHom.base := by
  rw [← Set.range_eq_univ, range_base_refineDatumToBase.{u}]
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ :=
    (coverGlueData.{u} obj poly glue hrange hsym hcocycle).ι_jointly_surjective x
  obtain ⟨b, h, z, hz, rfl⟩ := hcov i y
  subst h
  rw [coverSpaceHomOfEq_self.{u}]
  exact Set.mem_iUnion.2 ⟨b, z, hz, rfl⟩

/-- **And it is surjective exactly when the images of the refined members are everything**, which
is `Set.range_eq_univ` at the image computation.

**This is the converse `ComplexAnalytic.surjective_base_refineDatumToBase` does not give, and the
difference is the point.** `ComplexAnalytic.RefineDatumCovers` is a statement about each member of
the original cover; what
surjectivity is *equivalent* to is the same statement about the glued space, where a point of one
member may be reached through another. So the implication above is strict as stated — that is
`ComplexAnalytic.dupStrict`, and this equivalence is that theorem's first consumer — and this
equivalence is what a caller arguing in the other direction has. -/
theorem surjective_base_refineDatumToBase_iff :
    Function.Surjective
        (refineDatumToBase.{u} obj poly σ fam q glue rr uu he hu hsym hrange hq hf
          hcocycle).toLRSHom.base ↔
      ⋃ b : B, (coverIota.{u} obj poly glue hrange hsym hcocycle (σ b)).toLRSHom.base ''
        (localisationOpen.{u} (obj (σ b)).g (fam b) :
          Set (AnalyticSpace.analytification.{u} (obj (σ b)).g)) = Set.univ := by
  rw [← Set.range_eq_univ, range_base_refineDatumToBase.{u}]

end

/-! ### The instance at the trivial refining family -/

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hsym : ∀ i j : J, glue j i = (glue i j).symm)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
        coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The trivial refining family covers as soon as the index map is surjective**, for every cover
datum.

`ComplexAnalytic.localisationOpen_one` makes `D(1)` the whole member, so nothing is left of the
containment and what remains is that some refined index lie over each original one. The
identification is along `rfl` after the surjectivity has been eliminated, so
`ComplexAnalytic.coverSpaceHomOfEq_refl` closes it.

**This is what stops `ComplexAnalytic.RefineDatumCovers` from being a condition with no instance**,
and it is the trivial end of it: `fam ≡ 1` refines nothing, as
`Oka/Analytification/RefineDatumWitness.lean` says of its own witness in terms, so nothing here is
evidence about a family that cuts a member down. -/
theorem refineDatumOneCovers (hs : Function.Surjective σ) :
    RefineDatumCovers.{u} obj σ (fun _ ↦ (1 : MvPolynomial (ULift.{u} (Fin (obj (σ _)).n)) ℂ)) := by
  intro i y
  obtain ⟨b, rfl⟩ := hs i
  refine ⟨b, rfl, y, ?_, ?_⟩
  · rw [localisationOpen_one.{u}]
    trivial
  · rw [coverSpaceHomOfEq_refl.{u}]
    rfl

/-- **So `Oka/Analytification/RefineDatumWitness.lean`'s witness maps onto the cover it refines**,
for every cover datum and every surjective index map.

The source is `ComplexAnalytic.refineDatumOneAnalytification` — that definition is
`ComplexAnalytic.refineDatumAnalytificationOfLaws` at these arguments, so the two morphisms are the
same term and no bridge is needed. `OkaTest/RefineDatumWitness.lean` instantiates this at `σ = id`
on a three-element index type, where `Function.surjective_id` is the hypothesis. -/
theorem surjective_base_refineDatumOneToBase (hs : Function.Surjective σ) :
    Function.Surjective
      (refineDatumToBase.{u} obj poly σ (fun _ ↦ 1) (fun x y ↦ poly (σ x) (σ y)) glue
        (refineDatumOneR.{u} obj poly σ glue) (refineDatumOneU.{u} obj poly σ glue)
        (refineDatumOneCrossEq.{u} obj poly σ glue) (refineDatumOneCrossUnit.{u} obj poly σ glue)
        hsym hrange (refineDatumOneRangeCross.{u} obj poly σ glue hrange)
        (refineDatumOneRangeEq.{u} obj poly σ glue) hcocycle).toLRSHom.base :=
  surjective_base_refineDatumToBase.{u} obj poly σ _ _ glue _ _ _ _ hsym hrange _ _ hcocycle
    (refineDatumOneCovers.{u} obj σ hs)

/-! ### The condition is strictly stronger, and the datum that shows it

Two copies of one presentation, glued along the whole of each. Every off-diagonal overlap is
`D(1)`, so each member is already the whole gluing and the second one is redundant; an index map
that misses it still gives a surjection and no longer meets the per-member condition.

**The two triple-overlap laws are vacuous here rather than proved.** A two-element index type has
no three pairwise distinct members, which is `ComplexAnalytic.GlueShape.hRange_of_no_three` and
`ComplexAnalytic.GlueShape.hCocycle_of_no_three` — so nothing below is evidence that either law
holds of anything, and a reader should not take this datum as an instance of them. It is a datum
because they cannot be tested at this size, which is the honest reason and is the same one
`OkaTest/ProjectiveLine.lean` gives for its own two-member cover.
-/

section Dup

/-- **A two-element index type**: the smallest one on which a member can be redundant. -/
abbrev dupIdx : Type u := ULift.{u} (Fin 2)

/-- Two of any three of its elements coincide, which is what makes the two triple-overlap
hypotheses vacuous. -/
theorem dup_no_three (i j k : dupIdx.{u}) : i = j ∨ i = k ∨ j = k := by
  obtain ⟨i⟩ := i; obtain ⟨j⟩ := j; obtain ⟨k⟩ := k
  simp only [ULift.up.injEq]
  omega

variable (P : Presentation.{u})

/-- **Both members are `P`.** -/
abbrev dupObj : dupIdx.{u} → Presentation.{u} := fun _ ↦ P

/-- **Every overlap is the whole member**, `D(1)`. This is what makes each member redundant. -/
abbrev dupPoly : ∀ i : dupIdx.{u}, dupIdx.{u} →
    MvPolynomial (ULift.{u} (Fin (dupObj.{u} P i).n)) ℂ := fun _ _ ↦ 1

/-- **The transition is the identity**, the two overlap presentations being the same term. -/
abbrev dupGlue : ∀ i j : dupIdx.{u},
    coverOverlap.{u} (dupObj.{u} P) (dupPoly.{u} P) i j ≅
      coverOverlap.{u} (dupObj.{u} P) (dupPoly.{u} P) j i := fun _ _ ↦ Iso.refl _

theorem dupHsymm (i j : dupIdx.{u}) : dupGlue.{u} P j i = (dupGlue.{u} P i j).symm :=
  (Iso.refl_symm _).symm

theorem dupHrange : GlueShape.HRange.{u} (dupObj.{u} P) (dupPoly.{u} P) (dupGlue.{u} P) :=
  GlueShape.hRange_of_no_three.{u} _ _ _ dup_no_three.{u}

theorem dupHcocycle :
    GlueShape.HCocycle.{u} (dupObj.{u} P) (dupPoly.{u} P) (dupGlue.{u} P) (dupHrange.{u} P) :=
  GlueShape.hCocycle_of_no_three.{u} _ _ _ _ dup_no_three.{u}

/-- **The index map that misses the second member.** -/
def dupSigma : dupIdx.{u} → dupIdx.{u} := fun _ ↦ ULift.up 0

theorem dupCoverOpen_eq_top (i j : dupIdx.{u}) (_h : i ≠ j) :
    coverOpen.{u} (dupObj.{u} P) (dupPoly.{u} P) i j = ⊤ :=
  localisationOpen_one.{u} _

/-- **Each member is already the whole gluing.**

`ComplexAnalytic.surjective_ι_coverGlueData` at `ComplexAnalytic.dupCoverOpen_eq_top`, read through
`ComplexAnalytic.toLRSHom_coverIota`. -/
theorem dupSurjective_coverIota (i : dupIdx.{u}) :
    Function.Surjective
      (coverIota.{u} (dupObj.{u} P) (dupPoly.{u} P) (dupGlue.{u} P) (dupHrange.{u} P)
        (dupHsymm.{u} P) (dupHcocycle.{u} P) i).toLRSHom.base :=
  surjective_ι_coverGlueData.{u} _ _ _ _ _ _ (dupCoverOpen_eq_top.{u} P) i

/-- **The morphism down is surjective at the constant index map.**

`ComplexAnalytic.surjective_base_refineDatumToBase_iff`'s first consumer, spent in the direction
that file says a caller arguing the other way would want: the union of the images is everything
because the single member `ComplexAnalytic.dupSigma` does hit is already everything. -/
theorem dupSurjective_refine :
    Function.Surjective
      (refineDatumToBase.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (fun _ ↦ 1)
        (fun x y ↦ dupPoly.{u} P (dupSigma.{u} x) (dupSigma.{u} y)) (dupGlue.{u} P)
        (refineDatumOneR.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (refineDatumOneU.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (refineDatumOneCrossEq.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (refineDatumOneCrossUnit.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (dupHsymm.{u} P) (dupHrange.{u} P)
        (refineDatumOneRangeCross.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P)
          (dupHrange.{u} P))
        (refineDatumOneRangeEq.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (dupHcocycle.{u} P)).toLRSHom.base := by
  rw [surjective_base_refineDatumToBase_iff.{u}]
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨y, hy⟩ := dupSurjective_coverIota.{u} P (ULift.up 0) x
  refine Set.mem_iUnion.2 ⟨ULift.up 0, ⟨y, ?_, hy⟩⟩
  rw [localisationOpen_one.{u}]
  trivial

/-- **And the condition fails**, at the index the map misses, as soon as that member has a point.

`ComplexAnalytic.not_refineDatumCovers_of_notMem_range` and nothing else. -/
theorem dupNot_refineDatumCovers (y : coverSpace.{u} (dupObj.{u} P) (ULift.up 1)) :
    ¬ RefineDatumCovers.{u} (dupObj.{u} P) dupSigma.{u}
      (fun _ ↦ (1 : MvPolynomial (ULift.{u} (Fin (dupObj.{u} P (dupSigma.{u} _)).n)) ℂ)) := by
  refine not_refineDatumCovers_of_notMem_range.{u} _ _ _ _ y ?_
  rintro ⟨b, hb⟩
  have h : (0 : Fin 2) = 1 := congrArg ULift.down hb
  exact absurd h (by decide)

/-- **So `ComplexAnalytic.RefineDatumCovers` is strictly stronger than surjectivity.**

The two halves **at one refining family**, which is what makes this a statement about the
implication rather than two statements about two families; it is an `And` for that reason and
should stay one. -/
theorem dupStrict (y : coverSpace.{u} (dupObj.{u} P) (ULift.up 1)) :
    Function.Surjective
      (refineDatumToBase.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (fun _ ↦ 1)
        (fun x y ↦ dupPoly.{u} P (dupSigma.{u} x) (dupSigma.{u} y)) (dupGlue.{u} P)
        (refineDatumOneR.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (refineDatumOneU.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (refineDatumOneCrossEq.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (refineDatumOneCrossUnit.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (dupHsymm.{u} P) (dupHrange.{u} P)
        (refineDatumOneRangeCross.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P)
          (dupHrange.{u} P))
        (refineDatumOneRangeEq.{u} (dupObj.{u} P) (dupPoly.{u} P) dupSigma.{u} (dupGlue.{u} P))
        (dupHcocycle.{u} P)).toLRSHom.base ∧
      ¬ RefineDatumCovers.{u} (dupObj.{u} P) dupSigma.{u} (fun _ ↦ 1) :=
  ⟨dupSurjective_refine.{u} P, dupNot_refineDatumCovers.{u} P y⟩

/-- **The presentation of a point**: no variables and no relations. -/
abbrev dupPtPres : Presentation.{u} := ⟨0, 0, Fin.elim0⟩

/-- **Its point**, so that `ComplexAnalytic.dupStrict`'s hypothesis is discharged rather than
carried. The construction is `Oka/Analytification/GlueShape.lean`'s `ctPt` at this presentation:
the empty tuple of coordinates satisfies the empty family of relations. -/
def dupPtPoint : coverSpace.{u} (dupObj.{u} dupPtPres.{u}) (ULift.up 1) :=
  ⟨⟨(fun _ ↦ 0 : ULift.{u} (Fin 0) → ℂ), trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} (dupObj.{u} dupPtPres.{u} (ULift.up 1)).g _).2
      (fun j ↦ j.elim0)⟩

/-- **The strictness on no hypothesis at all**, which is what makes the counterexample a
counterexample rather than a conditional one. -/
theorem dupPtStrict :
    Function.Surjective
      (refineDatumToBase.{u} (dupObj.{u} dupPtPres.{u}) (dupPoly.{u} dupPtPres.{u}) dupSigma.{u}
        (fun _ ↦ 1) (fun x y ↦ dupPoly.{u} dupPtPres.{u} (dupSigma.{u} x) (dupSigma.{u} y))
        (dupGlue.{u} dupPtPres.{u})
        (refineDatumOneR.{u} _ _ dupSigma.{u} (dupGlue.{u} dupPtPres.{u}))
        (refineDatumOneU.{u} _ _ dupSigma.{u} (dupGlue.{u} dupPtPres.{u}))
        (refineDatumOneCrossEq.{u} _ _ dupSigma.{u} (dupGlue.{u} dupPtPres.{u}))
        (refineDatumOneCrossUnit.{u} _ _ dupSigma.{u} (dupGlue.{u} dupPtPres.{u}))
        (dupHsymm.{u} dupPtPres.{u}) (dupHrange.{u} dupPtPres.{u})
        (refineDatumOneRangeCross.{u} _ _ dupSigma.{u} (dupGlue.{u} dupPtPres.{u})
          (dupHrange.{u} dupPtPres.{u}))
        (refineDatumOneRangeEq.{u} _ _ dupSigma.{u} (dupGlue.{u} dupPtPres.{u}))
        (dupHcocycle.{u} dupPtPres.{u})).toLRSHom.base ∧
      ¬ RefineDatumCovers.{u} (dupObj.{u} dupPtPres.{u}) dupSigma.{u} (fun _ ↦ 1) :=
  dupStrict.{u} dupPtPres.{u} dupPtPoint.{u}

end Dup

/-! ### The condition at an index map that is the identity, where it is one equation per member

At `σ = id` the refined family is indexed by the original cover's own index type and the
`∃ b, ∃ h : σ b = i` of the condition can only be answered by `i` itself, so
`ComplexAnalytic.coverSpaceHomOfEq` is an identification of a member with itself and
`ComplexAnalytic.coverSpaceHomOfEq_self` disposes of it. **What is left is that `D(fam i)` be the
whole of the `i`-th member**, and a refining family that cuts a member down is exactly a family
that fails that.

**That is a biconditional and it is proved here as one**,
`ComplexAnalytic.refineDatumCovers_id_iff`. The first draft of this section proved the forward
implication at five sites that read as an equivalence, which is the defect
`ComplexAnalytic.dupStrict` was written to retire one branch earlier and in this same file; the
converse costs one term and the sentences are now true rather than nearly true.

**`ComplexAnalytic.not_refineDatumCovers_id_of_ne_top` keeps its own name although the
equivalence subsumes it**, because it is the form `OkaTest/RefineDatumUnitFamily.lean` spends and
inlining it would put the negation step in a test file. The bullet for it above says so without
naming that file, since a backticked path under `## Main results` is read by
`scripts/guard_coverage.py` as a result this file advertises.

**The three statements below are quantified over `i` rather than proved at an index**, and that is
not a style choice. `ComplexAnalytic.RefineDatumCovers` is stated across an identification of two
members, so at a concrete index `subst` has nothing to eliminate and
`rw [ComplexAnalytic.coverSpaceHomOfEq_self]` fails on a goal reported as *"not type-correct under
the `instances` transparency level"* — the defect `Oka/Analytification/RefineDatumRange.lean`
documents, measured again here. Substituting inside a lemma stated at a variable is what makes
these four lines, and it is the same ordering
`ComplexAnalytic.surjective_base_refineDatumToBase` above is written in.

**None of this is about surjectivity.** `ComplexAnalytic.dupStrict` says the condition is strictly
stronger than the surjectivity of the morphism down, so refuting it at a datum decides nothing
about that morphism at that datum, in either direction. A caller wanting surjectivity has
`ComplexAnalytic.surjective_base_refineDatumToBase_iff` and nothing here.
-/

section CoversId

variable (fam : ∀ b : J, MvPolynomial (ULift.{u} (Fin (obj (id b)).n)) ℂ)

/-- **At an identity index map the condition puts every point of the `i`-th member in `D(fam i)`.**

The condition offers a `b` with `id b = i`, which is `i`, and a point of `D(fam b)` mapping to `y`
along the identification of the two; `subst` turns the first into `rfl` and
`ComplexAnalytic.coverSpaceHomOfEq_self` turns the second into the identity, after which the point
offered *is* `y`. **The `rfl` pattern in the `obtain` is what does the work**: it lands the
identification's value in the goal rather than in a hypothesis, which is why nothing has to be
rewritten in the other direction. -/
theorem mem_localisationOpen_of_refineDatumCovers_id
    (h : RefineDatumCovers.{u} obj id fam) (i : J) (y : coverSpace.{u} obj i) :
    y ∈ localisationOpen.{u} (obj i).g (fam i) := by
  obtain ⟨b, hb, z, hz, rfl⟩ := h i y
  subst hb
  rw [coverSpaceHomOfEq_self.{u}]
  exact hz

/-- **So at an identity index map each refined member is the whole of the member it lies over.**

`eq_top_iff` at the theorem above. This is the form in which the condition is a statement about the
*family* rather than about points, and it is what makes the contrapositive below one line. -/
theorem localisationOpen_eq_top_of_refineDatumCovers_id
    (h : RefineDatumCovers.{u} obj id fam) (i : J) :
    localisationOpen.{u} (obj i).g (fam i) = ⊤ :=
  eq_top_iff.2 fun y _ ↦ mem_localisationOpen_of_refineDatumCovers_id.{u} obj fam h i y

/-- **One member whose `D(fam i)` is a proper open refutes the condition**, at an identity index
map.

The contrapositive of the theorem above, and the form an instance spends: a refinement is a
refinement precisely when some `D(fam i)` is not the whole member, so at `σ = id` a refinement that
refines cannot meet `ComplexAnalytic.RefineDatumCovers`. **That is a fact about the condition and
not about the refinement's morphism down**, for the reason the section header gives. -/
theorem not_refineDatumCovers_id_of_ne_top (i : J)
    (hne : localisationOpen.{u} (obj i).g (fam i) ≠ ⊤) :
    ¬ RefineDatumCovers.{u} obj id fam :=
  fun h ↦ hne (localisationOpen_eq_top_of_refineDatumCovers_id.{u} obj fam h i)

/-- **And conversely: if every `D(fam i)` is the whole member, the condition holds** at an identity
index map.

A term and not a tactic proof, which is the point of writing it this way. The witness is `i`
itself, the identification is along `rfl`, and the last component is
`ComplexAnalytic.coverSpaceHomOfEq_refl` read at a point through `congrArg`.

**The two obvious tactic steps both fail, and they fail for the reason the section header gives.**
`rw [h i]` does not match a goal reading `y ∈ localisationOpen (obj (id i)).g (fam i)`, because
`id i` is not syntactically `i`; and `rw [coverSpaceHomOfEq_self]` does not match either, because
the stored proof has type `id i = i` while the pattern wants `?i = ?i` — the same *"not type-correct
under the `instances` transparency level"* report the forward direction met, in a shape where
nothing is available to `subst`. **A term application unifies at default transparency and neither
step arises**, which is `Oka/Analytification/RefineDatumRange.lean`'s own prescription — the bridge
is `rfl`, so state it with the type written out and let `congrArg` carry it. -/
theorem refineDatumCovers_id_of_forall_eq_top
    (h : ∀ i : J, localisationOpen.{u} (obj i).g (fam i) = ⊤) :
    RefineDatumCovers.{u} obj id fam := fun i y ↦
  ⟨i, rfl, y, (h i).ge trivial,
    congrArg (fun m : coverSpace.{u} obj i ⟶ coverSpace.{u} obj i ↦
      (ConcreteCategory.hom m.base) y) (coverSpaceHomOfEq_refl.{u} obj i)⟩

/-- **So at an identity index map the condition *is* the equation**, and not merely implies it.

The two directions above joined. **This is what the prose of this section says and what its first
draft did not prove**: five sentences read as a biconditional where only `→` was available, which is
the same species as the assertions `ComplexAnalytic.dupStrict` retired one branch earlier in this
file. -/
theorem refineDatumCovers_id_iff :
    RefineDatumCovers.{u} obj id fam ↔
      ∀ i : J, localisationOpen.{u} (obj i).g (fam i) = ⊤ :=
  ⟨localisationOpen_eq_top_of_refineDatumCovers_id.{u} obj fam,
    refineDatumCovers_id_of_forall_eq_top.{u} obj fam⟩

end CoversId

end

/-! ### The instance at a family that is a unit on each overlap

`Oka/Analytification/RefineDatumUnitFamily.lean` builds the refined cover datum at an injective
index map and a family that is a unit on each overlap, and stops at its glue data and its space:
**it does not name the morphism down**, because that morphism is
`ComplexAnalytic.refineDatumToBase` and this file, not that one, is where the trivial family's
counterpart already lives. `ComplexAnalytic.surjective_base_refineDatumOneToBase` is that
counterpart and it is under this file's `### The instance at the trivial refining family`.

**Named and not located**, and deliberately. Every sentence in this section that points at another
part of this file **names its heading** rather than counting positions, so a section appended past
or reordered cannot falsify this paragraph silently and a heading renamed leaves a citation a
`grep` can find. Counting was the defect this subtree has spent several branches on, and the
sentences above were written the counting way first.

**The type of `ComplexAnalytic.refineDatumUnitFamToBase` is the whole point of naming it.** Its
source is written as `ComplexAnalytic.refineDatumUnitFamAnalytification` rather than as the
fifteen arguments that definition unfolds to, so the morphism is tied to the space a caller has a
name for; the two are the same term, because that definition **is**
`ComplexAnalytic.refineDatumAnalytificationOfLaws` at exactly these arguments, and no bridge is
needed. Its target is `ComplexAnalytic.coverAnalytification`, which is the cover it refines.

**The equivalence is what pays for the filing.** Without
`ComplexAnalytic.surjective_base_refineDatumUnitFamToBase_iff` a caller asking whether a proper
refinement covers has to spell fifteen arguments to state the question, and the first instance to
ask it did exactly that.
-/

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hfam : ∀ a b : B, σ a ≠ σ b → IsUnit (Ideal.Quotient.mk (presentationIdeal.{u}
    (localisationPresentation.{u} (obj (σ a)).g (poly (σ a) (σ b))))
    (MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n) (fam a))))
  (hsym : ∀ i j : J, glue j i = (glue i j).symm)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))

/-- **The morphism down at an injective index map and a family that is a unit on each overlap.**

`ComplexAnalytic.refineDatumToBase` with the four cross-member choices taken from
`Oka/Analytification/RefineDatumUnitFamily.lean` and the two range conditions discharged by
`ComplexAnalytic.refineDatumRangeCross_poly` and
`ComplexAnalytic.refineDatumRangeEq_of_injective` — the same fifteen arguments
`ComplexAnalytic.refineDatumUnitFamAnalytification` is built from, in the same order.

**The source is `ComplexAnalytic.refineDatumUnitFamAnalytification` on the nose and the type says
so**, which is the reason this definition exists at all. That space is
`ComplexAnalytic.refineDatumAnalytificationOfLaws` at these arguments by definition, so the
ascription costs nothing and no transport appears — the same argument
`ComplexAnalytic.surjective_base_refineDatumOneToBase` makes for the trivial family, under this
file's `### The instance at the trivial refining family`. Without it a caller states the morphism
at fifteen arguments and ends up with a well-typed term that nothing ties to the space it comes
out of, which is the defect
`ComplexAnalytic.refineDatumUnitFamAnalytification_toLocallyRingedSpace` was written to close on
the other side. -/
def refineDatumUnitFamToBase (hσ : Function.Injective σ)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    refineDatumUnitFamAnalytification.{u} obj poly σ fam glue hfam hsym hrange hσ hcocycle ⟶
      coverAnalytification.{u} obj poly glue hrange hsym hcocycle :=
  refineDatumToBase.{u} obj poly σ fam (fun x y ↦ poly (σ x) (σ y)) glue
    (refineDatumUnitFamR.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamU.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamCrossEq.{u} obj poly σ fam glue hfam)
    (refineDatumUnitFamCrossUnit.{u} obj poly σ fam glue hfam) hsym hrange
    (refineDatumRangeCross_poly.{u} obj poly σ fam glue _ _ _ _ hrange)
    (refineDatumRangeEq_of_injective.{u} obj poly σ fam _ glue _ _ _ _ hσ) hcocycle

/-- **So that morphism is surjective exactly when the images of the refined members are
everything.**

`ComplexAnalytic.surjective_base_refineDatumToBase_iff` read at these arguments, which is what a
caller asking whether a proper refinement covers needs and what it otherwise spells fifteen
arguments to state. **A term application and not a `rw`**: `rw` naming a definition plants its
equation lemma even when the definition is in the same file, whereas unification unfolds
`ComplexAnalytic.refineDatumUnitFamToBase` at default transparency and nothing is generated.

**This is the sufficient condition's converse and not the condition.**
`ComplexAnalytic.RefineDatumCovers` implies surjectivity and `ComplexAnalytic.dupStrict` says it is
not implied by it, so a caller that has refuted the condition at its own datum has learned nothing
about this morphism and has to spend this equivalence instead. -/
theorem surjective_base_refineDatumUnitFamToBase_iff (hσ : Function.Injective σ)
    (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
      coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
        coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
          coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _) :
    Function.Surjective
        (refineDatumUnitFamToBase.{u} obj poly σ fam glue hfam hsym hrange hσ
          hcocycle).toLRSHom.base ↔
      ⋃ b : B, (coverIota.{u} obj poly glue hrange hsym hcocycle (σ b)).toLRSHom.base ''
        (localisationOpen.{u} (obj (σ b)).g (fam b) :
          Set (AnalyticSpace.analytification.{u} (obj (σ b)).g)) = Set.univ :=
  surjective_base_refineDatumToBase_iff.{u} obj poly σ fam _ glue _ _ _ _ hsym hrange _ _ hcocycle

end

end ComplexAnalytic

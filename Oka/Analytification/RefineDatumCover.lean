/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.RefineDatumToBase
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
reproduces: this module's closure is **97** `Oka` modules and **71** Mathlib roots, itself counted
in, against **96** and **71** for either append. **One `Oka` module and no Mathlib root**, which is
the same trade `Oka/Analytification/SpecRefinedChoice.lean` recorded making for its own existence.

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

## Main definitions

- `ComplexAnalytic.RefineDatumCovers`: **the refining family covers** — every point of every member
  of the original cover lies in a refined member lying over that member.

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

## What is not here

* **No injectivity, and no claim that anything is an isomorphism.** The image is computed and
  nothing below says a word about fibres. `Oka/Analytification/RefineDatumToBase.lean`'s *"No
  morphism in the other direction, and no claim that this one is an isomorphism"* is untouched in
  both of its halves, and `ComplexAnalytic.not_isIso_refineToBase` — a negative about the
  one-member comparison at a constant `σ` — bears on nothing here, in either direction, for the
  reason that file gives.
* **Nothing about a refining family that is not a unit.**
  `Oka/Analytification/RefineDatumUnitFamily.lean` builds the only refinement in this repository
  that cuts its members down, and **whether `ComplexAnalytic.lineRefinement` meets
  `ComplexAnalytic.RefineDatumCovers` is untouched here in both directions.** Nothing below is
  evidence either way and no sentence here should be read as one; it is the obvious next question
  and it is a separate subject.
* **No open cover out of the refined members.** `ComplexAnalytic.coverAnalytificationOpenCover`
  presents the *original* datum's members as an
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover`; the same for the images of the refined members
  would need the `idx` choice and an open-immersion statement for the composite, and nothing below
  supplies either.
* **Nothing that says the refined datum *refines* the original space.**
  `Oka/Analytification/CrossMemberDatum.lean`'s remaining half — that the refined overlaps are cut
  out where `ComplexAnalytic.refineDatumPoly` says they are — is a statement about that definition
  and is not this one; a surjection down is not a refinement of covers.
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
form is equivalent to is `ComplexAnalytic.surjective_base_refineDatumToBase_iff`.

**`ComplexAnalytic.coverSpaceHomOfEq` is why no transport appears.** `fam b` is a polynomial in the
variables of `obj (σ b)` and the point is in the `i`-th member, so the containment cannot be stated
without identifying the two members somewhere; `Oka/Analytification/RefineDatumRange.lean` declares
that identification for exactly this problem. -/
def RefineDatumCovers : Prop :=
  ∀ (i : J) (y : coverSpace.{u} obj i), ∃ (b : B) (h : σ b = i)
    (z : coverSpace.{u} obj (σ b)),
      z ∈ localisationOpen.{u} (obj (σ b)).g (fam b) ∧
        (coverSpaceHomOfEq.{u} obj h).base z = y

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
member may be reached through another. So the implication above is strict as stated and this
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

end

end ComplexAnalytic

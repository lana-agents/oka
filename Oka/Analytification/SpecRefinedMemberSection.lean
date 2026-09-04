/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecRefinedMember
import Oka.Analytification.SpecMemberSections

/-!
# The refined member's range, in the section vocabulary

`Oka/Analytification/SpecRefinedMember.lean` builds, for a polynomial `p` in the variables of a
presentation `P` and an open immersion `f` out of `Spec` of `P`'s algebra, an open immersion
`ComplexAnalytic.presentationRefinedIota` into `X`, and
`ComplexAnalytic.opensRange_presentationRefinedIota` says its range is the image under `f` of
`D(p)` — a statement about `Spec` of the presented algebra, transported into `X`. It states both
at a member `i` of a cover datum as well, as `ComplexAnalytic.refinedIota` and
`ComplexAnalytic.opensRange_refinedIota`, each the general form at
`ComplexAnalytic.specSchemeIota`.

`Oka/Analytification/SpecMemberSections.lean` reads the same polynomial the other way, as a
**section of `𝒪_X`** over the immersion's range: `ComplexAnalytic.presentationSection`, whose
`ComplexAnalytic.basicOpen_presentationSection` describes the open it cuts out by the same image,
and `ComplexAnalytic.specSchemeIotaSection` with
`ComplexAnalytic.basicOpen_specSchemeIotaSection` at a member.

**So the two files describe one open twice, and this file says so — at both levels.** The
right-hand sides of the two theorems are the same term, so the equation between the two
descriptions is `Eq.trans` and `Eq.symm` and nothing else — no rewrite under a dependent argument,
and in particular no `rw` at `AlgebraicGeometry.Scheme.Hom.opensRange`, whose `IsOpenImmersion`
argument makes a `rw` at the morphism fail with *"motive is not type correct"*. **The predicted
hazard does not arise because the proof is a term.**

## Why this is a file of its own rather than a line in either of them

`Oka/Analytification/SpecRefinedMember.lean` does not import
`Oka/Analytification/SpecMemberSections.lean` and **states in its own `## What is not here` that
this is a property of it worth having**: `ComplexAnalytic.opensRange_refinedIota` is *"a statement
about the open itself, and stays the usable one for a reader who has not imported that file."*
Appending this theorem there would make that clause false about its own file — the reader of it
would have imported that file — and would cost that module's transitive closure **three `Oka`
modules and one Mathlib root**: `Oka.Analytification.SpecMemberSections`,
`Oka.Analytification.SpecTwoData`, `Oka.AlgebraicGeometry.OpenImmersion` and
`Mathlib.AlgebraicGeometry.OpenImmersion`, taking it from 86 modules and 71 roots to 89 and 72 —
counted with the file itself in, as `scripts/import_cost.py`'s comment-stripping and `IMPORT`
regex read the tree. **This file's own closure is 90 and 72**, which is that same 89 plus this
file, so the reader who wants the bridge pays for both sides and the reader who wants only the
range does not. `lake build` does not grow either way, since both modules are already in
`Oka.lean`'s closure; what grows is what a reader importing one file in isolation pays.

Adding it to `Oka/Analytification/SpecMemberSections.lean` instead is the mirror problem: that
file would gain `Oka.Analytification.SpecRefinedMember`, and its subject is a section over a
member rather than a refinement of one.

**A third module that imports both and states the bridge costs one build job and grows no
existing closure**, which is the same trade `Oka/Analytification/SpecMemberChoice.lean` took for
the analogous one-theorem step, and for the same reason: appending would have falsified a
file-scoped `## What is not here` bullet that is informative about where a line is drawn.

## Two theorems, and why that is not the two spellings this file already declined

**These two are not two names for one statement.** The first is at an **arbitrary** open immersion
and the second is the first at `ComplexAnalytic.specSchemeIota`; they differ in how general the
immersion is, and the general one reaches immersions the specialised one cannot name — a member of
a *second* cover datum carried into the first datum's scheme is
`ComplexAnalytic.specSchemeIotaMap`, and is not `specSchemeIota` of anything in the first datum.
`Oka/Analytification/SpecRefinedMember.lean`'s own two-level section has the argument in full and
this file follows it rather than restating it.

**What this file still declines is the other thing**, which is a *re-spelling at one fixed
immersion*. `ComplexAnalytic.specSchemeIotaSection` is `ComplexAnalytic.presentationSection` at
`ComplexAnalytic.specSchemeIota`, by definition, so the member-level equation below could equally
be stated with `presentationSection` on its right-hand side; that statement differs from the one
below by unfolding a `def` and is one `rfl` away for a reader who wants it. **It is not stated**,
for the reason `ComplexAnalytic.specSchemeIotaSection` exists at all and gives in its own
docstring: a caller holding a cover datum and an index should not have to spell the six arguments
of the general form, and `Oka/Analytification/SpecMemberSections.lean` already argues against
stating both. **Generality in the immersion is content; a second name at one immersion is not.**

**Two backticked names and no file path in the `## Main results` block below, and that is
deliberate rather than terse**: `scripts/guard_coverage.py` reads every whitespace-free backticked
token under that heading as a declaration this file advertises, and a file path resolves to
nothing and moves a census row for no reason. The files these theorems bridge are named in the
paragraphs above, which is where the extractor does not look — and this paragraph is above the
heading for the same reason.

## The overlap of two refined members at one immersion, and the sentence it narrows

Two files on this line say, in two spellings, that what a cover **datum** additionally needs over
an affine open cover is `poly`, the three laws, and *the condition that every pairwise overlap be a
distinguished open of each of the two members it lies in* — and that **that** is what the points of
`X` cannot supply. `Oka/Analytification/SpecMemberChoice.lean` and
`Oka/Analytification/SpecRefinedCover.lean` are the two, and both sentences are now narrowed rather
than deleted, because their true half is what makes the remaining piece work.

**At two refined members of the *same* immersion the overlap is a refined member of that
immersion again, at the product of the two polynomials.** Both chosen sections are sections over
one open — the immersion's range — so `AlgebraicGeometry.Scheme.basicOpen_mul` applies on the nose
and the overlap is cut out by `p * q`, a polynomial in the **ambient** member's variables. The
other reading of the same fact puts the overlap inside the *refined* member rather than the ambient
one, and that is `AlgebraicGeometry.Scheme.basicOpen_res` with **no affineness hypothesis at all**.

**That is not yet the doubly-distinguished condition at such a pair, and what is missing is a
rename and a symmetry.** The condition quantifies over the two members the overlap lies in — here
`D(p)` and `D(q)` — and asks for a polynomial in *each* of their own variables.
`ComplexAnalytic.presentationRefinedPres` gives `D(p)` a presentation with one variable more than
`P`'s, so `p * q` is not a polynomial on `D(p)` at all and does not typecheck there. What is here
at `D(p)` is `ComplexAnalytic.basicOpen_res_presentationSection`, which cuts the overlap out of
`D(p)` by `ComplexAnalytic.presentationSection` of `q` restricted — the condition's content at that
member in the vocabulary of *sections*. The same at `D(q)` is that theorem with the two polynomials
exchanged and is not stated, and the polynomial spelling at either member would come from the
other's polynomial along the map `ComplexAnalytic.localisationIncl` names. **So the same-member
half is two steps short of a `poly` entry rather than none**, and neither step is taken below.

**At two refined members of different immersions nothing here applies and none of it is claimed.**
The two sections live over different opens, so `AlgebraicGeometry.Scheme.basicOpen_mul` does not
typecheck and `AlgebraicGeometry.Scheme.basicOpen_res` has no containment to restrict along. What
is available there is `AlgebraicGeometry.exists_basicOpen_le_affine_inter`'s **pointwise**
statement — at each point of the intersection there is *some* doubly-distinguished open containing
it — which `Oka/Analytification/SpecRefinedChoice.lean` already spends and which does not say the
overlap *itself* is distinguished. That is the half those two sentences are right about.

**The same split is on record one level down**, and a reader estimating from these three theorems
should have it: for a one-datum refinement of an analytic cover, the same-member overlaps are
`Oka/Analytification/LocalisationComposite.lean`'s `D(f₁) ∩ D(f) = D(f₁·f)` at the presentation
level, and the cross-member ones need the original transition transported through two
localisations. **The two halves are not the same size, and it is the first that this file is
about** — short of a `poly` entry by the two steps above, where the second is short of one by an
amount nobody has measured.

## Main results

- `ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen`: **the range of the refined
  immersion is the basic open of the section attached to the same polynomial** — one open, named
  on the left in the vocabulary of the file that builds the immersion and on the right in the
  vocabulary of the file that reads the same polynomial as a section.
- `ComplexAnalytic.opensRange_refinedIota_eq_basicOpen`: **the same at a member of a cover
  datum**, which is the previous theorem at that member's own inclusion and nothing else.
- `ComplexAnalytic.presentationSection_mul`: **the section a product of polynomials names is the
  product of the sections they name**, which is the algebra step of the next theorem stated apart
  from its geometry.
- `ComplexAnalytic.opensRange_presentationRefinedIota_inf`: **the overlap of two refined members at
  one immersion is a refined member at that immersion**, at the product of the two polynomials —
  a statement about the member the two sit inside, and not about either of the two members the
  overlap lies in, for the reason the section above gives.
- `ComplexAnalytic.basicOpen_res_presentationSection`: **and that overlap is a distinguished open
  of the first refined member itself**, cut out by the second section restricted to it — which is
  the doubly-distinguished condition at that one of the two members, in the vocabulary of sections
  and not of polynomials.

## What is not here

* **No affineness theorem in the section vocabulary**, at either level, and in particular nothing
  restating `ComplexAnalytic.isAffineOpen_presentationRefinedIota` or
  `ComplexAnalytic.isAffineOpen_refinedIota` as *the basic open of that section is an affine open
  of `X`*. It does follow, in one `Eq.mpr` on
  `ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen`, and it is left out on purpose:
  nothing asks for it, and a caller that wants it rewrites with that theorem in the direction
  it needs rather than reading a third name off this file.
* **No `poly`, no `glue`, and none of a cover datum's three laws**, so nothing here is or produces
  a common refinement — that is `Oka/Analytification/CrossMemberDatum.lean`,
  `Oka/Analytification/CrossMemberDatumGlue.lean` and the `Oka/Analytification/RefineDatum*.lean`
  files. **Nothing here is a cover datum and nothing here claims to refine one**: the three
  overlap theorems are at **one** immersion and **two** polynomials, and a `poly` is a function of
  two *indices* satisfying three laws. **The gap between them is not arithmetic, and it is not
  confined to the pairs whose two members are different.** A `poly` entry at a pair of refined
  members is a polynomial in each of *their* variables, and
  `ComplexAnalytic.opensRange_presentationRefinedIota_inf` names one in the ambient member's — so
  even at a same-member pair two things are missing: the rename
  `ComplexAnalytic.localisationIncl` names, and the companion of
  `ComplexAnalytic.basicOpen_res_presentationSection` at the second member. At a pair whose two
  members are different none of the three applies at all, and **that** is the half nobody has
  sized.
* **Nothing about overlaps of three or more.** The overlap theorem above is stated at two
  polynomials; the triple overlaps a `hcocycle` quantifies over are not here, and iterating it is
  not the same as stating the law.
* **Nothing indexed by the points of `X`.**
  `ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`
  (`Oka/Analytification/SpecMemberChoice.lean`) is a family and it is indexed by points, which is
  not a cover datum's index type; the theorems below are at one immersion and one polynomial and
  neither is a refinement of that family.
* **No second cover datum.** `ComplexAnalytic.specSchemeIotaMap` and
  `Oka/Analytification/SpecTwoData.lean`'s two-datum vocabulary do not appear, even though the
  import above makes them reachable. **What the general theorem changes is that such a morphism is
  now a legal argument, which is not the same as appearing**: no *statement* below mentions a
  second datum, quantifies over one, or says anything about two.
* **Nothing analytic.** No analytification, no `X^an`, no comparison morphism.
* **Nothing about `p` being non-zero, or the open being non-empty.** At `p = 0` both sides are the
  empty open and both theorems stay true.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

section

variable {X : Scheme.{u}} {P : Presentation.{u}} (f : Spec (CommRingCat.of P.alg) ⟶ X)
  [IsOpenImmersion f]

/-- **The range of the refined immersion is the basic open of the section the same polynomial
names.**

`ComplexAnalytic.opensRange_presentationRefinedIota` describes that range as `f ''ᵁ D(p)`, and
`ComplexAnalytic.basicOpen_presentationSection` describes `X.basicOpen (presentationSection f p)`
by the same expression. **The two right-hand sides are literally the same term**, so this is
`Eq.trans` of the first with the symmetric form of the second and there is nothing else in it.

**Stated as a term rather than by rewriting, and that is not only a style choice.**
`AlgebraicGeometry.Scheme.Hom.opensRange` takes an `AlgebraicGeometry.IsOpenImmersion` argument,
so a `rw` at the morphism under it fails with *"motive is not type correct"* and needs a
`simp only`; composing the two equations sidesteps the question, since neither side is ever
rewritten under that argument.

**What it buys is that a caller who has chosen `p` to cut out a particular open of `X` can name
the affine open `ComplexAnalytic.isAffineOpen_presentationRefinedIota` gives it in the vocabulary
the choice was made in**, without transporting anything: the section is a section of `𝒪_X`, and
the open is one of its basic opens. **The immersion being arbitrary is what makes that available
on both sides of a two-datum choice**, where one member is a `ComplexAnalytic.specSchemeIota` and
the other is not. -/
theorem opensRange_presentationRefinedIota_eq_basicOpen
    (p : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    (presentationRefinedIota.{u} f p).opensRange = X.basicOpen (presentationSection.{u} f p) :=
  (opensRange_presentationRefinedIota.{u} f p).trans
    (basicOpen_presentationSection.{u} f p).symm

/-! #### And the overlap of two of them, at one immersion -/

/-- **The section a product of polynomials names is the product of the sections they name.**

`ComplexAnalytic.presentationSection` is `AlgebraicGeometry.IsOpenImmersion.specΓIsoTop` applied to
`Ideal.Quotient.mk` of the polynomial, and both are ring homomorphisms, so this is `map_mul` twice
and nothing else.

**Stated because the next theorem is about the *open* and this is about the *section*.** A reader
checking that the overlap below is cut out by the product wants to see the algebra step separately
from the geometric one; folding them into one proof would leave the geometric step's content —
`AlgebraicGeometry.Scheme.basicOpen_mul` — sharing a line with a rewrite that has nothing to do
with it. -/
theorem presentationSection_mul (p q : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    presentationSection.{u} f (p * q) =
      presentationSection.{u} f p * presentationSection.{u} f q :=
  (congrArg (IsOpenImmersion.specΓIsoTop f).hom
      (map_mul (Ideal.Quotient.mk (presentationIdeal.{u} P.g)) p q)).trans (map_mul _ _ _)

/-- **The overlap of two refined members at one immersion is a refined member at that immersion**,
at the product of the two polynomials.

`AlgebraicGeometry.Scheme.basicOpen_mul` read through
`ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen` at all three polynomials, with
`ComplexAnalytic.presentationSection_mul` closing the algebra step. The two sections are sections
over **the same** open — the immersion's range — which is the whole hypothesis and the whole
limitation.

**What this settles and what it does not.** A cover datum requires every pairwise overlap of
members to be a distinguished open of *each* of the two members it lies in, cut out by a polynomial
in that member's own variables. The two members here are `D(p)` and `D(q)`, and `p * q` is a
polynomial in **`f`'s** variables and not in theirs: `ComplexAnalytic.presentationRefinedPres`
gives `D(p)` a presentation with one variable more, so `p * q` does not typecheck as a polynomial
on it. **So this is the condition's shape at the member the two sit inside, and not the condition
at either of the two members it quantifies over** — for the second of those see
`ComplexAnalytic.basicOpen_res_presentationSection` below, and this file's `## What is not here`
for what is still missing after it. `Oka/Analytification/SpecMemberChoice.lean` and
`Oka/Analytification/SpecRefinedCover.lean` say that condition is what the points of `X` cannot
supply; their sentences are now narrowed to say which half of it is a rename and a symmetry away
and which half nobody has sized, and this theorem is why there are two halves.

**Nothing here is a `poly`.** A cover datum's `poly` is a function of *two indices* satisfying
three laws, and this is one equation at one immersion and two polynomials; see this file's
`## What is not here`. -/
theorem opensRange_presentationRefinedIota_inf (p q : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    (presentationRefinedIota.{u} f p).opensRange ⊓ (presentationRefinedIota.{u} f q).opensRange =
      (presentationRefinedIota.{u} f (p * q)).opensRange := by
  rw [opensRange_presentationRefinedIota_eq_basicOpen,
    opensRange_presentationRefinedIota_eq_basicOpen,
    opensRange_presentationRefinedIota_eq_basicOpen, presentationSection_mul,
    Scheme.basicOpen_mul]

/-- **And that overlap is a distinguished open of the first refined member itself**, cut out by the
second section restricted to it.

`AlgebraicGeometry.Scheme.basicOpen_res` at the inclusion `AlgebraicGeometry.Scheme.basicOpen_le`
gives, and **it has no affineness hypothesis at all**: the statement is about a scheme's basic
opens and nothing about presentations, cover data or affine members enters it.

**Why both this and the theorem above.** That one says the overlap is distinguished in the
*ambient* member, in the vocabulary of polynomials, which is the vocabulary a cover datum's `poly`
is written in; this one says it is distinguished in `D(p)`, which is one of the two members the
overlap actually lies in, in the vocabulary of sections, and that is the form a caller holding one
refined member and wanting to cut it down again needs. **The two are about different members**, so
neither implies the other and neither implies the other's spelling. The companion at `D(q)` is this
theorem with `p` and `q` exchanged and is not stated; nor is either of them in the polynomial
vocabulary the condition is written in. -/
theorem basicOpen_res_presentationSection (p q : MvPolynomial (ULift.{u} (Fin P.n)) ℂ) :
    X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le (presentationSection.{u} f p))).op
        (presentationSection.{u} f q)) =
      X.basicOpen (presentationSection.{u} f p) ⊓ X.basicOpen (presentationSection.{u} f q) :=
  Scheme.basicOpen_res _ _ _

end

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj poly i j k ≫ specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j k : Set (specSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      specTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The range of the refined member's inclusion is the basic open of the section the same
polynomial names.**

`ComplexAnalytic.opensRange_presentationRefinedIota_eq_basicOpen` at
`ComplexAnalytic.specSchemeIota`. What the specialisation adds is the index: the general form
names the open by a morphism the reader has to supply, and here both sides are named by a member
of this cover datum — `ComplexAnalytic.specSchemeIotaSection` on the right, which is
`ComplexAnalytic.presentationSection` at the same immersion by definition, so the term closes the
difference definitionally and nothing is rewritten.

**What it buys is that a caller who has chosen `p` to cut out a particular open of `X` — which is
what `ComplexAnalytic.exists_mvPolynomial_basicOpen_specSchemeIota_inter` produces — can name the
affine open `ComplexAnalytic.isAffineOpen_refinedIota` gives it in the vocabulary the choice was
made in**, without transporting anything: the section is a section of `𝒪_X`, and the open is one
of its basic opens. -/
theorem opensRange_refinedIota_eq_basicOpen (i : J)
    (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p).opensRange =
      (specScheme.{u} obj poly glue hrange hsymm hcocycle).basicOpen
        (specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle i p) :=
  opensRange_presentationRefinedIota_eq_basicOpen.{u}
    (specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i) p

end

end ComplexAnalytic

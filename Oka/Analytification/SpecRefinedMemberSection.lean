/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecRefinedMember
import Oka.Analytification.SpecMemberSections

/-!
# The refined member's range, in the section vocabulary

`Oka/Analytification/SpecRefinedMember.lean` builds, for a member `i` of a cover datum and a
polynomial `p` in that member's own variables, an open immersion
`ComplexAnalytic.refinedIota` into the glued scheme `X`, and
`ComplexAnalytic.opensRange_refinedIota` says its range is the image under the member's inclusion
of `D(p)` — a statement about `Spec` of the member's algebra, transported into `X`.

`Oka/Analytification/SpecMemberSections.lean` reads the same polynomial the other way, as a
**section of `𝒪_X`** over the member's range: `ComplexAnalytic.specSchemeIotaSection`, whose
`ComplexAnalytic.basicOpen_specSchemeIotaSection` describes the open it cuts out by the same
image.

**So the two files describe one open twice, and this file says so.** The right-hand sides of the
two theorems are the same term, so the equation between the two descriptions is
`Eq.trans` and `Eq.symm` and nothing else — no rewrite under a dependent argument, and in
particular no `rw` at `AlgebraicGeometry.Scheme.Hom.opensRange`, whose `IsOpenImmersion` argument
makes a `rw` at the morphism fail with *"motive is not type correct"*. **The predicted hazard does
not arise because the proof is a term.**

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

## One name and not two

`ComplexAnalytic.specSchemeIotaSection` is `ComplexAnalytic.presentationSection` at
`ComplexAnalytic.specSchemeIota`, by definition, so the same equation reads in either vocabulary
and the two statements differ by unfolding a `def`. **The cover-datum-level name is the one
stated**, for the reason `ComplexAnalytic.specSchemeIotaSection` exists at all and gives in its
own docstring: a caller holding a cover datum and an index should not have to spell the six
arguments of the general form. The general-form spelling is one `rfl` away for a reader who wants
it, and `Oka/Analytification/SpecMemberSections.lean` already argues against stating both.

**One backticked name and no file path in the `## Main results` block below, and that is
deliberate rather than terse**: `scripts/guard_coverage.py` reads every whitespace-free backticked
token under that heading as a declaration this file advertises, and a file path resolves to
nothing and moves a census row for no reason. The two files this theorem bridges are named in the
paragraphs above, which is where the extractor does not look — and this paragraph is above the
heading for the same reason.

## Main results

- `ComplexAnalytic.opensRange_refinedIota_eq_basicOpen`: **the range of the refined member's
  inclusion is the basic open of the section attached to the same polynomial** — one open, named
  on the left in the vocabulary of the file that builds the immersion and on the right in the
  vocabulary of the file that reads the same polynomial as a section.

## What is not here

* **No second theorem in the section vocabulary**, and in particular nothing restating
  `ComplexAnalytic.isAffineOpen_refinedIota` as *the basic open of that section is an affine open
  of `X`*. It does follow, in one `Eq.mpr` on the theorem below, and it is left out on purpose:
  nothing asks for it, and a caller that wants it rewrites with the theorem below in the direction
  it needs rather than reading a second name off this file.
* **No `poly`, no `glue`, and none of a cover datum's three laws**, so nothing here is or produces
  a common refinement — that is `Oka/Analytification/CrossMemberDatum.lean`,
  `Oka/Analytification/CrossMemberDatumGlue.lean` and the `Oka/Analytification/RefineDatum*.lean`
  files. **Nothing here is a cover datum and nothing here claims to refine one**: `i` and `p` are
  one member and one polynomial, exactly as in the file this refines.
* **Nothing indexed by the points of `X`.**
  `ComplexAnalytic.exists_family_mvPolynomial_basicOpen_specSchemeIotaMap`
  (`Oka/Analytification/SpecMemberChoice.lean`) is a family and it is indexed by points, which is
  not a cover datum's index type; the theorem below is at one index and one polynomial and is not
  a refinement of that family.
* **No second cover datum.** `ComplexAnalytic.specSchemeIotaMap` and
  `Oka/Analytification/SpecTwoData.lean`'s two-datum vocabulary do not appear, even though the
  import above makes them reachable.
* **Nothing analytic.** No analytification, no `X^an`, no comparison morphism.
* **Nothing about `p` being non-zero, or the open being non-empty.** At `p = 0` both sides are the
  empty open and the theorem stays true.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

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

`ComplexAnalytic.opensRange_refinedIota` describes that range as
`ComplexAnalytic.specSchemeIota i ''ᵁ D(p)`, and
`ComplexAnalytic.basicOpen_specSchemeIotaSection` describes
`X.basicOpen (ComplexAnalytic.specSchemeIotaSection i p)` by the same expression. **The two
right-hand sides are literally the same term**, so this is `Eq.trans` of the first with the
symmetric form of the second and there is nothing else in it.

**Stated as a term rather than by rewriting, and that is not only a style choice.**
`AlgebraicGeometry.Scheme.Hom.opensRange` takes an `AlgebraicGeometry.IsOpenImmersion` argument,
so a `rw` at the morphism under it fails with *"motive is not type correct"* and needs a
`simp only`; composing the two equations sidesteps the question, since neither side is ever
rewritten under that argument.

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
  (opensRange_refinedIota.{u} obj poly glue hrange hsymm hcocycle i p).trans
    (basicOpen_specSchemeIotaSection.{u} obj poly glue hrange hsymm hcocycle i p).symm

end

end ComplexAnalytic

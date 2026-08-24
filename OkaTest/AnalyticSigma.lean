/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.ProjectiveLine

/-!
# Non-vacuity of the disjoint union of complex analytic spaces

`ComplexAnalytic.AnalyticSpace.sigma` builds an analytic space out of a family of them. Two
readings would make that say nothing, and they are at opposite ends of the index type.

* **It might return one of its members**, or some fixed space, whatever the family. The check is
  on the carrier: at **two copies of the affine line** the inclusion of one member misses the
  other member's origin, so it is not surjective on points —
  `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base` applied to
  `ComplexAnalytic.lineOrigin`. `OkaTest/ProjectiveLine.lean` is where that point and the space
  come from; nothing about `ℙ¹` is used, only the affine line and a point of it.
* **It might be empty**, whatever the family, which the first check does not exclude — a
  construction returning the empty space for every family passes nothing about surjectivity
  because there is nothing to be surjective onto. `sigma_empty_isEmpty` is the other end and it
  says the empty family really does give the empty space, so the two together pin the carrier
  from both sides.

The pair is the analogue of the two readings `OkaTest/LocallyRingedSpaceCoproduct.lean` closes one
level down, and of `OkaTest/ProjectiveLine.lean`'s *"neither `⊤` nor `⊥`"*.

## What is not checked here

**That the disjoint union is not isomorphic to one of its members.** The statements below are
about the carrier and about one map; two analytic spaces with different carriers can still be
isomorphic to a third, and no invariant is computed anywhere in this repository that would settle
it. `OkaTest/AffineCover.lean` and `OkaTest/ProjectiveLine.lean` say the same about their own
gluings.

**Nothing about `ComplexAnalytic.AnalyticSpace.IsFinite`, `…IsLocalIso` or a count of sheets**,
for the inclusions or for the trivial `n`-sheeted cover `∐_{Fin n} X ⟶ X`. Those are the next
step and none of them is touched here.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry ComplexAnalytic

universe u

namespace OkaTest.AnalyticSigma

noncomputable section

/-- Two copies of the affine line, as a family of analytic spaces. -/
abbrev twoLines : pair.{u} → AnalyticSpace.{u} :=
  fun _ ↦ AnalyticSpace.analytification.{u} lineRel.{u}

/-- **The disjoint union of two copies of the affine line is not one of them**: the inclusion of
the first copy misses the origin of the second, so it is not surjective on points.

Both hypotheses of `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base` are supplied and
both are needed — a one-member family would make the inclusion surjective, and so would a second
member with no points. -/
theorem not_surjective_sigmaι_twoLines :
    ¬ Function.Surjective
      (AnalyticSpace.sigmaι.{u} twoLines.{u} (ULift.up 0)).toLRSHom.base :=
  AnalyticSpace.not_surjective_sigmaι_base.{u} twoLines.{u}
    (i := ULift.up 0) (j := ULift.up 1) (by decide) lineOrigin.{u}

/-- **The disjoint union of the empty family is empty.**

The other end of the non-vacuity, and the reading the statement above cannot close: a construction
returning the empty space for every family would satisfy it vacuously. -/
theorem sigma_empty_isEmpty (F : ULift.{u} Empty → AnalyticSpace.{u}) :
    IsEmpty (AnalyticSpace.sigma.{u} F) :=
  AnalyticSpace.isEmpty_sigma.{u} F

/-- **The disjoint union's `ℂ`-algebra structure restricts to each member's**, at the two lines.

The round trip, instantiated: this is what says the object is the disjoint union and not an
unrelated space with the right carrier, and it is the hypothesis-free form, since
`ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma` needs nothing about the family. -/
theorem comapAlgMap_sigma_twoLines (j : pair.{u}) :
    LocallyRingedSpace.comapAlgMap ((AnalyticSpace.sigmaCover.{u} twoLines.{u}).map j)
        (AnalyticSpace.sigma.{u} twoLines.{u}).algebraMap = (twoLines.{u} j).algebraMap :=
  AnalyticSpace.comapAlgMap_sigma.{u} twoLines.{u} j

end

end OkaTest.AnalyticSigma

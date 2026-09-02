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

**`ComplexAnalytic.AnalyticSpace.IsFinite` and `…IsLocalIso` for the inclusions are settled, and
not here.** The section on the trivial cover below is about the descent map `∐_{i : ι} X ⟶ X` and
says nothing about `ComplexAnalytic.AnalyticSpace.sigmaι`;
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι`
(`Oka/AnalyticSpace/SigmaFiniteEtale.lean`) is the statement for the inclusion, and it holds for
**every** family with no hypothesis on the other members. **This bullet used to say an inclusion
is *not* finite unless the other members are empty, *"since its image is not closed in general"*,
and both the claim and its reason were wrong**: the members of a coproduct are pairwise disjoint,
so each image is the complement of a union of opens and is **clopen** —
`ComplexAnalytic.AnalyticSpace.isClosed_range_sigmaι_base`. What an inclusion is *not* is
**surjective**, which is `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base`, is true, and
is a different statement from not being finite.

## The trivial cover, and what the count is a test of

`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` computes the number of sheets of
`∐_{i : ι} X ⟶ X` for every `ι` and every `X`, so an instance of it is not a test of the
arithmetic — it is a test that the general statement has a **non-vacuous** instance at a space
this repository can exhibit, which `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` needs, and that
the `ULift` bookkeeping between `Fin n` and the `Type u` index of
`ComplexAnalytic.AnalyticSpace.sigma` closes. `n = 0` is instantiated with the others because it
is the case a definition could reasonably have excluded, and this development does not:
`Oka/AnalyticSpace/SigmaFiniteEtale.lean` says why.
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

/-! ### The trivial `n`-sheeted cover of the affine line -/

/-- The affine line, as the analytic space the trivial covers below are taken of. -/
abbrev line : AnalyticSpace.{u} := AnalyticSpace.analytification.{u} lineRel.{u}

/-- **The trivial `n`-sheeted cover of the affine line is finite étale**, for every `n`.

The instance `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold` at `ULift (Fin n)`, whose
`Finite` hypothesis is found by instance search. Nothing about the affine line is used and nothing
about `n` is assumed — in particular **not** `0 < n`. -/
theorem isFiniteEtale_sigmaFold_line (n : ℕ) :
    AnalyticSpace.IsFiniteEtale (AnalyticSpace.sigmaFold.{u} (ULift.{u} (Fin n)) line.{u}) :=
  inferInstance

/-- **Every fibre of the trivial `n`-sheeted cover of the affine line has `n` points.**

`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` with the index type's cardinality computed:
`Nat.card (ULift (Fin n))` is `n`. This is the first witness in this repository at which the
number of sheets of a finite étale morphism is a value other than `2`, and it is a witness at
**every** value. -/
theorem card_fiber_sigmaFold_line (n : ℕ) (x : line.{u}) :
    Nat.card ((AnalyticSpace.sigmaFold.{u} (ULift.{u} (Fin n)) line.{u}).toLRSHom.base ⁻¹' {x})
      = n := by
  rw [AnalyticSpace.card_fiber_sigmaFold, Nat.card_ulift, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **At `n = 0` the source of the trivial cover is empty**, which is the case the count above
could have been read as vacuous at.

`ComplexAnalytic.AnalyticSpace.isEmpty_sigma` at the empty index type. Together with
`OkaTest.AnalyticSigma.card_fiber_sigmaFold_line` at `n = 0` this says the empty analytic space
is finite étale over the affine line with no sheets, rather than that the statement fails to
apply. -/
theorem isEmpty_sigmaFold_line_zero :
    IsEmpty (AnalyticSpace.sigma.{u} (fun _ : ULift.{u} (Fin 0) ↦ line.{u})) :=
  AnalyticSpace.isEmpty_sigma.{u} _

/-- **At `n = 1` the fibres are singletons.**

Recorded beside `n = 0` and `n = 2` because it is the case in which the fold map is a bijection on
points; **it is not stated to be an isomorphism**, which would be a claim about the structure
sheaves and is not proved anywhere. -/
theorem card_fiber_sigmaFold_line_one (x : line.{u}) :
    Nat.card ((AnalyticSpace.sigmaFold.{u} (ULift.{u} (Fin 1)) line.{u}).toLRSHom.base ⁻¹' {x})
      = 1 :=
  card_fiber_sigmaFold_line.{u} 1 x

/-- **At `n = 2` the fibres have two points**, which is the value
`ComplexAnalytic.card_fiber_base_sq` reaches for the squaring map of the punctured line by a
completely different argument — one about roots in `ℂ`.

The two morphisms are not isomorphic and nothing here says they are: this one has a disconnected
source and that one does not. What the pair shows is that the value `2` in
`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` is realised twice over, once with
analysis in the proof and once without. -/
theorem card_fiber_sigmaFold_line_two (x : line.{u}) :
    Nat.card ((AnalyticSpace.sigmaFold.{u} (ULift.{u} (Fin 2)) line.{u}).toLRSHom.base ⁻¹' {x})
      = 2 :=
  card_fiber_sigmaFold_line.{u} 2 x

end

end OkaTest.AnalyticSigma

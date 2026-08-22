/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.PullbackModulesStalk
import Oka.Analytification.PresentationFlatness
import Oka.Analytification.Sheaf
import OkaTest.Analytification

/-!
# `Hom.pullbackModulesStalkIso` applies to the analytification, and meets the flatness

`Oka/AnalyticSpace/PullbackModulesStalk.lean` is general theory about locally ringed spaces with
no consumer inside it. The risk with a general theorem is not that it is degenerate — it is
quantified over every morphism and every sheaf, so there is nothing to degenerate to — but that
it is **inapplicable**, in the specific way this development keeps meeting: the site of
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf` is spelled `↑Y.toPresheafedSpace`, and a
statement phrased at any other spelling elaborates and then fails instance search.

The first two `example`s below are that check, at the comparison morphism `X^an ⟶ Spec A` and
then at the node.

**The third is the one that matters.** `ComplexAnalytic.analytificationSheaf` is the pullback
along that morphism, so `Hom.pullbackModulesStalkIso` computes it on stalks as a base change
along `(ComplexAnalytic.analytificationToSpec g).stalkMap y` — and that is *syntactically the
same ring homomorphism* that
`ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec` is about. The two halves of
GAGA's local input therefore compose with nothing in between, which is the fact the exactness
argument needs and the one thing about this file that could have gone wrong.

**What is not here is exactness.** The isomorphism consumes no flatness and needs none; the
flatness in the third example is not used by the first two. Putting them together is GAGA.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The analytification of a sheaf, on stalks.** The general theorem applies at the comparison
morphism, with the site spelled as `ringSheaf` spells it. -/
def analytificationSheafStalkIso
    (y : (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace) :
    analytificationSheaf.{u} g ⋙
        (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.stalkFunctor y ≅
      (Spec.locallyRingedSpaceObj
            (CommRingCat.of
              (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).stalkFunctor
          ((analytificationToSpec.{u} g).base y) ⋙
        ModuleCat.extendScalars ((analytificationToSpec.{u} g).stalkMap y).hom :=
  (analytificationToSpec.{u} g).pullbackModulesStalkIso y

/-- The same at the node, at the origin: `ℂ[x, y] ⧸ (x y)`, whose ideal is not zero and whose
space is not smooth. -/
def nodeAnalytificationSheafStalkIso :
    analytificationSheaf.{u} nodeG.{u} ⋙
        (AnalyticSpace.analytification.{u} nodeG.{u}).toLocallyRingedSpace.stalkFunctor
          originNode.{u} ≅
      (Spec.locallyRingedSpaceObj
            (CommRingCat.of
              (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸
                presentationIdeal.{u} nodeG.{u}))).stalkFunctor
          ((analytificationToSpec.{u} nodeG.{u}).base originNode.{u}) ⋙
        ModuleCat.extendScalars
          ((analytificationToSpec.{u} nodeG.{u}).stalkMap originNode.{u}).hom :=
  analytificationSheafStalkIso.{u} nodeG.{u} originNode.{u}

/-- **The base change above is along a faithfully flat ring homomorphism.**

The term `((analytificationToSpec g).stalkMap y).hom` is the same one that appears inside
`ModuleCat.extendScalars` in `analytificationSheafStalkIso`, so the stalk computation and the
flatness meet with nothing in between. -/
theorem faithfullyFlat_extendScalars_hom
    (y : (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace) :
    ((analytificationToSpec.{u} g).stalkMap y).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_analytificationToSpec.{u} g y

end ComplexAnalytic

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.Sheaf
import OkaTest.Analytification

/-!
# Non-vacuity of the analytification of a sheaf

`Oka/Analytification/Sheaf.lean` defines the analytification of a sheaf of modules as the
pullback along `ComplexAnalytic.analytificationToSpec`. A functor defined as a left adjoint is
exactly the kind of definition that can be inert: it exists because an adjoint exists, and
nothing forces it to be applicable to anything.

This file applies it at the node `ℂ[x, y] ⧸ (x y)` — the presentation whose ideal is not zero and
whose space is not smooth — and names the three things a consumer will want:

* the functor itself, at that presentation, with both categories written out;
* `ComplexAnalytic.analytificationSheafUnitToUnit` there, which is the map a comparison theorem
  between `𝒪_X` and `𝒪_{X^an}` is a statement about;
* right exactness there, which is the half of GAGA's exactness that the adjunction gives away.

**What is not here is the other half.** Preservation of finite limits is where the flatness of
the stalk maps gets consumed, and it is GAGA; see `Oka/Analytification/Sheaf.lean`'s
`## What is not here`.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

/-- **The analytification of a sheaf, at the node.** Both categories are written out: sheaves of
modules on `Spec (ℂ[x, y] ⧸ (x y))` on the left, on the node itself on the right. -/
def nodeAnalytificationSheaf :
    SheafOfModules.{u}
        (Spec.locallyRingedSpaceObj
          (CommRingCat.of
            (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸ presentationIdeal.{u} nodeG.{u}))).ringSheaf ⥤
      SheafOfModules.{u}
        (AnalyticSpace.analytification.{u} nodeG.{u}).toLocallyRingedSpace.ringSheaf :=
  analytificationSheaf.{u} nodeG.{u}

/-- **The analytification of `𝒪_X` maps to `𝒪_{X^an}`, at the node.** -/
def nodeAnalytificationSheafUnitToUnit :
    nodeAnalytificationSheaf.{u}.obj
        (SheafOfModules.unit
          (Spec.locallyRingedSpaceObj
            (CommRingCat.of
              (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸
                presentationIdeal.{u} nodeG.{u}))).ringSheaf) ⟶
      SheafOfModules.unit
        (AnalyticSpace.analytification.{u} nodeG.{u}).toLocallyRingedSpace.ringSheaf :=
  analytificationSheafUnitToUnit.{u} nodeG.{u}

/-- **The analytification of a sheaf is right exact at the node.**

The node is where a statement that had accidentally assumed the ideal was zero, or the space
smooth, would be a statement about `ℂ²` instead. -/
theorem preservesColimits_nodeAnalytificationSheaf :
    PreservesColimits nodeAnalytificationSheaf.{u} :=
  preservesColimits_analytificationSheaf.{u} nodeG.{u}

end ComplexAnalytic

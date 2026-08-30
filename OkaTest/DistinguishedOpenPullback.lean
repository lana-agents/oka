/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.LocalisationFunctor

/-!
# Non-vacuity of the pullback of a distinguished open

`Oka/Analytification/DistinguishedOpenPullback.lean` says that a distinguished open pulls back
along `ComplexAnalytic.analytificationMap` to a distinguished open. Every statement there is an
equation of open subsets, so two readings would empty it and both are closed here.

* **The general statement specialises to the one that was proved by hand.**
  `localisationOpen_rename_of_comap` re-derives `ComplexAnalytic.localisationOpen_rename` — the
  case of the structure map `A ⟶ A_f`, where the representative is the renamed polynomial — from
  the general theorem, by a route that shares no step with the original proof: that one is
  `ComplexAnalytic.eval_localisationProj` at a point, this one is the naturality of
  `ComplexAnalytic.quotientToGlobal`. A direction error or a wrong side in the hypothesis would
  show up here and nowhere in the file itself.
* **The preimage is not always everything.** `comap_localisationOpen_nodeStructureHom_ne_top`
  pulls `D(z₁)` on the node back to the localisation at `z₀`, where it misses the point
  `(1, 0, 1)` that `OkaTest/AnalytificationDistinguishedOpen.lean` already built. So the equation
  is not `⊤ = ⊤`, and `localisationOpen_ne_top_of_comap_eq` reads that back through the
  existential: **whatever polynomial of the base the theorem produces there, its open is a proper
  subset of the node.** That is a statement about the output and not only about the input, which
  is what makes it evidence.

**What is not checked.** Nothing here is about a cover or a refinement — the file under test
mentions neither — and nothing checks the *other* half of the cross-member chain, which is that
the overlap of two refined members is the preimage of anything. Taxis #1287 carries that.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.DistinguishedOpenPullback

open OkaTest.LocalisationFunctor

/-- **`ComplexAnalytic.localisationOpen_rename`, re-derived from the general pullback theorem.**

The structure map `A ⟶ A_f` sends the class of `f'` to the class of `f'` with its variables
renamed (`ComplexAnalytic.localisationRingHom_mk`), so it is a representative in the sense the
theorem asks for, and `ComplexAnalytic.analytificationMap_localisationPresHom` identifies the
morphism it induces with the projection. -/
theorem localisationOpen_rename_of_comap {n k : ℕ}
    (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (f f' : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    localisationOpen.{u} (localisationPresentation.{u} g f)
        (MvPolynomial.rename (localisationIncl.{u} n) f') =
      (Opens.map (localisationProj.{u} g f).toLRSHom.base).obj (localisationOpen.{u} g f') := by
  rw [← analytificationMap_localisationPresHom.{u} g f]
  exact localisationOpen_eq_comap_analytificationMap.{u} (localisationPresHom.{u} g f) f'
    (MvPolynomial.rename (localisationIncl.{u} n) f') (localisationRingHom_mk.{u} g f f')

/-- The other coordinate of the node, `z₁`: the one that vanishes on the punctured `z₀`-axis. -/
abbrev nodeY : MvPolynomial (ULift.{u} (Fin 2)) ℂ := MvPolynomial.X (ULift.up 1)

/-- **`z₁` vanishes at the point `(1, 0, 1)` of the localisation**, read upstairs.

`ComplexAnalytic.eval_localisationProj` moves the evaluation down to the image point, which is
`axisPoint 0` by `base_localisationProj_nodeLocPoint`, and there the second coordinate is `0`. -/
theorem eval_rename_nodeY_nodeLocPoint :
    MvPolynomial.eval (nodeLocPoint.{u}.1.1 : ULift.{u} (Fin 3) → ℂ)
        (MvPolynomial.rename (localisationIncl.{u} 2) nodeY.{u}) = 0 := by
  rw [← eval_localisationProj, base_localisationProj_nodeLocPoint, MvPolynomial.eval_X,
    axisPoint_coord, if_neg]
  intro hcon
  simpa using congrArg ULift.down hcon

/-- **The preimage of `D(z₁)` on the localisation at `z₀` is a proper open subset.**

So the pullback theorem is not an equation between two copies of `⊤`. The witness is the point
`(1, 0, 1)`, and the preimage is computed by the theorem itself: it is the distinguished open of
the renamed `z₁`, which `ComplexAnalytic.localisationOpen_ne_top` then separates from the whole
space. -/
theorem comap_localisationOpen_nodeStructureHom_ne_top :
    (Opens.map (analytificationMap.{u} nodeStructureHom.{u}).toLRSHom.base).obj
        (localisationOpen.{u} nodePres.{u} nodeY.{u}) ≠ ⊤ := by
  rw [← localisationOpen_eq_comap_analytificationMap.{u}
    (localisationPresHom.{u} nodePres.{u} nodeX.{u}) nodeY.{u}
    (MvPolynomial.rename (localisationIncl.{u} 2) nodeY.{u})
    (localisationRingHom_mk.{u} nodePres.{u} nodeX.{u} nodeY.{u})]
  exact localisationOpen_ne_top.{u} (localisationPresentation.{u} nodePres.{u} nodeX.{u})
    (MvPolynomial.rename (localisationIncl.{u} 2) nodeY.{u}) nodeLocPoint.{u}
    eval_rename_nodeY_nodeLocPoint.{u}

/-- **Whatever polynomial of the node the existential produces at this pullback, its open is a
proper subset of the node.**

`ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj` produces a `Q` on the
base with a stated property; this says that property has consequences, so the theorem cannot be
satisfied by a `Q` whose open is everything — `Q = 1` is not a witness. It is the non-vacuity of
the *output*, which the equation on its own does not give. -/
theorem localisationOpen_ne_top_of_comap_eq (Q : MvPolynomial (ULift.{u} (Fin 2)) ℂ)
    (hQ : (Opens.map (analytificationMap.{u} nodeStructureHom.{u}).toLRSHom.base).obj
        (localisationOpen.{u} nodePres.{u} nodeY.{u}) =
      (Opens.map (localisationProj.{u} nodePres.{u} nodeX.{u}).toLRSHom.base).obj
        (localisationOpen.{u} nodePres.{u} Q)) :
    localisationOpen.{u} nodePres.{u} Q ≠ ⊤ := by
  intro hcon
  refine comap_localisationOpen_nodeStructureHom_ne_top.{u} ?_
  rw [hQ, hcon]
  exact Opens.map_top _

end OkaTest.DistinguishedOpenPullback

end

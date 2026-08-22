/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.Sheaf
import OkaTest.AnalytificationFlatness

/-!
# Non-vacuity of the exactness of the analytification of a sheaf

`ComplexAnalytic.preservesFiniteLimits_analytificationSheaf` is GAGA's local half. It is
quantified over every presentation and every sheaf of modules, so it cannot be degenerate in the
way a statement about one object can — but it can be **empty in two ways**, and this file rules
out both at the node `ℂ[x, y] ⧸ (x y)`.

## Degeneracy 1: the presentation could be trivial

If the ideal were zero the theorem would be the statement for `ℂ^n ⟶ 𝔸^n`, which is the ambient
case and proves nothing about analytification of a *singular* space. The theorem's only
hypothesis is the flatness of the stalk maps, so the test is that this flatness is available at a
point where the space is genuinely singular: `node_faithfullyFlat_and_not_domain` records it
together with the fact that the stalk there **is not a domain**, which on `ℂ²` is impossible.

## Degeneracy 2: an exactness statement about zero objects

An exactness statement is vacuous if the objects it is applied to are zero. `node_stalk_nontrivial`
rules that out at the target end: the stalk of the node's structure sheaf at the origin is
nontrivial, because a trivial ring **does** satisfy `NoZeroDivisors` and this one does not. So the
categories the functor moves between are not zero categories.

## What is checked positively

* `nodePreservesFiniteLimits` — the theorem at the node, with both categories written out, so
  that the site-spelling seam that has cost this development three separate instances is
  exercised at a concrete presentation rather than at a variable.
* `nodePreservesMonomorphisms` — the concrete content of left exactness, which is what the proof
  actually establishes and everything else is formal around.

**No coherence hypothesis appears anywhere**, here or upstream.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

/-- **The analytification of a sheaf is left exact, at the node.** Both categories written out:
sheaves of modules on `Spec (ℂ[x, y] ⧸ (x y))` on the left, on the node itself on the right. -/
theorem nodePreservesFiniteLimits :
    PreservesFiniteLimits
      (analytificationSheaf.{u} nodeG.{u} :
        SheafOfModules.{u}
            (Spec.locallyRingedSpaceObj
              (CommRingCat.of
                (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸
                  presentationIdeal.{u} nodeG.{u}))).ringSheaf ⥤
          SheafOfModules.{u}
            (AnalyticSpace.analytification.{u} nodeG.{u}).toLocallyRingedSpace.ringSheaf) :=
  preservesFiniteLimits_analytificationSheaf.{u} nodeG.{u}

/-- **The concrete content of left exactness at the node**: the analytification of an injection of
sheaves is an injection. Everything else in the proof is formal around this. -/
theorem nodePreservesMonomorphisms :
    (analytificationSheaf.{u} nodeG.{u}).PreservesMonomorphisms :=
  haveI := nodePreservesFiniteLimits.{u}
  inferInstance

/-- **The flatness the theorem consumes at the node's origin is flatness over a ring that is not a
domain.** On `ℂ²` the corresponding stalk *is* a domain, so a development in which the ideal had
been accidentally trivial could not state this — which is what makes the exactness at the node
something other than the ambient case in disguise. -/
theorem node_faithfullyFlat_and_not_domain :
    ((analytificationToSpec nodeG.{u}).stalkMap originNode.{u}).hom.FaithfullyFlat ∧
      ¬ NoZeroDivisors ((AnalyticSpace.analytification nodeG.{u}).presheaf.stalk
        originNode.{u}) :=
  ⟨faithfullyFlat_stalkMap_analytificationToSpec_nodeG_origin.{u},
    not_noZeroDivisors_stalk_analytification_nodeG.{u}⟩

/-- **The target stalk is nontrivial**, so the exactness statement is not about zero objects.

The trivial ring satisfies `NoZeroDivisors` vacuously, so failing it forces nontriviality. -/
theorem node_stalk_nontrivial :
    Nontrivial ((AnalyticSpace.analytification nodeG.{u}).presheaf.stalk originNode.{u}) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact not_noZeroDivisors_stalk_analytification_nodeG.{u} inferInstance

end ComplexAnalytic

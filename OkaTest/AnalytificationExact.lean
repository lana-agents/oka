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
  that the site-spelling seam is exercised at a concrete presentation rather than at a variable.
  **That seam has three instance transports and two of them are costs**, measured below rather
  than remembered.
* `nodePreservesMonomorphisms` — the concrete content of left exactness, which is what the proof
  actually establishes and everything else is formal around.

**No coherence hypothesis appears anywhere**, here or upstream.

## What the site-spelling seam costs, and how to re-derive the number

The count above used to read *"three separate instances"* with nothing behind it, which is the
species of claim a merge falsifies without touching the sentence. **The criterion, so that it can
be re-run**: an `instance` under `Oka/` whose body is `inferInstanceAs` and whose type mentions
`Opens.grothendieckTopology`, `TopCat.Sheaf` or `stalkFunctor`. On 2026-08-25, at `master` =
`16c1637`, there are three, and deleting each and re-elaborating separates transport from cost.

* `AlgebraicGeometry.LocallyRingedSpace.hasSheafify_toPresheafedSpace`
  (`Oka/Geometry/RingedSpace/LocallyRingedSpace/Modules.lean`) — **a cost, and an invisible one.**
  Delete it and its own file still compiles; `lake build` fails 3900 modules later, in a different
  subtree, at `Oka/Analytification/SheafCoherent.lean:150` with `failed to synthesize instance of
  type class (analytificationSheaf g).PreservesZeroMorphisms`.
* `PreservesFiniteLimits (TopCat.Sheaf.stalkFunctor X x)`
  (`Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean`) — **a cost, and a local one.** Delete it and
  the declaring file fails: `failed to synthesize instance of type class PreservesFiniteLimits
  (Sheaf.stalkFunctor X x)`.
* `(TopCat.Sheaf.stalkFunctor X x).Additive` (the same file) — **a transport and not a cost.**
  Delete it alone and nothing fails; only when it goes together with the previous one does
  `failed to synthesize instance of type class (stalkFunctor X x).PreservesZeroMorphisms` appear.
  Its own docstring says as much and calls it *kept as API*.

**Three transports, two costs.** The first is the one worth carrying: its absence is invisible in
the file that declares it, so a reader auditing this seam by re-elaborating the file it lives in
would conclude it is free.
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

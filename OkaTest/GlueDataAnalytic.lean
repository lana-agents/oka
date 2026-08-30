/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.OpenSubspace

/-!
# Non-vacuity of the analytic structure on a gluing

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` takes an
`AlgebraicGeometry.LocallyRingedSpace.GlueData`, a `ℂ`-algebra structure on each member, and two
hypotheses: that the members have local models, and that the transitions are `ℂ`-linear
(`ComplexAnalytic.GlueDataCLinear`). Both could in principle be unsatisfiable except in degenerate
cases, and the output could in principle be unrelated to the input. This file exhibits a glue data
at which both hold and checks the output against the input, on a **two-member open cover of the
node**, glued back together.

**What that does and does not settle**, since the two hypotheses are not on the same footing here:

* the local-model hypothesis is discharged at a genuine analytic space, by
  `ComplexAnalytic.AnalyticSpace.restrict`;
* the output is checked, both on each member and globally, against the structure the gluing
  started from;
* the `ℂ`-linearity hypothesis is discharged by `ComplexAnalytic.glueDataCLinear_comapAlgMap`,
  which makes it **automatic** — the structures here are pulled back from one on the gluing.
  **That is exactly the case
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap` was written not to
  need**, so this file does not show the hypothesis satisfiable where it has
  content. The glue data that would is `ComplexAnalytic.coverGlueData`; see below for why it is
  not here.

## The witness

`AlgebraicGeometry.LocallyRingedSpace.OpenCover.gluedCover` of the cover of
`ComplexAnalytic.AnalyticSpace.node` by the two opens `z₀ ≠ 1` and `z₀ ≠ 0`. **Neither member is
`⊤` and neither is `⊥`**, and all four facts are proved below. That matters: a cover by `⊤` and
anything else is a cover whatever the second member is, its overlap *is* the second member, and
nothing about that member would then say anything about the glue data. Here each member omits a
point the other keeps — the first omits `z₀ = 1`, the second omits the origin — so the overlap is
a pullback of two immersions neither of which is the identity.

* The `ℂ`-linearity hypothesis is `ComplexAnalytic.glueDataCLinear_comapAlgMap`, at the structure
  the gluing inherits from the node through
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover.fromGlued`.
* The local-model hypothesis is `ComplexAnalytic.AnalyticSpace.restrict`'s own, after
  `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict` turns the pullback along the
  inclusion of a member into the restriction of the node's structure.
* The output is checked *both* ways the file that defines it offers:
  `ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap` on each member and
  `ComplexAnalytic.AnalyticSpace.algebraMap_ofGlueDataCLinear_comapAlgMap` globally.

## What is *not* checked here

* **This is not the interesting instantiation, and it is not the only one.**
  `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` is applied to a glue datum built by
  `ComplexAnalytic.coverGlueData` inside `ComplexAnalytic.coverAnalytification`, which
  `OkaTest/AffineCover.lean` quotes as `ComplexAnalytic.nodeTripleSpace` — a gluing of three
  spaces rather than a space taken apart and put back. (That application moved into
  `Oka/Analytification/AffineCover.lean` when the general construction landed; the test file
  keeps an `example` recording that the two spellings agree.) What that one needs and this one
  does not is
  `Oka/CategoryTheory/GlueData.lean`'s unfolding lemmas, since
  `ComplexAnalytic.GlueDataCLinear` reads `D.f` and `D.t` and `CategoryTheory.GlueData.ofGlueData'`
  supplies them as `dite`s.
* **Nothing here says the glued space is not the node.** It is: the cover's
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover.fromGlued` is an isomorphism, which is the point
  of the witness rather than a defect — a cover of a space one already understands is the shape in
  which the hypotheses can be discharged at all, and it is what makes the round trip a *check*
  rather than a definition. A gluing that is genuinely new is `ℙ¹`, and it is a different issue.
* **No claim that the two members are the smallest interesting cover.** One member would also
  satisfy every hypothesis; two is used because the overlap is then a pullback of two different
  immersions, which is what the compatibility hypothesis is about.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.GlueDataAnalytic

/-! ### A two-member open cover of the node -/

/-- **The points of the node whose first coordinate is not `c`.**

At `c = 0` this is `nodeAxis 0`; the cover below uses `c = 1` as well, so that **neither** member
is `⊤`. The proof of openness is `nodeAxis`'s: the first coordinate is continuous and the
complement of a point is open. -/
def nodeAvoid (c : ℂ) : Opens (AnalyticSpace.node.{u}) :=
  ⟨{p : AnalyticSpace.node.{u} | p.1.1 (ULift.up 0) ≠ c},
    isOpen_compl_singleton.preimage ((continuous_apply (ULift.up 0)).comp
      (continuous_subtype_val.comp continuous_subtype_val))⟩

theorem mem_nodeAvoid_iff (c : ℂ) (p : AnalyticSpace.node.{u}) :
    p ∈ nodeAvoid.{u} c ↔ p.1.1 (ULift.up 0) ≠ c := Iff.rfl

/-- The two members of the cover: the node minus the point with `z₀ = 1`, and the node minus the
axis `z₀ = 0`.

**Neither is `⊤`.** A cover by `⊤` and anything else is a cover whatever the second member is, so
its overlap is that second member and the second member's non-degeneracy says nothing about the
glue data; here each member genuinely omits points the other keeps. -/
def nodeOpens : ULift.{u} (Fin 2) → Opens (AnalyticSpace.node.{u}) :=
  fun j ↦ nodeAvoid.{u} (if j.down = 0 then 1 else 0)

theorem nodeOpens_zero : nodeOpens.{u} (ULift.up 0) = nodeAvoid.{u} 1 := rfl

theorem nodeOpens_one : nodeOpens.{u} (ULift.up 1) = nodeAvoid.{u} 0 := rfl

theorem nodeOrigin_coord_zero : (nodeOrigin.{u}).1.1 (ULift.up 0) = 0 := rfl

theorem axisPoint_zero_coord_zero :
    (axisPoint.{u} (ULift.up 0)).1.1 (ULift.up 0) = 1 := by
  rw [axisPoint_coord, if_pos rfl]

/-- **The first member misses the point of the node with `z₀ = 1`**, so it is not `⊤`. -/
theorem nodeOpens_zero_ne_top : nodeOpens.{u} (ULift.up 0) ≠ ⊤ := by
  intro h
  have hmem : axisPoint.{u} (ULift.up 0) ∈ nodeOpens.{u} (ULift.up 0) := h ▸ trivial
  rw [nodeOpens_zero, mem_nodeAvoid_iff] at hmem
  exact hmem axisPoint_zero_coord_zero.{u}

/-- **The second member misses the origin**, so it is not `⊤` either. -/
theorem nodeOpens_one_ne_top : nodeOpens.{u} (ULift.up 1) ≠ ⊤ := by
  intro h
  have hmem : nodeOrigin.{u} ∈ nodeOpens.{u} (ULift.up 1) := h ▸ trivial
  rw [nodeOpens_one, mem_nodeAvoid_iff] at hmem
  exact hmem nodeOrigin_coord_zero.{u}

/-- **The first member is nonempty**: the origin is in it. -/
theorem nodeOpens_zero_ne_bot : nodeOpens.{u} (ULift.up 0) ≠ ⊥ := by
  intro h
  have hmem : nodeOrigin.{u} ∈ nodeOpens.{u} (ULift.up 0) := by
    rw [nodeOpens_zero, mem_nodeAvoid_iff, nodeOrigin_coord_zero]
    exact zero_ne_one
  rw [h] at hmem
  exact hmem

/-- **The second member is nonempty**: the point with `z₀ = 1` is in it. -/
theorem nodeOpens_one_ne_bot : nodeOpens.{u} (ULift.up 1) ≠ ⊥ := by
  intro h
  have hmem : axisPoint.{u} (ULift.up 0) ∈ nodeOpens.{u} (ULift.up 1) := by
    rw [nodeOpens_one, mem_nodeAvoid_iff, axisPoint_zero_coord_zero]
    exact one_ne_zero
  rw [h] at hmem
  exact hmem

/-- The open cover itself: the two members cover because `0 ≠ 1`, so a point whose first
coordinate is `1` lies in the second and every other point lies in the first. -/
def nodeCover : (AnalyticSpace.node.{u}).toLocallyRingedSpace.OpenCover :=
  LocallyRingedSpace.openCoverOfOpens nodeOpens.{u} fun x ↦ by
    by_cases h : x.1.1 (ULift.up 0) = 1
    · exact ⟨ULift.up 1,
        show x.1.1 (ULift.up 0) ≠ 0 from fun hc ↦ one_ne_zero (h.symm.trans hc)⟩
    · exact ⟨ULift.up 0, show x.1.1 (ULift.up 0) ≠ 1 from h⟩

/-- The node's own `ℂ`-algebra structure. -/
abbrev nodeGamma : ℂ →+* (AnalyticSpace.node.{u}).toLocallyRingedSpace.presheaf.obj (op ⊤) :=
  (AnalyticSpace.node.{u}).algebraMap

/-- The structure the gluing of the cover inherits from the node, along
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.fromGlued`. -/
abbrev nodeGluedAlg :
    ℂ →+* (nodeCover.{u}.gluedCover.toGlueData.glued).presheaf.obj (op ⊤) :=
  LocallyRingedSpace.comapAlgMap nodeCover.{u}.fromGlued nodeGamma.{u}

/-! ### The two hypotheses -/

/-- **The transitions are `ℂ`-linear.** Free, by `ComplexAnalytic.glueDataCLinear_comapAlgMap`:
the structures on the members are pulled back from one on the gluing. -/
theorem glueDataCLinear_nodeCover : GlueDataCLinear.{u} nodeCover.{u}.gluedCover
    fun j ↦ LocallyRingedSpace.comapAlgMap (nodeCover.{u}.gluedCover.toGlueData.ι j)
      nodeGluedAlg.{u} :=
  glueDataCLinear_comapAlgMap.{u} _ _

/-- **Each member has local models.** The structure it carries is the node's restricted to an
open subset — `AlgebraicGeometry.LocallyRingedSpace.OpenCover.ι_fromGlued` composes the two
pullbacks into one, and `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict` turns that
into `resAlgMap` — so `ComplexAnalytic.AnalyticSpace.restrict` supplies it. -/
theorem hasLocalModels_nodeCover (j : nodeCover.{u}.gluedCover.J) :
    HasLocalModels.{u} (nodeCover.{u}.gluedCover.U j)
      (LocallyRingedSpace.comapAlgMap (nodeCover.{u}.gluedCover.toGlueData.ι j)
        nodeGluedAlg.{u}) := by
  rw [← LocallyRingedSpace.comapAlgMap_comp, nodeCover.{u}.ι_fromGlued j]
  change HasLocalModels.{u} _ (LocallyRingedSpace.comapAlgMap
    ((AnalyticSpace.node.{u}).toLocallyRingedSpace.ofRestrict _) nodeGamma.{u})
  rw [LocallyRingedSpace.comapAlgMap_ofRestrict]
  exact (AnalyticSpace.node.{u}.restrict (nodeOpens.{u} j)).local_model

/-! ### The analytic space, and the two checks -/

/-- **The node, taken apart along a two-member open cover and glued back together as a complex
analytic space.** -/
def nodeReglued : AnalyticSpace.{u} :=
  AnalyticSpace.ofGlueDataCLinear.{u} nodeCover.{u}.gluedCover _
    glueDataCLinear_nodeCover.{u} hasLocalModels_nodeCover.{u}

/-- Its underlying locally ringed space is the gluing, on the nose. -/
example : (nodeReglued.{u}).toLocallyRingedSpace =
    nodeCover.{u}.gluedCover.toGlueData.glued := rfl

/-- **The glued `ℂ`-algebra structure is the one the gluing inherited** — the round trip, and the
check `Oka/AnalyticSpace/Glue.lean` says to use rather than inventing a new one. -/
example : (nodeReglued.{u}).algebraMap = nodeGluedAlg.{u} :=
  AnalyticSpace.algebraMap_ofGlueDataCLinear_comapAlgMap.{u} _ _ hasLocalModels_nodeCover.{u}

/-- **And it restricts on each member to the structure that member was given** — the other half of
the same check, on the pieces rather than globally. -/
example (j : nodeCover.{u}.gluedCover.J) :
    LocallyRingedSpace.comapAlgMap (nodeCover.{u}.gluedCover.toGlueData.ι j)
        (nodeReglued.{u}).algebraMap =
      LocallyRingedSpace.comapAlgMap (nodeCover.{u}.gluedCover.toGlueData.ι j) nodeGluedAlg.{u} :=
  AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap.{u} _ _ glueDataCLinear_nodeCover.{u}
    hasLocalModels_nodeCover.{u} j

end OkaTest.GlueDataAnalytic

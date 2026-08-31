/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the local homeomorphism, on a hypersurface that has one, one that does not, and
the open subspace on which the second one does

`ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv` says the projection of a
polynomial hypersurface in `ℂ²` to the `z₀`-line is a local homeomorphism when `∂P/∂z₁` vanishes
at no point of it. **Both of its hypotheses are about data that has to exist**, and this file
supplies data satisfying them, and data failing them.

## The graph of the squaring map, and why it is that curve and not the other one

`ComplexAnalytic.squareGraphPoly` is `z₁ − z₀²`, whose zero locus is the graph of `z₀ ↦ z₀²` — a
smooth curve whose projection to the `z₀`-line forgets nothing, and the simplest hypersurface
that is not a coordinate hyperplane. `ComplexAnalytic.pderiv_squareGraphPoly` computes `∂/∂z₁` of
it to be `1`, so the hypothesis holds at every point with nothing to check about the point, and
`ComplexAnalytic.isLocalHomeomorph_squareGraphProj` is the conclusion.

**It is the same curve as `OkaTest/MonicProjection.lean`'s, with the axes exchanged, and that is
the point.** `ComplexAnalytic.parabolaPoly` there is `X² − C z`, i.e. `z₀ = z₁²`, monic in the
last variable; its projection to the `z₀`-line is finite and **two-to-one**
(`ComplexAnalytic.not_injective_base_parabolaIncl_comp_proj`), and that file's own
`## What is not checked here` says the germ *"has a simple zero along the last axis only away
from the origin"*. Exchanging the axes exchanges the two properties: the curve below is a local
homeomorphism over the whole line and is not finite, the one there is finite and is not a local
homeomorphism at the origin. Neither file exhibits a morphism with both.

The cut-out datum is `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`, so the
space is the zero locus with its quotient structure sheaf and nothing about it is chosen here.

## The node, which is the control and then the example

`ComplexAnalytic.nodePoly` is `z₀z₁`, and `ComplexAnalytic.pderiv_nodePoly` computes `∂/∂z₁` of it
to be `z₀`, which **vanishes at the origin** — a point of the node, by
`ComplexAnalytic.origin_mem_zeroLocus_nodeSection`. So
`ComplexAnalytic.eval_pderiv_nodePoly_origin` witnesses that the hypothesis of the theorem is a
real restriction on the hypersurface and not a condition every polynomial satisfies. The node is
two lines crossing and its projection collapses one of them, so the conclusion fails there too;
**that last clause is not compiled and nothing below claims it.**

**And then the same curve is the example for the restricted statement**, which is why it is worth
having both in one file.
`ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_pderiv`
asks the derivative to be nonzero only at the points of an open subspace, and
`ComplexAnalytic.nodePunctured` — the node with `z₀ ≠ 0` — is one where it is.
`ComplexAnalytic.isLocalHomeomorph_nodePuncturedProj` is that theorem applied. **The pair is what
makes the restricted statement measurably stronger rather than a corollary**: the unrestricted
theorem is unavailable on this hypersurface, and the obstruction is not an argument but the
compiled `eval_pderiv_nodePoly_origin` two declarations above.

## Main results

- `ComplexAnalytic.pderiv_squareGraphPoly` and `ComplexAnalytic.pderiv_nodePoly`: the two
  derivatives, computed rather than bounded away from zero.
- `ComplexAnalytic.isLocalHomeomorph_squareGraphProj`: **the theorem applied**, to a hypersurface
  built here from `AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspaceι`.
- `ComplexAnalytic.eval_pderiv_nodePoly_origin`: the control — the derivative is `0` at a point
  of the node.
- `ComplexAnalytic.nodePunctured`: **the open subspace of the node on which the derivative does
  not vanish**, and `ComplexAnalytic.isLocalHomeomorph_nodePuncturedProj`: **the restricted
  theorem applied to it**, on the one hypersurface here that the unrestricted theorem cannot
  reach.

## What is not checked here

* **The `ComplexAnalytic.AnalyticSpace.IsLocalIso` form is not instantiated.**
  `ComplexAnalytic.isLocalIso_comp_proj_of_pderiv` needs a morphism in
  `ComplexAnalytic.AnalyticSpace`, that is a `ℂ`-linear one, together with an
  `ComplexAnalytic.IsCutOutBy` datum for it; `ComplexAnalytic.nodeIncl` is the only such
  inclusion of a hypersurface in the tree, its cut-out datum through
  `AlgebraicGeometry.LocallyRingedSpace.ofRestrict` is stated nowhere, and the node fails the
  hypothesis anyway. Building the graph at that level is the same construction repeated and is
  not done here. **So the local-isomorphism theorem is an assembly of two halves, of which only
  the topological one is exercised below**; the stalk one is exercised by
  `Oka/AnalyticSpace/SimpleZeroPolynomial.lean`'s own consumers.
* **Nothing about the image.** No statement below says the projection of the graph is injective
  or surjective, though it is both.
* **Nothing about `ComplexAnalytic.proj` on its own.** `ComplexAnalytic.not_isLocalIso_proj`
  (`OkaTest/FiniteMorphism.lean`) says the projection `ℂ² ⟶ ℂ` is not a local isomorphism, so the
  statement below is not an instance of one about the projection: the hypersurface is doing the
  work, and the two results are the same map read on different sources.
* **No `Fin`-indexed form.** The theorem exists only at the `ULift (Fin _)` indexing, so there is
  nothing to test at the other one.
* **Nothing says the projection of the whole node fails to be a local homeomorphism.** What
  `ComplexAnalytic.eval_pderiv_nodePoly_origin` compiles is that the *hypothesis* of the
  unrestricted theorem fails at the origin, which is what makes
  `ComplexAnalytic.isLocalHomeomorph_nodePuncturedProj` not an instance of it. The conclusion at
  the origin is a separate question and is asked nowhere here.
* **`ComplexAnalytic.nodePunctured` is not identified with a set.** Its carrier is written as the
  non-vanishing locus of the first coordinate pulled back along the immersion, and no statement
  below says it is one axis minus the origin, though
  `ComplexAnalytic.mem_zeroLocus_nodeSection_iff` would give that in a line at the ambient
  presentation `Oka/AnalyticSpace/LocalModel.lean` uses. It is a different ambient space from the
  one used here and the identification buys nothing the theorem needs.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry MvPolynomial

universe u

noncomputable section

namespace ComplexAnalytic

/-- The polynomial `z₁ − z₀²`, whose zero locus in `ℂ²` is the graph of the squaring map.

Not to be confused with `ComplexAnalytic.parabolaPoly` of `OkaTest/MonicProjection.lean`, which is
the same curve with the axes exchanged and is a `Polynomial ℂ` rather than a multivariate one. -/
def squareGraphPoly : MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  MvPolynomial.X (ULift.up 1) - MvPolynomial.X (ULift.up 0) ^ 2

/-- The one-element family of holomorphic functions on `ℂ²` cutting out that graph. -/
def squareGraphSection : Fin 1 → OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)) :=
  ![OkaRing.ofMvPolynomial ⊤ squareGraphPoly.{u}]

/-- The closed immersion of the graph into `ℂ²`. -/
def squareGraphIncl :
    (complexAffineSpace.{u} 2).zeroLocusSubspace squareGraphSection.{u} ⟶
      complexAffineSpace.{u} 2 :=
  (complexAffineSpace.{u} 2).zeroLocusSubspaceι squareGraphSection.{u}

/-- The graph is cut out by `z₁ − z₀²`. -/
theorem isCutOutBy_squareGraphIncl :
    IsCutOutBy squareGraphIncl.{u} ![OkaRing.ofMvPolynomial ⊤ squareGraphPoly.{u}] :=
  (complexAffineSpace.{u} 2).isCutOutBy_zeroLocusSubspaceι squareGraphSection.{u}

/-- **`∂(z₁ − z₀²)/∂z₁ = 1`**, so the graph has a simple zero along the last axis at every
one of its points and the hypothesis of the theorem below needs no point to be named. -/
theorem pderiv_squareGraphPoly :
    MvPolynomial.pderiv (ULift.up.{u} (Fin.last 1)) squareGraphPoly.{u} = 1 := by
  have h : (ULift.up.{u} (Fin.last 1)) = ULift.up.{u} (1 : Fin 2) := rfl
  rw [squareGraphPoly, h]
  simp

/-- **The projection of the graph of the squaring map to the `z₀`-line is a local
homeomorphism.** -/
theorem isLocalHomeomorph_squareGraphProj :
    IsLocalHomeomorph
      ((squareGraphIncl.{u} ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} 1))).base) :=
  isLocalHomeomorph_base_comp_uliftProj_of_pderiv isCutOutBy_squareGraphIncl.{u} fun _ ↦ by
    rw [pderiv_squareGraphPoly]
    simp

/-- **`∂(z₀z₁)/∂z₁ = z₀`**: the node's derivative along the last axis is not a nonzero constant,
which is what the control below turns on. -/
theorem pderiv_nodePoly :
    MvPolynomial.pderiv (ULift.up.{u} (Fin.last 1)) nodePoly.{u} =
      MvPolynomial.X (ULift.up.{u} (0 : Fin 2)) := by
  have h : (ULift.up.{u} (Fin.last 1)) = ULift.up.{u} (1 : Fin 2) := rfl
  rw [nodePoly, h]
  simp

/-- **The control: at the origin, which is a point of the node, the derivative vanishes.**

So the hypothesis of `ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv` is not
satisfied by every polynomial, and the theorem is not an instance of one with fewer hypotheses.
That the origin is on the node is `ComplexAnalytic.origin_mem_zeroLocus_nodeSection`. -/
theorem eval_pderiv_nodePoly_origin :
    MvPolynomial.eval (0 : ULift.{u} (Fin 2) → ℂ)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last 1)) nodePoly.{u}) = 0 := by
  rw [pderiv_nodePoly]
  simp

/-! ### Restricting the source, where the node stops being a control and becomes an example -/

/-- The one-element family cutting the node out of `ℂ²`, at the ambient space
`ComplexAnalytic.complexAffineSpace 2` rather than the `restrict ⊤` presentation
`ComplexAnalytic.nodeSection` of `Oka/AnalyticSpace/LocalModel.lean` uses. The polynomial is the
same one and is quoted rather than repeated. -/
def nodeCutSection : Fin 1 → OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)) :=
  ![OkaRing.ofMvPolynomial ⊤ nodePoly.{u}]

/-- The closed immersion of the node into `ℂ²`, built exactly as
`ComplexAnalytic.squareGraphIncl` is. -/
def nodeCutIncl :
    (complexAffineSpace.{u} 2).zeroLocusSubspace nodeCutSection.{u} ⟶
      complexAffineSpace.{u} 2 :=
  (complexAffineSpace.{u} 2).zeroLocusSubspaceι nodeCutSection.{u}

/-- The node is cut out by `z₀z₁`. -/
theorem isCutOutBy_nodeCutIncl :
    IsCutOutBy nodeCutIncl.{u} ![OkaRing.ofMvPolynomial ⊤ nodePoly.{u}] :=
  (complexAffineSpace.{u} 2).isCutOutBy_zeroLocusSubspaceι nodeCutSection.{u}

/-- **The part of the node where the first coordinate does not vanish**, as an open subspace of
the node. It is one of the two axes with the origin removed, and the origin is precisely the point
`ComplexAnalytic.eval_pderiv_nodePoly_origin` rules out. -/
def nodePunctured : Opens ((complexAffineSpace.{u} 2).zeroLocusSubspace nodeCutSection.{u}) where
  carrier := {x | (nodeCutIncl.{u}.base x : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) ≠ 0}
  is_open' :=
    isOpen_ne.preimage ((continuous_apply _).comp nodeCutIncl.{u}.base.hom.continuous)

/-- **The projection of the punctured node to the `z₀`-line is a local homeomorphism**, which is
the restricted statement applied and is the point of this section.

**The unrestricted theorem cannot give this and the obstruction is compiled two declarations
up.** `ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv` asks the derivative to be
nonzero at *every* point of the hypersurface, and `ComplexAnalytic.eval_pderiv_nodePoly_origin`
says it is `0` at the origin, which lies on the node
(`ComplexAnalytic.origin_mem_zeroLocus_nodeSection`). So this is not the unrestricted theorem
precomposed with an open immersion — there is nothing to precompose — and the node is the witness
that the restricted statement is strictly stronger rather than a corollary.

**What is not claimed is that the conclusion fails without the restriction.** Nothing here says
the projection of the whole node is not a local homeomorphism; what is exhibited is that the
*hypothesis* fails there, which is what makes the open subspace necessary for this route and not
for the statement. -/
theorem isLocalHomeomorph_nodePuncturedProj :
    IsLocalHomeomorph
      ((((complexAffineSpace.{u} 2).zeroLocusSubspace nodeCutSection.{u}).ofRestrict
        nodePunctured.{u}.isOpenEmbedding ≫ nodeCutIncl.{u} ≫
          okaMapHom (coordEmb (uliftCastSuccEmb.{u} 1))).base) :=
  isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_pderiv isCutOutBy_nodeCutIncl.{u}
    nodePunctured.{u} fun x ↦ by
      rw [pderiv_nodePoly, MvPolynomial.eval_X]
      exact x.2

end ComplexAnalytic

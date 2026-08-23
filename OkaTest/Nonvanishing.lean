/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.OpenSubspace

/-!
# Non-vacuity of the non-vanishing locus and of `liftOpen`

Both declarations tested here are satisfied by degenerate data. `nonvanishing` is an `Opens`, and
`⊤` is one; `liftOpen` produces a morphism into `X|U`, and at `U = ⊤`, or at a `φ` which is
already the inclusion of an open subspace, it produces something the repository already had. So
the checks below are chosen to rule those two readings out.

* **The non-vanishing locus is computed on a space which is not `ℂ^n`, and it is an open subset
  the development already had.** `nonvanishing_nodeCoord_eq_nodeAxis` says the non-vanishing locus
  of the `j`-th coordinate function of the node **is** `nodeAxis j`, the punctured `j`-th axis
  that `OkaTest/OpenSubspace.lean` constructs by hand, openness proof included — so the two
  routes to that open subset agree, and this one proves nothing about openness. It is a **proper
  nonempty** open subset: `nonvanishing_nodeCoord_ne_top` and `ne_bot`.

* **On a space with zero divisors the two loci are disjoint.** `nodeCoord 0 * nodeCoord 1 = 0`
  on the node, so `nonvanishing_nodeCoord_inf_eq_bot` follows from
  `ComplexAnalytic.AnalyticSpace.nonvanishing_mul`. This is what a locus defined through germs
  buys over one defined by hand: it interacts with the ring structure. Composed with the equality
  above it **reproves `nodeAxis_inf_eq_bot`**, which `OkaTest/OpenSubspace.lean` gets from a
  pointwise argument — two independent proofs of one statement, which is what makes the equality
  a check rather than a definition unfolded.

* **`liftOpen` is run at a morphism that is not an inclusion of open subspaces.** `nodeIncl`
  embeds the node in `ℂ²`, and the section `1 - z₀ z₁` is invertible at every point of the node
  precisely *because* of the node's equation, so the node lifts to the open subspace
  `ℂ²|D(1 - z₀z₁)` — and `ambientOpen_ne_top` records that this open subspace is a proper one, so
  the lift is not the original morphism in disguise. `nodeInclLift_fac` is the factorisation and
  `base_nodeInclLift` computes it on points.

* **On the one case where the answer was already known, it agrees.**
  `liftOpen_ofRestrict_eq_restrictLE`: lifting the inclusion of an open subspace along a larger
  open subspace gives `ComplexAnalytic.AnalyticSpace.restrictLE`, the one construction of this
  shape the repository had before.

**What is not checked here.** Nothing says the analytic structure on `ℂ²|D(1 - z₀z₁)` is the one a
reader would expect beyond its being a restriction; and no statement here is about a *closed*
immersion factoring through an open subspace, which is the situation
`Oka/Analytification/` will meet.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-! ### The non-vanishing locus of a coordinate on the node -/

/-- **A point of the node lies in the non-vanishing locus of the `j`-th coordinate function
exactly when its `j`-th coordinate is nonzero.** `ComplexAnalytic.eval_nodeCoord` reads the value
off; nothing else is involved. -/
theorem mem_nonvanishing_nodeCoord_iff (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 2)) :
    p ∈ (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) ↔ p.1.1 j ≠ 0 := by
  rw [AnalyticSpace.mem_nonvanishing_iff, eval_nodeCoord]

/-- **The non-vanishing locus of the `j`-th coordinate function of the node is the punctured
`j`-th axis.**

`nodeAxis` is built by hand in `OkaTest/OpenSubspace.lean`, with its own continuity argument for
openness; `ComplexAnalytic.AnalyticSpace.nonvanishing` gets the same open subset out of
`AlgebraicGeometry.RingedSpace.basicOpen` and proves nothing topological. That the two agree is
what makes the definition the right one rather than merely a definition. -/
theorem nonvanishing_nodeCoord_eq_nodeAxis (j : ULift.{u} (Fin 2)) :
    (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) = nodeAxis.{u} j :=
  TopologicalSpace.Opens.ext (Set.ext fun p ↦ mem_nonvanishing_nodeCoord_iff p j)

/-- **The punctured axis is not everything**: the origin is a point of the node at which the
coordinate vanishes. -/
theorem nonvanishing_nodeCoord_ne_top (j : ULift.{u} (Fin 2)) :
    (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) ≠ ⊤ := by
  intro hcon
  have hmem : nodeOrigin.{u} ∈ (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) := by
    rw [hcon]
    trivial
  exact (mem_nonvanishing_nodeCoord_iff nodeOrigin.{u} j).1 hmem rfl

/-- **The punctured axis is not empty**: `(1, 0)` and `(0, 1)` are points of the node. -/
theorem nonvanishing_nodeCoord_ne_bot (j : ULift.{u} (Fin 2)) :
    (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) ≠ ⊥ := by
  intro hcon
  have hmem : axisPoint.{u} j ∈ (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) :=
    (mem_nonvanishing_nodeCoord_iff _ j).2
      (by rw [axisPoint_coord, if_pos rfl]; exact one_ne_zero)
  rw [hcon] at hmem
  exact hmem

/-- **The two punctured axes are disjoint**, because the two coordinate functions of the node
multiply to zero. This is `ComplexAnalytic.AnalyticSpace.nonvanishing_mul` — the non-vanishing
locus sees the ring structure — rather than a second pointwise argument. -/
theorem nonvanishing_nodeCoord_inf_eq_bot :
    (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} (ULift.up 0)) ⊓
      (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} (ULift.up 1)) = ⊥ := by
  rw [← AnalyticSpace.nonvanishing_mul, nodeCoord_mul]
  refine eq_bot_iff.2 fun p hp ↦ ?_
  exact ((AnalyticSpace.mem_nonvanishing_iff (AnalyticSpace.node.{u}) 0).1 hp (map_zero _)).elim

/-- **`nodeAxis_inf_eq_bot` a second time, from the node's equation rather than pointwise.**
`OkaTest/OpenSubspace.lean` proves it by taking a point and using `z₀ z₁ = 0` on it; here it is
`nodeCoord_mul` and the fact that the non-vanishing locus of a product is an intersection, with
no point mentioned. -/
example : nodeAxis.{u} (ULift.up 0) ⊓ nodeAxis.{u} (ULift.up 1) = ⊥ := by
  rw [← nonvanishing_nodeCoord_eq_nodeAxis, ← nonvanishing_nodeCoord_eq_nodeAxis]
  exact nonvanishing_nodeCoord_inf_eq_bot.{u}

/-! ### Lifting the inclusion of the node into a proper open subspace of `ℂ²` -/

/-- The section `1 - z₀ z₁` of the structure sheaf of `ℂ²`. It is invertible at every point of
the node and vanishes at `(1, 1)`. -/
def ambientSection : OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)) :=
  1 - coord (ULift.up 0) * coord (ULift.up 1)

lemma eval_ambientSection (y : AnalyticSpace.complexAffineSpace.{u} 2) :
    (AnalyticSpace.complexAffineSpace.{u} 2).eval (U := ⊤) y trivial ambientSection.{u} =
      1 - y (ULift.up 0) * y (ULift.up 1) := by
  rw [eval_complexAffineSpace, ambientSection, map_sub, map_one, map_mul, evalHom_coord,
    evalHom_coord]

/-- The open subspace `ℂ²|{1 - z₀z₁ ≠ 0}`. -/
def ambientOpen : Opens (AnalyticSpace.complexAffineSpace.{u} 2) :=
  (AnalyticSpace.complexAffineSpace.{u} 2).nonvanishing ambientSection.{u}

/-- **It is a proper open subset**: `1 - z₀z₁` vanishes at `(1, 1)`. Without this the lift below
would be `nodeIncl` in disguise. -/
theorem ambientOpen_ne_top : ambientOpen.{u} ≠ ⊤ := by
  intro hcon
  have hmem : (fun _ ↦ 1 : ULift.{u} (Fin 2) → ℂ) ∈ ambientOpen.{u} := by
    rw [hcon]
    trivial
  refine (AnalyticSpace.mem_nonvanishing_iff (AnalyticSpace.complexAffineSpace.{u} 2)
    ambientSection.{u}).1 hmem ?_
  rw [eval_ambientSection]
  norm_num

/-- **The node lies in `{1 - z₀z₁ ≠ 0}`**, and it does so *because of its own equation*: on the
node `z₀ z₁ = 0`, so the value of `1 - z₀z₁` is `1`. -/
theorem range_base_nodeIncl_subset :
    Set.range (nodeIncl.{u}).toLRSHom.base ⊆ (ambientOpen.{u} : Set _) := by
  rintro _ ⟨p, rfl⟩
  rw [SetLike.mem_coe, ambientOpen, AnalyticSpace.mem_nonvanishing_iff, eval_ambientSection,
    base_nodeIncl, base_nodeIncl, (mem_zeroLocus_nodeSection_iff p.1).1 p.2]
  norm_num

/-- **The inclusion of the node into `ℂ²`, lifted to the open subspace on which `1 - z₀z₁` is
invertible.** Neither `nodeIncl` nor the lift is an inclusion of one open subspace in another. -/
def nodeInclLift :
    AnalyticSpace.node.{u} ⟶ (AnalyticSpace.complexAffineSpace.{u} 2).restrict ambientOpen.{u} :=
  AnalyticSpace.liftOpen nodeIncl.{u} ambientOpen.{u} range_base_nodeIncl_subset.{u}

/-- **The lift is a factorisation of the inclusion.** -/
theorem nodeInclLift_fac :
    nodeInclLift.{u} ≫ (AnalyticSpace.complexAffineSpace.{u} 2).ofRestrict ambientOpen.{u} =
      nodeIncl.{u} :=
  AnalyticSpace.liftOpen_fac _ _ _

/-- **The lift is the inclusion on points.** -/
theorem base_nodeInclLift (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 2)) :
    ((nodeInclLift.{u}.toLRSHom.base p).1 : ULift.{u} (Fin 2) → ℂ) j = p.1.1 j :=
  congrArg (fun y : AnalyticSpace.complexAffineSpace.{u} 2 ↦ y j)
    (AnalyticSpace.base_liftOpen nodeIncl.{u} ambientOpen.{u} range_base_nodeIncl_subset.{u} p)

/-! ### The instance the `liftRestrict` docstring is about

`AlgebraicGeometry.LocallyRingedSpace.liftRestrict` exists because the open of an analytic space
reaches a call site spelled through `↑X.toPresheafedSpace` rather than `X.toTopCat`. Which
failure that produces depends on the **expected type**: at
`ComplexAnalytic.AnalyticSpace.liftOpen`'s, instance search fails; at the one below — a morphism
into `X.toLocallyRingedSpace.restrict U.isOpenEmbedding` — it succeeds and the
`range_ofRestrict` rewrite fails instead.

This is the second half as a test rather than as a recollection. The first half cannot be one: a
tactic that fails is not recordable. If `IsOpenImmersion (X.ofRestrict …)` ever stops being found
at *this* spelling, the docstring's account becomes wrong and this line breaks.
-/

example (X : AnalyticSpace.{u}) (U : X.Opens) :
    LocallyRingedSpace.IsOpenImmersion
      (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) := inferInstance

/-! ### The lift agrees with `restrictLE` where both apply -/

/-- **Lifting the inclusion of an open subspace along a larger open subspace gives
`restrictLE`.** This is the one instantiation whose answer was known in advance, and it is the
check that `liftOpen` is the map it is supposed to be rather than merely a map. -/
theorem liftOpen_ofRestrict_eq_restrictLE {X : AnalyticSpace.{u}} {V W : X.Opens} (h : V ≤ W) :
    AnalyticSpace.liftOpen (X.ofRestrict V) W
        ((LocallyRingedSpace.range_ofRestrict X.toLocallyRingedSpace V).subset.trans h) =
      X.restrictLE h :=
  AnalyticSpace.hom_ext_restrict W _ _
    ((AnalyticSpace.liftOpen_fac _ _ _).trans (X.restrictLE_fac h).symm)

end

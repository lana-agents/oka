/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the non-vanishing locus and of `liftOpen`

Both declarations tested here are satisfied by degenerate data. `nonvanishing` is an `Opens`, and
`⊤` is one; `liftOpen` produces a morphism into `X|U`, and at `U = ⊤`, or at a `φ` which is
already the inclusion of an open subspace, it produces something the repository already had. So
the checks below are chosen to rule those two readings out.

* **The non-vanishing locus is computed on a space which is not `ℂ^n`.**
  `mem_nonvanishing_nodeCoord_iff` says the non-vanishing locus of the `j`-th coordinate function
  of the node is `{p | p_j ≠ 0}` — the punctured `j`-th axis, which `OkaTest/OpenSubspace.lean`
  constructs by hand as `nodeAxis j`, openness proof included. Here openness comes from
  `ComplexAnalytic.AnalyticSpace.nonvanishing` and is not proved again. It is a **proper nonempty**
  open subset: `nonvanishing_nodeCoord_ne_top` and `ne_bot`.

* **On a space with zero divisors the two loci are disjoint.** `nodeCoord 0 * nodeCoord 1 = 0`
  on the node, so `nonvanishing_nodeCoord_inf_eq_bot` follows from
  `ComplexAnalytic.AnalyticSpace.nonvanishing_mul`. This is what a locus defined through germs
  buys over one defined by hand: it interacts with the ring structure.

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

/-- **The non-vanishing locus of the `j`-th coordinate function of the node is the punctured
`j`-th axis.** `OkaTest/OpenSubspace.lean` builds the same open subset by hand, with its own
continuity argument; here it is `ComplexAnalytic.AnalyticSpace.nonvanishing` and the value is
read off by `ComplexAnalytic.eval_nodeCoord`. -/
theorem mem_nonvanishing_nodeCoord_iff (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 2)) :
    p ∈ (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) ↔ p.1.1 j ≠ 0 := by
  rw [AnalyticSpace.mem_nonvanishing_iff, eval_nodeCoord]

/-- The point of the node whose `j`-th coordinate is `1` and whose other coordinate is `0`. -/
def nodeAxisPoint (j : ULift.{u} (Fin 2)) : AnalyticSpace.node.{u} := by
  classical
  refine ⟨⟨fun l ↦ if l = j then 1 else 0, trivial⟩, (mem_zeroLocus_nodeSection_iff _).2 ?_⟩
  dsimp only
  rcases eq_or_ne (ULift.up 0 : ULift.{u} (Fin 2)) j with h | h
  · rw [if_neg (fun hcon : (ULift.up 1 : ULift.{u} (Fin 2)) = j ↦ by
      simpa using congrArg ULift.down (h.trans hcon.symm)), mul_zero]
  · rw [if_neg h, zero_mul]

lemma nodeAxisPoint_coord (j l : ULift.{u} (Fin 2)) :
    (nodeAxisPoint.{u} j).1.1 l = if l = j then 1 else 0 := rfl

/-- The origin of `ℂ²`, as a point of the node. -/
def nodeOriginPoint : AnalyticSpace.node.{u} :=
  ⟨(⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩ : nodeAmbient.{u}),
    origin_mem_zeroLocus_nodeSection.{u}⟩

/-- **The punctured axis is not everything**: the origin is a point of the node at which the
coordinate vanishes. -/
theorem nonvanishing_nodeCoord_ne_top (j : ULift.{u} (Fin 2)) :
    (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) ≠ ⊤ := by
  intro hcon
  have hmem : nodeOriginPoint.{u} ∈ (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) := by
    rw [hcon]
    trivial
  exact (mem_nonvanishing_nodeCoord_iff nodeOriginPoint.{u} j).1 hmem rfl

/-- **The punctured axis is not empty**: `(1, 0)` and `(0, 1)` are points of the node. -/
theorem nonvanishing_nodeCoord_ne_bot (j : ULift.{u} (Fin 2)) :
    (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) ≠ ⊥ := by
  intro hcon
  have hmem : nodeAxisPoint.{u} j ∈ (AnalyticSpace.node.{u}).nonvanishing (nodeCoord.{u} j) :=
    (mem_nonvanishing_nodeCoord_iff _ j).2
      (by rw [nodeAxisPoint_coord, if_pos rfl]; exact one_ne_zero)
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

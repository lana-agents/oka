/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.MonicHypersurface
import Oka.Analytification.StandardEtaleAnalytification

/-!
# `A[X] ⧸ (F)` is finite over `A^an` when `F` is monic, for a presented base `A`

`Oka/Analytification/MonicHypersurface.lean` proves that the analytification of
`ℂ[x₁, …, x_n, X] ⧸ (G)`, for `G` monic in the last variable, is finite over `ℂ^n`, and its
`ComplexAnalytic.isFinite_analytification_comp_proj` says in terms what that statement is missing
and what it is missing it for:

> **The target is `ℂ^n`, and the Riemann-existence line wants the analytification of a base
> algebra.** … the arrow between the two statements is
> `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp` … **What is missing is not the arrow
> but its hypothesis**: the cancellation needs the composite above to *be* the composite through
> the base algebra's analytification, and no statement in this repository factors it that way.

This file is that factorisation and the theorem it unlocks. Over an arbitrary presentation `g` of
`A`, the structure map `A ⟶ A[X] ⧸ (F)` — `ComplexAnalytic.hypersurfacePresHom`, which
`Oka/Analytification/StandardEtaleAnalytification.lean` already builds — analytifies to a
**finite** morphism as soon as `F` is monic in the last variable. That is the first transfer of
finiteness across `ComplexAnalytic.AnalyticSpace.analytification` in this development in which the
target is not `ℂ^n`.

## The one step that is not bookkeeping

Cancelling `A^an ↪ ℂ^n` needs the composite to `ℂ^n` to be finite, and that composite is the
hypersurface's own inclusion into `ℂ^(n+1)` followed by the projection. But **the image of that
inclusion is not the hypersurface**: it is cut out by the `k` relations of `g` as well as by `F`,
so it is a proper closed subset of `{F = 0}` as soon as `g` has a relation at all, and
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` asks for an equality it cannot supply.

`ComplexAnalytic.isFinite_comp_proj_of_range_subset` is that theorem with the hypothesis weakened
to an inclusion, which is all its proof ever used — both obligations of
`ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` are asked *along the image*,
so a smaller image is never harder. It is in `Oka/AnalyticSpace/MonicProjection.lean` beside the
theorem it generalises, and that theorem is now one line of it and keeps its name and its four
consumers.

## Where `ComplexAnalytic.AnalyticSpace.coordPullback_proj` sits, and why it is here

The coordinates of `ComplexAnalytic.AnalyticSpace.proj` belong under `Oka/AnalyticSpace/`, next to
the projection. **No file there sees both of the declarations it mentions**: `AnalyticSpace.proj`
is in `Oka/AnalyticSpace/ProjectionStalk.lean`, whose transitive imports do not contain
`Oka/AnalyticSpace/HomToComplex.lean`, where `AnalyticSpace.coordPullback` is defined, and the
import in the other direction is absent too. The earliest module whose import closure contains both
is `Oka/Analytification/MonicHypersurface.lean`, this file's own import. So it is stated here,
where it is used, rather than by adding an import edge between two files under `Oka/AnalyticSpace/`
— which is a decision about that directory's shape and not one this file needs to take.

## Main results

- `ComplexAnalytic.AnalyticSpace.coordPullback_proj`: **the `j`-th coordinate of the projection
  `ℂ^(n+1) ⟶ ℂ^n` is the `j`-th of the first `n` coordinates.**
- `ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp`: **the factorisation** — the
  analytified structure map followed by `A^an ↪ ℂ^n` is the hypersurface's own inclusion into
  `ℂ^(n+1)` followed by the projection.
- `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom`: **the analytification of
  `A ⟶ A[X] ⧸ (F)` is finite**, for `F` monic in the last variable.

## What is not here

* **No general finite morphism.** One adjoined root of one monic polynomial is what this covers;
  a module-finite extension is a quotient of an iterated one, and the induction — which needs the
  presentation of the intermediate algebras and a comparison of the two structure maps — is not
  attempted and is not a corollary.
* **Nothing about `ComplexAnalytic.etalePresentation`.** A standard étale algebra is this
  hypersurface with `G` inverted, and inverting `G` destroys finiteness: the punctured parabola
  over the line is the witness, and `Oka/Analytification/MonicHypersurface.lean`'s
  `## What is not here` gives it. Nothing here applies to it, and the localisation is where the
  finite étale line has to say something different.
* **No converse and no degree.** Nothing says the fibres have `G.natDegree` points — that is a
  statement about `ComplexAnalytic.AnalyticSpace.degree` and about multiplicity, and finiteness is
  indifferent to it.
* **No claim that this is a scheme-theoretic statement.** There is no `AlgebraicGeometry.Scheme`
  on this line of files; what is analytified is a presentation, and `A ⟶ A[X] ⧸ (F)` is a map of
  presented `ℂ`-algebras. The scheme-level reading is the reason the statement is wanted and is not
  what is proved.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

variable {n k : ℕ}

/-- **Pulling the `j`-th coordinate of `ℂ^n` back along the projection `ℂ^(n+1) ⟶ ℂ^n` gives the
`j`-th coordinate of `ℂ^(n+1)`**, at the index `ComplexAnalytic.uliftCastSuccEmb` names.

`ComplexAnalytic.AnalyticSpace.proj` is `ComplexAnalytic.AnalyticSpace.okaMap` at
`ComplexAnalytic.coordEmb`, so this is `ComplexAnalytic.Γ_map_okaMapHom_coord` and the two
definitional unfoldings around it. -/
theorem AnalyticSpace.coordPullback_proj (j : ULift.{u} (Fin n)) :
    AnalyticSpace.coordPullback (AnalyticSpace.proj.{u} n) j =
      coord (uliftCastSuccEmb.{u} n j) :=
  Γ_map_okaMapHom_coord (coordEmb (uliftCastSuccEmb.{u} n)) j

variable (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-- **The analytified structure map `(A[X] ⧸ (F))^an ⟶ A^an`, followed by the inclusion of `A^an`
into `ℂ^n`, is the inclusion of `(A[X] ⧸ (F))^an` into `ℂ^(n+1)` followed by the projection.**

The compatibility `Oka/Analytification/MonicHypersurface.lean` names as the missing hypothesis of
the cancellation. Two morphisms into `ℂ^n` agree as soon as their `n` coordinate pullbacks do
(`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace`), and both sides' coordinates are
already computed: on the left by `ComplexAnalytic.coordPullback_analytificationMap_comp` and
`ComplexAnalytic.transported_hypersurfacePresHom`, on the right by naturality of the coordinate
pullback and `ComplexAnalytic.AnalyticSpace.coordPullback_proj`.

The two sides meet because `ComplexAnalytic.uliftCastSuccEmb` and
`ComplexAnalytic.localisationIncl` are the same function — the first bundled as an embedding, the
second not — so the last step is `rfl` and no bridge lemma is needed. **Nothing here reads `F`**:
the equality holds for every `F`, and monicity enters only in the finiteness below. -/
theorem analytificationMap_hypersurfacePresHom_comp :
    analytificationMap.{u} (hypersurfacePresHom.{u} g F) ≫ analytificationInclHom.{u} g =
      analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
        AnalyticSpace.proj.{u} n := by
  refine AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦ ?_
  have hl : AnalyticSpace.coordPullback
      (analytificationMap.{u} (hypersurfacePresHom.{u} g F) ≫ analytificationInclHom.{u} g) j =
      analytificationCoord.{u} (hypersurfacePresentation.{u} g F) (localisationIncl.{u} n j) :=
    (coordPullback_analytificationMap_comp.{u} (hypersurfacePresHom.{u} g F) j).trans
      (transported_hypersurfacePresHom.{u} g F j)
  have hr : AnalyticSpace.coordPullback
      (analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
        AnalyticSpace.proj.{u} n) j =
      analytificationCoord.{u} (hypersurfacePresentation.{u} g F) (localisationIncl.{u} n j) := by
    rw [AnalyticSpace.coordPullback_comp, AnalyticSpace.coordPullback_proj]
    rfl
  exact hl.trans hr.symm

/-- **The analytification of `A ⟶ A[X] ⧸ (F)` is a finite morphism**, for `F` monic in the last
variable and `A` presented by `g`.

`ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp` cancels the closed embedding
`A^an ↪ ℂ^n`, whose base map is injective by
`ComplexAnalytic.isClosedEmbedding_base_analytificationIncl`; the composite it needs is the
factorisation above, and that composite is finite by
`ComplexAnalytic.isFinite_comp_proj_of_range_subset` at the family
`ComplexAnalytic.polyFamily G`. The range condition is an inclusion and not an equality precisely
because the image is cut out by the `k` relations of `g` as well as by `F`; what supplies it is the
`Fin.last`-th component of `ComplexAnalytic.range_base_analytificationIncl`, the others being
discarded.

`G` is the input rather than `F` because monicity *in the last variable* is not a property of a
multivariate polynomial: `ComplexAnalytic.lastVarPolyEquiv` is where that is discussed, and taking
`G` here is the same choice `ComplexAnalytic.isFinite_analytification_comp_proj` makes. -/
theorem isFinite_analytificationMap_hypersurfacePresHom
    (G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)) (hG : G.Monic) :
    AnalyticSpace.IsFinite (analytificationMap.{u}
      (hypersurfacePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm G))) := by
  refine AnalyticSpace.isFinite_of_isFinite_comp _ (analytificationInclHom.{u} g)
    (isClosedEmbedding_base_analytificationIncl.{u} g).injective ?_
  rw [analytificationMap_hypersurfacePresHom_comp]
  refine isFinite_comp_proj_of_range_subset _
    (isClosedEmbedding_base_analytificationIncl.{u} _) (monic_polyFamily.{u} G hG)
    (natDegree_polyFamily.{u} G hG) (continuous_coeff_polyFamily.{u} G) ?_
  refine Set.Subset.trans (Eq.subset (range_base_analytificationIncl.{u} _)) ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  rw [← eval_lastVarPolyEquiv_symm.{u} G]
  have hlast := hz (Fin.last k)
  rwa [hypersurfacePresentation, Fin.snoc_last] at hlast

end ComplexAnalytic

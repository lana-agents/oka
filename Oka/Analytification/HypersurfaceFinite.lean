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

## The iteration is three problems, and the price on record covered only the first two

The bullet under `## What is not here` used to read *"a module-finite extension is a quotient of an
iterated one, and the induction — which needs the presentation of the intermediate algebras and a
comparison of the two structure maps — is not attempted and is not a corollary"*. That sentence
runs three obstructions together, and they are of very different sizes. Measured, on taxis #1379:

* **The second step is free.** `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom` is
  stated over an *arbitrary* presentation `g`, and `ComplexAnalytic.hypersurfacePresentation g F`
  is a presentation of the same shape one variable up. So the second step is the first at a
  different base, the `Fin.snoc` produces exactly the index arithmetic the theorem's binders want,
  and the composite is finite by the `ComplexAnalytic.AnalyticSpace.isFinite_comp` instance with
  **nothing to prove**. *"Is not a corollary"* was right about the general case and wrong about
  this one.
* **The comparison of the two structure maps is one missing composition law.** Both structure maps
  are `ComplexAnalytic.PresHom.ofRename`, and `Oka/Analytification/ChangeOfVariables.lean` had only
  the *inverse-pair* statement about that constructor — `σ ∘ τ = id` giving the identity — which
  says nothing about a tower. The general law is `ComplexAnalytic.PresHom.ofRename_comp`, added
  there rather than here, and with it the two-step extension is one `PresHom` and not a composite.
* **The quotient is the wall, and it is not an induction at all.** A module-finite `A`-algebra is a
  *quotient* of an iterated hypersurface: adjoin one root per module generator, then kill the
  kernel. The surjection is finite on the algebraic side because it is a closed immersion, and what
  that needs analytically is that a surjection of presented algebras has closed-embedding base map.

**The third is reachable from what is here, and this is measured rather than argued.** A surjection
of presented `ℂ`-algebras adds relations and no variables, so it is
`ComplexAnalytic.PresHom.ofRename` at the identity between two presentations in the *same* `n`
variables whose ideals are nested, and its analytification is the inclusion of one zero locus into
a larger one inside one `ℂ^n`. In a spike, deleted and not committed, the statement

    IsClosedEmbedding ⇑(analytificationMap (PresHom.ofRename id h)).base

compiles in about fifteen lines: the triangle `analytificationMap (ofRename id h) ≫
analytificationInclHom b = analytificationInclHom a` by
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` and
`ComplexAnalytic.coordPullback_analytificationMap_comp` — the transported tuple of a rename at the
identity is the source's own coordinates — and then
`ComplexAnalytic.isClosedEmbedding_base_analytificationIncl` **twice** with
`Topology.IsClosedEmbedding.of_comp_iff`. No new topology and no Nullstellensatz.

**It is not here, deliberately.** Nothing would consume it until the general theorem is built, and
this file's own standard is that an unused lemma with an axiom guard is worse than an absence with
a sentence. What the spike buys is the answer to the question the old bullet left open: the wall is
priced, it is low, and the general statement is a construction problem — pick module generators,
build the tower, exhibit the kernel — rather than a missing piece of analytic geometry.

**And the shape of the surjection matters.** What compiles is the same-variables case, which is the
one the module-finite argument produces; a surjection between presentations in *different* numbers
of variables is not of that form and nothing above is evidence about it.

## Main results

- `ComplexAnalytic.AnalyticSpace.coordPullback_proj`: **the `j`-th coordinate of the projection
  `ℂ^(n+1) ⟶ ℂ^n` is the `j`-th of the first `n` coordinates.**
- `ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp`: **the factorisation** — the
  analytified structure map followed by `A^an ↪ ℂ^n` is the hypersurface's own inclusion into
  `ℂ^(n+1)` followed by the projection.
- `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom`: **the analytification of
  `A ⟶ A[X] ⧸ (F)` is finite**, for `F` monic in the last variable.
- `ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom`: **two adjoined roots are one
  renaming** — the composite of the two structure maps is the map of presentations given by the
  inclusion of the old variables into the new, composed.
- `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom`:
  **the analytification of `A ⟶ A[X₁] ⧸ (F₁) ⟶ (A[X₁] ⧸ (F₁))[X₂] ⧸ (F₂)` is finite**, as one
  morphism, for both polynomials monic in their last variable.

## What is not here

* **No general finite morphism, and the section above says which of its three parts is missing.**
  What is here is two adjoined roots; the `m`-step iterate and the quotient are not, and the
  quotient is the one nothing in the repository states.
* **No `m`-step iterate.** `ComplexAnalytic.hypersurfacePresentation` applied `m` times is a
  presentation in `n + m` variables whose `i`-th polynomial lives over `n + i` of them, so the
  tower is a dependent recursion and not a family; nothing here builds it. The two-step case below
  needs no such recursion because the second step is the first at a different base, and that is
  exactly what stops being available once the base is `Nat.rec`.
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

variable (F' : MvPolynomial (ULift.{u} (Fin (n + 1 + 1))) ℂ)

/-- **Adjoining two roots one after the other is one renaming of variables.**

The composite of the two structure maps `A ⟶ A[X₁] ⧸ (F)` and
`A[X₁] ⧸ (F) ⟶ (A[X₁] ⧸ (F))[X₂] ⧸ (F')` is `ComplexAnalytic.PresHom.ofRename` at the two
inclusions of old variables composed — which is what the sentence *"a comparison of the two
structure maps"* in this file's `## What is not here` used to ask for.

`ComplexAnalytic.PresHom.ofRename_comp` is the whole proof, because
`ComplexAnalytic.hypersurfacePresHom` **is** an `ofRename` on both sides; the second step is the
first at the base `ComplexAnalytic.hypersurfacePresentation g F`, which is a presentation like any
other, so no re-indexing happens anywhere.

`h` is an argument for the reason it is one there: it occurs only under `ofRename`, whose value
does not depend on it, and `ComplexAnalytic.rename_mem_presentationIdeal` supplies it from the two
memberships `hypersurfacePresHom` already carries. **Nothing here reads `F` or `F'`** — the
equality holds for every pair, and monicity enters only in the finiteness below. -/
theorem hypersurfacePresHom_comp_hypersurfacePresHom
    (h : ∀ j, MvPolynomial.rename (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (g j) ∈
      presentationIdeal.{u}
        (hypersurfacePresentation.{u} (hypersurfacePresentation.{u} g F) F')) :
    (hypersurfacePresHom.{u} (hypersurfacePresentation.{u} g F) F').comp
        (hypersurfacePresHom.{u} g F) =
      PresHom.ofRename.{u} (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) h :=
  PresHom.ofRename_comp.{u} _ _ _ _ _

/-- **The analytification of `A ⟶ (A[X₁] ⧸ (F₁))[X₂] ⧸ (F₂)` is finite**, for both polynomials
monic in their last variable, as one morphism rather than as a composite.

`ComplexAnalytic.analytificationMap_comp` splits it, and then the two factors are the one-step
theorem above at two different bases: at `g` for the first, and at
`ComplexAnalytic.hypersurfacePresentation g ((lastVarPolyEquiv n).symm G₁)` for the second, which
is a presentation of the same shape one variable up. **The last step is `infer_instance`**, because
`ComplexAnalytic.AnalyticSpace.isFinite_comp` is an instance and the two `haveI`s are what it
needs; nothing is proved here that the one-step theorem did not already prove.

`ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom` above says the morphism this is
about is one `ComplexAnalytic.PresHom.ofRename`, so this is a statement about a single map of
presentations and not only about a factorisation of one. -/
theorem isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom
    (G₁ : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)) (hG₁ : G₁.Monic)
    (G₂ : Polynomial (MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)) (hG₂ : G₂.Monic) :
    AnalyticSpace.IsFinite (analytificationMap.{u}
      ((hypersurfacePresHom.{u}
          (hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm G₁))
          ((lastVarPolyEquiv.{u} (n + 1)).symm G₂)).comp
        (hypersurfacePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm G₁)))) := by
  haveI h₁ := isFinite_analytificationMap_hypersurfacePresHom.{u} g G₁ hG₁
  haveI h₂ := isFinite_analytificationMap_hypersurfacePresHom.{u}
    (hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm G₁)) G₂ hG₂
  rw [analytificationMap_comp]
  infer_instance

end ComplexAnalytic

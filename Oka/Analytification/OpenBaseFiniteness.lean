/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.MonicHypersurface
import Oka.AnalyticSpace.OpenBaseProjection

/-!
# The hypersurface over an open subset of the base, and where a second polynomial cannot vanish

`Oka/AnalyticSpace/OpenBaseProjection.lean` proves that a closed subspace of the cylinder over an
open `V ⊆ ℂ^n`, cut out by a family of monic polynomials of fixed degree, is finite over `V`. This
file is the first consumer of `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` **whose
source is an analytification**, at `ℂ[x₁, …, x_n, X] ⧸ (F)` for `F` monic in the last variable.

The consumers that came before it split two ways and neither way reaches an analytification.
`ComplexAnalytic.isFinite_comp_projRestrict_of_isCutOutBy` and
`ComplexAnalytic.isFinite_comp_projRestrict_of_monic` are **restatements**: each takes the source
`i` as a hypothesis and exhibits no space at all, so neither has a source to be an analytification
of. The sources that *are* exhibited are both in the test tree and both hand-written
`ComplexAnalytic.AnalyticSpace.okaMap`s — the parabola of `OkaTest/OpenBaseProjection.lean`, and
the transcendental curve of `OkaTest/HolomorphicFamily.lean`, which reaches the theorem through
the second restatement. **So this is also the first consumer in the library that supplies a source
rather than passing one through**, and that is the same fact said the other way round.

**An earlier draft of this paragraph said that nothing anywhere consumed the theorem and that this
file was its first consumer, and that was false when it was written**: the theorem was already
named in seven files and applied in three. It is recorded here rather than quietly deleted because
the way it went wrong is reusable — the hits sort `Oka/` before `OkaTest/`, so a
`git grep -n … | head` at the default ten lines stops one line short of the test file, and both
the draft and the first review of it made that cut. **Count with `git grep -c` before claiming
that nothing anywhere does something.**

The reason to want it is `Oka/Analytification/MonicHypersurface.lean`'s `## What is not here`,
which said, until this file landed and the same push corrected it, what a standard étale algebra
needs and this repository did not have:

> What is true is that the inversion becomes **vacuous over an open subset of the base**, and that
> is the shape of the remaining work rather than a lemma anyone has. … Closedness in hand, the
> image of the closed set where `F` and `G` both vanish is closed; above its complement `V` no
> point of the hypersurface has `G = 0`

Both halves of that sentence are here. **They are two independent statements and the file is
arranged to keep them apart**, which is the one thing the plan as written does not make clear.

## The finiteness needs no `V` at all, and that is worth saying first

`ComplexAnalytic.isFinite_analytification_comp_projRestrict` holds over **every** open `V`. It is
the one-relation hypersurface restricted to the cylinder, and restricting a finite morphism along
an open of the base is not where any content is: the three hypotheses on the family of polynomials
are `Oka/Analytification/MonicHypersurface.lean`'s three, composed with `↥V → (ULift (Fin n) → ℂ)`,
because `Polynomial.isClosed_fst_image_of_monic` and its companion are stated over an arbitrary
parameter space and so instantiate at `V` rather than at `ℂ^n`.

**So `V` is not what makes the projection finite.** What `V` is for is the *source*: over the
complement of `ComplexAnalytic.hypersurfaceCommonZeroImage` the locus `{G ≠ 0}` is all of the
hypersurface, so the space that a localised algebra would analytify to is the space this theorem is
already about. That is `ComplexAnalytic.eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage`, and it
is where `G` does the only work it does in this file.

## Why the bad set is an image and not a set-builder

`ComplexAnalytic.hypersurfaceCommonZeroImage` is defined as the image, under the projection of the
hypersurface, of the locus where `G` vanishes on it — **not** as
`{w | ∃ X, F (w, X) = G (w, X) = 0}`. The two are the same set and only the first is closed for a
reason already in the tree: `ComplexAnalytic.isFinite_analytification_comp_proj` makes the
projection of `{F = 0}` a **closed map**, since `ComplexAnalytic.AnalyticSpace.IsFinite`'s first
field is `isClosedMap`, and the image formulation is the one that consumes it. Written as a
set-builder over the base, closedness would be a second theorem with no shorter proof than
"rewrite it as the image".

## The open set can be empty, and that is proved rather than warned about

Nothing in the plan on record asks whether the complement of the bad set is ever nonempty, and if
it is empty every statement above holds vacuously. Both directions are settled here at witnesses:

* `ComplexAnalytic.hypersurfaceCommonZeroImage_one` — for `G = 1` the bad set is **empty**, so `V`
  may be all of `ℂ^n`. That is the case of no localisation, where this file's theorem is
  `ComplexAnalytic.isFinite_analytification_comp_proj` read over the cylinder.
* `ComplexAnalytic.hypersurfaceCommonZeroImage_X` — for `F = G = X`, the last coordinate, the bad
  set is **everything**, so `V` is empty and the theorem says nothing. The mechanism is not special
  to `X`: it is that `G` vanishes on the whole hypersurface, and then the bad set is the image of
  the whole hypersurface, which is all of `ℂ^n` whenever the projection is onto.

**So non-vacuity is a hypothesis on the pair `(F, G)` that nothing here supplies**, and a consumer
that wants a nonempty `V` has to produce one.
`Oka/Analytification/StandardEtaleAnalytification.lean` faced the same question from the other
side — taxis #1196 was filed because nothing said the open subspace it constructs is ever
nonempty — and that is the file with the standing to answer it,
since `StandardEtalePair.cond` is a hypothesis about `F` and `G` together and no such hypothesis is
available here.

## Main definitions

- `ComplexAnalytic.hypersurfaceCommonZeroImage`: **the image in `ℂ^n` of the points of the
  hypersurface `{F = 0}` at which `G` also vanishes.**

## Main results

- `ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage`: **it is closed**, so its complement is an
  open subset of the base.
- `ComplexAnalytic.eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage`: **above the complement, `G`
  does not vanish on the hypersurface** — the vacuity of the inversion, and the only statement here
  that reads `G` twice.
- `ComplexAnalytic.isFinite_analytification_comp_projRestrict`: **the hypersurface over the
  cylinder is finite over `V`**, for every open `V` and with no hypothesis relating `V` to `G`.
- `ComplexAnalytic.hypersurfaceCommonZeroImage_one` and
  `ComplexAnalytic.hypersurfaceCommonZeroImage_X`: **the two witnesses** — the bad set is empty for
  `G = 1` and is everything for `F = G = X`, so the complement is `ℂ^n` in one case and empty in
  the other.

## What is not here

* **No standard étale algebra, and no `IsFiniteEtale`.** The unrestricted statement is **false** —
  taxis #1112 carries the counterexample, the punctured parabola over the line — and nothing here
  states it. Identifying the source of this theorem with the analytification of a *localised*
  algebra is the step `ComplexAnalytic.etaleAnalytificationIso` would be spent on, and it is not
  taken: the vacuity below is a statement about points, not an isomorphism of analytic spaces.
* **Nothing about the stalks**, so no local-isomorphism half and no `IsFiniteEtale`. That is the
  other half of taxis #1112 and it is where `Oka/AnalyticSpace/SimpleZeroTopology.lean` and
  `Oka/AnalyticSpace/OpenBaseProjection.lean`'s stalk half live.
* **No monic lift chosen.** `F` is a hypothesis here, monic in the last variable over
  `ℂ[x₁, …, x_n]`, and `StandardEtalePair.monic_f` is monicity over a *presented* base — a
  different statement. `Oka/Analytification/MonicHypersurface.lean` records that a monic lift
  exists because the leading coefficient `1` lifts to `1`; choosing it belongs where the standard
  étale pair is, not here.
* **No general-degree version of the emptiness witness.** `hypersurfaceCommonZeroImage_X` is at
  `F = G = X`, where the root of the fibre polynomial is `0` and no field theory is needed. The
  same holds for every monic `F` of positive degree, because a monic polynomial of positive degree
  over `ℂ` has a root — but that is algebraic closedness, `IsAlgClosed.exists_root` is not in this
  file's import closure, and paying an import for a second witness of a fact one witness already
  settles is the wrong trade. **It is stated as a reason and not as a compiled claim.**
* **No presented base.** Everything here is over `ℂ^n`, which is the shape
  `ComplexAnalytic.isFinite_analytification_comp_proj` has. Over a presented `A` the projection is
  `Oka/Analytification/HypersurfaceFinite.lean`'s and the cylinder would be over `A^an`, for which
  `Oka/AnalyticSpace/OpenBaseProjection.lean` has no analogue.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n : ℕ} (F G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))

/-! ### The bad set and its complement -/

/-- **The image in `ℂ^n` of the points of the hypersurface `{F = 0}` at which `G` also vanishes.**

An image and not a set-builder over the base, for the reason the module docstring gives: closedness
comes from `ComplexAnalytic.isFinite_analytification_comp_proj` being a closed map, and only the
image formulation consumes that.

`F` and `G` enter asymmetrically and deliberately. `F` is the hypersurface — the space whose points
are taken — and is the one that has to be monic for anything below to hold; `G` is read only as a
condition on those points and no hypothesis is placed on it anywhere in this file. -/
def hypersurfaceCommonZeroImage :
    Set ((AnalyticSpace.complexAffineSpace.{u} n).toLocallyRingedSpace) :=
  ⇑(AnalyticSpace.Hom.toLRSHom (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm F] ≫
      AnalyticSpace.proj.{u} n)).base ''
    (⇑(AnalyticSpace.Hom.toLRSHom
        (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm F])).base ⁻¹'
      {z | MvPolynomial.eval z ((lastVarPolyEquiv.{u} n).symm G) = 0})

/-- **The bad set is closed**, so its complement is an open subset of the base.

Three steps and none of them is new: the zero set of `G` in `ℂ^(n+1)` is closed because
`MvPolynomial.continuous_eval` says a polynomial is continuous; its preimage under the inclusion of
the hypersurface is closed; and the image of that is closed because
`ComplexAnalytic.isFinite_analytification_comp_proj` makes the projection of the hypersurface a
finite morphism, whose **first field** is `ComplexAnalytic.AnalyticSpace.IsFinite.isClosedMap`.

`F.Monic` is used exactly once **in this proof**, in that last step. It is also the only
hypothesis anywhere in the file, which is a different claim and not a stronger one:
`ComplexAnalytic.isFinite_analytification_comp_projRestrict` asks for it as well and spends it
twice. What no result here asks for is a hypothesis on `G`. -/
theorem isClosed_hypersurfaceCommonZeroImage (hF : F.Monic) :
    IsClosed (hypersurfaceCommonZeroImage.{u} F G) := by
  haveI := isFinite_analytification_comp_proj.{u} F hF
  refine AnalyticSpace.IsFinite.isClosedMap _ ?_
  refine IsClosed.preimage ?_ ?_
  · exact (AnalyticSpace.Hom.toLRSHom
      (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm F])).base.hom.continuous
  · exact isClosed_eq (MvPolynomial.continuous_eval _) continuous_const

/-- **Above the complement of the bad set, `G` does not vanish on the hypersurface.**

This is the vacuity of the inversion, and it is the whole of what an open subset of the base buys:
the theorem below is finite over every `V`, and this is the statement that says what is special
about a `V` avoiding `ComplexAnalytic.hypersurfaceCommonZeroImage`.

**It is a statement about points and not an isomorphism of spaces.** Turning it into the assertion
that the source below *is* the analytification of the localised algebra is where
`ComplexAnalytic.etaleAnalytificationIso` would be spent, and that step is not taken here.

The proof is the definition read backwards — a point of the hypersurface at which `G` vanishes is
by construction in the image — so it is `fun h ↦ hy ⟨y, h, rfl⟩` and needs no monicity. -/
theorem eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage
    (y : (AnalyticSpace.analytification.{u}
      ![(lastVarPolyEquiv.{u} n).symm F]).toLocallyRingedSpace)
    (hy : ⇑(AnalyticSpace.Hom.toLRSHom
        (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm F] ≫
          AnalyticSpace.proj.{u} n)).base y ∉ hypersurfaceCommonZeroImage.{u} F G) :
    MvPolynomial.eval (⇑(AnalyticSpace.Hom.toLRSHom
        (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm F])).base y)
      ((lastVarPolyEquiv.{u} n).symm G) ≠ 0 :=
  fun h ↦ hy ⟨y, h, rfl⟩

/-! ### The finiteness, over every open subset of the base -/

/-- **The hypersurface over the cylinder is finite over `V`**, for every open `V ⊆ ℂ^n` and for
every monic `F`, with no hypothesis relating `V` to anything.

This is the first consumer of `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` whose
source is an analytification, and not its first consumer — the module docstring names the three
that came before. Its four hypotheses:

* the closed embedding is `ComplexAnalytic.isClosedEmbedding_base_restrictHom` applied to
  `ComplexAnalytic.isClosedEmbedding_base_analytificationIncl` — restricting a closed embedding
  along an open of the target keeps it;
* the three conditions on the family of fibre polynomials are
  `ComplexAnalytic.monic_polyFamily`, `ComplexAnalytic.natDegree_polyFamily` and
  `ComplexAnalytic.continuous_coeff_polyFamily` composed with the inclusion `↥V → ℂ^n`, which is
  what `Oka/AnalyticSpace/OpenBaseProjection.lean` means by stating them over an arbitrary
  parameter space;
* the range condition is `ComplexAnalytic.mem_range_base_restrictHom_iff` — a point of the
  restricted target is in the range exactly when it is in the unrestricted one — followed by
  `ComplexAnalytic.range_base_analytificationIncl` and
  `ComplexAnalytic.eval_lastVarPolyEquiv_symm`.

**The range step is built with `Set.ext` and `Iff.trans` rather than with `rw`.** That shape is
not this file's invention: it is `ComplexAnalytic.range_base_parabolaPunctured`'s in
`OkaTest/OpenBaseProjection.lean` and `ComplexAnalytic.range_base_curvePunctured`'s in
`OkaTest/HolomorphicFamily.lean`. What is stated nowhere else, and is the reason to keep the
paragraph, is *why* `rw` is unavailable. `ComplexAnalytic.cylinder V` is declared at
`TopologicalSpace.Opens (ULift (Fin (n + 1)) → ℂ)` while
`ComplexAnalytic.AnalyticSpace.restrict` asks for the space's own `Opens`, so a goal mentioning
`(complexAffineSpace (n + 1)).restrict (cylinder V)` is not type-correct at `instances`
transparency and `rw` cannot build its motive — it fails with *"Did not find an occurrence of the
pattern"* on a pattern that is visibly present. Supplying the `Iff` as a term instead sidesteps
the motive entirely. -/
theorem isFinite_analytification_comp_projRestrict (hF : F.Monic)
    (V : Opens (ULift.{u} (Fin n) → ℂ)) :
    AnalyticSpace.IsFinite
      (AnalyticSpace.restrictHom (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm F])
          (cylinder.{u} V) ≫ AnalyticSpace.projRestrict.{u} V) := by
  refine isFinite_comp_projRestrict_of_range_eq (d := F.natDegree) _
    (isClosedEmbedding_base_restrictHom
      (isClosedEmbedding_base_analytificationIncl.{u} _) (cylinder.{u} V))
    (q := fun w : ↥V ↦ polyFamily.{u} F w)
    (fun w ↦ monic_polyFamily.{u} F hF w)
    (fun w ↦ natDegree_polyFamily.{u} F hF w)
    (fun j ↦ (continuous_coeff_polyFamily.{u} F j).comp continuous_subtype_val) ?_
  refine Set.ext fun y ↦ (mem_range_base_restrictHom_iff
    (AnalyticSpace.Hom.toLRSHom (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm F]))
    (cylinder.{u} V) y).trans ?_
  have hr : Set.range ⇑(AnalyticSpace.Hom.toLRSHom
      (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm F])).base =
      {z | ∀ j, MvPolynomial.eval z (![(lastVarPolyEquiv.{u} n).symm F] j) = 0} :=
    range_base_analytificationIncl.{u} _
  rw [hr]
  simp only [Fin.forall_fin_one, Matrix.cons_val_zero]
  exact Iff.of_eq (congrArg (fun t : ℂ ↦ t = 0) (eval_lastVarPolyEquiv_symm.{u} F _))

/-! ### The two witnesses, in both directions -/

/-- **With nothing inverted the bad set is empty**, so the open subset of the base may be all of
`ℂ^n`.

The case `G = 1` is the case of no localisation, and it is here to say that the theorem above is
not vacuous for want of a `V`: with this `G` every open `V` avoids the bad set, including `⊤`. No
monicity is used and the proof is that `1 ≠ 0` in `ℂ`. -/
theorem hypersurfaceCommonZeroImage_one :
    hypersurfaceCommonZeroImage.{u} (n := n) F 1 = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro w ⟨y, hy, -⟩
  simp only [map_one] at hy
  exact one_ne_zero hy

/-- **The bad set can be everything, and then the open subset of the base is empty and the theorem
above says nothing.**

At `F = G = X` — the last coordinate in both roles — the hypersurface is the hyperplane where that
coordinate vanishes, `G` vanishes at every one of its points, and its projection to `ℂ^n` is onto.
So the bad set is all of `ℂ^n` and its complement is empty.

**The mechanism is not special to `X`.** What makes the bad set everything is that `G` vanishes on
the whole hypersurface and the projection is onto, and the projection is onto whenever `F` is monic
of positive degree — over `ℂ` the fibre polynomial then has a root. That general statement is not
proved here and the `## What is not here` section says why: it is algebraic closedness, and this
file does not import it. `X` needs none of that, because its root is `0`.

Read together with `ComplexAnalytic.hypersurfaceCommonZeroImage_one`, the pair says that **the size
of the open subset of the base is a hypothesis on `(F, G)` and not a theorem**: it ranges over
everything from `∅` to `ℂ^n` and nothing in this file narrows it. -/
theorem hypersurfaceCommonZeroImage_X :
    hypersurfaceCommonZeroImage.{u} (n := n) Polynomial.X Polynomial.X = Set.univ := by
  refine Set.eq_univ_of_forall fun w ↦ ?_
  set z : ULift.{u} (Fin (n + 1)) → ℂ := (uliftSnocHomeo.{u} n).symm (w, 0) with hz
  have hzero : MvPolynomial.eval z ((lastVarPolyEquiv.{u} n).symm (Polynomial.X :
      Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))) = 0 := by
    rw [eval_lastVarPolyEquiv_symm.{u}, hz, Homeomorph.apply_symm_apply]
    simp [polyFamily]
  have hmem : z ∈ Set.range ⇑(AnalyticSpace.Hom.toLRSHom
      (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm
        (Polynomial.X : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))])).base := by
    have hr : Set.range ⇑(AnalyticSpace.Hom.toLRSHom
        (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm
          (Polynomial.X : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))])).base =
        {y | ∀ j, MvPolynomial.eval y (![(lastVarPolyEquiv.{u} n).symm
          (Polynomial.X : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))] j) = 0} :=
      range_base_analytificationIncl.{u} _
    rw [hr]
    intro j
    fin_cases j
    exact hzero
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_, ?_⟩
  · change MvPolynomial.eval _ _ = 0
    rw [hy]
    exact hzero
  · have h1 : ⇑(AnalyticSpace.proj.{u} n).toLRSHom.base z = w := by
      rw [base_proj_eq.{u}, hz]
      simp
    exact (congrArg (⇑(AnalyticSpace.proj.{u} n).toLRSHom.base) hy).trans h1

end

end ComplexAnalytic

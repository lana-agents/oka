/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CoverFunctoriality

/-!
# Two presentations of each member give the same `X^an`

`Oka/Analytification/AffineCover.lean` builds `X^an` from a cover as *data* — an index type, a
presentation for each index, a polynomial cutting out each overlap, and an isomorphism of the two
descriptions of each overlap — and the construction depends on all of it. **Nothing so far says
that two data describing the same geometry give the same space.** This file is the first
instalment of that, and it is the smallest one: the two data share an index type and their
members are isomorphic *as presentations*.

## What is varied, and it is less than the name "cover independence" suggests

The two inputs here have the **same index type**, so the members correspond one to one and there
is no reindexing; the overlaps sit at the same pairs; and both `hrange` and `hcocycle` are asked
for on each side separately. What varies is only the **presentation of each member** — an
isomorphism `ψ i : obj i ≅ obj' i` in `ComplexAnalytic.Presentation` — and, with it, everything
downstream of a presentation: the polynomials cutting out the overlaps, the identifications of
the overlaps, and the two triple-overlap hypotheses.

**The honest name for this is member-wise presentation independence.** taxis #1107 lists what is
still missing: reindexing along an equivalence of index types, refinement, a definition of
*admissible*, and the functor.

## The caller supplies two compatibility hypotheses and they do not reduce to one

`ComplexAnalytic.coverMap` asks for agreement over the overlaps, and this file asks for it twice —
once for `ψ.hom` and once for `ψ.inv`. **That is not redundancy and it is worth saying why, since
it is the first question a reader has.** The two hypotheses are equations over *different spaces*:
the first is about `ComplexAnalytic.coverPart obj poly i j` and the second about
`ComplexAnalytic.coverPart obj' poly' i j`. Those are open subspaces cut out by `poly i j` and
`poly' i j`, which do not even live in the same type — `poly i j` is a polynomial in
`(obj i).n` variables and `poly' i j` in `(obj' i).n` — so neither hypothesis is a statement the
other could imply.

## The proof, and it does not touch a glue datum

Both round trips go through `ComplexAnalytic.coverAnalytification_hom_ext` and
`ComplexAnalytic.coverIota_comp_coverMap`, which is what
`Oka/Analytification/CoverFunctoriality.lean` set up for exactly this: a morphism out of `X^an` is
determined by its restrictions, so the composite is identified by restricting it. Neither
`ComplexAnalytic.coverMap_id` nor `ComplexAnalytic.coverMap_comp` is used — the composite's family
is `fun i ↦ (ψ i).hom ≫ (ψ i).inv` rather than `fun i ↦ 𝟙`, so going through the two laws would
need a congruence step that going through uniqueness directly does not.

**One trap, recorded because four rewrites fail on it.** After `simp` the residual goal *displays*
as `F.map h ≫ F.map h⁻¹ ≫ ι`, and `rw [← Functor.map_comp]`, `rw [← Functor.map_comp_assoc]`,
`simp [← Functor.map_comp]` and `simp [← Functor.map_comp_assoc]` all fail with *"did not find an
occurrence of the pattern"*. This is the pathology `Oka/CategoryTheory/GlueData.lean`'s module
docstring predicts by name — the objects carry unreduced `ComplexAnalytic.coverAnalytification`
projections — and it is the fifth file on this line of work to hit it.
`CategoryTheory.Iso.hom_inv_id_assoc` at `ComplexAnalytic.analytificationFunctor.mapIso` names the
fact instead of asking `simp` to find it, and that is what the proofs below use.

**And they normalise with `simp only` and an explicit list rather than with `simp`**, which is not
a style preference: `lake build --wfail` runs the `flexible` linter, and a bare `simp` followed by
an `exact` that modifies the same goal is a **build failure** on this project rather than a
warning. The list the linter itself suggests is the one below, and
`ComplexAnalytic.analytificationFunctor_obj` is in it — the fourth consumer of a lemma whose own
docstring predicts that every consumer of the functor spells its object the other way.

## Main definitions

- `ComplexAnalytic.coverAnalytificationIso`: **the isomorphism `X^an ≅ X'^an`.**

## Main results

- `ComplexAnalytic.coverMap_hom_inv` and `ComplexAnalytic.coverMap_inv_hom`: the two round trips,
  stated as theorems beside the isomorphism rather than inlined into its fields, so that a caller
  who wants one of them need not project.

## What is not here

* **No reindexing.** The two index types are the same type, not equivalent types. Allowing an
  `Equiv` is taxis #1107's second increment and is **not** a corollary of this one: the round trip
  then leaves a transport over `e.symm (e i)` inside `ComplexAnalytic.coverIota`'s index, where
  `obj (e.symm (e i))` and `obj i` are propositionally and not definitionally equal, and four
  standard tactics leave it open. That was measured before this file was written.
* **No refinement, and no scheme.** Nothing here says the two data describe the same scheme —
  there is no scheme in this line of files at all, and
  `Oka/Analytification/CoverFunctoriality.lean` and `Oka/Analytification/AffineCover.lean` each
  argue in a titled section why. taxis #1107's headline speaks of two *admissible covers of a
  scheme*, and **admissible is a notion this repository does not have**; defining it is that
  issue's fourth increment and comes before proving anything about it.
* **No naturality.** That the isomorphism commutes with `ComplexAnalytic.coverMap` out of either
  side, or with the comparison morphisms of `Oka/Analytification/CoverComparison.lean`, is not
  stated. Nothing consumes it yet.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj poly i j k ≫
        coverTransitionHom.{u} obj poly glue i j).base ⊆
      (coverOpen.{u} obj poly j k : Set (coverSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      coverTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)
  (obj' : J → Presentation.{u})
  (poly' : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj' i).n)) ℂ)
  (glue' : ∀ i j : J, coverOverlap.{u} obj' poly' i j ≅ coverOverlap.{u} obj' poly' j i)
  (hrange' : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (coverTripleIncl.{u} obj' poly' i j k ≫
        coverTransitionHom.{u} obj' poly' glue' i j).base ⊆
      (coverOpen.{u} obj' poly' j k : Set (coverSpace.{u} obj' j)))
  (hsymm' : ∀ i j : J, glue' j i = (glue' i j).symm)
  (hcocycle' : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    coverTriple.{u} obj' poly' glue' hrange' i j k hij hik hjk ≫
      coverTriple.{u} obj' poly' glue' hrange' j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} obj' poly' glue' hrange' k i j hik.symm hjk.symm hij = 𝟙 _)
  (ψ : ∀ i : J, obj i ≅ obj' i)

/-! ### The two compatibility hypotheses -/

variable (hcomm : ∀ i j : J, i ≠ j →
  coverIncl.{u} obj poly i j ≫
      (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' id
        (fun i ↦ (ψ i).hom) i).toLRSHom =
    (coverTransition.{u} obj poly glue i j).hom ≫ coverIncl.{u} obj poly j i ≫
      (coverMapPart.{u} obj obj' poly' glue' hrange' hsymm' hcocycle' id
        (fun i ↦ (ψ i).hom) j).toLRSHom)
  (hcomm' : ∀ i j : J, i ≠ j →
    coverIncl.{u} obj' poly' i j ≫
        (coverMapPart.{u} obj' obj poly glue hrange hsymm hcocycle id
          (fun i ↦ (ψ i).inv) i).toLRSHom =
      (coverTransition.{u} obj' poly' glue' i j).hom ≫ coverIncl.{u} obj' poly' j i ≫
        (coverMapPart.{u} obj' obj poly glue hrange hsymm hcocycle id
          (fun i ↦ (ψ i).inv) j).toLRSHom)

/-! ### The isomorphism -/

/-- **The two induced morphisms compose to the identity of `X^an`.**

`ComplexAnalytic.coverAnalytification_hom_ext` and `ComplexAnalytic.coverIota_comp_coverMap`: the
composite restricts on the `i`-th member to `analytificationFunctor.map ((ψ i).hom ≫ (ψ i).inv)`
followed by the inclusion, and that functor sends an isomorphism's round trip to the identity. -/
theorem coverMap_hom_inv :
    coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm' hcocycle'
        id (fun i ↦ (ψ i).hom) hcomm ≫
      coverMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj poly glue hrange hsymm hcocycle
        id (fun i ↦ (ψ i).inv) hcomm' = 𝟙 _ :=
  coverAnalytification_hom_ext.{u} obj poly glue hrange hsymm hcocycle _ _ fun i ↦ by
    simp only [coverIota_comp_coverMap_assoc, analytificationFunctor_obj, id_eq, Category.assoc,
      coverIota_comp_coverMap, Category.comp_id]
    exact (analytificationFunctor.{u}.mapIso (ψ i)).hom_inv_id_assoc _

/-- **And the other way round**, on `X'^an`. -/
theorem coverMap_inv_hom :
    coverMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj poly glue hrange hsymm hcocycle
        id (fun i ↦ (ψ i).inv) hcomm' ≫
      coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm' hcocycle'
        id (fun i ↦ (ψ i).hom) hcomm = 𝟙 _ :=
  coverAnalytification_hom_ext.{u} obj' poly' glue' hrange' hsymm' hcocycle' _ _ fun i ↦ by
    simp only [coverIota_comp_coverMap_assoc, analytificationFunctor_obj, id_eq, Category.assoc,
      coverIota_comp_coverMap, Category.comp_id]
    exact (analytificationFunctor.{u}.mapIso (ψ i)).inv_hom_id_assoc _

/-- **Two presentations of each member give canonically isomorphic analytifications.**

Both morphisms are `ComplexAnalytic.coverMap`, so the isomorphism restricts on each member to the
analytified isomorphism of presentations — which is what says it is the intended one and not
merely one of the right type, and is `ComplexAnalytic.coverIota_comp_coverMap` at each of them. -/
def coverAnalytificationIso :
    coverAnalytification.{u} obj poly glue hrange hsymm hcocycle ≅
      coverAnalytification.{u} obj' poly' glue' hrange' hsymm' hcocycle' where
  hom := coverMap.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue' hrange' hsymm'
    hcocycle' id (fun i ↦ (ψ i).hom) hcomm
  inv := coverMap.{u} obj' poly' glue' hrange' hsymm' hcocycle' obj poly glue hrange hsymm
    hcocycle id (fun i ↦ (ψ i).inv) hcomm'
  hom_inv_id := coverMap_hom_inv.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue'
    hrange' hsymm' hcocycle' ψ hcomm hcomm'
  inv_hom_id := coverMap_inv_hom.{u} obj poly glue hrange hsymm hcocycle obj' poly' glue'
    hrange' hsymm' hcocycle' ψ hcomm hcomm'

end

end ComplexAnalytic

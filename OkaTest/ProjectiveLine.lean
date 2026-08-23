/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# `ℙ¹`, glued from two copies of the affine line

`ComplexAnalytic.coverGlueData` takes a family of presentations, a distinguished open of each
member for every other member, and an isomorphism identifying the two descriptions of each
overlap, and returns an `AlgebraicGeometry.LocallyRingedSpace.GlueData`. `OkaTest/AffineCover.lean`
instantiates it at three copies of the node glued along the punctured axis, which is the smallest
input that exercises `t'` and the cocycle condition — and it records the gap this file closes:

> the transition here is the identity, so nothing exercises a *non-trivial* algebra isomorphism
> between the two descriptions of an overlap; `ℙ¹` from two copies of `𝔸¹` with `z ↦ 1/z` is the
> example that would.

`glue` is the one input to `ComplexAnalytic.coverGlueData` that the members and their opens do
not determine: it says *how* the two descriptions of an overlap are identified. The only other
place in this repository where it is supplied, `OkaTest/AffineCover.lean`, supplies `Iso.refl`.
Here it is `ComplexAnalytic.lineSwapIso`, the automorphism of `ℂ[z, t] ⧸ (t z - 1)` exchanging `z`
and `t` — which is `z ↦ 1/z` — and `ComplexAnalytic.lineSwapIso_ne_refl` proves it is not the
identity.

## Why two members, when three was the smallest honest test

The two examples are complementary and the reason is one measurement. `coverGlueData`'s `hrange`
and `hcocycle` are quantified over triples of **pairwise distinct** indices, because that is all
`CategoryTheory.GlueData'` consumes, and a two-element index type has no such triple. So:

* with three members both hypotheses have content and `t'` is exercised — that is
  `OkaTest/AffineCover.lean`, and it is the smallest honest test of the *construction*;
* with two members both are vacuous (`ComplexAnalytic.pair_no_distinct_triple`) and everything
  reduces to the transition — that is this file, and it is the smallest interesting *space*.

## What is proved here

* **It is a gluing of two copies of `𝔸¹` along `D(z)`**, and `D(z)` is neither `⊤` nor `⊥`
  (`ComplexAnalytic.localisationOpen_lineRel_ne_top` and `…_ne_bot`), so this is not two copies
  glued along everything — which would return one copy — nor along nothing.
* **The transition is not the identity.**  `ComplexAnalytic.lineSwapIso_ne_refl`, by separating
  the two variables of `ℂ[z, t] ⧸ (t z - 1)` at the point `(z, t) = (2, 2⁻¹)`, which is a zero of
  the relation. This is the statement that distinguishes this example from the one in
  `OkaTest/AffineCover.lean`.
* **Neither member is the whole space.**
  `ComplexAnalytic.not_surjective_ι_projectiveLineGlueData`: the origin of `𝔸¹` lies off `D(z)`,
  so it is glued to nothing, and its image under the other member's inclusion is not in the range
  of this one's. With `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` and
  `ComplexAnalytic.coverGlueData_ι_isOpenImmersion` that says the glued space is covered by two
  copies of `𝔸¹` and is neither of them.

## What is not proved here, and is not claimed anywhere below

**Nothing here says the glued space is `ℙ¹`.** It is glued from the two charts of `ℙ¹` along the
transition of `ℙ¹`, which is why it is named after it, and that is the whole justification for
the name. In particular:

* it is **not** shown compact, which is the honest analytic statement and needs an argument about
  the topology of the gluing that nothing in this repository supplies;
* it is **not** shown to differ from the analytification of a single presentation — the real
  theorem, and one that needs an invariant nothing here computes. `OkaTest/AffineCover.lean` says
  the same about the node with a tripled origin;
* there is **no analytic structure** on it. That is `ComplexAnalytic.AnalyticSpace.ofGlueData`,
  whose compatibility hypothesis is a statement about the *glued* space and a separate step; this
  file stops at the locally ringed space.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The affine line, and the distinguished open `D(z)` -/

/-- The index type of the cover: two members. Three would be needed to give `hrange` and
`hcocycle` any content; two is what `ℙ¹` has. -/
abbrev pair : Type u := ULift.{u} (Fin 2)

/-- **The affine line**, presented in one variable with no relations. -/
abbrev lineRel : Fin 0 → MvPolynomial (ULift.{u} (Fin 1)) ℂ := Fin.elim0

/-- The coordinate `z` on the affine line, as a polynomial. -/
abbrev lineZ : MvPolynomial (ULift.{u} (Fin 1)) ℂ := MvPolynomial.X (ULift.up 0)

/-- Every member of the cover is the affine line. -/
abbrev lineCoverObj : pair.{u} → Presentation.{u} := fun _ ↦ ⟨1, 0, lineRel.{u}⟩

/-- Every overlap is cut out by `z`, so every one of them is `𝔸¹ ∖ {0}`. -/
abbrev lineCoverPoly :
    ∀ i : pair.{u}, pair.{u} → MvPolynomial (ULift.{u} (Fin (lineCoverObj.{u} i).n)) ℂ :=
  fun _ _ ↦ lineZ.{u}

/-- The origin of the affine line: the point at which `z` vanishes. -/
def lineOrigin : AnalyticSpace.analytification.{u} lineRel.{u} :=
  ⟨⟨(0 : ULift.{u} (Fin 1) → ℂ), trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} lineRel.{u} _).2 (fun j ↦ j.elim0)⟩

/-- The point `z = 1` of the affine line. -/
def lineOne : AnalyticSpace.analytification.{u} lineRel.{u} :=
  ⟨⟨(1 : ULift.{u} (Fin 1) → ℂ), trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} lineRel.{u} _).2 (fun j ↦ j.elim0)⟩

/-- **The origin is off `D(z)`**, which is what every non-degeneracy statement below rests on:
the origin is a point of one member glued to nothing in the other. -/
theorem lineOrigin_notMem_localisationOpen :
    lineOrigin.{u} ∉ localisationOpen.{u} lineRel.{u} lineZ.{u} := fun h ↦
  (mem_localisationOpen_iff.{u} lineRel.{u} lineZ.{u}).1 h (MvPolynomial.eval_X _)

/-- **`D(z)` is a proper open subset**, so this is not two copies of `𝔸¹` glued along everything —
which would return one copy. -/
theorem localisationOpen_lineRel_ne_top :
    localisationOpen.{u} lineRel.{u} lineZ.{u} ≠ ⊤ := fun hcon ↦
  lineOrigin_notMem_localisationOpen.{u} (hcon ▸ trivial)

/-- **`D(z)` is not empty either**, so this is not two copies glued along nothing. -/
theorem localisationOpen_lineRel_ne_bot : localisationOpen.{u} lineRel.{u} lineZ.{u} ≠ ⊥ := by
  intro hcon
  have hmem : lineOne.{u} ∈ localisationOpen.{u} lineRel.{u} lineZ.{u} :=
    (mem_localisationOpen_iff.{u} lineRel.{u} lineZ.{u}).2 (by
      rw [MvPolynomial.eval_X]
      exact one_ne_zero)
  rw [hcon] at hmem
  exact hmem

/-! ### The transition `z ↦ 1/z` -/

/-- **The presentation of the overlap**, `ℂ[z, t] ⧸ (t z - 1)`. Both members present the overlap
by the same presentation, on the nose — the `example` below — which is what lets the transition be
an *automorphism* rather than an isomorphism between two different objects. -/
abbrev linePres : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  localisationPresentation.{u} lineRel.{u} lineZ.{u}

example (i j : pair.{u}) :
    coverOverlap.{u} lineCoverObj.{u} lineCoverPoly.{u} i j = ⟨2, 1, linePres.{u}⟩ := rfl

/-- **The one relation of the overlap is `t z - 1`**, with `t` the new variable
`ComplexAnalytic.localisationVar` and `z` the old one carried across
`ComplexAnalytic.localisationIncl`. Stated because everything below is a computation with this
polynomial and nothing else about the presentation is used. -/
theorem linePres_zero :
    linePres.{u} 0 = MvPolynomial.X (ULift.up 1) * MvPolynomial.X (ULift.up 0) - 1 := by
  change localisationPresentation.{u} _ _ (Fin.last 0) = _
  rw [localisationPresentation_last]
  simp [localisationVar, localisationIncl]

/-- **The change of coordinates `z ↦ 1/z`**, as a permutation of the two variables of the
overlap: it exchanges `z` with the variable inverse to it. -/
def lineSwap : ULift.{u} (Fin 2) → ULift.{u} (Fin 2) :=
  fun i ↦ ULift.up (Equiv.swap 0 1 i.down)

@[simp]
theorem lineSwap_up_zero : lineSwap.{u} (ULift.up 0) = ULift.up 1 := by
  simp [lineSwap]

@[simp]
theorem lineSwap_up_one : lineSwap.{u} (ULift.up 1) = ULift.up 0 := by
  simp [lineSwap]

/-- **It is an involution**, which is the whole of the `hsymm` hypothesis below. -/
theorem lineSwap_comp_lineSwap : lineSwap.{u} ∘ lineSwap.{u} = id := by
  funext i
  simp [lineSwap, Function.comp]

/-- **The swap fixes the relation of the overlap**, by `mul_comm` and nothing else: renaming
`t z - 1` sends it to `z t - 1`, the same polynomial. This is the one algebraic fact `ℙ¹` needs,
and it is why the transition costs no commutative algebra. -/
theorem rename_lineSwap_linePres (j : Fin 1) :
    MvPolynomial.rename lineSwap.{u} (linePres.{u} j) ∈ presentationIdeal.{u} linePres.{u} := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  have h : MvPolynomial.rename lineSwap.{u} (linePres.{u} 0) = linePres.{u} 0 := by
    rw [linePres_zero]
    simp only [map_sub, map_mul, map_one, MvPolynomial.rename_X, lineSwap_up_zero,
      lineSwap_up_one]
    rw [mul_comm]
  rw [h]
  exact Ideal.subset_span ⟨0, rfl⟩

/-- **The transition of `ℙ¹`**, the automorphism of `ℂ[z, t] ⧸ (t z - 1)` exchanging the two
variables — the input `ComplexAnalytic.coverGlueData` calls `glue`, and the only value this
repository gives that input other than `Iso.refl`.

Both renamings are `ComplexAnalytic.lineSwap` and both hypotheses are the same, because the swap
is its own inverse. -/
def lineSwapIso (i j : pair.{u}) :
    coverOverlap.{u} lineCoverObj.{u} lineCoverPoly.{u} i j ≅
      coverOverlap.{u} lineCoverObj.{u} lineCoverPoly.{u} j i :=
  Presentation.isoOfRename.{u} lineSwap.{u} lineSwap.{u} rename_lineSwap_linePres.{u}
    rename_lineSwap_linePres.{u} lineSwap_comp_lineSwap.{u} lineSwap_comp_lineSwap.{u}

/-- The symmetry hypothesis, which is `rfl` here: an involution's `hom` and `inv` are the same
term, so `Iso.symm` permutes nothing but two proofs of a proposition. -/
theorem hsymm_lineCover (i j : pair.{u}) :
    lineSwapIso.{u} j i = (lineSwapIso.{u} i j).symm :=
  rfl

/-! ### The transition is not the identity

This is what `OkaTest/AffineCover.lean` cannot say about its own transition and the reason this
file exists. It is a statement about the *algebra*: `z` and `1/z` are different elements of
`ℂ[z, t] ⧸ (t z - 1)`, and they are separated by a single point of that algebra's spectrum. -/

/-- The point `(z, t) = (2, 2⁻¹)`, which is a zero of `t z - 1` at which the two variables take
different values. -/
abbrev lineSep : ULift.{u} (Fin 2) → ℂ := fun i ↦ if i = ULift.up 0 then 2 else 2⁻¹

theorem eval_lineSep_linePres (j : Fin 1) :
    MvPolynomial.eval lineSep.{u} (linePres.{u} j) = 0 := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rw [linePres_zero]
  norm_num [lineSep]

/-- **`z` and `1/z` are different elements of `ℂ[z, t] ⧸ (t z - 1)`.** Evaluation at
`ComplexAnalytic.lineSep` kills the relation, so it factors through the quotient, and it takes
the two variables to `2` and `2⁻¹`. -/
theorem mk_X_one_ne_mk_X_zero :
    Ideal.Quotient.mk (presentationIdeal.{u} linePres.{u}) (MvPolynomial.X (ULift.up 1)) ≠
      Ideal.Quotient.mk (presentationIdeal.{u} linePres.{u}) (MvPolynomial.X (ULift.up 0)) := by
  intro hcon
  have hmem : MvPolynomial.X (ULift.up 1) - MvPolynomial.X (ULift.up 0) ∈
      presentationIdeal.{u} linePres.{u} := by
    rwa [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  have hle : presentationIdeal.{u} linePres.{u} ≤
      RingHom.ker (MvPolynomial.eval lineSep.{u}) := by
    rw [presentationIdeal, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simpa [RingHom.mem_ker] using eval_lineSep_linePres.{u} j
  have hker := hle hmem
  rw [RingHom.mem_ker, map_sub] at hker
  norm_num [lineSep] at hker

theorem lineSwapIso_hom_toRingHom_mk_X (i j : pair.{u}) (l : ULift.{u} (Fin 2)) :
    (lineSwapIso.{u} i j).hom.toRingHom
        (Ideal.Quotient.mk (presentationIdeal.{u} linePres.{u}) (MvPolynomial.X l)) =
      Ideal.Quotient.mk (presentationIdeal.{u} linePres.{u})
        (MvPolynomial.X (lineSwap.{u} l)) := by
  simp [lineSwapIso, Presentation.isoOfRename]

/-- **The transition is not the identity.**

Without this the gluing would be indistinguishable in kind from `OkaTest/AffineCover.lean`'s,
whose transition is `Iso.refl` by construction, and `ComplexAnalytic.coverGlueData`'s only input
with content in it would still never have been exercised. -/
theorem lineSwapIso_ne_refl (i j : pair.{u}) : lineSwapIso.{u} i j ≠ Iso.refl _ := by
  intro hcon
  refine mk_X_one_ne_mk_X_zero.{u} ?_
  have h := congrArg (fun e : coverOverlap.{u} lineCoverObj.{u} lineCoverPoly.{u} i j ≅
      coverOverlap.{u} lineCoverObj.{u} lineCoverPoly.{u} j i ↦
    e.hom.toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} linePres.{u})
      (MvPolynomial.X (ULift.up 0)))) hcon
  rwa [lineSwapIso_hom_toRingHom_mk_X, lineSwap_up_zero] at h

/-! ### The two remaining hypotheses are vacuous -/

/-- **A two-element index type has no triple of pairwise distinct indices**, which is why `ℙ¹`
needs neither a range condition nor a cocycle: `CategoryTheory.GlueData'` asks for both only at
such a triple. -/
theorem pair_no_distinct_triple {i j k : pair.{u}} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  simp only [ne_eq, ULift.up.injEq] at hij hik hjk
  revert hij hik hjk
  revert i j k
  decide

theorem hrange_lineCover (i j k : pair.{u}) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Set.range (coverTripleIncl.{u} lineCoverObj.{u} lineCoverPoly.{u} i j k ≫
        coverTransitionHom.{u} lineCoverObj.{u} lineCoverPoly.{u} lineSwapIso.{u} i j).base ⊆
      ((coverOpen.{u} lineCoverObj.{u} lineCoverPoly.{u} j k ⊓
          coverOpen.{u} lineCoverObj.{u} lineCoverPoly.{u} j i :
        Opens (coverSpace.{u} lineCoverObj.{u} j)) :
          Set (coverSpace.{u} lineCoverObj.{u} j)) :=
  (pair_no_distinct_triple.{u} hij hik hjk).elim

theorem hcocycle_lineCover (i j k : pair.{u}) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    coverTriple.{u} lineCoverObj.{u} lineCoverPoly.{u} lineSwapIso.{u} hrange_lineCover.{u}
        i j k hij hik hjk ≫
      coverTriple.{u} lineCoverObj.{u} lineCoverPoly.{u} lineSwapIso.{u} hrange_lineCover.{u}
        j k i hjk hij.symm hik.symm ≫
      coverTriple.{u} lineCoverObj.{u} lineCoverPoly.{u} lineSwapIso.{u} hrange_lineCover.{u}
        k i j hik.symm hjk.symm hij = 𝟙 _ :=
  (pair_no_distinct_triple.{u} hij hik hjk).elim

/-! ### The gluing -/

/-- The `CategoryTheory.GlueData'` behind the gluing, named for the reason
`ComplexAnalytic.nodeTripleGlueData'` is: `CategoryTheory.GlueData'.f'` below cannot be stated
with a `_` for it, since the unifier then meets `?D.J =?= pair` — a projection applied to a
metavariable — and unfolds forever. -/
abbrev projectiveLineGlueData' : GlueData' LocallyRingedSpace.{u} :=
  coverGlueData'.{u} lineCoverObj.{u} lineCoverPoly.{u} lineSwapIso.{u} hrange_lineCover.{u}
    hsymm_lineCover.{u} hcocycle_lineCover.{u}

/-- **Two copies of the affine line, glued along `D(z)` by `z ↦ 1/z`.**

Read the module docstring before calling this `ℙ¹`: it is glued from the charts of `ℙ¹` along the
transition of `ℙ¹`, and nothing below proves it compact or proves it is not affine. -/
def projectiveLineGlueData : LocallyRingedSpace.GlueData.{u} :=
  coverGlueData.{u} lineCoverObj.{u} lineCoverPoly.{u} lineSwapIso.{u} hrange_lineCover.{u}
    hsymm_lineCover.{u} hcocycle_lineCover.{u}

/-- The members are the affine line, on the nose. -/
example (i : pair.{u}) :
    projectiveLineGlueData.{u}.U i =
      (AnalyticSpace.analytification.{u} lineRel.{u}).toLocallyRingedSpace :=
  rfl

/-- **The inclusion of an overlap into a member is `CategoryTheory.GlueData'.f'` off the
diagonal**, which is an `eqToHom` followed by the inclusion of the open subspace.

`eqToHom` appears because `CategoryTheory.GlueData'.f'` is *defined* with one, and the `dite` it
sits in is dependent — `rw [dif_neg]` reports *motive is not type correct*, so the branch has to
be taken with `split_ifs`. -/
theorem f_projectiveLineGlueData (i j : pair.{u}) (hij : i ≠ j) :
    projectiveLineGlueData.{u}.toGlueData.f i j =
      eqToHom (dif_neg hij) ≫ coverIncl.{u} lineCoverObj.{u} lineCoverPoly.{u} i j := by
  change CategoryTheory.GlueData'.f' projectiveLineGlueData'.{u} i j = _
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs with h
  · exact absurd h hij
  · rfl

/-- **The overlap of two distinct members lands in `D(z)`**, which is what the two statements
below need: a point off `D(z)` is glued to nothing. -/
theorem range_f_subset_projectiveLineGlueData (i j : pair.{u}) (hij : i ≠ j) :
    Set.range (projectiveLineGlueData.{u}.toGlueData.f i j).base ⊆
      (coverOpen.{u} lineCoverObj.{u} lineCoverPoly.{u} i j :
        Set (coverSpace.{u} lineCoverObj.{u} i)) := by
  rintro _ ⟨z, rfl⟩
  rw [f_projectiveLineGlueData i j hij]
  exact ((coverSpace.{u} lineCoverObj.{u} i).range_ofRestrict
    (coverOpen.{u} lineCoverObj.{u} lineCoverPoly.{u} i j)).le ⟨_, rfl⟩

/-- **The two copies of the origin are distinct in the gluing.** The origin lies off `D(z)`, so
by `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff` two members' points can agree in the
gluing only if they come from a point of the overlap, and the image of the overlap misses it.

This is the statement that `0` and `∞` are two points, and it is what stops
`ComplexAnalytic.coverGlueData` from being satisfied here by a construction that returns its
first member. -/
theorem ι_lineOrigin_ne (i j : pair.{u}) (hij : i ≠ j) :
    (projectiveLineGlueData.{u}.toGlueData.ι i).base lineOrigin.{u} ≠
      (projectiveLineGlueData.{u}.toGlueData.ι j).base lineOrigin.{u} := by
  rw [Ne, LocallyRingedSpace.GlueData.ι_eq_iff]
  rintro ⟨z, hz, -⟩
  exact lineOrigin_notMem_localisationOpen.{u}
    (range_f_subset_projectiveLineGlueData i j hij ⟨z, hz⟩)

/-- The other member's copy of the origin is not in the range of this member's inclusion — the
same computation as `ComplexAnalytic.ι_lineOrigin_ne`, with the point of the first member left
arbitrary. -/
theorem lineOrigin_notMem_range_ι (i j : pair.{u}) (hij : i ≠ j) :
    (projectiveLineGlueData.{u}.toGlueData.ι j).base lineOrigin.{u} ∉
      Set.range (projectiveLineGlueData.{u}.toGlueData.ι i).base := by
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, -⟩ :=
    (LocallyRingedSpace.GlueData.ι_eq_iff projectiveLineGlueData.{u} j i lineOrigin.{u} y).1
      hy.symm
  exact lineOrigin_notMem_localisationOpen.{u}
    (range_f_subset_projectiveLineGlueData j i hij.symm ⟨z, hz⟩)

/-- **Neither member is the whole space.**

With `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` and
`ComplexAnalytic.coverGlueData_ι_isOpenImmersion` — the two `example`s below — this says the
glued space is covered by two copies of the affine line and is neither of them. It is the
strongest thing proved about the space here; compactness and non-affineness are not. -/
theorem not_surjective_ι_projectiveLineGlueData (i : pair.{u}) :
    ¬ Function.Surjective (projectiveLineGlueData.{u}.toGlueData.ι i).base := by
  obtain ⟨j, hij⟩ : ∃ j : pair.{u}, i ≠ j := by
    obtain ⟨i⟩ := i
    refine ⟨ULift.up (Equiv.swap 0 1 i), ?_⟩
    simp only [ne_eq, ULift.up.injEq]
    revert i
    decide
  exact fun hsurj ↦ lineOrigin_notMem_range_ι.{u} i j hij (hsurj _)

/-- Each member is an open subspace of the gluing. -/
example (i : pair.{u}) :
    LocallyRingedSpace.IsOpenImmersion (projectiveLineGlueData.{u}.toGlueData.ι i) :=
  coverGlueData_ι_isOpenImmersion.{u} lineCoverObj.{u} lineCoverPoly.{u} lineSwapIso.{u}
    hrange_lineCover.{u} hsymm_lineCover.{u} hcocycle_lineCover.{u} i

/-- And together they cover it. -/
example (x : projectiveLineGlueData.{u}.toGlueData.glued) :
    ∃ (i : pair.{u}) (y : projectiveLineGlueData.{u}.U i),
      (projectiveLineGlueData.{u}.toGlueData.ι i).base y = x :=
  projectiveLineGlueData.{u}.ι_jointly_surjective x

end

end ComplexAnalytic

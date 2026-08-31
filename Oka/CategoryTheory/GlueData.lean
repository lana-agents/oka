/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.CategoryTheory.GlueData

/-!
# The fields of `CategoryTheory.GlueData.ofGlueData'`

Material for `Mathlib/CategoryTheory/GlueData.lean`; see `README.md` on the mirror tree.

`CategoryTheory.GlueData'` is the variant of a glue datum that asks for the overlaps only when
`i ≠ j`, and `CategoryTheory.GlueData.ofGlueData'` turns one into a `CategoryTheory.GlueData` by
filling the diagonal with `dite`s. **Mathlib has no projection lemmas for it at all** — `grep`
finds `ofGlueData'` only in its own defining file — so a caller that has to *use* `f` or `t` of
the result has to unfold a `dite` by hand.

This file supplies nine: two for `CategoryTheory.GlueData'.f'`, two for each of
`CategoryTheory.GlueData.ofGlueData'`'s `f` and `t`, the composite `t i j ≫ f j i`, and the two
directions of the compatibility condition a family of morphisms out of the members satisfies.

## Why they are not one `simp` call at the call site

The `dite`s of `CategoryTheory.GlueData'.f'` and of `CategoryTheory.GlueData.ofGlueData'`'s `t`
are **dependent**: the two branches have different types, since `V (i, i)` is `U i` and
`V (i, j)` is the given overlap. Consequently, at a goal where the `dite` is not at the head:

* `rw [dif_neg h]` reports *motive is not type correct*;
* `split_ifs` reports *tactic does nothing*;
* `simp` with `h : i ≠ j` in its argument list reports that argument **unused** and leaves the
  `dite` standing — the `Decidable` instance is `Classical.propDecidable`, from the
  `open scoped Classical` in Mathlib's own definition.

The technique that does work is to put the `dite` at the head — `change` to the `GlueData'.f'`
spelling, `dsimp only`, then `split_ifs` — and that is what these lemmas do once so that a caller
does not have to do it at every use.

## The composite `t i j ≫ f j i`, and the `dsimp only` that is not discoverable

`ComplexAnalytic.GlueDataCLinear` — and anything else comparing structures across an overlap —
asks about `t i j ≫ f j i`, where the two `eqToHom`s in the middle cancel.
`CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne` is that, and its proof is three lines: rewrite
with the two lemmas above, `dsimp only [GlueData.ofGlueData']`, `simp`.

**The middle line is the whole content, and deleting it leaves a goal that `simp`, `aesop_cat` and
`rw [Category.assoc]` all fail on** — the last reporting *did not find an occurrence of the pattern
`(?f ≫ ?g) ≫ ?h`* against a goal that visibly has that shape. Measured both ways: with the
`dsimp only` the proof closes in under two seconds, without it the goal is left unsolved.

The reason is **not** that the objects are `dite`s. After the two rewrites the *factors* carry the
`dite`s, while the composition's object positions still carry unreduced
`(GlueData.ofGlueData' D).V (i, j)` projections; `rw` matches at reducible transparency and
`GlueData.ofGlueData'` is a plain `def`, so the two spellings never meet. The blocker is an opaque
definition in an object position, which is why exactly one `dsimp only` removes it and why no set
of `simp` lemmas would have — and why `rw [Category.assoc]` *succeeds* on that same goal once the
`dsimp only` has run.

**That is why this is a lemma rather than three lines at the call site**: the middle line cannot be
guessed from the error message, which points at `Category.assoc` and says nothing about
transparency.

## The compatibility condition, and why its two directions are not one `iff`

Anything that maps *out* of a gluing — `AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms`
is this repository's instance — asks that a family `fY i : U i ⟶ Y` satisfy
`f i j ≫ fY i = t i j ≫ f j i ≫ fY j` at **every** pair, because that is the form the glue datum's
own `glue_condition` has. A caller can only supply it **off the diagonal**: `V (i, i)` is not a
chosen overlap and `t i i` is not a chosen transition, so there is nothing there to check and no
hypothesis to state about it.

`CategoryTheory.GlueData.ofGlueData'_comm` is that asymmetry — hypothesis at `i ≠ j`, conclusion at
every pair — and `CategoryTheory.GlueData.comm_of_ofGlueData'_comm` is the converse, which recovers
the caller's form from the glue datum's. **They are deliberately not packaged as an `iff`**: the
statements are not literally converse, since one quantifies over `i ≠ j` and the other over all
pairs, and each direction is used at a different place. The forward one turns a caller's
compatibility into `glueMorphisms`' hypothesis; the backward one reads a glue datum's own
`CategoryTheory.GlueData.glue_condition` back into the caller's vocabulary, which is what says the
inclusions `ι i` are themselves such a family and hence that gluing them returns the identity.

## Main results

- `CategoryTheory.GlueData'.f'_self` and `CategoryTheory.GlueData'.f'_of_ne`
- `CategoryTheory.GlueData.ofGlueData'_f_self` and
  `CategoryTheory.GlueData.ofGlueData'_f_of_ne`
- `CategoryTheory.GlueData.ofGlueData'_t_self` and
  `CategoryTheory.GlueData.ofGlueData'_t_of_ne`
- `CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne`
- `CategoryTheory.GlueData.ofGlueData'_comm` and
  `CategoryTheory.GlueData.comm_of_ofGlueData'_comm`
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (D : GlueData' C)

/-- **`CategoryTheory.GlueData'.f'` on the diagonal is the `eqToHom` identifying `V (i, i)` with
`U i`.** -/
theorem GlueData'.f'_self (i : D.J) : D.f' i i = eqToHom (dif_pos rfl) := by
  dsimp only [GlueData'.f']
  split_ifs with h
  · rfl
  · exact absurd rfl h

/-- **`CategoryTheory.GlueData'.f'` off the diagonal is the given inclusion after the `eqToHom`
identifying `V (i, j)` with the given overlap.**

Stated about `f'` rather than about `CategoryTheory.GlueData.ofGlueData'`'s `f` field — they are
the same term — because it is the `f'` spelling that a goal is left in after
`dsimp only [GlueData.ofGlueData']`, and that is the position
`CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne` needs it at. -/
theorem GlueData'.f'_of_ne {i j : D.J} (h : i ≠ j) :
    D.f' i j = eqToHom (dif_neg h) ≫ D.f i j h := by
  dsimp only [GlueData'.f']
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- **On the diagonal, `CategoryTheory.GlueData.ofGlueData'`'s inclusion is the `eqToHom` that
identifies `V (i, i)` with `U i`.** -/
theorem GlueData.ofGlueData'_f_self (i : D.J) :
    (GlueData.ofGlueData' D).f i i = eqToHom (dif_pos rfl) :=
  GlueData'.f'_self D i

/-- **Off the diagonal, it is the given inclusion after the `eqToHom` that identifies
`V (i, j)` with the given overlap.**

This is `ComplexAnalytic.f_nodeTripleGlueData` (`OkaTest/AffineCover.lean`) and
`ComplexAnalytic.f_projectiveLineGlueData` made general: both were the same three-line unfolding
at a concrete glue datum. -/
theorem GlueData.ofGlueData'_f_of_ne {i j : D.J} (h : i ≠ j) :
    (GlueData.ofGlueData' D).f i j = eqToHom (dif_neg h) ≫ D.f i j h :=
  GlueData'.f'_of_ne D h

open scoped Classical in
/-- **On the diagonal, `CategoryTheory.GlueData.ofGlueData'`'s transition is an `eqToHom`.**

`CategoryTheory.GlueData` requires `t i i` to be the identity up to the identification of
`V (i, i)` with `U i`, and `ofGlueData'` discharges that; this is the value it discharges it
with. -/
theorem GlueData.ofGlueData'_t_self (i : D.J) :
    (GlueData.ofGlueData' D).t i i = eqToHom (by simp) := by
  dsimp only [GlueData.ofGlueData']
  split_ifs with h
  · rfl
  · exact absurd rfl h

open scoped Classical in
/-- **Off the diagonal, it is the given transition conjugated by the two `eqToHom`s that identify
`V (i, j)` and `V (j, i)` with the given overlaps.** -/
theorem GlueData.ofGlueData'_t_of_ne {i j : D.J} (h : i ≠ j) :
    (GlueData.ofGlueData' D).t i j =
      eqToHom (dif_neg h) ≫ D.t i j h ≫ eqToHom (dif_neg (Ne.symm h)).symm := by
  dsimp only [GlueData.ofGlueData']
  split_ifs with h'
  · exact absurd h' h
  · rfl

open scoped Classical in
/-- **The composite `t i j ≫ f j i`, with the two `eqToHom`s in the middle cancelled.**

The shape a caller comparing structures across an overlap works with. The `dsimp only` between
the rewrites and the `simp` is the whole content: without it the goal defeats `simp`, `aesop_cat`
and `rw [Category.assoc]`, because the composition's object positions carry unreduced
`GlueData.ofGlueData'` projections that `rw` will not unfold at reducible transparency. See the
module docstring; that line is not discoverable from the error, which is why this is a lemma. -/
theorem GlueData.ofGlueData'_t_comp_f_of_ne {i j : D.J} (h : i ≠ j) :
    (GlueData.ofGlueData' D).t i j ≫ (GlueData.ofGlueData' D).f j i =
      eqToHom (dif_neg h) ≫ D.t i j h ≫ D.f j i (Ne.symm h) := by
  rw [GlueData.ofGlueData'_t_of_ne D h, GlueData.ofGlueData'_f_of_ne D (Ne.symm h)]
  dsimp only [GlueData.ofGlueData']
  simp

open scoped Classical in
/-- **Morphisms out of the members which agree over the given overlaps agree over
`CategoryTheory.GlueData.ofGlueData'`'s.**

The hypothesis is at `i ≠ j` and the conclusion at every pair, and that asymmetry is the point: a
caller has nothing to say about the diagonal, where `V (i, i)` is not a chosen overlap and `t i i`
is not a chosen transition, while `CategoryTheory.GlueData.glue_condition` and everything that
consumes it quantify over all pairs. The diagonal is discharged by
`CategoryTheory.GlueData.ofGlueData'_f_self` and `…ofGlueData'_t_self`, both of which are
`eqToHom`s.

The `dsimp only [GlueData.ofGlueData']` between the rewrites is load-bearing for the reason the
module docstring gives, and this proof is where it bites again: without it `rw [Category.assoc]`
reports *did not find an occurrence of the pattern `(?f ≫ ?g) ≫ ?h`* against a goal of visibly
that shape. -/
theorem GlueData.ofGlueData'_comm {Y : C} (fY : ∀ i, D.U i ⟶ Y)
    (h : ∀ i j, ∀ hij : i ≠ j, D.f i j hij ≫ fY i = D.t i j hij ≫ D.f j i hij.symm ≫ fY j)
    (i j : D.J) :
    (GlueData.ofGlueData' D).f i j ≫ fY i =
      (GlueData.ofGlueData' D).t i j ≫ (GlueData.ofGlueData' D).f j i ≫ fY j := by
  rcases eq_or_ne i j with rfl | hij
  · rw [GlueData.ofGlueData'_f_self, GlueData.ofGlueData'_t_self]
    simp
  · rw [← Category.assoc, GlueData.ofGlueData'_t_comp_f_of_ne D hij,
      GlueData.ofGlueData'_f_of_ne D hij]
    dsimp only [GlueData.ofGlueData']
    rw [Category.assoc, Category.assoc, cancel_epi, Category.assoc]
    exact h i j hij

open scoped Classical in
/-- **The converse**: a family which agrees over `CategoryTheory.GlueData.ofGlueData'`'s overlaps
agrees over the given ones.

The same three rewrites, applied to the hypothesis rather than to the goal. What it is for is
reading a glue datum's own `CategoryTheory.GlueData.glue_condition` — which is stated at
`ofGlueData'`'s `f` and `t` — back into the vocabulary a caller built the datum in, and hence
saying that the inclusions of the members are one of these families. -/
theorem GlueData.comm_of_ofGlueData'_comm {Y : C} (fY : ∀ i, D.U i ⟶ Y)
    (h : ∀ i j, (GlueData.ofGlueData' D).f i j ≫ fY i =
      (GlueData.ofGlueData' D).t i j ≫ (GlueData.ofGlueData' D).f j i ≫ fY j)
    {i j : D.J} (hij : i ≠ j) :
    D.f i j hij ≫ fY i = D.t i j hij ≫ D.f j i hij.symm ≫ fY j := by
  have hij' := h i j
  rw [← Category.assoc, GlueData.ofGlueData'_t_comp_f_of_ne D hij,
    GlueData.ofGlueData'_f_of_ne D hij] at hij'
  dsimp only [GlueData.ofGlueData'] at hij'
  rw [Category.assoc, Category.assoc, cancel_epi, Category.assoc] at hij'
  exact hij'

end CategoryTheory

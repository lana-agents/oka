/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# A distinguished-open refinement whose overlaps are proper and non-empty

`Oka/Analytification/CoverRefinement.lean` builds the refined cover datum for a same-member
distinguished-open refinement: the refined members `D(f_a)` of one fixed member, the polynomial
cutting each overlap out, the glue isomorphism, its symmetry law and the coherence triangle. Every
one of those statements is **hypothesis-free in `K` and in `fam`**, so none of them can be
vacuously satisfied — but that says nothing about whether the *objects* are degenerate, and they
can be. `K` may be empty; and for `fam` constantly `0` every `D(f_a)` is empty, every overlap is
empty, and every law there holds of nothing.

**This file is the witness that they need not be.** The base is empty over one variable, so the
fixed member is the whole of `ℂ¹`, and the refining family is `(z₀, z₀ - 1)`: the two refined
members are the punctured lines `ℂ ∖ {0}` and `ℂ ∖ {1}`.

## What is checked, and why both halves are needed

A witness that is merely non-empty is satisfied by data that trivialises the construction — take
`fam` constant and every overlap becomes the whole refined member, at which point the glue
isomorphism is an identity and says nothing.

* `OkaTest.CoverRefinement.coverOpen_refine_ne_bot` — **every** refined overlap is non-empty, at
  every pair of indices. The point `z₀ = 2` is in both `D(z₀)` and `D(z₀ - 1)`, and it lifts to
  the refined member because `ComplexAnalytic.range_base_localisationProj` says the projection's
  range *is* the distinguished open.
* `OkaTest.CoverRefinement.coverOpen_refine_ne_top` — the `(0, 1)` overlap is **not** the whole of
  the refined member, so `ComplexAnalytic.refineGlue` at this data glues along something smaller
  than the member it sits in. The point `z₀ = 1` is in `D(z₀)` and not in `D(z₀ - 1)`.
* `OkaTest.CoverRefinement.nonempty_coverOverlapSpace_refine` — the space that
  `ComplexAnalytic.refineGlue` is an isomorphism *of* is non-empty, obtained by transporting the
  point along `ComplexAnalytic.coverOverlapIso`. This is the statement that makes the glue
  isomorphism one of non-empty spaces rather than one of empty ones, and it is the only place
  here where an isomorphism of the library file's is applied rather than described.

`ComplexAnalytic.localisationOpen_rename` is what carries all three: the refined overlap is by
that lemma the *preimage* of `D(f_b)` along the projection, so membership upstairs is a question
about the image point downstairs and no point of a double localisation ever has to be written
down.

## What is not checked here

* **No `hrange` and no `hcocycle`**, and no claim that either is true at this data. Those are the
  two laws `Oka/Analytification/CoverRefinement.lean` does not have; a witness that the objects
  are non-degenerate is not evidence about them.
* **Nothing about the cross-member case.** `σ` is constant in the library file and constant here.
* **No claim that this is the smallest witness**, or that one exists for every `K` and `fam`. It
  does not: `fam = 0` makes every overlap empty, which is exactly the degeneracy this file is
  filed against, and the library statements are hypothesis-free precisely because they are true
  of that case too.
-/

open MvPolynomial CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace OkaTest.CoverRefinement

open ComplexAnalytic

noncomputable section

/-! ### The data -/

/-- **The empty base in one variable**: no relations, so the fixed member of the refinement is the
whole of `ℂ¹` and nothing about it can make an overlap empty. -/
abbrev lineBase : Fin 0 → MvPolynomial (ULift.{u} (Fin 1)) ℂ := fun j ↦ j.elim0

/-- **The refining family** `(z₀, z₀ - 1)`, indexed by `ULift (Fin 2)` because the index type of a
refinement lives in the same universe as the coordinates. The two refined members are `ℂ ∖ {0}`
and `ℂ ∖ {1}`, which meet in `ℂ ∖ {0, 1}` — non-empty, and a proper subset of each. -/
def lineFam : ULift.{u} (Fin 2) → MvPolynomial (ULift.{u} (Fin 1)) ℂ := fun a ↦
  ![MvPolynomial.X (ULift.up 0), MvPolynomial.X (ULift.up 0) - 1] a.down

/-- **The point `z₀ = c` of the fixed member.** The base is empty, so there is nothing to check
beyond the ambient membership. -/
def linePoint (c : ℂ) : AnalyticSpace.analytification.{u} lineBase.{u} :=
  ⟨⟨fun _ ↦ c, trivial⟩, (mem_zeroLocus_polySection_iff.{u} _ _).2 fun j ↦ j.elim0⟩

/-- The two refining polynomials at that point, in one statement so that the two membership
arguments below are the same argument twice. -/
theorem eval_linePoint (c : ℂ) (a : ULift.{u} (Fin 2)) :
    MvPolynomial.eval ((linePoint.{u} c).1.1 : ULift.{u} (Fin 1) → ℂ) (lineFam.{u} a) =
      ![c, c - 1] a.down := by
  fin_cases a <;> simp [lineFam, linePoint]

/-- **`z₀ = c` lies in `D(f_a)`** exactly when the `a`-th polynomial does not vanish there. -/
theorem linePoint_mem (c : ℂ) (a : ULift.{u} (Fin 2)) (h : ![c, c - 1] a.down ≠ 0) :
    linePoint.{u} c ∈ localisationOpen.{u} lineBase.{u} (lineFam.{u} a) :=
  (mem_localisationOpen_iff.{u} _ _).2 (by rw [eval_linePoint]; exact h)

/-- **A point of the `a`-th refined member over `z₀ = c`.**

This is where `ComplexAnalytic.range_base_localisationProj` does the work: the range of the
projection `D(f_a) ← (A_{f_a})^an` **is** the distinguished open, so a point of the open is the
image of a point upstairs and no coordinate of the localisation has to be exhibited. -/
theorem exists_over (c : ℂ) (a : ULift.{u} (Fin 2)) (h : ![c, c - 1] a.down ≠ 0) :
    ∃ y : AnalyticSpace.analytification.{u}
        (localisationPresentation.{u} lineBase.{u} (lineFam.{u} a)),
      (localisationProj.{u} lineBase.{u} (lineFam.{u} a)).toLRSHom.base y = linePoint.{u} c := by
  have hmem : linePoint.{u} c ∈ Set.range
      (localisationProj.{u} lineBase.{u} (lineFam.{u} a)).toLRSHom.base := by
    rw [range_base_localisationProj.{u}]
    exact linePoint_mem.{u} c a h
  exact hmem

/-! ### Every refined overlap is inhabited -/

/-- **A point of the `(a, b)` refined overlap**, for every pair of indices: the point `z₀ = 2` is
in `D(z₀)` and in `D(z₀ - 1)` both, and `ComplexAnalytic.localisationOpen_rename` turns membership
in the overlap upstairs into membership of the image point downstairs. -/
theorem exists_mem_coverOpen_refine (a b : ULift.{u} (Fin 2)) :
    ∃ y, y ∈ coverOpen.{u} (refineObj.{u} lineBase.{u} lineFam.{u})
      (refinePoly.{u} lineBase.{u} lineFam.{u}) a b := by
  obtain ⟨y, hy⟩ := exists_over.{u} 2 a (by fin_cases a <;> norm_num)
  refine ⟨y, ?_⟩
  change y ∈ localisationOpen.{u} (localisationPresentation.{u} lineBase.{u} (lineFam.{u} a))
    (MvPolynomial.rename (localisationIncl.{u} 1) (lineFam.{u} b))
  rw [localisationOpen_rename.{u} lineBase.{u} (lineFam.{u} a) (lineFam.{u} b)]
  have hb := linePoint_mem.{u} (2 : ℂ) b (by fin_cases b <;> norm_num)
  rw [← hy] at hb
  exact hb

/-- **No refined overlap is empty.** This is what stops every statement of
`Oka/Analytification/CoverRefinement.lean` from being a statement about empty spaces. -/
theorem coverOpen_refine_ne_bot (a b : ULift.{u} (Fin 2)) :
    coverOpen.{u} (refineObj.{u} lineBase.{u} lineFam.{u})
      (refinePoly.{u} lineBase.{u} lineFam.{u}) a b ≠ ⊥ := by
  obtain ⟨y, hy⟩ := exists_mem_coverOpen_refine.{u} a b
  intro hcon
  rw [hcon] at hy
  exact hy

/-- **The space that `ComplexAnalytic.refineGlue` is an isomorphism of is non-empty.**

`ComplexAnalytic.coverOverlapIso` identifies the analytification of the overlap presentation — a
*double* localisation, whose points nothing here writes down — with the open subspace of the
refined member, and the point above is transported backwards along it. -/
theorem nonempty_coverOverlapSpace_refine (a b : ULift.{u} (Fin 2)) :
    Nonempty (coverOverlapSpace.{u} (refineObj.{u} lineBase.{u} lineFam.{u})
      (refinePoly.{u} lineBase.{u} lineFam.{u}) a b) := by
  obtain ⟨y, hy⟩ := exists_mem_coverOpen_refine.{u} a b
  exact ⟨(LocallyRingedSpace.homeoOfIso (coverOverlapIso.{u}
    (refineObj.{u} lineBase.{u} lineFam.{u})
    (refinePoly.{u} lineBase.{u} lineFam.{u}) a b)).symm ⟨y, hy⟩⟩

/-! ### The `(0, 1)` overlap is a proper open of the refined member -/

/-- **The `(0, 1)` overlap is not the whole of the first refined member**, so the glue is along
something smaller than the member and the refinement is not the identity in disguise. The point
`z₀ = 1` is in `D(z₀)` and is where `z₀ - 1` vanishes. -/
theorem coverOpen_refine_ne_top :
    coverOpen.{u} (refineObj.{u} lineBase.{u} lineFam.{u})
      (refinePoly.{u} lineBase.{u} lineFam.{u}) (ULift.up 0) (ULift.up 1) ≠ ⊤ := by
  obtain ⟨y, hy⟩ := exists_over.{u} 1 (ULift.up 0) (by norm_num)
  intro hcon
  have htop : y ∈ coverOpen.{u} (refineObj.{u} lineBase.{u} lineFam.{u})
      (refinePoly.{u} lineBase.{u} lineFam.{u}) (ULift.up 0) (ULift.up 1) := by
    rw [hcon]; trivial
  have hmem : y ∈ localisationOpen.{u} (localisationPresentation.{u} lineBase.{u}
      (lineFam.{u} (ULift.up 0)))
      (MvPolynomial.rename (localisationIncl.{u} 1) (lineFam.{u} (ULift.up 1))) := htop
  rw [localisationOpen_rename.{u}] at hmem
  have hmem' : (localisationProj.{u} lineBase.{u} (lineFam.{u} (ULift.up 0))).toLRSHom.base y ∈
      localisationOpen.{u} lineBase.{u} (lineFam.{u} (ULift.up 1)) := hmem
  rw [hy] at hmem'
  exact (mem_localisationOpen_iff.{u} _ _).1 hmem' (by rw [eval_linePoint]; norm_num)

end

end OkaTest.CoverRefinement

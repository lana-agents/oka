/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.StandardEtaleCond

/-!
# The unrestricted standard étale analytification is not finite, at the square-root cover

`Oka/Analytification/StandardEtaleFiniteness.lean` proves
`ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp`: the analytification
of a standard étale morphism over `ℂ^n`, **restricted over an open `V` disjoint from
`ComplexAnalytic.hypersurfaceCommonZeroImage`**, is finite over `V`. Its docstring says the
hypothesis is not decoration and names the pair that shows it:

> At `F = X² - x` and `G = X` the bad set is the origin of the line, so `V = ⊤` meets it, and
> inverting `G` cuts the point `(0, 0)` out of the parabola; the projection of what is left has
> the punctured line for image, which is not closed, so the morphism is not finite.
> `Oka/Analytification/MonicHypersurface.lean` carries that computation in terms. **It is not
> compiled anywhere in this repository** and is asserted here on the same footing it is asserted
> there.

This file compiles it.

**The claim was in seven module docstrings under `Oka/` at `d58421e` and proved in none of them.**
Named rather than counted from here on, because a count of prose sites is what goes stale first:
`Oka/Analytification/MonicHypersurface.lean`, which is where the argument lives;
`Oka/Analytification/StandardEtaleAnalytification.lean`;
`Oka/Analytification/StandardEtaleFiniteness.lean`;
`Oka/Analytification/StandardEtaleFiniteEtale.lean`;
`Oka/Analytification/OpenBaseFiniteness.lean`;
`Oka/Analytification/StandardEtaleLocalIso.lean`; and
`Oka/Analytification/StandardEtaleLocalIsoBase.lean`, whose version is at `k ≥ 1` and so is a
different statement citing the same counterexample. **The numeral is pinned and this file is not
in it** — a claim of this shape written into the tree it counts becomes a member of what it
counts, which is the trap `Oka/Analytification/MonicHypersurface.lean` records for a printed
`grep`. **It is pinned here and nowhere else, and an earlier draft of this file did not manage
that**: the count escaped into three declaration docstrings below as *three*, a numeral no
sweep supports and which this paragraph refutes. They now point back at the list above and carry
no count of their own, which is what *named rather than counted* has to mean if it is to survive
the next edit.

**And the sweep that found the seventh had to normalise whitespace, and had to reach outside
`Oka/`.** `Oka/Analytification/StandardEtaleLocalIsoBase.lean` wraps as *"Unrestricted finiteness
at `k ≥ 1` is"* / *"false"*, so a line-anchored grep for the two words returns **six** of the
seven. And three files under `OkaTest/` carry the same citation —
`OkaTest/Axioms/Analytification.lean`, `OkaTest/StandardEtaleAnalytification.lean` and
`OkaTest/StandardEtaleCond.lean` — which no sweep of `Oka/` can see, since nothing under `Oka/`
imports `OkaTest/`. **All three say `Oka/Analytification/MonicHypersurface.lean` carries the
witness, which is still true**, so none of them is repaired here; they are listed so that the next
census does not have to find them again.

## The pair is quoted and not built

`ComplexAnalytic.condPair` (`OkaTest/StandardEtaleCond.lean`) is already `f = X² - C z₀`,
`g = X` over `ComplexAnalytic.PresentedAlgebra 1 0 ComplexAnalytic.condBase` — the empty
presentation of the line — with `ComplexAnalytic.condF_eq` and `ComplexAnalytic.condG_eq` the two
lift computations. That is exactly the pair the sentence above names, so nothing here rebuilds it
and this file adds no `StandardEtalePair`. What it adds is a point, a coordinate computation, and
the two theorems.

## The argument is not the one the prose gives, and the difference is the whole economy

The sentence quoted above argues from the **image**: it is the punctured line, which is not
closed, so the base map is not closed and
`ComplexAnalytic.AnalyticSpace.IsFinite`'s first field fails. Carrying that out means computing
the image exactly, which needs a square root of every non-zero complex number.

**This file argues from one missing point instead.** The composite is a local isomorphism —
`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`, at `ComplexAnalytic.condPair` —
so its image is **open**; if it were also finite its image would be **closed**; the line is
connected, so the image would be `∅` or everything; the source is not empty, and the image misses
the origin. That is
`ComplexAnalytic.AnalyticSpace.not_isFinite_of_isLocalIso_of_not_surjective`
(`Oka/AnalyticSpace/LocalIso.lean`), and it turns a statement about a *set* into a statement about
a *point*. **Nothing below computes the image**, and in particular nothing below says it is the
punctured line; see `## What is not checked here`.

**That general lemma is not invented for this file — it is the argument
`Oka/Analytification/MonicHypersurface.lean` already runs in prose**, twice: *"an open set closed
in the connected `ℂ^n` is `∅` or `⊤`"* in its `## What is not here`, and
`Oka/Analytification/StandardEtaleLocalIso.lean`'s *"a local isomorphism has open image"* in its
own. Both were readings of two classes and neither was a declaration; the lemma is those two
sentences with the connectedness hypothesis written down.

## The two tuples, and why the missing point is the origin

Coordinates of `ComplexAnalytic.etalePresentation ComplexAnalytic.condBase ComplexAnalytic.condF
ComplexAnalytic.condG` are `(z₀, z₁, z₂)` in `ℂ³`: the base variable, the root adjoined by
`ComplexAnalytic.polyPresentation`, and the inverse adjoined by
`ComplexAnalytic.localisationPresentation`. The two relations are `z₂·z₁ - 1` and `z₁² - z₀`.

* **The source is not empty**: `ComplexAnalytic.condEtalePt` is the constant tuple `(1, 1, 1)`,
  where both relations are `1 - 1`.
* **The origin is missed**: at any point of the source `z₁² = z₀`, so `z₀ = 0` forces `z₁ = 0`,
  and then `z₂·z₁ - 1` is `-1` and not `0`. The relations are inconsistent over the origin, which
  is the branch point the standard étale algebra inverts away.

**`ComplexAnalytic.base_analytificationMap_etalePresHom_comp_apply` is what makes the second of
those a statement about the morphism** rather than about a tuple: it says the projection to the
base is the first `n` coordinates. Without it a point of the source and a point of the base are
unrelated, since a morphism out of `ComplexAnalytic.analytificationMap` is opaque on points.

## Main definitions

- `ComplexAnalytic.condEtaleProj`: **the morphism**, the analytification of
  `ComplexAnalytic.condPair`'s structure map followed by the base's inclusion into `ℂ¹` — the
  unrestricted composite the module docstrings named at the top of this file are about.
- `ComplexAnalytic.condEtalePt`: the tuple `(1, 1, 1)` of `ℂ³`, a point of its source.

## Main results

- `ComplexAnalytic.not_isFinite_condEtaleProj` and
  `ComplexAnalytic.not_isFiniteEtale_condEtaleProj`: **the unrestricted morphism is not finite,
  and so not finite étale** — the claim the module docstrings named at the top of this file make
  and none of them compiles.
- `ComplexAnalytic.nonempty_analytification_etalePresentation_cond`: **the source is not empty**,
  without which the result above would hold of an empty space and say nothing.
- `ComplexAnalytic.base_condEtaleProj_ne_zero`: **the origin of the line is not in the image**,
  which is the whole of what the two theorems above read.
- `ComplexAnalytic.eval_etalePresentation_cond_zero` and
  `ComplexAnalytic.eval_etalePresentation_cond_one`: the two relations of the étale presentation,
  written out at a tuple.

## What is not checked here

* **The image is not computed.** The prose this file discharges says it is the punctured line;
  nothing below says so, and nothing below says the image is anything other than a set missing
  the origin. Proving it *is* the punctured line needs a square root of every non-zero complex
  number and is a strictly stronger statement; it would also make
  `ComplexAnalytic.AnalyticSpace.not_isFinite_of_isLocalIso_of_not_surjective` unnecessary here,
  which is the trade this file declines.
* **No statement says the `V` hypothesis of the restricted theorem is irredundant.**
  `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp` is about
  `ComplexAnalytic.AnalyticSpace.restrictHom` of this composite, and nothing in this repository
  relates that at `V = ⊤` to the composite itself, so the two are different morphisms and the
  implication is prose. **What is compiled is the counterexample the prose points at**, which is
  what those docstrings say is missing; the last step from it to *"the hypothesis cannot be
  dropped"* is not taken.
* **Nothing at `k ≥ 1`.** `ComplexAnalytic.condBase` is the empty presentation, so this is the
  `k = 0` case, which is what
  `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` is stated at. The `k ≥ 1`
  projection statement is a different one and `Oka/Analytification/StandardEtaleLocalIso.lean`
  argues *it* false for a different reason — an open image inside a proper closed subset of
  `ℂ^n` — which is untouched here.
* **Two of the seven sites named above are left as they stand**, and they are not falsified by
  this file: `Oka/Analytification/StandardEtaleLocalIso.lean` and
  `Oka/Analytification/StandardEtaleLocalIsoBase.lean` both say that
  `Oka/Analytification/MonicHypersurface.lean` *carries the counterexample in terms*, which is
  still true — that file still carries the argument, and this one adds a theorem beside it rather
  than moving it. They are under-cited and not wrong, and both were held by an unmerged branch
  when this was written. The other five say something this file makes false or stale and are
  repaired in the same push.
* **Nothing about `ComplexAnalytic.sqSubOnePair` or any other pair.** The failure is not a
  property of every standard étale pair:
  `ComplexAnalytic.hypersurfaceCommonZeroImage_sqSubOnePair` (`OkaTest/OpenBaseFiniteness.lean`)
  has a bad set that is everything and
  `Oka/Analytification/StandardEtaleFiniteness.lean` says in terms that finiteness there is not
  known to fail. This file is one pair.
-/

universe u

open CategoryTheory ComplexAnalytic

namespace ComplexAnalytic

noncomputable section

/-! ### The two relations, written out -/

/-- **The localisation relation is `z₂·z₁ - 1`**: the inverse variable against
`ComplexAnalytic.condG`. -/
theorem eval_etalePresentation_cond_zero (z : ULift.{u} (Fin 3) → ℂ) :
    MvPolynomial.eval z (etalePresentation.{u} condBase.{u} condF.{u} condG.{u} 0) =
      z (ULift.up 2) * z (ULift.up 1) - 1 := by
  simp [etalePresentation, localisationPresentation, localisationIncl, localisationVar, Fin.snoc]

/-- **The hypersurface relation is `z₁² - z₀`**: `ComplexAnalytic.condF` in the new variables. -/
theorem eval_etalePresentation_cond_one (z : ULift.{u} (Fin 3) → ℂ) :
    MvPolynomial.eval z (etalePresentation.{u} condBase.{u} condF.{u} condG.{u} 1) =
      z (ULift.up 1) ^ 2 - z (ULift.up 0) := by
  simp [etalePresentation, localisationIncl, Fin.snoc]

/-! ### The morphism and a point of its source -/

/-- **The unrestricted composite**: the analytification of `ComplexAnalytic.condPair`'s structure
map, followed by the inclusion of the base's analytification into `ℂ¹`.

An `abbrev` rather than a `def` so that the two `IsLocalIso` and `Nonempty` facts below are found
through it by instance search; nothing here depends on its being reducible otherwise. -/
abbrev condEtaleProj :
    AnalyticSpace.analytification.{u} (etalePresentation.{u} condBase.{u} condF.{u} condG.{u}) ⟶
      AnalyticSpace.complexAffineSpace.{u} 1 :=
  analytificationMap.{u} (etalePresHom.{u} condBase.{u} condF.{u} condG.{u}) ≫
    analytificationInclHom.{u} condBase.{u}

/-- **The tuple `(1, 1, 1)` of `ℂ³`.** Both relations read `1 - 1` there, which is why the
constant function is the cheapest point: `z₁ = 1` is its own square root and its own inverse. -/
def condEtalePt : ULift.{u} (Fin 3) → ℂ := fun _ ↦ 1

/-- **The two relations vanish at `ComplexAnalytic.condEtalePt`**, by the two computations above.

**`ComplexAnalytic.condEtalePt` is unfolded by a `rfl` at each coordinate and never by naming it
to `simp`**, and the difference is measurable: a draft writing `simp [… , condEtalePt]` put
`ComplexAnalytic.condEtalePt.eq_1` into this module's `scripts/DumpOkaDecls.lean` row, which
`lake build` does not see and `comm -13` on that dump does. That is the economy
`OkaTest/StandardEtaleLocalIsoBase.lean` records for the same defect at four definitions; here one
`have` closes it, because the tuple is constant and so has one coordinate value rather than
four. -/
theorem eval_etalePresentation_condEtalePt (j : Fin 2) :
    MvPolynomial.eval condEtalePt.{u}
      (etalePresentation.{u} condBase.{u} condF.{u} condG.{u} j) = 0 := by
  have hpt : ∀ i, condEtalePt.{u} i = 1 := fun _ ↦ rfl
  fin_cases j <;>
    simp [eval_etalePresentation_cond_zero.{u}, eval_etalePresentation_cond_one.{u}, hpt]

/-- **The source of `ComplexAnalytic.condEtaleProj` is not empty.**

Without this the theorems below would be statements about a morphism out of an empty space, which
both fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso` and both of
`ComplexAnalytic.AnalyticSpace.IsFinite` satisfy vacuously — so a non-finiteness claim would be
false rather than uninteresting, and it is the hypothesis
`ComplexAnalytic.AnalyticSpace.not_isFinite_of_isLocalIso_of_not_surjective` takes. -/
theorem nonempty_analytification_etalePresentation_cond :
    Nonempty (AnalyticSpace.analytification.{u}
      (etalePresentation.{u} condBase.{u} condF.{u} condG.{u})) :=
  ⟨⟨⟨condEtalePt.{u}, trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} _ _).2 eval_etalePresentation_condEtalePt.{u}⟩⟩

/-! ### The missing point, and the two theorems -/

/-- **The origin of the line is not in the image of `ComplexAnalytic.condEtaleProj`.**

`ComplexAnalytic.base_analytificationMap_etalePresHom_comp_apply` reads the coordinate of the
image off the point, and then the two relations do the rest: `z₁² = z₀ = 0` forces `z₁ = 0` and
the localisation relation becomes `-1 = 0`. **That is where the standard étale algebra's inversion
is visible on points** — the branch point of the square-root cover is exactly what inverting `g`
removes, and it is the one point of the base with no preimage. -/
theorem base_condEtaleProj_ne_zero
    (y : AnalyticSpace.analytification.{u}
      (etalePresentation.{u} condBase.{u} condF.{u} condG.{u})) :
    ((condEtaleProj.{u}.toLRSHom.base y : AnalyticSpace.complexAffineSpace.{u} 1) :
      ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0 := by
  have hrel := (mem_zeroLocus_polySection_iff.{u} _ y.1).1 y.2
  have h0 := (eval_etalePresentation_cond_zero.{u} _).symm.trans (hrel 0)
  have h1 := (eval_etalePresentation_cond_one.{u} _).symm.trans (hrel 1)
  rw [base_analytificationMap_etalePresHom_comp_apply.{u},
    show localisationIncl.{u} (1 + 1) (localisationIncl.{u} 1 (ULift.up 0)) = ULift.up 0 from rfl]
  intro hz
  rw [hz, sub_eq_zero] at h1
  rw [pow_eq_zero_iff two_ne_zero |>.1 h1, mul_zero, zero_sub, neg_eq_zero] at h0
  exact one_ne_zero h0

/-- **The analytification of a standard étale morphism is not finite over the whole base**, at the
square-root cover of the line — the counterexample the module docstrings named at the top of this
file assert and none of them compiles.

The three inputs are `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` at
`ComplexAnalytic.condPair`, `ComplexAnalytic.nonempty_analytification_etalePresentation_cond`, and
`ComplexAnalytic.base_condEtaleProj_ne_zero`; the connectedness of `ℂ¹` is
`inferInstanceAs`, since the carrier of `ComplexAnalytic.AnalyticSpace.complexAffineSpace` is
`ULift (Fin n) → ℂ` definitionally but not syntactically, so instance search does not cross it on
its own. -/
theorem not_isFinite_condEtaleProj : ¬ AnalyticSpace.IsFinite condEtaleProj.{u} := by
  haveI := isLocalIso_analytificationMap_etalePresHom_comp.{u} condBase.{u} condF.{u} condG.{u}
    condPair.{u} condF_eq.{u} condG_eq.{u}
  haveI := nonempty_analytification_etalePresentation_cond.{u}
  haveI : PreconnectedSpace (AnalyticSpace.complexAffineSpace.{u} 1) :=
    inferInstanceAs (PreconnectedSpace (ULift.{u} (Fin 1) → ℂ))
  refine AnalyticSpace.not_isFinite_of_isLocalIso_of_not_surjective.{u} _ ?_
  intro hsurj
  obtain ⟨y, hy⟩ := hsurj (fun _ ↦ 0)
  exact base_condEtaleProj_ne_zero.{u} y (by rw [hy])

/-- **And so it is not finite étale**, which is the shape those same docstrings state the falsity
in. `ComplexAnalytic.AnalyticSpace.IsFiniteEtale.isFinite` is the whole proof; the
local-isomorphism field is *true* here, so it is the finiteness alone that fails. -/
theorem not_isFiniteEtale_condEtaleProj : ¬ AnalyticSpace.IsFiniteEtale condEtaleProj.{u} :=
  fun h ↦ not_isFinite_condEtaleProj.{u} h.isFinite

end

end ComplexAnalytic

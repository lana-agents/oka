/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# `ComplexAnalytic.etaleAnalytificationIso` is not an isomorphism of empty spaces

`Oka/Analytification/StandardEtaleAnalytification.lean` proves that the analytification of a
standard étale presentation is the distinguished open `D(G)` inside the analytification of the
hypersurface presentation, over the base. All three of its results are **hypothesis-free in `F`
and `G`** — no monicity, no `StandardEtalePair.cond`, no non-degeneracy — so none of them can be
vacuously satisfied. What was unchecked, and what that file's `## What is not here` recorded, is
whether the *objects* are degenerate: nothing said `ComplexAnalytic.localisationOpen
(hypersurfacePresentation g F) G` is inhabited for any `g`, `F`, `G` at all, so for all the
repository said the isomorphism could have been one of empty spaces.

**This file supplies one witness, and it is a construction rather than a quotation.** Taxis #1187
suggested quoting taxis #1112's `Pex` — `R = ℂ[X]`, `f = X² − C X`, `g = X` — and that does not
work: `Pex` is a `StandardEtalePair` exhibited to show the *unrestricted* `IsFiniteEtale`
statement false, by way of a **non-closed image**
(`Oka/Analytification/MonicHypersurface.lean`'s `## What is not here`). That shares no hypothesis
with "some `localisationOpen` is inhabited", and no amount of quoting it produces a point.

## The data, and why it is not degenerate in a second way

The base is **empty** — `k = 0`, so `ComplexAnalytic.polyPresentation` contributes nothing — over
`n = 1` variable, and the hypersurface is cut out by the last of the two variables alone:
`ComplexAnalytic.hyperLineF` is `z₁`, so `ComplexAnalytic.hyperLinePres` presents `ℂ[z₀, z₁] ⧸
(z₁)` and its analytification is the line `z₁ = 0` in `ℂ²`. `ComplexAnalytic.hyperLineG` is `z₀`,
so `D(G)` is that line punctured at the origin.

Two things have to be checked and both are here, because a witness that is non-empty and nothing
else is satisfied by data that trivialises the construction:

* `ComplexAnalytic.localisationOpen_hyperLinePres_ne_bot` — `D(G)` is **not empty**, so
  `ComplexAnalytic.etaleAnalytificationIso` at this data is not an isomorphism of empty spaces.
  Were `F` a unit the hypersurface itself would be empty and this would fail.
* `ComplexAnalytic.localisationOpen_hyperLinePres_ne_top` — `D(G)` is **not everything** either,
  so the localisation is not the identity and
  `ComplexAnalytic.etaleAnalytificationIso`'s right-hand side is a proper open subspace. Were `G`
  a nonzero constant this would fail, and the isomorphism would say nothing about an immersion.

## Main results

- `ComplexAnalytic.localisationOpen_hyperLinePres_ne_bot` and
  `ComplexAnalytic.localisationOpen_hyperLinePres_ne_top`: the distinguished open is a **proper
  non-empty** open subset of the hypersurface's analytification.
- `ComplexAnalytic.nonempty_restrict_hyperLinePres`: the right-hand side of
  `ComplexAnalytic.etaleAnalytificationIso` is non-empty at this data.
- `ComplexAnalytic.nonempty_analytification_etalePresentation_hyperLine`: **so is the left-hand
  side**, by transporting the point along the isomorphism itself. This is the statement that makes
  the isomorphism one of non-empty spaces, and it is the only place in this file where
  `ComplexAnalytic.etaleAnalytificationIso` is applied rather than described.

## What is not checked here

* **Nothing about `StandardEtalePair`.** `ComplexAnalytic.hyperLineF` and
  `ComplexAnalytic.hyperLineG` are polynomials chosen to make the two statements above true; no
  claim is made that they come from a standard étale pair, and
  `ComplexAnalytic.etaleAnalytificationIso` does not ask for one. So this is non-vacuity of the
  *isomorphism*, not evidence about étale morphisms.
* **Nothing about the simple-zero condition.** The germ of `z₁` at a point of `D(G)` does have
  order one along the last axis — `OkaTest/SimpleZeroStalk.lean` computes exactly that shape for
  a coordinate — but connecting it to `ComplexAnalytic.bijective_stalkMap_comp_uliftProj` here
  would need the cut-out datum for this hypersurface, which is not built. Taxis #1187 §3 is where
  that gap is recorded and it is unaffected.
* **No claim that this is the smallest witness**, or that a witness exists for every `F` and `G`.
  It does not: `F = 1` makes the hypersurface empty and `G = 0` makes `D(G)` empty. The statements
  in the library file are hypothesis-free precisely because they are true of those too, both sides
  being empty.
-/

open MvPolynomial CategoryTheory

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The data -/

/-- **The empty base**: no relations, in one variable. `ComplexAnalytic.polyPresentation` of it is
the empty family, so `ComplexAnalytic.hyperLinePres` is `ComplexAnalytic.hyperLineF` alone. -/
abbrev hyperLineBase : Fin 0 → MvPolynomial (ULift.{u} (Fin 1)) ℂ := fun j ↦ j.elim0

/-- The polynomial `z₁` cutting out the hypersurface: the line `z₁ = 0` in `ℂ²`. -/
abbrev hyperLineF : MvPolynomial (ULift.{u} (Fin 2)) ℂ := MvPolynomial.X (ULift.up 1)

/-- The polynomial `z₀` being inverted, so `D(G)` is that line punctured at the origin. -/
abbrev hyperLineG : MvPolynomial (ULift.{u} (Fin 2)) ℂ := MvPolynomial.X (ULift.up 0)

/-- **The hypersurface presentation at this data**, `ComplexAnalytic.hypersurfacePresentation` with
an empty base. -/
abbrev hyperLinePres : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  hypersurfacePresentation.{u} hyperLineBase.{u} hyperLineF.{u}

/-- Its one relation is `ComplexAnalytic.hyperLineF`, on the nose — so the analytification below is
the line and not a space built for the occasion. -/
theorem hyperLinePres_eq (j : Fin 1) : hyperLinePres.{u} j = hyperLineF.{u} := by
  rw [show j = Fin.last 0 from Subsingleton.elim _ _]
  exact Fin.snoc_last _ _

/-! ### Two points of the hypersurface -/

/-- **The point `(1, 0)`**, which is on the line and off the puncture. -/
def hyperLinePoint : AnalyticSpace.analytification.{u} hyperLinePres.{u} := by
  classical
  refine ⟨⟨fun l ↦ if l = ULift.up 0 then 1 else 0, trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} _ _).2 fun j ↦ ?_⟩
  rw [hyperLinePres_eq.{u} j, hyperLineF, MvPolynomial.eval_X]
  simp

/-- **The origin**, which is on the line and *at* the puncture. This is what makes `D(G)` proper
rather than the whole hypersurface. -/
def hyperLineOrigin : AnalyticSpace.analytification.{u} hyperLinePres.{u} :=
  ⟨⟨fun _ ↦ 0, trivial⟩, (mem_zeroLocus_polySection_iff.{u} _ _).2 fun j ↦ by
    rw [hyperLinePres_eq.{u} j, hyperLineF, MvPolynomial.eval_X]⟩

/-! ### The distinguished open is proper and non-empty -/

/-- **`ComplexAnalytic.hyperLinePoint` lies in `D(G)`**, since `z₀` takes the value `1` there. -/
theorem hyperLinePoint_mem :
    hyperLinePoint.{u} ∈ localisationOpen.{u} hyperLinePres.{u} hyperLineG.{u} := by
  refine (mem_localisationOpen_iff.{u} hyperLinePres.{u} hyperLineG.{u}).2 ?_
  rw [hyperLineG, MvPolynomial.eval_X]
  simp [hyperLinePoint]

/-- **The distinguished open is not empty**, so `ComplexAnalytic.etaleAnalytificationIso` at this
data is not an isomorphism of empty spaces. -/
theorem localisationOpen_hyperLinePres_ne_bot :
    localisationOpen.{u} hyperLinePres.{u} hyperLineG.{u} ≠ ⊥ := by
  intro hcon
  have hmem := hyperLinePoint_mem.{u}
  rw [hcon] at hmem
  exact hmem

/-- **The distinguished open is not everything either**, so the localisation is not the identity
and the right-hand side of `ComplexAnalytic.etaleAnalytificationIso` is a *proper* open subspace.
The origin is the point at which `z₀` vanishes. -/
theorem localisationOpen_hyperLinePres_ne_top :
    localisationOpen.{u} hyperLinePres.{u} hyperLineG.{u} ≠ ⊤ :=
  localisationOpen_ne_top.{u} hyperLinePres.{u} hyperLineG.{u} hyperLineOrigin.{u}
    (by rw [hyperLineG, MvPolynomial.eval_X]; rfl)

/-! ### Both sides of the isomorphism are non-empty -/

/-- **The right-hand side of `ComplexAnalytic.etaleAnalytificationIso` is non-empty** at this
data. -/
theorem nonempty_restrict_hyperLinePres :
    Nonempty ((AnalyticSpace.analytification.{u} hyperLinePres.{u}).restrict
      (localisationOpen.{u} hyperLinePres.{u} hyperLineG.{u})) :=
  ⟨⟨hyperLinePoint.{u}, hyperLinePoint_mem.{u}⟩⟩

/-- **And so is the left-hand side**, by transporting the point along the isomorphism.

This is what makes `ComplexAnalytic.etaleAnalytificationIso` an isomorphism of non-empty spaces
rather than a statement that survives being about nothing, and it is the only place in this file
where that isomorphism is applied rather than described. Note the direction: the isomorphism runs
from the étale analytification to the distinguished open, so it is its `inv` that carries the
point back. -/
theorem nonempty_analytification_etalePresentation_hyperLine :
    Nonempty (AnalyticSpace.analytification.{u}
      (etalePresentation.{u} hyperLineBase.{u} hyperLineF.{u} hyperLineG.{u})) :=
  ⟨(etaleAnalytificationIso.{u} hyperLineBase.{u} hyperLineF.{u} hyperLineG.{u}).inv.toLRSHom.base
    ⟨hyperLinePoint.{u}, hyperLinePoint_mem.{u}⟩⟩

end

end ComplexAnalytic

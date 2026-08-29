/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.FiniteMorphism

/-!
# Non-vacuity of finiteness for the projection of a monic hypersurface

`ComplexAnalytic.isFinite_comp_proj_of_range_eq` says that a hypersurface of `ℂ^(n+1)` cut out by
a continuous family of monic polynomials of one fixed degree is finite over `ℂ^n`. Its hypotheses
are six, and nothing in its statement says they can all hold at once. This file exhibits one
morphism at which they do.

**The parabola `z = w²` in `ℂ²`, projected to the `z`-line.** The curve is the image of the
closed embedding `ComplexAnalytic.parabolaIncl : ℂ ⟶ ℂ²`, `w ↦ (w², w)`, and the family is
`ComplexAnalytic.parabolaPoly`, the constant-coefficient-free `X² - C z` — monic of degree
exactly two, with a coefficient that genuinely moves with the base point.

## Why this example and not the axis

`OkaTest/FiniteMorphism.lean` already has a finite composite whose second factor is not finite:
`ComplexAnalytic.isFinite_axisIncl_comp_proj`, the first axis of `ℂ²` projected to the `z`-line.
**That one proves nothing about the theorem here**, for two reasons, and both are what this
example is chosen to avoid.

* Its composite is the *identity* of `ℂ`, so it is finite by
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` and needs no root bound. The
  composite below is `w ↦ w²`, which is **not injective**
  (`ComplexAnalytic.not_injective_base_parabolaIncl_comp_proj`), so that route is unavailable and
  `ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` is being used for something
  the older lemma cannot reach.
* Its hypersurface is `w = 0`, a *constant* family of degree one. The family below has degree two
  and its coefficient is the base coordinate itself, so `hc` — continuity of the coefficients —
  is a hypothesis with content rather than `continuous_const`.

What the two examples do share is the second factor: `ComplexAnalytic.AnalyticSpace.proj 1` is
`ComplexAnalytic.proj` (`ComplexAnalytic.analyticSpaceProj_one_eq_proj`), which is **not** finite,
so neither composite is an instance of `ComplexAnalytic.AnalyticSpace.isFinite_comp`.

**And it is not `ComplexAnalytic.isFinite_sq` either.** That morphism is `z ↦ z²` on the
*punctured* line `ℂ ∖ {0}`, obtained from `isClosedMap_npow` — a statement about one polynomial
map, on the space where it is a covering. What is below is the same function on the whole of `ℂ`,
obtained from the family bound; the two share no lemma, and the puncture is what
`ComplexAnalytic.isFinite_sq` needs and this does not.

## What is not checked here

* **Nothing about `ComplexAnalytic.IsCutOutBy`.** The morphism is built by hand and its image is
  computed directly, so `ComplexAnalytic.isFinite_comp_proj_of_range_eq` is what is applied here
  and `ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy` is not. Its one consumer anywhere is
  `ComplexAnalytic.isFinite_comp_proj_of_monic` in `Oka/Analytification/MonicHypersurface.lean`,
  which still takes the cut-out datum as a *hypothesis* — so what is not exhibited, here or there,
  is a concrete morphism of analytic spaces carrying one. The reason is the one
  `OkaTest/FiniteMorphism.lean` gives for `ComplexAnalytic.axisIncl`: cut-out data for a
  morphism of *analytic* spaces is never produced in this repository, only assumed.
* **Nothing about stalks**, so nothing here is a finite étale morphism.
  `Oka/AnalyticSpace/SimpleZeroStalk.lean` is the other half and the germ of `X² - C z` at a point
  of the parabola has a simple zero along the last axis only away from the origin, so this curve
  is *not* an instance of both halves at once — which is the honest reason no `IsFiniteEtale`
  statement appears below.
* **No degeneration.** The family here has constant degree by construction; that dropping the
  degree hypothesis to a bound breaks the theorem is asserted in the module docstring of
  `Oka/Topology/Algebra/Polynomial.lean` and is not exhibited here or anywhere.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

/-! ### The parabola `z = w²` as a closed subspace of `ℂ²` -/

/-- The pair of entire functions `(w², w)` on `ℂ`, as a family of global sections. -/
def parabolaFamily : ULift.{u} (Fin 2) → OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  fun j ↦ if j = ULift.up 0 then coord (ULift.up 0) ^ 2 else coord (ULift.up 0)

/-- **The parametrisation of the parabola, `ℂ ⟶ ℂ²`, `w ↦ (w², w)`.** -/
def parabolaIncl :
    AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.complexAffineSpace.{u} 2 :=
  AnalyticSpace.okaMap parabolaFamily.{u}

/-- **Its underlying map is `w ↦ (w², w)`.** -/
theorem base_parabolaIncl (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    ((parabolaIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) =
      fun j ↦ if j = ULift.up 0 then (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ^ 2
        else (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) := by
  refine funext fun j ↦ ?_
  change okaMapFun parabolaFamily.{u} _ j = _
  rw [okaMapFun_apply, parabolaFamily]
  by_cases hj : j = ULift.up 0
  · rw [if_pos hj, if_pos hj, map_pow, evalHom_coord]
  · rw [if_neg hj, if_neg hj, evalHom_coord]

/-- **The image of the parametrisation is exactly the parabola.**

The inclusion `⊆` is `ComplexAnalytic.base_parabolaIncl` read at the two indices; the reverse
sends a point of the parabola to its second coordinate, which is the retraction used below. -/
theorem range_base_parabolaIncl :
    Set.range ((parabolaIncl.{u}).toLRSHom.base :
        AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) =
      {q : AnalyticSpace.complexAffineSpace.{u} 2 |
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) =
          (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) ^ 2} := by
  refine Set.ext fun q ↦ ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    change ((parabolaIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) =
      ((parabolaIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) ^ 2
    rw [base_parabolaIncl]
    simp
  · refine ⟨fun _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1), funext fun j ↦ ?_⟩
    rw [show ((parabolaIncl.{u}).toLRSHom.base _ : ULift.{u} (Fin 2) → ℂ) = _
      from base_parabolaIncl _]
    dsimp only
    obtain ⟨j⟩ := j
    fin_cases j
    · simpa using hq.symm
    · simp

/-- The second coordinate, as a continuous retraction of `ComplexAnalytic.parabolaIncl`. -/
def parabolaRetract : AnalyticSpace.complexAffineSpace.{u} 2 →
    AnalyticSpace.complexAffineSpace.{u} 1 :=
  fun q _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1)

/-- **The parametrisation is a closed embedding.**

Embedding by `Function.LeftInverse.isEmbedding` at `ComplexAnalytic.parabolaRetract`, exactly as
for `ComplexAnalytic.axisIncl`; closed because by `ComplexAnalytic.range_base_parabolaIncl` the
image is where two continuous functions of `q` agree. -/
theorem isClosedEmbedding_base_parabolaIncl :
    IsClosedEmbedding ((parabolaIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) where
  toIsEmbedding := by
    refine Function.LeftInverse.isEmbedding (f := parabolaRetract.{u}) ?_
      (continuous_pi fun _ ↦ continuous_apply (ULift.up 1))
      (parabolaIncl.{u}).toLRSHom.base.hom.continuous
    intro p
    refine funext fun l ↦ ?_
    change ((parabolaIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = _
    rw [base_parabolaIncl]
    change (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = (p : ULift.{u} (Fin 1) → ℂ) l
    exact congrArg _ (Subsingleton.elim _ _)
  isClosed_range := by
    have h0 : Continuous fun q : AnalyticSpace.complexAffineSpace.{u} 2 ↦
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) := continuous_apply _
    have h1 : Continuous fun q : AnalyticSpace.complexAffineSpace.{u} 2 ↦
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) := continuous_apply _
    rw [range_base_parabolaIncl]
    exact isClosed_eq h0 (h1.pow 2)

/-! ### The family it is the zero locus of -/

/-- **The family `X² - C z` of monic quadratics over the `z`-line.** -/
def parabolaPoly (w : ULift.{u} (Fin 1) → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 2 - Polynomial.C (w (ULift.up 0))

theorem monic_parabolaPoly (w : ULift.{u} (Fin 1) → ℂ) : (parabolaPoly.{u} w).Monic :=
  Polynomial.monic_X_pow_sub_C _ two_ne_zero

theorem natDegree_parabolaPoly (w : ULift.{u} (Fin 1) → ℂ) :
    (parabolaPoly.{u} w).natDegree = 2 :=
  Polynomial.natDegree_X_pow_sub_C

/-- **Its coefficients are continuous in the base point**, and the one in degree zero is not
constant — it is the base coordinate. This is the hypothesis of
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` that the axis example discharges by
`continuous_const`. -/
theorem continuous_coeff_parabolaPoly (j : ℕ) :
    Continuous fun w : ULift.{u} (Fin 1) → ℂ ↦ (parabolaPoly.{u} w).coeff j := by
  have hz : Continuous fun w : ULift.{u} (Fin 1) → ℂ ↦ w (ULift.up 0) := continuous_apply _
  rcases eq_or_ne j 0 with rfl | hj
  · have h : (fun w : ULift.{u} (Fin 1) → ℂ ↦ (parabolaPoly.{u} w).coeff 0)
        = fun w ↦ -w (ULift.up 0) := by
      funext w
      simp [parabolaPoly]
    rw [h]
    exact hz.neg
  · have h : (fun w : ULift.{u} (Fin 1) → ℂ ↦ (parabolaPoly.{u} w).coeff j)
        = fun _ ↦ (Polynomial.X ^ 2 : Polynomial ℂ).coeff j := by
      funext w
      simp [parabolaPoly, Polynomial.coeff_C, hj]
    rw [h]
    exact continuous_const

/-- **The parabola is the zero locus of that family**, in the coordinates
`ComplexAnalytic.uliftSnocHomeo` supplies. -/
theorem range_base_parabolaIncl_eq_zeroLocus :
    Set.range ((parabolaIncl.{u}).toLRSHom.base :
        AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) =
      {z : AnalyticSpace.complexAffineSpace.{u} 2 |
        (parabolaPoly.{u} (uliftSnocHomeo.{u} 1 z).1).eval
          (uliftSnocHomeo.{u} 1 z).2 = 0} := by
  rw [range_base_parabolaIncl]
  ext q
  simp only [Set.mem_setOf_eq, parabolaPoly, uliftSnocHomeo_apply, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  exact eq_comm

/-! ### The projection this is finite over -/

/-- **The projection used here is the one `OkaTest/FiniteMorphism.lean` shows is not finite.**

`ComplexAnalytic.AnalyticSpace.proj 1` is `ComplexAnalytic.coordEmb` at
`ComplexAnalytic.uliftCastSuccEmb` and `ComplexAnalytic.proj` is `ComplexAnalytic.projFamily`;
the two families agree because `ULift (Fin 1)` is a subsingleton, so `Fin.castSucc` on it is the
constant `0`. Without this the statement below would be about a projection nobody had shown
anything about. -/
theorem analyticSpaceProj_one_eq_proj : AnalyticSpace.proj.{u} 1 = ComplexAnalytic.proj.{u} := by
  refine congrArg AnalyticSpace.okaMap (funext fun j ↦ ?_)
  change coord (ULift.up j.down.castSucc) = coord (ULift.up 0)
  rw [show j.down = 0 from Subsingleton.elim _ _]
  rfl

/-- **And it is not finite**, by `ComplexAnalytic.not_isFinite_proj` — its fibre over the origin
is the second axis. So the theorem below is not an instance of
`ComplexAnalytic.AnalyticSpace.isFinite_comp` either. -/
theorem not_isFinite_analyticSpaceProj_one :
    ¬ AnalyticSpace.IsFinite (AnalyticSpace.proj.{u} 1) :=
  analyticSpaceProj_one_eq_proj.{u} ▸ not_isFinite_proj.{u}

/-! ### The conclusion -/

/-- **The parabola is finite over the `z`-line**, by
`ComplexAnalytic.isFinite_comp_proj_of_range_eq`.

Every hypothesis of that theorem is discharged by a named statement above, so this is the witness
that the six of them are simultaneously satisfiable. -/
theorem isFinite_parabolaIncl_comp_proj :
    AnalyticSpace.IsFinite (parabolaIncl.{u} ≫ AnalyticSpace.proj.{u} 1) :=
  isFinite_comp_proj_of_range_eq parabolaIncl.{u} isClosedEmbedding_base_parabolaIncl.{u}
    monic_parabolaPoly.{u} natDegree_parabolaPoly.{u} continuous_coeff_parabolaPoly.{u}
    range_base_parabolaIncl_eq_zeroLocus.{u}

/-- **The underlying map of the composite is `w ↦ w²`.** -/
theorem base_parabolaIncl_comp_proj (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    (((parabolaIncl.{u} ≫ AnalyticSpace.proj.{u} 1).toLRSHom.base p) :
        ULift.{u} (Fin 1) → ℂ) =
      fun _ ↦ (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ^ 2 := by
  refine funext fun l ↦ ?_
  have hl : l.down = (0 : Fin 1) := Subsingleton.elim _ _
  rw [show ((parabolaIncl.{u} ≫ AnalyticSpace.proj.{u} 1).toLRSHom.base p :
      ULift.{u} (Fin 1) → ℂ) = _ from congrFun (base_proj_eq.{u} 1) _]
  change ((parabolaIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ)
    (ULift.up l.down.castSucc) = _
  rw [base_parabolaIncl]
  simp [hl]

/-- **And it is not injective**, so `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`
cannot produce `ComplexAnalytic.isFinite_parabolaIncl_comp_proj`.

This is the whole point of choosing the parabola: `1` and `-1` have the same image. The axis
example of `OkaTest/FiniteMorphism.lean` has an injective — indeed bijective — composite and so
says nothing about the theorem being tested. -/
theorem not_injective_base_parabolaIncl_comp_proj :
    ¬ Function.Injective ((parabolaIncl.{u} ≫ AnalyticSpace.proj.{u} 1).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 1) := by
  intro hinj
  have key : ((fun _ ↦ (1 : ℂ)) : AnalyticSpace.complexAffineSpace.{u} 1) =
      ((fun _ ↦ (-1 : ℂ)) : AnalyticSpace.complexAffineSpace.{u} 1) := by
    refine hinj (funext fun l ↦ ?_)
    rw [show (((parabolaIncl.{u} ≫ AnalyticSpace.proj.{u} 1).toLRSHom.base
        ((fun _ ↦ (1 : ℂ)) : AnalyticSpace.complexAffineSpace.{u} 1)) :
        ULift.{u} (Fin 1) → ℂ) = _ from base_parabolaIncl_comp_proj _,
      show (((parabolaIncl.{u} ≫ AnalyticSpace.proj.{u} 1).toLRSHom.base
        ((fun _ ↦ (-1 : ℂ)) : AnalyticSpace.complexAffineSpace.{u} 1)) :
        ULift.{u} (Fin 1) → ℂ) = _ from base_parabolaIncl_comp_proj _]
    norm_num
  have h := congrFun key (ULift.up 0)
  norm_num at h

end ComplexAnalytic

end

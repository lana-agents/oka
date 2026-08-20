/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the joint analyticity of the divided difference

`analyticAt_dslope_pair` says that `x ↦ dslope h (x 0) (x 1)` is analytic in the pair. An
existence-flavoured statement about a function nobody can identify is not usable, and a
statement about a function that happened to be constant in one of its arguments would be
one-variable analysis wearing a disguise. So this file pins the function down at a concrete `h`
where the answer is known: for `h z = z ^ 2` the divided difference is `a + b`, which depends on
both arguments and is not constant in either.

It also exercises `AnalyticAt.dslope_comp`, the form `#628` consumes: two holomorphic functions
substituted into the divided difference give a holomorphic function.
-/

open Complex Metric
open scoped Real

noncomputable section

/-- The squaring map is differentiable on every closed disc. -/
theorem differentiableOn_sq (R : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ ↦ z ^ 2) (closedBall 0 R) := by fun_prop

/-- **The divided difference of `z ↦ z ^ 2` is `a + b`**, on the diagonal as well as off it.

This is the known answer the joint statement is checked against. -/
theorem dslope_sq (a b : ℂ) : dslope (fun z : ℂ ↦ z ^ 2) a b = a + b := by
  rcases eq_or_ne b a with rfl | hab
  · rw [dslope_same, deriv_pow_field]
    norm_num
    ring
  · rw [dslope_of_ne _ hab, slope_def_field, div_eq_iff (sub_ne_zero.2 hab)]
    ring

/-- The Cauchy-kernel formula agrees with it, so `dividedDifference_eq_dslope` is not vacuous
either: the contour integral really does compute `a + b`. -/
theorem dividedDifference_sq {a b : ℂ} (ha : ‖a‖ < 2) (hb : ‖b‖ < 2) :
    dividedDifference 2 (fun z : ℂ ↦ z ^ 2) ![a, b] = a + b :=
  (dividedDifference_eq_dslope two_pos (differentiableOn_sq 2) ha hb).trans (dslope_sq a b)

/-- **The joint statement fires at a concrete point**, and the function it is about is
`x ↦ x 0 + x 1`, which is constant in neither argument. -/
theorem analyticAt_dslope_pair_sq (x₀ : Fin 2 → ℂ) (hx₀ : ∀ i, ‖x₀ i‖ < 2) :
    AnalyticAt ℂ (fun x : Fin 2 → ℂ ↦ dslope (fun z : ℂ ↦ z ^ 2) (x 0) (x 1)) x₀ :=
  analyticAt_dslope_pair two_pos (differentiableOn_sq 2) hx₀

/-- The function of the previous theorem, named. Without this the analyticity statement would be
consistent with the divided difference being constant, which would make it a statement about
one-variable analysis. -/
theorem eq_add_dslope_pair_sq :
    (fun x : Fin 2 → ℂ ↦ dslope (fun z : ℂ ↦ z ^ 2) (x 0) (x 1)) = fun x ↦ x 0 + x 1 :=
  funext fun _ ↦ dslope_sq _ _

/-- **Two holomorphic functions substituted into the divided difference**, at a concrete
instance: `z ↦ dslope (·² ) z (z ^ 3)` is analytic at the origin. This is the shape the mapping
property of `#628` consumes, and it is not available from Mathlib's one-variable `dslope`
lemmas, which would force the first argument to be constant. -/
theorem analyticAt_dslope_comp_sq :
    AnalyticAt ℂ (fun z : ℂ ↦ dslope (fun w : ℂ ↦ w ^ 2) z (z ^ 3)) 0 :=
  AnalyticAt.dslope_comp two_pos (differentiableOn_sq 2) analyticAt_id
    (analyticAt_id.pow 3) (by norm_num) (by norm_num)

/-- And it is the function it should be: `z + z ^ 3`. -/
theorem analyticAt_dslope_comp_sq_eq :
    (fun z : ℂ ↦ dslope (fun w : ℂ ↦ w ^ 2) z (z ^ 3)) = fun z ↦ z + z ^ 3 :=
  funext fun _ ↦ dslope_sq _ _

end

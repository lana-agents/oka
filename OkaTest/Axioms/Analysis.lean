/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Complex analysis

Results in one and several complex variables that mention nothing sheaf-theoretic — the material
of `Oka/Analytic/`.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### The divided difference is analytic in both variables -/

/--
info: 'analyticAt_dslope_pair' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_dslope_pair

/--
info: 'AnalyticAt.dslope_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AnalyticAt.dslope_comp

/--
info: 'dividedDifference_eq_dslope' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dividedDifference_eq_dslope

/-! ### `x ↦ xⁿ` on the nonzero elements of a proper normed field -/

/--
info: 'isClosedMap_npow' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isClosedMap_npow

/--
info: 'finite_fiber_npow' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finite_fiber_npow

/-! ### A function differentiable on an open set is analytic at each of its points

The one advertised result of `Oka/Analytic/ParametricCircleIntegral.lean` that no guard reaches.
Fifteen of the other sixteen are in the cone of the three `OkaTest/Axioms/Weierstrass.lean`
guards, since that file exists to prove the two circle-integral lemmas `Oka/Weierstrass.lean`
consumes; the sixteenth, `analyticAt_of_shift`, is reached by the three divided-difference guards
of this file — `analyticAt_dslope_pair`, `AnalyticAt.dslope_comp` and `dividedDifference_eq_dslope`
— through `Oka/Analytic/DividedDifference.lean`. This one is a by-product of the Cauchy formula
on a polydisc and has no consumer under `Oka/` at all.
See `OkaTest/Axioms.lean` for the measurement and the two probes that establish it. -/

/--
info: 'analyticAt_of_differentiableOn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_of_differentiableOn

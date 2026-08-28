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

/-! ### The zero locus of a continuous family of monic polynomials

The six results of `Oka/Topology/Algebra/Polynomial.lean`: the root bound, the joint continuity of
evaluation, the closed-image statement that carries the content, and the three forms of the
conclusion.
-/

/--
info: 'Polynomial.IsRoot.norm_le_monicRootBound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.IsRoot.norm_le_monicRootBound

/--
info: 'Polynomial.continuous_eval_of_continuous_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.continuous_eval_of_continuous_coeff

/--
info: 'Polynomial.isClosed_fst_image_of_monic' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.isClosed_fst_image_of_monic

/--
info: 'Polynomial.isClosedMap_fst_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.isClosedMap_fst_zeroLocus

/--
info: 'Polynomial.finite_preimage_fst_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.finite_preimage_fst_zeroLocus

/--
info: 'Polynomial.isProperMap_fst_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.isProperMap_fst_zeroLocus

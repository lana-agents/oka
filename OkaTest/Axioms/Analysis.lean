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

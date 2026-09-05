/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Complex analysis, `π₁(ℂ ∖ {0})`, and polynomial zero loci

Results that mention nothing sheaf-theoretic, from four modules:

* `Oka/Analytic/DividedDifference.lean`, the divided difference of a holomorphic function;
* `Oka/Analysis/Complex/CoveringMap.lean`, the map `x ↦ xⁿ` on the nonzero elements of a proper
  normed field;
* `Oka/Analysis/Complex/FundamentalGroup.lean`, the fundamental group of `ℂ ∖ {0}`;
* `Oka/Topology/Algebra/Polynomial.lean`, the zero locus of a continuous family of monic
  polynomials over an arbitrary topological parameter space.

**The last is the bulk of the file and it is not complex analysis.** The sentence this replaces
said *"the material of `Oka/Analytic/`"*, which at `27c185a` covered three of the guards below;
**the fourth module's are guarded below as well**, whose parameter space is any topological space
and whose statements never mention `ℂ`. `OkaTest/Axioms.lean`'s row for this file was widened on
that measurement, and this paragraph is the other half of the same repair — the routing table and
the file's own description had drifted apart in opposite directions. **The third module is not
complex analysis either**, and the same care applies to it: `ℂ ∖ {0}` appears in it as a
topological space, and what is computed is a fundamental group.

**A list is affordable here because four modules is the whole file.**
`OkaTest/Axioms/Sheaves.lean` declines to enumerate in terms — *"That is a description and not a
list"* — and `OkaTest/Axioms/LocalOkaRing.lean` enumerates but refuses to let the list be the
record, saying the headings are. At four modules neither move buys anything: a list this short is
the description, and it goes stale the moment a module is added — **which is what happened**. The
paragraph this replaces said, of three modules, that a fourth appearing is exactly when to
re-read it; the fourth is `Oka/Analysis/Complex/FundamentalGroup.lean`, and re-reading it is what
moved the count above, this file's title, and `OkaTest/Axioms.lean`'s row. **A sentence that
names the condition under which it goes stale is worth more than a stable one only if the person
who triggers the condition reads it**, so the same clause is left standing for the fifth.

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

/-! ### The fundamental group of the punctured plane

The four results of `Oka/Analysis/Complex/FundamentalGroup.lean`: that the period group of
`Complex.exp` is infinite cyclic, the fundamental group of `ℂ ∖ {0}` at an arbitrary basepoint and
at `1`, and that it is infinite — the last being what stops the other two from being an
isomorphism onto a group a reader cannot see is non-trivial.
-/

/--
info: 'Complex.intEquivZMultiplesTwoPiI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Complex.intEquivZMultiplesTwoPiI

/--
info: 'Complex.fundamentalGroupPuncturedEquivInt' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Complex.fundamentalGroupPuncturedEquivInt

/--
info: 'Complex.fundamentalGroupPuncturedOneEquivInt' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Complex.fundamentalGroupPuncturedOneEquivInt

/--
info: 'Complex.infinite_fundamentalGroupPunctured' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Complex.infinite_fundamentalGroupPunctured

/-! ### The zero locus of a continuous family of monic polynomials

The seven results of `Oka/Topology/Algebra/Polynomial.lean`: the root bound, the joint continuity
of evaluation, the two set-level statements that carry the content, and the three forms of the
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
info: 'Polynomial.finite_inter_fst_preimage_of_monic' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.finite_inter_fst_preimage_of_monic

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

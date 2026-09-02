/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: general commutative ring theory

The mirror-tree results about local rings with a coefficient field, about adic completions, about
localising at a maximal ideal, about descent and quotient base change of flatness, about relations
between elements of a ring localising, about counting the `n`-th roots of an element of an
algebraically closed field, and about evaluating a multivariate polynomial through the
equivalence that splits off one variable. Nothing here mentions anything complex-analytic.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Rigidity of a local homomorphism out of a ring with a coefficient field -/

/--
info: 'IsLocalRing.IsCoefficientField.ringHom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.IsCoefficientField.ringHom_ext

/-! ### Coefficient fields: evaluation, its uniqueness, and transport along a surjection

`Oka/RingTheory/LocalRing/ResidueField/Basic.lean`, which is the API the rigidity statement above
is stated about: the value of an element, the uniqueness of the constant it is congruent to, and
the surjection along which a coefficient field is inherited. -/

/--
info: 'IsLocalRing.IsCoefficientField.evalHom_eq_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.IsCoefficientField.evalHom_eq_iff

/--
info: 'IsLocalRing.IsCoefficientField.existsUnique_sub_mem_maximalIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.IsCoefficientField.existsUnique_sub_mem_maximalIdeal

/--
info: 'IsLocalRing.IsCoefficientField.of_surjective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.IsCoefficientField.of_surjective

/--
info: 'IsLocalRing.IsCoefficientField.evalHom_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.IsCoefficientField.evalHom_map

/--
info: 'IsLocalRing.IsCoefficientField.isLocalHom_comp_evalHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.IsCoefficientField.isLocalHom_comp_evalHom


/-! ### The projections of an adic completion -/

/--
info: 'AdicCompletion.factorPow_evalₐ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AdicCompletion.factorPow_evalₐ

/-! ### Recognising a ring as an adic completion, and localising at a maximal ideal -/

/--
info: 'AdicCompletion.equivOfQuotientEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AdicCompletion.equivOfQuotientEquiv

/--
info: 'IsLocalization.quotientPowAtPrimeEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalization.quotientPowAtPrimeEquiv

/--
info: 'MvPolynomial.idealOfVars.isMaximal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.idealOfVars.isMaximal

/-! ### Descent of flatness along the middle ring -/

/--
info: 'Module.Flat.of_faithfullyFlat_tower' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Flat.of_faithfullyFlat_tower

/-! ### Flatness under quotienting by an ideal of the base -/

/--
info: 'Module.Flat.quotIdealMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Flat.quotIdealMap

/--
info: 'Module.FaithfullyFlat.quotIdealMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.FaithfullyFlat.quotIdealMap

/-! ### Quotienting a faithfully flat ring map by an ideal of the source -/

/--
info: 'RingHom.FaithfullyFlat.quotIdealMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RingHom.FaithfullyFlat.quotIdealMap

/--
info: 'Module.Finite.of_ringEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.Finite.of_ringEquiv

/--
info: 'Module.FinitePresentation.of_ringEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Module.FinitePresentation.of_ringEquiv

/-! ### Relations between elements of a ring localise

`Oka/RingTheory/Localization/Module.lean`, the one piece of general commutative algebra behind
the coherence of the structure sheaf of a noetherian scheme. -/

/--
info: 'IsLocalization.exists_fun_eq_sum_of_sum_mul_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalization.exists_fun_eq_sum_of_sum_mul_eq_zero

/-! ### Counting `n`-th roots over an algebraically closed field

`Oka/FieldTheory/IsAlgClosed/Basic.lean`, which is what puts a number on the fibres of
`ComplexAnalytic.sq`. -/

/--
info: 'IsAlgClosed.card_setOf_pow_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsAlgClosed.card_setOf_pow_eq

/-! ### Evaluation through `MvPolynomial.optionEquivLeft` -/

/--
info: 'MvPolynomial.eval_eq_eval_optionEquivLeft' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.eval_eq_eval_optionEquivLeft

/-! ### A polynomial vanishing on a non-empty open set is zero

`Oka/Algebra/MvPolynomial/Funext.lean`, appended as its own section so that no section above
moves. It sits with `MvPolynomial.eval_eq_eval_optionEquivLeft` above rather than in
`OkaTest/Axioms/Analytification.lean` because it is a mirror-tree lemma about `MvPolynomial` and
names nothing of this repository's own.

Its consumer is `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`, guarded in
`OkaTest/Axioms/Analytification.lean`, which is the only place the topology hypotheses are
discharged — at `ℂ`, by instances Mathlib already has. -/

/--
info: 'MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.eq_zero_of_eval_eq_zero_of_isOpen

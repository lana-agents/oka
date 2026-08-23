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
between elements of a ring localising, and about counting the `n`-th roots of an element of an
algebraically closed field. Nothing here mentions anything complex-analytic.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Rigidity of a local homomorphism out of a ring with a coefficient field -/

/--
info: 'IsLocalRing.IsCoefficientField.ringHom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.IsCoefficientField.ringHom_ext


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

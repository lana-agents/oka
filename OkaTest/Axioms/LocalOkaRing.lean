/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: The ring of convergent power series

Results about `LocalOkaRing`, the ring of germs at the origin of holomorphic functions: the
Rückert basis theorem, the maximal ideal and its powers, the easy half of the analytic
Nullstellensatz, regularity of the germ ring, its completion, the quotients by a degree-one
Weierstrass polynomial, and change of coordinates. **This list is the file's headings and goes
stale the moment one is added without it** — the headings themselves are the record.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### The Rückert basis theorem -/

/--
info: 'LocalOkaRing.isNoetherianRing_fin' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.isNoetherianRing_fin

/--
info: 'LocalOkaRing.instIsNoetherianRing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.instIsNoetherianRing

/--
info: 'ComplexAnalytic.AnalyticSpace.instIsNoetherianRingStalk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.instIsNoetherianRingStalk

/--
info: 'LocalOkaRing.instUniqueFactorizationMonoid' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.instUniqueFactorizationMonoid

/-! ### The maximal ideal and the truncations -/

/--
info: 'LocalOkaRing.maximalIdeal_eq_span_coord' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.maximalIdeal_eq_span_coord

/--
info: 'LocalOkaRing.truncQuotientEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.truncQuotientEquiv
/-! ### The analytic Nullstellensatz (easy inclusion only) -/

/--
info: 'LocalOkaRing.radical_le_vanishingIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.radical_le_vanishingIdeal

/--
info: 'LocalOkaRing.vanishingIdeal_bot' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.vanishingIdeal_bot

/-! ### The germ ring is regular of dimension `n` -/

/--
info: 'LocalOkaRing.exists_eq_mul_lastVar_add_incl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_eq_mul_lastVar_add_incl

/--
info: 'LocalOkaRing.incl_eq_zero_of_mem_span_lastVar' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.incl_eq_zero_of_mem_span_lastVar

/--
info: 'LocalOkaRing.quotientLastVarEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.quotientLastVarEquiv

/--
info: 'LocalOkaRing.ringKrullDim_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.ringKrullDim_eq

/--
info: 'LocalOkaRing.ringKrullDim_eq_natCard' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.ringKrullDim_eq_natCard

/--
info: 'LocalOkaRing.instIsRegularLocalRing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.instIsRegularLocalRing

/--
info: 'LocalOkaRing.spanFinrank_maximalIdeal_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.spanFinrank_maximalIdeal_eq



/-! ### The completion is the formal power series ring

`Oka/Completion.lean`. `LocalOkaRing.toAdicCompletion_coe` is guarded alongside the isomorphism
because it is what says the isomorphism is the one induced by the inclusion; an isomorphism
without it is a statement about two abstract `ℂ`-algebras. -/

/--
info: 'LocalOkaRing.adicCompletionEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.adicCompletionEquiv

/--
info: 'LocalOkaRing.toAdicCompletion_coe' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.toAdicCompletion_coe

/--
info: 'LocalOkaRing.instFaithfullyFlat' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.instFaithfullyFlat

/--
info: 'LocalOkaRing.coe_mem_map_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.coe_mem_map_iff

/-! ### Quotienting by a degree-one Weierstrass polynomial

`Oka/Regular.lean`. The generalisation of `LocalOkaRing.quotientLastVarEquiv` from the coordinate
`X_n` to an arbitrary local Weierstrass polynomial of degree one, its instance at the graph of
a germ vanishing at the origin, and the ideal inequality that says the generalisation is one. -/

/--
info: 'LocalOkaRing.exists_eq_mul_fromPolynomial_add_incl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_eq_mul_fromPolynomial_add_incl

/--
info: 'LocalOkaRing.incl_eq_zero_of_mem_span_fromPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.incl_eq_zero_of_mem_span_fromPolynomial

/--
info: 'LocalOkaRing.quotientDegreeOneEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.quotientDegreeOneEquiv

/--
info: 'LocalOkaRing.isLocalWeierstrassPolynomial_X_sub_C' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.isLocalWeierstrassPolynomial_X_sub_C

/--
info: 'LocalOkaRing.quotientGraphEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.quotientGraphEquiv

/--
info: 'LocalOkaRing.span_fromPolynomial_X_sub_C_ne_span_lastVar' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.span_fromPolynomial_X_sub_C_ne_span_lastVar

/-! ### From a simple zero along the last axis to a degree-one polynomial

`Oka/Regular.lean`. Producing the `c` of the section above from an arbitrary germ: the shape of a
degree-one Weierstrass polynomial, the degree that `localweierstrass_preparation` does not report,
the resulting equality of ideals, and the quotient equivalence with no graph in its statement. -/

/--
info: 'LocalOkaRing.eq_X_sub_C_of_natDegree_eq_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.eq_X_sub_C_of_natDegree_eq_one

/--
info: 'LocalOkaRing.order_partialEval_eq_natDegree' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.order_partialEval_eq_natDegree

/--
info: 'MvPowerSeries.order_partialEval_eq_one_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPowerSeries.order_partialEval_eq_one_iff

/--
info: 'LocalOkaRing.exists_span_eq_span_X_sub_C' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_span_eq_span_X_sub_C

/--
info: 'LocalOkaRing.quotientSimpleZeroEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.quotientSimpleZeroEquiv

/-! ### Changing coordinates

`Oka/ChangeOfCoordinates.lean`. `LocalOkaRing.congr` transports a germ along a linear change of
the variables. Under this heading, the `LocalOkaRing.congr_…` guards are its characterisation, its
compatibility with taking germs and its functoriality; `LocalOkaRing.congrEquiv` is `congr` at a
bijection of the index type; and the `LocalOkaRing.exists_congr_…` guards are what it exists for —
every finite family of nonzero germs becomes general in the last variable after one common change,
which is Weierstrass preparation without a genericity hypothesis. -/

/--
info: 'LocalOkaRing.congr_represents' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congr_represents

/--
info: 'LocalOkaRing.congr_eq_of_represents' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congr_eq_of_represents

/--
info: 'LocalOkaRing.congr_germ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congr_germ

/--
info: 'LocalOkaRing.congr_toLocalOkaRingHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congr_toLocalOkaRingHom

/--
info: 'LocalOkaRing.congr_refl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congr_refl

/--
info: 'LocalOkaRing.congr_trans' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congr_trans

/--
info: 'LocalOkaRing.congrEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congrEquiv

/--
info: 'LocalOkaRing.exists_congr_isGeneralIn' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_congr_isGeneralIn

/--
info: 'LocalOkaRing.exists_congr_isGeneralIn_of_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_congr_isGeneralIn_of_ne_zero

/--
info: 'LocalOkaRing.exists_congr_localweierstrass_preparation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_congr_localweierstrass_preparation

/-! ### Relabelling the variables along an embedding of index types

`Oka/RenameIndex.lean`. `LocalOkaRing.incl` and `LocalOkaRing.congrEquiv` are the same
construction — renaming the variables — at an embedding and at a bijection respectively, and
`LocalOkaRing.uliftEquiv_renameEmb` and `LocalOkaRing.uliftEquiv_renameEmb_incl` say what that
buys: relabelling `ULift ι` as `ι` commutes with it, which is how a statement about
`ComplexAnalytic.AnalyticSpace`, whose coordinates are indexed by `ULift (Fin n)`, reaches one
about `LocalOkaRing.incl`, whose are indexed by `Fin n`. `LocalOkaRing.coeff_uliftEquiv` and
`LocalOkaRing.constantCoeff_uliftEquiv` say what that relabelling does to a coefficient: it moves
each to the relabelled exponent, and fixes the constant term. -/

/--
info: 'MvPowerSeries.Represents.renameEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPowerSeries.Represents.renameEmb

/--
info: 'LocalOkaRing.renameEmb_refl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.renameEmb_refl

/--
info: 'LocalOkaRing.renameEmb_trans' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.renameEmb_trans

/--
info: 'LocalOkaRing.incl_eq_renameEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.incl_eq_renameEmb

/--
info: 'LocalOkaRing.congrEquiv_eq_renameEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congrEquiv_eq_renameEmb

/--
info: 'LocalOkaRing.uliftEquiv_renameEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.uliftEquiv_renameEmb

/--
info: 'LocalOkaRing.uliftEquiv_renameEmb_incl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.uliftEquiv_renameEmb_incl

/--
info: 'LocalOkaRing.coeff_uliftEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.coeff_uliftEquiv

/--
info: 'LocalOkaRing.constantCoeff_uliftEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.constantCoeff_uliftEquiv

/--
info: 'LocalOkaRing.renameEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.renameEmb

/--
info: 'LocalOkaRing.uliftEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.uliftEquiv

/-! ### Realizing a germ Weierstrass polynomial at other coordinates

`Oka/UliftCoord.lean`. The heading above relabels the variables of a *germ*; this one moves the
realization of a germ Weierstrass polynomial by an honest polynomial over `OkaRing` across a
linear change of the coordinate space, which is what carries `Oka/Weierstrass.lean`'s output to
the `ULift`-indexed convention `ComplexAnalytic.AnalyticSpace` is stated at. -/

/--
info: 'LocalOkaRing.uliftCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.uliftCoord

/--
info: 'LocalOkaRing.congr_uliftCoord' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.congr_uliftCoord

/--
info: 'LocalOkaRing.exists_monic_realize_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_monic_realize_congr

/--
info: 'LocalOkaRing.exists_monic_realize_ulift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_monic_realize_ulift

/--
info: 'LocalOkaRing.exists_congr_monic_realize_of_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_congr_monic_realize_of_ne_zero

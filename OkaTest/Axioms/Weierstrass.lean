/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Weierstrass division and preparation

The Weierstrass division and preparation theorems and their uniqueness statements, from
`Oka/Weierstrass.lean` and `Oka/OkaLemma.lean`, together with the germ-versus-function dictionary
that `Oka/Weierstrass.lean` builds on the way to preparation.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.

## Why all of `Oka/Weierstrass.lean` is routed here, and not by namespace

Twelve of the fourteen results `Oka/Weierstrass.lean` advertises were guarded by nothing until
this file grew the headings below, and their names span four namespaces — `LocalOkaRing`,
`OkaRing`, `MvPowerSeries` and `Polynomial` — three of which have a row of their own in
`OkaTest/Axioms.lean`'s table. **They are all here anyway, because that table routes by the module
a declaration lives in and not by the namespace it is declared into**, and its own
re-measurement recipe says so: resolve every `#print axioms` name to its module and ask whether
some module's guards are covered by no row. All twelve resolve to `Oka.Weierstrass`, whose guards
this row already covered.

`exists_analyticAt_implicit` is the one where topic and module pull apart, and it stays here too.
It is the analytic implicit function theorem, so `OkaTest/Axioms/Analysis.lean` is arguable — but
that file guards only mirror-tree modules (`Oka.Analysis.*`, `Oka.Analytic.*`, `Oka.Topology.*`),
this theorem is not mirror-tree material, and its own docstring states it *"in the form needed for
the Weierstrass preparation theorem"*.
-/

/-! ### Weierstrass theory -/

/--
info: 'localweierstrass_division' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_division

/--
info: 'localweierstrass_division_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_division_unique

/--
info: 'localweierstrass_preparation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_preparation

/-! ### The germ–function dictionary

`Oka/Weierstrass.lean`'s own `## Main results` calls these *the dictionary between functions and
germs used to reduce Oka's coherence lemma to them*. -/

/--
info: 'OkaRing.germ_toOkaRing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OkaRing.germ_toOkaRing

/--
info: 'LocalOkaRing.fromPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.fromPolynomial

/--
info: 'OkaRing.exists_restrict_eq_of_germ_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OkaRing.exists_restrict_eq_of_germ_eq

/--
info: 'LocalOkaRing.exists_okaRing_germ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_okaRing_germ

/--
info: 'OkaRing.exists_isUnit_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OkaRing.exists_isUnit_restrict

/-! ### Realizing germ polynomials by polynomials over a neighbourhood

`LocalOkaRing.exists_isWeierstrassPolynomial_realize` is the one of the twelve with live
consumers: `LocalOkaRing.exists_monic_realize_congr`, `LocalOkaRing.exists_monic_realize_ulift`
and `LocalOkaRing.exists_congr_monic_realize_of_ne_zero` in `Oka/UliftCoord.lean` all rest on it,
and all three are guarded — so `#print axioms` already covered it *transitively*. **A transitive
guard is not a guard**: it fails the moment the consumer is restated or removed, and it says
nothing about this lemma on its own. Its two neighbours in the preparation chain,
`localweierstrass_preparation` above and `LocalOkaRing.exists_congr_localweierstrass_preparation`
in `OkaTest/Axioms/LocalOkaRing.lean`, were pinned and it was not, so the chain was held at both
ends and not in the middle. -/

/--
info: 'LocalOkaRing.exists_isWeierstrassPolynomial_realize' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_isWeierstrassPolynomial_realize

/--
info: 'LocalOkaRing.exists_poly_germPoly' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.exists_poly_germPoly

/--
info: 'Polynomial.exists_map_restrict_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.exists_map_restrict_eq_zero

/-! ### The change of coordinates making finitely many germs general in the last variable -/

/--
info: 'MvPowerSeries.Represents.homogeneous_eval_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPowerSeries.Represents.homogeneous_eval_eq_zero

/--
info: 'MvPowerSeries.exists_direction' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPowerSeries.exists_direction

/--
info: 'lineEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lineEquiv

/-! ### The analytic implicit function theorem

The input to `localweierstrass_preparation` above, and the reason division by the generic
Weierstrass polynomial suffices to prove it. -/

/--
info: 'exists_analyticAt_implicit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_analyticAt_implicit

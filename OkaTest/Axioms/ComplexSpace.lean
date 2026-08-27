/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Holomorphic functions on `ℂ^ι`

Results about `OkaRing` and the structure sheaf of `ℂ^ι`, including polynomials read as
holomorphic functions.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Polynomials as holomorphic functions -/

/--
info: 'OkaRing.ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OkaRing.ofMvPolynomial

/--
info: 'LocalOkaRing.ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.ofMvPolynomial

/--
info: 'LocalOkaRing.constantCoeff_coe_ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.constantCoeff_coe_ofMvPolynomial

/--
info: 'MvPowerSeries.fromPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPowerSeries.fromPolynomial

/-! ### The stalk of the structure sheaf at a point

`Oka/StalkEquiv.lean`: the stalk of `𝒪_{ℂ^ι}` at `y` is the ring of convergent power series
about `y`, the germs vanishing at `y` are its maximal ideal, and so the stalk is local. -/

/--
info: 'okaStalkEquiv_germ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms okaStalkEquiv_germ

/--
info: 'constantCoeff_okaStalkEquiv_germ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms constantCoeff_okaStalkEquiv_germ

/--
info: 'mem_maximalIdeal_stalk_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_maximalIdeal_stalk_iff

/--
info: 'ComplexAnalytic.stalkCoord_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.stalkCoord_ne_zero

/--
info: 'germ_mem_maximalIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms germ_mem_maximalIdeal_iff

/--
info: 'map_okaStalkEquiv_maximalIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms map_okaStalkEquiv_maximalIdeal

/--
info: 'isLocalRing_okaStalk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLocalRing_okaStalk

/-! ### The structure sheaf itself, and the locally-ringed-space spelling of it

`okaSheaf` is the definition every statement above is about, and `complexSpace_ringSheaf` is the
`rfl` that lets a theorem stated for `(complexSpace ι).ringSheaf` be read as a theorem about it.
Both are advertised — the second by `Oka/AnalyticSpace/Relations.lean`, which is where the
reading is used — and until this tranche neither was reached by any guard. -/

/--
info: 'okaSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms okaSheaf

/--
info: 'complexSpace_ringSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexSpace_ringSheaf

/--
info: 'okaCommSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms okaCommSheaf

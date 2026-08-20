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
Nullstellensatz, and regularity of the germ ring.

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


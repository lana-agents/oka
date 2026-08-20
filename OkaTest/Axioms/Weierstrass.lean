/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Weierstrass division and preparation

The Weierstrass division and preparation theorems and their uniqueness statements, from
`Oka/Weierstrass.lean` and `Oka/OkaLemma.lean`.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
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


/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: general commutative ring theory

The mirror-tree results about local rings with a coefficient field. Nothing here mentions
anything complex-analytic.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Rigidity of a local homomorphism out of a ring with a coefficient field -/

/--
info: 'IsLocalRing.IsCoefficientField.ringHom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsLocalRing.IsCoefficientField.ringHom_ext

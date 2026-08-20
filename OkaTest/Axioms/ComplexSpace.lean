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


/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Analytification

The comparison morphism `ℂ^ι ⟶ Spec (MvPolynomial ι ℂ)` of `Oka/Analytification/` and its
map on stalks.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### The comparison morphism `ℂ^ι ⟶ Spec (MvPolynomial ι ℂ)` -/

/--
info: 'complexSpaceToSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexSpaceToSpec

/--
info: 'mem_complexSpaceToSpec_base_asIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_complexSpaceToSpec_base_asIdeal_iff

/--
info: 'isMaximal_complexSpaceToSpec_base_asIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isMaximal_complexSpaceToSpec_base_asIdeal

/--
info: 'complexSpaceToSpec_base_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexSpaceToSpec_base_injective

/--
info: 'complexAffineSpaceToAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexAffineSpaceToAffineSpace

/-! ### The stalk map of the comparison morphism -/

/--
info: 'toStalk_stalkMap_complexSpaceToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toStalk_stalkMap_complexSpaceToSpec

/--
info: 'okaStalkEquiv_stalkMap_complexSpaceToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms okaStalkEquiv_stalkMap_complexSpaceToSpec

/--
info: 'isUnit_ofMvPolynomial_of_mem_primeCompl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isUnit_ofMvPolynomial_of_mem_primeCompl

/--
info: 'stalkMap_eq_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stalkMap_eq_lift

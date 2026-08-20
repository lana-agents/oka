/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Subspaces cut out by global sections

The zero locus of a family of global sections of the structure sheaf of a locally ringed
space, the closed immersion cutting it out, and the mapping property of that immersion.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### The zero locus of a family of global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isClosed_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isClosed_zeroLocus

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.range_zeroLocusι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.range_zeroLocusι

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isClosedEmbedding_zeroLocusι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isClosedEmbedding_zeroLocusι

/-! ### The closed subspace cut out by a family of global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.stalkMap_zeroLocusιHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.stalkMap_zeroLocusιHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.zeroLocusStalkQuotientEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.zeroLocusStalkQuotientEquiv

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι

/-! ### The topological half of the mapping property of `IsCutOutBy` -/

/--
info: 'ComplexAnalytic.Γgerm_mem_maximalIdeal_of_c_app_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γgerm_mem_maximalIdeal_of_c_app_eq_zero

/--
info: 'ComplexAnalytic.IsCutOutBy.baseLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.baseLift

/--
info: 'ComplexAnalytic.IsCutOutBy.baseLift_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.baseLift_unique

/-! ### Uniqueness of the factorisation through a subspace cut out by global sections -/

/--
info: 'ComplexAnalytic.IsCutOutBy.mono' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.mono

/--
info: 'ComplexAnalytic.IsCutOutBy.hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.hom_ext

/--
info: 'ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy

/-! ### The structure sheaf of a subspace cut out by global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_quotientSheafifyToPushforward' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_quotientSheafifyToPushforward

/--
info: 'ComplexAnalytic.IsCutOutBy.pushforwardIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.pushforwardIso

/-! ### The mapping property of a subspace cut out by global sections -/

/--
info: 'ComplexAnalytic.IsCutOutBy.existsUnique_lift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.existsUnique_lift

/--
info: 'ComplexAnalytic.IsCutOutBy.uniqueIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.uniqueIso

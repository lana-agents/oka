/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression test

The library is `sorry`-free, and its results rest only on the three standard axioms of Lean:
`propext`, `Classical.choice` and `Quot.sound`. A `sorry` is only a warning, not an error, so
nothing in an ordinary `lake build` would notice if one were reintroduced — the proof of a
theorem depending on it would simply start depending on `sorryAx` as well.

This file pins that down: each `#guard_msgs` below fails the build if the axiom dependencies of
the named theorem ever change. Together with the `sorry` grep in
`.github/workflows/lean_action_ci.yml` it is what keeps the completeness claim in `README.md`
honest.

The file is not part of the `Oka` library; it is the `OkaTest` library of `lakefile.toml`,
which `defaultTargets` also builds, so plain `lake build` exercises it. The layout follows
Mathlib's own `MathlibTest`: a test library must live in a directory of its own, outside the
source tree of the library it tests, or Lake rejects its imports.

## Updating this file

If a theorem below is legitimately restated or renamed, do **not** delete its assertion. Run
the corresponding `#print axioms` (for instance with `lake env lean OkaTest/Axioms.lean`, or
in the editor) and paste the message Lean actually prints back into the expected docstring.
The expected message must stay `[propext, Classical.choice, Quot.sound]`: any other axiom —
`sorryAx` above all — is a regression, not something to record.

New assertions go at the **end** of the file, under a new `/-! ### … -/` heading, and never in
the middle. The main theorem is stated first precisely so that the tail of the file is a pure
append zone: every feature branch used to insert just before `/-! ### The main theorem -/`,
which made this file a standing merge conflict between concurrent pull requests. See issue
#558.
-/

/-! ### The main theorem -/

/--
info: 'ComplexAnalytic.IsLocalModel.hasLocalRelations' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsLocalModel.hasLocalRelations

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf

/-! ### Oka's coherence lemma on `ℂ^n` -/

/-- info: 'oka' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka

/-- info: 'oka'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka'

/-- info: 'oka_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka_fin

/-- info: 'okaStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms okaStatement

/-! ### Oka's bounded degree lemma -/

/-- info: 'oka_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka_lemma

/-- info: 'oka_lemma_weierstrass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka_lemma_weierstrass

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

/-! ### Quotients of presheaves of rings -/

/--
info: 'TopCat.Presheaf.surjective_stalkFunctor_map_toQuotientSpan' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Presheaf.surjective_stalkFunctor_map_toQuotientSpan

/--
info: 'TopCat.Presheaf.ker_stalkFunctor_map_toQuotientSpan' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Presheaf.ker_stalkFunctor_map_toQuotientSpan

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

/-! ### Coherence of finitely generated ideal sheaves -/

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherent_idealSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherent_idealSheaf

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteType_kernel_sectionsHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteType_kernel_sectionsHom

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

/-! ### Local models, and the node as a complex analytic space -/

/--
info: 'ComplexAnalytic.isLocalModel_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalModel_zeroLocus

/--
info: 'ComplexAnalytic.AnalyticSpace.zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.zeroLocus

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf_zeroLocus

/--
info: 'ComplexAnalytic.mem_zeroLocus_nodeSection_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_zeroLocus_nodeSection_iff

/--
info: 'ComplexAnalytic.isCoherentStructureSheaf_node' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherentStructureSheaf_node

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

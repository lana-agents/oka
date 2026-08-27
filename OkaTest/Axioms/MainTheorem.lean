/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Oka coherence: the main theorem

The headline results of the development: Oka's coherence theorem for `ℂ^n`, the coherence of
the structure sheaf of a complex analytic space, and the two lemmas of `Oka/Statement.lean`
they rest on.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
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


/-! ### The coherence of `𝒪_{ℂ^ι}`, at the spellings its consumers hold

`ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf` above is the statement for a general
analytic space.  These four are `ℂ^ι` itself, at the four spellings of its structure sheaf that
`Oka/AnalyticSpace/Relations.lean` advertises, and none of them was reached by any guard before
this tranche: the general theorem's proof does not go through them, so a `sorry` in one would
have turned nothing red. -/

/--
info: 'isCoherentStructureSheaf_complexSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isCoherentStructureSheaf_complexSpace

/--
info: 'isCoherent_unit_okaSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isCoherent_unit_okaSheaf

/--
info: 'isCoherent_unit_okaSheaf_fin' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isCoherent_unit_okaSheaf_fin

/--
info: 'isCoherentStructureSheaf_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isCoherentStructureSheaf_complexAffineSpace

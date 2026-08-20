/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: morphisms of complex analytic spaces

The morphisms of analytic spaces built from holomorphic maps, and the first morphism out of a
space which is not `ℂ^n`.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Morphisms given by a family of entire functions -/

/--
info: 'ComplexAnalytic.okaMapHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaMapHom

/--
info: 'ComplexAnalytic.Γ_map_okaMapHom_coord' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γ_map_okaMapHom_coord

/--
info: 'ComplexAnalytic.AnalyticSpace.okaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.okaMap

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_hom_complexLine' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_hom_complexLine

/-! ### The coordinate morphisms out of the node -/

/--
info: 'ComplexAnalytic.nodeToLine' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.nodeToLine

/--
info: 'ComplexAnalytic.Γ_map_nodeToLineHom_coord' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γ_map_nodeToLineHom_coord

/--
info: 'ComplexAnalytic.surjective_base_nodeToLineHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_base_nodeToLineHom

/--
info: 'ComplexAnalytic.not_injective_base_nodeToLineHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.not_injective_base_nodeToLineHom

/--
info: 'ComplexAnalytic.nodeToLine_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.nodeToLine_ne

/-! ### The `m`-fold statement and its naturality -/

/--
info: 'ComplexAnalytic.AnalyticSpace.coordPullback_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coordPullback_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquiv

/--
info: 'ComplexAnalytic.eq_nodeIncl_of_coordPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eq_nodeIncl_of_coordPullback

/-! ### The mapping property for morphisms of complex analytic spaces -/

/--
info: 'ComplexAnalytic.IsCutOutBy.isCLinearHom_lift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.isCLinearHom_lift

/--
info: 'ComplexAnalytic.IsCutOutBy.existsUnique_liftHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.existsUnique_liftHom

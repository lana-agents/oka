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

/--
info: 'ComplexAnalytic.base_nodeIncl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.base_nodeIncl

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

/-! ### Morphisms out of an open subspace of `ℂ^n` -/

/--
info: 'ComplexAnalytic.okaMapOpenHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaMapOpenHom

/--
info: 'ComplexAnalytic.Γ_map_okaMapOpenHom_coord' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γ_map_okaMapOpenHom_coord

/--
info: 'ComplexAnalytic.AnalyticSpace.okaMapOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.okaMapOpen

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.homComplexLineEquivRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.homComplexLineEquivRestrict

/-! ### From local morphisms to `ℂ` to a global one -/

/--
info: 'ComplexAnalytic.AnalyticSpace.restrictLE' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.restrictLE

/--
info: 'ComplexAnalytic.AnalyticSpace.base_eq_eval_coordPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.base_eq_eval_coordPullback

/--
info: 'ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_local_hom_of_chartLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_local_hom_of_chartLift

/-! ### `Hom(Z, ℂ) ≃ Γ(Z, 𝒪_Z)` for a general `Z` -/

/--
info: 'ComplexAnalytic.Γ_map_restrictHom_toRestrictΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γ_map_restrictHom_toRestrictΓ

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_chartLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_chartLift

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_general' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_general

/--
info: 'ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral

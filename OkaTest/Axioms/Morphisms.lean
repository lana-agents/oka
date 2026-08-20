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

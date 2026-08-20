/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: General sheaf theory

Results about presheaves and sheaves that mention nothing analytic — the mirror-tree material
of `Oka/Topology/Sheaves/` and `Oka/CategoryTheory/`.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

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


/-! ### Pushforward along an embedding is fully faithful -/

/--
info: 'TopCat.Presheaf.pushforwardFullyFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Presheaf.pushforwardFullyFaithful

/--
info: 'TopCat.Sheaf.pushforwardFullyFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Sheaf.pushforwardFullyFaithful

/-! ### Gluing locally ringed spaces along an open cover -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_eq_iff

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.isOpen_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.isOpen_iff

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.isIso_fromGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.isIso_fromGlued

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.openCoverOfOpens

/-! ### Two open immersions of locally ringed spaces with the same image -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq

/-! ### Gluing morphisms over a cover by open subsets -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_to_base_of_left' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_to_base_of_left

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.restrictLE' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.restrictLE

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isEmpty' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isEmpty

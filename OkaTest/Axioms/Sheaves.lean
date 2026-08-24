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

/-! ### Locality of global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover

/-! ### Crossing an isomorphism on global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_hom_inv_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_hom_inv_apply

/-! ### Sections and germs on an open subspace -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.germ_eq_stalkMap_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.germ_eq_stalkMap_ofRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_over_ambient' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_over_ambient

/-! ### The `Γ`-`Spec` adjunction

`Oka/AlgebraicGeometry/GammaSpecAdjunction.lean`. Consumed by
`Oka/Analytification/Presentation.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality

/-! ### Gluing an algebra structure over an open cover

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueSection

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueSection

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueSection_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueSection_eq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isCompatible_map_le_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isCompatible_map_le_top

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueSection_map_le_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueSection_map_le_top

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.resAlgMap_eq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.resAlgMap_eq_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMap

/-! ### Pulling an algebra structure back, and gluing one given on the members of a cover

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean` and
`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_ofRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_hom_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_hom_injective

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.iSup_isOpenEmbedding_obj_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.iSup_isOpenEmbedding_obj_top

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.glueAlgMapRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.glueAlgMapRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMapRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMapRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.opensRange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.opensRange

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.iSup_opensRange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.iSup_opensRange

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict_hom_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict_hom_fac

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.restrictAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.restrictAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.restrictAlgMap_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.restrictAlgMap_comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.isCompatible_restrictAlgMap_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.isCompatible_restrictAlgMap_comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueAlgMapRestrict_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueAlgMapRestrict_comapAlgMap

/-! ### The germ of a global section of `𝒪_{Spec R}` at a prime

`Oka/AlgebraicGeometry/Spec.lean`. Mirror-tree material with nothing analytic in it. -/

/--
info: 'AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff

/--
info: 'AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff'

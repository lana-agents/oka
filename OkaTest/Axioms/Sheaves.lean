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


/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict_of_isEmpty' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict_of_isEmpty

/-! ### Locality of global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover

/-! ### Functoriality of global sections, read elementwise

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. The two lemmas the `Iso` versions
below specialise: `AlgebraicGeometry.LocallyRingedSpace.Γ` is contravariant, and these
say so at an element rather than at the map. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_id_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_id_apply

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply

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


/--
info: 'AlgebraicGeometry.LocallyRingedSpace.germ_res' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.germ_res

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.c_app_res' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.c_app_res

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γ_map_ofRestrict_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γ_map_ofRestrict_apply

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Γgerm_Γ_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Γgerm_Γ_map

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap

/-! ### The image of an open subspace

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`. What the underlying map of
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict` hits, for one open and for a composite
of two. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict_comp

/-! ### Lifting sections and germs along a stalkwise-surjective morphism

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`'s `LocalModel` section. A germ in the
image of a stalk map is the germ of a section on a smaller open, and the family version
that a finite generating set needs. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_localLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_localLift

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_localCombination' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_localCombination

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_localLift_family' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_localLift_family

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
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover

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

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.OpenCover.comapAlgMap_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.OpenCover.comapAlgMap_ext

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

/-! ### Stalk maps along a factorisation, and the coproduct of locally ringed spaces

`Oka/Geometry/RingedSpace/LocallyRingedSpace.lean` and
`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`. Two out of three for stalk maps,
the coproduct's cover and the injectivity of its inclusions, and the four properties of a descent
map out of it that a finite étale morphism is built from.

**Every declaration that second file lists under `## Main results` is asserted here, and that is
still not a complete guard of it.** The sentence that stood here named `sigmaOpenCover` among the
unasserted ones and it is asserted below; what remains unasserted is what the file does not
advertise — `exists_sigma_ι_base_eq`, `eq_of_sigmaι_base_eq`, `sigmaι_base_injective`,
`disjoint_range_sigmaι` and the rest. `python3 scripts/guard_coverage.py --by-file` is what
distinguishes the two, and it reports the advertised half only. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_of_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_of_comp

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.base_sigmaι_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.base_sigmaι_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.image_base_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.image_base_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc


/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigma_ι_isOpenImmersion' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigma_ι_isOpenImmersion

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_colimit_ι_base_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_colimit_ι_base_eq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_eq_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.sigmaι_base_eq_iff

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover

/-! ### The inverse image of a locally ringed space along a continuous map

`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImage.lean`. The two definitions — the space
and the morphism to the base — and the two results, which are the same isomorphism read as a
statement about the stalks and as a statement about the morphism. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImage

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.inverseImageHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.inverseImageHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.stalkMap_inverseImageHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.stalkMap_inverseImageHom

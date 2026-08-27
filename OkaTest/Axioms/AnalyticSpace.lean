/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Complex analytic spaces

Local models, the node as a complex analytic space that is not a manifold, and the value of a
section of the structure sheaf at a point.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Local models, and the node as a complex analytic space -/

/--
info: 'ComplexAnalytic.isLocalModel_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalModel_zeroLocus

/--
info: 'ComplexAnalytic.isCLinearHom_restrictTopIso_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_restrictTopIso_inv

/--
info: 'ComplexAnalytic.isCLinearHom_restrictTopIso_inv_constants' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_restrictTopIso_inv_constants

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
info: 'ComplexAnalytic.origin_mem_zeroLocus_nodeSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.origin_mem_zeroLocus_nodeSection


/--
info: 'ComplexAnalytic.isCoherentStructureSheaf_node' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherentStructureSheaf_node

/-! ### The residue field of a complex analytic space is `ℂ` -/

/--
info: 'ComplexAnalytic.AnalyticSpace.existsUnique_sub_stalkAlgMap_mem_maximalIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.existsUnique_sub_stalkAlgMap_mem_maximalIdeal

/--
info: 'ComplexAnalytic.AnalyticSpace.evalStalk_eq_zero_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.evalStalk_eq_zero_iff
/--
info: 'ComplexAnalytic.AnalyticSpace.residueFieldEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.residueFieldEquiv


/--
info: 'ComplexAnalytic.eval_ofCutOut' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_ofCutOut

/--
info: 'ComplexAnalytic.eval_nodeCoord' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_nodeCoord

/--
info: 'ComplexAnalytic.nodeCoord_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.nodeCoord_mul

/--
info: 'ComplexAnalytic.nodeCoord_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.nodeCoord_ne_zero

/-! ### Continuity of the value of a section -/

/--
info: 'ComplexAnalytic.evalStalk_chart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.evalStalk_chart

/--
info: 'ComplexAnalytic.AnalyticSpace.continuous_eval' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.continuous_eval

/--
info: 'ComplexAnalytic.AnalyticSpace.continuous_eval_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.continuous_eval_top

/-! ### Naturality of evaluation, and rigidity of germs on `ℂ^ι` -/

/--
info: 'ComplexAnalytic.AnalyticSpace.evalStalk_stalkMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.evalStalk_stalkMap

/--
info: 'ComplexAnalytic.AnalyticSpace.eval_c_app' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.eval_c_app

/--
info: 'ComplexAnalytic.okaStalk_ringHom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaStalk_ringHom_ext

/-! ### A morphism to `ℂ^n` is determined by the pullbacks of the coordinates

`AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext` is general locally-ringed-space material
with no row of its own in the topic table of `OkaTest/Axioms.lean`; it sits here because the
only thing that uses it is the rigidity statement below. If a reviewer prefers it in
`OkaTest/Axioms/Sheaves.lean` that is a two-line change. -/

/--
info: 'ComplexAnalytic.eval_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_complexAffineSpace

/--
info: 'ComplexAnalytic.eval_restrict_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_restrict_complexAffineSpace

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext

/--
info: 'ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace

/--
info: 'ComplexAnalytic.nodeCoord_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.nodeCoord_ne

/-! ### An open subspace of a complex analytic space is a complex analytic space -/

/--
info: 'ComplexAnalytic.exists_local_model_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_local_model_restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofRestrict

/-! ### Being a complex analytic space is a local condition

`Oka/AnalyticSpace/Local.lean`. -/

/--
info: 'ComplexAnalytic.HasLocalModels' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.HasLocalModels

/--
info: 'ComplexAnalytic.AnalyticSpace.hasLocalModels' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hasLocalModels

/--
info: 'ComplexAnalytic.AnalyticSpace.ofHasLocalModels' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofHasLocalModels

/--
info: 'ComplexAnalytic.HasLocalModels.restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.HasLocalModels.restrict

/--
info: 'ComplexAnalytic.HasLocalModels.of_iSup_eq_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.HasLocalModels.of_iSup_eq_top

/--
info: 'ComplexAnalytic.hasLocalModels_iff_iSup_eq_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hasLocalModels_iff_iSup_eq_top

/--
info: 'ComplexAnalytic.AnalyticSpace.ofOpens' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofOpens

/-! ### The `ℂ`-algebra structure of a glued analytic space

`Oka/AnalyticSpace/Local.lean`. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.ofOpensCompatible' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofOpensCompatible

/--
info: 'ComplexAnalytic.AnalyticSpace.map_ofOpensCompatible_algebraMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.map_ofOpensCompatible_algebraMap

/-! ### The non-vanishing locus of a section, and mapping into an open subspace

`Oka/AnalyticSpace/Nonvanishing.lean`. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.liftRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.liftRestrict

/--
info: 'AlgebraicGeometry.RingedSpace.isUnit_res_of_le_basicOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.RingedSpace.isUnit_res_of_le_basicOpen

/--
info: 'ComplexAnalytic.AnalyticSpace.liftOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftOpen

/--
info: 'ComplexAnalytic.AnalyticSpace.liftOpen_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftOpen_fac

/--
info: 'ComplexAnalytic.AnalyticSpace.hom_ext_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hom_ext_restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff

/--
info: 'ComplexAnalytic.AnalyticSpace.isUnit_resΓ_of_le_nonvanishing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isUnit_resΓ_of_le_nonvanishing

/-! ### Gluing an analytic space out of a cover by abstract spaces

`Oka/AnalyticSpace/Glue.lean`. -/

/--
info: 'ComplexAnalytic.IsCLinearHom.eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCLinearHom.eq

/--
info: 'ComplexAnalytic.isCLinearHom_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_comapAlgMap

/--
info: 'ComplexAnalytic.IsCLinearHom.of_openCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCLinearHom.of_openCover

/--
info: 'ComplexAnalytic.HasLocalModels.of_iso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.HasLocalModels.of_iso

/--
info: 'ComplexAnalytic.AnalyticSpace.ofOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofOpenCover

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap

/--
info: 'ComplexAnalytic.AnalyticSpace.ofGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofGlueData

/--
info: 'ComplexAnalytic.AnalyticSpace.algebraMap_ofOpenCover_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.algebraMap_ofOpenCover_comapAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.liftRestrict_uniq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.liftRestrict_uniq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_f'

/-! ### The analytic structure on a gluing -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.comp_toSpecOfAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.comp_toSpecOfAlgMap

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.toSpecOfAlgMap_injective

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.exists_toSpecOfAlgMap_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.exists_toSpecOfAlgMap_eq

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.vIsoPullback

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap

/--
info: 'ComplexAnalytic.GlueDataCLinear' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueDataCLinear

/--
info: 'ComplexAnalytic.glueDataCLinear_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDataCLinear_comapAlgMap

/--
info: 'ComplexAnalytic.isCompatible_of_glueDataCLinear' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCompatible_of_glueDataCLinear

/--
info: 'ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_ofGlueDataCLinear_algebraMap

/--
info: 'ComplexAnalytic.AnalyticSpace.algebraMap_ofGlueDataCLinear_comapAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.algebraMap_ofGlueDataCLinear_comapAlgMap

/-! ### The fields of `CategoryTheory.GlueData.ofGlueData'` -/

/--
info: 'CategoryTheory.GlueData.ofGlueData'_f_self' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_f_self

/--
info: 'CategoryTheory.GlueData.ofGlueData'_f_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_f_of_ne

/--
info: 'CategoryTheory.GlueData.ofGlueData'_t_self' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_t_self

/--
info: 'CategoryTheory.GlueData.ofGlueData'_t_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_t_of_ne

/--
info: 'CategoryTheory.GlueData'.f'_self' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData'.f'_self

/--
info: 'CategoryTheory.GlueData'.f'_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData'.f'_of_ne

/--
info: 'CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_t_comp_f_of_ne

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom

/-! ### Gluing a morphism -/

/--
info: 'ComplexAnalytic.AnalyticSpace.isCLinearHom_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCLinearHom_glueMorphisms

/--
info: 'ComplexAnalytic.AnalyticSpace.glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.glueMorphisms

/--
info: 'ComplexAnalytic.AnalyticSpace.toLRSHom_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toLRSHom_glueMorphisms

/--
info: 'ComplexAnalytic.AnalyticSpace.ι_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ι_glueMorphisms

/--
info: 'ComplexAnalytic.AnalyticSpace.isCLinearHom_map_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCLinearHom_map_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.glueMorphisms_map_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.glueMorphisms_map_comp

/-! ### The disjoint union of a family of analytic spaces

`Oka/AnalyticSpace/Sigma.lean`. The object, its inclusions, the descent map, and the two
non-vacuity statements at the two ends of the index type. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigma

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaι

/--
info: 'ComplexAnalytic.isCLinearHom_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.isEmpty_sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isEmpty_sigma

/--
info: 'ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc

/-! ### The trivial `n`-sheeted cover, and finiteness of a descent map

`Oka/AnalyticSpace/SigmaFiniteEtale.lean`. That finiteness and being a local isomorphism pass
from the members of a disjoint union to a descent map out of it, and the trivial `ι`-sheeted
cover `∐_{i : ι} X ⟶ X` with its count of sheets. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.toLRSHom_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toLRSHom_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold

/-! ### The constants of a complex analytic space

`Oka/AnalyticSpace/Basic.lean` advertises this under `## Main definitions`: the algebra map from
the constants agrees with the restriction map, which is what lets a section be compared with a
scalar at all. -/

/--
info: 'ComplexAnalytic.constantsAlgMap_eq_resAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.constantsAlgMap_eq_resAlgMap

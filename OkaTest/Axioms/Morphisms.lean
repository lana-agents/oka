/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: morphisms of complex analytic spaces

The morphisms of analytic spaces built from holomorphic maps, the first morphism out of a
space which is not `ℂ^n`, and the classes of morphisms — finite, local isomorphism, finite étale —
together with the topological criteria they are proved from.

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

/--
info: 'ComplexAnalytic.AnalyticSpace.symm_homComplexLineEquivGeneral_coordPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.symm_homComplexLineEquivGeneral_coordPullback

/--
info: 'ComplexAnalytic.AnalyticSpace.coordPullback_symm_homComplexLineEquivGeneral' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coordPullback_symm_homComplexLineEquivGeneral

/-! ### The `m`-fold statement: `Hom(Z, ℂ^m) ≃ Γ(Z, 𝒪_Z)^m`

`Oka/AnalyticSpace/HolomorphicMapOpen.lean` and
`Oka/AnalyticSpace/HolomorphicMapGeneral.lean`. The `m = 1` results guarded above are now
instances of these rather than separate proofs. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_restrict

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_of_local' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_of_local

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general

/--
info: 'ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral

/--
info: 'ComplexAnalytic.AnalyticSpace.symm_homComplexAffineSpaceEquivGeneral_coordPullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.symm_homComplexAffineSpaceEquivGeneral_coordPullback

/--
info: 'ComplexAnalytic.AnalyticSpace.coordPullback_symm_homComplexAffineSpaceEquivGeneral' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coordPullback_symm_homComplexAffineSpaceEquivGeneral

/--
info: 'ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquiv_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquiv_eq

/-! ### Finite morphisms -/

/--
info: 'ComplexAnalytic.AnalyticSpace.IsFinite' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.IsFinite

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_iff

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_id

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_of_isIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_of_isIso

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_of_isCutOutBy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_of_isCutOutBy

/--
info: 'ComplexAnalytic.AnalyticSpace.not_isFinite_of_infinite_fiber' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_isFinite_of_infinite_fiber

/--
info: 'ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber

/-! ### Local isomorphisms and finite étale morphisms -/

/--
info: 'ComplexAnalytic.AnalyticSpace.IsLocalIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.IsLocalIso

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_id

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso

/--
info: 'ComplexAnalytic.AnalyticSpace.IsFiniteEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.IsFiniteEtale

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_id

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_isIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_isIso

/--
info: 'ComplexAnalytic.AnalyticSpace.liftRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftRestrict

/--
info: 'ComplexAnalytic.AnalyticSpace.toLRSHom_liftRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toLRSHom_liftRestrict

/--
info: 'ComplexAnalytic.AnalyticSpace.liftRestrict_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftRestrict_fac

/-! ### The germ dictionary: a local inverse makes a holomorphic map a stalk isomorphism -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_liftRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_liftRestrict

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict

/--
info: 'ComplexAnalytic.injective_stalkMap_okaMapHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.injective_stalkMap_okaMapHom

/--
info: 'ComplexAnalytic.surjective_stalkMap_okaMapHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_stalkMap_okaMapHom

/--
info: 'ComplexAnalytic.isIso_stalkMap_okaMapHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_okaMapHom

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_stalkMap_okaMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_stalkMap_okaMap

/-! ### Forgetting coordinates, on germs and stalks

`Oka/AnalyticSpace/ProjectionStalk.lean`. The heading above records when a stalk map is an
isomorphism; these record what one particular stalk map *is*, which is what a quotient statement
about `LocalOkaRing` needs before it can be read as a statement about a morphism of spaces. The
`coordEmb` three are the general statement, for the map `ℂ^ι → ℂ^κ` forgetting the coordinates
outside an embedding `κ ↪ ι`; the `projCoords` three are its instance at `Fin.castSuccEmb`, and
the last is the same projection between complex analytic spaces, where the coordinates are
indexed by `ULift (Fin n)` and the germ rings have to be relabelled to reach
`LocalOkaRing.incl`. -/

/--
info: 'ComplexAnalytic.okaMapFun_projCoords' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaMapFun_projCoords

/--
info: 'ComplexAnalytic.germ_okaMapC_projCoords' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.germ_okaMapC_projCoords

/--
info: 'ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords

/--
info: 'ComplexAnalytic.okaMapFun_coordEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaMapFun_coordEmb

/--
info: 'ComplexAnalytic.germ_okaMapC_coordEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.germ_okaMapC_coordEmb

/--
info: 'ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_coordEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_coordEmb

/--
info: 'ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj

/-! ### The third rung: a finite étale morphism is a covering map

The first of the two is the mirror-tree topological criterion in
`Oka/Topology/Covering/Basic.lean` and says nothing about analytic spaces; it is guarded here
rather than apart from its only consumer. -/

/--
info: 'IsClosedMap.isCoveringMap_of_isLocalHomeomorph' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsClosedMap.isCoveringMap_of_isLocalHomeomorph

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale

/-! ### The number of sheets, constant over a preconnected base

`IsEvenlyCovered.eventually` and the two `IsCoveringMap` statements are mirror-tree topology, in
`Oka/Topology/Covering/Basic.lean`; the two `ComplexAnalytic` ones are their application to the
third rung. -/

/--
info: 'IsEvenlyCovered.eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsEvenlyCovered.eventually

/--
info: 'IsCoveringMap.eventually_nonempty_homeomorph' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsCoveringMap.eventually_nonempty_homeomorph

/--
info: 'IsCoveringMap.nonempty_homeomorph_fiber' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsCoveringMap.nonempty_homeomorph_fiber

/--
info: 'ComplexAnalytic.AnalyticSpace.nonempty_homeomorph_fiber_of_isFiniteEtale' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.nonempty_homeomorph_fiber_of_isFiniteEtale

/--
info: 'ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale

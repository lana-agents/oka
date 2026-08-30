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
together with the topological criteria they are proved from, in both directions — the criteria
that read a class off the underlying map, and the construction that produces a morphism in a
class from a covering map — and the constructions that feed those criteria a family of monic
polynomials.

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
info: 'ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp

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
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict

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
outside an embedding `κ ↪ ι`; the `projCoords` group is its instance at `Fin.castSuccEmb`, and
the `uliftProj` pair is the same projection between complex analytic spaces, where the
coordinates are indexed by `ULift (Fin n)` and the germ rings have to be relabelled to reach
`LocalOkaRing.incl`. The two `…_apply` guards are the germ statements read at an arbitrary
element of the stalk, which is the form `Oka/AnalyticSpace/SimpleZeroStalk.lean` consumes. The
last **four** are the definitions the whole group is about, in file order:
`ComplexAnalytic.coordEmb`, `ComplexAnalytic.projCoords`, `ComplexAnalytic.uliftCastSuccEmb` and
`ComplexAnalytic.AnalyticSpace.proj`. -/

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
info: 'ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords_apply

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

/--
info: 'ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply

/--
info: 'ComplexAnalytic.coordEmb' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coordEmb

/--
info: 'ComplexAnalytic.projCoords' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.projCoords

-- The only assertion in this tree that is *not* `[propext, Classical.choice, Quot.sound]`, and
-- the direction it differs in is the safe one: relabelling `Fin.castSucc` through `ULift` is
-- structural, so nothing analytic and no choice reaches it. `OkaTest/Axioms.lean`'s rule is that
-- an assertion must never name a *further* axiom; naming fewer is a fact about the declaration.
/-- info: 'ComplexAnalytic.uliftCastSuccEmb' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.uliftCastSuccEmb

/--
info: 'ComplexAnalytic.AnalyticSpace.proj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.proj

/-! ### The third rung: a finite étale morphism is a covering map

The first two are mirror-tree topological criteria in `Oka/Topology/Covering/Basic.lean` and say
nothing about analytic spaces; they are guarded here rather than apart from their consumers. They
are converse to one another, and only the second is used by the heading at the foot of this
file. -/

/--
info: 'IsClosedMap.isCoveringMap_of_isLocalHomeomorph' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsClosedMap.isCoveringMap_of_isLocalHomeomorph

/--
info: 'IsCoveringMap.isClosedMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsCoveringMap.isClosedMap

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

/-! ### A hypersurface with a simple zero projects isomorphically on stalks

`Oka/AnalyticSpace/SimpleZeroStalk.lean`. The stalk half of *the analytification of a standard
étale morphism is a local isomorphism*: the two headings above supply what a stalk map of a
projection *is* and when a stalk map is an isomorphism, and these join them to
`LocalOkaRing.quotientSimpleZeroEquiv`. The first is the kernel of a one-section cut-out, the
second is the whole proof with both identifications taken as arguments, and the four after it are
its two instances — `Fin` and `ULift (Fin _)` — each as a bijection and as an `IsIso`. -/

/--
info: 'ComplexAnalytic.IsCutOutBy.mem_ker_stalkMap_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.mem_ker_stalkMap_iff

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_of_incl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_of_incl

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_projCoords' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_projCoords

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_projCoords' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_projCoords

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_uliftProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_uliftProj

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_uliftProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_uliftProj

/--
info: 'ComplexAnalytic.IsCutOutBy.evalHom_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.evalHom_eq_zero

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_coeff

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_coeff

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_coeff

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff

/-! ### The same hypothesis as a partial derivative, for a polynomial cutting section

`Oka/AnalyticSpace/SimpleZeroPolynomial.lean`. The four above take one Taylor coefficient of the
germ of the cutting section; these four take `MvPolynomial.pderiv` of the polynomial the section
comes from, evaluated at the point, which is the form a standard étale presentation supplies.
They are guarded under this heading rather than the one above because they are results of a
different file, and beside it because each is one rewrite away from its neighbour there. -/

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_pderiv

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_pderiv

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_pderiv

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv

/-! ### The projection of a monic hypersurface to its base is finite

`Oka/AnalyticSpace/MonicProjection.lean`, together with the general criterion it consumes from
`Oka/AnalyticSpace/Finite.lean`. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding

/--
info: 'ComplexAnalytic.uliftSnocHomeo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.uliftSnocHomeo

/--
info: 'ComplexAnalytic.base_proj_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.base_proj_eq

/--
info: 'ComplexAnalytic.range_base_eq_of_isCutOutBy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_eq_of_isCutOutBy

/--
info: 'ComplexAnalytic.isFinite_comp_proj_of_range_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_comp_proj_of_range_eq

/--
info: 'ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy

/-! ### Over an open subset of the base: the projection of a cylinder

`Oka/AnalyticSpace/OpenBaseProjection.lean`, together with
`ComplexAnalytic.AnalyticSpace.restrictHom` from `Oka/AnalyticSpace/OpenSubspace.lean`, which is
what makes the projection over `V` a restricted morphism. The two headings above are the same two
halves over the whole of `ℂ^(n+1)`; these carry both across the restriction, which is what a
standard étale algebra — inverting a polynomial as well as cutting one out — needs. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.restrictHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.restrictHom

/--
info: 'ComplexAnalytic.cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.cylinder

/--
info: 'ComplexAnalytic.mem_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_cylinder

/--
info: 'ComplexAnalytic.AnalyticSpace.projRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.projRestrict

/--
info: 'ComplexAnalytic.cylinderHomeo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.cylinderHomeo

/--
info: 'ComplexAnalytic.base_projRestrict_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.base_projRestrict_eq

/--
info: 'ComplexAnalytic.range_base_eq_of_isCutOutBy_resΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_eq_of_isCutOutBy_resΓ

/--
info: 'ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq

/--
info: 'ComplexAnalytic.isFinite_comp_projRestrict_of_isCutOutBy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_comp_projRestrict_of_isCutOutBy

/--
info: 'ComplexAnalytic.cylinderStalkEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.cylinderStalkEquiv

/--
info: 'ComplexAnalytic.baseStalkEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.baseStalkEquiv

/--
info: 'ComplexAnalytic.cylinderStalkEquiv_stalkMap_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.cylinderStalkEquiv_stalkMap_ofRestrict

/--
info: 'ComplexAnalytic.cylinderStalkEquiv_stalkMap_projRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.cylinderStalkEquiv_stalkMap_projRestrict

/--
info: 'ComplexAnalytic.cylinderStalkEquiv_Γgerm_resΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.cylinderStalkEquiv_Γgerm_resΓ

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_projRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_projRestrict

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_projRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_projRestrict

/-! ### A covering space of a complex analytic space is a complex analytic space

`Oka/AnalyticSpace/CoveringSpace.lean`. The converse of *the third rung* above, at the level of
the spaces and not only of the maps: a local homeomorphism into an analytic space makes its source
one, and a covering map with finite fibres makes it finite étale. `IsCoveringMap.isClosedMap`,
guarded under that heading, is what supplies the second half — the closed base map that finite
fibres do not give. It is not the only mirror-tree topology the construction consumes: the cover
by sheets the first half is checked on is `IsLocalHomeomorph.sSup_sheetOpens`, guarded in
`OkaTest/Axioms/Sheaves.lean`. -/

/--
info: 'ComplexAnalytic.inverseImageAlgMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.inverseImageAlgMap

/--
info: 'ComplexAnalytic.hasLocalModels_inverseImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hasLocalModels_inverseImage

/--
info: 'ComplexAnalytic.AnalyticSpace.coveringSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coveringSpace

/--
info: 'ComplexAnalytic.AnalyticSpace.coveringSpaceHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coveringSpaceHom

/--
info: 'ComplexAnalytic.AnalyticSpace.base_coveringSpaceHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.base_coveringSpaceHom

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_coveringSpaceHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_coveringSpaceHom

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom

/--
info: 'ComplexAnalytic.AnalyticSpace.toCoveringSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toCoveringSpace

/--
info: 'ComplexAnalytic.AnalyticSpace.toLRSHom_toCoveringSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toLRSHom_toCoveringSpace

/--
info: 'ComplexAnalytic.AnalyticSpace.base_toCoveringSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.base_toCoveringSpace

/--
info: 'ComplexAnalytic.AnalyticSpace.toCoveringSpace_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.toCoveringSpace_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_toCoveringSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_toCoveringSpace

/--
info: 'ComplexAnalytic.AnalyticSpace.coveringSpaceIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coveringSpaceIso

/--
info: 'ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.exists_iso_coveringSpace

/-! ### The family of a monic polynomial with holomorphic coefficients

`Oka/AnalyticSpace/HolomorphicFamily.lean`. The heading above transports the projection of a
monic hypersurface across a restriction of the base and takes the family as a hypothesis; this
one produces the family, from a polynomial whose coefficients are holomorphic functions on the
base rather than polynomial functions on `ℂ^n`. -/

/--
info: 'ComplexAnalytic.uliftInitCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.uliftInitCLM

/--
info: 'ComplexAnalytic.pullbackCylinder' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.pullbackCylinder

/--
info: 'ComplexAnalytic.lastCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.lastCoord

/--
info: 'ComplexAnalytic.cylinderSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.cylinderSection

/--
info: 'ComplexAnalytic.okaFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaFamily

/--
info: 'ComplexAnalytic.evalHom_cylinderSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.evalHom_cylinderSection

/--
info: 'ComplexAnalytic.monic_okaFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.monic_okaFamily

/--
info: 'ComplexAnalytic.natDegree_okaFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.natDegree_okaFamily

/--
info: 'ComplexAnalytic.continuous_coeff_okaFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.continuous_coeff_okaFamily

/--
info: 'ComplexAnalytic.isFinite_comp_projRestrict_of_monic' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_comp_projRestrict_of_monic

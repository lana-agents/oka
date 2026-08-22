/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Analytification

The comparison morphisms of `Oka/Analytification/`: `ℂ^ι ⟶ Spec (MvPolynomial ι ℂ)` and its
map on stalks, `X^an ⟶ Spec (ℂ[x]/I)` for a presented affine `ℂ`-algebra, the local ring of
`𝔸^ι` at the origin with its completion, the faithful flatness of the germs over it, and the
analytification as a functor on finitely generated `ℂ`-algebras.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### The comparison morphism `ℂ^ι ⟶ Spec (MvPolynomial ι ℂ)` -/

/--
info: 'complexSpaceToSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexSpaceToSpec

/--
info: 'mem_complexSpaceToSpec_base_asIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_complexSpaceToSpec_base_asIdeal_iff

/--
info: 'isMaximal_complexSpaceToSpec_base_asIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isMaximal_complexSpaceToSpec_base_asIdeal

/--
info: 'complexSpaceToSpec_base_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexSpaceToSpec_base_injective

/--
info: 'complexAffineSpaceToAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexAffineSpaceToAffineSpace

/-! ### The stalk map of the comparison morphism -/

/--
info: 'toStalk_stalkMap_complexSpaceToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toStalk_stalkMap_complexSpaceToSpec

/--
info: 'okaStalkEquiv_stalkMap_complexSpaceToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms okaStalkEquiv_stalkMap_complexSpaceToSpec

/--
info: 'isUnit_ofMvPolynomial_of_mem_primeCompl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isUnit_ofMvPolynomial_of_mem_primeCompl

/--
info: 'stalkMap_eq_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stalkMap_eq_lift

/-! ### The analytification of a presented affine `ℂ`-algebra

`Oka/Analytification/Presentation.lean`. The guard for
`AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality`, which that file consumes, is in
`OkaTest/Axioms/Sheaves.lean` with the rest of the mirror-tree `LocallyRingedSpace` material;
it sat here while PR #71 was in the merge queue, to keep two branches from appending to the
same file's tail, and that reason has expired. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.analytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.analytification

/--
info: 'ComplexAnalytic.mem_zeroLocus_polySection_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_zeroLocus_polySection_iff

/--
info: 'ComplexAnalytic.AnalyticSpace.mem_toΓSpec_base_asIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.mem_toΓSpec_base_asIdeal_iff

/--
info: 'ComplexAnalytic.analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec

/--
info: 'ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff

/--
info: 'ComplexAnalytic.analytificationToSpec_base_asIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec_base_asIdeal

/--
info: 'ComplexAnalytic.isMaximal_analytificationToSpec_base_asIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isMaximal_analytificationToSpec_base_asIdeal

/--
info: 'ComplexAnalytic.analytificationToSpec_base_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec_base_injective

/--
info: 'ComplexAnalytic.analytificationToSpec_comp_specMk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec_comp_specMk

/-! ### The universal property of the analytification -/

/--
info: 'ComplexAnalytic.Γ_map_comp_ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γ_map_comp_ofMvPolynomial

/--
info: 'ComplexAnalytic.analytificationInclHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationInclHom

/--
info: 'ComplexAnalytic.eval₂_analytificationCoord_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval₂_analytificationCoord_eq_zero

/--
info: 'ComplexAnalytic.existsUnique_hom_analytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.existsUnique_hom_analytification

/--
info: 'ComplexAnalytic.hom_ext_analytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hom_ext_analytification

/--
info: 'ComplexAnalytic.analytificationIsoOfPresentationIdealEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationIsoOfPresentationIdealEq

/-! ### The local ring at the origin and its completion

`Oka/Analytification/LocalRing.lean`. `polyLocalAdicCompletionEquiv_of_algebraMap` is guarded
alongside the isomorphism because it is what says the isomorphism is the one induced by the
inclusion of polynomials. -/

/--
info: 'ComplexAnalytic.polyLocalToMvPowerSeries' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalToMvPowerSeries

/--
info: 'ComplexAnalytic.polyLocalAdicCompletionEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalAdicCompletionEquiv

/--
info: 'ComplexAnalytic.polyLocalAdicCompletionEquiv_of_algebraMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalAdicCompletionEquiv_of_algebraMap

/--
info: 'ComplexAnalytic.flat_polyLocalToMvPowerSeries' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.flat_polyLocalToMvPowerSeries

/-! ### The germs are faithfully flat over the local ring at the origin

`Oka/Analytification/Flatness.lean`. `coe_polyLocalToGerm` is guarded alongside the flatness
because it is what makes the two maps out of `ℂ[x]_{(x)}` into a scalar tower; without it the
descent has nothing to run in. -/

/--
info: 'ComplexAnalytic.polyLocalToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalToGerm

/--
info: 'ComplexAnalytic.coe_polyLocalToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coe_polyLocalToGerm

/--
info: 'ComplexAnalytic.flat_polyLocalToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.flat_polyLocalToGerm

/--
info: 'ComplexAnalytic.faithfullyFlat_polyLocalToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.faithfullyFlat_polyLocalToGerm

/-! ### Presentation-independence -/

/--
info: 'ComplexAnalytic.eval₂Hom_transported' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval₂Hom_transported

/--
info: 'ComplexAnalytic.analytificationMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap

/--
info: 'ComplexAnalytic.analytificationMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap_comp

/--
info: 'ComplexAnalytic.analytificationIsoOfPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationIsoOfPresHom

/-! ### The analytification as a functor -/

/--
info: 'ComplexAnalytic.analytificationFunctor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFunctor

/--
info: 'ComplexAnalytic.exists_presentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_presentation

/--
info: 'ComplexAnalytic.toFGAlgFullyFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toFGAlgFullyFaithful

/--
info: 'ComplexAnalytic.analytificationFGAlg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlg

/--
info: 'ComplexAnalytic.analytificationFGAlgCompIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgCompIso

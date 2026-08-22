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
`𝔸^ι` at the origin with its completion, the faithful flatness of the germs over it and the same
at an arbitrary point — where it becomes a statement about the stalk map itself — the
analytification as a functor on finitely generated `ℂ`-algebras, the stalk map of the
comparison morphism of a presented algebra, the naturality of the comparison morphism, the
faithful flatness of that stalk map, and the analytification of a sheaf.

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

/-! ### The same at an arbitrary point, and for the geometric stalk map

`Oka/Analytification/FlatnessAtAPoint.lean`. `polyLocalToGermAt_eq_comp` is guarded alongside the
two flatness statements because it is the *only* mathematical step between them and the results
at the origin — everything else in that file is transport — and
`LocalOkaRing.ofMvPolynomial_taylorAlgHom` because it is in turn the only step in it that is
about germs rather than about localisations. -/

/--
info: 'MvPolynomial.map_taylorEquiv_primeCompl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.map_taylorEquiv_primeCompl

/--
info: 'LocalOkaRing.ofMvPolynomial_taylorAlgHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.ofMvPolynomial_taylorAlgHom

/--
info: 'ComplexAnalytic.polyLocalToGermAt' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalToGermAt

/--
info: 'ComplexAnalytic.polyLocalToGermAt_eq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyLocalToGermAt_eq_comp

/--
info: 'ComplexAnalytic.faithfullyFlat_polyLocalToGermAt' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.faithfullyFlat_polyLocalToGermAt

/--
info: 'ComplexAnalytic.okaStalkEquiv_comp_stalkMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.okaStalkEquiv_comp_stalkMap

/--
info: 'ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec

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

/-! ### The stalk map of `X^an ⟶ Spec (ℂ[x] ⧸ I)`

`Oka/Analytification/PresentationStalk.lean`. -/

/--
info: 'ComplexAnalytic.quotientToGerm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.quotientToGerm

/--
info: 'ComplexAnalytic.toStalk_stalkMap_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toStalk_stalkMap_analytificationToSpec

/--
info: 'ComplexAnalytic.isUnit_quotientToGerm_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isUnit_quotientToGerm_iff

/--
info: 'ComplexAnalytic.stalkMap_analytificationToSpec_eq_lift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.stalkMap_analytificationToSpec_eq_lift

/--
info: 'ComplexAnalytic.algebraMapSubmonoid_primeCompl_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.algebraMapSubmonoid_primeCompl_eq

/--
info: 'ComplexAnalytic.analytificationStalkQuotEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationStalkQuotEquiv

/-! ### The comparison morphism is natural

`Oka/Analytification/Comparison.lean`. The component lemmas are guarded alongside the two natural
transformations because a transformation whose components nobody can compute is inert, which is
the same obligation `ComplexAnalytic.analytificationFGAlgObjIso` discharges above. -/

/--
info: 'ComplexAnalytic.analytificationToSpec_naturality' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpec_naturality

/--
info: 'ComplexAnalytic.analytificationToSpecNatTrans' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpecNatTrans

/--
info: 'ComplexAnalytic.specFunctor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specFunctor_eq

/--
info: 'ComplexAnalytic.analytificationFGAlgToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgToSpec

/--
info: 'ComplexAnalytic.analytificationFGAlgToSpec_app' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgToSpec_app

/-! ### The analytification of a sheaf

`Oka/Analytification/Sheaf.lean`, and the general pullback of `𝒪`-modules along a morphism of
locally ringed spaces it is built from. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModules' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModules

/--
info: 'ComplexAnalytic.analytificationSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheaf

/--
info: 'ComplexAnalytic.analytificationSheafAdj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheafAdj

/--
info: 'ComplexAnalytic.preservesColimits_analytificationSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.preservesColimits_analytificationSheaf

/--
info: 'ComplexAnalytic.analytificationSheafUnitToUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheafUnitToUnit

/--
info: 'ComplexAnalytic.analytificationFGAlgObjIso_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgObjIso_hom

/--
info: 'ComplexAnalytic.analytificationFGAlgToSpec_app_toFGAlg_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgToSpec_app_toFGAlg_obj

/-! ### The germ of a polynomial, and the flatness of the stalk map of `X^an ⟶ Spec (ℂ[x] ⧸ I)`

`Oka/Analytification/FlatnessAtAPoint.lean` and `Oka/Analytification/PresentationFlatness.lean`.
`ComplexAnalytic.injective_germOfMvPolynomial` is guarded alongside the flatness because it is
what the non-vacuity test rests on, and `ComplexAnalytic.stalkMap_analytificationToSpec_eq_comp`
because a flatness deduced through three identifications is only as good as the square that says
they commute. -/

/--
info: 'ComplexAnalytic.germOfMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.germOfMvPolynomial

/--
info: 'ComplexAnalytic.injective_germOfMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.injective_germOfMvPolynomial

/--
info: 'ComplexAnalytic.ker_stalkMap_analytificationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.ker_stalkMap_analytificationIncl

/--
info: 'ComplexAnalytic.germQuotEquivStalk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.germQuotEquivStalk

/--
info: 'ComplexAnalytic.germQuotEquivStalk_mk_germOfMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.germQuotEquivStalk_mk_germOfMvPolynomial

/--
info: 'ComplexAnalytic.stalkMap_analytificationToSpec_eq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.stalkMap_analytificationToSpec_eq_comp

/--
info: 'ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec

/--
info: 'ComplexAnalytic.flat_stalkMap_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.flat_stalkMap_analytificationToSpec

/-! ### GAGA's local half: the analytification of a sheaf is exact -/

/--
info: 'ComplexAnalytic.preservesFiniteLimits_analytificationSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.preservesFiniteLimits_analytificationSheaf


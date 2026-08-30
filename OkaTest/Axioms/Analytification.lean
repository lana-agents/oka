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
faithful flatness of that stalk map, the analytification of a sheaf, the identification of
the analytification of `A_f` with the non-vanishing locus of `f` and the same open on the `Spec`
side, the glue data of an affine cover with distinguished
overlaps together with the morphisms out of the space it glues to and the same glue data on the
`Spec` side, the image of the analytification in `ℂ^n`, and the family of
monic polynomials of a polynomial monic in the last variable, with the finiteness over `ℂ^n`
that it supplies.

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

/--
info: 'ComplexAnalytic.PresHom.ofRename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.PresHom.ofRename

/--
info: 'ComplexAnalytic.PresHom.ofRename_comp_ofRename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.PresHom.ofRename_comp_ofRename

/-! ### The analytification as a functor -/

/--
info: 'ComplexAnalytic.analytificationFunctor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFunctor

/--
info: 'ComplexAnalytic.Presentation.isoOfRename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Presentation.isoOfRename

/--
info: 'ComplexAnalytic.exists_presentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_presentation

/--
info: 'ComplexAnalytic.toFGAlg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toFGAlg

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

/--
info: 'ComplexAnalytic.analytificationFGAlgObjIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationFGAlgObjIso

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
info: 'ComplexAnalytic.analytificationToSpecNatTrans_app' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpecNatTrans_app

/--
info: 'ComplexAnalytic.specFunctor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specFunctor

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

/-! ### The analytification of `𝒪_X` is `𝒪_{X^an}` -/

/--
info: 'TopologicalSpace.Opens.final_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopologicalSpace.Opens.final_map

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_pullbackModulesUnitToUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_pullbackModulesUnitToUnit

/--
info: 'ComplexAnalytic.analytificationSheafUnitIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheafUnitIso

/--
info: 'ComplexAnalytic.analytificationSheafFreeIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationSheafFreeIso


/-! ### The analytification of a distinguished open -/

/--
info: 'ComplexAnalytic.AnalyticSpace.pullbackΓ_eval₂' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.pullbackΓ_eval₂

/--
info: 'ComplexAnalytic.localisationIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIso

/--
info: 'ComplexAnalytic.localisationIso_hom_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIso_hom_ofRestrict

/--
info: 'ComplexAnalytic.localisationIso_inv_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIso_inv_localisationProj

/--
info: 'ComplexAnalytic.eval_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_localisationProj

/--
info: 'ComplexAnalytic.base_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.base_localisationProj

/--
info: 'ComplexAnalytic.localisationOpen_ne_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_ne_top

/-! ### The analytification of a coherent sheaf is coherent

`Oka/Analytification/SheafCoherent.lean`, whose title this header now matches: it used to read
*the analytification of a finitely presented sheaf*, which was that file's title until the
coherent statement was added, and which under-described the last of the four guards below.

`ComplexAnalytic.AnalyticSpace.isCoherent_free` is the one of the four that lives elsewhere
(`Oka/AnalyticSpace/Coherent.lean`); it is Oka's theorem in every finite rank, and the other
three rest on it. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherent_free' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherent_free

/--
info: 'ComplexAnalytic.isCoherent_analytificationSheaf_cokernel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherent_analytificationSheaf_cokernel

/--
info: 'ComplexAnalytic.isCoherent_analytificationSheaf_cokernel_sectionsHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherent_analytificationSheaf_cokernel_sectionsHom

/--
info: 'ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent

/-! ### The distinguished open, through the functor -/

/--
info: 'ComplexAnalytic.rename_localisationIncl_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.rename_localisationIncl_mem

/--
info: 'ComplexAnalytic.localisationPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresHom

/--
info: 'ComplexAnalytic.analytificationMap_localisationPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap_localisationPresHom

/--
info: 'ComplexAnalytic.localisationIso_inv_analytificationMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationIso_inv_analytificationMap

/-! ### The projection is an open immersion -/

/--
info: 'ComplexAnalytic.isOpenImmersion_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_localisationProj

/--
info: 'ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_analytificationMap_localisationPresHom

/-! ### The same distinguished open on the `Spec` side

`Oka/Analytification/SpecDistinguishedOpen.lean`, the mirror of the two above. The triangle is
guarded beside the two open-immersion statements because it is the only thing either of them
uses, and the isomorphism is guarded because a triangle over an identification nobody can name
is inert.

The range and the isomorphism with the open subspace are under the same heading rather than one
of their own: they are the same distinguished open, and the open immersion is what makes both of
them statable. -/

/--
info: 'ComplexAnalytic.specLocalisationRingIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationRingIso

/--
info: 'ComplexAnalytic.localisationRingHom_comp_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationRingHom_comp_eq

/--
info: 'ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom

/--
info: 'ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_specFunctor_map_localisationHom

/--
info: 'ComplexAnalytic.specLocalisationOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationOpen

/--
info: 'ComplexAnalytic.range_base_specFunctor_map_localisationHom' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_specFunctor_map_localisationHom

/--
info: 'ComplexAnalytic.specLocalisationIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationIso

/--
info: 'ComplexAnalytic.specLocalisationIso_hom_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationIso_hom_ofRestrict

/--
info: 'ComplexAnalytic.specLocalisationIso_inv_specFunctor_map' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specLocalisationIso_inv_specFunctor_map

/-! ### The glue data of an affine cover with distinguished overlaps -/

/--
info: 'ComplexAnalytic.localisationOpen_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_mul

/--
info: 'ComplexAnalytic.range_base_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_localisationProj

/--
info: 'ComplexAnalytic.coverTransition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTransition

/--
info: 'ComplexAnalytic.coverTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTriple

/--
info: 'ComplexAnalytic.range_coverTransitionHom_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_coverTransitionHom_subset

/--
info: 'ComplexAnalytic.range_comp_coverTransitionHom_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_comp_coverTransitionHom_subset

/--
info: 'ComplexAnalytic.coverGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueData

/--
info: 'ComplexAnalytic.coverGlueData_U' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueData_U

/--
info: 'ComplexAnalytic.comapAlgMap_coverOverlapIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_coverOverlapIso

/--
info: 'ComplexAnalytic.comapAlgMap_coverGlueIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_coverGlueIso

/--
info: 'ComplexAnalytic.comapAlgMap_coverIncl_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_coverIncl_eq

/--
info: 'ComplexAnalytic.glueDataCLinear_coverGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDataCLinear_coverGlueData

/--
info: 'ComplexAnalytic.coverAnalytification_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytification_toLocallyRingedSpace

/--
info: 'ComplexAnalytic.isOpenImmersion_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_coverIota

/--
info: 'ComplexAnalytic.coverIota' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota

/--
info: 'ComplexAnalytic.coverAnalytificationOpenCover_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytificationOpenCover_obj

/--
info: 'ComplexAnalytic.coverAnalytificationOpenCover_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytificationOpenCover_map

/-! #### Morphisms out of `X^an`

`ComplexAnalytic.coverGlueMorphisms` and the four statements that make it usable, plus the round
trip. They belong with the block above rather than in one of their own: the cover is what
`ComplexAnalytic.AnalyticSpace.glueMorphisms` consumes and these are what supply its hypothesis,
so `ComplexAnalytic.coverAnalytificationOpenCover_obj` and `…_map` directly above are the same
line of statements one step earlier.
-/

/--
info: 'ComplexAnalytic.comm_coverGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_coverGlueData

/--
info: 'ComplexAnalytic.coverGlueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueMorphisms

/--
info: 'ComplexAnalytic.toLRSHom_coverGlueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_coverGlueMorphisms

/--
info: 'ComplexAnalytic.coverIota_comp_coverGlueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_comp_coverGlueMorphisms

/--
info: 'ComplexAnalytic.coverAnalytification_hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytification_hom_ext

/--
info: 'ComplexAnalytic.coverIncl_comp_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIncl_comp_coverIota

/--
info: 'ComplexAnalytic.coverGlueMorphisms_coverIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueMorphisms_coverIota

/-! ### The glue data of the members' `Spec`s

`Oka/Analytification/SpecAffineCover.lean`, the mirror of the block above with
`ComplexAnalytic.specFunctor` in place of the analytification. It is a heading of its own rather
than part of that block because the two constructions share an *input* and nothing else: neither
file's declarations appear in the other's statements — and that is still true now that the file
which relates them exists. It is `Oka/Analytification/CoverComparison.lean`, guarded below under a
heading of its own: it names declarations from both of these blocks, neither of these blocks names
anything of the other's, and so it takes a third heading rather than pulling either of these two
under the other.

**This paragraph has now been wrong twice, in the two ways this file goes wrong.** It read "the
file that will relate them … does not exist yet" until that file arrived, which is an absence a
heading was justified by and the next branch retired; and its replacement said that file was "the
last block below", which was a *position* and was false on the day it was written. The heading is
named and not pointed at for that reason, and the paragraph under that heading says the same thing
from the other side.

`ComplexAnalytic.range_specTransitionHom_subset` and its composite are guarded because
`ComplexAnalytic.specTriple` consumes the second of them: it supplies the `D(f_ji)` half of
`AlgebraicGeometry.LocallyRingedSpace.liftRestrict`'s obligation so that `hrange` does not have to
ask for it. **They were guarded before anything consumed them** — as the evidence for the file's
claim that half of that hypothesis is free — and the analytic mirrors added alongside them in the
block above stand in the same relation to `ComplexAnalytic.coverTriple`.
-/

/--
info: 'ComplexAnalytic.specOverlapIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specOverlapIso

/--
info: 'ComplexAnalytic.specTransition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specTransition

/--
info: 'ComplexAnalytic.specGlueIso_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlueIso_symm

/--
info: 'ComplexAnalytic.range_specTransitionHom_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_specTransitionHom_subset

/--
info: 'ComplexAnalytic.range_comp_specTransitionHom_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_comp_specTransitionHom_subset

/--
info: 'ComplexAnalytic.specTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specTriple

/--
info: 'ComplexAnalytic.specTriple_fac' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specTriple_fac

/--
info: 'ComplexAnalytic.specGlueData'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlueData'

/--
info: 'ComplexAnalytic.specGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlueData

/--
info: 'ComplexAnalytic.specGlueData_U' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlueData_U

/--
info: 'ComplexAnalytic.specGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGlued

/--
info: 'ComplexAnalytic.specIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specIota

/--
info: 'ComplexAnalytic.isOpenImmersion_specIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isOpenImmersion_specIota

/--
info: 'ComplexAnalytic.specIncl_comp_specIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specIncl_comp_specIota

/-! ### A morphism of covered schemes analytifies

The two definitions and six results of `Oka/Analytification/CoverFunctoriality.lean`, which is the
morphism *between* two gluings of the kind `### The glue data of an affine cover with distinguished
overlaps` builds. A heading of its own rather than a `####` under that one, because its subject is
a morphism of two covers where everything there is one cover; under this file's topic heading at
all, because `ComplexAnalytic.coverGlueMorphisms` is what it is built from and
`OkaTest/Axioms.lean`'s routing rule puts a file's guards under the heading its topic belongs to.

**Named by heading and not by position**, which is not a stylistic preference: this block and the
`Spec`-side glue-data block above it were written against the same anchor by two branches that did
not know about each other, so whichever landed second would have carried a false "the block above"
had it pointed rather than named. That block does point, and it is still right — it sits directly
under the block it names, and nothing may be inserted between them without repairing its first
sentence.
-/

/--
info: 'ComplexAnalytic.coverMapPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMapPart

/--
info: 'ComplexAnalytic.coverMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap

/--
info: 'ComplexAnalytic.coverIota_comp_coverMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_comp_coverMap

/--
info: 'ComplexAnalytic.coverMap_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_unique

/--
info: 'ComplexAnalytic.comm_coverMapPart_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_coverMapPart_id

/--
info: 'ComplexAnalytic.coverMap_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_id

/--
info: 'ComplexAnalytic.comm_coverMapPart_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_coverMapPart_comp

/--
info: 'ComplexAnalytic.coverMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_comp

/-! ### The comparison morphism `X^an ⟶ X`

The three definitions and five results of `Oka/Analytification/CoverComparison.lean`, the
morphism from the gluing `### The glue data of an affine cover with distinguished overlaps`
builds to the gluing `### The glue data of the members' `Spec`s` builds. It is a heading of its
own rather than a `####` under either because it is about neither cover on its own: its input is
one datum and its content is that the affine comparison morphism is natural enough to descend to
it. Placed after both blocks it consumes, and **named by heading rather than by position**, which
is what the blocks above cannot be revised into cheaply: `"the block above"` occurs three times up
there, twice in the `Spec` block and once in `#### Morphisms out of \`X^an\``, and **all three are
true** — each of the two blocks really does sit under the one it means. That is the hazard, not a
contradiction: a pointer is true only relative to a position, so every one of them constrains what
may be inserted where, and a name constrains nothing.
-/

/--
info: 'ComplexAnalytic.toLRSHom_localisationProj_comp_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_localisationProj_comp_analytificationToSpec

/--
info: 'ComplexAnalytic.coverOverlapIso_hom_coverIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapIso_hom_coverIncl

/--
info: 'ComplexAnalytic.comparisonPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comparisonPart

/--
info: 'ComplexAnalytic.coverIncl_comp_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIncl_comp_analytificationToSpec

/--
info: 'ComplexAnalytic.comparisonPart_comp_specTransition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comparisonPart_comp_specTransition

/--
info: 'ComplexAnalytic.comparisonPartIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comparisonPartIota

/--
info: 'ComplexAnalytic.comm_comparisonPartIota' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_comparisonPartIota

/--
info: 'ComplexAnalytic.analytificationToSpecGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpecGlued

/--
info: 'ComplexAnalytic.toLRSHom_coverIota_comp_analytificationToSpecGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_coverIota_comp_analytificationToSpecGlued

/--
info: 'ComplexAnalytic.analytificationToSpecGlued_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationToSpecGlued_unique

/-! ### The two-level index category of a glue data

The five advertised results of `Oka/Analytification/GlueShape.lean`, which arrived under `Oka/`
when `ComplexAnalytic.coverAnalytification` gave the shape a consumer. They sit here rather than
in a file of their own because the module is `Oka.Analytification.GlueShape` and
`OkaTest/Axioms.lean`'s table routes `Oka/Analytification/` here — the same row that carries
`ComplexAnalytic.coverGlueData` directly above, which is what the shape's diagram produces.

The first says the shape has no morphisms a glue-data diagram does not account for; the second
that `hsymm` is a consequence of its one law; the third that `hrange` is **not** a consequence of
the diagram, which is the file's negative result; the last two that neither triple-overlap
hypothesis has content below three members.
-/

/--
info: 'ComplexAnalytic.GlueShape.lift_uniq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.lift_uniq

/--
info: 'ComplexAnalytic.GlueShape.hsymm_of_hglue' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.hsymm_of_hglue

/--
info: 'ComplexAnalytic.GlueShape.not_ctHRange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.not_ctHRange

/--
info: 'ComplexAnalytic.GlueShape.hRange_of_no_three' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.hRange_of_no_three

/--
info: 'ComplexAnalytic.GlueShape.hCocycle_of_no_three' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.GlueShape.hCocycle_of_no_three

/-! ### A standard étale algebra over a presented `ℂ`-algebra is presented

The five advertised results of `Oka/Analytification/StandardEtale.lean`. The two operations —
adjoin a variable, add a relation — and the three forms of the identification with
`StandardEtalePair.Ring`: the one that names the quotient, the one that names `P.Ring`, and the
one that quantifies the polynomial lifts of `f` and `g` away.
-/

/--
info: 'ComplexAnalytic.presentedAlgebraSnocEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentedAlgebraSnocEquiv

/--
info: 'ComplexAnalytic.polyPresentedAlgebraEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyPresentedAlgebraEquiv

/--
info: 'ComplexAnalytic.etalePresentedAlgebraEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.etalePresentedAlgebraEquiv

/--
info: 'ComplexAnalytic.etalePresentedAlgebraEquivRing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.etalePresentedAlgebraEquivRing

/--
info: 'ComplexAnalytic.exists_presentation_standardEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_presentation_standardEtale

/-! ### The étale presentation analytifies to a distinguished open

The three advertised results of `Oka/Analytification/StandardEtaleAnalytification.lean`: the ideal
identity that lets the two presentations be compared at all, the isomorphism read against the open
immersion, and the statement that it is an isomorphism **over the base**. The last is the one that
makes the first two say something about the projection of the étale cover rather than about two
spaces that happen to be isomorphic.
-/

/--
info: 'ComplexAnalytic.presentationIdeal_etalePresentation_eq_localisation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.presentationIdeal_etalePresentation_eq_localisation

/--
info: 'ComplexAnalytic.etaleAnalytificationIso_hom_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.etaleAnalytificationIso_hom_ofRestrict

/--
info: 'ComplexAnalytic.etaleAnalytificationIso_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.etaleAnalytificationIso_hom_comp

/-! ### The image of the analytification in `ℂ^n` -/

/--
info: 'ComplexAnalytic.isClosedEmbedding_base_analytificationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isClosedEmbedding_base_analytificationIncl

/--
info: 'ComplexAnalytic.range_base_analytificationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_analytificationIncl

/-! ### The monic-hypersurface family of a polynomial -/

/--
info: 'ComplexAnalytic.lastVarPolyEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.lastVarPolyEquiv

/--
info: 'ComplexAnalytic.eval_eq_eval_lastVarPolyEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_eq_eval_lastVarPolyEquiv

/--
info: 'ComplexAnalytic.polyFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyFamily

/--
info: 'ComplexAnalytic.monic_polyFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.monic_polyFamily

/--
info: 'ComplexAnalytic.natDegree_polyFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.natDegree_polyFamily

/--
info: 'ComplexAnalytic.continuous_coeff_polyFamily' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.continuous_coeff_polyFamily

/--
info: 'ComplexAnalytic.lastVarSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.lastVarSection

/--
info: 'ComplexAnalytic.evalHom_lastVarSection' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.evalHom_lastVarSection

/--
info: 'ComplexAnalytic.isFinite_comp_proj_of_monic' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_comp_proj_of_monic

/--
info: 'ComplexAnalytic.isFinite_analytification_comp_proj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytification_comp_proj

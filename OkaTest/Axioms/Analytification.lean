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
that it supplies, the glue of a refined overlap that meets two different members of the
original cover with the symmetry law it satisfies, and the square saying that the refined
transition lies over the original cover's own transition.

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

/-! ### The Taylor coefficients of a shifted polynomial, and of a germ

`Oka/Algebra/MvPolynomial/Taylor.lean`, `Oka/Algebra/MvPolynomial/PDeriv.lean` and
`Oka/Polynomial/Germ.lean`. The two mirror-tree statements read the constant and the linear
coefficient of `p(x + z)` — the second as a partial derivative — and the two after them are what
carries that to a germ: at the origin the germ of a polynomial *is* the polynomial, and so the
linear coefficient of the germ at any point is a partial derivative there. They are guarded under
this heading rather than in `OkaTest/Axioms/RingTheory.lean` for the reason
`MvPolynomial.map_taylorEquiv_primeCompl` above is: their consumer is the germ of a polynomial,
which is what this file's routing row covers. -/

/--
info: 'MvPolynomial.constantCoeff_taylorAlgHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.constantCoeff_taylorAlgHom

/--
info: 'MvPolynomial.coeff_single_one_taylorAlgHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.coeff_single_one_taylorAlgHom

/--
info: 'LocalOkaRing.ofMvPolynomial_zero_X' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.ofMvPolynomial_zero_X

/--
info: 'LocalOkaRing.coe_ofMvPolynomial_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.coe_ofMvPolynomial_zero

/--
info: 'LocalOkaRing.coeff_single_one_ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.coeff_single_one_ofMvPolynomial

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
info: 'ComplexAnalytic.Presentation.algEquivOfIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Presentation.algEquivOfIso

/--
info: 'ComplexAnalytic.Presentation.isoOfAlgEquiv_algEquivOfIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Presentation.isoOfAlgEquiv_algEquivOfIso

/--
info: 'ComplexAnalytic.Presentation.algEquivOfIso_isoOfAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Presentation.algEquivOfIso_isoOfAlgEquiv

/--
info: 'ComplexAnalytic.exists_presentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_presentation

/--
info: 'ComplexAnalytic.finiteType_presentationAlg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.finiteType_presentationAlg

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

/-! ### Two polynomials cutting out the same distinguished open, up to a unit

The four statements `Oka/Analytification/LocalisationIndependence.lean` gained for the
cross-member overlap of a refinement: the isomorphism at a **unit multiple** and its triangle,
that the inverted polynomial is a unit upstairs, and that every polynomial of a localisation is a
unit multiple of a renamed one.

**That file's other four declarations are unguarded and this heading does not retrofit them.**
They are unguarded because the file has no `## Main results` heading — its list of statements
sits under the title — so `scripts/guard_coverage.py` reads nothing from it in either direction,
and the four below land in *guarded and advertised nowhere* rather than in the overlap. Guarding
what a branch adds is this project's practice; guarding four declarations a branch does not touch
is another branch's business. -/

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfUnitMul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfUnitMul

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp

/--
info: 'ComplexAnalytic.isUnit_mk_rename_localisationIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isUnit_mk_rename_localisationIncl

/--
info: 'ComplexAnalytic.exists_mk_rename_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_mk_rename_eq

/-! ### The same distinguished open of two *different* members

The two statements `Oka/Analytification/LocalisationIndependence.lean` gained for the step after
the block above: an isomorphism of two presented algebras carrying one cutting polynomial to the
other identifies the two localisations, and the identification is one over that isomorphism.
Everything in the block above keeps the base fixed and varies the polynomial; these vary the base.

The same sentence as that heading applies to the coverage figures: that file still has no
`## Main results` heading, so both land in *guarded and advertised nowhere* rather than in the
overlap, and the four declarations of the block above stay guarded while the file's original
eight stay unguarded. -/

/--
info: 'ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv

/--
info: 'ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentedAlgebraEquivOfAlgEquiv_localisationRingHom

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfAlgEquiv

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfAlgEquiv_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfAlgEquiv_hom_comp

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

/-! ### The glue data of an affine cover with distinguished overlaps

The `ComplexAnalytic.localisationOpen` lemmas are guarded under this heading rather than under
`### The analytification of a distinguished open` because this heading is what they are for.
`ComplexAnalytic.localisationOpen_mul` is the triple overlap;
`ComplexAnalytic.localisationOpen_rename` is the overlap of a refined member read upstairs; and
`ComplexAnalytic.exists_localisationOpen_eq_rename`, the converse of that one for every
distinguished open at once, is what says an overlap cut out of a *localisation* still needs only
one polynomial — the arity a cover datum asks for. Its three auxiliaries and its `Opens.map` form
are guarded beside it.

The four after those are `Oka/Analytification/DistinguishedOpenPullback.lean`, and they belong
under this heading for the same reason: a distinguished open pulls back along
`ComplexAnalytic.analytificationMap` to a distinguished open, which is what says the overlap an
overlap is *transported* to is still one of the opens a cover datum can name.
`ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj` is that composed with
`ComplexAnalytic.exists_localisationOpen_eq_comap`, and is the pair's conclusion.
-/

/--
info: 'ComplexAnalytic.localisationOpen_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_mul

/--
info: 'ComplexAnalytic.localisationOpen_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_rename

/--
info: 'ComplexAnalytic.eq_localisationVar_or_exists_localisationIncl' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eq_localisationVar_or_exists_localisationIncl

/--
info: 'ComplexAnalytic.exists_pow_mul_eq_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_pow_mul_eq_rename

/--
info: 'ComplexAnalytic.eval_rename_localisationIncl_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_rename_localisationIncl_ne_zero

/--
info: 'ComplexAnalytic.exists_localisationOpen_eq_rename' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_localisationOpen_eq_rename

/--
info: 'ComplexAnalytic.exists_localisationOpen_eq_comap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_localisationOpen_eq_comap

/--
info: 'ComplexAnalytic.pullbackΓ_analytificationMap_polyToGlobal' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.pullbackΓ_analytificationMap_polyToGlobal

/--
info: 'ComplexAnalytic.localisationOpen_eq_comap_analytificationMap' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationOpen_eq_comap_analytificationMap

/--
info: 'ComplexAnalytic.exists_localisationOpen_eq_comap_analytificationMap' depends
  on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_localisationOpen_eq_comap_analytificationMap

/--
info: 'ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_comap_analytificationMap_eq_comap_localisationProj

/--
info: 'ComplexAnalytic.range_base_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_localisationProj

/--
info: 'ComplexAnalytic.coverOverlapIso_hom_coverIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapIso_hom_coverIncl

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

/--
info: 'ComplexAnalytic.specGluedOpenCover' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGluedOpenCover

/--
info: 'ComplexAnalytic.specGluedOpenCover_obj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGluedOpenCover_obj

/--
info: 'ComplexAnalytic.specGluedOpenCover_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specGluedOpenCover_map

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

/-! ### Two cover data with isomorphic members give the same `X^an`

The three definitions and four results of `Oka/Analytification/CoverIndependence.lean`, the first
two instalments of taxis #1107. It is a heading of its own rather than a `####` under
`### A morphism of covered schemes analytifies`, whose `ComplexAnalytic.coverMap` it is built
from, because its subject is two data for *one* gluing where that block's is a morphism between
two gluings — and it is placed after the blocks it consumes for the same reason that one gives,
**named by heading and not by position**.

**The same-index pair is guarded on its own account even though it is an instance of the
reindexed pair**, which that file measures and says: `ComplexAnalytic.coverMap_hom_inv` is
`ComplexAnalytic.coverMap_reindex_hom_inv` at `Equiv.refl` with no coercion at all. A guard on an
advertised name is a statement about that name, and the census
`scripts/guard_coverage.py` reports counts advertised names rather than distinct facts, so
dropping either pair here would open a gap without removing a claim.
-/

/--
info: 'ComplexAnalytic.coverMap_hom_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_hom_inv

/--
info: 'ComplexAnalytic.coverMap_inv_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_inv_hom

/--
info: 'ComplexAnalytic.coverAnalytificationIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytificationIso

/--
info: 'ComplexAnalytic.coverReindexInv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverReindexInv

/--
info: 'ComplexAnalytic.coverMap_reindex_hom_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_reindex_hom_inv

/--
info: 'ComplexAnalytic.coverMap_reindex_inv_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverMap_reindex_inv_hom

/--
info: 'ComplexAnalytic.coverAnalytificationReindexIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytificationReindexIso

/-! ### A morphism of covered schemes on the `Spec` side

The two definitions and seven results of `Oka/Analytification/SpecFunctoriality.lean`, which is to
`### The glue data of the members' `Spec`s` what `### A morphism of covered schemes analytifies` is
to `### The glue data of an affine cover with distinguished overlaps`. A heading of its own for the
reason that block gives about itself: its subject is a morphism of two covers where the glue-data
blocks are each about one.

`ComplexAnalytic.comm_specGlueData` is guarded here and not with the `Spec`-side glue data,
because that is where it is declared — its analytic mirror sits under
`### Morphisms out of `X^an``, which is a `####` inside the analytic glue-data block, and the
`Spec` side has no such section: nothing needed a family out of the members until this file.
-/

/--
info: 'ComplexAnalytic.comm_specGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_specGlueData

/--
info: 'ComplexAnalytic.specMapPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMapPart

/--
info: 'ComplexAnalytic.specMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMap

/--
info: 'ComplexAnalytic.specIota_comp_specMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specIota_comp_specMap

/--
info: 'ComplexAnalytic.specMap_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMap_unique

/--
info: 'ComplexAnalytic.comm_specMapPart_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_specMapPart_id

/--
info: 'ComplexAnalytic.specMap_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMap_id

/--
info: 'ComplexAnalytic.comm_specMapPart_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comm_specMapPart_comp

/--
info: 'ComplexAnalytic.specMap_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.specMap_comp

/-! ### The comparison morphism commutes with a morphism of covered schemes

The two results of `Oka/Analytification/ComparisonSquare.lean`, the only statement in the tree
that needs `### The comparison morphism `X^an ⟶ X``, `### A morphism of covered schemes
analytifies` and `### A morphism of covered schemes on the `Spec` side` at once — which is why it
is a fourth heading rather than an addition to any of the three, and why it is placed after all of
them.

`ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec` is the naturality square at the member
morphism, and it is guarded although the file states it only to use it: it is the whole content of
the square below, so a proof of the square whose axioms differed from its would mean the square
was proved some other way.
-/

/--
info: 'ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_map_comp_analytificationToSpec

/--
info: 'ComplexAnalytic.toLRSHom_coverMap_comp_analytificationToSpecGlued' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.toLRSHom_coverMap_comp_analytificationToSpecGlued

/-! ### The two-level index category of a glue data

The five advertised results of `Oka/Analytification/GlueShape.lean`, which arrived under `Oka/`
when `ComplexAnalytic.coverAnalytification` gave the shape a consumer. They sit here rather than
in a file of their own because the module is `Oka.Analytification.GlueShape` and
`OkaTest/Axioms.lean`'s table routes `Oka/Analytification/` here — the same row that carries
`ComplexAnalytic.coverGlueData`, under `### The glue data of an affine cover with distinguished
overlaps`, which is what the shape's diagram produces. **That clause read "directly above" until
2026-08-30**, by which time several blocks had been appended between the two — and it is named
rather than pointed at for the reason `### The comparison morphism `X^an ⟶ X`` and
`### Two presentations of each member give the same `X^an`` both give. **The count of blocks
between them is deliberately not stated**: it was four when this was repaired and more by the end
of the same afternoon, which is the whole argument for naming.

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

The six advertised results of `Oka/Analytification/StandardEtale.lean`. The two operations —
adjoin a variable, add a relation — the three forms of the identification with
`StandardEtalePair.Ring` (the one that names the quotient, the one that names `P.Ring`, and the
one that quantifies the polynomial lifts of `f` and `g` away), and the bridge from
`Polynomial.derivative` to `MvPolynomial.pderiv` that a consumer of `StandardEtalePair.cond` has
to come through.

**The bridge is one declaration and it needed no helpers**, which is worth recording because the
obvious proof needs two: a crossing lemma for `MvPolynomial.optionEquivLeft` that Mathlib has
only for `MvPolynomial.sumRingEquiv`, and a reindexing lemma for
`ComplexAnalytic.localisationVarEquiv`. Both are avoided by inducting on the polynomial instead
of opening the equivalence up, which also plants no equation lemma; the proof's own docstring
has the measurement.
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

/--
info: 'ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv

/-! ### `StandardEtalePair.cond` at a point

The two results of `Oka/Analytification/StandardEtale.lean` that read that field: the equation
moved from `A[X]` down to the polynomial ring the presentation cuts with, and the same equation
evaluated at a point of the hypersurface off the zero locus of `G`. The third of the chain is in
the guard block below, since it is declared one file on.
-/

/--
info: 'ComplexAnalytic.exists_mk_pderiv_mul_add_eq_mk_pow' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_mk_pderiv_mul_add_eq_mk_pow

/--
info: 'ComplexAnalytic.eval_pderiv_ne_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_pderiv_ne_zero

/-! ### The étale presentation analytifies to a distinguished open

The advertised results of `Oka/Analytification/StandardEtaleAnalytification.lean`: the ideal
identity that lets the two presentations be compared at all, the isomorphism read against the open
immersion, the statement that it is an isomorphism **over the base**, and — last, and about the
étale hypothesis rather than about the comparison — `StandardEtalePair.cond` read at a point of
the hypersurface's analytification. The third is the one that makes the first two say something
about the projection of the étale cover rather than about two spaces that happen to be isomorphic.
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

/--
info: 'ComplexAnalytic.eval_pderiv_ne_zero_of_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_pderiv_ne_zero_of_mem

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

/-! ### Refining one member of a cover by distinguished opens

`Oka/Analytification/CoverRefinement.lean`. The refined members, the polynomials cutting their
overlaps out, the glue isomorphism built from `ComplexAnalytic.localisationPresentationIsoMul`,
the two laws that are algebraic, **the two that are geometric**, and the space the refined datum
glues to with its morphism down to the fixed member. The geometric pair was absent here until
`ComplexAnalytic.localisationOpen_rename` — guarded under
`### The glue data of an affine cover with distinguished overlaps` above — gave them the one
statement they were waiting for.

`ComplexAnalytic.not_isIso_refineToBase` is guarded like the rest and is a **negative**: the
morphism is not an isomorphism, at an empty family. A guard on it says only that its proof uses
no axiom beyond the three, which is worth as much here as anywhere — the theorem is what says
this construction produces a morphism and not an identification.

`ComplexAnalytic.refineObj`, `ComplexAnalytic.refinePoly` and `ComplexAnalytic.refineMul` are
`abbrev`s and carry no guard of their own: an `abbrev` is definitionally its body, so a guard on
one would assert the axioms of `ComplexAnalytic.localisationPresentation`, which is guarded where
it is defined.
-/

/--
info: 'ComplexAnalytic.refineMulIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineMulIso

/--
info: 'ComplexAnalytic.refineMul_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineMul_comm

/--
info: 'ComplexAnalytic.refineGlue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue

/--
info: 'ComplexAnalytic.eqToIso_symm'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eqToIso_symm'

/--
info: 'ComplexAnalytic.refineGlue_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue_symm

/--
info: 'ComplexAnalytic.eqToHom_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eqToHom_localisationHom

/--
info: 'ComplexAnalytic.refineGlue_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue_comp

/--
info: 'ComplexAnalytic.refineGlue_analytification_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue_analytification_comp

/--
info: 'ComplexAnalytic.refineTransitionHom_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineTransitionHom_localisationProj

/--
info: 'ComplexAnalytic.refineTripleIncl_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineTripleIncl_localisationProj

/--
info: 'ComplexAnalytic.refineHrange' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineHrange

/--
info: 'ComplexAnalytic.refineTriple_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineTriple_localisationProj

/--
info: 'ComplexAnalytic.refineHcocycle' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineHcocycle

/--
info: 'ComplexAnalytic.refineAnalytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineAnalytification

/--
info: 'ComplexAnalytic.refineToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineToBase

/--
info: 'ComplexAnalytic.coverIota_comp_refineToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverIota_comp_refineToBase

/--
info: 'ComplexAnalytic.isEmpty_refineAnalytification' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isEmpty_refineAnalytification

/--
info: 'ComplexAnalytic.not_isIso_refineToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.not_isIso_refineToBase

/-! ### The glue of a refined overlap that meets two different members

`Oka/Analytification/CrossMemberGlue.lean`. The re-association of a double localisation over
either of its two factors, the transport across an isomorphism of the bases with a unit
correcting the cutting polynomial, and the cross-member glue those two compose to, each with its
coherence triangle. `ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq` is the
`rfl` saying the same-member glue guarded above is an instance of the first of them.

The two triangles are what carry the content: an isomorphism of the right type between two
descriptions of an overlap says nothing until it is recorded as a morphism over the thing both
descriptions lie over, which here is the original cover's own overlap and not either member.
-/

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfMulEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfMulEq

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfMulEq_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfMulEq_hom_comp

/--
info: 'ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineGlue_eq_localisationPresentationIsoOfMulEq

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul

/--
info: 'ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.localisationPresentationIsoOfAlgEquivUnitMul_hom_comp

/--
info: 'ComplexAnalytic.refineCrossProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineCrossProj

/--
info: 'ComplexAnalytic.refineCrossProj_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineCrossProj_localisationHom

/--
info: 'ComplexAnalytic.refineCrossGlue' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineCrossGlue

/--
info: 'ComplexAnalytic.refineCrossGlue_hom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineCrossGlue_hom_comp

/-! ### The `poly` field of a refined cover datum

`Oka/Analytification/CrossMemberDatum.lean`. The refined member for a general `σ`, the datum's
`poly` with its diagonal normalised, the extra factor carrying the transport, and the field the
two multiply to — with the two cases read back off it and the constant-`σ` reductions to
`Oka/Analytification/CoverRefinement.lean`'s member and polynomial.

They are guarded together and after the glue above because the point of the file is which of the
two the case split lands in: `ComplexAnalytic.refineDatumPoly`'s *type* carries neither a `dite`
nor a `▸`, and `ComplexAnalytic.refineDatumFactor`'s carries the `▸` between two values of one
type. The pair `ComplexAnalytic.refineDatumPoly_of_eq` and `ComplexAnalytic.refineDatumPoly_of_ne`
is what makes that a relocation and not a loss.
-/

/--
info: 'ComplexAnalytic.refineDatumObj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumObj

/--
info: 'ComplexAnalytic.refineDatumObj_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumObj_const

/--
info: 'ComplexAnalytic.polyDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyDiagOne

/--
info: 'ComplexAnalytic.polyDiagOne_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyDiagOne_of_eq

/--
info: 'ComplexAnalytic.polyDiagOne_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.polyDiagOne_of_ne

/--
info: 'ComplexAnalytic.refineDatumFactor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumFactor

/--
info: 'ComplexAnalytic.refineDatumPoly' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPoly

/--
info: 'ComplexAnalytic.refineDatumPoly_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPoly_of_eq

/--
info: 'ComplexAnalytic.refineDatumPoly_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPoly_of_ne

/--
info: 'ComplexAnalytic.refineDatumPoly_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumPoly_const

/--
info: 'ComplexAnalytic.coverOverlap_refineDatumPoly_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlap_refineDatumPoly_const

/-! ### The `glue` of a cross-member refined datum where the two members are equal

`Oka/Analytification/CrossMemberDatumGlue.lean`. The refined overlap with its cutting polynomial
abstracted, the swap of two refining polynomials over one member, that swap transported across an
equality of members, and the datum's own `glue` on the branch where the two members are equal —
each with its symmetry and its coherence triangle, plus the analytified triangle and the
constant-`σ` reduction.

They are guarded together and after the `poly` field because the point of the file is the
transport: `ComplexAnalytic.refineSwapGlueOfEq` is the one declaration whose two sides sit over
two different objects of `ComplexAnalytic.Presentation`, and every statement above it is over one.
`ComplexAnalytic.refineDatumCrossAlgEquiv` is guarded here and is what the unequal branch, in the
section at the end of this file, feeds to `Oka/Analytification/CrossMemberGlue.lean`'s glue: it is
the original datum's own glue and not a missing construction.
`ComplexAnalytic.refineSwapGlue_eq` and `ComplexAnalytic.refineDatumGlueEq_eq` are guarded beside
the definitions they unfold, which is where a reader looking for a missing guard would expect
them.
-/

/--
info: 'ComplexAnalytic.refineDatumOverlap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumOverlap

/--
info: 'ComplexAnalytic.coverOverlap_refineDatumObj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlap_refineDatumObj

/--
info: 'ComplexAnalytic.refineSwapGlue' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlue

/--
info: 'ComplexAnalytic.refineSwapMul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapMul

/--
info: 'ComplexAnalytic.refineSwapGlue_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlue_eq

/--
info: 'ComplexAnalytic.refineSwapGlue_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlue_symm

/--
info: 'ComplexAnalytic.refineSwapGlue_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlue_comp

/--
info: 'ComplexAnalytic.refineSwapGlueOfEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlueOfEq

/--
info: 'ComplexAnalytic.refineSwapGlueOfEq_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlueOfEq_symm

/--
info: 'ComplexAnalytic.refineSwapGlueOfEq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineSwapGlueOfEq_comp

/--
info: 'ComplexAnalytic.refineDatumGlueEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq

/--
info: 'ComplexAnalytic.refineDatumGlueEq_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_eq

/--
info: 'ComplexAnalytic.refineDatumGlueEq_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_symm

/--
info: 'ComplexAnalytic.refineDatumGlueEq_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_comp

/--
info: 'ComplexAnalytic.refineDatumGlueEq_analytification_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_analytification_comp

/--
info: 'ComplexAnalytic.refineDatumGlueEq_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueEq_const

/--
info: 'ComplexAnalytic.refineDatumCrossAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossAlgEquiv

/-! ### The diagonal of a cover datum is unread

`Oka/Analytification/DiagonalIndependence.lean`. The transports that say each piece of
`Oka/Analytification/AffineCover.lean`'s glue datum reads `poly` only at the pair it is indexed
by, the two geometric hypotheses transporting because they are stated at distinct indices, the
glue datum and the glued analytic space depending on nothing at the diagonal, and the
diagonal-normalised datum of `Oka/Analytification/CrossMemberDatum.lean` as the instance.

They are guarded together and after `ComplexAnalytic.refineDatumPoly` above because the
normalisation is what that declaration uses and this is the statement it left open.
`ComplexAnalytic.glueDiagOne` is the only definition among them; everything else is a transport,
and each is `Classical.choice` only through the `HEq` machinery and the `Classical.dec` inside
`ComplexAnalytic.polyDiagOne`.
-/

/--
info: 'ComplexAnalytic.coverOverlap_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlap_congr

/--
info: 'ComplexAnalytic.coverOverlapSpace_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapSpace_congr

/--
info: 'ComplexAnalytic.coverOpen_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOpen_congr

/--
info: 'ComplexAnalytic.coverPart_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverPart_congr

/--
info: 'ComplexAnalytic.coverTriplePart_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverTriplePart_congr

/--
info: 'ComplexAnalytic.heq_coverIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverIncl

/--
info: 'ComplexAnalytic.heq_coverOverlapIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverOverlapIso

/--
info: 'ComplexAnalytic.heq_coverTripleIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverTripleIncl

/--
info: 'ComplexAnalytic.heq_coverGlueIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverGlueIso

/--
info: 'ComplexAnalytic.heq_coverTransition' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverTransition

/--
info: 'ComplexAnalytic.heq_coverTransitionHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverTransitionHom

/--
info: 'ComplexAnalytic.heq_coverTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_coverTriple

/--
info: 'ComplexAnalytic.hrange_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hrange_congr

/--
info: 'ComplexAnalytic.hcocycle_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hcocycle_congr

/--
info: 'ComplexAnalytic.coverGlueData'_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueData'_congr

/--
info: 'ComplexAnalytic.coverGlueData_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverGlueData_congr

/--
info: 'ComplexAnalytic.coverAnalytification_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytification_congr

/--
info: 'ComplexAnalytic.glueDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDiagOne

/--
info: 'ComplexAnalytic.heq_glueDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.heq_glueDiagOne

/--
info: 'ComplexAnalytic.glueDiagOne_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.glueDiagOne_of_eq

/--
info: 'ComplexAnalytic.hsymm_glueDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hsymm_glueDiagOne

/--
info: 'ComplexAnalytic.coverAnalytification_polyDiagOne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverAnalytification_polyDiagOne

/-! ### Finiteness over a presented base

`Oka/Analytification/HypersurfaceFinite.lean`. The coordinates of the projection `ℂ^(n+1) ⟶ ℂ^n`,
the factorisation of the analytified structure map `A ⟶ A[X] ⧸ (F)` through the ambient `ℂ^(n+1)`,
and the finiteness that cancelling `A^an ↪ ℂ^n` against it gives. They are guarded here rather
than in `OkaTest/Axioms/Morphisms.lean`, where the projection's own finiteness lives, because the
file that declares them is under `Oka/Analytification/`; the theorem they generalise,
`ComplexAnalytic.isFinite_comp_proj_of_range_subset`, is guarded there beside
`ComplexAnalytic.isFinite_comp_proj_of_range_eq`.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.coordPullback_proj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.coordPullback_proj

/--
info: 'ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom


/-! ### The unequal branch of that `glue`, and the field the two branches assemble into

`Oka/Analytification/CrossMemberDatumGlue.lean`. The two equations a caller's choice of `r` and
`u` has to satisfy, the cross-member glue conjugated onto the datum's own overlaps, the projection
of a cross-member refined overlap to the original overlap, the coherence triangle over that
projection, and the `glue` field the two branches assemble into with its two readers and its
constant-`σ` reduction.

They are guarded here rather than beside the equal branch above because the file's section split
is the same: everything above is the branch that needs a transport between two members, and
everything here takes the caller's choice as an argument. `ComplexAnalytic.RefineDatumCrossEq` and
`ComplexAnalytic.RefineDatumCrossUnit` are `abbrev`s and so are guarded like the definitions they
are, and `ComplexAnalytic.refineDatumGlueNe_eq` and `ComplexAnalytic.refineDatumCrossProj_eq` sit
beside the definitions they unfold, as their equal-branch counterparts do.
-/

/--
info: 'ComplexAnalytic.RefineDatumCrossEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumCrossEq

/--
info: 'ComplexAnalytic.RefineDatumCrossUnit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumCrossUnit

/--
info: 'ComplexAnalytic.refineDatumGlueNe' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe

/--
info: 'ComplexAnalytic.refineDatumGlueNe_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_eq

/--
info: 'ComplexAnalytic.refineDatumCrossProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProj

/--
info: 'ComplexAnalytic.refineDatumCrossProj_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProj_eq

/--
info: 'ComplexAnalytic.isoOfAlgEquiv_symm_refineDatumCrossAlgEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isoOfAlgEquiv_symm_refineDatumCrossAlgEquiv

/--
info: 'ComplexAnalytic.refineDatumGlueNe_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_comp

/--
info: 'ComplexAnalytic.refineDatumGlue' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue

/--
info: 'ComplexAnalytic.refineDatumGlue_of_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue_of_eq

/--
info: 'ComplexAnalytic.refineDatumGlue_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue_of_ne

/--
info: 'ComplexAnalytic.refineDatumGlue_const' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue_const


/-! ### The analytified form of the unequal branch's triangle, and the projection it needs

`Oka/Analytification/CrossMemberDatumGlue.lean`. The `a`-side projection of a cross-member refined
overlap followed down to its member, the same statement under the analytification functor, and the
unequal branch's coherence triangle analytified.

They are guarded in their own section rather than folded into the one above because the section
above enumerates what that branch had when it was written, and the file's `## What is not here`
said at the time that the analytified triangle was absent. All three are theorems, so none of them
is the `abbrev` case that section records.
-/

/--
info: 'ComplexAnalytic.refineDatumCrossProj_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProj_localisationHom

/--
info: 'ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProj_analytification_localisationProj

/--
info: 'ComplexAnalytic.refineDatumGlueNe_analytification_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_analytification_comp

/-! ### The caller's choice in a cross-member `glue`

`Oka/Analytification/CrossMemberChoice.lean`: the two obligations a cross-member `glue` puts on
the caller collapse to one associate statement, and that statement holds — so the choice the field
takes exists at every ordered pair. -/

/--
info: 'ComplexAnalytic.coverOverlapClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapClass

/--
info: 'ComplexAnalytic.coverOverlapClass_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOverlapClass_mul

/--
info: 'ComplexAnalytic.refineDatumCrossAlgEquiv_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossAlgEquiv_symm

/--
info: 'ComplexAnalytic.exists_refineDatumCrossEq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCrossEq

/--
info: 'ComplexAnalytic.refineDatumCross_exists_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCross_exists_iff

/--
info: 'ComplexAnalytic.RefineDatumCrossFactor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.RefineDatumCrossFactor

/--
info: 'ComplexAnalytic.exists_refineDatumCrossFactor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCrossFactor

/--
info: 'ComplexAnalytic.exists_refineDatumCrossUnit_of_factor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCrossUnit_of_factor

/--
info: 'ComplexAnalytic.exists_refineDatumCross' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.exists_refineDatumCross

/-! ### Two adjoined roots, and the composition law for a renaming that it needs

`Oka/Analytification/ChangeOfVariables.lean` and `Oka/Analytification/HypersurfaceFinite.lean`.
The general composition law for `ComplexAnalytic.PresHom.ofRename` with the ideal statement under
it, and the two-step hypersurface extension it makes expressible as one map of presentations,
with its finiteness.

Appended as their own section rather than folded into the two above because those sections
enumerate what their files had when they were written, and because every branch on this board adds
a section at the end of this file — a section moved is a conflict for somebody else. All four are
theorems.
-/

/--
info: 'ComplexAnalytic.rename_mem_presentationIdeal' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.rename_mem_presentationIdeal

/--
info: 'ComplexAnalytic.PresHom.ofRename_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.PresHom.ofRename_comp

/--
info: 'ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom

/--
info: 'ComplexAnalytic.towerPresentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresentation

/--
info: 'ComplexAnalytic.towerPresHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresHom

/--
info: 'ComplexAnalytic.isFinite_analytificationMap_towerPresHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytificationMap_towerPresHom

/--
info: 'ComplexAnalytic.towerPresentation_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresentation_one

/--
info: 'ComplexAnalytic.towerPresHom_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresHom_one

/--
info: 'ComplexAnalytic.towerPresHom_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.towerPresHom_two

/-! ### The hypersurface over an open subset of the base

`Oka/Analytification/OpenBaseFiniteness.lean`. The image in `ℂ^n` of the points of a hypersurface
at which a second polynomial vanishes, its closedness, the vacuity of that vanishing above the
complement, the finiteness of the hypersurface over the cylinder, and the two witnesses that bound
how large the complement can be.

The first is a `def` and is guarded for that reason: the convention here is every declaration and
not every theorem, and `scripts/guard_coverage.py` cannot report a missing guard on a name
advertised under `## Main definitions`, which it does not read.
-/

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage

/--
info: 'ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage

/--
info: 'ComplexAnalytic.eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage

/--
info: 'ComplexAnalytic.isFinite_analytification_comp_projRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_analytification_comp_projRestrict

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage_one

/--
info: 'ComplexAnalytic.hypersurfaceCommonZeroImage_X' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfaceCommonZeroImage_X

/-! ### The refined datum's symmetry law, and the monomorphism under it

`Oka/Analytification/RefineDatumSymm.lean`. The universal property of a localisation at a
distinguished open, the monomorphism it makes of the structure map, the two monomorphisms of the
cross-member projection that follow, and the three consequences for the refined cover datum's
`glue` — that the coherence triangle determines it, that it does not depend on the caller's
choice, and that it is symmetric.

Three of the eight are `instance`s and are guarded for the same reason the rest are: the
convention here is every declaration and not every theorem, and `scripts/guard_coverage.py`
reports nothing about a name it does not find under `## Main results`.
-/

/--
info: 'ComplexAnalytic.ringHom_ext_localisationRingHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.ringHom_ext_localisationRingHom

/--
info: 'ComplexAnalytic.mono_localisationHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mono_localisationHom

/--
info: 'ComplexAnalytic.mono_refineCrossProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mono_refineCrossProj

/--
info: 'ComplexAnalytic.mono_refineDatumCrossProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mono_refineDatumCrossProj

/--
info: 'ComplexAnalytic.refineDatumGlueNe_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_unique

/--
info: 'ComplexAnalytic.refineDatumGlueNe_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_congr

/--
info: 'ComplexAnalytic.refineDatumGlueNe_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_symm

/--
info: 'ComplexAnalytic.refineDatumGlue_symm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlue_symm

/-! ### The cross-member refined transition, over the original cover's transition

`Oka/Analytification/RefineDatumTransition.lean`. The comparison of a cross-member refined overlap
with the original overlap it lies over, on a double overlap and on a triple one, the square saying
that the refined transition lies over the original datum's own transition, and what that makes of
`hrange`: the half the original law supplies, and the equivalence saying it is the only half.

Three of the fourteen are `def`s and are guarded for the same reason the rest are: the convention
here is every declaration and not every theorem.
-/

/--
info: 'ComplexAnalytic.refineDatumCrossProjSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProjSpace

/--
info: 'ComplexAnalytic.refineDatumCrossProjSpace_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossProjSpace_localisationProj

/--
info: 'ComplexAnalytic.refineDatumCrossPart' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossPart

/--
info: 'ComplexAnalytic.refineDatumCrossPart_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossPart_eq

/--
info: 'ComplexAnalytic.refineDatumCrossPart_coverIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossPart_coverIncl

/--
info: 'ComplexAnalytic.refineDatumGlueNe_analytification_localisationProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumGlueNe_analytification_localisationProj

/--
info: 'ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne

/--
info: 'ComplexAnalytic.coverOpen_refineDatumPoly_of_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.coverOpen_refineDatumPoly_of_ne

/--
info: 'ComplexAnalytic.range_refineDatumCrossTriple_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumCrossTriple_subset

/--
info: 'ComplexAnalytic.refineDatumCrossTriple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossTriple

/--
info: 'ComplexAnalytic.refineDatumCrossTriple_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossTriple_eq

/--
info: 'ComplexAnalytic.refineDatumCrossTriple_coverTripleIncl' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.refineDatumCrossTriple_coverTripleIncl

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_localisationProj_subset

/--
info: 'ComplexAnalytic.range_refineDatumTransitionHom_subset_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_refineDatumTransitionHom_subset_iff

/-! ### The side condition of the two-root renaming

`ComplexAnalytic.rename_mem_presentationIdeal`'s first consumer, and the composite law of
`Oka/Analytification/HypersurfaceFinite.lean` with its hypothesis discharged at it. Both are
theorems.

Appended as its own section for the reason the section above gives: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.rename_localisationIncl_comp_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.rename_localisationIncl_comp_mem

/--
info: 'ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom'

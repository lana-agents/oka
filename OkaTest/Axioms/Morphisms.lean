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
polynomials, together with the category the finite étale ones form over a fixed base and the
cancellations that say a morphism of that category is itself finite étale. Two sections are of a
third kind, named here because the description above does not reach them: **transports of the
local-isomorphism class along a change of source and target** — over an open subset of the
target, and to subspaces cut out by a family of global sections and by its pullbacks. Those are
`### And a local isomorphism restricted over an open of the target is one` and
`### And a local isomorphism restricted to subspaces cut out by a family and by its pullbacks`.
And one section is of a fourth kind, named here for the same reason: statements about the class
of **isomorphisms**, which are not built from a topological criterion and are not transported from
anywhere — `### An isomorphism of analytic spaces is bijective on points`. And one is of a fifth:
statements about a topological property of a cover's **total space** rather than about any class
of morphisms — that preconnectedness passes along a morphism surjective on points, and the
separation of two covers of equal degree that buys —
`### Connectedness of the total space separates two covers of the same degree`.

**Named rather than counted from the end**, which is the repair and not the description. **The
sentence this replaces called them *the last two***; they stopped being that when two further
sections were appended past them — and one of those two was written across two lines, so no
count of this file could see it and the claim went stale without leaving a trace anything could
find. **That
is the best argument for the heading check `.orchestra/validation.sh` now runs**: not a wrong
number, which a recount repairs, but a positional claim in an append-at-end file that nothing
was able to contradict.

**Naming a section does not protect the name against being rewritten.** The fourth-kind pointer
above said `### An isomorphism of analytic spaces is surjective on points` until the branch that
renamed that heading to its present form — the same file and the same push — left the pointer
behind, and the same sentence said *a* statement where the section holds two. **Nothing mechanical
sees either half**: the heading check above asks that a heading be written on the line that opens
its doc comment and not that anything cite it, and `scripts/check_docstring_names.py` resolves
backticked *declaration* names, which a heading is not. So this is a third failure mode of the
same sentence — not stale by position and not stale by count, but naming something that no longer
exists — and the repair for it is the one the sections themselves use: quote the heading as it is
written.

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
info: 'ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp

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
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp

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
`LocalOkaRing.quotientSimpleZeroEquiv`. `ComplexAnalytic.IsCutOutBy.mem_ker_stalkMap_iff` is the
kernel of a one-section cut-out and `ComplexAnalytic.bijective_stalkMap_comp_of_incl` is the whole
proof with both identifications taken as arguments;
`ComplexAnalytic.bijective_stalkMap_comp_projCoords` and
`ComplexAnalytic.bijective_stalkMap_comp_uliftProj` are its `Fin` and `ULift (Fin _)` instances,
each with its `IsIso` form beside it. `ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` is that every
cutting section vanishes at every point of the subspace it cuts out, which is what makes the
vanishing half of the hypothesis below free rather than asked for, and the `…_of_coeff` results
after it are the same conclusion from one Taylor coefficient of the germ rather than from the
order. -/

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

`Oka/AnalyticSpace/SimpleZeroPolynomial.lean`. The `…_of_coeff` results above take one Taylor
coefficient of the germ of the cutting section; the `…_of_pderiv` results here take
`MvPolynomial.pderiv` of the polynomial the section comes from, evaluated at the point, which is
the form a standard étale presentation supplies.
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
info: 'ComplexAnalytic.isFinite_comp_proj_of_range_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isFinite_comp_proj_of_range_subset

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

`Oka/AnalyticSpace/OpenBaseProjection.lean` and
`Oka/AnalyticSpace/OpenBaseProjectionPolynomial.lean`, together with
`ComplexAnalytic.AnalyticSpace.restrictHom` from `Oka/AnalyticSpace/OpenSubspace.lean`, which is
what makes the projection over `V` a restricted morphism. The two headings above are the same two
halves over the whole of `ℂ^(n+1)`; these carry both across the restriction, in all three
spellings of the simple-zero hypothesis — an order, one Taylor coefficient, and a derivative of a
polynomial.

**The restriction is of the base**, `V ⊆ ℂ^n` with `ComplexAnalytic.cylinder V` its preimage. A
standard étale algebra also inverts a polynomial, and that polynomial involves the fibre variable,
so `D(G)` is cut out of the *source* and is a cylinder only in the special case where `G` does
not. **The source restriction is no longer missing and its guards are the `####` subsection
below**, which is why this paragraph no longer sends a reader elsewhere for it; the two
restrictions stay different and neither subsumes the other. **This sentence ended by naming what
`Oka/Analytification/StandardEtaleAnalytification.lean` *"still records as absent"* — the
`ComplexAnalytic.IsCutOutBy` datum for a presentation's `k + 1` relations — and that file no
longer records it as absent**: the count was right and the reading of it was wrong, `k + 1`
against one being the signature of a statement whose base is the whole of `ℂ^n`, and at `k = 0`
the datum is `ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`
(`Oka/Analytification/StandardEtaleLocalIso.lean`). Still untouched is any statement at
`k ≥ 1`. -/

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
info: 'ComplexAnalytic.Γgerm_resΓ_mem_maximalIdeal_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γgerm_resΓ_mem_maximalIdeal_iff

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

/--
info: 'ComplexAnalytic.evalHom_eq_zero_of_isCutOutBy_resΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.evalHom_eq_zero_of_isCutOutBy_resΓ

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_projRestrict_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_projRestrict_of_coeff

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_projRestrict_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_projRestrict_of_coeff

/--
info: 'ComplexAnalytic.bijective_stalkMap_comp_projRestrict_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.bijective_stalkMap_comp_projRestrict_of_pderiv

/--
info: 'ComplexAnalytic.isIso_stalkMap_comp_projRestrict_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isIso_stalkMap_comp_projRestrict_of_pderiv

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

/-! ### The finite étale covers of a fixed base, as a category

`Oka/AnalyticSpace/FiniteEtaleOver.lean`. Finite étale read as a
`CategoryTheory.MorphismProperty`, the category it cuts out of `CategoryTheory.Over X`, two
objects of that category, and the lemma that separates an object from the base over itself.

The `CategoryTheory.MorphismProperty` instances of that file are anonymous and are not guarded
here; each is a quotation of one of the instances guarded above, whose guards cover the axioms
they are built from.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_iff

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.id

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_hom_of_iso_id

/-! ### The projection of a hypersurface with a simple zero, and the implicit function theorem

`Oka/Analysis/Calculus/Implicit.lean` is mirror-tree — level sets of a strictly differentiable
function on `ι → 𝕜`, with no complex analysis and nothing sheaf-theoretic in it — and no row of
`OkaTest/Axioms.lean`'s topic table names its subject. Its guards are therefore here, with the
guards of the analytic result that motivated it, which is the rule that table states and the
placement `Oka/Topology/Covering/Basic.lean` already has in this file. -/

/--
info: 'ImplicitFunctionData.ofCoordProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ImplicitFunctionData.ofCoordProj

/--
info: 'ImplicitFunctionData.injOn_rightFun_levelSet' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ImplicitFunctionData.injOn_rightFun_levelSet

/--
info: 'ImplicitFunctionData.isOpen_image_rightFun_levelSet' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ImplicitFunctionData.isOpen_image_rightFun_levelSet

/--
info: 'isLocalHomeomorph_coordProj_comp_of_isEmbedding' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLocalHomeomorph_coordProj_comp_of_isEmbedding

/--
info: 'isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter

/--
info: 'isLocalHomeomorph_coordProj_levelSet' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLocalHomeomorph_coordProj_levelSet

/--
info: 'ComplexAnalytic.not_mem_range_uliftCastSuccEmb' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.not_mem_range_uliftCastSuccEmb

/--
info: 'ComplexAnalytic.mem_range_uliftCastSuccEmb' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.mem_range_uliftCastSuccEmb

/--
info: 'ComplexAnalytic.range_base_eq_zeroSet' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_eq_zeroSet

/--
info: 'ComplexAnalytic.base_comp_uliftProj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.base_comp_uliftProj

/--
info: 'ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff

/--
info: 'ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv

/--
info: 'ComplexAnalytic.isLocalIso_comp_proj_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_comp_proj_of_coeff

/--
info: 'ComplexAnalytic.isLocalIso_comp_proj_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_comp_proj_of_pderiv

/-! #### The same after restricting the source to an open subspace

The restricted statements below are the transport of the two halves across an open subspace of the
*hypersurface*, which three module docstrings recorded as absent until taxis #1112. They are
guarded together and apart from the unrestricted ones above because the asymmetry is the content:
the stalk half is already quantified one point at a time and transports by composition, while the
topological one is not reached from its own unrestricted form and goes through
`isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter` above — which is itself a corollary of
the theorem guarded above it, so **nothing here rests on a statement the tree did not already
have**. -/

/--
info: 'ComplexAnalytic.range_base_ofRestrict_eq_zeroSet_inter' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.range_base_ofRestrict_eq_zeroSet_inter

/--
info: 'ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_coeff

/--
info: 'ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_pderiv' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalHomeomorph_base_ofRestrict_comp_uliftProj_of_pderiv

/--
info: 'ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_coeff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_coeff

/--
info: 'ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv

/-! ### Cancellation of finiteness and of finite étaleness

`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` is in `Oka/AnalyticSpace/Finite.lean`
beside the fibre half it completes, and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` is in `Oka/AnalyticSpace/LocalIso.lean`,
which is where `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is declared. Neither uses a covering
map: the `[T2Space]` of both is on the middle space and is spent in the first, through Mathlib's
proper-map cancellation.

`IsCoveringMap.isClosedMap_of_comp` is the **fourth** `IsCoveringMap` statement guarded in this
file — after `IsCoveringMap.isClosedMap`, `IsCoveringMap.eventually_nonempty_homeomorph` and
`IsCoveringMap.nonempty_homeomorph_fiber` above — and the only one that is a *cancellation*. It
is mirror-tree material that nothing in this repository consumes, which is why it is guarded here
and named nowhere else: an unconsumed declaration is exactly the one whose disappearance nothing
else would catch.

The witness that the `[T2Space]` of the two analytic statements cannot be dropped is
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` (`OkaTest/FiniteEtaleCancel.lean`) and is
**not** guarded here: this file imports `Oka` and not `OkaTest`, so no declaration of a test file
is in its environment. -/

/--
info: 'IsCoveringMap.isClosedMap_of_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsCoveringMap.isClosedMap_of_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp

/-! ### Restricting a composite, and the finiteness of a restriction over an open inside the image

`Oka/AnalyticSpace/OpenSubspace.lean`, at the level of complex analytic spaces. The first is
`ComplexAnalytic.restrictHom_comp` reflected along the faithful forgetful functor; the second is
`ComplexAnalytic.isClosedEmbedding_base_restrictHom_of_subset_range` read through
`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`, and it is the shape an **open**
immersion needs — finite over an open subset of its image while not finite at all.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.restrictHom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.restrictHom_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range

/-! ### And a local isomorphism restricted over an open of the target is one

`Oka/AnalyticSpace/OpenSubspace.lean`. Its own section rather than an addition to the one above,
because that header enumerates the two statements under it and a third appended silently would
make the header false — which is the failure this file's section docstrings are most exposed to,
since they assert the state of the repository and a sweep over `Oka/` does not reach them.

**Read it against `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` directly
above**: that one needs `V` inside the image because finiteness is not local on the target, and
this one needs nothing at all because both fields of
`ComplexAnalytic.AnalyticSpace.IsLocalIso` are conditions at a point. It is the second field of
`Oka/Analytification/StandardEtaleFiniteEtale.lean`'s `IsFiniteEtale`, whose guards are in
`OkaTest/Axioms/Analytification.lean`.

Appended as its own section for the reason the sections above give: a section moved is a conflict
for somebody else.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom

/-! ### And a local isomorphism restricted to subspaces cut out by a family and by its pullbacks

`Oka/AnalyticSpace/CutOutLocalIso.lean`, the whole of it, in the order they are declared. The
sibling of the section directly above and appended as its own for the same reason that one gives:
that header enumerates what its file had when it was written, and a guard appended into it would
make it false silently.

**Two of the guards below ask nothing of the morphism the class is transported along.**
`ComplexAnalytic.AnalyticSpace.stalkMap_Γgerm_pullbackΓ` and
`ComplexAnalytic.AnalyticSpace.range_base_of_isCutOutBy_pullbackΓ` hold for an arbitrary morphism
of analytic spaces; `ComplexAnalytic.AnalyticSpace.isOpenMap_base_of_isCutOutBy_pullbackΓ` asks
only that its base map is open. The `ComplexAnalytic.AnalyticSpace.IsLocalIso` hypothesis is
spent by the last three alone. **Every guard below is a theorem.**
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.stalkMap_Γgerm_pullbackΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.stalkMap_Γgerm_pullbackΓ

/--
info: 'ComplexAnalytic.AnalyticSpace.range_base_of_isCutOutBy_pullbackΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.range_base_of_isCutOutBy_pullbackΓ

/--
info: 'ComplexAnalytic.AnalyticSpace.isOpenMap_base_of_isCutOutBy_pullbackΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isOpenMap_base_of_isCutOutBy_pullbackΓ

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalHomeomorph_base_of_isCutOutBy_pullbackΓ' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalHomeomorph_base_of_isCutOutBy_pullbackΓ

/--
info: 'ComplexAnalytic.AnalyticSpace.bijective_stalkMap_of_isCutOutBy_pullbackΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.bijective_stalkMap_of_isCutOutBy_pullbackΓ

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ

/-! ### Surjectivity of a finite local isomorphism over a connected base

`Oka/AnalyticSpace/LocalIso.lean`, appended as its own section for the reason the sections above
give: a section moved is a conflict for somebody else.

The guards below read the two rungs against each other and nothing else — a local isomorphism is
an open map and a finite morphism is a closed one, so over a preconnected base the image of a
non-empty source is everything. The contrapositive is the one with a consumer:
`ComplexAnalytic.not_isFinite_condEtaleProj` (`OkaTest/StandardEtaleNotFinite.lean`) is where the
unrestricted standard étale morphism is refuted by a missing point, and that consumer is a test
declaration and so is **not** guarded here — this file imports `Oka` and not `OkaTest`, which is
the reason the cancellation section above gives for the same omission. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.surjective_base_of_isLocalIso_of_isFinite' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.surjective_base_of_isLocalIso_of_isFinite

/--
info: 'ComplexAnalytic.AnalyticSpace.surjective_base_of_isFiniteEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.surjective_base_of_isFiniteEtale

/--
info: 'ComplexAnalytic.AnalyticSpace.not_isFinite_of_isLocalIso_of_not_surjective' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_isFinite_of_isLocalIso_of_not_surjective

/-! ### A property of the restriction over `⊤` is a property of the morphism

`ComplexAnalytic.AnalyticSpace.restrictHom f V` is a morphism between two *other* spaces, so a
statement about it is not on its face a statement about `f`. At `V = ⊤` the two inclusions are
isomorphisms and the property transfers, which is what lets a `V` hypothesis be **refuted** rather
than only left unproved: a morphism that is not finite étale now gives
`¬ ComplexAnalytic.AnalyticSpace.IsFiniteEtale` of its own restriction over `⊤` by contraposition,
and likewise for `ComplexAnalytic.AnalyticSpace.IsFinite`. **The finiteness half is the one the
two `## What is not here` bullets elsewhere were about**, since both name a finiteness theorem; it
lives in `Oka/AnalyticSpace/OpenSubspace.lean` because `ComplexAnalytic.AnalyticSpace.IsFinite` is
not a `CategoryTheory.MorphismProperty` here and needs no part of this file.

**Appended as its own section**, for the reason the sections above give. The open-subspace
statements underneath these — `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`,
`ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict`,
`ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`,
`ComplexAnalytic.AnalyticSpace.isIso_liftTop` and
`ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top` — are guarded in
`OkaTest/Axioms/AnalyticSpace.lean`, with the constructions that build a space rather than with the
classes of morphisms, and so is the one definition they are stated about,
`ComplexAnalytic.AnalyticSpace.liftTop`. **Listed rather than counted**, because a list is
falsified by a missing entry and a numeral by any addition anywhere.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top

/-! ### An isomorphism of analytic spaces is bijective on points

`Oka/AnalyticSpace/Basic.lean`, appended as its own section for the reason the sections above
give: a section moved is a conflict for somebody else.

**Not the same statement as the one under `### Surjectivity of a finite local isomorphism over a
connected base`**, which is the section this is most easily confused with. That one reads
surjectivity off *two* classes — a local isomorphism is open, a finite morphism is closed — and
needs a preconnected base and a non-empty source. This one is the categorical fact and needs
nothing: an inverse exists, so the base has a right inverse. **The section is named and not
located**, because it is not the section immediately above this one and counting would say it was.

Its consumers spend it in the contrapositive, to turn a non-surjectivity into a `¬ IsIso`, and
they are **not all `Oka/`'s** — which is what decides whether each of them is guarded here.
`ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι` (`Oka/AnalyticSpace/Sigma.lean`) is the library's,
and is guarded in `OkaTest/Axioms/AnalyticSpace.lean` beside the disjoint union's other statements;
`ComplexAnalytic.not_isIso_lineRefineToBase` (`OkaTest/RefineDatumUnitFamily.lean`) is a test
declaration and so is **not** guarded here — this file imports `Oka` and not `OkaTest`, which is
the reason the `### Cancellation of finiteness and of finite étaleness` section gives for the same
omission.

**Guarded here rather than in `OkaTest/Axioms/AnalyticSpace.lean`, and the reason is the subject
and not the module.** That file's `Oka/AnalyticSpace/Basic.lean` guards are all
`ComplexAnalytic.IsCLinearHom` statements sitting under its gluing heading; its own docstring sends
the *classes* of morphisms here, and `CategoryTheory.IsIso` is one. The sibling above,
`ComplexAnalytic.AnalyticSpace.surjective_base_of_isLocalIso_of_isFinite`, is guarded here for the
same reason and is declared in a different module again.

**Two statements, and the second is the first's `.surjective`.**
`ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso` is where the homeomorphism and every
caveat above now live; `ComplexAnalytic.AnalyticSpace.surjective_base_of_isIso` is a projection of
it and is kept because a non-surjectivity is the shape that refutes an `IsIso`. Both are guarded,
because both are advertised under `Oka/AnalyticSpace/Basic.lean`'s `## Main results` and a guard
of a corollary does not guard what it is a corollary of — the axioms of the projection could in
principle be a strict subset. Here they are not, and the two blocks below say so. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso

/--
info: 'ComplexAnalytic.AnalyticSpace.surjective_base_of_isIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.surjective_base_of_isIso

/-! ### The degree does not see a change of source, and is an invariant of a cover

`Oka/AnalyticSpace/Degree.lean`'s two statements about precomposition, and the degree of an object
of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver` that they buy
(`Oka/AnalyticSpace/FiniteEtaleOver.lean`), appended as their own section for the reason the
sections above give: a section moved is a conflict for somebody else.

**Guarded here and not with the `### The finite étale covers of a fixed base, as a category`
section above, although the declarations below are drawn from that section's own file
(`Oka/AnalyticSpace/FiniteEtaleOver.lean`) as well as from `Oka/AnalyticSpace/Degree.lean`.** The
subject of every one of them is `ComplexAnalytic.AnalyticSpace.degree`, which is a function of a
*morphism* and belongs to this file by the topic table's `morphisms of analytic spaces` row; the
category section above is about the objects and their separation by `¬ IsIso`, and none of its
guards reads a fibre.

**Named by file rather than counted**, and this paragraph said *"four of the seven declarations
are that file's"* instead — both numerals wrong of the section as it stands. The repair is not a
recount: a census of an append-at-end section goes stale on the next append and nothing mechanical
reads it, which is the same reason this file's module docstring names its sections rather than
counting them from the end.

**`Oka/AnalyticSpace/Degree.lean`'s older advertised results are still unguarded**, exactly as
they were before this section existed — `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`,
`ComplexAnalytic.AnalyticSpace.degree_id`, `ComplexAnalytic.AnalyticSpace.degree_sigmaFold`,
`ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one` and
`ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`, which
`scripts/guard_coverage.py --by-file` prints by name under that file. That is neither a regression
nor a repair: **a branch guards what it adds**, the whole-file figure it leaves behind is
whatever the sum is, and retro-guarding five declarations a branch does not touch is a separate
and purely mechanical job. The list above is by name and not by count, so nothing in it goes
stale when one of them is guarded. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.degree_comp_of_bijective_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.degree_comp_of_bijective_base

/--
info: 'ComplexAnalytic.AnalyticSpace.degree_isIso_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.degree_isIso_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_of_iso

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_degree_ne

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_id

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_trivial

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_eq_of_iso_trivial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_eq_of_iso_trivial

/-! ### Connectedness of the total space separates two covers of the same degree

`Oka/AnalyticSpace/Basic.lean`'s transport of preconnectedness along a morphism surjective on
points, and the statements of `Oka/AnalyticSpace/FiniteEtaleOver.lean` it buys: that
preconnectedness of the total space is an invariant of an object, the contrapositive that
separates two objects by it, that a trivial cover with two distinct sheets is disconnected, and
the two composed.

**Appended as its own section rather than added to either of the two it draws from**, for the
reason the sections above give — a section moved is a conflict for somebody else — and because
the subject is neither of theirs. `### An isomorphism of analytic spaces is bijective on points`
is about the class of isomorphisms and the first declaration below is stated at a surjection;
`### The degree does not see a change of source, and is an invariant of a cover` is about
`ComplexAnalytic.AnalyticSpace.degree`, and the whole point of this section is the separation that
degree cannot make.

**Named by file rather than counted**, as the section above says and for the reason it gives.

**`ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma`, which is what the third statement
below reads, is guarded in `OkaTest/Axioms/AnalyticSpace.lean`** beside the disjoint union's other
statements, and so is `ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base` under it — a
disjoint union is a space and not a morphism, which is the topic table's split.
`OkaTest/FiniteEtaleOver.lean`'s `not_iso_trivial_sqOver`, the witness at the punctured line, is a
test declaration and so is **not** guarded here: this file imports `Oka` and not `OkaTest`, the
same reason the `### Cancellation of finiteness and of finite étaleness` section gives for its own
omission. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.preconnectedSpace_of_surjective_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.preconnectedSpace_of_surjective_base

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preconnectedSpace_of_iso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.preconnectedSpace_of_iso

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_of_preconnectedSpace

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.not_preconnectedSpace_trivial

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_of_preconnectedSpace'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_of_preconnectedSpace

/-! ### The fibre functor

The fibre of a cover over a point of the base, the two functors it assembles into and the values
they take, all of `Oka/AnalyticSpace/FiniteEtaleOver.lean`: the fibre type, its finiteness, the
action of a morphism of covers on it, the functor into `Type u`, the functor into `FintypeCat`, the
equivalence an isomorphism of covers induces, the count against
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`, and the two values — a point over the base
over itself and `ι` over the trivial `ι`-sheeted cover.

**Named by file rather than counted**, as the two sections above say and for the reason they give.

**Definitions are guarded here as well as theorems, and that is this file's existing practice
rather than a departure** — `ComplexAnalytic.AnalyticSpace.okaMap` and
`ComplexAnalytic.AnalyticSpace.restrictLE` are among the definitions guarded in the sections above,
and this paragraph said the opposite until it was checked. A `#print axioms` on a `def` reports
what its *value* was built from, which for the two functors is the whole of the claim that they are
constructions and not a `Classical.choice` in disguise.

**`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv` is `noncomputable` and is on
the same three axioms as everything else here**, so noncomputability and the axiom footprint come
apart. The modifier is forced and the reason was measured by deleting it and reading the error:
`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv` is `noncomputable`, and it is that and
not anything in `Oka/AnalyticSpace/FiniteEtaleOver.lean` that the compiler stops at.

`Mathlib.CategoryTheory.FintypeCat` enters `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s import
closure with the second functor and is the only import that push adds; it is not guarded here
because nothing in this repository declares it. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.finite_fiber

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberMap

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberEquivOfIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberEquivOfIso

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.card_fiber

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.uniqueFiberId

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberTrivialEquiv

/-! ### The trivial cover at one sheet is the base over itself

`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s isomorphism of objects at an inhabited subsingleton
index type, and the two-directional statement over a non-empty base that it and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isEmpty_iso_trivial_id` make together. Appended as
its own section rather than merged into the degree sections above: moving or reordering a section
of this file is a conflict for every branch that has appended to it.

**What the guards below are a check of is that the two directions are proved by different means.**
The forward one goes through `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree`, which
separates isomorphism classes and never produces an isomorphism; the backward one goes through
`ComplexAnalytic.AnalyticSpace.sigmaFoldIso` and the universal property of the disjoint union,
which reads no structure sheaf and no fibre. Neither is the other read backwards.

**`Classical.choice` is in every guard below and is not a surprise**: both statements mention
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivial`, which is built out of a gluing, and the
forward direction spends `Nat.card`.

**Named and not located.** No sentence here says which section precedes or follows it.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.trivialIsoId

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_iso_trivial_id_iff

/-! ### Unique lifting for morphisms of covers

The rigidity statements of `Oka/AnalyticSpace/FiniteEtaleOver.lean`: that two morphisms of covers
agreeing at one point of a preconnected source agree on points, the same conclusion from a point
of a fibre and from the fibre functor's action, and the endomorphism corollary.

**Appended as its own section rather than added to the section above**, for the reason the
sections above give — a section moved is a conflict for somebody else — and because the subject is
not that one's: `### The fibre functor` is about the fibre and the functors it assembles into,
where these are about what a morphism of covers is pinned down by, and only
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberMap_eq` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq` mention a fibre at
all.

**Named by file rather than counted**, as the sections above say and for the reason they give.

**`IsCoveringMap.eq_of_comp_eq` is Mathlib's and is not guarded here**, nothing in this repository
declaring it; what the guards below check is that composing it with
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` — guarded in
`OkaTest/Axioms/AnalyticSpace.lean` — introduces nothing, which is the same thing the sections
above check of their own compositions. `Classical.choice` is in every guard below and arrives with
the covering-map rung, not with anything stated here.

**Named and not located.** No sentence here says which section is above or below it; the next
branch appends between them. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_apply_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_apply_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberMap_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberMap_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_of_fiberFunctor_map_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_id_of_apply_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.base_eq_id_of_apply_eq

/-! ### Faithfulness for morphisms of covers

`Oka/AnalyticSpace/FiniteEtaleOver.lean` and `Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`:
that a morphism of covers is determined by its base map, the unique-lifting statements guarded
above with an equality of *morphisms* rather than of maps as their conclusion, the endomorphism
corollary, and the general locally-ringed-space lemma the first of those runs on.

**`AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq` is mirror-tree material guarded here
rather than in `OkaTest/Axioms/Sheaves.lean`, which is the row that routes its file** and which
already holds `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isEmpty` from that same file. This
is consumer-placement, which `OkaTest/Axioms.lean` records as a practice with two precedents and
which `OkaTest/Axioms/AnalyticSpace.lean` reaches for
`AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext` — a declaration of the same file and the one
this lemma is built from. The reason to prefer it here is that the statements below are the whole
of why that lemma exists, and `OkaTest/Axioms/Sheaves.lean` would separate it from them. **A
later seat who disagrees moves one guard**, and nothing in this section's prose depends on where
it sits.

**`Classical.choice` is in every guard below.** It is not introduced here: it arrives with the
covering-map rung through the statements guarded above, and it is present even in
`AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq`, whose statements ask for no
separation axiom and no connectedness at all.

**Named by file rather than counted**, as the sections above say and for the reason they give.

**Named and not located.** No sentence here says which section is above or below it. -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_base_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_apply_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_apply_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberMap_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberMap_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberFunctor_map_eq' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_fiberFunctor_map_eq

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.eq_id_of_apply_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.eq_id_of_apply_eq

/-! ### The fibre functor is faithful, as a class, on the connected Hausdorff covers

`Oka/AnalyticSpace/FiniteEtaleOver.lean` and `Oka/AnalyticSpace/LocalIso.lean`: the clopen
dichotomy with `Nonempty` moved into the conclusion, the fibre it produces over a preconnected
base, the extensionality statement that needs no point of that fibre, the injectivity statements
it gives for the fibre functors, the full subcategory they are faithful on, the objects of it
named in `Oka/`, and the `CategoryTheory.Functor.Faithful` instances themselves.

**`ComplexAnalytic.AnalyticSpace.surjective_base_or_isEmpty_of_isFiniteEtale` is guarded here and
not with the surjectivity statements it is a corollary of.** This file's rule is that a guard goes
in the section of the push that added it, and the whole reason that disjunction exists is the
faithfulness statements below — the surjectivity theorem it calls was already here and already
guarded. **A later seat who prefers it beside its own line moves one guard**, and no sentence here
depends on where it sits.

**`Classical.choice` is in every guard below** and is not introduced by any of them: it arrives
through the covering-map rung, exactly as the section above records, and is present even in the
`CategoryTheory.ObjectProperty` that names the subcategory.

**Named by file rather than counted**, as the sections above say and for the reason they give.

**Named and not located.** No sentence here says which section is above or below it. -/

/--
info: 'ComplexAnalytic.AnalyticSpace.surjective_base_or_isEmpty_of_isFiniteEtale' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.surjective_base_or_isEmpty_of_isFiniteEtale
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_fiber' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.nonempty_fiber
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.hom_ext_of_forall_fiberMap_eq
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor_map_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiberFunctor_map_injective
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor_map_injective' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor_map_injective
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_id' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_id

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty_base'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isPreconnectedT2_trivial_of_isEmpty_base
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fiberFunctor
/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fintypeFiberFunctor' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.faithful_fintypeFiberFunctor

/-! ### Multiplicativity of the degree, and the divisibility it gives on covers

`ComplexAnalytic.AnalyticSpace.degree_comp` (`Oka/AnalyticSpace/Degree.lean`), the elementary
count under it (`Oka/SetTheory/Cardinal/Finite.lean`), and what reading it at the triangle of a
morphism of covers buys (`Oka/AnalyticSpace/FiniteEtaleOver.lean`). Appended as its own section
rather than merged into `### The degree does not see a change of source, and is an invariant of a
cover` above, for the reason that section itself gives: moving or reordering a section of this
file is a conflict for every branch that has appended to it.

**The mirror-tree declarations are guarded here and not in a file of their own.**
`Set.preimageCompEquivSigma` and `Nat.card_preimage_singleton_comp` are declared by
`Oka/SetTheory/Cardinal/Finite.lean`, which has no complex-analytic content and no
`## Main results` heading of its own; the precedent for guarding such a declaration under the
topic of the statement that consumes it is the `IsCoveringMap` guards earlier in this file, which
are `Oka/Topology/Covering/Basic.lean`'s. The subject of everything below is
`ComplexAnalytic.AnalyticSpace.degree`, a function of a *morphism*, which is the topic table's
`morphisms of analytic spaces` row.

**`Set.preimageCompEquivSigma` is the only guard below that is not `Classical.choice`**, and that
is the finding worth having a guard for rather than a fact about bookkeeping: splitting the fibre
of a composite into the fibres of its first factor is a construction, it assumes nothing about
either map, and the choice enters only when the pieces are *counted* —
`Nat.card_preimage_singleton_comp` manufactures a `Fintype` from a `Finite` instance and is
`Classical.choice` for that reason and not because of anything geometric. -/

/--
info: 'Set.preimageCompEquivSigma' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Set.preimageCompEquivSigma

/--
info: 'Nat.card_preimage_singleton_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Nat.card_preimage_singleton_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.degree_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.degree_comp

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_dvd_degree' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_dvd_degree

/--
info: 'ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_left_eq_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_left_eq_one

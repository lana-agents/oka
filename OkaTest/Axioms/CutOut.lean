/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Subspaces cut out by global sections

The zero locus of a family of global sections of the structure sheaf of a locally ringed
space, the closed immersion cutting it out, the mapping property of that immersion, how
such a datum is transported, and the complex analytic space one presents.

**The description above ended at *"and how such a datum is transported"* until 2026-09-07**, when
`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus` was guarded here: that declaration is an object
of `ComplexAnalytic.AnalyticSpace` and no clause about a datum reaches it.

The last clause is here because the description above did not reach the sections whose subject
is neither a zero locus nor a mapping property. It says **how** and not *which*, and that is
deliberate: this file already guards transport along an isomorphism of the target
(`ComplexAnalytic.IsCutOutBy.iso_comp`), to an open of the ambient space, to another family with
the same range, and against a datum for an intermediate subspace, so a clause naming *two* ways
a datum moves would have been false of this file the day it was written.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### The zero locus of a family of global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isClosed_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isClosed_zeroLocus

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.range_zeroLocusι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.range_zeroLocusι

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isClosedEmbedding_zeroLocusι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isClosedEmbedding_zeroLocusι

/-! ### The closed subspace cut out by a family of global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.stalkMap_zeroLocusιHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.stalkMap_zeroLocusιHom

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.zeroLocusStalkQuotientEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.zeroLocusStalkQuotientEquiv

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspaceι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspaceι

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι

/-! ### The topological half of the mapping property of `IsCutOutBy` -/

/--
info: 'ComplexAnalytic.Γgerm_mem_maximalIdeal_of_c_app_eq_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.Γgerm_mem_maximalIdeal_of_c_app_eq_zero

/--
info: 'ComplexAnalytic.IsCutOutBy.baseLift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.baseLift

/--
info: 'ComplexAnalytic.IsCutOutBy.baseLift_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.baseLift_unique

/-! ### Uniqueness of the factorisation through a subspace cut out by global sections -/

/--
info: 'ComplexAnalytic.IsCutOutBy.mono' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.mono

/--
info: 'ComplexAnalytic.IsCutOutBy.hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.hom_ext

/--
info: 'ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy

/-! ### The structure sheaf of a subspace cut out by global sections -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isIso_quotientSheafifyToPushforward' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isIso_quotientSheafifyToPushforward

/--
info: 'ComplexAnalytic.IsCutOutBy.pushforwardIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.pushforwardIso

/-! ### The mapping property of a subspace cut out by global sections -/

/--
info: 'ComplexAnalytic.IsCutOutBy.existsUnique_lift' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.existsUnique_lift

/--
info: 'ComplexAnalytic.IsCutOutBy.uniqueIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.uniqueIso

/-! ### Being cut out is local on the target -/

/--
info: 'ComplexAnalytic.restrictHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.restrictHom

/--
info: 'ComplexAnalytic.IsCutOutBy.restrictOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.restrictOpen

/--
info: 'ComplexAnalytic.isCLinearHom_restrictHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_restrictHom

/--
info: 'ComplexAnalytic.IsCutOutBy.iso_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.iso_comp

/-! ### Restricting a composite, and restricting over an open inside the image

`Oka/AnalyticSpace/Restrict.lean`. Three general facts about `ComplexAnalytic.restrictHom` that
the section above did not need: that it takes a composite to a composite, and that over an open
subset of the target lying **inside the image** it is surjective and — once the base of the
morphism is an embedding — a closed embedding.

The last of the three is the companion of `ComplexAnalytic.isClosedEmbedding_base_restrictHom` at
the opposite trade, and it is what an *open* immersion needs: the inclusion of an open subspace is
an embedding whose base is not a closed map, so the earlier theorem does not reach it, while its
restriction over a smaller open **is** a closed embedding because the two ranges then agree.

**`ComplexAnalytic.isClosedEmbedding_base_restrictHom` is guarded here too, and it is older than
this section.** It had no guard because it was in no `## Main results` list; naming it in the one
the third theorem below needed — the two are a pair and neither reads without the other — is what
`scripts/guard_coverage.py` then reported as a **new** unguarded result. The gap was there before
and the citation is what made it visible, so it is closed here rather than left for the counter to
carry.

Appended as its own section for the reason the sections in the other guard files give: a section
moved is a conflict for somebody else.
-/

/--
info: 'ComplexAnalytic.isClosedEmbedding_base_restrictHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isClosedEmbedding_base_restrictHom

/--
info: 'ComplexAnalytic.restrictHom_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.restrictHom_comp

/--
info: 'ComplexAnalytic.surjective_base_restrictHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.surjective_base_restrictHom

/--
info: 'ComplexAnalytic.isClosedEmbedding_base_restrictHom_of_subset_range' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isClosedEmbedding_base_restrictHom_of_subset_range

/-! ### Cancelling a cut-out datum: cutting out inside a subspace

`Oka/AnalyticSpace/CutOutCancel.lean`, the whole of it, in the order they are declared. Appended
as its own section rather than into the one above, which is about
`ComplexAnalytic.restrictHom` and would be falsified by an addition it does not describe — the
same reason that section gives for being its own.

**None of `ComplexAnalytic.IsCutOutBy.of_range_eq`, `ComplexAnalytic.IsCutOutBy.of_comp_append`
and `ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq` is about complex analytic spaces**, and the
one general `Fin` fact `ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq` consumes,
`Fin.range_append`, is in the mirror tree
(`Oka/Data/Fin/Tuple/Basic.lean`) and is **deliberately not guarded here**: no guard file in this
repository guards a `Fin` lemma, and `Fin.init_zero`, the file's only other declaration, is not
guarded either.

**This paragraph opened *"None of the guards below is about complex analytic spaces"* until
2026-09-07**, and a section was appended after it in which
`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus` and
`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus_toLocallyRingedSpace` are about one; the three
this section guards are named above instead, which is what the clause was always about.
-/

/--
info: 'ComplexAnalytic.IsCutOutBy.of_range_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.of_range_eq

/--
info: 'ComplexAnalytic.IsCutOutBy.of_comp_append' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.of_comp_append

/--
info: 'ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq

/-! ### Composing cut-out data: cutting a subspace down further

`Oka/AnalyticSpace/CutOutCompose.lean`, the whole of it, in the order they are declared. Appended
as its own section rather than into the section headed *Cancelling a cut-out datum*, which is
about `Oka/AnalyticSpace/CutOutCancel.lean` and says so.

`ComplexAnalytic.IsCutOutBy.comp_append` and `ComplexAnalytic.IsCutOutBy.comp_of_range_eq` are
statements about morphisms of locally ringed spaces;
`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus` and
`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus_toLocallyRingedSpace` are about complex analytic
spaces, which is why the description at the head of this file has a clause for them.

**`AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspaceι` is guarded under *The closed subspace
cut out by a family of global sections* above and not here**, beside
`AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`, which is the cut-out datum
it carries. It had no guard at all until 2026-09-07, when
`Oka/AnalyticSpace/CutOutCompose.lean`'s `## Main results` became the first to advertise it and
`scripts/guard_coverage.py` reported the gap.

**`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus` is what makes
`ComplexAnalytic.IsCutOutBy.comp_append` and `ComplexAnalytic.IsCutOutBy.comp_of_range_eq`
non-vacuous.**
A composition lemma whose hypotheses nothing supplies is consistent with being about nothing;
`ComplexAnalytic.IsCutOutBy.zeroLocusSubspaceι_comp` supplies them from
`AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`, which is guarded above and
holds for every locally ringed space and every finite family.
-/

/--
info: 'ComplexAnalytic.IsCutOutBy.comp_append' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.comp_append

/--
info: 'ComplexAnalytic.IsCutOutBy.comp_of_range_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.comp_of_range_eq

/--
info: 'ComplexAnalytic.IsCutOutBy.zeroLocusSubspaceι_comp' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsCutOutBy.zeroLocusSubspaceι_comp

/--
info: 'ComplexAnalytic.isLocalModel_zeroLocusSubspace_of_isCutOutBy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isLocalModel_zeroLocusSubspace_of_isCutOutBy

/--
info: 'ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus

/--
info: 'ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus_toLocallyRingedSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus_toLocallyRingedSpace

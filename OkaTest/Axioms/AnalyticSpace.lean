/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Complex analytic spaces

Complex analytic spaces as objects, and the constructions that build one: local models and the
node; the residue field, the continuity and naturality of the value of a section, and the
rigidity of germs; open subspaces — in general and at the open that is everything — and the
non-vanishing locus; that being a complex analytic space is a local condition; **gluing** — the
`ℂ`-algebra structure of a glued space, a cover by abstract spaces, the analytic structure on
the gluing, the fields of
`CategoryTheory.GlueData.ofGlueData'`, and gluing a morphism; and the
**coproduct** — the disjoint union of a family, the trivial `n`-sheeted cover, the sheet
comparison, and the one-sheeted disjoint union; and that the spaces this development
**constructs** are **Hausdorff**, which is the one heading below naming a property of a space
rather than a construction of one. **Two of the headings below are about morphisms after all** —
gluing one, and that a morphism to `ℂ^n` is determined by the pullbacks of the coordinates —
because each is a statement about the space the construction produces; the *classes* of
morphisms are `OkaTest/Axioms/Morphisms.lean`'s.

**That is a description and not a list, and the headings below are the record**: each names the
statement its assertions defend, and the recipe beside `OkaTest/Axioms.lean`'s routing table
resolves them to modules. The stance is `OkaTest/Axioms/Sheaves.lean`'s and
`OkaTest/Axioms/LocalOkaRing.lean`'s, and it is taken here because this file is past the size at
which a list stays true: at `883b62f` it held 138 guards under nineteen headings over nineteen
modules.

**The sentence this replaces named local models, the node and the value of a section**, which at
`27c185a` was at most 19 of the 102 guards there and four of the sixteen headings there. At
`883b62f` gluing alone — **the five headings named above**, from the `ℂ`-algebra structure of a
glued space to gluing a morphism — was 51 of those 138 and **the four coproduct headings named
above** 32, and neither appeared in it. **Six of the nineteen modules are not
`Oka/AnalyticSpace/`'s** and contributed 29 guards there:
`Oka/CategoryTheory/GlueData.lean` ten, four modules of `Oka/Geometry/RingedSpace/` fifteen, and
`Oka/AlgebraicGeometry/GammaSpecAdjunction.lean` four — most of them under the gluing headings,
beside the analytic statements they serve. See `OkaTest/Axioms.lean` on why a mirror-tree module
such as the first has no row of its own.

**Every figure above is pinned to the commit it was measured at, and this file used to take that
decision the other way.** The paragraphs above carried undated counts and said in terms that the
list to recheck after adding a guard was every one of them; `OkaTest/Axioms.lean`'s rule that
prose about a section should name rather than count says instead that a numeral a reader has to
recheck should not be written, and the two cannot both be followed. **What settles it is that the
rechecking did not happen**, measured at `883b62f`, before this paragraph was rewritten:
*eighteen headings* was false in both sentences carrying it, falsified by `a6dcf31`, which
appended a nineteenth; *130 guards* was false in both places, falsified by `1a7cd87`; the
coproduct *24* was false, falsified by that same commit, which put two guards under the trivial
cover, and moved again by `a6dcf31`, which appended a fourth coproduct heading, so the partition
the number was of changed as well as its value; and the ledger below carried that same number
once more, as what the three coproduct headings *hold now*, where it is pinned to `4853cc2`
instead. **All four were already false when the sweep that reached this file fenced this block**
(`5d45345`), which left them standing on the ground that the conflict of rules had to be settled
before anything here was touched. The gluing *51*, the *29* outside `Oka/AnalyticSpace/` and the
module count are what happened to survive.

**The same numeral had done it once before, and that record is the sharper one.** When the warning
that stood here was written the coproduct read *19* and the sentence carrying it said the number
*"has simply not moved yet"*. The **very next commit to touch this file** falsified it —
`d58c85d`, four guards under the trivial cover — and it then stood wrong for **23 commits**,
because it was the one numeral nobody rechecked. A reader who wants today's arithmetic runs the
**two** recipes beside `OkaTest/Axioms.lean`'s routing table — the one that resolves a guard name
to its module, and the one that attributes a guard to the heading above it. **The counts in the
paragraphs above are what those two returned at the commit each is pinned to**, and the reason to
prefer a member a reader can check to a cardinal they have to recount is
`OkaTest/Axioms/Analytification.lean`'s tower section's.

**The ledger of what has moved, in two rounds, because the second round found the first one's
values already stale.** Counted as `#print axioms` **names**, which here equals the command count,
at every figure below.

At `4c91029` five numerals had gone false and were repaired to *112*, *51*, *29*, *ten* and
*fifteen*, from *108*, *48*, *27*, *nine* and *fourteen*; all five had been right at `f63cb3a`,
which wrote them, and four guards added and none removed since —
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ext_of_toGlueData`,
`CategoryTheory.GlueData'.ext_of_heq`,
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_congr` and
`ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ` — accounted for every one of the five
deltas exactly, three of them under gluing headings and two outside `Oka/AnalyticSpace/`. **What
had made *48* uncheckable rather than merely stale is that the sentence listing the gluing
headings named four of them and the number counted five**, so a recount could not tell a wrong
number from a different partition; the list above is the five the number is of.

**Two of those five went stale again before `0ad0426` touched anything, and one of them was
never repaired at `4c91029` at all.** At `a4f3a81` the guard total is **122** and not *112*, and
the coproduct subtotal is **23** and not the *19* that has stood since `f63cb3a` — ten guards
arrived between `4c91029` and `a4f3a81`, four from lana-agents/oka#365 and six from
lana-agents/oka#380, and **only the four are under a coproduct heading**, which is why the
coproduct moved by exactly four and the gluing *51* did not move at all. The other six have a
heading of their own, and the last paragraph below is why every count of this file taken before
it charged them to the sheet comparison anyway. The *19* is the case this file's own warning
is about: it stood in the same clause as the *51*, was the same kind of number, and had simply not
moved yet when the clause was written.

**`0ad0426` added seven guards under one new heading and one new module**, so *112* → **129**,
seventeen headings → **eighteen** and eighteen modules → **nineteen**; the gluing *51*, the *29*
outside `Oka/AnalyticSpace/`, the *ten*, the *fifteen* and the *four* are all unmoved, because
`Oka/AnalyticSpace/Hausdorff.lean` is under `Oka/AnalyticSpace/` and none of its guards is under a
gluing or coproduct heading.

**Why every count above was wrong in the same place, and the one line that fixes it.** The
paragraph that stood here said six guards from `Oka/AnalyticSpace/OpenSubspace.lean` —
`ComplexAnalytic.AnalyticSpace.mono_ofRestrict`, `ComplexAnalytic.AnalyticSpace.liftTop`,
`ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict`,
`ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`,
`ComplexAnalytic.AnalyticSpace.isIso_liftTop` and
`ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top` — sat under
`### The sheet comparison is ℂ-linear`, which is about none of them, and had to be moved.
**They never sat there.** `3177e67` gave them a heading of its own,
`### The open subspace at an open that is everything`, and that section's own prose argues for
the placement in terms. What `3177e67` did not do is write the heading in the `/-! ### … -/`
form the rule beside `OkaTest/Axioms.lean`'s routing table asks for: it opened the doc comment
on one line and put the `###` on the next. **Every count this file has ever been given matches a
header by its opening delimiter and `###` on one line**, so all of them were blind to the
eighteenth heading and charged its six guards to the seventeenth. The repair is the one line that
pulls that `###` up onto the delimiter, and it moves no guard.

**This paragraph located that anchor in a per-heading `awk` in the recipe beside that table, and
there was no such `awk`.** That recipe resolves a guard *name* to its module and reads no heading
at all, so every count of this file had in fact been taken by an instrument written out on a
thread and kept nowhere — which is why each of them repeated the same blindness. There is a
per-heading recipe beside the table now; it matches a heading in either form, and
`.orchestra/validation.sh` rejects the second outright.

**Two numerals were wrong from `3177e67` for that one reason, and neither is the kind an author
is told to recheck.** The heading count, because a heading the instrument cannot see is not one
the author is warned they added: *sixteen* at `a4f3a81` where the file held seventeen, hence the
ledger row above reading *seventeen* where it should read **eighteen**. And the coproduct, whose
three headings held `8 + 11 + 4 = 23` at that repair, and `9 + 11 + 4 = 24` at `4853cc2` where
that clause was written — and which was read as *29*. Both were repaired there; the guard total
did not move, which is the check that no guard was touched, and it stood at *129* until the
disjoint union's `¬ IsIso` was added.

**So this is not the defect lana-agents/oka#358 repaired at `4c91029`, though it was filed as a
recurrence of it.** That one was a guard appended past a heading. `3177e67` appended a heading
too — it did the thing the rule asks for — and the counting still went wrong, one level down: **an
instrument blind to a heading reports a wrong partition for every section after it, and reports
it silently.** No checker in `scripts/` attributes a guard to a heading, so there is nothing to
harden there; the operative sentence is already in `OkaTest/Axioms.lean` and it already says
`/-! ### … -/`, on one line. What this file lacked was a reason to believe the form mattered.
`scripts/check_module_docstrings.py`'s own docstring has carried that reason since 2026-08-23: a
one-line grep for an opening delimiter carrying `##` returns 58 where its own predicate returns
59, and it names `Oka/LocalOkaRing.lean`, *"whose header is written across two lines"*, as the
file the grep cannot see.
The same has been true of this file since `3177e67`, across the one recount of it taken
since — `0ad0426`'s, which is where the *seventeen* above came from — and nobody joined the two
up.

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
`OkaTest/Axioms/Sheaves.lean` that is a two-line change.

**The clause *the only thing that uses it* has stopped being true, and the sentence is left
standing rather than repaired because `OkaTest/Axioms.lean` quotes it verbatim** — its routing
paragraph cites this heading as one of the two precedents for guarding a mirror-tree declaration
beside its consumer, and editing a quoted sentence silently breaks the quotation at the other
end. What falsifies it is `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_comp_eq`, declared in
the same mirror-tree file and proved from
`AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext`; it is guarded in
`OkaTest/Axioms/Morphisms.lean`, beside the statements about covers that are its only consumers,
which is this same practice rather than a departure from it. **The placement of the guard below
is unchanged** and its reason now reads *the only thing in this file's subject that uses it*. -/

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
info: 'ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ

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
info: 'ComplexAnalytic.isCLinearHom_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_ofRestrict

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
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.ext_of_toGlueData' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.ext_of_toGlueData

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

/--
info: 'ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_congr' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear_congr

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
info: 'CategoryTheory.GlueData.ofGlueData'_comm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.ofGlueData'_comm

/--
info: 'CategoryTheory.GlueData.comm_of_ofGlueData'_comm' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData.comm_of_ofGlueData'_comm

/--
info: 'CategoryTheory.GlueData'.ext_of_heq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GlueData'.ext_of_heq

/--
info: 'ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom

/-! ### Gluing a morphism

Two levels, and the second is not a special case of the first.
`ComplexAnalytic.AnalyticSpace.glueMorphisms` glues out of an **open cover** and asks for
agreement over a categorical pullback;
`AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms` glues out of a **gluing** and asks
for agreement over the glue datum's own overlaps, which is the only form a caller who built the
datum can state. `…GlueData.pullback_condition_of_comm` is the transport between them, through
`…GlueData.vIsoPullback` under the heading above.
-/

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

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.pullback_condition_of_comm' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.pullback_condition_of_comm

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.glueMorphisms

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_glueMorphisms' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_glueMorphisms

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext

/-! ### The disjoint union of a family of analytic spaces

`Oka/AnalyticSpace/Sigma.lean`. The object, its inclusions, the descent map, the two non-vacuity
statements at the two ends of the index type, and that an inclusion is not an isomorphism. -/

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
info: 'ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_isIso_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc

/-! ### The trivial `n`-sheeted cover, the descent map, and the inclusions

`Oka/AnalyticSpace/SigmaFiniteEtale.lean`. That finiteness and being a local isomorphism pass
from the members of a disjoint union to a descent map out of it; the trivial `ι`-sheeted cover
`∐_{i : ι} X ⟶ X` with its count of sheets; and the same two properties of the **inclusion** of a
member, which hold for every family and are the other direction — together with what that
inclusion's image being **clopen** gives: a disjoint union with two distinct inhabited members is
not preconnected. The header names the subjects rather than counting the guards, so appending one
does not falsify it. -/

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

/--
info: 'ComplexAnalytic.AnalyticSpace.isClosed_range_sigmaι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isClosed_range_sigmaι_base

/--
info: 'ComplexAnalytic.AnalyticSpace.isFinite_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFinite_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isClopen_range_sigmaι_base

/--
info: 'ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.not_preconnectedSpace_sigma


/-! ### The sheet comparison is `ℂ`-linear

`Oka/AnalyticSpace/InverseImageSheet.lean`. The `ℂ`-algebra half of
`AlgebraicGeometry.LocallyRingedSpace.sheetIso`, whose locally-ringed-space half is guarded in
`OkaTest/Axioms/Sheaves.lean`: the two structures the comparison relates, and that it and its
inverse respect them. -/

/--
info: 'ComplexAnalytic.comapAlgMap_sheetToBase' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_sheetToBase

/--
info: 'ComplexAnalytic.isCLinearHom_sheetHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_sheetHom

/--
info: 'ComplexAnalytic.isCLinearHom_sheetIso_inv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.isCLinearHom_sheetIso_inv

/--
info: 'ComplexAnalytic.comapAlgMap_sheetHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.comapAlgMap_sheetHom

/-! ### The open subspace at an open that is everything

`ComplexAnalytic.AnalyticSpace.ofRestrict` is guarded above; guarded here are
`ComplexAnalytic.AnalyticSpace.liftTop`, its section at an open that is everything, and the
statements that make the two invertible — that the inclusion is a monomorphism, that the section
is a section of it, and the two `IsIso` statements that follow — together with the factorisation
of a morphism through its own restriction over `⊤` that they exist for. **Named rather than
counted**, and every declaration this branch adds under `Oka/AnalyticSpace/OpenSubspace.lean` is
guarded here except `ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top`, which is a class
of morphisms and is in `OkaTest/Axioms/Morphisms.lean` with the finite étale one. **Appended as
its own section rather than folded into the open-subspace heading above**, for the reason the
sections above give: a section moved is a conflict for somebody else.

**`ComplexAnalytic.AnalyticSpace.liftTop` is a `def` and is guarded anyway, and an earlier head of
this branch left it out** — which made the sentence above false, since that sentence quantifies
over declarations and its own pull-request body counts this one among them. The rule it is guarded
under is the one `Oka/Analytification/RefineDatumToBase.lean`'s guards state in terms for
`ComplexAnalytic.refineDatumPresHom`: a definition advertised under a `## Main definitions`
heading is guarded even when it has no content of its own, and
`Oka/AnalyticSpace/OpenSubspace.lean` advertises this one. **That is not a claim about the whole
file**: `ComplexAnalytic.AnalyticSpace.resΓ` is advertised there too and is guarded nowhere, which
predates this branch and is not its to close.

`ComplexAnalytic.AnalyticSpace.mono_ofRestrict` is the one with a life outside this line — a
cancellation property of the inclusion at *every* open, which before this had to be routed through
`AlgebraicGeometry.LocallyRingedSpace` by hand. The consumers that asked are
`ComplexAnalytic.AnalyticSpace.isFinite_of_restrictHom_top` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_restrictHom_top`, both guarded in
`OkaTest/Axioms/Morphisms.lean` with the classes of morphisms rather than here.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.mono_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.mono_ofRestrict

/--
info: 'ComplexAnalytic.AnalyticSpace.liftTop' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftTop

/--
info: 'ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftTop_ofRestrict

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_liftTop' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_liftTop

/--
info: 'ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.liftTop_comp_restrictHom_top

/-! ### The analytic spaces this development constructs are Hausdorff

`Oka/AnalyticSpace/Hausdorff.lean`, the whole of it, appended as its own heading rather than under
one above: no heading above it names a separation property. **The clause that stood here said a
guard appended past the end of the file would have landed under the sheet comparison, and that
this is what had happened to the six guards below.** It had not; they have a heading of their own
and always did. See the last paragraph of the module docstring for what actually went wrong and
why this file's own counts could not see it.

**Every guard below is one `inferInstanceAs`**, so a guard here is a weak check by design —
what it defends is that no route to `T2Space` of a construction ever acquires an axiom, which is
exactly the failure a `sorry` in a subtype instance would produce.
`ComplexAnalytic.t2Space_analytification` is not here: it is `Oka/Analytification/Hausdorff.lean`'s
and is guarded in `OkaTest/Axioms/Analytification.lean` with the covering-map corollaries it exists
for. **That sentence called it *"the seventh"*, which the two sentences before it falsify** — the
whole of `Oka/AnalyticSpace/Hausdorff.lean` is guarded here and that instance is not in it, so the
ordinal counted a set it does not belong to; it is dropped rather than incremented, since no
ordinal was doing any work in it. It is a leftover from a six-instance draft.
-/

/--
info: 'ComplexAnalytic.t2Space_complexSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_complexSpace

/--
info: 'ComplexAnalytic.t2Space_restrict_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_restrict_complexAffineSpace

/--
info: 'ComplexAnalytic.t2Space_zeroLocusSubspace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_zeroLocusSubspace

/--
info: 'ComplexAnalytic.t2Space_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_restrict

/--
info: 'ComplexAnalytic.t2Space_complexAffineSpace' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_complexAffineSpace

/--
info: 'ComplexAnalytic.t2Space_zeroLocus' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_zeroLocus

/--
info: 'ComplexAnalytic.t2Space_node' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.t2Space_node

/-! ### The one-sheeted disjoint union is the space itself

`Oka/AnalyticSpace/Sigma.lean`'s uniqueness half of the universal property and the isomorphism it
buys at a subsingleton index type, together with `Oka/AnalyticSpace/SigmaFiniteEtale.lean`'s
reading of that at the fold map — the statement, its packaging as an isomorphism, the `simp` lemma
that lets the general round trip fire through a `def`, and the projection of the packaging.
Appended as its own section rather than merged into the disjoint-union sections above: moving or
reordering a section of this file is a conflict for every branch that has appended to it.

**What the guards below are a check of is one universal property.**
`ComplexAnalytic.AnalyticSpace.hom_ext_sigma` is
`CategoryTheory.Limits.Sigma.hom_ext` carried across
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`, and everything else here is that
lemma with `ComplexAnalytic.AnalyticSpace.sigmaι_sigmaDesc` and two-out-of-three for isomorphisms.
No structure sheaf is read anywhere in the section, which is the point of it:
`Oka/AnalyticSpace/SigmaFiniteEtale.lean` had recorded the fold map's case as absent and priced it
as a statement about the structure sheaves.

**`Classical.choice` is in every guard below and is not a surprise**: the disjoint union is built
by `ComplexAnalytic.AnalyticSpace.ofOpenCover` out of a gluing, and every statement here mentions
`ComplexAnalytic.AnalyticSpace.sigma`.

**Named and not located.** No sentence here says which section precedes or follows it.
-/

/--
info: 'ComplexAnalytic.AnalyticSpace.hom_ext_sigma' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.hom_ext_sigma

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_sigmaι' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_sigmaι

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaι_sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaι_sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.isIso_sigmaFold' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isIso_sigmaFold

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaFoldIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaFoldIso

/--
info: 'ComplexAnalytic.AnalyticSpace.sigmaFoldIso_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.sigmaFoldIso_hom

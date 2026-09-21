/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SimplyConnectedCriterion
import Oka.AnalyticSpace.ConnectedCover

/-!
# The first base whose fundamental group is trivial, and it is a point

`Oka/AnalyticSpace/SimplyConnected.lean` proves that over a base whose fundamental group at a point
is trivial every connected cover is the base over itself and every cover is a finite coproduct of
copies of it; `Oka/AnalyticSpace/SimplyConnectedCriterion.lean` proves the converse and makes the
two an `Iff`. **Neither has ever been applied to a base**, because at the commit this file is cut
from no base in this repository is known to satisfy the hypothesis — that is the first bullet of
both files' `## What is not here`, and this file is what retires the tree-wide half of it.

**The base is a point.** A base whose underlying space is a subsingleton has trivial fundamental
group at its point, and `ComplexAnalytic.AnalyticSpace.complexAffineSpace 0` is such a base. That
is the whole of what is closed here and the next section says it in the plainest terms available,
because a file with *simply connected* in its subject and a one-line proof at the end is the kind
of push a later run over-reads.

## What this closes is the trivial case, and nothing about a positive-dimensional base

**No base of positive dimension is shown to have trivial fundamental group below, and none is
claimed to.** `ℂ¹`, the unit disc and the punctured line are untouched. The punctured line's group
is **not** trivial — `OkaTest/FundamentalGroup.lean`'s `nontrivial_fundamentalGroup`, which is the
only other base at which this repository decides anything about this group — and this file does not
bear on it in either direction. **The interesting statement of this shape is that `ℂ¹` or a disc
has trivial fundamental group and that is a theorem nobody here has**; what is below is the base
over which the category of covers is as small as it can be while still having a point.

**What the push is for is that the implications stop being unwitnessed.** Four statements of the
two modules above have carried `[Subsingleton (…SeparatedFiniteEtaleOver.fundamentalGroup x)]` or
its equivalent as a hypothesis with nothing to discharge it;
`…SeparatedFiniteEtaleOver.exists_iso_coprod_id_originZero` below is the first place in this
repository where one of them is applied to a base rather than quantified over one.

## The mathematics is a finiteness and a discreteness, and no step of it is analytic

Fix a base `X` whose carrier is a subsingleton and a point `x` of it, and a cover `A` separated
over it and connected as an object of the category.

1. **`A`'s total space is finite.** The fibre over `x` is the whole of it — every point of the base
   equals `x`, so `Subtype.val` out of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber` is
   surjective — and a fibre is finite with no hypothesis at all, by the `Finite` instance
   `Oka/AnalyticSpace/FiniteEtaleOver.lean` declares beside that definition. This is
   `…SeparatedFiniteEtaleOver.finite_left_of_subsingleton_base` below and it reads no connectedness.
2. **`A`'s total space is a point.** It is connected, by
   `…SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace`'s forward direction
   (`Oka/AnalyticSpace/ConnectedCover.lean`); it is Hausdorff, by
   `…SeparatedFiniteEtaleOver.t2Space_left`; finite and Hausdorff makes it discrete, by Mathlib's
   `Finite.instDiscreteTopology` through the `T1Space` a `T2Space` supplies; and
   `PreconnectedSpace.constant` applied to the identity map of a connected discrete space says any
   two of its points are equal.
3. **So the fibre is a subsingleton and the cover is the base over itself.** That is the second
   half of `…SeparatedFiniteEtaleOver.nonempty_iso_id`'s proof, which reads the trivial group only
   through the subsingleton fibre it produces;
   `…SeparatedFiniteEtaleOver.nonempty_iso_id_of_subsingleton_fiber` below is that half stated on
   its own, at a general base, and it is the one statement here that is not about a subsingleton
   base at all.
4. **The criterion does the rest.**
   `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id` turns *every connected cover
   is the base over itself* into *the group is trivial*, and its hypothesis is exactly (3)
   quantified over `A`.

**Step (3) is why this file is not an append to either sibling.** The factorisation it needs —
the fibre-level statement without the group — does not exist in
`Oka/AnalyticSpace/SimplyConnected.lean`, and producing it there would change that module's four
declarations into five; and the criterion it consumes is declared one module later, so the
statement cannot sit before it either.

## The two topological hypotheses of this line come off here, and that is the reason for the shape

`[T2Space (X : Type u)]`, `[PreconnectedSpace (X : Type u)]` and `[Nonempty (X : Type u)]` are the
section variable of `Oka/AnalyticSpace/FundamentalGroup.lean`,
`Oka/AnalyticSpace/SimplyConnected.lean` and `Oka/AnalyticSpace/SimplyConnectedCriterion.lean`
alike. **Over a subsingleton base all three are free**, and each is one term:

* `T2Space` is `⟨fun _ _ h ↦ absurd (Subsingleton.elim _ _) h⟩` — two points that can be separated
  are distinct, and there are no distinct points;
* `PreconnectedSpace` is `⟨Set.subsingleton_univ.isPreconnected⟩`;
* `Nonempty` is `⟨x⟩`, the point the statement already takes.

**So the four statements below that are about an arbitrary base with at most one point bind
`[Subsingleton (X : Type u)]` and none of the three**, and a consumer supplies one instance where
the siblings ask for three. The other five bind neither way round: the fibre-level statement binds
two of the three and not `[Subsingleton]`, and the four declarations at `ℂ⁰` bind nothing, their
base being a fixed object rather than a variable.

**Neither of the first two terms is a declaration of this file.** Both are facts about an arbitrary
topological space with no analytic space in them, so a named version is mirror-tree material for
Mathlib rather than a result of this development, and nothing outside the proofs below wants
either. **They are `haveI` at the sites that need them and occur nowhere else in the tree, and the
two counts are not the same**: the `T2Space` term is at three sites and the `PreconnectedSpace`
term at four. The fourth is `…SeparatedFiniteEtaleOver.exists_iso_coprod_id_originZero`, whose base
is `ℂ⁰` rather than a variable and which therefore takes its separation from the instance
`ComplexAnalytic.t2Space_complexAffineSpace` and only its preconnectedness from the term above.
Four inline uses are no more of an argument for a named lemma than three.

## Why the witness is under `Oka/` where the punctured line's is under `OkaTest/`

`OkaTest/Axioms/Morphisms.lean` states the rule for the other witness on this line: of
`OkaTest/FundamentalGroup.lean`'s `nontrivial_fundamentalGroup` it says *"it is in the test library
because the object it is about is"* — that theorem is about `OkaTest/FiniteEtaleOver.lean`'s
`sqOver` over the punctured line, and both are test objects.
`ComplexAnalytic.AnalyticSpace.complexAffineSpace` is not: it is declared in
`Oka/AnalyticSpace/Basic.lean` and is read across the library. **So the same rule puts this witness
under `Oka/`**, and the guards for it under `OkaTest/Axioms/` with the rest of the library's.

## The names below, and the one whose discriminating suffix does not fit

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.` is **fifty-five** columns, a
`## Main results` entry has to carry the whole name — an elided one resolves against nothing, which
is the trap `Oka/AnalyticSpace/FundamentalGroup.lean` records at length — and `- `, the two
backticks and the `:` are **five** more, so a name in that namespace has **forty** columns before
the hundred-column limit `lake exe lint-style` enforces. **That budget is spent exactly in the list
below and not approximately**: `subsingleton_fundamentalGroup_originZero` is forty characters and
its entry there is a hundred columns on the nose, which is inside the limit with nothing left over.
Line length is a build linter here, so the figure is not advisory: a
forty-one-character name in this namespace, advertised, fails `lake build --wfail`. Six of the
seven names in that namespace below carry a suffix naming the hypothesis that distinguishes them;
the seventh cannot: `subsingleton_fundamentalGroup_of_subsingleton_base` is **fifty**. **It is
`…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup` and the base condition is an instance
argument**, which is the shape Mathlib omits from a name anyway and is the argument
`Oka/AnalyticSpace/SimplyConnected.lean` makes for its own four names; nothing else in this
repository carries that name, so nothing is ambiguous. **The suffixes are not dropped from the
other six**, because `…SeparatedFiniteEtaleOver.nonempty_iso_id` is already taken by the sibling
and a name that differed from it only by its instance arguments would be the worse choice.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.originZero`: **the point of `ℂ⁰`.** Written as the constant
  function for the reason `ComplexAnalytic.AnalyticSpace.origin` records at `ℂ¹` — the carrier is
  `ULift (Fin 0) → ℂ` only up to unfolding and instance search does not unfold it — and it is a
  separate name from that one because the two are points of two different spaces.
- `ComplexAnalytic.AnalyticSpace.subsingleton_complexAffineSpace_zero`: **`ℂ⁰` has at most one
  point.** The only `instance` below.

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_id_of_subsingleton_fiber`:
  **a connected cover with a subsingleton fibre at a point is the base over itself.** No
  subsingleton base and no fundamental group in it.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.finite_left_of_subsingleton_base`:
  **a cover over a base with at most one point has finite total space.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_left_of_subsingleton_base`:
  **and if it is connected its total space has at most one point.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_id_of_subsingleton_base`:
  **so a connected cover over such a base is the base over itself.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup`: **the
  fundamental group of a base with at most one point is trivial**, at the point it has.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_originZero`:
  **complex affine 0-space is such a base**, which is the witness this line has not had.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_iso_coprod_id_originZero`: **so
  every cover separated over it is a finite coproduct of copies of it over itself**, which is the
  third result of `Oka/AnalyticSpace/SimplyConnected.lean` applied to a base for the first time.

## The list above is written in full, and the one token in it that is not a name costs one row

Every head in the list above is the whole name, with the house `…` elision kept for the prose
outside it, because `scripts/guard_coverage.py` resolves a backticked token of a `## Main results`
section against the declaration dump and an elided one resolves to nothing. **The same tool counts
every backticked token of such a section that resolves to nothing**, whether it is an elided name
or notation, so `ℂ⁰` in a bullet raises the *backticked tokens skipped* row exactly as an elided
citation does. **The first draft of that section carried four and the row moved by four**; the
bullets above now carry the seven names **and one repository path**, and that path is the whole of
why the row moves by **one** instead of staying flat. `## What the census scripts return` below
prices it. **The row reads the same at every earlier head of this branch and moves at the one
that wrote the path in** — one fixed dump pair, each head's own tree — so this bullet is the only
thing on this branch that has ever touched it. That is what a citation in a bullet costs, and it is
cheap at the price: the bullet it buys names the module it points at instead of counting import
lines to it.
**The `## Main definitions` section above them is free to carry either, because that tool does not
read it** — the same fact read the other way, since a path written there could not have moved this
row at all.

## What the import costs, measured in the environment and not by a scan

**This file has two `import` lines and neither is in the other's closure.**
`Oka.AnalyticSpace.SimplyConnectedCriterion` brings **5027** modules at `d34b436` and
`Oka.AnalyticSpace.ConnectedCover` **5006**; the first does not contain the second and the second
does not contain the first, by a membership test over `Lean.Environment.allImportedModuleNames` at
each. **What the second adds to the first is exactly two modules** — itself and
`Oka.AnalyticSpace.EmptyBase`, which is its only `import` — so this module's own closure is
**5030**: the criterion's 5027, those two, and this module. **Those three totals are properties of
what this file imports and not of the tree**: the first two are the same run at `c6bfc1f` and at
`ef9e5d2`, three landings later, and the third is the same run at this head, which is the only
tree it can be taken in at all. **Neither can have moved at `6a792ba`, this branch's base now**:
`lana-agents/oka#616` is the only landing between the two and `git diff --name-only ef9e5d2
6a792ba` returns four prose files and neither root module, so no module enters or leaves any
closure — which is an argument and not a fourth run, and is labelled as one.
**One of the two is in the closure and is read by nothing below**, and the `## What is not here`
bullet on the empty base says why.

**The marginal cost to `import Oka` is nevertheless one module, and that is a run and not a diff**:
`import Oka` brings **5541** modules at `d34b436` and this push adds **one**, by a set difference
over `Lean.Environment.allImportedModuleNames`, and the one module the difference contains is this
one. **The total is what a landing moves and the one is not**: at `c6bfc1f` it is **5542** and at
`ef9e5d2` — two landings further on, one of which adds a module — it is **5543**, and at
`6a792ba`, this branch's base now, it is **5543** still for the reason above, while the same set
difference against this head is at every one of them the **one** module.
**No Mathlib module enters the closure**, and no `Oka` module does either — both imports were
already there, `Oka.lean` naming every module of the library. **A marginal import cost is a figure
about the importer at a commit and is meaningless without one**, which is why every total in this
section and the next names its commit by hash, and why what the two of them state about this push
is a delta.

## What the census scripts return

**Every row below is a total at `d34b436`, named by hash, and the delta this push adds to it**, and
**`d34b436` is an ancestor of this branch and no longer its parent** — the parent is `6a792ba` —
which costs the rows nothing, because a total at a hash is checkable from any base and that is the
whole reason they are written this way; what it does cost is one delta, three paragraphs down. And
**no row states a total at the commit that will add it**: that commit does not exist while this is
being written, and both earlier attempts at one were falsified by the next landing. The reason is
the one the section above gives of the marginal import cost — *a figure about the importer at a
commit is meaningless without one* — and it is as true of a tree-wide total as of a closure, which
this section learned the expensive way and then learned again. **Every row below stood unpinned
until 2026-09-21, and two successive landings falsified three of them**: `lana-agents/oka#606`
moved the backticked row by ten occurrences and one distinct name, and `lana-agents/oka#601` moved
it by a further eighty-seven and ten and moved both dump totals as well. The three read *the dump
total moves **4998 → 5007***, ***338274 → 338284***, and ***18161 (4421) → 18213 (4434)*** — each
of them a correct pair of runs at `a3d656d`, which was this branch's base for one round, and none
of them a statement anyone could check a week later. **Pinning the before-column by hash was not
enough, and that is why these rows are deltas and not pairs.** Until 2026-09-21 every row read
*before* at `d34b436` and *after* at the head that adds it, and an after-column is a claim about a
commit that does not exist while it is being written: `lana-agents/oka#610` landing as `6e0c610`
falsified the backticked row's, which read ***18258 (4432) → 18311 (4445)***, and by `c6bfc1f`, one
landing further on, eight more were false — both dump totals, the guard row, the advertised row and
its file count, *in both lists*, the *backticked tokens skipped* figure this section calls flat,
and the dotless row — without a line of this branch changing. **What no landing moves is an
*additive* delta**: the nine declaration rows, the ten environment rows and the fifty-seven
backticked occurrences this push adds are properties of the push rather than of any commit, and
that division is what every row below is built on. **A count of *distinct* names added is not of
that kind, and a landing has now moved one**: it is a set difference and not a sum, so it depends
on what the tree already cites in a way an occurrence count does not. **Of the thirteen distinct
names below, nine are this push's own declarations and no landing can pre-empt a name that does not
exist until this push writes it**; the other four are borrowed, and `lana-agents/oka#602` has since
taken one of the four. **Each additive delta is measured twice and the two agree**: once against
`d34b436` and once as the difference between `6a792ba` and this branch's head —
the nine, the ten, the nine, the seven, the one, the seven and the two are each the same
figure at both; **the distinct-name row is the exception and it is twelve at the second**, and the
occurrence, elided and dotless rows are runs at `6a792ba` alone, this push having reworded itself
after the landing. **The `scripts/guard_coverage.py` rows came through the first two
landings unmoved, and the two rows were flat for different reasons.** The module
`lana-agents/oka#601` adds carries **no** `#print axioms` and says so itself, so the guard row had
nothing to miss: the one occurrence of that string in the file is a prose bullet, which a `git
grep` counts and that script's comment-masked guard count does not. **The advertised row did have
something to miss**: that module's `## Main results` advertises five declarations it declares, and
the row misses them because that script's advertisement walk is the `Oka/` library and its root
module and reaches no `OkaTest/` file at all. **A row that happens to be flat is not a row that
cannot move, and a later landing moved both**: at `c6bfc1f` the guard row is **2023** and the
advertised row **1519** in **234** files, which is a landing and not this push, and this push's
deltas on them are what they are at `d34b436`.

`scripts/DumpOkaDecls.lean` writes **9** rows at this module — the nine declarations, with **no**
equation lemma, match lemma or congruence lemma — and the dump total is **5010** at `6a792ba`, to
which this push adds **9**; it was **5003** at `d34b436` and the **9** was the same there.
`scripts/DumpEnvNames.lean` is **338289** here and **338280** there, and this push adds **10** at
both, which is those nine declarations and this one module and nothing else.

`scripts/guard_coverage.py` adds **9** guards under `OkaTest/Axioms/` to the **2028** at
`6a792ba`, all nine in `OkaTest/Axioms/Morphisms.lean`; **7** advertised in a `## Main results` to
**1523**, in **1** file to **235**; **7** *in both lists* to **1381**; and **2** *guarded and
advertised nowhere* to **647**, which is the two names of `## Main definitions` above, a section
that script does not read. **`Δguards = Δ(in both) + Δ(nowhere)` closes at `9 = 7 + 2`**, and it
closed on the same three deltas at `d34b436`, where the four totals were **2021**, **1517** in
**233**, **1375** and **646** — which is a thing a pair of totals cannot say. The *unguarded* row
is **flat** on **142, in 60 files**, *advertised from another file* flat on **89**, *abbreviated
citations, not counted* flat on **30, four of them dotted**, and *backticked tokens skipped*
**1 / 132 / 721** to **1 / 132 / 722**. **Flat is the delta and not the total**: the last of those
four reads **1 / 132 / 719** at `d34b436`, moved by a landing and not by this push. **The one this
push adds to it is a repository path and not a name**, written into the `## Main results` list
above by the round that stopped reaching a module by its distance in the import chain: that script
counts a backticked path among the tokens it cannot resolve, and the docstring-name checker does
not read it at all, the slashes putting it outside that population. **`## Main results` is the only
section the row can be moved from**, the count being over the backticked tokens of those sections
and of nothing else, so the section that names the list is the section that pays.

`scripts/check_docstring_names.py` is **18451 (4481)** backticked names at `6a792ba` and this push
adds **58 occurrences and 12 distinct names**; elided citations are **408 (175)** there and it adds
**51 and 10**; **0** are unresolved and **6** resolve under more than one namespace at both ends of
both. **The backticked total is the one figure of this section that `lana-agents/oka#616` moved**,
by **two occurrences and one distinct name**, `Function.pullbackDiagonal` in
`Oka/Topology/SeparatedMap.lean`; it moved no delta of this push, and the elided total it did not
move at all. **The elided delta is 51 and was 49 at the previous head**: the round that wrote this
sentence spells `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id` twice more —
once in the guard section's account of what consumes the borrowed name and once in this sentence —
and that is a name the tree already elides, so the occurrence half moved and the distinct half did
not, which is the same asymmetry the backticked side records two sentences below at the other end.
**The occurrence delta on the backticked side moved for the same reason**, from **57** to **58**,
and the two figures this paragraph adds to itself are counted rather than excused.
**The distinct half is the one row of this section that a landing moved, and it is the only row
that is not a sum**: `--diff` returns **12 added and 0 removed** on the backticked side — the
nine declarations below, `Finite.instDiscreteTopology`, `PreconnectedSpace.constant` and the module
name `Oka.AnalyticSpace.EmptyBase`, which is not an `import` of this file at all but the only one
of the other. **It was 13 while this branch was cut from `d34b436`**, the thirteenth being
`Oka.AnalyticSpace.SimplyConnectedCriterion`, one of this file's two `import` lines, which
`lana-agents/oka#602` has since backticked in `Oka/AnalyticSpace/SimplyConnectedCoprod.lean`; so it
is a name the tree already cites and this push no longer adds it. **The other three of the four
borrowed names are uncited elsewhere at this base and the nine cannot be cited at all before this
push writes them**, which is why one row moved and not the whole side. The elided side is **10
added and 0 removed** at both bases, the nine declarations again in their elided spelling and
`…FiniteEtaleOver.fiber`.
**`Oka.AnalyticSpace.ConnectedCover`, which is this file's other `import`, is cited in this file as
well — **three** times at this head, against `Oka.AnalyticSpace.EmptyBase`'s **three** and
`Oka.AnalyticSpace.SimplyConnectedCriterion`'s **four** — and is not among the twelve**: the
tree backticks it already at `d34b436`, twice in
`Oka/AnalyticSpace/ConnectedCover.lean` and once in `OkaTest/Axioms/Morphisms.lean`, and those
three are still the three at `6a792ba`. **A name the tree already cites adds nothing to the
distinct count however often a new file cites it**, which is the whole of what separates the two
halves and is why this row cannot be read off the list of what this file spells. **That is what
happened to `Oka.AnalyticSpace.SimplyConnectedCriterion` between two of this branch's bases**, and
the clause about `Oka.AnalyticSpace.ConnectedCover` was already the general statement of it: a
borrowed name is one a landing can take, and only the nine below are safe from that. **The per-file
figure is the head's and not the draft's, and saying so is not pedantry**: until the round that
wrote this sentence the three were cited once each here and the clause read *once*, which spelling
all three names in it made false in the act of writing it — the same shape as the dated record two
sentences below, one turn tighter, and a count inside a clause is as much a fixed point to check as
a row. The occurrence halves are larger than the distinct ones because most of these names are
cited more than once, which is what a citation count is for. **The dotless row is 246 (125) at
`6a792ba` — 240 (120) at `d34b436` — and this push adds 2 (2) at either, and the two are this
sentence's own**: a first draft of the
paragraph above carried `…nonempty_iso_id` and a first draft of the guard section `…originZero`,
each of which elides a prefix of a component rather than a namespace and each of which moved the
row by one; both were repaired to the dotted spelling, and what this push adds to the row is the
two quotations in this sentence and no live citation. **A dated record that quotes what it retires
moves the count the retirement was for**, which is a shape this repository has met before in its
sweeps and is worth publishing rather than rounding away.

**Both halves of every figure in this section are runs** — the total in a worktree at `d34b436` and
the delta as the difference between two of them — the base column taken by running the base
worktree's own copy of each script rather than the head's: both set their repository root from
`os.path.abspath(__file__)` and not from the working directory, so the head's copy run inside a
base worktree returns the head's guard count against the base's advertised count.

## What is not here

* **No positive-dimensional base, and no claim about one.** Said at length two sections into this
  docstring, and repeated here because it is the one thing about this file that a later run can get
  wrong: `ℂ⁰` is the base below and `ℂ¹` is not.
* **No count of the index type.** `…SeparatedFiniteEtaleOver.exists_iso_coprod_id_originZero`'s
  index type is existential, exactly as the theorem it instantiates leaves it, and nothing below
  relates it to a fibre cardinality or to a degree. `Oka/AnalyticSpace/SimplyConnected.lean`'s own
  `## What is not here` says the same of the theorem and that bullet is untouched.
* **No transport is consumed.**
  `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_congr` and its positive form now have a
  base they could be applied to, and nothing below applies them: at a subsingleton base every point
  is every other point, so the transport carries nothing that `Subsingleton.elim` does not.
* **Nothing about the empty base.** `Oka/AnalyticSpace/EmptyBase.lean`'s
  `…SeparatedFiniteEtaleOver.isoIdOfIsEmpty` says every cover over a base with **no** points is the
  base over itself, which is a statement about a base at which no fibre functor and no fundamental
  group can be formed at all — the group below is taken at a point and an empty base has none.
  Neither module imports the other and nothing below reads that theorem.
* **No comparison with the topologist's fundamental group**, and nothing about
  `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`, which is in this repository's
  import closure already and which neither this file nor its two siblings mention in any statement.
  `Oka/AnalyticSpace/FundamentalGroup.lean`'s `## What is not here` records that nothing relates the
  two groups and nothing below relates them either.
* **Nothing about `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`.** Every statement below is at the
  *separated* covers, which is where the `CategoryTheory.GaloisCategory` instance is and therefore
  where the group is; `…SeparatedFiniteEtaleOver.finite_left_of_subsingleton_base` reads
  `…FiniteEtaleOver.fiber` through the forgetful functor and states nothing at the ambient category.
* **No second witness and no classification of the covers of `ℂ⁰`.** What is proved is that the
  group is trivial, not that the category is `FintypeCat`: the coproduct statement is existential in
  its index type, no equivalence of categories is stated, and no cover of `ℂ⁰` is exhibited.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}}

section Fibre

variable [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)] [Nonempty (X : Type u)]

omit [Nonempty (X : Type u)] in
/-- **A connected cover whose fibre at a point is a subsingleton is the base over itself.**

This is the second half of `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.nonempty_iso_id`
stated on its own. That theorem's hypothesis is a trivial fundamental group and the only thing its
proof does with it is produce a subsingleton fibre, through
`…SeparatedFiniteEtaleOver.subsingleton_fiber`; everything after that is this proof, verbatim.
**Nothing here mentions the group and nothing here asks the base to have at most one point** — the
statement is about one cover and one point, and it is the rung the rest of this file feeds.

The fibre is non-empty by `CategoryTheory.PreGaloisCategory.nonempty_fiber_of_isConnected`, so it
is terminal in `FintypeCat` (`…SeparatedFiniteEtaleOver.isTerminalFintypeFiber`); the fibre of the
base over itself is terminal too (`…SeparatedFiniteEtaleOver.isTerminalFintypeFiberId`); the
morphism `…SeparatedFiniteEtaleOver.isTerminalId` supplies is therefore an isomorphism on fibres by
`CategoryTheory.Limits.IsTerminal.hom_ext` in each direction, and the fibre functor reflects
isomorphisms.

**`[Nonempty (X : Type u)]` is `omit`ted and that is not an economy**: the section variable of the
two sibling modules carries it, this proof never reads it, and leaving it bound would make the
telescope of this statement differ from what it needs. -/
theorem SeparatedFiniteEtaleOver.nonempty_iso_id_of_subsingleton_fiber (x : X)
    (A : SeparatedFiniteEtaleOver.{u} X) [PreGaloisCategory.IsConnected A]
    [Subsingleton ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A)] :
    Nonempty (A ≅ SeparatedFiniteEtaleOver.id.{u} X) := by
  haveI : Nonempty ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :=
    PreGaloisCategory.nonempty_fiber_of_isConnected _ A
  set f : A ⟶ SeparatedFiniteEtaleOver.id.{u} X :=
    (SeparatedFiniteEtaleOver.isTerminalId.{u} X).from A with hf
  have hiso : IsIso ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).map f) :=
    ⟨(SeparatedFiniteEtaleOver.isTerminalFintypeFiber.{u} x A).from _,
      (SeparatedFiniteEtaleOver.isTerminalFintypeFiber.{u} x A).hom_ext _ _,
      (SeparatedFiniteEtaleOver.isTerminalFintypeFiberId.{u} x).hom_ext _ _⟩
  haveI : IsIso f := isIso_of_reflects_iso f (SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x)
  exact ⟨asIso f⟩

end Fibre

section SubsingletonBase

variable [Subsingleton (X : Type u)]

/-- **A cover over a base with at most one point has finite total space.**

The fibre over the point is the whole of the total space, because every point of the base is that
point: `Subtype.val` out of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber` is surjective,
with `Subsingleton.elim` discharging the membership. The fibre itself is finite with no hypothesis
at all — not a separation axiom, not connectedness, nothing about the base — by the `Finite`
instance `Oka/AnalyticSpace/FiniteEtaleOver.lean` declares beside that definition.

**The lambda writes its domain as `…FiniteEtaleOver.fiber` and it has to.** That name is a `def`
and instance search does not unfold it, so a `Function.Surjective` stated at `Subtype.val` unfolds
to the subtype and the `Finite` instance is then not found; naming the fibre keeps it.

**Nothing here is about connectedness**, which is why this is a statement of its own rather than a
step of the next one: it is true of every cover over such a base, including the empty one. -/
theorem SeparatedFiniteEtaleOver.finite_left_of_subsingleton_base (x : X)
    (A : SeparatedFiniteEtaleOver.{u} X) : Finite (A.left : Type u) :=
  Finite.of_surjective
    (fun b : FiniteEtaleOver.fiber.{u} x ((SeparatedFiniteEtaleOver.toFiniteEtaleOver X).obj A) ↦
      (b.1 : (A.left : Type u)))
    fun a ↦ ⟨⟨a, by simp only [Set.mem_preimage]; exact Subsingleton.elim _ x⟩, rfl⟩

/-- **A connected cover over a base with at most one point has at most one point.**

Four facts, and none of them is analytic. The total space is connected, by
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.connectedSpace_of_isConnected` — the half
of `…SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace` that goes from the categorical
condition to the topological one. It is Hausdorff, by `…SeparatedFiniteEtaleOver.t2Space_left`. It
is finite, by the theorem above. And finite plus `T1` is discrete (`Finite.instDiscreteTopology`),
while a connected discrete space has one point, by `PreconnectedSpace.constant` at the identity
map — the target of that lemma is any discrete space and taking it to be the space itself is what
turns *every continuous map to a discrete space is constant* into *any two points are equal*.

**The two topological hypotheses the cited theorems ask of the base are supplied here and not
bound.** `T2Space` and `PreconnectedSpace` of a subsingleton are one term each and are written
inline; `Nonempty` is the point this statement already takes. That is what lets the statement bind
`[Subsingleton (X : Type u)]` alone. -/
theorem SeparatedFiniteEtaleOver.subsingleton_left_of_subsingleton_base (x : X)
    (A : SeparatedFiniteEtaleOver.{u} X) [PreGaloisCategory.IsConnected A] :
    Subsingleton (A.left : Type u) := by
  haveI : T2Space (X : Type u) := ⟨fun _ _ h ↦ absurd (Subsingleton.elim _ _) h⟩
  haveI : PreconnectedSpace (X : Type u) := ⟨Set.subsingleton_univ.isPreconnected⟩
  haveI : Nonempty (X : Type u) := ⟨x⟩
  haveI : ConnectedSpace (A.left : Type u) :=
    SeparatedFiniteEtaleOver.connectedSpace_of_isConnected.{u} A
  haveI : Finite (A.left : Type u) :=
    SeparatedFiniteEtaleOver.finite_left_of_subsingleton_base.{u} x A
  haveI : DiscreteTopology (A.left : Type u) := Finite.instDiscreteTopology
  exact ⟨fun a b ↦ PreconnectedSpace.constant (α := (A.left : Type u)) inferInstance
    continuous_id (x := a) (y := b)⟩

/-- **A connected cover over a base with at most one point is the base over itself.**

The theorem above makes the total space a subsingleton, so the fibre is one — a fibre is a subtype
of the total space, and `Subtype.ext` is what carries it, instance search not unfolding
`…FiniteEtaleOver.fiber` far enough to see it — and the first theorem of this file finishes.

**This is the hypothesis of `…SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id`,
quantified over the cover**, and the next theorem is nothing but that observation. -/
theorem SeparatedFiniteEtaleOver.nonempty_iso_id_of_subsingleton_base (x : X)
    (A : SeparatedFiniteEtaleOver.{u} X) [PreGaloisCategory.IsConnected A] :
    Nonempty (A ≅ SeparatedFiniteEtaleOver.id.{u} X) := by
  haveI : T2Space (X : Type u) := ⟨fun _ _ h ↦ absurd (Subsingleton.elim _ _) h⟩
  haveI : PreconnectedSpace (X : Type u) := ⟨Set.subsingleton_univ.isPreconnected⟩
  haveI := SeparatedFiniteEtaleOver.subsingleton_left_of_subsingleton_base.{u} x A
  haveI : Subsingleton ((SeparatedFiniteEtaleOver.fintypeFiberFunctor.{u} x).obj A) :=
    ⟨fun a b ↦ Subtype.ext (Subsingleton.elim (α := (A.left : Type u)) _ _)⟩
  exact SeparatedFiniteEtaleOver.nonempty_iso_id_of_subsingleton_fiber.{u} x A

/-- **The fundamental group of a base with at most one point is trivial.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id`
fed by the theorem above. **This is the statement the two modules before this one have been unable
to discharge anywhere**, and the module docstring says why the base condition is not in the name.

**It takes a point of the base and it has to**: the group is the automorphism group of the fibre
functor at a point, so there is no group to speak of without one, and a subsingleton base with no
point is the empty base, where `Oka/AnalyticSpace/EmptyBase.lean` says something else. -/
theorem SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup (x : X) :
    Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} x) := by
  haveI : T2Space (X : Type u) := ⟨fun _ _ h ↦ absurd (Subsingleton.elim _ _) h⟩
  haveI : PreconnectedSpace (X : Type u) := ⟨Set.subsingleton_univ.isPreconnected⟩
  haveI : Nonempty (X : Type u) := ⟨x⟩
  exact SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_of_iso_id.{u} x
    fun A _ ↦ SeparatedFiniteEtaleOver.nonempty_iso_id_of_subsingleton_base.{u} x A

end SubsingletonBase

/-- **The point of `ℂ⁰`.**

Written as the constant function rather than as `0` for the reason
`ComplexAnalytic.AnalyticSpace.origin` records at `ℂ¹`: the carrier of
`ComplexAnalytic.AnalyticSpace.complexAffineSpace 0` is `ULift (Fin 0) → ℂ` only up to unfolding
and instance search does not unfold it, while a lambda elaborates against the unfolded expected
type. **The lambda is never applied** — its argument type is empty — so the `0` in it is there to
make the term total and is not a choice of point; the instance below says there is nothing to
choose. -/
def originZero : (complexAffineSpace.{u} 0 : Type u) := fun _ ↦ 0

/-- **`ℂ⁰` has at most one point.**

Its carrier is a function type out of `ULift (Fin 0)`, which is empty, and two functions out of an
empty type are equal. `inferInstanceAs` is what crosses the seam between the carrier as an analytic
space and that function type, which is the same seam
`ComplexAnalytic.AnalyticSpace.origin`'s docstring records one dimension up.

**This is the only `instance` in this file**, and it is one because every statement above takes the
condition as an instance argument. -/
instance subsingleton_complexAffineSpace_zero :
    Subsingleton (complexAffineSpace.{u} 0 : Type u) :=
  inferInstanceAs (Subsingleton (ULift.{u} (Fin 0) → ℂ))

/-- **The fundamental group of `ℂ⁰` is trivial** — the first base in this repository for which
that is known.

The theorem above at `ComplexAnalytic.AnalyticSpace.originZero`, with the instance above supplying
its only hypothesis. **The base is a point and the module docstring says at length what that does
and does not close**; in particular nothing here bears on `ℂ¹`, on a disc, or on
`OkaTest/FundamentalGroup.lean`'s punctured line, whose group is not trivial. -/
theorem SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_originZero :
    Subsingleton (SeparatedFiniteEtaleOver.fundamentalGroup.{u} originZero.{u}) :=
  SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup.{u} originZero.{u}

/-- **Every cover separated over `ℂ⁰` is a finite coproduct of copies of `ℂ⁰` over itself.**

`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_iso_coprod_id` applied to a base,
which is the first time in this repository that any statement of the simply-connected line is
applied to one rather than quantified over one. The three instances its telescope asks of the base
are supplied here: `T2Space` is already an instance at `ℂⁿ`
(`ComplexAnalytic.t2Space_complexAffineSpace`), `PreconnectedSpace` is the subsingleton term this
file uses three times above — **this is its fourth and last site, and the docstring's count of
four is this one included** — `Nonempty` is `…AnalyticSpace.originZero`, and the trivial group is
the theorem above.

**The index type is existential and nothing below counts it.** That is exactly what the theorem
being instantiated says and the module docstring's `## What is not here` repeats it. -/
theorem SeparatedFiniteEtaleOver.exists_iso_coprod_id_originZero
    (A : SeparatedFiniteEtaleOver.{u} (complexAffineSpace.{u} 0)) :
    ∃ (ι : Type) (_ : Finite ι),
      Nonempty (A ≅ ∐ fun _ : ι ↦ SeparatedFiniteEtaleOver.id.{u} (complexAffineSpace.{u} 0)) := by
  haveI : PreconnectedSpace (complexAffineSpace.{u} 0 : Type u) :=
    ⟨Set.subsingleton_univ.isPreconnected⟩
  haveI : Nonempty (complexAffineSpace.{u} 0 : Type u) := ⟨originZero.{u}⟩
  haveI := SeparatedFiniteEtaleOver.subsingleton_fundamentalGroup_originZero.{u}
  exact SeparatedFiniteEtaleOver.exists_iso_coprod_id.{u} originZero.{u} A

end ComplexAnalytic.AnalyticSpace

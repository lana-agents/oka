/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.Axioms.AnalyticSpace
import OkaTest.Axioms.Analysis
import OkaTest.Axioms.Analytification
import OkaTest.Axioms.ComplexSpace
import OkaTest.Axioms.CutOut
import OkaTest.Axioms.LocalOkaRing
import OkaTest.Axioms.MainTheorem
import OkaTest.Axioms.Morphisms
import OkaTest.Axioms.RingTheory
import OkaTest.Axioms.SheafOfModules
import OkaTest.Axioms.Sheaves
import OkaTest.Axioms.Weierstrass

/-!
# Axiom regression test

The library is `sorry`-free, and its results rest only on the three standard axioms of Lean:
`propext`, `Classical.choice` and `Quot.sound`. A `sorry` is only a warning, not an error, so
nothing in an ordinary `lake build` would notice if one were reintroduced — the proof of a
theorem depending on it would simply start depending on `sorryAx` as well.

The files imported above pin that down: each `#guard_msgs` in them fails the build if the axiom
dependencies of the named theorem ever change. Together with the `sorry` grep in
`.github/workflows/lean_action_ci.yml` that is what keeps the completeness claim in `README.md`
honest.

These files are not part of the `Oka` library; they are the `OkaTest` library of
`lakefile.toml`, whose `globs = ["OkaTest.+"]` picks up every module under `OkaTest/` and which
`defaultTargets` also builds, so plain `lake build` exercises them. Adding a file under
`OkaTest/Axioms/` therefore needs no change to `lakefile.toml`. The layout follows Mathlib's own
`MathlibTest`: a test library must live in a directory of its own, outside the source tree of
the library it tests, or Lake rejects its imports.

## Where to put a new assertion

**Add it to the file for its topic, under the matching `/-! ### … -/` heading, and if there is
no such file, add a new one and one import line here. Never append to whichever file you
happened to open.**

| topic | file |
| --- | --- |
| Oka's theorem and the coherence of `𝒪_X` | `OkaTest/Axioms/MainTheorem.lean` |
| Weierstrass division and preparation | `OkaTest/Axioms/Weierstrass.lean` |
| complex analysis, `π₁(ℂ ∖ {0})`, and polynomial zero loci | `OkaTest/Axioms/Analysis.lean` |
| `LocalOkaRing`: Rückert, maximal ideal, regularity | `OkaTest/Axioms/LocalOkaRing.lean` |
| `OkaRing` and the structure sheaf of `ℂ^ι` | `OkaTest/Axioms/ComplexSpace.lean` |
| analytification, and the comparison morphisms to `Spec` | `OkaTest/Axioms/Analytification.lean` |
| general presheaf and sheaf theory, and ringed spaces | `OkaTest/Axioms/Sheaves.lean` |
| sheaves of modules and coherence | `OkaTest/Axioms/SheafOfModules.lean` |
| zero loci and closed immersions | `OkaTest/Axioms/CutOut.lean` |
| analytic spaces, local models, the node | `OkaTest/Axioms/AnalyticSpace.lean` |
| morphisms of analytic spaces | `OkaTest/Axioms/Morphisms.lean` |
| general commutative ring theory | `OkaTest/Axioms/RingTheory.lean` |

That rule is the whole point of the split, and it is not a matter of taste. Until 2026-08-20
every assertion lived in this one file and every pull request appended to its end, so git
reported a conflict between *any* two concurrent pull requests: only one could merge per rebase
round, and each of the others needed a rebase, a force-push, a re-`attach_pr` and a fresh
review of a tree whose library files were byte-identical to the one already approved. That cost
four such cycles in a single morning. Issue #558's append-at-the-end convention reduced the
damage but could not remove it, because two additions at the end of a file still collide.
Concurrent pull requests that touch *different files* do not. See issue #640.

**Every row above has been measured against the guards it routes to, and here is how to
re-measure one.** For each row, resolve every `#print axioms` name in its file to the module the
declaration lives in, and ask whether the row's phrase covers what comes back. In a built
checkout, with the dump taken **after** `lake build` and on the branch being measured — `lake env
lean` reads the oleans, so a dump taken across a branch switch is the other branch's:

    OKA_DECL_DUMP=/tmp/d.txt lake env lean scripts/DumpOkaDecls.lean
    perl -0777 -ne 'while(/^[ \t]*#print axioms(?:[ \t]+|[ \t]*\n[ \t]+)(\S+)[ \t]*$/mg)
        { print "$1\n" }' OkaTest/Axioms/<File>.lean | sort -u |
      while read -r n; do awk -F'\t' -v n="$n" '$2==n {print $1; exit}' /tmp/d.txt; done |
      sort | uniq -c | sort -rn

**The `perl` is not decoration.** The obvious `grep -oP '(?<=#print axioms ).*'` misses a guard
whose name is wrapped onto the next line, and this directory has such guards today; a census
taken that way comes out short of `scripts/guard_coverage.py`'s by one for each of them, and that
script is where the regular expression above is from. **This clause read *"there is one such
guard today, in `OkaTest/Axioms/SheafOfModules.lean`"* and on 2026-09-04 there were four of them
in three files**, so it had stopped being true — exactly what the *name rather than count* rule
below forbids, in the paragraph that states the recipe. A row is wrong when some module's guards
are covered by no row at all — that is the failure this table exists to prevent — and not merely
when its phrase is shorter than the file.

**A second recipe, for the other question the rule above raises: which *heading* a guard sits
under.** The one above resolves a guard to its module; this one counts guards per section, which
is what a module docstring's subtotals are of and what nothing in `scripts/` reads:

    awk '/^\/[-]! ### /{if(h!="")print n"\t"h; h=$0; n=0; next}
         /^### /        {if(h!="")print n"\t"h; h=$0; n=0; next}
         /^#print axioms/{n++}
         END{print n"\t"h}' OkaTest/Axioms/<File>.lean

**The bracket in the first pattern is a Lean requirement and not an awk one.** This file is
itself a doc comment and Lean's block comments nest, so spelling the opening delimiter literally
here would open a comment that never closes; at a shell you would type it without the brackets.
**Neither of the two oddities that are awk's is optional and both were paid for.** The trailing
space in the first pattern is what stops a `####` sub-heading opening a section of its own —
there are two today — and without it `OkaTest/Axioms/Morphisms.lean` comes out with one section
too many: the sub-heading gets a row of its own and its guards are subtracted from the `###`
section that contains them, so two rows are wrong and the total is right, which is the shape
that survives an append and is why no numeral is given here. The second pattern, matching
a heading on a line of its own, is what sees one whose author opened the doc comment on one line
and wrote the `###` on the next: that form elaborates identically, and a recipe blind to it
charges the heading's guards to the *previous* one and reports a wrong partition from there to
the end of the file, silently. **That is how `OkaTest/Axioms/AnalyticSpace.lean`'s docstring came
to give a coproduct subtotal of *29* for a partition holding 23.**
`.orchestra/validation.sh` now rejects the two-line form, so the second pattern is a fallback
rather than a licence, and the check there says why it is a `grep` and not a comparison of these
counts.

**The worked example is `OkaTest/Axioms/AnalyticSpace.lean`**, the only file here whose
per-heading distribution has been checked against its own prose — and checked more than once,
because each reconciliation had gone stale before the next was taken. Run the `awk` above to get
today's partition; that file's docstring carries the ledger of those recounts and says in terms
which of its numerals are records pinned to a commit and which are undated claims about the tree
that go stale. The two rows worth knowing before you run it are the sheet comparison
and the open subspace at `⊤`: while the second heading stood in the two-line form `3177e67`
wrote it in, every count of that file charged its guards to the first, because no instrument then
in use could see it.

**Prose about a section should name rather than count, and this file is not exempt.** A clause
that counts the declarations of a file or the guards of a section is falsified by the next append
to either, and nothing in `scripts/` can tell such a clause from a sentence that happens to
contain a number, so the only defence is how the sentence is written. A section's opening should
name the file whose declarations are guarded and the files the rest were written in; a reader who
wants the arithmetic can run `grep -c '#print axioms'` over the section and get an answer that is
right on the day they run it. **A spelling is exempt when it cannot rot.** A figure
pinned to a commit or a date is a record — which is what the measurements further down are, and
they say so — and so is a numeral about a repair that has already landed, since falsifying either
means rewriting history rather than appending. **Rotting slowly is not the same as not rotting**,
and a *proportion* is the shape that tests the difference. *Most of them*, *the bulk of*, *the
largest member* name no member and give no total, so the append that falsifies one is usually not
the next one — which is why the mechanism above does not reach it — and when it comes it is as
silent as a count's, with nothing in `scripts/` to answer it, since the population has to be
classified by hand before it can be measured. **A proportion is therefore not exempt, and it is
not one of the objects above either**, which count; what it is owed is the naming form, for the
reason the redundancy exemption below gives. **Argued at taxis #1721**, which measured the shape
under the guard files and under `Oka/` and found it live in both; the comparative spelling read as
absent from the tree until the second of those was scanned, which is the fence and not the tree.
**The rule was first written into the guard section next to the one that carried the defect** —
`OkaTest/Axioms/Analytification.lean`'s *The refined datum refines across members, and the two
members meet in nothing else*, which was created already in the naming form and whose opening
names the files its guards were written in and counts none of them. The section that carried the
defect is the one immediately above it, whose clause enumerating six of its seven guards had been
repaired by a separate branch the same day. **That opening is the
spelling to copy.** The rule is repeated here because this is the file every author of a new guard
section reads, and because when it was written this file was itself carrying counts of the class —
the wrapped-guard clause in the `perl` paragraph, the section count in the `awk` paragraph, and the
row total in the worked example — and **on 2026-09-04 all three were false**. Only the first leaves
a record, quoted and dated where it stood; the other two sentences were rewritten to carry no
figure at all. **Do not answer this with a checker** — it would have to guess which numbers in a
docstring are censuses, and `scripts/` has no way to tell.

**A numeral that totals a naming the same passage gives is exempt too, and by a mechanism
different from the ones above.** Those work by being about the past. This one works by being
redundant: *the four results of such-and-such a module*, with the four then named or described in
the same breath, adds nothing to the naming beside it — and naming is what the rule asks for in
the first place. Strike the numeral and the same append leaves the same passage stale, in the same
place, saying the same wrong thing; so the numeral is a way of writing the list and not a second
claim about the section. **What this is not is a promise that such a clause stays true.** It goes
false exactly when the naming goes false, and a naming that has gone false is a sentence that is
wrong about *what is there* — which is the failure this rule is content to have, and the opposite
of a count that goes wrong while every word around it still reads.

**The corollary is the one that costs triage time.** A *the two*, *both* or *the pair* is out of
class only when the passage accounts for both. Where it instead counts a section's contents by
kind and names none of them — *the definition is guarded and not only the two theorems* — a third
theorem appended falsifies it in silence, and it is a census clause like any other. **Which kind a
clause is has to be read and cannot be matched**, so the refusal of a checker above covers this
exemption as much as the rule it qualifies.

**An audit paragraph is exempt through the pinning spelling and not because it is an audit**, and
the case that settled it is `OkaTest/Axioms/AnalyticSpace.lean`'s module docstring. That block is
a ledger of numerals that had gone false — which commit falsified each, and the instrument bug
that made a whole partition wrong — and it argued in terms for its own undated counts, telling a
reader that the list to recheck after adding a guard was every one of them. **At `883b62f` those
counts had rotted in four places**, one of them inside the ledger itself, written as what three
headings *hold now*; and all four were already false when the sweep that reached that file fenced
the block rather than touching it, so the rechecking the paragraph asked for is what did not
happen. **A paragraph whose subject is rot gets no licence to carry it.** The way to keep such a
record is to pin every figure in it to the commit it was measured at, which is what that file now
does, and the two rules then agree instead of having to be ranked. **The exemption attaches to a
figure and not to the paragraph around it**, so a pinned opening does not reach a present-tense
clause further down; that is what left the `Δdump` sentence below contested until taxis #1721
measured its population.

**The rule has a third object and the two named above are not the whole of it: a clause that counts
or quotes rows — of the table above, or of the declaration dump — is in the class too.** It is not
falsified by an append to any guard section, so no scan built on that line can see it — the noun
after the numeral is *rows*, and not *declarations* or *guards*. The worked case is
`OkaTest/Axioms/Weierstrass.lean`'s routing paragraph, which carried one of each and they failed
differently: *"three of which have a row of their own"* was **wrong at the commit that wrote it**,
two of the four namespaces it lists being named by a row and no more, while a **quotation** of the
`OkaTest/Axioms/Analysis.lean` row beside it was exact when written and went wrong when that row
was reworded. **A quotation is in the class for the same reason a count is**: it asserts something
about a structure the clause does not own, and the owner changes it without looking.

**Swept at `c8e77d0`, and what the sweep found is a shape rather than a list.** The class has two
populations. Clauses about the table above are few, and each is exempt on its face — by naming
the rows it counts, or by pinning the figure to the commit it was taken at. Clauses about
`scripts/DumpOkaDecls.lean`'s rows are many, and nearly all of them are one shape: the `Δdump`
note recording what a draft the file did not take would have cost. **Such a note is exempt under
the pinning spelling and not the naming one**, and reading it under the naming one is the mistake
the first draft of this paragraph made. Whether it names every row it counts varies, and that is
the question the naming exemption would turn on; here it does not arise, because a figure about
an abandoned draft is falsified by rewriting history rather than by an append. The `Δdump` notes
written in the present tense are the ones the rule reaches, and where such a note gives its figure
against the same file's declaration count, the first object above already reached it;
`Oka/Analytification/CrossMemberDatumGlue.lean`'s gives it against that count *and* the planted
rows the file keeps deliberately, says so in the same breath, and is reached by this object alone.

**The widening is not free, and at `c8e77d0` it cost two repairs.** At that commit
`Oka/Analytification/CrossMemberGlue.lean` said its module adds its own declarations to the dump
*"and nothing else, apart from two `congr_simp` lemmas"*, and
`Oka/Analytification/CrossMemberDatumGlue.lean` said that file *"carries two of exactly this
shape"* — a live count of planted rows naming none of them, the second of them about a file the
clause does not own. **Both were exact when measured**, the dump carrying two such rows under
that module and no more, **and both are one `simp only` from being silently wrong.** They are
left to a push of their own: they are under `Oka/`, and the subject of this one is the rule and
the routing paragraph that motivated it.

**What the sweep asked of each clause is that and only that**: which population it is in, and
under which spelling it is exempt. Whether the other figures those sentences carry are still
exact is a question in the objects named above and was not re-asked here, which is what a sweep of
one class is and is not. **The membership is recorded as a shape and not as a list of sites** —
a list of where a class is instantiated goes stale on the next `Δdump` note anyone writes, and
the draft of this paragraph that carried one named a small part of the tree's sites and reached a
verdict that fails at a site it had not named. **The record of the sweep is what makes this
paragraph cheap to have installed**, not the rule: a rule that grows and is not swept is the
failure this file exists to prevent, and `scripts/` cannot do this one either, for the reason the
checker sentence above gives.

**Most mirror-tree material is routed by a row, and a small tail of it is deliberately routed by
none.** `README.md`'s *Layout: the Mathlib mirror tree* defines a mirror-tree file by its path — a
file under `Oka/` mirroring a path under `Mathlib/`, holding no complex-analytic mathematics and
staged for upstreaming. **That is 221 of the 645 guards at `27c185a`**, and two rows exist to
route almost nothing else: `OkaTest/Axioms/Sheaves.lean` is **87 of 87** mirror-tree, mostly
`Oka/Geometry/RingedSpace/`, and `OkaTest/Axioms/RingTheory.lean` is **19 of 19**. So being
mirror-tree is not what decides whether a row names a module, and the criterion above applies to
mirror-tree modules exactly as to any other.

**What gets no row is a mirror-tree module whose subject no existing row names.** Such a module
has no subject *in this development*, so the only row that could name it would name a source
directory rather than a topic, and the table routes by topic. **Guard one in the file of the
analytic result that motivated it**, under that result's heading — which is what
`OkaTest/Axioms/Morphisms.lean` already says of `Oka/Topology/Covering/Basic.lean`: *"mirror-tree
topological criteria … say nothing about analytic spaces; they are guarded here rather than apart
from their consumers."* `OkaTest/Axioms/AnalyticSpace.lean` reaches the same placement for a
module the sheaves row *does* route — *"general locally-ringed-space material with **no row of its
own** in the topic table … it sits here because the only thing that uses it is the rigidity
statement below"* — so this paragraph records a practice with two independent precedents rather
than inventing one.

At `27c185a` that tail is **18 guards in six modules**, against 645 in all: seven from
`Oka/CategoryTheory/GlueData.lean` (in `OkaTest/Axioms/AnalyticSpace.lean`), five from
`Oka/Topology/Covering/Basic.lean` (in `OkaTest/Axioms/Morphisms.lean`), three from
`Oka/Topology/IsLocalHomeomorph.lean` (in `OkaTest/Axioms/Sheaves.lean`), and one each from
`Oka/CategoryTheory/Limits/Shapes/KernelBiprod.lean` (in `OkaTest/Axioms/SheafOfModules.lean`),
`Oka/Topology/Category/TopCat/Opens.lean` (in `OkaTest/Axioms/Analytification.lean`) and
`Oka/FieldTheory/IsAlgClosed/Basic.lean` (in `OkaTest/Axioms/RingTheory.lean`). **The rule above
is being written down for the first time and the tail does not yet follow it**: three of the six
modules sit in a file holding some of their consumer's guards and three do not, and by guards the
minority is the larger — **7 of the 18 conform and 11 do not.** The three that do not:

* **`Oka/CategoryTheory/GlueData.lean`**, the largest member at seven. Its only importer is
  `Oka/Analytification/AffineCover.lean`, whose guards are all in
  `OkaTest/Axioms/Analytification.lean`; and its guards sit under a heading of their own rather
  than under an analytic result's, so it fails both halves of the rule.
* **`Oka/Topology/IsLocalHomeomorph.lean`**, whose only user is
  `Oka/AnalyticSpace/CoveringSpace.lean`, guarded in `OkaTest/Axioms/Morphisms.lean`. It was
  placed beside the file it was *written for*, which **deliberately does not import it** for the
  import-cost reason that file gives, and `OkaTest/Axioms/Sheaves.lean`'s heading for it says so.
* **`Oka/FieldTheory/IsAlgClosed/Basic.lean`**, which has **no user under `Oka/` at all**:
  `Oka/AnalyticSpace/CoveringMap.lean` names its one theorem in a docstring and does not import
  it, and the only use in the repository is inside `OkaTest/FiniteMorphism.lean`, which this
  repository does not guard. There is no analytic result to place it beside.

**Read a consumer off the imports, not off a name grep.** All three were got wrong that way
before they were measured, and the first was got wrong in the draft of this very paragraph:
`ofGlueData'` is Mathlib's name and several files mention it, only one imports the module that
proves things about it. Moving any of them is a tidy-up nobody has done and not a defect in the
table.
**The figure is here so that a later sweep can tell growth from noise**: a tail that stays near
this size is the expected one, and a tail that doubles means a row really is missing.

## What these guards cover, and what they do not

**Nothing here claims to be complete, and the gap is measured rather than guessed.**
`python3 scripts/guard_coverage.py` counts the declarations this repository's module docstrings
advertise under a `## Main results` heading and asks which of them some `#print axioms` names. **At
`7b6fd39`, the base this file's tranche was written on, that was 502 guarded names against 506
advertised declarations, of which 179 were named by no guard at all, spread over 63 files; the
nineteen guards added below account for nineteen of those 179, leaving 160 unguarded in 61
files.** **A second tranche of twelve was measured against `0ac74d4`, where the gap stood at 162
in 61 files, and leaves 150 in 60.** Ten of those twelve are the whole of
`Oka/ChangeOfCoordinates.lean`'s `## Main results`; the other two are the ones lana-agents/oka#201
put into the gap by *advertising* them, which is the mechanism of the next paragraph running the
other way and the reason a tranche is a standing job rather than a finite one. So **still close to
a third** of what the library announces as its main results carries no axiom assertion. Neither
list contains the other: **175 guarded names are advertised in no `## Main results`**, which is
not a defect, since a guard on a lemma no docstring announces is worth exactly as much as one on
a lemma it does — and that figure is unchanged across both tranches, which is what says each was
drawn from the advertised-and-unguarded pool and not from somewhere else.

The figures are pinned to a commit rather than to a date, because a paragraph that says *"on the
tree this lands in"* cannot be re-run without first finding which tree that was. **The two totals
are what goes stale; the gap is not**, which is why the sentence above reports a base and a delta
rather than a current total. A pull request that guards the result it advertises moves both
totals and leaves their difference alone: between `7b6fd39` and `3f185f0` two of them landed, the
totals went 502 and 506 to 512 and 516, and the gap stayed 179 in 63 files. So a later run that
reproduces the 160 and the 61 has reproduced this measurement even if neither total matches.

**That is a measurement and not a rule, and this file does not turn it into one.** Some of the 160
should probably stay unguarded — `Oka/Analytic/ParametricCircleIntegral.lean` is general complex
analysis with a Mathlib destination and contributes 17 of them — so the right number is not zero,
nobody has decided what it is, and the script is a reporter run by hand rather than a check in
`.orchestra/validation.sh`. What the paragraph above rules out is only the reading that an
absent guard means somebody decided against one.

## Updating an assertion

If a theorem is legitimately restated or renamed, do **not** delete its assertion. Run the
corresponding `#print axioms` (for instance with `lake env lean OkaTest/Axioms/<File>.lean`, or
in the editor) and paste the message Lean actually prints back into the expected docstring.
The expected message must stay `[propext, Classical.choice, Quot.sound]`: any other axiom —
`sorryAx` above all — is a regression, not something to record.
-/

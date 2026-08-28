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
| complex analysis, and the topology of polynomial zero loci | `OkaTest/Axioms/Analysis.lean` |
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
whose name is wrapped onto the next line, and there is one such guard today, in
`OkaTest/Axioms/SheafOfModules.lean`; a census taken that way comes out one short of
`scripts/guard_coverage.py`'s, which is where the regular expression above is from. A row is
wrong when some module's guards are covered by no row at all — that is the failure this table
exists to prevent — and not merely when its phrase is shorter than the file.

**Most mirror-tree material is routed by a row, and a small tail of it is deliberately routed by
none.** `README.md`'s *Layout: the Mathlib mirror tree* defines a mirror-tree file by its path — a
file under `Oka/` mirroring a path under `Mathlib/`, holding no complex-analytic mathematics and
staged for upstreaming. **That is 221 of the 645 guards at `4025f01`**, and two rows exist to
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

At `4025f01` that tail is **18 guards in six modules**, against 645 in all: seven from
`Oka/CategoryTheory/GlueData.lean` (in `OkaTest/Axioms/AnalyticSpace.lean`), five from
`Oka/Topology/Covering/Basic.lean` (in `OkaTest/Axioms/Morphisms.lean`), three from
`Oka/Topology/IsLocalHomeomorph.lean` (in `OkaTest/Axioms/Sheaves.lean`), and one each from
`Oka/CategoryTheory/Limits/Shapes/KernelBiprod.lean` (in `OkaTest/Axioms/SheafOfModules.lean`),
`Oka/Topology/Category/TopCat/Opens.lean` (in `OkaTest/Axioms/Analytification.lean`) and
`Oka/FieldTheory/IsAlgClosed/Basic.lean` (in `OkaTest/Axioms/RingTheory.lean`). **Four of the six
already sit in a file that holds some of their consumer's guards** — the rule above is being
written down rather than imposed. The two that do not are
`Oka/FieldTheory/IsAlgClosed/Basic.lean`, whose one theorem is used by
`Oka/AnalyticSpace/CoveringMap.lean`, and `Oka/Topology/IsLocalHomeomorph.lean`, whose only user
is `Oka/AnalyticSpace/CoveringSpace.lean`; both those users are guarded in
`OkaTest/Axioms/Morphisms.lean`. The second was placed beside the file it was *written for*,
which **deliberately does not import it** for the import-cost reason that file gives, and
`OkaTest/Axioms/Sheaves.lean`'s heading for it says so. Moving either is a tidy-up nobody has
done and not a defect in the table.
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

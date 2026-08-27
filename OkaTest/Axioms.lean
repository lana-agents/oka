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
| complex analysis in one and several variables | `OkaTest/Axioms/Analysis.lean` |
| `LocalOkaRing`: Rückert, maximal ideal, regularity | `OkaTest/Axioms/LocalOkaRing.lean` |
| `OkaRing` and the structure sheaf of `ℂ^ι` | `OkaTest/Axioms/ComplexSpace.lean` |
| the comparison morphism to `Spec` | `OkaTest/Axioms/Analytification.lean` |
| general presheaf and sheaf theory | `OkaTest/Axioms/Sheaves.lean` |
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

## What these guards cover, and what they do not

**Nothing here claims to be complete, the gap is measured rather than guessed, and the figure the
first two tranches were written against is not the one that matters.**
`python3 scripts/guard_coverage.py` counts the declarations this repository's module docstrings
advertise under a `Main …` heading and asks which of them some `#print axioms` names. `--cone`
then asks a different and sharper question, because **`#print axioms` is transitive**: it reports
the axioms of every constant the named proof term mentions, transitively, so a `sorry` below a
guarded theorem turns *that* theorem's guard red. A declaration in the cone of some guard is
therefore already covered by the regression test these files are, and a second `#print axioms`
naming it would fail at exactly the same times.

**The two questions differ by a factor of seven here.** At `d12d334`, the base the third tranche
was written on: 546 guarded names against 759 advertised declarations in 119 files, of which
**301, in 84 files, had no guard of their own — and 259 of those 301 sit in some guard's cone.
42, in 29 files, were reached by nothing at all.** The third tranche is those 42, and it takes
**41** guards, because a guard brings its cone with it: `MvPolynomial.awayBaseHom` is in the cone
of `MvPolynomial.isLocalization_away_quotient_awayIdeal`, which was itself one of the 42. So at
the commit this lands in the figures are **587 guarded, 260 unguarded in 79 files, and 0 reached
by no guard.** Neither list contains the other: **88 guarded names are advertised under no
`Main …` heading**, which is not a defect, since a guard on a lemma no docstring announces is
worth exactly as much as one on a lemma it does — and that figure is *unchanged* across the
tranche, which is what says all 41 were drawn from the advertised-and-unguarded pool and not from
somewhere easier.

**The denominator was ambiguous until this tranche, and that is why the figure moved.** The script
matched the exact string `## Main results` and so could not see the 74 `## Main definitions`
sections and the one `## Main declarations`, worth 238 further advertised declarations of which
151 had no guard. Mathlib uses at least ten spellings of that heading — `## Main statements` and
`## Main definitions and results` among them — so which one an author reached for is not a fact
about whether a declaration is announced. It now matches any heading beginning `Main` and prints
the spellings it saw, so an eleventh is announced rather than swallowed. Under the old narrow
reading the same measurement at `d12d334` is 521 advertised, 150 unguarded in 60 files, 122 in a
cone, 28 uncovered in 19 files.

**That is why the second figure is the one to watch.** *Unguarded* has no right value and nobody
could decide one: two tranches and three sessions declined to, and the reason is now visible —
most of it was never a gap. *Reached by no guard at all* has an obvious right value, namely zero,
because an advertised main result outside every cone is one that no regression test in this
repository touches.

**Both halves are compiled and neither is a reading.** Replacing the proof of
`hasSum_multiGeometric` — advertised by `Oka/Analytic/ParametricCircleIntegral.lean`, guarded by
nothing, and in the cone of the `OkaTest/Axioms/Weierstrass.lean` guards — by `sorry` makes
`#print axioms localweierstrass_division` print
`[propext, sorryAx, Classical.choice, Quot.sound]`, so the `#guard_msgs` in
`OkaTest/Axioms/Weierstrass.lean` fails. The same substitution in `analyticAt_of_differentiableOn`,
the one advertised result of that file that was in no cone, leaves that message unchanged **and a
full `lake build` succeeding, 3988 jobs, no guard red** — a `sorry` in an advertised main result
that 546 assertions could not see. Both were run at `d12d334`, against a built `master`.

**`Oka/Analytic/ParametricCircleIntegral.lean` is the file this settles, and the answer is neither
of the two that were argued.** Three sessions left it alone, and this file and `README.md` both
cited its 17 unguarded results as the reason the right number is not zero. Fifteen of the
seventeen are in the cone of the three Weierstrass guards — the file exists to prove the two
circle-integral lemmas `Oka/Weierstrass.lean` consumes, and its own module docstring says so —
the sixteenth, `analyticAt_of_shift`, is reached instead by the three divided-difference guards
already in `OkaTest/Axioms/Analysis.lean`, through `Oka/Analytic/DividedDifference.lean`, and the
seventeenth, the analyticity of a function differentiable on an open set, is used by nothing
guarded. It needed **one** guard, not seventeen, not an exclusion, and no flag in the script.
Run the three Weierstrass roots by themselves and the answer is 15 of the 16 covered ones, not
16: `analyticAt_of_shift` is covered by a different guard and never was in the gap either way.

**The weakness of a cone membership, since it is real.** A guard on `f` holds whatever else
changes; `f`'s membership of `g`'s cone lasts exactly as long as `g`'s proof goes on mentioning
`f`, and a refactor of `g` can end it in silence. What makes that tolerable is that nothing is
recorded and nothing is inferred: re-run `--cone` and a name that has dropped out of every cone
is back in the uncovered column, which is where the next tranche would find it.

The figures are pinned to a commit rather than to a date, because a paragraph that says *"on the
tree this lands in"* cannot be re-run without first finding which tree that was. **The totals are
what goes stale.** A pull request that guards the result it advertises moves both totals and
leaves their difference alone: between `7b6fd39` and `3f185f0` two of them landed, the totals went
502 and 506 to 512 and 516, and the unguarded figure stayed 179 in 63 files. The two earlier
tranches are recorded in those terms — **nineteen guards against `7b6fd39`, where the unguarded
figure was 179 in 63 files, and twelve against `0ac74d4`, where it was 162 in 61** — measured
under the narrow heading and against no cone, so neither knew that most of what it left behind
was already covered and neither could see a `## Main definitions` list at all.

**This is a measurement and not a rule, and this file does not turn it into one.**
`scripts/guard_coverage.py` is a reporter run by hand and is deliberately not in
`.orchestra/validation.sh`: the uncovered figure is zero today, and the way it stops being zero is
a pull request that advertises a new result — an ordinary and desirable thing to do, which no
author should meet as a red build in a script they have never run. What the paragraphs above rule
out is only the two readings that were available before: that an absent guard means somebody
decided against one, and that an absent guard means nothing is watching.

## Updating an assertion

If a theorem is legitimately restated or renamed, do **not** delete its assertion. Run the
corresponding `#print axioms` (for instance with `lake env lean OkaTest/Axioms/<File>.lean`, or
in the editor) and paste the message Lean actually prints back into the expected docstring.
The expected message must stay `[propext, Classical.choice, Quot.sound]`: any other axiom —
`sorryAx` above all — is a regression, not something to record.
-/

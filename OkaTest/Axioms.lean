/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression test

The library is `sorry`-free, and its results rest only on the three standard axioms of Lean:
`propext`, `Classical.choice` and `Quot.sound`. A `sorry` is only a warning, not an error, so
nothing in an ordinary `lake build` would notice if one were reintroduced — the proof of a
theorem depending on it would simply start depending on `sorryAx` as well.

This file pins that down: each `#guard_msgs` below fails the build if the axiom dependencies of
the named theorem ever change. Together with the `sorry` grep in
`.github/workflows/lean_action_ci.yml` it is what keeps the completeness claim in `README.md`
honest.

The file is not part of the `Oka` library; it is the `OkaTest` library of `lakefile.toml`,
which `defaultTargets` also builds, so plain `lake build` exercises it. The layout follows
Mathlib's own `MathlibTest`: a test library must live in a directory of its own, outside the
source tree of the library it tests, or Lake rejects its imports.

## Updating this file

If a theorem below is legitimately restated or renamed, do **not** delete its assertion. Run
the corresponding `#print axioms` (for instance with `lake env lean OkaTest/Axioms.lean`, or
in the editor) and paste the message Lean actually prints back into the expected docstring.
The expected message must stay `[propext, Classical.choice, Quot.sound]`: any other axiom —
`sorryAx` above all — is a regression, not something to record.
-/

/-! ### Oka's coherence lemma on `ℂ^n` -/

/-- info: 'oka' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka

/-- info: 'oka'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka'

/-- info: 'oka_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka_fin

/-- info: 'okaStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms okaStatement

/-! ### Oka's bounded degree lemma -/

/-- info: 'oka_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka_lemma

/-- info: 'oka_lemma_weierstrass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oka_lemma_weierstrass

/-! ### Weierstrass theory -/

/--
info: 'localweierstrass_division' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_division

/--
info: 'localweierstrass_division_unique' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_division_unique

/--
info: 'localweierstrass_preparation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms localweierstrass_preparation

/-! ### The Rückert basis theorem -/

/--
info: 'LocalOkaRing.isNoetherianRing_fin' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.isNoetherianRing_fin

/--
info: 'LocalOkaRing.instIsNoetherianRing' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.instIsNoetherianRing

/--
info: 'ComplexAnalytic.AnalyticSpace.instIsNoetherianRingStalk' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.instIsNoetherianRingStalk

/--
info: 'LocalOkaRing.instUniqueFactorizationMonoid' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.instUniqueFactorizationMonoid

/-! ### The maximal ideal and the truncations -/

/--
info: 'LocalOkaRing.maximalIdeal_eq_span_coord' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.maximalIdeal_eq_span_coord

/--
info: 'LocalOkaRing.truncQuotientEquiv' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.truncQuotientEquiv
/-! ### Polynomials as holomorphic functions -/

/--
info: 'OkaRing.ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OkaRing.ofMvPolynomial

/--
info: 'LocalOkaRing.ofMvPolynomial' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalOkaRing.ofMvPolynomial

/-! ### The main theorem -/

/--
info: 'ComplexAnalytic.IsLocalModel.hasLocalRelations' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.IsLocalModel.hasLocalRelations

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the germ bridge, and that its output is an input of the projection theorem

`Oka/UliftCoord.lean` produces, from a nonzero germ, a monic `P : Polynomial (OkaRing W)` with
`W : Opens (ULift (Fin n) → ℂ)`. **Two things have to be true for that to be worth anything, and
neither is visible in its statement.**

## What each check is for

* `ComplexAnalytic.exists_ne_zero_localOkaRing` — **the hypothesis is satisfiable.** A theorem
  about nonzero germs says nothing if there are none; `LocalOkaRing` is nontrivial, so `1` is one.
  This is the cheapest possible non-example check and it is here because the conclusion of
  `LocalOkaRing.exists_congr_monic_realize_of_ne_zero` is an existential, which is vacuously
  provable from an empty hypothesis.
* `ComplexAnalytic.exists_okaFamily_of_ne_zero` — **the output is an input.** The whole reason
  `Oka/UliftCoord.lean` exists is the index convention: `Oka/Weierstrass.lean` states its
  realization at `Fin n` and `ComplexAnalytic.okaFamily` takes `Opens (ULift (Fin n) → ℂ)`. That
  the two now meet is a *typechecking* claim and not a mathematical one, so nothing under `Oka/`
  can state it without also stating something it does not need. Here it is stated: from a nonzero
  germ one gets a family of monic polynomials of one fixed degree with continuous coefficients —
  **all three hypotheses of `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq`** — and the
  proof is the bridge followed by the three lemmas of
  `Oka/AnalyticSpace/HolomorphicFamily.lean`, with no coercion and no relabelling in between.

## What is not checked here

* **No finiteness, because the image is missing.**
  `ComplexAnalytic.isFinite_comp_projRestrict_of_monic` needs a fourth thing the three above do
  not give: a morphism whose image is the zero locus of
  `ComplexAnalytic.cylinderSection W P`. Nothing produces one from a germ, which
  `Oka/UliftCoord.lean` records under its own `## What is not here`, and supplying one by hand is
  what `OkaTest/HolomorphicFamily.lean` does for a curve written down rather than prepared.
* **No germ that is not a polynomial.** `1` is the witness above, and its Weierstrass polynomial
  is as degenerate as a Weierstrass polynomial gets. The bridge is indifferent to which germ it
  is handed — that is why `ComplexAnalytic.exists_okaFamily_of_ne_zero` quantifies over all of
  them — but **no statement here exhibits a transcendental one**, and the germ of `z·(e^z)²` that
  `OkaTest/HolomorphicFamily.lean` uses is written down rather than produced by preparation, so
  it is not one either.
* **Nothing about the neighbourhood.** `W` is whatever the preparation theorem produces; no
  statement here says it is a polydisc, or connected, or that two applications give the same one.
-/

open TopologicalSpace

universe u

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-- **A nonzero germ exists**, so the hypothesis of
`LocalOkaRing.exists_congr_monic_realize_of_ne_zero` is satisfiable and its conclusion is not
vacuous. `LocalOkaRing` is nontrivial, and that is the whole proof. -/
theorem exists_ne_zero_localOkaRing : ∃ f : LocalOkaRing (Fin (n + 1)), f ≠ 0 :=
  ⟨1, one_ne_zero⟩

/-- **From a nonzero germ to a family satisfying all three hypotheses of the projection theorem
over an open base.**

`LocalOkaRing.exists_congr_monic_realize_of_ne_zero` produces the monic `P` at
`ULift (Fin n)`, and `ComplexAnalytic.monic_okaFamily`, `ComplexAnalytic.natDegree_okaFamily` and
`ComplexAnalytic.continuous_coeff_okaFamily` read off the three hypotheses
`ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` asks of a family. **There is no
relabelling, coercion or transport between the two halves**, and that is the statement: the
`Fin`-indexed side of `Oka/Weierstrass.lean` and the `ULift`-indexed side of
`ComplexAnalytic.AnalyticSpace` now compose.

What this does *not* say is anything about which germ, or about the hypersurface — see this
file's `## What is not checked here`. -/
theorem exists_okaFamily_of_ne_zero {f : LocalOkaRing (Fin (n + 1))} (hf : f ≠ 0) :
    ∃ (W : Opens (ULift.{u} (Fin n) → ℂ)) (P : Polynomial (OkaRing W)),
      (∀ w : ↥W, (okaFamily.{u} W P w).Monic) ∧
      (∀ w : ↥W, (okaFamily.{u} W P w).natDegree = P.natDegree) ∧
      (∀ j : ℕ, Continuous fun w : ↥W ↦ (okaFamily.{u} W P w).coeff j) := by
  obtain ⟨_, _, _, W, _, P, hP, _⟩ := LocalOkaRing.exists_congr_monic_realize_of_ne_zero.{u} hf
  exact ⟨W, P, monic_okaFamily.{u} W P hP, natDegree_okaFamily.{u} W P hP,
    continuous_coeff_okaFamily.{u} W P⟩

end ComplexAnalytic

end

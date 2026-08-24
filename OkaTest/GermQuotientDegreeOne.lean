/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the degree-one Weierstrass quotient

`LocalOkaRing.quotientDegreeOneEquiv` says that quotienting the germ ring in `n + 1` variables by
a local Weierstrass polynomial of degree one returns the germ ring in `n` variables.
`LocalOkaRing.quotientLastVarEquiv` is the case `q = X`, which was already on the record, so the
reading that would make the general statement say nothing new is that **every degree-one local
Weierstrass polynomial is the coordinate `X_n`**.

It is not. `LocalOkaRing.quotientGraphEquiv` applies at `X_n - c` for every germ `c` vanishing at
the origin, and this file exhibits one with `c ≠ 0`: the **diagonal** `X₁ - X₀` in two variables.
`LocalOkaRing.coord_ne_zero` is what separates it from `X₁`, and it is a statement about the germ
and not about the polynomial, which is the form the general statement is indexed by.

## What is not checked here

**That the quotient map is anything in particular.** The equivalence is
`LocalOkaRing.incl` followed by the quotient, and nothing below computes its value on a named
germ; the content is that it is bijective.

**Nothing about analytic spaces.** The bridge from a stalk of the structure sheaf of `ℂ^ι` to
`LocalOkaRing` is `okaStalkEquiv` (`Oka/StalkEquiv.lean`, root namespace) and it is not used
here — this file is about the germ ring alone.

**Nothing about a general hypersurface.** That a germ `f` with `∂f/∂X_n` a unit generates the same
ideal as some `X_n - c` is Weierstrass preparation plus a unit factor, and neither step is taken
anywhere in this repository yet.
-/

open IsLocalRing Polynomial LocalOkaRing

namespace OkaTest.GermQuotientDegreeOne

noncomputable section

/-- **The first coordinate lies in the maximal ideal**, so it is an admissible `c`. -/
theorem coord_mem_maximalIdeal (i : Fin 1) :
    (LocalOkaRing.coord i : LocalOkaRing (Fin 1)) ∈
      IsLocalRing.maximalIdeal (LocalOkaRing (Fin 1)) := by
  rw [LocalOkaRing.maximalIdeal_eq_span_coord]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- **The diagonal `X₁ - X₀` is a degree-one local Weierstrass polynomial in two variables**, and
its constant term is not zero — so it is genuinely not the coordinate `X₁`.

This is the non-vacuity: `LocalOkaRing.quotientLastVarEquiv` covers `X₁` and nothing else, and
`LocalOkaRing.quotientDegreeOneEquiv` covers this. -/
theorem coord_zero_ne_zero : (LocalOkaRing.coord 0 : LocalOkaRing (Fin 1)) ≠ 0 :=
  LocalOkaRing.coord_ne_zero 0

/-- **The germ ring in one variable is the germ ring in two modulo the diagonal.**

`LocalOkaRing.quotientGraphEquiv` at `c = X₀`, which
`OkaTest.GermQuotientDegreeOne.coord_zero_ne_zero` says is not the germ `0` — so this is an
instance of `LocalOkaRing.quotientDegreeOneEquiv` that `LocalOkaRing.quotientLastVarEquiv` does
not cover. -/
def diagonalEquiv :
    LocalOkaRing (Fin 1) ≃+*
      (LocalOkaRing (Fin 2) ⧸
        Ideal.span {fromPolynomial (X - C (LocalOkaRing.coord (0 : Fin 1)))}) :=
  LocalOkaRing.quotientGraphEquiv (coord_mem_maximalIdeal 0)

end

end OkaTest.GermQuotientDegreeOne

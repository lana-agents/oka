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

**A nonzero `c` is not on its own enough to say the two equivalences differ**, and it is worth
being exact about the gap, because `LocalOkaRing.quotientLastVarEquiv` and
`LocalOkaRing.quotientGraphEquiv` have the *same source* `LocalOkaRing (Fin n)`. All that
distinguishes them is their targets, which are quotients by the ideals `(X_n)` and `(X_n - c)`,
and two distinct elements can generate the same principal ideal. So the statement that one does
not cover the other is a statement about **ideals**, and it is
`LocalOkaRing.span_fromPolynomial_X_sub_C_ne_span_lastVar`, instantiated here as
`OkaTest.GermQuotientDegreeOne.diagonalSpan_ne_span_lastVar`.

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

/-- **The constant term of the diagonal `X₁ - X₀` is not the zero germ.**

This is the input to the non-vacuity and not the non-vacuity itself:
`OkaTest.GermQuotientDegreeOne.diagonalSpan_ne_span_lastVar` is what turns it into a statement
about the two ideals, which is what *covers* means here. -/
theorem coord_zero_ne_zero : (LocalOkaRing.coord 0 : LocalOkaRing (Fin 1)) ≠ 0 :=
  LocalOkaRing.coord_ne_zero 0

/-- **The diagonal and the coordinate generate different ideals of the germ ring in two
variables**, so the quotients `LocalOkaRing.quotientGraphEquiv` and
`LocalOkaRing.quotientLastVarEquiv` identify are quotients by different things.

`LocalOkaRing.span_fromPolynomial_X_sub_C_ne_span_lastVar` at `c = X₀`, whose hypothesis is
`OkaTest.GermQuotientDegreeOne.coord_zero_ne_zero`. **This is the file's non-vacuity**, and the
reason it and not `coord_zero_ne_zero` is that the two equivalences have the same source: nothing
about `c` alone separates them, and two distinct germs can generate the same principal ideal. -/
theorem diagonalSpan_ne_span_lastVar :
    Ideal.span {fromPolynomial (X - C (LocalOkaRing.coord (0 : Fin 1)))} ≠
      Ideal.span {(lastVar : LocalOkaRing (Fin 2))} :=
  LocalOkaRing.span_fromPolynomial_X_sub_C_ne_span_lastVar coord_zero_ne_zero

/-- **The germ ring in one variable is the germ ring in two modulo the diagonal.**

`LocalOkaRing.quotientGraphEquiv` at `c = X₀`, which
`OkaTest.GermQuotientDegreeOne.coord_zero_ne_zero` says is not the germ `0`. That this is an
instance of `LocalOkaRing.quotientDegreeOneEquiv` which `LocalOkaRing.quotientLastVarEquiv` does
not cover is `OkaTest.GermQuotientDegreeOne.diagonalSpan_ne_span_lastVar` — a statement about the
two ideals, which is what the two equivalences differ in, their sources being equal. -/
def diagonalEquiv :
    LocalOkaRing (Fin 1) ≃+*
      (LocalOkaRing (Fin 2) ⧸
        Ideal.span {fromPolynomial (X - C (LocalOkaRing.coord (0 : Fin 1)))}) :=
  LocalOkaRing.quotientGraphEquiv (coord_mem_maximalIdeal 0)

end

end OkaTest.GermQuotientDegreeOne

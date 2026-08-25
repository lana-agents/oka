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

**Nothing about the derivative.** `LocalOkaRing.exists_span_eq_span_X_sub_C` does produce the `c`
from a general germ, and `OkaTest.GermQuotientDegreeOne.skewDiagonalEquiv` below is an instance of
it — but its hypothesis is that the restriction to the last axis has a simple zero, not that
`∂f/∂X_n` is a unit. **The second is not expressible on `LocalOkaRing`**, which has no
partial-derivative operator; that the two conditions agree is a bridge nobody here has built.

## Non-vacuity of the simple-zero quotient, which is a different question

`LocalOkaRing.quotientSimpleZeroEquiv` takes an arbitrary germ `f` with a simple zero along the
last axis, so the reading that would make *it* say nothing new is that such an `f` is always
`X_n - c` on the nose. `OkaTest.GermQuotientDegreeOne.skewDiagonal` is `(X₁ - X₀)(1 + X₁)`, which
is not: it has an `X₁²` term, and it is not a Weierstrass polynomial of any degree because the
coefficient of `X₁` in it is a unit.

**The informative half is the negative one.**
`OkaTest.GermQuotientDegreeOne.order_partialEval_parabola` computes the axis order of
`X₁² - X₀` as `2`, so `LocalOkaRing.quotientSimpleZeroEquiv` does not apply to the parabola — the
hypothesis is doing work rather than holding of everything in sight. Nothing here says the germ
ring of the parabola is *not* one dimension down; the claim is only that this theorem does not say
it is.
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

/-! ### A simple zero that is not a graph on the nose -/

/-- **`1 + X₁` is a unit of the germ ring in two variables**, since its value at the origin is
`1`. It is the factor that takes the diagonal out of Weierstrass form. -/
theorem isUnit_one_add_lastVar : IsUnit (1 + (lastVar : LocalOkaRing (Fin 2))) := by
  rw [LocalOkaRing.isUnit_iff, map_add, map_one, lastVar_eq_coord, constantCoeff_coord]
  simp

/-- **The diagonal times a unit**, `(X₁ - X₀)(1 + X₁)`.

Expanded this is `X₁ + X₁² - X₀ - X₀X₁`. As a polynomial in `X₁` it is monic of degree two with
the coefficient of `X₁` equal to `1 - X₀`, which is a **unit** and so not in the maximal ideal —
so it is not a local Weierstrass polynomial at all, let alone one of degree one. -/
def skewDiagonal : LocalOkaRing (Fin 2) :=
  fromPolynomial (X - C (LocalOkaRing.coord (0 : Fin 1))) * (1 + lastVar)

/-- **The restriction of the skew diagonal to the last axis has a simple zero.**

`LocalOkaRing.order_partialEval_eq_natDegree` at the unit `1 + X₁` and the Weierstrass polynomial
`X - C X₀`, whose degree is one. -/
theorem order_partialEval_skewDiagonal :
    PowerSeries.order (MvPowerSeries.partialEval (Fin.last 1)
      ((skewDiagonal : LocalOkaRing (Fin 2)) : MvPowerSeries (Fin 2) ℂ)) = 1 := by
  rw [skewDiagonal, LocalOkaRing.order_partialEval_eq_natDegree isUnit_one_add_lastVar
    (LocalOkaRing.isLocalWeierstrassPolynomial_X_sub_C (coord_mem_maximalIdeal 0)) rfl,
    natDegree_X_sub_C]
  rfl

/-- **The germ ring in one variable is the germ ring in two modulo the skew diagonal.**

`LocalOkaRing.quotientSimpleZeroEquiv` at a germ that is not `X₁ - c` for any `c`, which is the
non-vacuity of that definition:
`OkaTest.GermQuotientDegreeOne.order_partialEval_skewDiagonal` is the only hypothesis, and the
`c` whose graph this turns out to be is produced by the theorem rather than supplied. -/
def skewDiagonalEquiv :
    LocalOkaRing (Fin 1) ≃+* (LocalOkaRing (Fin 2) ⧸ Ideal.span {skewDiagonal}) :=
  LocalOkaRing.quotientSimpleZeroEquiv order_partialEval_skewDiagonal

/-- **The parabola `X₁² - X₀` has axis order two, not one**, so
`LocalOkaRing.quotientSimpleZeroEquiv` does not apply to it.

This is the negative control and it is the informative one: the simple-zero hypothesis is not
satisfied by every hypersurface through the origin, and `2 ≠ 1` is what says so. The computation
does not go through `LocalOkaRing.order_partialEval_eq_natDegree` — it is
`partialEval_coe_fromPolynomial` (`Oka/Weierstrass.lean`, root namespace) directly, since
evaluating the coefficients of `X² - C X₀` at the origin gives `X²`. -/
theorem order_partialEval_parabola :
    PowerSeries.order (MvPowerSeries.partialEval (Fin.last 1)
      ((fromPolynomial (X ^ 2 - C (LocalOkaRing.coord (0 : Fin 1))) : LocalOkaRing (Fin 2)) :
        MvPowerSeries (Fin 2) ℂ)) = 2 := by
  rw [partialEval_coe_fromPolynomial, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, constantCoeff_coord, map_zero, sub_zero,
    Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.order_X_pow]
  rfl

end

end OkaTest.GermQuotientDegreeOne

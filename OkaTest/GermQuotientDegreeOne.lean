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
is not, and both halves of *is not* are theorems here rather than remarks:
`OkaTest.GermQuotientDegreeOne.skewDiagonal_ne_fromPolynomial_X_sub_C` for `X₁ - c` at any `c`,
and
`OkaTest.GermQuotientDegreeOne.not_isLocalWeierstrassPolynomial_of_fromPolynomial_eq_skewDiagonal`
for a local Weierstrass polynomial of any degree. **The first is the one the non-vacuity needs**;
the second is what rules out the reading that it is a Weierstrass polynomial the file forgot to
put in Weierstrass form.

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

Expanded this is `X₁ + X₁² - X₀ - X₀X₁`: as a polynomial in `X₁` it is monic of degree two with
the coefficient of `X₁` equal to `1 - X₀`. The two things that expansion is here to make plausible
are theorems rather than prose —
`OkaTest.GermQuotientDegreeOne.skewDiagonal_ne_fromPolynomial_X_sub_C` says it is not `X₁ - c` for
any `c`, and
`OkaTest.GermQuotientDegreeOne.not_isLocalWeierstrassPolynomial_of_fromPolynomial_eq_skewDiagonal`
says it is not a local Weierstrass polynomial of any degree, the coefficient `1 - X₀` being a unit
and so not in the maximal ideal. -/
def skewDiagonal : LocalOkaRing (Fin 2) :=
  fromPolynomial (X - C (LocalOkaRing.coord (0 : Fin 1))) * (1 + lastVar)

/-- **The skew diagonal is not `X₁ - c` for any germ `c`**, so
`OkaTest.GermQuotientDegreeOne.skewDiagonalEquiv` is not an instance of
`LocalOkaRing.quotientGraphEquiv` in disguise.

**This is what makes that equivalence a non-vacuity rather than a respelling.** The obvious
candidate for a germ with a simple zero along the last axis is `X₁ - X₀²`, and it is useless
here: it is `X₁ - C c` on the nose, so it witnesses nothing that
`OkaTest.GermQuotientDegreeOne.diagonalEquiv` does not already witness.

`LocalOkaRing.fromPolynomial` is an injective `AlgHom` (`LocalOkaRing.fromPolynomial_injective`)
and `LocalOkaRing.fromPolynomial_X` turns `1 + X₁` into the image of `1 + X`, so both sides are
images of polynomials and an equality between them is an equality of polynomials.
`Polynomial.natDegree` then separates them: two on the left, one on the right. -/
theorem skewDiagonal_ne_fromPolynomial_X_sub_C (c : LocalOkaRing (Fin 1)) :
    skewDiagonal ≠ LocalOkaRing.fromPolynomial (X - C c) := by
  intro h
  have hm : (1 + X : (LocalOkaRing (Fin 1))[X]) = X + C 1 := by rw [add_comm, C_1]
  have hmonic : (1 + X : (LocalOkaRing (Fin 1))[X]).Monic := by rw [hm]; exact monic_X_add_C 1
  rw [skewDiagonal, show (1 + (lastVar : LocalOkaRing (Fin 2)))
      = LocalOkaRing.fromPolynomial (1 + X : (LocalOkaRing (Fin 1))[X]) by
        rw [map_add, map_one, fromPolynomial_X], ← map_mul] at h
  have hd := congrArg Polynomial.natDegree (LocalOkaRing.fromPolynomial_injective h)
  rw [natDegree_mul (X_sub_C_ne_zero _) hmonic.ne_zero, natDegree_X_sub_C, hm,
    natDegree_X_add_C, natDegree_X_sub_C] at hd
  omega

/-- **The skew diagonal is not a local Weierstrass polynomial of any degree.**

The statement is about the *preimage*, which is the only place it can live: `skewDiagonal` is an
element of `LocalOkaRing (Fin 2)` and `IsLocalWeierstrassPolynomial` is a predicate on
polynomials, so what is denied is that any polynomial mapping to it is one. That quantifier is
harmless because `LocalOkaRing.fromPolynomial` is injective: there is exactly one such
polynomial, `(X - C X₀)(1 + X)`.

The witness is the coefficient of `X₁`, which is `1 - X₀` and has constant term `1`: a local
Weierstrass polynomial needs every coefficient below the leading one to vanish at the origin, and
this one is a unit. **Nothing here is special to degree one** — the degree of the polynomial is
computed rather than assumed, and it is the Weierstrass condition at the index below the leading
coefficient that fails. -/
theorem not_isLocalWeierstrassPolynomial_of_fromPolynomial_eq_skewDiagonal
    {q : (LocalOkaRing (Fin 1))[X]} (hq : LocalOkaRing.fromPolynomial q = skewDiagonal) :
    ¬ IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring (Fin 1)).toSubring) q) := by
  intro h
  have hqq : q = (X - C (LocalOkaRing.coord (0 : Fin 1))) * (1 + X) :=
    LocalOkaRing.fromPolynomial_injective <| by
      rw [hq, skewDiagonal, map_mul, map_add, map_one, fromPolynomial_X]
  have hone : (1 + X : (LocalOkaRing (Fin 1))[X]).Monic := by
    rw [add_comm, ← C_1]; exact monic_X_add_C 1
  have hmonic : q.Monic := by rw [hqq]; exact (monic_X_sub_C _).mul hone
  have hdeg : q.natDegree = 2 := by
    rw [hqq, natDegree_mul (X_sub_C_ne_zero _) hone.ne_zero, natDegree_X_sub_C,
      add_comm (1 : (LocalOkaRing (Fin 1))[X]) X, ← C_1, natDegree_X_add_C]
  have hlt : (1 : WithBot ℕ) <
      (Polynomial.map (Subring.subtype (localOkaSubring (Fin 1)).toSubring) q).degree := by
    rw [Polynomial.degree_map_eq_of_injective Subtype.val_injective,
      Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
    exact_mod_cast Nat.one_lt_two
  have h1 := h.apply_zero 1 hlt
  have hc1 : q.coeff 1 = 1 - LocalOkaRing.coord (0 : Fin 1) := by
    have hexp : ((X - C (LocalOkaRing.coord (0 : Fin 1))) * (1 + X) : (LocalOkaRing (Fin 1))[X])
        = X ^ 2 + C (1 - LocalOkaRing.coord (0 : Fin 1)) * X
          - C (LocalOkaRing.coord (0 : Fin 1)) := by
      rw [map_sub, map_one]; ring
    rw [hqq, hexp]
    simp
  rw [Polynomial.coeff_map, hc1] at h1
  simp only [map_sub, map_one] at h1
  rw [show (MvPowerSeries.constantCoeff ((localOkaSubring (Fin 1)).toSubring.subtype
    (LocalOkaRing.coord (0 : Fin 1)))) = (0 : ℂ) from LocalOkaRing.constantCoeff_coord 0,
    sub_zero] at h1
  exact one_ne_zero h1

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

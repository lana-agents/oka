/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Polynomial
import Oka.Weierstrass

/-!
# Germs of polynomial functions

The germ at a point `y ∈ ℂ^ι` of the holomorphic function defined by a polynomial, as a
`ℂ`-algebra map `MvPolynomial ι ℂ →ₐ[ℂ] LocalOkaRing ι`.

This is separated from `Oka/Polynomial.lean` because `OkaRing.germ` lives in
`Oka/Weierstrass.lean`, and "a polynomial function is holomorphic" should not depend on
Weierstrass theory.

## Main definitions

- `LocalOkaRing.ofMvPolynomial y`: the germ at `y` of the holomorphic function defined by a
  polynomial.

## Main results

- `LocalOkaRing.constantCoeff_ofMvPolynomial`: the constant term of the germ at `y` is the
  value `MvPolynomial.eval y p`, with `LocalOkaRing.constantCoeff_coe_ofMvPolynomial` its
  `simp` normal form. In particular the germ is a unit exactly when `p` does not vanish at `y`,
  which is what identifies the zero set of a family of polynomials with the points where their
  germs are non-units.
-/

open TopologicalSpace

variable {ι : Type*} [Fintype ι]

namespace LocalOkaRing

/-- The germ at `y` of the holomorphic function on `ℂ^ι` defined by a polynomial. -/
noncomputable def ofMvPolynomial (y : ι → ℂ) : MvPolynomial ι ℂ →ₐ[ℂ] LocalOkaRing ι :=
  (OkaRing.germ (U := ⊤) (y := y) trivial).comp (OkaRing.ofMvPolynomial ⊤)

lemma ofMvPolynomial_eq (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    ofMvPolynomial y p = OkaRing.germ (U := ⊤) (y := y) trivial (OkaRing.ofMvPolynomial ⊤ p) :=
  rfl

/-- The constant term of the germ at `y` of a polynomial is its value at `y`. -/
lemma constantCoeff_ofMvPolynomial (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    LocalOkaRing.constantCoeff (ofMvPolynomial y p) = MvPolynomial.eval y p := by
  rw [ofMvPolynomial_eq, OkaRing.constantCoeff_germ, OkaRing.evalHom_ofMvPolynomial]

/-- `constantCoeff_ofMvPolynomial` in `simp` normal form.

`LocalOkaRing.constantCoeff_apply` is itself a `simp` lemma, so `simp` rewrites
`LocalOkaRing.constantCoeff P` to `MvPowerSeries.constantCoeff ↑P` before it ever sees
`constantCoeff_ofMvPolynomial`; tagging that lemma `@[simp]` therefore does nothing. This is the
form a goal is actually in by the time `simp` gets there. -/
@[simp]
lemma constantCoeff_coe_ofMvPolynomial (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    MvPowerSeries.constantCoeff ((ofMvPolynomial y p : LocalOkaRing ι) : MvPowerSeries ι ℂ) =
      MvPolynomial.eval y p := by
  rw [← constantCoeff_apply, constantCoeff_ofMvPolynomial]

/-- The germ at `y` of a polynomial is a unit exactly when the polynomial does not vanish
at `y`. -/
lemma isUnit_ofMvPolynomial_iff (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    IsUnit (ofMvPolynomial y p) ↔ MvPolynomial.eval y p ≠ 0 := by
  rw [isUnit_iff, constantCoeff_ofMvPolynomial]

end LocalOkaRing

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Algebra.MvPolynomial.Taylor
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
- `LocalOkaRing.ofMvPolynomial_taylorAlgHom`: **the germ at `y` is the germ at the origin of the
  shifted polynomial** `p(x + y)`. Since `LocalOkaRing ι` is the germ ring at the origin by
  construction, this is what lets a statement about germs at `y` be transported to one about
  germs at the origin, and it is a statement about *polynomials* only in that both sides are
  spelled with `LocalOkaRing.ofMvPolynomial`.
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

/-- **The germ at `y` of a polynomial is the germ at the origin of the polynomial shifted by
`y`.**

The germ at `y` is by definition the Taylor series at the origin of the translate of the
function (`OkaRing.germ`), and translating the *function* attached to `p` is reading the shifted
*polynomial* `p(x + y)` as a function — which is `MvPolynomial.eval_taylorAlgHom`. So no analysis
is involved: the two ingredients are `OkaRing.germ_shift`, which moves the base point, and
`OkaRing.germ_restrict`, which crosses from `(⊤ : Opens (ι → ℂ)).shift y` back to `⊤`. -/
lemma ofMvPolynomial_taylorAlgHom (y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    ofMvPolynomial (0 : ι → ℂ) (MvPolynomial.taylorAlgHom y p) = ofMvPolynomial y p := by
  have h0 : (0 : ι → ℂ) ∈ (⊤ : Opens (ι → ℂ)).shift y := by simp
  have hshift : OkaRing.shift (⊤ : Opens (ι → ℂ)) y (OkaRing.ofMvPolynomial ⊤ p) =
      OkaRing.ofMvPolynomial ((⊤ : Opens (ι → ℂ)).shift y) (MvPolynomial.taylorAlgHom y p) :=
    Subtype.ext (funext fun w ↦ (MvPolynomial.eval_taylorAlgHom y (w : ι → ℂ) p).symm)
  calc ofMvPolynomial (0 : ι → ℂ) (MvPolynomial.taylorAlgHom y p)
      = OkaRing.germ h0
          (OkaRing.restrict le_top (OkaRing.ofMvPolynomial ⊤ (MvPolynomial.taylorAlgHom y p))) :=
        (OkaRing.germ_restrict le_top h0 _).symm
    _ = OkaRing.germ h0 (OkaRing.shift ⊤ y (OkaRing.ofMvPolynomial ⊤ p)) := by
        rw [OkaRing.restrict_ofMvPolynomial, hshift]
    _ = ofMvPolynomial y p :=
        OkaRing.germ_shift (U := ⊤) y (show y ∈ (⊤ : Opens (ι → ℂ)) from trivial) h0
          (zero_add y) _

end LocalOkaRing

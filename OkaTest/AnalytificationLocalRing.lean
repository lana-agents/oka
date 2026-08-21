/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Oka

/-!
# Non-vacuity of the completion of the local ring at the origin

`Oka/Analytification/LocalRing.lean` proves that the completion of `ℂ[x]_{(x)}` is
`MvPowerSeries ι ℂ` and that the formal power series are flat over it. Both statements would be
true and empty of a map that collapsed everything: an isomorphism of `ℂ`-algebras says nothing
about polynomials and their Taylor expansions unless it is *the* map induced by the inclusion,
and flatness of a ring map to the zero ring is free.

The library file names the triangle on polynomials
(`ComplexAnalytic.polyLocalAdicCompletionEquiv_of_algebraMap`). This file adds the two facts that
say the local ring is not collapsed by any of it:

* `ComplexAnalytic.polyLocalToMvPowerSeries_injective` — **a rational function regular at the
  origin is determined by its Taylor series.** The embedding is injective, so `ℂ[x]_{(x)}` really
  is a subring of `ℂ⟦x⟧` and the flatness statement is about an extension rather than a quotient.
* `ComplexAnalytic.polyLocalToMvPowerSeries_coord` and
  `ComplexAnalytic.polyLocalToMvPowerSeries_inv` — the embedding is computed on an element that
  is *not* a polynomial: the inverse of `1 - xᵢ`, which exists in `ℂ[x]_{(x)}` precisely because
  `1 - xᵢ` does not vanish at the origin, and whose image is a power series with constant term
  `1`. Nothing about the triangle on polynomials forces a denominator to go anywhere in
  particular.
-/

open MvPowerSeries IsLocalRing

universe u

namespace ComplexAnalytic

variable {ι : Type u} [Finite ι]

/-- **A rational function regular at the origin is determined by its Taylor series.**

The embedding of `ℂ[x]_{(x)}` in `ℂ⟦x⟧` is the canonical map into the completion read through
`ComplexAnalytic.polyLocalAdicCompletionEquiv`, and a Noetherian local ring is separated for its
maximal-adic topology, so that map is injective. -/
theorem polyLocalToMvPowerSeries_injective :
    Function.Injective (polyLocalToMvPowerSeries (ι := ι)) := by
  have h : ⇑(polyLocalToMvPowerSeries (ι := ι)) =
      polyLocalAdicCompletionEquiv ∘ AdicCompletion.of (maximalIdeal (polyLocal ι)) (polyLocal ι) :=
    funext fun a ↦ (polyLocalAdicCompletionEquiv_algebraMap a).symm
  rw [h]
  exact (polyLocalAdicCompletionEquiv (ι := ι)).injective.comp (AdicCompletion.of_injective _ _)

omit [Finite ι] in
/-- The image of a coordinate is the corresponding variable. -/
theorem polyLocalToMvPowerSeries_coord (i : ι) :
    polyLocalToMvPowerSeries (algebraMap (MvPolynomial ι ℂ) (polyLocal ι) (MvPolynomial.X i)) =
      (X i : MvPowerSeries ι ℂ) := by
  rw [polyLocalToMvPowerSeries_algebraMap]
  simp

omit [Finite ι] in
/-- **The embedding computed on something that is not a polynomial.** `1 - x₀` does not vanish at
the origin, so it is a unit of `ℂ[x]_{(x)}`; the image of its inverse is a power series with
constant term `1`, and in particular is not zero. -/
theorem polyLocalToMvPowerSeries_inv (i : ι) (u : (polyLocal ι)ˣ)
    (hu : (u : polyLocal ι) =
      algebraMap (MvPolynomial ι ℂ) (polyLocal ι) (1 - MvPolynomial.X i)) :
    constantCoeff (polyLocalToMvPowerSeries ((u⁻¹ : (polyLocal ι)ˣ) : polyLocal ι)) = 1 := by
  have h1 : polyLocalToMvPowerSeries
      ((u : polyLocal ι) * ((u⁻¹ : (polyLocal ι)ˣ) : polyLocal ι)) = 1 := by
    rw [Units.mul_inv]
    exact map_one _
  rw [map_mul, hu, polyLocalToMvPowerSeries_algebraMap] at h1
  have h2 := congrArg constantCoeff h1
  rw [map_mul, map_one] at h2
  have h3 : constantCoeff ((1 - MvPolynomial.X i : MvPolynomial ι ℂ) : MvPowerSeries ι ℂ) = 1 := by
    simp [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
  rw [h3, one_mul] at h2
  exact h2

end ComplexAnalytic

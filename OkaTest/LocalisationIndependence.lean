/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.AnalytificationDistinguishedOpen

/-!
# Non-vacuity of the independence of the presentation of a distinguished open

`ComplexAnalytic.localisationPresentationIsoOfDvdPow` identifies the presentations of the
localisation at two polynomials cutting out the same distinguished open. The reading that would
make it empty is that its hypotheses force the two polynomials to give the *same* presentation,
in which case it would be an identity in disguise and would say nothing about a choice.

The checks below close that, on `f` and `f ^ 2`:

* **The hypotheses are satisfiable at `f` and `f ^ 2`, for every presentation and every `f`** —
  `dvd_pow_sq` and `sq_dvd_pow`, with witnesses `2` and `1`. Nothing about the node is used, so
  this is the general statement that the isomorphism has instances at all.
* **And the two presentations really are different**, at the node with `f = z₀`:
  `localisationPresentation_ne_sq`. So the isomorphism is between two distinct objects of
  `ComplexAnalytic.Presentation`, and `Iso.refl` does not typecheck at this type — the same
  argument `OkaTest/LocalisationFunctor.lean`'s `presentation_ne` makes for the structure map.

Together: the isomorphism exists, and what it identifies is not already equal.

`f` and `f ^ 2` are also the smallest witness that the hypotheses are strictly weaker than
Mathlib's `IsLocalization.Away.of_associated`, which the mirror file
`Oka/RingTheory/Localization/Away/Basic.lean` records: `Associated f (f ^ 2)` fails whenever `f`
is not a unit, and `z₀` in `ℂ[z₀, z₁] ⧸ (z₀ z₁)` is not.
-/

open CategoryTheory MvPolynomial ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.LocalisationIndependence

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- The image of `f ^ 2` divides the second power of the image of `f`; it is equal to it. -/
theorem dvd_pow_sq : ∃ N, Ideal.Quotient.mk (presentationIdeal.{u} g) (f ^ 2) ∣
    Ideal.Quotient.mk (presentationIdeal.{u} g) f ^ N :=
  ⟨2, by simp⟩

/-- The image of `f` divides the first power of the image of `f ^ 2`. -/
theorem sq_dvd_pow : ∃ M, Ideal.Quotient.mk (presentationIdeal.{u} g) f ∣
    Ideal.Quotient.mk (presentationIdeal.{u} g) (f ^ 2) ^ M :=
  ⟨1, by simp⟩

/-- **The isomorphism has an instance at every presentation and every `f`.** -/
def isoSq : (⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ : Presentation.{u}) ≅
    ⟨n + 1, k + 1, localisationPresentation.{u} g (f ^ 2)⟩ :=
  localisationPresentationIsoOfDvdPow.{u} g f (f ^ 2) (dvd_pow_sq.{u} g f) (sq_dvd_pow.{u} g f)

/-- **The two presentations are different tuples**, so `isoSq` is not an identity in disguise:
the last equation is `t·f - 1` on one side and `t·f² - 1` on the other, and `f ≠ f²` because
`MvPolynomial.rename` along `ComplexAnalytic.localisationIncl` is injective and `z₀` and `z₀²`
have different total degrees. -/
theorem localisationPresentation_ne_sq :
    localisationPresentation.{u} nodePres.{u} nodeX.{u} ≠
      localisationPresentation.{u} nodePres.{u} (nodeX.{u} ^ 2) := by
  intro hcon
  have h := congrFun hcon (Fin.last 1)
  rw [localisationPresentation_last, localisationPresentation_last, sub_left_inj] at h
  have h2 := mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := ℂ) (localisationVar.{u} 2)) h
  have h3 := MvPolynomial.rename_injective _ (localisationIncl_injective.{u} 2) h2
  simpa using congrArg MvPolynomial.totalDegree h3

end OkaTest.LocalisationIndependence

end

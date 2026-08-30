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
* **And the triangle it satisfies is not `𝟙 ≫ h = h`** — `isoSq_hom_comp`, an instance of
  `ComplexAnalytic.localisationPresentationIsoOfDvdPow_hom_comp`. Both sides of that equation are
  morphisms `⟨n + 1, k + 1, localisationPresentation g f⟩ ⟶ ⟨n, k, g⟩`, with the same source *and*
  the same target, so nothing about its endpoints makes it non-trivial. What does is that the
  left-hand side factors through `⟨n + 1, k + 1, localisationPresentation g (f ^ 2)⟩`, which the
  bullet above separates from the source at the node — so `isoSq.hom` is not an identity there,
  and the equation relates two presentations rather than restating one.

Together: the isomorphism exists, what it identifies is not already equal, and the triangle it
satisfies runs through the object that separates them.

`f` and `f ^ 2` are also the pair showing that these hypotheses are strictly weaker than
Mathlib's `IsLocalization.Away.of_associated`, which the mirror file
`Oka/RingTheory/Localization/Away/Basic.lean` records: they satisfy the hypotheses at every
presentation, by `dvd_pow_sq` and `sq_dvd_pow` below, and need not be associated — that file's
witness is `2` and `4` in `ℤ`.

## The unit-multiple statements, and what their witness can and cannot be

`ComplexAnalytic.exists_mk_rename_eq` says every polynomial of a localisation is a unit multiple
of a renamed one, in the presented algebra. The reading that would empty it is the one that
empties every equation in a ring: **that the ring is zero**, in which case it and
`ComplexAnalytic.localisationPresentationIsoOfUnitMul` hold of nothing and the unit group is
trivial. That is not a hypothetical here — for `f = 0` the last equation is `0 = 1` and the
presented algebra really is the zero ring.

`nontrivial_presentedAlgebra_localisation_node` closes it at the node localised at `z₀`, and the
witness is the point `(1, 0, 1)` that `OkaTest/AnalytificationDistinguishedOpen.lean` already
built: **a point of the analytification is an evaluation that kills every relation**, so the ideal
misses `1` and the quotient is not the zero ring. Nothing about the localisation is used beyond
its being presented, which is why the proof is four lines and not a computation in `ℂ[x, y, t]`.

**What is not checked, and the first of the two is a real question with a known route.** That
the `Q` the existential produces can never be `q` itself — that is, that the unit is doing work —
is **not** established here, and the reason is that nobody has written the argument, not that the
argument is out of reach. **Evaluation does separate**, at the family of points rather than at
one: a point of this analytification is a common zero of `z₀z₁` and `t·z₀ - 1`, so it is
`(x, 0, 1/x)` for any `x ≠ 0`, of which the point above is the member at `x = 1`. On it `t` takes
the value `1/x` and a renamed `Q` takes `Q(x, 0)`, so `mk (rename Q) = mk (X_t)` would force
`x · Q(x, 0) = 1` for **every** non-zero `x`, and a polynomial with infinitely many roots is zero.
What that costs is the family — one parameterised point, where this file has one point — and the
polynomial-identity step; **it does not need the identification of this localisation with
`ℂ[z₀, z₀⁻¹]`**, which an earlier version of this paragraph claimed and which is a much larger
statement.

And whether `f` and `f ^ 2` are associated at the node is untouched, as before: no statement below
mentions `Associated`, and `localisationPresentation_ne_sq` distinguishes the two presentations by
total degree without saying anything about units.
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

/-- **The triangle at that instance**: `isoSq` carries the structure map of `A_{f²}` to the
structure map of `A_f`. With `localisationPresentation_ne_sq` below, this is the triangle holding
between two presentations that are not the same tuple. -/
theorem isoSq_hom_comp :
    (isoSq.{u} g f).hom ≫ localisationHom.{u} g (f ^ 2) = localisationHom.{u} g f :=
  localisationPresentationIsoOfDvdPow_hom_comp.{u} g f (f ^ 2) (dvd_pow_sq.{u} g f)
    (sq_dvd_pow.{u} g f)

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

/-- **The ideal of the node localised at `z₀` is not everything.**

Evaluating at the point `(1, 0, 1)` kills every relation of
`ComplexAnalytic.localisationPresentation nodePres nodeX` — that is what
`nodeLocPoint` being a point of the analytification says, through
`ComplexAnalytic.mem_zeroLocus_polySection_iff` — so the ideal is inside the kernel of that
evaluation, which does not contain `1`. -/
theorem presentationIdeal_localisation_node_ne_top :
    presentationIdeal.{u} (localisationPresentation.{u} nodePres.{u} nodeX.{u}) ≠ ⊤ := by
  intro hcon
  have hle : presentationIdeal.{u} (localisationPresentation.{u} nodePres.{u} nodeX.{u}) ≤
      RingHom.ker (MvPolynomial.eval
        (nodeLocPoint.{u}.1.1 : ULift.{u} (Fin (2 + 1)) → ℂ)) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact (mem_zeroLocus_polySection_iff _ _).1 nodeLocPoint.{u}.2 j
  have h1 := RingHom.mem_ker.1 (hle ((Ideal.eq_top_iff_one _).1 hcon))
  rw [map_one] at h1
  exact one_ne_zero h1

/-- **So the presented algebra the unit-multiple statements are equations in is not the zero
ring**, at the node localised at `z₀`.

`ComplexAnalytic.exists_mk_rename_eq` and `ComplexAnalytic.localisationPresentationIsoOfUnitMul`
are statements about `Ideal.Quotient.mk` and the units of this algebra; in the zero ring both hold
of nothing, and for `f = 0` that is exactly what happens. -/
instance nontrivial_presentedAlgebra_localisation_node :
    Nontrivial (PresentedAlgebra.{u} (2 + 1) (1 + 1)
      (localisationPresentation.{u} nodePres.{u} nodeX.{u})) :=
  Ideal.Quotient.nontrivial_iff.mpr presentationIdeal_localisation_node_ne_top.{u}

end OkaTest.LocalisationIndependence

end

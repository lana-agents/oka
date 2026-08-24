/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.AnalytificationDistinguishedOpen

/-!
# Non-vacuity of the composite of two localisations of a presentation

`ComplexAnalytic.localisationPresentationIsoMul` identifies the presentation obtained by localising
twice with the one obtained by localising once at the product. It carries no hypotheses at all, so
the reading that would make it empty is not that it has no instances — it is that the two sides
might be the *same* presentation, in which case the isomorphism would be an identity in disguise
and would say nothing about a composite.

The checks below close that:

* **The two sides are never the same object of `ComplexAnalytic.Presentation`** —
  `presentation_ne_mul`, for every `g`, `f` and `f₁`, because localising twice adjoins two
  variables and localising once adjoins one. So `Iso.refl` does not typecheck at this type, the
  same argument `OkaTest/LocalisationIndependence.lean`'s `localisationPresentation_ne_sq` makes
  for the isomorphism beside it.
* **And the construction is inhabited at the node** — `nodeCompositeIso`, at `f = f₁ = z₀` in
  `ℂ[z₀, z₁] ⧸ (z₀ z₁)`. Nothing about the node is used by the general statement; this is the
  witness that the arities line up on a presentation that was written by hand.

The node instance is the one worth reading, because it is the smallest overlap a cover can have:
`D(z₀) ∩ D(z₀) = D(z₀)`. Composing the localisation at `z₀` with itself lands at `z₀ * z₀`, and
`ComplexAnalytic.localisationPresentationIsoOfDvdPow` takes it back to `z₀` — so the two files
together say that going round the overlap twice returns to where it started, which is the shape of
a cocycle condition and not merely of an arity check.

## What is not checked here

That the composite isomorphism is *the* one a coherence law would ask for. That is
`ComplexAnalytic.localisationPresentedAlgebraEquivMul_localisationRingHom`, proved in the library
file as a statement about the structure maps, and nothing below re-states it at the node: the two
theorems here are about presentations as tuples of polynomials and about arities, and neither
mentions `ComplexAnalytic.localisationRingHom`.
-/

open CategoryTheory MvPolynomial ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.LocalisationComposite

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f f₁ : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The two presentations are different objects**, so
`ComplexAnalytic.localisationPresentationIsoMul` is not an identity in disguise: localising twice
adjoins two variables and localising once adjoins one, and the number of variables is a field of
`ComplexAnalytic.Presentation`. -/
theorem presentation_ne_mul :
    (⟨n + 1 + 1, k + 1 + 1, localisationPresentation.{u} (localisationPresentation.{u} g f)
        (MvPolynomial.rename (localisationIncl.{u} n) f₁)⟩ : Presentation.{u}) ≠
      ⟨n + 1, k + 1, localisationPresentation.{u} g (f₁ * f)⟩ := by
  intro hcon
  have h : n + 1 + 1 = n + 1 := congrArg Presentation.n hcon
  omega

/-- The image of `z₀` divides the first power of the image of `z₀ * z₀`, and conversely for the
second power. The two hypotheses `ComplexAnalytic.localisationPresentationIsoOfDvdPow` asks for, at
the pair the composite at the node produces. -/
theorem nodeX_dvd :
    ∃ N, Ideal.Quotient.mk (presentationIdeal.{u} nodePres.{u}) nodeX.{u} ∣
      Ideal.Quotient.mk (presentationIdeal.{u} nodePres.{u}) (nodeX.{u} * nodeX.{u}) ^ N :=
  ⟨1, by
    rw [pow_one, map_mul]
    exact dvd_mul_right _ _⟩

/-- The companion of `nodeX_dvd`: the image of `z₀ * z₀` divides the second power of the image of
`z₀`, being equal to it. -/
theorem nodeX_mul_dvd :
    ∃ M, Ideal.Quotient.mk (presentationIdeal.{u} nodePres.{u}) (nodeX.{u} * nodeX.{u}) ∣
      Ideal.Quotient.mk (presentationIdeal.{u} nodePres.{u}) nodeX.{u} ^ M :=
  ⟨2, by simp [pow_two]⟩

/-- **Localising the node at `z₀` twice returns to the localisation at `z₀`.**

The composite of `ComplexAnalytic.localisationPresentationIsoMul`, which lands at `z₀ * z₀`, with
`ComplexAnalytic.localisationPresentationIsoOfDvdPow`, which identifies `z₀ * z₀` with `z₀` because
they cut out the same distinguished open. This is `D(z₀) ∩ D(z₀) = D(z₀)` on the presentations, and
it is the smallest instance of the composite that a cover would produce. -/
def nodeCompositeIso :
    (⟨4, 3, localisationPresentation.{u} (localisationPresentation.{u} nodePres.{u} nodeX.{u})
        (MvPolynomial.rename (localisationIncl.{u} 2) nodeX.{u})⟩ : Presentation.{u}) ≅
      ⟨3, 2, localisationPresentation.{u} nodePres.{u} nodeX.{u}⟩ :=
  (localisationPresentationIsoMul.{u} nodePres.{u} nodeX.{u} nodeX.{u}).trans
    (localisationPresentationIsoOfDvdPow.{u} nodePres.{u} (nodeX.{u} * nodeX.{u}) nodeX.{u}
      nodeX_dvd.{u} nodeX_mul_dvd.{u})

end OkaTest.LocalisationComposite

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SimpleZeroStalk
import Oka.Polynomial.Germ

/-!
# A polynomial hypersurface with a nonvanishing derivative projects isomorphically on stalks

`Oka/AnalyticSpace/SimpleZeroStalk.lean` states the simple-zero hypothesis as one Taylor
coefficient of the germ of the cutting section:
`MvPowerSeries.coeff (Finsupp.single (Fin.last n) 1)` of it is nonzero. That is the right form for
a general holomorphic `F`, and it is the wrong form for a caller who has a **polynomial**, because
such a caller has a derivative and not a Taylor coefficient. This file closes that gap: when the
cutting section is `OkaRing.ofMvPolynomial ⊤ P`, the hypothesis is

```
MvPolynomial.eval (i.base x) (MvPolynomial.pderiv (Fin.last n) P) ≠ 0
```

— *"the partial derivative of `P` in the last variable does not vanish at the point"*, with no
germ, no power series and no relabelling anywhere in it.

## What supplies it, and what it is not

The whole content is `LocalOkaRing.coeff_single_one_ofMvPolynomial`
(`Oka/Polynomial/Germ.lean`): the coefficient of `xᵢ` in the germ at `y` of a polynomial is
`∂p/∂xᵢ` evaluated at `y`. Each theorem below is that rewrite and the corresponding theorem of
`Oka/AnalyticSpace/SimpleZeroStalk.lean`, in two lines; the step from the cutting section to the
germ is `LocalOkaRing.ofMvPolynomial_eq`, which is `rfl`.

**No derivative operator on `LocalOkaRing` is constructed here or anywhere**, and
`Oka/Regular.lean` and `OkaTest/GermQuotientDegreeOne.lean` still record correctly that there is
none and that no bridge from one has been built. The derivative below is Mathlib's
`MvPolynomial.pderiv`, on polynomials, and the route reaches the germ's coefficient without ever
differentiating a germ — by translating the polynomial to the point and reading a *polynomial*
coefficient off the shift.

## Main results

- `ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_pderiv` and
  `ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_pderiv`: **the projection of a polynomial
  hypersurface with a nonvanishing last partial derivative is an isomorphism on stalks**, for the
  `Fin`-indexed `ℂ^(n+1)`.
- `ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_pderiv` and
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv`: the same at the
  `ULift (Fin _)` indexing, which is the one the Riemann-existence line consumes.

## What is not here

**No `IsLocalIso` and no `IsFiniteEtale`, and this file moves neither any closer than its
import did.** `Oka/AnalyticSpace/SimpleZeroStalk.lean` says of its own conclusion that *"nothing
below says anything about the underlying map of `i ≫ p`, not even that it is open"*, and nothing
below says anything about it either: the four results are the four it re-states, at a hypothesis
a polynomial supplies.

**Nothing reads `StandardEtalePair.cond`.** The step that would — from
`derivative f * p₁ + f * p₂ = g ^ n` in `R[X]`, at a point where `f` vanishes and `g` does not, to
the derivative being nonzero there — is about `Polynomial.derivative` in a **one**-variable
polynomial ring over `MvPolynomial (ULift (Fin n)) ℂ`, and reaching `MvPolynomial.pderiv` of the
image in `MvPolynomial (ULift (Fin (n+1))) ℂ` needs a bridge between the two that is not here and
has not been measured. `Oka/Analytification/StandardEtaleAnalytification.lean` records what is
left of that step.

**No hypersurface inside an open subset.** As in the file this one builds on, `F` is entire and
the ambient space is the whole of `ℂ^(n+1)`; the transport to an open base is
`Oka/AnalyticSpace/OpenBaseProjection.lean` and it is stated for the germ hypothesis, not for this
one.

**No non-polynomial gain.** Every statement here is an instance of one in the imported file, so a
consumer holding a general holomorphic `F` should use that file directly; this one is not more
general and does not try to be.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Function

universe u

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

section Fin

variable {X : LocallyRingedSpace.{0}} {i : X ⟶ complexSpace (Fin (n + 1))}
  {P : MvPolynomial (Fin (n + 1)) ℂ}

/-- **The projection of a polynomial hypersurface to its base is bijective on stalks at a point
where the last partial derivative does not vanish.**

This is `ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_coeff` with its Taylor coefficient
read as a derivative by `LocalOkaRing.coeff_single_one_ofMvPolynomial`. The vanishing of `P` at
the point is not a hypothesis here either: it follows from `hcut`, by
`ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` inside the theorem this one calls. -/
theorem bijective_stalkMap_comp_projCoords_of_pderiv
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (x : X)
    (hlin : MvPolynomial.eval (i.base x) (MvPolynomial.pderiv (Fin.last n) P) ≠ 0) :
    Function.Bijective ((i ≫ okaMapHom (projCoords n)).stalkMap x).hom := by
  refine bijective_stalkMap_comp_projCoords_of_coeff hcut x ?_
  rw [← LocalOkaRing.ofMvPolynomial_eq, LocalOkaRing.coeff_single_one_ofMvPolynomial]
  exact hlin

/-- **The same as an isomorphism.** -/
theorem isIso_stalkMap_comp_projCoords_of_pderiv
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (x : X)
    (hlin : MvPolynomial.eval (i.base x) (MvPolynomial.pderiv (Fin.last n) P) ≠ 0) :
    IsIso ((i ≫ okaMapHom (projCoords n)).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_stalkMap_comp_projCoords_of_pderiv hcut x hlin)

end Fin

section ULift

variable {X : LocallyRingedSpace.{u}} {i : X ⟶ complexAffineSpace.{u} (n + 1)}
  {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}

/-- **The same for `complexAffineSpace`**, whose coordinates are indexed by `ULift (Fin _)`.

The relabelling that `ComplexAnalytic.bijective_stalkMap_comp_uliftProj` carries in its hypothesis
does not appear here for the same reason it does not appear in
`ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_coeff`: the coefficient — and now the
derivative — is read at the index type the space actually has, `ULift.up (Fin.last n)`. -/
theorem bijective_stalkMap_comp_uliftProj_of_pderiv
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (x : X)
    (hlin : MvPolynomial.eval (i.base x)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    Function.Bijective
      ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x).hom := by
  refine bijective_stalkMap_comp_uliftProj_of_coeff hcut x ?_
  rw [← LocalOkaRing.ofMvPolynomial_eq, LocalOkaRing.coeff_single_one_ofMvPolynomial]
  exact hlin

/-- **The same as an isomorphism.** This is the form the Riemann-existence line consumes, since
`ComplexAnalytic.AnalyticSpace` indexes its coordinates by `ULift (Fin _)` and a standard étale
presentation is given by polynomials. -/
theorem isIso_stalkMap_comp_uliftProj_of_pderiv
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P]) (x : X)
    (hlin : MvPolynomial.eval (i.base x)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    IsIso ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_stalkMap_comp_uliftProj_of_pderiv hcut x hlin)

end ULift

end ComplexAnalytic

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# The simple-zero stalk isomorphism is not vacuous, and its hypothesis has content

`Oka/AnalyticSpace/SimpleZeroStalk.lean` proves that the projection of a hypersurface with a
simple zero along the last axis is an isomorphism on stalks. Its hypotheses are a
`ComplexAnalytic.IsCutOutBy` and a condition on a germ, and nothing in that file exhibits a
single pair satisfying both. This file does, twice — once for each of the two indexings — and
then shows the germ condition is a real restriction rather than something every hypersurface
satisfies. Each of the two indexings is witnessed **three times**, at the three spellings the
hypothesis has: the order of a restricted power series, the coefficients that
`ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff` takes instead, and the partial
derivative that `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv`
(`Oka/AnalyticSpace/SimpleZeroPolynomial.lean`) takes when the cutting section comes from a
polynomial. At the `ULift (Fin _)` indexing the last two mention no relabelling at all, which is
the point of having them; **all three are about one space, one point and one section**, so the
three spellings are compared rather than merely each exhibited.

## The instance

The **hyperplane** `z_n = 0`: the cutting section is the last coordinate function
`ComplexAnalytic.coord (Fin.last n)`, the subspace is
`AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspace` of it — whose
`ComplexAnalytic.IsCutOutBy` is `…isCutOutBy_zeroLocusSubspaceι`, so nothing has to be checked
there — and the point is the origin. It is the smallest instance there is: the germ of the last
coordinate at the origin is `LocalOkaRing.coord (Fin.last n)` on the nose, so its restriction to
the last axis is `PowerSeries.X` and the order is `1` by `PowerSeries.order_X`.

**It is a genuine instance and not a degenerate one**: `n` is arbitrary, the hyperplane is a
hypersurface of `ℂ^(n+1)` of codimension one, and the conclusion is that the germ ring of the
hyperplane at the origin is the germ ring of `ℂ^n` — the statement one would want to be true.
What it does not exercise is a *curved* hypersurface, since here the graph the Weierstrass
argument produces is the zero function; see `## What this does not test`.

## The control

`OkaTest.SimpleZeroStalk.order_partialEval_germ_sq` computes the same order for `z_n ^ 2` and gets
`2`, so the hypothesis of the theorem fails there. That is what makes the hypothesis a
restriction: without it the statement would have to hold for every hypersurface through the
point, and `z_n ^ 2` is one.

`OkaTest.SimpleZeroStalk.coeff_germ_hyperplaneSectionSq` is the sharper half of the same control.
`ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` makes the vanishing half of the order condition
automatic for *every* cutting section, so it can carry no information at all; **the linear
coefficient is where all of the content is**, and that computation is what shows it excluding
something.

`OkaTest.SimpleZeroStalk.eval_pderiv_hyperplanePolySq` is that same control in the derivative
spelling, and `OkaTest.SimpleZeroStalk.hyperplaneSectionSq_eq` is what makes it a control on the
same section rather than on a different one: `z_n ^ 2` is the polynomial `X_n ^ 2` read as a
holomorphic function, so the derivative the third spelling asks about is the derivative of the
polynomial the first two are about.

The control stops at the order and does **not** claim that the stalk map fails to be an
isomorphism for `z_n ^ 2`. That is true — the germ ring of `ℂ^(n+1) ⧸ (z_n²)` is not reduced and
`LocalOkaRing (Fin n)` is — but proving it needs an invariant this repository does not carry to
that statement, and asserting it here without proving it is what the control exists to avoid.

## What this does not test

* **No curved hypersurface.** `z_n = 0` is its own Weierstrass graph, so
  `LocalOkaRing.exists_span_eq_span_X_sub_C` is exercised at `c = 0`. A witness at `c ≠ 0` — say
  `z_n = z_0 ^ 2` — would exercise the preparation theorem properly and is not built here.
* **No failure of the conclusion.** See `## The control`.
* **Nothing about the underlying map**, which is what finiteness would be about and is not part
  of the statement being witnessed.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.SimpleZeroStalk

variable (n : ℕ)

/-! ### The `Fin`-indexed hyperplane -/

/-- **The last coordinate of `ℂ^(n+1)`**, whose zero locus is the hyperplane `z_n = 0`. -/
abbrev hyperplaneSection : OkaRing (⊤ : Opens (Fin (n + 1) → ℂ)) :=
  ComplexAnalytic.coord (Fin.last n)

/-- The origin lies on the hyperplane. -/
theorem zero_mem_zeroLocus :
    (0 : Fin (n + 1) → ℂ) ∈
      (complexSpace (Fin (n + 1))).zeroLocus ![hyperplaneSection n] := by
  refine (LocallyRingedSpace.mem_zeroLocus_iff _ _).2 fun j ↦ ?_
  fin_cases j
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact (not_isUnit_germ_ofMvPolynomial_iff (0 : Fin (n + 1) → ℂ)
    (MvPolynomial.X (Fin.last n))).2 (by simp)

/-- The origin, as a point of the hyperplane. -/
def origin : (complexSpace (Fin (n + 1))).zeroLocusSpace ![hyperplaneSection n] :=
  ⟨(0 : Fin (n + 1) → ℂ), zero_mem_zeroLocus n⟩

/-- **The germ of the last coordinate at the origin is the last variable.** The translation term
`OkaRing.germ_ofMvPolynomial_X` contributes is `0` because the point is the origin. -/
theorem germ_hyperplaneSection :
    OkaRing.germ (show (0 : Fin (n + 1) → ℂ) ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial)
      (hyperplaneSection n) = LocalOkaRing.coord (Fin.last n) := by
  rw [hyperplaneSection, ComplexAnalytic.coord_def, OkaRing.germ_ofMvPolynomial_X]
  simp

/-- **The germ has a simple zero along the last axis**, which is the hypothesis of
`ComplexAnalytic.isIso_stalkMap_comp_projCoords`. -/
theorem order_partialEval_germ :
    PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((OkaRing.germ (show (0 : Fin (n + 1) → ℂ) ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial)
        (hyperplaneSection n) : LocalOkaRing (Fin (n + 1))) :
          MvPowerSeries (Fin (n + 1)) ℂ)) = 1 := by
  rw [germ_hyperplaneSection, LocalOkaRing.coe_coord, MvPowerSeries.partialEval_X_self,
    PowerSeries.order_X]

/-- **The hypotheses of `ComplexAnalytic.isIso_stalkMap_comp_projCoords` are satisfiable**: the
projection of the hyperplane `z_n = 0` to `ℂ^n` is an isomorphism on stalks at the origin. -/
theorem isIso_stalkMap_hyperplane :
    IsIso ((((complexSpace (Fin (n + 1))).zeroLocusSubspaceι ![hyperplaneSection n]) ≫
      okaMapHom (projCoords n)).stalkMap (origin n)) :=
  isIso_stalkMap_comp_projCoords
    ((complexSpace (Fin (n + 1))).isCutOutBy_zeroLocusSubspaceι ![hyperplaneSection n])
    (origin n) (order_partialEval_germ n)

/-! ### The control: a double zero fails the hypothesis -/

/-- The square of the last coordinate, whose zero locus is the same hyperplane with a doubled
structure sheaf. -/
abbrev hyperplaneSectionSq : OkaRing (⊤ : Opens (Fin (n + 1) → ℂ)) :=
  ComplexAnalytic.coord (Fin.last n) ^ 2

/-- **The hypothesis is a restriction**: at `z_n ^ 2` the same order is `2`, not `1`, so
`ComplexAnalytic.isIso_stalkMap_comp_projCoords` does not apply to it. -/
theorem order_partialEval_germ_sq :
    PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((OkaRing.germ (show (0 : Fin (n + 1) → ℂ) ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial)
        (hyperplaneSectionSq n) : LocalOkaRing (Fin (n + 1))) :
          MvPowerSeries (Fin (n + 1)) ℂ)) = 2 := by
  rw [hyperplaneSectionSq, map_pow, germ_hyperplaneSection, Subalgebra.coe_pow,
    LocalOkaRing.coe_coord, map_pow, MvPowerSeries.partialEval_X_self, PowerSeries.order_X_pow]
  rfl

/-! ### The coefficient form of the hypothesis, at both indexings

`ComplexAnalytic.bijective_stalkMap_comp_projCoords_of_coeff` and its three siblings take the
germ condition as one coefficient rather than as an order — the vanishing half being free from
the `ComplexAnalytic.IsCutOutBy` they already hold. This section witnesses that form on the same
hyperplane, so the two spellings are exercised at the same pair. -/

/-- **Its linear coefficient along the last axis is `1`**, which is the whole hypothesis of
`ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_coeff`. The germ is
`LocalOkaRing.coord (Fin.last n)`, so the underlying series is `MvPowerSeries.X` and the
coefficient is read off `MvPowerSeries.coeff_X`. -/
theorem coeff_germ_hyperplaneSection :
    MvPowerSeries.coeff (Finsupp.single (Fin.last n) 1)
      ((OkaRing.germ (show (0 : Fin (n + 1) → ℂ) ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial)
        (hyperplaneSection n) : LocalOkaRing (Fin (n + 1))) :
          MvPowerSeries (Fin (n + 1)) ℂ) = 1 := by
  rw [germ_hyperplaneSection, LocalOkaRing.coe_coord, MvPowerSeries.coeff_X, if_pos rfl]

/-- **The control, in the coefficient spelling**: at `z_n ^ 2` the same coefficient is `0`, so the
hypothesis fails exactly where the order hypothesis did.

This is the sharper half of `OkaTest.SimpleZeroStalk.order_partialEval_germ_sq`, and what makes it
sharper is what `ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` says: the *vanishing* half of the
order condition holds for `z_n ^ 2` and for every other cutting section, automatically, so it can
carry no information. **The linear coefficient is where all of the content is**, and this is the
computation that shows it excluding something. -/
theorem coeff_germ_hyperplaneSectionSq :
    MvPowerSeries.coeff (Finsupp.single (Fin.last n) 1)
      ((OkaRing.germ (show (0 : Fin (n + 1) → ℂ) ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial)
        (hyperplaneSectionSq n) : LocalOkaRing (Fin (n + 1))) :
          MvPowerSeries (Fin (n + 1)) ℂ) = 0 := by
  rw [hyperplaneSectionSq, map_pow, germ_hyperplaneSection, Subalgebra.coe_pow,
    LocalOkaRing.coe_coord, MvPowerSeries.coeff_X_pow, if_neg]
  intro h
  exact absurd (congrArg (fun d ↦ d (Fin.last n)) h) (by simp)

/-- **The coefficient form reaches the same conclusion** as
`OkaTest.SimpleZeroStalk.isIso_stalkMap_hyperplane`, from the two coefficients instead of the
order. -/
theorem isIso_stalkMap_hyperplane_of_coeff :
    IsIso ((((complexSpace (Fin (n + 1))).zeroLocusSubspaceι ![hyperplaneSection n]) ≫
      okaMapHom (projCoords n)).stalkMap (origin n)) :=
  isIso_stalkMap_comp_projCoords_of_coeff
    ((complexSpace (Fin (n + 1))).isCutOutBy_zeroLocusSubspaceι ![hyperplaneSection n])
    (origin n) (fun h ↦ one_ne_zero ((coeff_germ_hyperplaneSection n).symm.trans h))

/-! ### The `ULift (Fin _)`-indexed hyperplane

`complexAffineSpace` (root namespace, `Oka/ComplexSpace.lean`) indexes its coordinates by
`ULift (Fin n)`, and
`ComplexAnalytic.isIso_stalkMap_comp_uliftProj`'s hypothesis is therefore about
`LocalOkaRing.uliftEquiv` of the germ. Relabelling sends a coordinate to a coordinate, which is
the only extra step. -/

/-- **Relabelling `ULift` sends a coordinate to a coordinate.** -/
theorem uliftEquiv_coord {ι : Type*} [Fintype ι] (j : ULift.{u} ι) :
    LocalOkaRing.uliftEquiv ι (LocalOkaRing.coord j) = LocalOkaRing.coord j.down := by
  apply Subtype.ext
  rw [LocalOkaRing.uliftEquiv_eq_renameEmb, LocalOkaRing.coe_renameEmb, LocalOkaRing.coe_coord,
    LocalOkaRing.coe_coord, MvPowerSeries.rename_X]
  rfl

/-- The last coordinate of `complexAffineSpace (n+1)`. -/
abbrev uliftHyperplaneSection : OkaRing (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) :=
  ComplexAnalytic.coord (ULift.up.{u} (Fin.last n))

/-- The origin lies on it. -/
theorem zero_mem_zeroLocus_ulift :
    (0 : ULift.{u} (Fin (n + 1)) → ℂ) ∈
      (complexAffineSpace.{u} (n + 1)).zeroLocus ![uliftHyperplaneSection.{u} n] := by
  refine (LocallyRingedSpace.mem_zeroLocus_iff _ _).2 fun j ↦ ?_
  fin_cases j
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact (not_isUnit_germ_ofMvPolynomial_iff (0 : ULift.{u} (Fin (n + 1)) → ℂ)
    (MvPolynomial.X (ULift.up.{u} (Fin.last n)))).2 (by simp)

/-- The origin, as a point of it. -/
def uliftOrigin :
    (complexAffineSpace.{u} (n + 1)).zeroLocusSpace ![uliftHyperplaneSection.{u} n] :=
  ⟨(0 : ULift.{u} (Fin (n + 1)) → ℂ), zero_mem_zeroLocus_ulift.{u} n⟩

/-- **The relabelled germ has a simple zero along the last axis**, which is the hypothesis of
`ComplexAnalytic.isIso_stalkMap_comp_uliftProj`. -/
theorem order_partialEval_germ_ulift :
    PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((LocalOkaRing.uliftEquiv (Fin (n + 1))
        (OkaRing.germ (show (0 : ULift.{u} (Fin (n + 1)) → ℂ) ∈
            (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial)
          (uliftHyperplaneSection.{u} n)) : LocalOkaRing (Fin (n + 1))) :
            MvPowerSeries (Fin (n + 1)) ℂ)) = 1 := by
  rw [uliftHyperplaneSection, ComplexAnalytic.coord_def, OkaRing.germ_ofMvPolynomial_X]
  rw [show (algebraMap ℂ (LocalOkaRing (ULift.{u} (Fin (n + 1))))
      ((0 : ULift.{u} (Fin (n + 1)) → ℂ) (ULift.up.{u} (Fin.last n))) +
      LocalOkaRing.coord (ULift.up.{u} (Fin.last n)) : LocalOkaRing (ULift.{u} (Fin (n + 1)))) =
      LocalOkaRing.coord (ULift.up.{u} (Fin.last n)) by simp]
  rw [uliftEquiv_coord, LocalOkaRing.coe_coord, MvPowerSeries.partialEval_X_self,
    PowerSeries.order_X]

/-- **The hypotheses of `ComplexAnalytic.isIso_stalkMap_comp_uliftProj` are satisfiable too.**
This is the indexing `ComplexAnalytic.AnalyticSpace` uses, and so the one the Riemann-existence
line will meet. -/
theorem isIso_stalkMap_uliftHyperplane :
    IsIso ((((complexAffineSpace.{u} (n + 1)).zeroLocusSubspaceι
        ![uliftHyperplaneSection.{u} n]) ≫
      okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap (uliftOrigin.{u} n)) :=
  isIso_stalkMap_comp_uliftProj
    ((complexAffineSpace.{u} (n + 1)).isCutOutBy_zeroLocusSubspaceι
      ![uliftHyperplaneSection.{u} n])
    (uliftOrigin.{u} n) (order_partialEval_germ_ulift.{u} n)

/-! ### The coefficient form at the `ULift (Fin _)` indexing

**This is where the coefficient form pays for itself.** Every statement below is about the germ
on `ComplexAnalytic.complexAffineSpace (n + 1)` itself: `LocalOkaRing.uliftEquiv` does not appear
in any of them, where `OkaTest.SimpleZeroStalk.order_partialEval_germ_ulift` needs it in the
statement and `OkaTest.SimpleZeroStalk.uliftEquiv_coord` to discharge it. -/

/-- **The germ of the last coordinate at the origin is the last variable**, at this indexing. The
translation term is `0` because the point is the origin, exactly as in
`OkaTest.SimpleZeroStalk.germ_hyperplaneSection`. -/
theorem germ_uliftHyperplaneSection :
    OkaRing.germ (show (0 : ULift.{u} (Fin (n + 1)) → ℂ) ∈
        (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial)
      (uliftHyperplaneSection.{u} n) = LocalOkaRing.coord (ULift.up.{u} (Fin.last n)) := by
  rw [uliftHyperplaneSection, ComplexAnalytic.coord_def, OkaRing.germ_ofMvPolynomial_X]
  simp

/-- **Its linear coefficient along the last axis is `1`** — read at the exponent
`Finsupp.single (ULift.up (Fin.last n)) 1` on the space itself, with no relabelling. -/
theorem coeff_germ_uliftHyperplaneSection :
    MvPowerSeries.coeff (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show (0 : ULift.{u} (Fin (n + 1)) → ℂ) ∈
          (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial)
        (uliftHyperplaneSection.{u} n) : LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) = 1 := by
  rw [germ_uliftHyperplaneSection, LocalOkaRing.coe_coord, MvPowerSeries.coeff_X, if_pos rfl]

/-- **The hypotheses of `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff` are
satisfiable**, at the indexing `ComplexAnalytic.AnalyticSpace` uses and so the one the
Riemann-existence line will meet. -/
theorem isIso_stalkMap_uliftHyperplane_of_coeff :
    IsIso ((((complexAffineSpace.{u} (n + 1)).zeroLocusSubspaceι
        ![uliftHyperplaneSection.{u} n]) ≫
      okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap (uliftOrigin.{u} n)) :=
  isIso_stalkMap_comp_uliftProj_of_coeff
    ((complexAffineSpace.{u} (n + 1)).isCutOutBy_zeroLocusSubspaceι
      ![uliftHyperplaneSection.{u} n])
    (uliftOrigin.{u} n)
    (fun h ↦ one_ne_zero ((coeff_germ_uliftHyperplaneSection.{u} n).symm.trans h))

/-! ### The derivative form, at both indexings

`Oka/AnalyticSpace/SimpleZeroPolynomial.lean` restates the four results witnessed above for a
cutting section that comes from a **polynomial**, replacing the Taylor coefficient by
`MvPolynomial.pderiv` of that polynomial at the point. The hyperplane is such a section on the
nose — `ComplexAnalytic.coord_def` says `ComplexAnalytic.coord j` *is*
`OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X j)`, definitionally — so the same instance witnesses
that form as well, at both indexings and with no new space to build.

**The control is the point of this section.** In the derivative spelling the hypothesis of the
double zero is `∂(z_n²)/∂z_n = 2·z_n` evaluated at the origin, which is `0`; and the section it
is the derivative of is `OkaTest.SimpleZeroStalk.hyperplaneSectionSq`, the same one the order and
coefficient controls above are about. So all three controls are about one pair, and the
derivative form excludes exactly what they exclude. -/

/-- **The last partial derivative of the hyperplane's equation is `1` at the origin**, which is
the whole hypothesis of `ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_pderiv`. -/
theorem eval_pderiv_hyperplanePoly :
    MvPolynomial.eval (0 : Fin (n + 1) → ℂ) (MvPolynomial.pderiv (Fin.last n)
      (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℂ)) = 1 := by
  simp

/-- **The derivative form reaches the same conclusion** as
`OkaTest.SimpleZeroStalk.isIso_stalkMap_hyperplane`, from a derivative of a polynomial instead of
a coefficient of a germ. The `ComplexAnalytic.IsCutOutBy` is the very same term: nothing here
converts between `ComplexAnalytic.coord` and `OkaRing.ofMvPolynomial`, because there is nothing to
convert. -/
theorem isIso_stalkMap_hyperplane_of_pderiv :
    IsIso ((((complexSpace (Fin (n + 1))).zeroLocusSubspaceι ![hyperplaneSection n]) ≫
      okaMapHom (projCoords n)).stalkMap (origin n)) :=
  isIso_stalkMap_comp_projCoords_of_pderiv
    ((complexSpace (Fin (n + 1))).isCutOutBy_zeroLocusSubspaceι ![hyperplaneSection n])
    (origin n) (fun h ↦ one_ne_zero ((eval_pderiv_hyperplanePoly n).symm.trans h))

/-- **The double zero is the polynomial one**, so the control below is about the section the two
controls above are about and not about a different one. `OkaRing.ofMvPolynomial` is a `ℂ`-algebra
map, so this is `map_pow`. -/
theorem hyperplaneSectionSq_eq :
    hyperplaneSectionSq n = OkaRing.ofMvPolynomial ⊤
      ((MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℂ) ^ 2) :=
  (map_pow (OkaRing.ofMvPolynomial ⊤) (MvPolynomial.X (Fin.last n)) 2).symm

/-- **The hypothesis is a restriction, in the derivative spelling**: `∂(z_n²)/∂z_n` is `2·z_n`,
which vanishes at the origin, so
`ComplexAnalytic.isIso_stalkMap_comp_projCoords_of_pderiv` does not apply to the section
`OkaTest.SimpleZeroStalk.hyperplaneSectionSq` names. -/
theorem eval_pderiv_hyperplanePolySq :
    MvPolynomial.eval (0 : Fin (n + 1) → ℂ) (MvPolynomial.pderiv (Fin.last n)
      ((MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℂ) ^ 2)) = 0 := by
  simp

/-- **The last partial derivative is `1` at the origin at the `ULift (Fin _)` indexing too**, read
at `ULift.up (Fin.last n)`, which is the index the space itself carries. -/
theorem eval_pderiv_uliftHyperplanePoly :
    MvPolynomial.eval (0 : ULift.{u} (Fin (n + 1)) → ℂ)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n))
        (MvPolynomial.X (ULift.up.{u} (Fin.last n)) :
          MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)) = 1 := by
  simp

/-- **The hypotheses of `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv` are
satisfiable**, at the indexing `ComplexAnalytic.AnalyticSpace` uses and so the one a standard
étale presentation — which is given by polynomials — will meet. -/
theorem isIso_stalkMap_uliftHyperplane_of_pderiv :
    IsIso ((((complexAffineSpace.{u} (n + 1)).zeroLocusSubspaceι
        ![uliftHyperplaneSection.{u} n]) ≫
      okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap (uliftOrigin.{u} n)) :=
  isIso_stalkMap_comp_uliftProj_of_pderiv
    ((complexAffineSpace.{u} (n + 1)).isCutOutBy_zeroLocusSubspaceι
      ![uliftHyperplaneSection.{u} n])
    (uliftOrigin.{u} n)
    (fun h ↦ one_ne_zero ((eval_pderiv_uliftHyperplanePoly.{u} n).symm.trans h))

end OkaTest.SimpleZeroStalk

end

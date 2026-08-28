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
satisfies.

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

/-! ### The `ULift (Fin _)`-indexed hyperplane

`ComplexAnalytic.complexAffineSpace` indexes its coordinates by `ULift (Fin n)`, and
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

/-- The last coordinate of `ComplexAnalytic.complexAffineSpace (n+1)`. -/
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

end OkaTest.SimpleZeroStalk

end

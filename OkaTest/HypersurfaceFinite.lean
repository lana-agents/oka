/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.MonicHypersurface

/-!
# Non-vacuity of finiteness over a presented base

`Oka/Analytification/HypersurfaceFinite.lean` proves that `A ⟶ A[X] ⧸ (F)` analytifies to a finite
morphism for every presentation of `A` and every `F` monic in the last variable. The statement is
universally quantified over the base presentation, so it holds vacuously for nobody — but two
things it is *for* are not visible in its type, and this file exhibits both at a base that is not
`ℂ^n`.

The witness is the square root of the coordinate over the parabola: base
`ℂ[x₀, x₁] ⧸ (x₁² - x₀)`, and `X² - x₀` adjoined to it.

* **The base has a relation.** `ComplexAnalytic.isFinite_analytificationMap_sqrtG` is the theorem
  at `k = 1`, which is the whole point of it —
  `ComplexAnalytic.isFinite_analytification_comp_proj` already covers `k = 0` and is the theorem
  `OkaTest/MonicHypersurface.lean` tests. It is also what makes the range hypothesis of
  `ComplexAnalytic.isFinite_comp_proj_of_range_subset` an inclusion rather than an equality: the
  image below is cut out by two equations and the hypersurface of `X² - x₀` by one.
* **The source is not empty and the morphism is not injective.**
  `ComplexAnalytic.range_base_analytificationIncl_sqrtG` computes the image in `ℂ³` as
  `{x₁² = x₀} ∩ {x₂² = x₀}`, and `ComplexAnalytic.mem_range_sqrtG` puts both `(1, 1, 1)` and
  `(1, 1, -1)` in it. Those two points agree in the coordinates the base reads, so the finiteness
  of the analytified structure map is not an instance of
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`.

## What is not checked here

* **Nothing about the map on points of the analytifications.** The two points above are exhibited
  in the *ambient* `ℂ³`, through `ComplexAnalytic.range_base_analytificationIncl`; that the
  structure map's own base map identifies them is the same statement one category down and would
  need the factorisation read at a point, which no statement in this repository does. That is the
  same gap `OkaTest/MonicHypersurface.lean`'s `## What is not checked here` records between the
  hand-built parabola and the analytification.
* **Nothing about the degree**, and nothing that says the source is the double cover rather than
  some space with the same image: comparing structure sheaves is
  `ComplexAnalytic.IsCutOutBy.uniqueIso`'s business and needs cut-out data this file does not
  produce.
* **Nothing standard étale.** `x₀` vanishes at the origin of the base, so this cover is branched
  there; it is a witness for finiteness and not for étaleness.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

/-! ### The parabola as a base, and a square root adjoined to it -/

/-- **The parabola `x₁² = x₀` in `ℂ²`, as a presentation with one relation.** -/
def parabolaBase : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  ![MvPolynomial.X (ULift.up 1) ^ 2 - MvPolynomial.X (ULift.up 0)]

/-- **`X² - x₀`, monic in the variable adjoined to the parabola.** -/
def sqrtG : Polynomial (MvPolynomial (ULift.{u} (Fin 2)) ℂ) :=
  Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X (ULift.up 0))

theorem monic_sqrtG : (sqrtG.{u}).Monic :=
  Polynomial.monic_X_pow_sub_C _ two_ne_zero

/-- **The adjoined variable is the last coordinate of `ℂ³` and the coefficient is the first**, so
the relation `ComplexAnalytic.sqrtG` contributes is `x₂² - x₀`. -/
theorem lastVarPolyEquiv_symm_sqrtG :
    (lastVarPolyEquiv.{u} 2).symm sqrtG.{u} =
      MvPolynomial.X (ULift.up 2) ^ 2 - MvPolynomial.X (ULift.up 0) := by
  rw [AlgEquiv.symm_apply_eq]
  have h0 : (ULift.up 0 : ULift.{u} (Fin 3)) = localisationIncl.{u} 2 (ULift.up 0) := rfl
  have h2 : (ULift.up 2 : ULift.{u} (Fin 3)) = localisationVar.{u} 2 := rfl
  rw [h0, h2]
  simp [sqrtG]

/-! ### The theorem at a base with a relation -/

/-- **The square root of the coordinate is finite over the parabola.**

`ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom` at `k = 1`: the target is the
analytification of `ℂ[x₀, x₁] ⧸ (x₁² - x₀)` and not an affine space. -/
theorem isFinite_analytificationMap_sqrtG :
    AnalyticSpace.IsFinite (analytificationMap.{u}
      (hypersurfacePresHom.{u} parabolaBase.{u} ((lastVarPolyEquiv.{u} 2).symm sqrtG.{u}))) :=
  isFinite_analytificationMap_hypersurfacePresHom.{u} parabolaBase.{u} sqrtG.{u} monic_sqrtG.{u}

/-! ### The source is not empty and the two sheets are distinct -/

/-- **The image of the source in `ℂ³` is `{x₁² = x₀} ∩ {x₂² = x₀}`** — two equations, where the
hypersurface of `ComplexAnalytic.sqrtG` alone is cut out by one. -/
theorem range_base_analytificationIncl_sqrtG :
    Set.range ⇑(analytificationIncl.{u} (hypersurfacePresentation.{u} parabolaBase.{u}
        ((lastVarPolyEquiv.{u} 2).symm sqrtG.{u}))).base =
      {z : complexAffineSpace.{u} 3 |
        (z : ULift.{u} (Fin 3) → ℂ) (ULift.up 1) ^ 2 = (z : ULift.{u} (Fin 3) → ℂ) (ULift.up 0) ∧
        (z : ULift.{u} (Fin 3) → ℂ) (ULift.up 2) ^ 2 =
          (z : ULift.{u} (Fin 3) → ℂ) (ULift.up 0)} := by
  rw [range_base_analytificationIncl]
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 := h (Fin.castSucc 0)
    have h1 := h (Fin.last 1)
    rw [hypersurfacePresentation, Fin.snoc_castSucc] at h0
    rw [hypersurfacePresentation, Fin.snoc_last, lastVarPolyEquiv_symm_sqrtG] at h1
    simp only [polyPresentation, parabolaBase, Matrix.cons_val_zero, MvPolynomial.eval_rename,
      map_sub, map_pow, MvPolynomial.eval_X, Function.comp_apply, sub_eq_zero] at h0
    simp only [map_sub, map_pow, MvPolynomial.eval_X, sub_eq_zero] at h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ j
    refine Fin.lastCases ?_ ?_ j
    · rw [hypersurfacePresentation, Fin.snoc_last, lastVarPolyEquiv_symm_sqrtG]
      simp only [map_sub, map_pow, MvPolynomial.eval_X, sub_eq_zero]
      exact h1
    · intro i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      rw [hypersurfacePresentation, Fin.snoc_castSucc]
      simp only [polyPresentation, parabolaBase, Matrix.cons_val_zero, MvPolynomial.eval_rename,
        map_sub, map_pow, MvPolynomial.eval_X, Function.comp_apply, sub_eq_zero]
      exact h0

/-- **Both sheets are there**: `(1, 1, 1)` and `(1, 1, -1)` are points of the image, and they
differ only in the coordinate the base does not read. -/
theorem mem_range_sqrtG (c : ℂ) (hc : c ^ 2 = 1) :
    ((fun j ↦ ![(1 : ℂ), 1, c] j.down) : complexAffineSpace.{u} 3) ∈
      Set.range ⇑(analytificationIncl.{u} (hypersurfacePresentation.{u} parabolaBase.{u}
        ((lastVarPolyEquiv.{u} 2).symm sqrtG.{u}))).base := by
  rw [range_base_analytificationIncl_sqrtG]
  exact ⟨by norm_num, by simpa using hc⟩

end ComplexAnalytic

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.HalfPlaneAut

/-!
# Elementary facts about `SL(2, ℝ)` acting on `ℍ`

For `g = [[a, b], [c, d]] ∈ SL(2, ℝ)` put `tr g = a + d` and `Q_g(z) = c z² + (d - a) z - b`, so
that `g • z = z` iff `Q_g(z) = 0`.

* `exists_smul_eq_self_of_trace_sq_lt`: if `(tr g)² < 4` then `g` fixes a point of `ℍ`.
* `displacement_lower_bound`: with `Δ = (tr g)² - 4`,
  `Δ |g z - z̄|² ≤ (Δ + 4) |g z - z|²`; for `Δ > 0` the pseudo-hyperbolic displacement
  `|g z - z| / |g z - z̄|` is bounded below by `√(Δ / (Δ + 4)) > 0`, uniformly in `z`.
* `conjFix`: conjugation by `[[η, -1], [1, 0]]` makes an element fixing the real point `η` upper
  triangular (its lower-left entry is `Q_g(η)`).
* `trace_commutator_sub_two`: for upper triangular `Y = [[y, s], [0, w]]`,
  `tr (X Y X⁻¹ Y⁻¹) - 2 = c_X (c_X s² + s (w - y)(d_X - a_X) - b_X (w - y)²)`.
-/

open Complex Set
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups

namespace Uniformization

/-- The trace of `g ∈ SL(2, ℝ)`. -/
def trSL (g : SL(2, ℝ)) : ℝ := g 0 0 + g 1 1

theorem det_SL (g : SL(2, ℝ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.2; rwa [Matrix.det_fin_two] at this

/-- The fixed-point polynomial `Q_g(z) = c z² + (d - a) z - b`. -/
def fixPoly (g : SL(2, ℝ)) (z : ℂ) : ℂ := (g 1 0 : ℂ) * z ^ 2 + (g 1 1 - g 0 0) * z - g 0 1

theorem smul_eq_self_iff (g : SL(2, ℝ)) (z : ℍ) : g • z = z ↔ fixPoly g z = 0 := by
  rw [UpperHalfPlane.ext_iff, coe_SL2R_smul, div_eq_iff (denom_SL2R_ne_zero g z.im_pos), fixPoly]
  constructor <;> intro h <;> linear_combination -h

theorem coe_smul_sub (g : SL(2, ℝ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) - z = -fixPoly g z / ((g 1 0 : ℂ) * z + g 1 1) := by
  have hd := denom_SL2R_ne_zero g z.im_pos
  rw [coe_SL2R_smul, eq_div_iff hd, fixPoly, sub_mul, div_mul_cancel₀ _ hd]
  ring

theorem exists_root_of_disc_neg (a b c d : ℝ) (hdet : a * d - b * c = 1)
    (h : (a + d) ^ 2 < 4) :
    ∃ z : ℂ, 0 < z.im ∧ (c : ℂ) * z ^ 2 + ((d : ℂ) - a) * z - b = 0 := by
  have hc : c ≠ 0 := by
    intro hc; rw [hc] at hdet; nlinarith [sq_nonneg (a - d)]
  set D := 4 - (a + d) ^ 2
  have hD : 0 < D := by simp only [D]; linarith
  set x := (a - d) / (2 * c)
  set y := Real.sqrt D / (2 * |c|)
  have hcpos : 0 < 2 * |c| := mul_pos two_pos (abs_pos.mpr hc)
  have hy : 0 < y := div_pos (Real.sqrt_pos.mpr hD) hcpos
  have hy2 : y ^ 2 = D / (4 * c ^ 2) := by
    simp only [y, div_pow, Real.sq_sqrt hD.le, mul_pow, sq_abs]; ring
  refine ⟨x + y * I, by simpa using hy, ?_⟩
  have hb : b = (a * d - 1) / c := by field_simp; linarith
  apply Complex.ext
  · simp only [sq, add_re, mul_re, ofReal_re, ofReal_im, add_im, mul_im, I_re, I_im, sub_re,
      zero_re, mul_zero, mul_one, sub_zero, add_zero, zero_add, sub_im, zero_mul]
    have : y * y = D / (4 * c ^ 2) := by rw [← sq, hy2]
    rw [show c * (x * x - y * y) + (d - a) * x - b = c * (x * x) - c * (y * y) + (d - a) * x - b by
      ring, this]
    simp only [x, D, hb]
    field_simp
    ring
  · simp only [sq, add_re, mul_re, ofReal_re, ofReal_im, add_im, mul_im, I_re, I_im, sub_im,
      zero_im, mul_zero, mul_one, sub_zero, add_zero, zero_add, sub_re, zero_mul]
    simp only [x]
    field_simp
    ring

/-- If `(tr g)² < 4`, then `g` fixes a point of `ℍ`. -/
theorem exists_smul_eq_self_of_trace_sq_lt (g : SL(2, ℝ)) (h : trSL g ^ 2 < 4) :
    ∃ z : ℍ, g • z = z := by
  obtain ⟨z, hz, hQ⟩ := exists_root_of_disc_neg (g 0 0) (g 0 1) (g 1 0) (g 1 1) (det_SL g) h
  exact ⟨⟨z, hz⟩, (smul_eq_self_iff g _).mpr hQ⟩

/-- The quantity `|Q_g(z)|²` dominates `((tr g)² - 4) (Im z)²`. -/
theorem fixPoly_norm_sq_ge (g : SL(2, ℝ)) (z : ℂ) :
    (trSL g ^ 2 - 4) * z.im ^ 2 ≤ normSq (fixPoly g z) := by
  set a := g 0 0; set b := g 0 1; set c := g 1 0; set d := g 1 1
  have hdet : a * d - b * c = 1 := det_SL g
  have hQ : normSq (fixPoly g z) = (c * (z.re ^ 2 - z.im ^ 2) + (d - a) * z.re - b) ^ 2 +
      (2 * c * z.re * z.im + (d - a) * z.im) ^ 2 := by
    simp only [fixPoly, normSq_apply, sq, add_re, sub_re, mul_re, ofReal_re, ofReal_im,
      add_im, sub_im, mul_im]
    ring
  rw [hQ]
  simp only [trSL]
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc] at hdet ⊢
    nlinarith [sq_nonneg ((d - a) * z.re - b), sq_nonneg z.im]
  · -- `16 c² (|Q|² - Δ y²) = (|W|² - Δ)²` with `W = 2 c z + d - a`
    have hb : b = (a * d - 1) / c := by field_simp; linarith
    have key : 16 * c ^ 2 * ((c * (z.re ^ 2 - z.im ^ 2) + (d - a) * z.re - b) ^ 2 +
        (2 * c * z.re * z.im + (d - a) * z.im) ^ 2 - ((a + d) ^ 2 - 4) * z.im ^ 2) =
        ((2 * c * z.re + d - a) ^ 2 + 4 * c ^ 2 * z.im ^ 2 - ((a + d) ^ 2 - 4)) ^ 2 := by
      rw [hb]; field_simp; ring
    have hc2 : 0 < 16 * c ^ 2 := by positivity
    nlinarith [sq_nonneg ((2 * c * z.re + d - a) ^ 2 + 4 * c ^ 2 * z.im ^ 2 - ((a + d) ^ 2 - 4))]

/-- **Displacement lower bound.** -/
theorem displacement_lower_bound (g : SL(2, ℝ)) (z : ℍ) :
    (trSL g ^ 2 - 4) * normSq ((g • z : ℍ) - (starRingEnd ℂ) (z : ℂ)) ≤
      trSL g ^ 2 * normSq ((g • z : ℍ) - (z : ℂ)) := by
  set w : ℂ := (g 1 0 : ℂ) * z + g 1 1
  have hw : w ≠ 0 := denom_SL2R_ne_zero g z.im_pos
  have hw2 : 0 < normSq w := normSq_pos.mpr hw
  have h1 : ((g • z : ℍ) : ℂ) - z = -fixPoly g z / w := coe_smul_sub g z
  -- `|g z - z̄|² = |g z - z|² + 4 Im(g z) Im z`
  have h2 : normSq ((g • z : ℍ) - (starRingEnd ℂ) (z : ℂ)) =
      normSq ((g • z : ℍ) - (z : ℂ)) + 4 * (g • z).im * z.im := by
    simp only [normSq_apply, sub_re, sub_im, conj_re, conj_im, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_re]
    ring
  have h3 : (g • z).im = z.im / normSq w := by
    have e : g • z = (Matrix.SpecialLinearGroup.toGL g) • z := rfl
    rw [e, UpperHalfPlane.im_smul_eq_div_normSq]
    simp [w, UpperHalfPlane.denom]
  rw [h2, h3, h1, normSq_div, normSq_neg]
  have hQ := fixPoly_norm_sq_ge g z
  simp only [UpperHalfPlane.coe_im] at hQ
  have e : (trSL g ^ 2 - 4) * (normSq (fixPoly g z) / normSq w + 4 * (z.im / normSq w) * z.im) =
      ((trSL g ^ 2 - 4) * (normSq (fixPoly g z) + 4 * z.im ^ 2)) / normSq w := by
    field_simp
  have e2 : trSL g ^ 2 * (normSq (fixPoly g z) / normSq w) =
      (trSL g ^ 2 * normSq (fixPoly g z)) / normSq w := by ring
  rw [e, e2]
  exact div_le_div_of_nonneg_right (by nlinarith) hw2.le

/-! ### Conjugating a fixed point to `∞` -/

/-- The matrix `[[η, -1], [1, 0]]`, mapping `∞` to `η`. -/
def conjFix (η : ℝ) : SL(2, ℝ) :=
  ⟨!![η, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- The lower-left entry of `conjFix η⁻¹ * g * conjFix η` is `Q_g(η)`. -/
theorem conjFix_lowerLeft (η : ℝ) (g : SL(2, ℝ)) :
    ((conjFix η)⁻¹ * g * conjFix η) 1 0 =
      g 1 0 * η ^ 2 + (g 1 1 - g 0 0) * η - g 0 1 := by
  simp [conjFix, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

/-- **The commutator trace for upper triangular `Y`.** -/
theorem trace_commutator_sub_two (X Y : SL(2, ℝ)) (hY : Y 1 0 = 0) :
    trSL (X * Y * X⁻¹ * Y⁻¹) - 2 = X 1 0 * (X 1 0 * Y 0 1 ^ 2 +
      Y 0 1 * (Y 1 1 - Y 0 0) * (X 1 1 - X 0 0) - X 0 1 * (Y 1 1 - Y 0 0) ^ 2) := by
  have hX := det_SL X
  have hYd := det_SL Y
  rw [hY] at hYd
  simp only [trSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hY]
  simp
  linear_combination (2 * Y 0 0 * Y 1 1) * hX + 2 * hYd

end Uniformization

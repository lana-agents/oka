/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Oka.Uniformization.Peripheral

/-!
# The commutator of the edge pairings is parabolic with trace `-2`

With `C = A⁻¹ B⁻¹ A B` the monodromy around a lattice point (`Oka/Uniformization/Peripheral.lean`):

* **`C` is not hyperbolic** (`trace_sq_le`): the lift `Σ` of `exp` is holomorphic on the
  half-plane `Re s < log r₀`, so by the Schwarz lemma the pseudo-hyperbolic distance between
  `Σ x` and `Σ (x + 2π i) = C • Σ x` is at most `2π / (log r₀ - x)`, which tends to `0` as
  `x → -∞`; for a hyperbolic `C` it is bounded below (`displacement_lower_bound`).
* **`C` acts nontrivially** (`not_forall_smul_eq_self`): otherwise `Σ` is `2π i`-periodic and
  `cayley ∘ Σ ∘ log` is a bounded holomorphic function on the punctured disc, which extends over
  `0` with a value inside the disc (open mapping); then `Σ (log p)` converges in `ℍ` as `p → 0`,
  and `ψ (Σ (log p)) = p → 0` forces `0 ∉ Λ`, a contradiction.
* **`C` is not elliptic**, since deck transformations with a fixed point act trivially.

So `(tr C)² = 4`. Finally **`tr C ≠ 2`** (`trace_ne_two`): if `tr C = 2` then `A` and `B` have a
common fixed point on `∂ℍ` (`trace_commutator_sub_two`); after conjugating it to `∞`, `C` is a
translation `z ↦ z + τ`, `τ ≠ 0`, and conjugating `C` by powers of `A^{±1}` or `B^{±1}` gives deck
transformations `z ↦ z + x^{2n} τ` with `|x| < 1` which accumulate at a point of `ℍ`, contradicting
local injectivity of `ψ`; if the diagonal entries of both `A` and `B` are `±1` they commute and
`C = 1`.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace Uniformization

namespace Peripheral

open Generators

variable {t : ℍ} (U : Unif (Lt t))

/-- The pseudo-hyperbolic distance quotient `(u - z) / (u - z̄)`. -/
noncomputable def phq (z u : ℂ) : ℂ := (u - z) / (u - (starRingEnd ℂ) z)

theorem sub_conj_ne_zero {z u : ℂ} (hz : 0 < z.im) (hu : 0 < u.im) :
    u - (starRingEnd ℂ) z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this; linarith

theorem norm_phq_lt_one {z u : ℂ} (hz : 0 < z.im) (hu : 0 < u.im) : ‖phq z u‖ < 1 := by
  rw [phq, norm_div, div_lt_one (norm_pos_iff.mpr (sub_conj_ne_zero hz hu))]
  have : ‖u - z‖ ^ 2 < ‖u - (starRingEnd ℂ) z‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

/-- **`C` is not hyperbolic.** -/
theorem trace_sq_le : trSL (Cm U) ^ 2 ≤ 4 := by
  by_contra hcon
  push Not at hcon
  set Δ := trSL (Cm U) ^ 2 - 4 with hΔ
  have hΔ0 : 0 < Δ := by linarith
  set R : ℝ := 2 * π * (Δ + 4) / Δ + 2 * π + 1 with hR
  have hR0 : 0 < R := by positivity
  set x : ℝ := Real.log (r₀ t) - R
  set s : ℂ := (x : ℂ)
  have hs : s ∈ Hr t := by simp [Hr, s, x]; linarith
  set z₀ : ℂ := (Sig U s : ℂ)
  have hz₀ : 0 < z₀.im := (Sig U s).im_pos
  set f : ℂ → ℂ := fun w ↦ phq z₀ (Sig U (s + w))
  have hball : ∀ w ∈ ball (0 : ℂ) R, s + w ∈ Hr t := fun w hw ↦ by
    rw [mem_ball_zero_iff] at hw
    have : |w.re| < R := (abs_re_le_norm w).trans_lt hw
    simp only [Hr, mem_setOf_eq, add_re, s, ofReal_re, x]
    linarith [(abs_lt.mp this).2]
  have hfd : DifferentiableOn ℂ f (ball 0 R) := by
    have hS : DifferentiableOn ℂ (fun w ↦ (Sig U (s + w) : ℂ)) (ball 0 R) :=
      (differentiableOn_Sig U).comp ((differentiableOn_const _).add differentiableOn_id) hball
    exact (hS.sub_const _).div (hS.sub_const _) fun w _ ↦ sub_conj_ne_zero hz₀ (Sig U _).im_pos
  have hf0 : f 0 = 0 := by
    change phq z₀ (Sig U (s + 0)) = 0
    rw [add_zero]; simp [phq, z₀]
  have hmaps : MapsTo f (ball 0 R) (ball (f 0) 1) := fun w _ ↦ by
    rw [hf0, mem_ball_zero_iff]; exact norm_phq_lt_one hz₀ (Sig U _).im_pos
  have h2π : (2 * π * I : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    simp [abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos,
      div_pos (mul_pos (mul_pos two_pos Real.pi_pos) (by linarith : (0:ℝ) < Δ + 4)) hΔ0]
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hfd
    (hmaps.mono_right ball_subset_closedBall) h2π
  rw [hf0, dist_zero_right, dist_zero_right] at hschwarz
  have hnorm2π : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [hnorm2π] at hschwarz
  -- the displacement lower bound
  have hC : Sig U (s + 2 * π * I) = Cm U • Sig U s := Sig_add_two_pi U hs
  have hdisp := displacement_lower_bound (Cm U) (Sig U s)
  have hf2π : f (2 * π * I) = phq z₀ ((Cm U • Sig U s : ℍ) : ℂ) := by simp only [f, hC]
  rw [hf2π, phq, norm_div] at hschwarz
  set N := ‖((Cm U • Sig U s : ℍ) : ℂ) - z₀‖
  set N' := ‖((Cm U • Sig U s : ℍ) : ℂ) - (starRingEnd ℂ) z₀‖
  have hN' : 0 < N' := norm_pos_iff.mpr (sub_conj_ne_zero hz₀ (Cm U • Sig U s).im_pos)
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hdisp
  have h1 : N / N' ≤ 2 * π / R := by
    have := hschwarz; rwa [div_mul_eq_mul_div, one_mul] at this
  have h2 : 2 * π / R < Δ / (Δ + 4) := by
    rw [div_lt_div_iff₀ hR0 (by linarith)]
    have : 2 * π * (Δ + 4) < Δ * R := by
      rw [hR]
      field_simp
      nlinarith [Real.pi_pos]
    linarith
  have h3 : N ≤ 2 * π / R * N' := by rwa [div_le_iff₀ hN'] at h1
  have hlt1 : 2 * π / R < 1 := h2.trans (by rw [div_lt_one (by linarith)]; linarith)
  have h4 : N ^ 2 ≤ (2 * π / R) ^ 2 * N' ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rwa [mul_pow] at this
  have h5 : (2 * π / R) ^ 2 < Δ / (Δ + 4) := by
    have hpos : 0 ≤ 2 * π / R := by positivity
    nlinarith
  -- `Δ N'² ≤ (Δ + 4) N²`
  have h6 : Δ * N' ^ 2 ≤ (Δ + 4) * N ^ 2 := by
    have : trSL (Cm U) ^ 2 = Δ + 4 := by rw [hΔ]; ring
    rw [this, add_sub_cancel_right] at hdisp; exact hdisp
  have h7 : Δ * N' ^ 2 < Δ * N' ^ 2 := by
    calc Δ * N' ^ 2 ≤ (Δ + 4) * N ^ 2 := h6
      _ ≤ (Δ + 4) * ((2 * π / R) ^ 2 * N' ^ 2) := by gcongr
      _ < (Δ + 4) * (Δ / (Δ + 4) * N' ^ 2) := by gcongr
      _ = Δ * N' ^ 2 := by field_simp
  exact lt_irrefl _ h7

end Peripheral

end Uniformization

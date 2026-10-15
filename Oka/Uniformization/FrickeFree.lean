/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Once-punctured torus groups are free (Fricke normal form and ping-pong)

Let `A, B ∈ SL(2, ℝ)` with `tr [A, B] = -2` and `tr A ≠ 0`, as for the deck group of a
uniformisation of a once-punctured elliptic curve (`Uniformization.exists_isUniformization`).
Then no nontrivial word in `A, B` equals `±1` (`Uniformization.Fricke.eq_one_of_lift_eq_pm_one`):
the image of `⟨A, B⟩` in `PSL(2, ℝ)` is free on the images of `A` and `B`.

Proof:
* **Fricke's identity** `tr [A, B] = x² + y² + z² - xyz - 2` (`x = tr A`, `y = tr B`,
  `z = tr AB`), so `x² + y² + z² = xyz`; hence `x, y, z ≠ 0` and `x² > 4`;
* **signs**: replacing `A`, `B` by `±A`, `±B` makes `x, y, z > 0` (`exists_sign_normalize`);
* **Fricke rigidity** (`exists_conj_of_tr_eq`): a pair with `x² > 4` and `tr [A, B] ≠ 2` is
  determined up to simultaneous `GL(2, ℝ)`-conjugacy by `(x, y, z)`; so the pair is conjugate to
  the explicit **Fricke normal form** `(nA, nB)`;
* **ping-pong** for the normal form (`pp_disjoint`): every nontrivial reduced word moves the open
  ideal quadrilateral `Q°` with vertices `-y/(xz), 0, x/(yz), ∞` off itself.

This file is a port of `OrbicurveCores.Fricke`, `OrbicurveCores.FrickeRigidity`,
`OrbicurveCores.exists_sign_normalize`, `OrbicurveCores.four_lt_sq_of_fricke`, the normal form
`OrbicurveCores.Fuchsian.nA`, `nB` and `OrbicurveCores/Fuchsian/PingPong.lean` from the
lana-agents repository `orbicurve-cores` (which depends on `oka` and so cannot be imported here),
restricted to what the freeness statement needs. The Nielsen descent of `orbicurve-cores` is not
needed: ping-pong only uses `x, y, z > 0`.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set Filter Topology
open scoped MatrixGroups Pointwise

namespace Uniformization.Fricke

/-! ### Trace identities -/

section Trace

variable {R : Type*} [CommRing R]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) R

/-- The trace of an element of `SL(2, R)`. -/
abbrev tr (A : SL2) : R := trace (A : Matrix (Fin 2) (Fin 2) R)

lemma det_eq (A : SL2) : (A : Matrix (Fin 2) (Fin 2) R) 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have := A.det_coe
  rw [Matrix.det_fin_two] at this
  exact this

lemma tr_def (A : SL2) : tr A = A 0 0 + A 1 1 := by
  simp [tr, trace_fin_two]

@[simp]
lemma tr_one : tr (1 : SL2) = 2 := by
  simp [tr_def]
  norm_num

lemma tr_inv (A : SL2) : tr A⁻¹ = tr A := by
  simp [tr_def, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  ring

lemma tr_mul_comm (A B : SL2) : tr (A * B) = tr (B * A) := by
  simp only [tr, Matrix.SpecialLinearGroup.coe_mul]
  exact trace_mul_comm _ _

lemma tr_inv_mul (A B : SL2) : tr (A⁻¹ * B) = tr A * tr B - tr (A * B) := by
  simp [tr_def, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, mul_apply,
    Fin.sum_univ_two]
  ring

lemma tr_mul_inv (A B : SL2) : tr (A * B⁻¹) = tr A * tr B - tr (A * B) := by
  simp [tr_def, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, mul_apply,
    Fin.sum_univ_two]
  ring

lemma tr_mul_mul_self (A B : SL2) : tr (A * (A * B)) = tr A * tr (A * B) - tr B := by
  have hA := det_eq A
  simp [tr_def, mul_apply, Fin.sum_univ_two]
  linear_combination (-(B 0 0) - B 1 1) * hA

/-- **Fricke's trace identity** for the commutator. -/
lemma tr_commutator (A B : SL2) :
    tr (A * B * A⁻¹ * B⁻¹) =
      tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 - tr A * tr B * tr (A * B) - 2 := by
  have hA := det_eq A
  have hB := det_eq B
  simp [tr_def, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, mul_apply,
    Fin.sum_univ_two]
  linear_combination ((B 0 0 + B 1 1) ^ 2 - 2 * (B 0 0 * B 1 1 - B 0 1 * B 1 0)) * hA
    + ((A 0 0 + A 1 1) ^ 2 - 2) * hB

/-- The commutator of a once-punctured torus group has trace `-2` iff `x² + y² + z² = xyz`. -/
lemma tr_commutator_eq_neg_two_iff (A B : SL2) :
    tr (A * B * A⁻¹ * B⁻¹) = -2 ↔
      tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 = tr A * tr B * tr (A * B) := by
  rw [tr_commutator]
  constructor <;> intro h <;> linear_combination h

end Trace

/-- On the Fricke surface `x² + y² + z² = xyz`, a nonzero coordinate has square `> 4`. -/
lemma four_lt_sq_of_fricke {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) (hx : x ≠ 0) :
    4 < x ^ 2 := by
  by_contra hle
  push Not at hle
  have hax : |x| ≤ 2 := by
    rw [← Real.sqrt_sq_eq_abs]; calc Real.sqrt (x ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hle
      _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h1 : x * y * z ≤ |x| * |y| * |z| := by
    rw [← abs_mul, ← abs_mul]; exact le_abs_self _
  have h2 : |x| * |y| * |z| ≤ 2 * (|y| * |z|) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hax (by positivity)
  have h3 : 2 * (|y| * |z|) ≤ y ^ 2 + z ^ 2 := by
    nlinarith [sq_nonneg (|y| - |z|), sq_abs y, sq_abs z]
  have : x ^ 2 ≤ 0 := by linarith
  exact hx (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg x)))

/-! ### Signs -/

lemma tr_neg (A : SL(2, ℝ)) : tr (-A) = -tr A := by
  simp [tr, Matrix.SpecialLinearGroup.coe_neg, trace_neg]

/-- Changing the signs of `A` and `B` so that the trace triple becomes `(|x|, |y|, |z|)`; this is
possible when `xyz > 0`. -/
lemma exists_sign_normalize {A B : SL(2, ℝ)} (hpos : 0 < tr A * tr B * tr (A * B)) :
    ∃ A' ∈ ({A, -A} : Set SL(2, ℝ)), ∃ B' ∈ ({B, -B} : Set SL(2, ℝ)),
      tr A' = |tr A| ∧ tr B' = |tr B| ∧ tr (A' * B') = |tr (A * B)| ∧
      tr (A' * B' * A'⁻¹ * B'⁻¹) = tr (A * B * A⁻¹ * B⁻¹) := by
  have hx : tr A ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  have hy : tr B ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  have hz : tr (A * B) ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · have hz' : 0 < tr (A * B) := by
      by_contra h; push Not at h; nlinarith [mul_pos_of_neg_of_neg hx hy]
    refine ⟨-A, by simp, -B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [tr_neg, abs_of_neg hx]
    · rw [tr_neg, abs_of_neg hy]
    · rw [neg_mul_neg, abs_of_pos hz']
    · rw [tr_commutator, tr_commutator, tr_neg, tr_neg, neg_mul_neg]; ring
  · have hz' : tr (A * B) < 0 := by
      by_contra h; push Not at h
      have : tr A * tr B < 0 := mul_neg_of_neg_of_pos hx hy
      nlinarith
    refine ⟨-A, by simp, B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [tr_neg, abs_of_neg hx]
    · rw [abs_of_pos hy]
    · rw [neg_mul, tr_neg, abs_of_neg hz']
    · rw [tr_commutator, tr_commutator, tr_neg, neg_mul, tr_neg]; ring
  · have hz' : tr (A * B) < 0 := by
      by_contra h; push Not at h
      have : tr A * tr B < 0 := mul_neg_of_pos_of_neg hx hy
      nlinarith
    refine ⟨A, by simp, -B, by simp, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_pos hx]
    · rw [tr_neg, abs_of_neg hy]
    · rw [mul_neg, tr_neg, abs_of_neg hz']
    · rw [tr_commutator, tr_commutator, tr_neg, mul_neg, tr_neg]; ring
  · have hz' : 0 < tr (A * B) := by
      by_contra h; push Not at h; nlinarith [mul_pos hx hy]
    exact ⟨A, by simp, B, by simp, (abs_of_pos hx).symm, (abs_of_pos hy).symm,
      (abs_of_pos hz').symm, rfl⟩

/-! ### Fricke rigidity -/

/-- The larger eigenvalue `(x + √(x² - 4))/2` of an element of trace `x`. -/
noncomputable def eigBig (x : ℝ) : ℝ := (x + Real.sqrt (x ^ 2 - 4)) / 2

/-- The smaller eigenvalue `(x - √(x² - 4))/2` of an element of trace `x`. -/
noncomputable def eigSmall (x : ℝ) : ℝ := (x - Real.sqrt (x ^ 2 - 4)) / 2

section eig

variable {x : ℝ} (hx : 4 < x ^ 2)
include hx

omit hx in
lemma eig_sum : eigBig x + eigSmall x = x := by unfold eigBig eigSmall; ring

lemma eig_prod : eigBig x * eigSmall x = 1 := by
  unfold eigBig eigSmall
  have := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 4 by linarith)
  linear_combination (-1 / 4 : ℝ) * this

lemma eig_sub_pos : 0 < eigBig x - eigSmall x := by
  unfold eigBig eigSmall
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < x ^ 2 - 4 by linarith)
  linarith

lemma eig_ne : eigBig x ≠ eigSmall x := sub_ne_zero.mp (eig_sub_pos hx).ne'

end eig

/-- Diagonalisation, in coordinates: for `A = [[p, q], [r, s]]` with `ps - qr = 1` and roots
`l ≠ m` of `t² - (p + s) t + 1`, an explicit invertible `P` with `P A = diag(l, m) P`. -/
lemma exists_diagonalize_aux (p q r s l m : ℝ) (hd : p * s - q * r = 1)
    (hsum : l + m = p + s) (hprod : l * m = 1) (hne : l - m ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
      P * !![p, q; r, s] = !![l, 0; 0, m] * P := by
  have hl : l ^ 2 - (p + s) * l + 1 = 0 := by rw [← hsum]; linear_combination -hprod
  have hm : m ^ 2 - (p + s) * m + 1 = 0 := by rw [← hsum]; linear_combination -hprod
  by_cases hr : r = 0
  · subst hr
    have hp : (p - l) * (p - m) = 0 := by linear_combination -p * hsum - hd + hprod
    rcases mul_eq_zero.mp hp with hpl | hpm
    · have hpl' : p = l := by linarith
      have hsm : s = m := by linarith
      subst hpl' hsm
      refine ⟨!![p - s, q; 0, s - p], ?_, ?_⟩
      · rw [det_fin_two_of]
        have := mul_self_ne_zero.mpr hne
        intro h; apply this; linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> ring
    · have hpm' : p = m := by linarith
      have hsl : s = l := by linarith
      subst hpm' hsl
      refine ⟨!![0, s - p; p - s, q], ?_, ?_⟩
      · rw [det_fin_two_of]
        have := mul_self_ne_zero.mpr hne
        intro h; apply this; linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> ring
  · refine ⟨!![r, l - p; r, m - p], ?_, ?_⟩
    · rw [det_fin_two_of]
      have : r * (m - p) - (l - p) * r = -(r * (l - m)) := by ring
      rw [this, neg_ne_zero]
      exact mul_ne_zero hr hne
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
      · ring
      · linear_combination -hl - hd
      · ring
      · linear_combination -hm - hd

/-- **Diagonalisation of a hyperbolic element.** If `det A = 1` and `(tr A)² > 4`, there is an
invertible `P` with `P A = diag(λ, μ) P`, where `λ, μ` are the two eigenvalues. -/
lemma exists_diagonalize {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 1)
    (hx : 4 < A.trace ^ 2) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
      P * A = !![eigBig A.trace, 0; 0, eigSmall A.trace] * P := by
  have hA := eta_fin_two A
  rw [det_fin_two] at hdet
  have hsum : eigBig A.trace + eigSmall A.trace = A 0 0 + A 1 1 := by
    rw [eig_sum, trace_fin_two]
  obtain ⟨P, hP, hPA⟩ := exists_diagonalize_aux (A 0 0) (A 0 1) (A 1 0) (A 1 1) _ _ hdet hsum
    (eig_prod hx) (eig_sub_pos hx).ne'
  exact ⟨P, hP, by rw [hA]; exact hPA⟩

/-- The normal form of the second matrix: `[[a, 1], [ad - 1, d]]` with
`a = (z - μy)/(λ - μ)`, `d = (λy - z)/(λ - μ)`. -/
noncomputable def normalB (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := (z - eigSmall x * y) / (eigBig x - eigSmall x)
  let d := (eigBig x * y - z) / (eigBig x - eigSmall x)
  !![a, 1; a * d - 1, d]

/-- The Fricke polynomial in normal form: for `D = diag(l, m)` with `lm = 1` and
`C = [[a, b], [c, d]]` with `det C = 1`, `x² + y² + z² - xyz - 4 = -bc (l - m)²` where
`x = l + m`, `y = a + d`, `z = la + md`. -/
lemma fricke_normal {l m a b c d : ℝ} (hprod : l * m = 1) (hdet : a * d - b * c = 1) :
    (l + m) ^ 2 + (a + d) ^ 2 + (l * a + m * d) ^ 2 - (l + m) * (a + d) * (l * a + m * d) - 4 =
      -(b * c) * (l - m) ^ 2 := by
  linear_combination (4 - (a + d) ^ 2) * hprod - (l - m) ^ 2 * hdet

/-- **Normal form of an irreducible pair with hyperbolic first element.** -/
theorem exists_conj_normal {A B : SL(2, ℝ)} (hx : 4 < tr A ^ 2)
    (hc : tr (A * B * A⁻¹ * B⁻¹) ≠ 2) :
    ∃ g : GL (Fin 2) ℝ,
      ((g * toGL A * g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![eigBig (tr A), 0; 0, eigSmall (tr A)] ∧
      ((g * toGL B * g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        normalB (tr A) (tr B) (tr (A * B)) := by
  set x := tr A with hxdef
  set l := eigBig x
  set m := eigSmall x
  have hprod : l * m = 1 := eig_prod hx
  have hlm : l - m ≠ 0 := (eig_sub_pos hx).ne'
  set D : Matrix (Fin 2) (Fin 2) ℝ := !![l, 0; 0, m] with hD
  obtain ⟨P, hP, hPA⟩ := exists_diagonalize (A := (A : Matrix (Fin 2) (Fin 2) ℝ)) A.det_coe hx
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hPPi : P * P⁻¹ = 1 := mul_nonsing_inv P hPu
  have hPiP : P⁻¹ * P = 1 := nonsing_inv_mul P hPu
  set C : Matrix (Fin 2) (Fin 2) ℝ := P * (B : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ with hC
  have hDA : P * (A : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ = D := by
    rw [hPA, mul_assoc, hPPi, mul_one]
  -- invariants of `C`
  have htrC : C.trace = tr B := by
    rw [hC, trace_mul_cycle, hPiP, one_mul]
  have htrDC : (D * C).trace = tr (A * B) := by
    rw [← hDA, hC, show P * (A : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ * (P * B * P⁻¹) =
      P * ((A : Matrix (Fin 2) (Fin 2) ℝ) * B) * P⁻¹ by
        simp only [mul_assoc]; rw [← mul_assoc P⁻¹ P, hPiP, one_mul],
      trace_mul_cycle, hPiP, one_mul]
    simp [tr]
  have hdetC : C.det = 1 := by
    rw [hC, det_mul, det_mul, B.det_coe, mul_one, ← det_mul, hPPi, det_one]
  set a := C 0 0
  set b := C 0 1
  set c := C 1 0
  set d := C 1 1
  have hCeta : C = !![a, b; c, d] := eta_fin_two C
  have hdet' : a * d - b * c = 1 := by rw [hCeta, det_fin_two_of] at hdetC; exact hdetC
  have hy : a + d = tr B := by rw [← htrC, hCeta, trace_fin_two_of]
  have hz : l * a + m * d = tr (A * B) := by
    rw [← htrDC, hCeta, hD]; simp [trace_fin_two]
  have hxlm : l + m = x := eig_sum
  -- `bc ≠ 0` by irreducibility
  have hbc : b * c ≠ 0 := by
    intro h0
    apply hc
    have hf := fricke_normal (b := b) (c := c) hprod hdet'
    rw [h0, hxlm, hy, hz] at hf
    rw [tr_commutator]
    linarith
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc
  -- rescale by `diag(b⁻¹, 1)`
  set Q : Matrix (Fin 2) (Fin 2) ℝ := !![b⁻¹, 0; 0, 1] with hQ
  have hQdet : Q.det ≠ 0 := by rw [hQ, det_fin_two_of]; simpa using hb
  set Qi : Matrix (Fin 2) (Fin 2) ℝ := !![b, 0; 0, 1] with hQi
  have hQQi : Q * Qi = 1 := by
    rw [hQ, hQi]; ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hb]
  have hQiQ : Qi * Q = 1 := by
    rw [hQ, hQi]; ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hb]
  have hQinv : Q⁻¹ = Qi := inv_eq_right_inv hQQi
  let g : GL (Fin 2) ℝ := GeneralLinearGroup.mkOfDetNeZero (Q * P)
    (by rw [det_mul]; exact mul_ne_zero hQdet hP)
  have hgc : (g : Matrix (Fin 2) (Fin 2) ℝ) = Q * P := rfl
  have hginv : ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = P⁻¹ * Qi := by
    rw [Matrix.coe_units_inv, hgc, Matrix.mul_inv_rev, hQinv]
  -- solve for `a`, `d`
  have ha : a = (tr (A * B) - m * tr B) / (l - m) := by
    rw [eq_div_iff hlm, ← hy, ← hz]; ring
  have hd' : d = (l * tr B - tr (A * B)) / (l - m) := by
    rw [eq_div_iff hlm, ← hy, ← hz]; ring
  refine ⟨g, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hgc, hginv, coe_GL_coe_matrix]
    rw [show Q * P * (A : Matrix (Fin 2) (Fin 2) ℝ) * (P⁻¹ * Qi) =
      Q * (P * A * P⁻¹) * Qi by simp only [mul_assoc], hDA, hQ, hQi, hD]
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply]
    field_simp
  · rw [Units.val_mul, Units.val_mul, hgc, hginv, coe_GL_coe_matrix]
    rw [show Q * P * (B : Matrix (Fin 2) (Fin 2) ℝ) * (P⁻¹ * Qi) =
      Q * C * Qi by simp only [hC, mul_assoc], hCeta, hQ, hQi, normalB]
    rw [← ha, ← hd']
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hb]
    · field_simp
    · linear_combination -hdet'

/-- **Fricke rigidity.** Two pairs in `SL(2, ℝ)` with the same trace triple, whose first element
is hyperbolic and which are irreducible (`tr [A, B] ≠ 2`), are simultaneously conjugate by an
element of `GL(2, ℝ)`. -/
theorem exists_conj_of_tr_eq {A B A' B' : SL(2, ℝ)} (hx : 4 < tr A ^ 2)
    (hc : tr (A * B * A⁻¹ * B⁻¹) ≠ 2) (h1 : tr A = tr A') (h2 : tr B = tr B')
    (h3 : tr (A * B) = tr (A' * B')) :
    ∃ g : GL (Fin 2) ℝ, g * toGL A * g⁻¹ = toGL A' ∧ g * toGL B * g⁻¹ = toGL B' := by
  have hx' : 4 < tr A' ^ 2 := h1 ▸ hx
  have hc' : tr (A' * B' * A'⁻¹ * B'⁻¹) ≠ 2 := by
    rwa [tr_commutator, ← h1, ← h2, ← h3, ← tr_commutator]
  obtain ⟨g, hgA, hgB⟩ := exists_conj_normal hx hc
  obtain ⟨g', hgA', hgB'⟩ := exists_conj_normal hx' hc'
  refine ⟨g'⁻¹ * g, ?_, ?_⟩
  · have e : g * toGL A * g⁻¹ = g' * toGL A' * g'⁻¹ := by
      ext1; rw [hgA, hgA', h1]
    calc g'⁻¹ * g * toGL A * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * toGL A * g⁻¹) * g' := by group
      _ = toGL A' := by rw [e]; group
  · have e : g * toGL B * g⁻¹ = g' * toGL B' * g'⁻¹ := by
      ext1; rw [hgB, hgB', h1, h2, h3]
    calc g'⁻¹ * g * toGL B * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * toGL B * g⁻¹) * g' := by group
      _ = toGL B' := by rw [e]; group

/-! ### The Fricke normal form -/

section normalForm

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The Fricke normal form `A₀`. -/
noncomputable def nA : SL(2, ℝ) :=
  ⟨!![x - y / z, x / z ^ 2; x, y / z], by
    rw [det_fin_two_of]; field_simp; linear_combination -hrel⟩

/-- The Fricke normal form `B₀`. -/
noncomputable def nB : SL(2, ℝ) :=
  ⟨!![y - x / z, -y / z ^ 2; -y, x / z], by
    rw [det_fin_two_of]; field_simp; linear_combination -hrel⟩

lemma coe_nA : ((nA hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![x - y / z, x / z ^ 2; x, y / z] := rfl

lemma coe_nB : ((nB hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![y - x / z, -y / z ^ 2; -y, x / z] := rfl

lemma coe_nAnB : ((nA hz hrel * nB hz hrel : SL(2, ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ) = !![z, -1 / z; z, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_nA, coe_nB, Matrix.mul_fin_two]
  have hz0 : z ≠ 0 := hz.ne'
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> grind

lemma tr_nA : tr (nA hz hrel) = x := by
  simp [tr, coe_nA, trace_fin_two]

lemma tr_nB : tr (nB hz hrel) = y := by
  simp [tr, coe_nB, trace_fin_two]

lemma tr_nAnB : tr (nA hz hrel * nB hz hrel) = z := by
  rw [tr, coe_nAnB]; simp [trace_fin_two]

end normalForm

/-! ### Ping-pong -/

/-- The basic Möbius computation. -/
lemma normSq_mul_re_smul_sub (g : SL(2, ℝ)) (v : ℝ) (hv : g 0 1 = v * g 1 1) (w : ℍ) :
    Complex.normSq (g 1 0 * (w : ℂ) + g 1 1) * ((g • w).re - v) =
      g 1 0 * (g 0 0 - v * g 1 0) * Complex.normSq (w : ℂ) + w.re := by
  have hdet := g.det_coe
  rw [det_fin_two] at hdet
  have hden : (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g) w
    simpa [UpperHalfPlane.denom] using this
  have hN : Complex.normSq (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
    rwa [Ne, Complex.normSq_eq_zero]
  have hre : (g • w).re = ((g 0 0 * (w : ℂ) + g 0 1) / (g 1 0 * (w : ℂ) + g 1 1)).re := by
    rw [UpperHalfPlane.re, coe_specialLinearGroup_apply]; simp
  set N := Complex.normSq (g 1 0 * (w : ℂ) + g 1 1)
  have hNe : N = (g 1 0 * w.re + g 1 1) ^ 2 + (g 1 0 * w.im) ^ 2 := by
    simp only [N, Complex.normSq_apply]; simp; ring
  have key : (g • w).re = ((g 0 0 * w.re + g 0 1) * (g 1 0 * w.re + g 1 1) +
      (g 0 0 * w.im) * (g 1 0 * w.im)) / N := by
    rw [hre, Complex.div_re]
    simp only [N]
    simp [Complex.normSq_apply]
    ring
  rw [key, mul_sub, mul_div_cancel₀ _ hN, hNe, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  rw [hv]
  rw [hv] at hdet
  linear_combination (w.re) * hdet

/-- The sign form: with `κ = c(a - vc) ≠ 0` and `m = -1/(2κ)`, `Re(g w) - v` has the sign of
`κ (|w - m|² - m²)`. -/
lemma re_smul_sub_eq (g : SL(2, ℝ)) (v κ : ℝ) (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ ≠ 0) (w : ℍ) :
    ∃ N > 0, N * ((g • w).re - v) =
      κ * (Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) - (1 / (2 * κ)) ^ 2) := by
  refine ⟨Complex.normSq (g 1 0 * (w : ℂ) + g 1 1), ?_, ?_⟩
  · have hden : (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
      have := UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g) w
      simpa [UpperHalfPlane.denom] using this
    exact Complex.normSq_pos.mpr hden
  rw [normSq_mul_re_smul_sub g v hv w, hκ]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp
  ring

lemma re_gt_of_out {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : 0 < κ) {w : ℍ}
    (hw : (1 / (2 * κ)) ^ 2 < Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ))) :
    v < (g • w).re := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne' w
  have : 0 < N * ((g • w).re - v) := by rw [h]; exact mul_pos hκ0 (by linarith)
  have := (pos_iff_pos_of_mul_pos this).mp hN
  linarith

lemma re_lt_of_out {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ < 0) {w : ℍ}
    (hw : (1 / (2 * κ)) ^ 2 < Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ))) :
    (g • w).re < v := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne w
  have : N * ((g • w).re - v) < 0 := by rw [h]; exact mul_neg_of_neg_of_pos hκ0 (by linarith)
  by_contra hc; push Not at hc; nlinarith

lemma in_of_re_lt {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : 0 < κ) {w : ℍ} (hw : w.re < v) :
    Complex.normSq (((g⁻¹ • w : ℍ) : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) < (1 / (2 * κ)) ^ 2 := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne' (g⁻¹ • w)
  rw [smul_inv_smul] at h
  have : N * (w.re - v) < 0 := mul_neg_of_pos_of_neg hN (by linarith)
  rw [h] at this
  by_contra hc; push Not at hc; nlinarith

lemma in_of_re_gt {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ < 0) {w : ℍ} (hw : v < w.re) :
    Complex.normSq (((g⁻¹ • w : ℍ) : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) < (1 / (2 * κ)) ^ 2 := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne (g⁻¹ • w)
  rw [smul_inv_smul] at h
  have : 0 < N * (w.re - v) := mul_pos hN (by linarith)
  rw [h] at this
  by_contra hc; push Not at hc; nlinarith

/-- Points of a closed disc `|w - m|² ≤ m²` have real part between `0` and `2m`. -/
lemma re_mem_of_normSq_le {w : ℍ} {m : ℝ} (h : Complex.normSq ((w : ℂ) - (m : ℂ)) ≤ m ^ 2) :
    min 0 (2 * m) ≤ w.re ∧ w.re ≤ max 0 (2 * m) := by
  have h' : (w.re - m) ^ 2 ≤ m ^ 2 := by
    have := w.im_pos
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    nlinarith
  constructor
  · rcases le_total 0 m with hm | hm
    · rw [min_eq_left (by linarith)]; nlinarith
    · rw [min_eq_right (by linarith)]; nlinarith
  · rcases le_total 0 m with hm | hm
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith

lemma re_mem_of_normSq_lt {w : ℍ} {m : ℝ} (h : Complex.normSq ((w : ℂ) - (m : ℂ)) < m ^ 2) :
    min 0 (2 * m) < w.re ∧ w.re < max 0 (2 * m) := by
  have h' : (w.re - m) ^ 2 < m ^ 2 := by
    have := w.im_pos
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    nlinarith
  constructor
  · rcases le_total 0 m with hm | hm
    · rw [min_eq_left (by linarith)]; nlinarith
    · rw [min_eq_right (by linarith)]; nlinarith
  · rcases le_total 0 m with hm | hm
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith

section normal

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The four ping-pong regions and the open quadrilateral. With `v₁ = -y/(xz)`, `v₃ = x/(yz)`:
`mA = v₁/2`, `mB = v₃/2`. -/
noncomputable def ppX (x y z : ℝ) : Fin 2 × Bool → Set ℍ
  | (0, true) => {w | x / (y * z) < w.re}
  | (0, false) => {w | Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) <
      (-y / (2 * x * z)) ^ 2}
  | (1, true) => {w | w.re < -y / (x * z)}
  | (1, false) => {w | Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) <
      (x / (2 * y * z)) ^ 2}

/-- The open fundamental quadrilateral. -/
def ppQ (x y z : ℝ) : Set ℍ :=
  {w | (-y / (2 * x * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) ∧
    (x / (2 * y * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) ∧
    -y / (x * z) < w.re ∧ w.re < x / (y * z)}

/-- The generators as letters. -/
noncomputable def ppGen : Fin 2 × Bool → SL(2, ℝ)
  | (0, true) => nA hz hrel
  | (0, false) => (nA hz hrel)⁻¹
  | (1, true) => nB hz hrel
  | (1, false) => (nB hz hrel)⁻¹

include hx hy in
lemma nA_hv : (nA hz hrel : SL(2, ℝ)) 0 1 = x / (y * z) * (nA hz hrel : SL(2, ℝ)) 1 1 := by
  simp only [coe_nA, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp

include hx hy in
lemma nA_hκ : (nA hz hrel : SL(2, ℝ)) 1 0 * ((nA hz hrel : SL(2, ℝ)) 0 0 -
    x / (y * z) * (nA hz hrel : SL(2, ℝ)) 1 0) = x * z / y := by
  simp only [coe_nA, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp
  grind

include hx hy in
lemma nB_hv : (nB hz hrel : SL(2, ℝ)) 0 1 = -y / (x * z) * (nB hz hrel : SL(2, ℝ)) 1 1 := by
  simp only [coe_nB, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp

include hx hy in
lemma nB_hκ : (nB hz hrel : SL(2, ℝ)) 1 0 * ((nB hz hrel : SL(2, ℝ)) 0 0 -
    -y / (x * z) * (nB hz hrel : SL(2, ℝ)) 1 0) = -(y * z / x) := by
  simp only [coe_nB, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp
  grind

include hx hy hz in
lemma pp_facts :
    (-y / (x * z) < 0) ∧ (0 < x / (y * z)) ∧ 2 * (-y / (2 * x * z)) = -y / (x * z) ∧
      2 * (x / (2 * y * z)) = x / (y * z) ∧
      -1 / (2 * (x * z / y)) = -y / (2 * x * z) ∧
      (1 / (2 * (x * z / y))) ^ 2 = (-y / (2 * x * z)) ^ 2 ∧
      -1 / (2 * -(y * z / x)) = x / (2 * y * z) ∧
      (1 / (2 * -(y * z / x))) ^ 2 = (x / (2 * y * z)) ^ 2 := by
  refine ⟨?_, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [neg_div]; exact neg_neg_of_pos (by positivity)
  all_goals field_simp

include hx hy in
/-- **Ping-pong step.** -/
lemma pp_step (s t : Fin 2 × Bool) (hst : s.1 = t.1 → s.2 = t.2) :
    ppGen hz hrel s • ppX x y z t ⊆ ppX x y z s := by
  obtain ⟨hv1, hv3, e1, e3, emA, erA, emB, erB⟩ := pp_facts hx hy hz
  have hκA : 0 < x * z / y := by positivity
  have hκB : -(y * z / x) < 0 := by rw [neg_lt_zero]; positivity
  -- domains
  have domA : ∀ w : ℍ, w.re < -y / (x * z) ∨ 0 < w.re →
      (-y / (2 * x * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) := by
    intro w hre
    by_contra hc; push Not at hc
    have := re_mem_of_normSq_le (m := -y / (2 * x * z)) hc
    rw [e1, min_eq_right hv1.le, max_eq_left hv1.le] at this
    rcases hre with h | h <;> linarith [this.1, this.2]
  have domB : ∀ w : ℍ, w.re < 0 ∨ x / (y * z) < w.re →
      (x / (2 * y * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) := by
    intro w hre
    by_contra hc; push Not at hc
    have := re_mem_of_normSq_le (m := x / (2 * y * z)) hc
    rw [e3, min_eq_left hv3.le, max_eq_right hv3.le] at this
    rcases hre with h | h <;> linarith [this.1, this.2]
  -- facts about the regions
  have hX : ∀ w : ℍ, w ∈ ppX x y z t →
      (t = (0, true) ∧ x / (y * z) < w.re) ∨ (t = (1, true) ∧ w.re < -y / (x * z)) ∨
      (t = (0, false) ∧ -y / (x * z) < w.re ∧ w.re < 0) ∨
      (t = (1, false) ∧ 0 < w.re ∧ w.re < x / (y * z)) := by
    intro w hw
    obtain ⟨j, c⟩ := t
    fin_cases j <;> cases c
    · right; right; left
      have := re_mem_of_normSq_lt (m := -y / (2 * x * z)) hw
      rw [e1, min_eq_right hv1.le, max_eq_left hv1.le] at this
      exact ⟨rfl, this⟩
    · left; exact ⟨rfl, hw⟩
    · right; right; right
      have := re_mem_of_normSq_lt (m := x / (2 * y * z)) hw
      rw [e3, min_eq_left hv3.le, max_eq_right hv3.le] at this
      exact ⟨rfl, this⟩
    · right; left; exact ⟨rfl, hw⟩
  -- actions
  have actA : ∀ w : ℍ, (-y / (2 * x * z)) ^ 2 <
      Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) →
        nA hz hrel • w ∈ ppX x y z (0, true) := by
    intro w hw
    exact re_gt_of_out (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA (by rwa [emA, erA])
  have actAi : ∀ w : ℍ, w.re < x / (y * z) → (nA hz hrel)⁻¹ • w ∈ ppX x y z (0, false) := by
    intro w hw
    have := in_of_re_lt (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA hw
    rwa [emA, erA] at this
  have actB : ∀ w : ℍ, (x / (2 * y * z)) ^ 2 <
      Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) →
        nB hz hrel • w ∈ ppX x y z (1, true) := by
    intro w hw
    exact re_lt_of_out (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB (by rwa [emB, erB])
  have actBi : ∀ w : ℍ, -y / (x * z) < w.re → (nB hz hrel)⁻¹ • w ∈ ppX x y z (1, false) := by
    intro w hw
    have := in_of_re_gt (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB hw
    rwa [emB, erB] at this
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨i, b⟩ := s
  rcases hX w hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
  fin_cases i <;> cases b <;> simp at hst <;> simp only [ppGen] <;>
  first
    | exact actA w (domA w (by first | (left; linarith) | (right; linarith)))
    | exact actAi w (by linarith)
    | exact actB w (domB w (by first | (left; linarith) | (right; linarith)))
    | exact actBi w (by linarith)

include hx hy in
lemma pp_stepQ (s : Fin 2 × Bool) : ppGen hz hrel s • ppQ x y z ⊆ ppX x y z s := by
  obtain ⟨hv1, hv3, e1, e3, emA, erA, emB, erB⟩ := pp_facts hx hy hz
  have hκA : 0 < x * z / y := by positivity
  have hκB : -(y * z / x) < 0 := by rw [neg_lt_zero]; positivity
  rintro _ ⟨w, ⟨hq1, hq2, hq3, hq4⟩, rfl⟩
  obtain ⟨i, b⟩ := s
  fin_cases i <;> cases b <;> simp only [ppGen]
  · have := in_of_re_lt (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA hq4
    rwa [emA, erA] at this
  · exact re_gt_of_out (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA (by rwa [emA, erA])
  · have := in_of_re_gt (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB hq3
    rwa [emB, erB] at this
  · exact re_lt_of_out (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB (by rwa [emB, erB])

lemma ppX_disjoint_Q (s : Fin 2 × Bool) : Disjoint (ppX x y z s) (ppQ x y z) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨hq1, hq2, hq3, hq4⟩
  obtain ⟨i, b⟩ := s
  fin_cases i <;> cases b <;> simp only [ppX, Set.mem_setOf_eq] at hw <;> linarith

include hx hy in
/-- **Ping-pong.** A reduced nonempty word maps `Q°` into the region of its first letter. -/
lemma pp_word : ∀ (L : List (Fin 2 × Bool)) (s : Fin 2 × Bool), FreeGroup.IsReduced (s :: L) →
    ((s :: L).map (ppGen hz hrel)).prod • ppQ x y z ⊆ ppX x y z s := by
  intro L
  induction L with
  | nil =>
    intro s _
    simpa using pp_stepQ hx hy hz hrel s
  | cons t L ih =>
    intro s hL
    rw [FreeGroup.isReduced_cons_cons] at hL
    rw [List.map_cons, List.prod_cons, mul_smul]
    exact (Set.smul_set_mono (ih t hL.2)).trans (pp_step hx hy hz hrel s t hL.1)

/-- The generator map `Fin 2 → SL(2, ℝ)`. -/
noncomputable def ppF : Fin 2 → SL(2, ℝ) := ![nA hz hrel, nB hz hrel]

lemma lift_mk_eq (L : List (Fin 2 × Bool)) :
    FreeGroup.lift (ppF hz hrel) (FreeGroup.mk L) = (L.map (ppGen hz hrel)).prod := by
  rw [FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  rintro ⟨i, b⟩ -
  fin_cases i <;> cases b <;> rfl

include hx hy in
/-- Every nontrivial element moves `Q°` off itself. -/
theorem pp_disjoint {g : FreeGroup (Fin 2)} (hg : g ≠ 1) :
    Disjoint (FreeGroup.lift (ppF hz hrel) g • ppQ x y z) (ppQ x y z) := by
  obtain ⟨s, L, hL⟩ : ∃ s L, g.toWord = s :: L := by
    rcases h : g.toWord with _ | ⟨s, L⟩
    · exact absurd (FreeGroup.toWord_eq_nil_iff.mp h) hg
    · exact ⟨s, L, rfl⟩
  have hred : FreeGroup.IsReduced (s :: L) := hL ▸ FreeGroup.isReduced_toWord
  rw [← FreeGroup.mk_toWord (x := g), hL, lift_mk_eq]
  exact Set.disjoint_of_subset_left (pp_word hx hy hz hrel L s hred)
    (ppX_disjoint_Q s)

include hx hy hz in
lemma ppQ_nonempty : (ppQ x y z).Nonempty := by
  obtain ⟨hv1, hv3, -⟩ := pp_facts hx hy hz
  have key : ∀ m : ℝ, m ^ 2 < Complex.normSq (Complex.I - (m : ℂ)) := by
    intro m; rw [Complex.normSq_apply]; simp; nlinarith
  have hre : (⟨Complex.I, by simp⟩ : ℍ).re = 0 := by simp [UpperHalfPlane.re]
  exact ⟨⟨Complex.I, by simp⟩, key _, key _, by rw [hre]; exact hv1, by rw [hre]; exact hv3⟩

lemma ppQ_isOpen : IsOpen (ppQ x y z) := by
  have h1 : Continuous fun w : ℍ ↦ Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) := by
    fun_prop
  have h2 : Continuous fun w : ℍ ↦ Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) := by
    fun_prop
  simp only [ppQ, Set.setOf_and]
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)))

include hx hy in
/-- **The normal form group is free on `A₀, B₀`.** -/
theorem injective_lift_normal : Function.Injective (FreeGroup.lift (ppF hz hrel)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  obtain ⟨w, hw⟩ := ppQ_nonempty hx hy hz
  have := pp_disjoint hx hy hz hrel hne
  rw [hg, one_smul, disjoint_self, Set.bot_eq_empty] at this
  rw [this] at hw; exact hw

end normal

/-! ### Freeness modulo `±1` -/

section Free

lemma neg_inv_SL (X : SL(2, ℝ)) : (-X)⁻¹ = -X⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])

/-- Changing the signs of the generators changes the value of a word by a sign. -/
lemma lift_signs {A B A' B' : SL(2, ℝ)} (hA : A' ∈ ({A, -A} : Set SL(2, ℝ)))
    (hB : B' ∈ ({B, -B} : Set SL(2, ℝ))) (w : FreeGroup (Fin 2)) :
    FreeGroup.lift ![A', B'] w = FreeGroup.lift ![A, B] w ∨
      FreeGroup.lift ![A', B'] w = -FreeGroup.lift ![A, B] w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
    fin_cases i
    · rcases hA with rfl | rfl <;> simp
    · rcases hB with rfl | rfl <;> simp
  | inv_of i h =>
    rw [map_inv, map_inv]
    rcases h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, neg_inv_SL])
  | mul x y hx hy =>
    rw [map_mul, map_mul]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact Or.inl rfl
    · exact Or.inr (mul_neg _ _)
    · exact Or.inr (neg_mul _ _)
    · exact Or.inl (neg_mul_neg _ _)

/-- **Once-punctured torus groups are free modulo `±1`.** If `tr [A, B] = -2` and `tr A ≠ 0`,
then a word `w` in `A, B` with value `±1` is trivial. -/
theorem eq_one_of_lift_eq_pm_one {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) {w : FreeGroup (Fin 2)}
    (hw : FreeGroup.lift ![A, B] w = 1 ∨ FreeGroup.lift ![A, B] w = -1) : w = 1 := by
  have hrel := (tr_commutator_eq_neg_two_iff A B).mp hcomm
  have hpos : 0 < tr A * tr B * tr (A * B) := by
    rw [← hrel]; have := pow_pos (abs_pos.mpr hA) 2; rw [sq_abs] at this; positivity
  obtain ⟨A'', hA'', B'', hB'', e1, e2, e3, e4⟩ := exists_sign_normalize hpos
  have hy' : tr B ≠ 0 := by
    intro h; rw [h] at hrel; apply hA; nlinarith [sq_nonneg (tr A), sq_nonneg (tr (A * B))]
  have hz' : tr (A * B) ≠ 0 := by
    intro h; rw [h] at hrel; apply hA; nlinarith [sq_nonneg (tr A), sq_nonneg (tr B)]
  have hx0 : 0 < |tr A| := abs_pos.mpr hA
  have hy0 : 0 < |tr B| := abs_pos.mpr hy'
  have hz0 : 0 < |tr (A * B)| := abs_pos.mpr hz'
  have hrelxyz : |tr A| ^ 2 + |tr B| ^ 2 + |tr (A * B)| ^ 2 =
      |tr A| * |tr B| * |tr (A * B)| := by
    simp only [sq_abs]
    rw [← abs_mul, ← abs_mul, ← hrel, abs_of_pos (by rw [hrel]; exact hpos)]
  have hx4 : 4 < tr A'' ^ 2 := by
    rw [e1, sq_abs]; exact four_lt_sq_of_fricke hrel hA
  have hc : tr (A'' * B'' * A''⁻¹ * B''⁻¹) ≠ 2 := by
    rw [e4, hcomm]; norm_num
  obtain ⟨g, hgA, hgB⟩ := exists_conj_of_tr_eq (A' := nA hz0 hrelxyz) (B' := nB hz0 hrelxyz)
    hx4 hc (by rw [e1, tr_nA]) (by rw [e2, tr_nB]) (by rw [e3, tr_nAnB])
  -- conjugation by `g` carries the `(A'', B'')`-word to the normal-form word
  have hconj : ∀ v : FreeGroup (Fin 2), g * toGL (FreeGroup.lift ![A'', B''] v) * g⁻¹ =
      toGL (FreeGroup.lift (ppF hz0 hrelxyz) v) := by
    intro v
    have := congrArg (fun φ : FreeGroup (Fin 2) →* GL (Fin 2) ℝ ↦ φ v)
      (FreeGroup.ext_hom (((MulAut.conj g).toMonoidHom.comp toGL).comp
        (FreeGroup.lift ![A'', B''])) (toGL.comp (FreeGroup.lift (ppF hz0 hrelxyz))) fun i ↦ by
          fin_cases i
          · simpa [ppF] using hgA
          · simpa [ppF] using hgB)
    simpa using this
  have hpm : FreeGroup.lift ![A'', B''] w = 1 ∨ FreeGroup.lift ![A'', B''] w = -1 := by
    rcases lift_signs hA'' hB'' w with h | h <;> rw [h] <;> rcases hw with hw | hw <;> rw [hw]
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  -- so the normal-form word is `±1`, hence acts trivially on `ℍ`
  have hcent : ∀ X : SL(2, ℝ), X = 1 ∨ X = -1 → g * toGL X * g⁻¹ = toGL X := by
    rintro X (rfl | rfl)
    · simp
    · ext1
      simp [Matrix.SpecialLinearGroup.coe_neg]
  have htriv : ∀ τ : ℍ, FreeGroup.lift (ppF hz0 hrelxyz) w • τ = τ := by
    have hX := hcent _ hpm
    rw [hconj] at hX
    have heq : FreeGroup.lift (ppF hz0 hrelxyz) w = FreeGroup.lift ![A'', B''] w :=
      toGL_injective hX
    intro τ
    rw [heq]
    rcases hpm with h | h <;> rw [h]
    · exact one_smul _ _
    · apply UpperHalfPlane.ext
      rw [coe_specialLinearGroup_apply]
      simp [Matrix.SpecialLinearGroup.coe_neg]
  by_contra hne
  obtain ⟨τ, hτ⟩ := ppQ_nonempty hx0 hy0 hz0
  have := pp_disjoint hx0 hy0 hz0 hrelxyz hne
  exact Set.disjoint_left.1 this ⟨τ, hτ, htriv τ⟩ hτ

end Free

end Uniformization.Fricke

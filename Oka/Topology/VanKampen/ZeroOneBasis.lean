/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.LoopsAround

/-!
# A geometric basis of `π₁(ℂ ∖ {0, 1})` whose product is a loop around `∞`

For every `R > 1/2` and every base point `x ∈ ℂ ∖ {0, 1}` there are loops `g₀`, `g₁` around `0`
and `1` (`Complex.PuncturedPlane.IsLoopAround`) forming a free basis of `π₁(ℂ ∖ {0, 1}, x)` and
such that `g₀ * g₁` is the class of `δ · B_R · δ⁻¹`, where `B_R` is the counterclockwise circle
of radius `R` around `1/2` (`Complex.PuncturedPlane.ZeroOne.bigPath`) and `δ` a path from `x`
to its lowest point `1/2 - R i` (`Complex.exists_isLoopAround_basis_zero_one`). Since the
product in `FundamentalGroup` is `p * q = q.trans p`, `g₀ * g₁` is "`g₁` first, then `g₀`".

The arbitrary basis of `Complex.exists_isLoopAround_basis` carries no such information: for
`|S| ≥ 3` the conditions "`g_s` is a loop around `s`" do not determine the conjugacy class of
any ordered product of the `g_s`.

## Proof

Seifert–van Kampen (`VanKampen.coprodEquiv`) for the cover of `ℂ ∖ {0, 1}` by
`U = {Re z < 2/3} ∖ {0}` and `V = {Re z > 1/3} ∖ {1}`, whose intersection is a convex strip. The
circle `B_R` (from its lowest point `1/2 - R i`) is literally the concatenation of its right half
`r` and its left half `l`; with the vertical segment `σ` from `1/2 - R i` to `1/2 + R i`,
`[B_R] = [r · σ⁻¹] ≫ [σ · l]`, where `ℓ₁ = r · σ⁻¹` is a loop in `V` and `ℓ₀ = σ · l` a loop in
`U`. Each `ℓ_a` is identified with a loop around `a` in its one-point convex region by its action
on the fibre of `exp : ℂ → ℂ ∖ {0}` (`Complex.PuncturedPlane.eq_conj_circle_of_lift`): an explicit
lift of `ℓ_a - a` along `exp` is built from `log` on the slit plane, on the piece in it, and from
`log (-z) + π i` on the piece in the opposite slit plane; it ends at its starting point plus
`2πi` (`Complex.arg_neg_eq_arg_sub_pi_of_im_pos`, `Complex.arg_neg_eq_arg_add_pi_of_im_neg`).

## References

* [A. Hatcher, *Algebraic Topology*, §1.2][hatcher02]
-/

open Set Topology Metric CategoryTheory

namespace Complex.PuncturedPlane

section Lift

/-- A path in `ℂ` with values in `Q`, as a path in the subtype `{z // Q z}`. -/
noncomputable def restrictPath {Q : ℂ → Prop} {y z : ℂ} (γ : Path y z) (h : ∀ t, Q (γ t)) :
    Path (⟨y, by simpa using h 0⟩ : Subtype Q) ⟨z, by simpa using h 1⟩ where
  toFun t := ⟨γ t, h t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp] lemma coe_restrictPath {Q : ℂ → Prop} {y z : ℂ} (γ : Path y z) (h : ∀ t, Q (γ t))
    (t : unitInterval) : (restrictPath γ h t : ℂ) = γ t := rfl

/-- The lift `t ↦ log (γ t - a)` along `exp` of `γ - a`, for `γ - a` in the slit plane. -/
noncomputable def logPath {y z : ℂ} (γ : Path y z) (a : ℂ) (h : ∀ t, γ t - a ∈ slitPlane) :
    Path (Complex.log (y - a)) (Complex.log (z - a)) where
  toFun t := Complex.log (γ t - a)
  continuous_toFun := (γ.continuous.sub continuous_const).clog h
  source' := by simp
  target' := by simp

lemma exp_logPath {y z : ℂ} (γ : Path y z) (a : ℂ) (h : ∀ t, γ t - a ∈ slitPlane)
    (t : unitInterval) : Complex.exp (logPath γ a h t) = γ t - a :=
  Complex.exp_log (slitPlane_ne_zero (h t))

/-- The lift `t ↦ log (-(γ t - a)) + π i` along `exp` of `γ - a`, for `-(γ - a)` in the slit
plane. -/
noncomputable def negLogPath {y z : ℂ} (γ : Path y z) (a : ℂ) (h : ∀ t, -(γ t - a) ∈ slitPlane) :
    Path (Complex.log (-(y - a)) + Real.pi * Complex.I)
      (Complex.log (-(z - a)) + Real.pi * Complex.I) where
  toFun t := Complex.log (-(γ t - a)) + Real.pi * Complex.I
  continuous_toFun := ((γ.continuous.sub continuous_const).neg.clog h).add continuous_const
  source' := by simp
  target' := by simp

lemma exp_negLogPath {y z : ℂ} (γ : Path y z) (a : ℂ) (h : ∀ t, -(γ t - a) ∈ slitPlane)
    (t : unitInterval) : Complex.exp (negLogPath γ a h t) = γ t - a := by
  change Complex.exp (Complex.log (-(γ t - a)) + Real.pi * Complex.I) = _
  rw [Complex.exp_add, Complex.exp_log (slitPlane_ne_zero (h t)), Complex.exp_pi_mul_I]
  ring

lemma log_neg_add_pi_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Complex.log (-w) + Real.pi * Complex.I = Complex.log w := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]
  push_cast
  ring

lemma log_neg_add_pi_of_im_neg {w : ℂ} (hw : w.im < 0) :
    Complex.log (-w) + Real.pi * Complex.I = Complex.log w + 2 * Real.pi * Complex.I := by
  simp only [Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]
  push_cast
  ring

/-- Pointwise lifts of two paths give a pointwise lift of their concatenation. -/
lemma exp_trans_apply {X : Type*} [TopologicalSpace X] {y z w : X} {e₀ e₁ e₂ : ℂ}
    (f : X → ℂ) {p₁ : Path y z} {p₂ : Path z w} {Γ₁ : Path e₀ e₁} {Γ₂ : Path e₁ e₂}
    (h₁ : ∀ t, Complex.exp (Γ₁ t) = f (p₁ t)) (h₂ : ∀ t, Complex.exp (Γ₂ t) = f (p₂ t))
    (t : unitInterval) : Complex.exp ((Γ₁.trans Γ₂) t) = f ((p₁.trans p₂) t) := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact h₁ _
  · exact h₂ _

/-- **A loop with an explicit lift along `exp` ending at its start plus `2πi` acts on the fibre
of `exp` by the period `2πi`.** -/
theorem fundamentalGroupToMulOpposite_of_lift {y : {z : ℂ // z ≠ 0}} (e : expMap ⁻¹' {y})
    (c : Path y y) (Γ : Path e.1 (e.1 + 2 * Real.pi * Complex.I))
    (hΓ : ∀ t, Complex.exp (Γ t) = c t) :
    Complex.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e
      (FundamentalGroup.fromPath (.mk c)) = MulOpposite.op (Multiplicative.ofAdd twoPiI) := by
  set hp := Complex.isAddQuotientCoveringMap_exp
  rw [IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff]
  have hy : expMap (e.1 + 2 * Real.pi * Complex.I) = y := by
    apply Subtype.ext
    have := hΓ 1
    rw [Γ.target, c.target] at this
    exact this
  have hm : hp.isCoveringMap.monodromy (⟦c⟧ : Path.Homotopic.Quotient y y) e =
      ⟨e.1 + 2 * Real.pi * Complex.I, hy⟩ := by
    refine hp.isCoveringMap.monodromy_eq_of_map_eq ⟦Γ⟧ ?_
    change Path.Homotopic.Quotient.mk (Γ.map _) = Path.Homotopic.Quotient.mk (c.cast _ _)
    congr 1
    ext t
    exact hΓ t
  change _ = ((hp.isCoveringMap.monodromy (⟦c⟧ : Path.Homotopic.Quotient y y) e : _) : ℂ)
  rw [hm]
  change (2 * Real.pi * Complex.I : ℂ) + e.1 = _
  ring

/-- **A loop in a one-point convex region with an explicit lift of winding one is the loop
around the puncture**: if `exp ∘ Γ = c - a` for a path `Γ` from `e₀` to `e₀ + 2πi`, then the
class of `c` equals `δ · circle · δ⁻¹` for every admissible circle around `a` and every `δ`. -/
theorem eq_conj_circle_of_lift {C : Set ℂ} {a : ℂ} (hCc : Convex ℝ C) {r : ℝ}
    (h : Admissible C {a} a r) {x : Region C {a}} (c : Path x x) {e₀ : ℂ}
    (Γ : Path e₀ (e₀ + 2 * Real.pi * Complex.I)) (hΓ : ∀ t, Complex.exp (Γ t) = (c t : ℂ) - a)
    (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (circleBase h)) :
    FundamentalGroup.fromPath (.mk c) = δ ≫ circleArrow h ≫ Groupoid.inv δ := by
  have hJ := map_bijective_of_homotopyEquiv (homotopyEquiv hCc h) x
  have he : expMap e₀ = shiftMap x := by
    apply Subtype.ext
    have := hΓ 0
    rw [Γ.source, c.source] at this
    exact this
  let e : expMap ⁻¹' {shiftMap x} := ⟨e₀, he⟩
  let Φ := Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e
  have h₁ : Φ (FundamentalGroup.map shiftMap x (FundamentalGroup.fromPath (.mk c))) =
      MulOpposite.op (Multiplicative.ofAdd twoPiI) := by
    change Complex.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e
      (FundamentalGroup.fromPath (.mk (c.map shiftMap.continuous))) = _
    exact fundamentalGroupToMulOpposite_of_lift e _ Γ hΓ
  have h₂ : Φ (FundamentalGroup.map shiftMap x (δ ≫ circleArrow h ≫ Groupoid.inv δ)) =
      MulOpposite.op (Multiplicative.ofAdd twoPiI) := by
    change Complex.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e
      ((FundamentalGroupoid.map shiftMap).map (δ ≫ circleArrow h ≫ Groupoid.inv δ)) = _
    rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Functor.map_inv,
      ← Groupoid.inv_eq_inv]
    refine fundamentalGroupToMulOpposite_conj_circle e _ ((circlePath h).map shiftMap.continuous)
      fun t ↦ ?_
    change circleFun a r t - a = ((a + (r : ℂ)) - a) * _
    simp only [circleFun]
    ring
  apply hJ.1
  apply Φ.injective
  change Φ (FundamentalGroup.map shiftMap x _) = Φ (FundamentalGroup.map shiftMap x _)
  rw [h₁, h₂]

/-- The loop of `eq_conj_circle_of_lift` is a loop around `a` and a free generator of
`π₁(C ∖ {a})`. -/
theorem isLoopAround_of_lift {C : Set ℂ} {a : ℂ} (hCo : IsOpen C) (hCc : Convex ℝ C) (ha : a ∈ C)
    {x : Region C {a}} (c : Path x x) {e₀ : ℂ} (Γ : Path e₀ (e₀ + 2 * Real.pi * Complex.I))
    (hΓ : ∀ t, Complex.exp (Γ t) = (c t : ℂ) - a) :
    IsLoopAround (FundamentalGroup.fromPath (.mk c)) a ∧
      Function.Bijective
        (FreeGroup.lift fun _ : ({a} : Finset ℂ) ↦ FundamentalGroup.fromPath (.mk c)) := by
  obtain ⟨-, γ, hγ, hbij⟩ := loopStatement_one C hCo hCc {a} (by simpa using ha) (by simp) x
  have key : ∀ s, γ s = FundamentalGroup.fromPath (.mk c) := by
    rintro ⟨s, hs⟩
    obtain rfl : s = a := Finset.mem_singleton.1 hs
    obtain ⟨r, h, δ, hδ⟩ := hγ ⟨s, hs⟩
    exact hδ.trans (eq_conj_circle_of_lift hCc h c Γ hΓ δ).symm
  have hfun : (fun _ : ({a} : Finset ℂ) ↦ FundamentalGroup.fromPath (.mk c)) = γ := funext fun s ↦
    (key s).symm
  refine ⟨?_, hfun ▸ hbij⟩
  rw [← key ⟨a, Finset.mem_singleton_self a⟩]
  exact hγ _

end Lift

/-! ### The circle of radius `R` around `1/2` and its two halves -/

namespace ZeroOne

/-- The lowest point `1/2 - R i` of the circle of radius `R` around `1/2`. -/
noncomputable def bot (R : ℝ) : ℂ := ⟨1 / 2, -R⟩

/-- The highest point `1/2 + R i` of the circle of radius `R` around `1/2`. -/
noncomputable def top (R : ℝ) : ℂ := ⟨1 / 2, R⟩

/-- The vertical segment from `1/2 - R i` to `1/2 + R i`. -/
noncomputable def segPath (R : ℝ) : Path (bot R) (top R) where
  toFun t := ⟨1 / 2, R * (2 * t - 1)⟩
  continuous_toFun := continuous_mk.comp (continuous_const.prodMk (by fun_prop))
  source' := by apply Complex.ext <;> simp [bot]
  target' := by apply Complex.ext <;> simp [top]; ring

/-- The right half `t ↦ 1/2 + R e^{i(πt - π/2)}` of the circle, from `1/2 - R i` to
`1/2 + R i`. -/
noncomputable def rightPath (R : ℝ) : Path (bot R) (top R) where
  toFun t := ⟨1 / 2 + R * Real.sin (Real.pi * t), -(R * Real.cos (Real.pi * t))⟩
  continuous_toFun := continuous_mk.comp ((by fun_prop : Continuous fun t : unitInterval ↦
    1 / 2 + R * Real.sin (Real.pi * t)).prodMk (by fun_prop))
  source' := by apply Complex.ext <;> simp [bot]
  target' := by apply Complex.ext <;> simp [top]

/-- The left half `t ↦ 1/2 + R e^{i(πt + π/2)}` of the circle, from `1/2 + R i` to
`1/2 - R i`. -/
noncomputable def leftPath (R : ℝ) : Path (top R) (bot R) where
  toFun t := ⟨1 / 2 - R * Real.sin (Real.pi * t), R * Real.cos (Real.pi * t)⟩
  continuous_toFun := continuous_mk.comp ((by fun_prop : Continuous fun t : unitInterval ↦
    1 / 2 - R * Real.sin (Real.pi * t)).prodMk (by fun_prop))
  source' := by apply Complex.ext <;> simp [top]
  target' := by apply Complex.ext <;> simp [bot]

/-- **The circle of radius `R` around `1/2`**, counterclockwise from its lowest point:
`t ↦ 1/2 + R e^{i(2πt - π/2)} = 1/2 - R i e^{2πit}`. -/
noncomputable def bigPath (R : ℝ) : Path (bot R) (bot R) where
  toFun t := ⟨1 / 2 + R * Real.sin (2 * Real.pi * t), -(R * Real.cos (2 * Real.pi * t))⟩
  continuous_toFun := continuous_mk.comp ((by fun_prop : Continuous fun t : unitInterval ↦
    1 / 2 + R * Real.sin (2 * Real.pi * t)).prodMk (by fun_prop))
  source' := by apply Complex.ext <;> simp [bot]
  target' := by apply Complex.ext <;> simp [bot]

lemma bigPath_apply (R : ℝ) (t : unitInterval) :
    (bigPath R t : ℂ) = 1 / 2 - R * Complex.I *
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  set θ : ℝ := 2 * Real.pi * t with hθ
  have he : Complex.exp ((θ : ℂ) * Complex.I) = ⟨Real.cos θ, Real.sin θ⟩ := by
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re]
    · rw [Complex.exp_ofReal_mul_I_im]
  rw [he]
  apply Complex.ext <;> simp [bigPath, ← hθ]

/-- The circle is the concatenation of its two halves. -/
theorem bigPath_eq_trans (R : ℝ) : bigPath R = (rightPath R).trans (leftPath R) := by
  ext t
  rw [Path.trans_apply]
  split_ifs with ht
  · have e : Real.pi * (2 * (t : ℝ)) = 2 * Real.pi * t := by ring
    apply Complex.ext <;> simp [bigPath, rightPath, e]
  · have e : Real.pi * (2 * (t : ℝ) - 1) = 2 * Real.pi * t - Real.pi := by ring
    apply Complex.ext <;> simp [bigPath, leftPath, e, Real.sin_sub_pi, Real.cos_sub_pi]

variable {R : ℝ}

lemma sin_pi_mul_nonneg (t : unitInterval) : 0 ≤ Real.sin (Real.pi * t) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le t.2.1)
    (mul_le_of_le_one_right Real.pi_pos.le t.2.2)

/-- On the half circles, `R sin (π t) - 1/2 > 0` wherever `R cos (π t) = 0`. -/
lemma arc_pos_or_ne (hR : 1 / 2 < R) (t : unitInterval) :
    0 < R * Real.sin (Real.pi * t) - 1 / 2 ∨ R * Real.cos (Real.pi * t) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hc : Real.cos (Real.pi * t) = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · exact h
  have hs := Real.sin_sq_add_cos_sq (Real.pi * t)
  have h0 := sin_pi_mul_nonneg t
  rw [hc] at hs
  have : Real.sin (Real.pi * t) = 1 := by nlinarith
  rw [this] at h1
  linarith

lemma seg_sub_zero_mem (t : unitInterval) : segPath R t - 0 ∈ slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (by simp [segPath]))

lemma neg_left_sub_zero_mem (hR : 1 / 2 < R) (t : unitInterval) :
    -(leftPath R t - 0) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases arc_pos_or_ne hR t with h | h
  · exact Or.inl (by simp [leftPath]; linarith)
  · exact Or.inr (by simpa [leftPath] using h)

lemma right_sub_one_mem (hR : 1 / 2 < R) (t : unitInterval) :
    rightPath R t - 1 ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases arc_pos_or_ne hR t with h | h
  · exact Or.inl (by simp [rightPath]; linarith)
  · exact Or.inr (by simpa [rightPath] using h)

lemma neg_segSymm_sub_one_mem (t : unitInterval) : -((segPath R).symm t - 1) ∈ slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (by simp [segPath]; norm_num))

/-- The left half plane `{Re z < 2/3}`. -/
def P₁ : Set ℂ := {z | z.re < 2 / 3}

/-- The right half plane `{Re z > 1/3}`. -/
def P₂ : Set ℂ := {z | 1 / 3 < z.re}

lemma isOpen_P₁ : IsOpen P₁ := isOpen_lt Complex.continuous_re continuous_const
lemma isOpen_P₂ : IsOpen P₂ := isOpen_lt continuous_const Complex.continuous_re
lemma convex_P₁ : Convex ℝ P₁ := convex_halfSpace_lt Complex.reLm.isLinear _
lemma convex_P₂ : Convex ℝ P₂ := convex_halfSpace_gt Complex.reLm.isLinear _

lemma seg_mem₁ (t : unitInterval) : segPath R t ∈ P₁ ∧ segPath R t ∉ ({0} : Finset ℂ) := by
  refine ⟨show (segPath R t).re < 2 / 3 by simp [segPath]; norm_num, ?_⟩
  simpa using slitPlane_ne_zero (seg_sub_zero_mem (R := R) t)

lemma left_mem₁ (hR : 1 / 2 < R) (t : unitInterval) :
    leftPath R t ∈ P₁ ∧ leftPath R t ∉ ({0} : Finset ℂ) := by
  have h0 := sin_pi_mul_nonneg t
  have hR0 : 0 ≤ R := by linarith
  refine ⟨show (leftPath R t).re < 2 / 3 by simp [leftPath]; nlinarith, ?_⟩
  simpa using slitPlane_ne_zero (neg_left_sub_zero_mem hR t)

lemma right_mem₂ (hR : 1 / 2 < R) (t : unitInterval) :
    rightPath R t ∈ P₂ ∧ rightPath R t ∉ ({1} : Finset ℂ) := by
  have h0 := sin_pi_mul_nonneg t
  have hR0 : 0 ≤ R := by linarith
  refine ⟨show 1 / 3 < (rightPath R t).re by simp [rightPath]; nlinarith, ?_⟩
  simpa [sub_eq_zero] using slitPlane_ne_zero (right_sub_one_mem hR t)

lemma segSymm_mem₂ (t : unitInterval) :
    (segPath R).symm t ∈ P₂ ∧ (segPath R).symm t ∉ ({1} : Finset ℂ) := by
  refine ⟨show 1 / 3 < ((segPath R).symm t).re by simp [segPath]; norm_num, ?_⟩
  have := slitPlane_ne_zero (neg_segSymm_sub_one_mem (R := R) t)
  intro hm
  rw [Finset.mem_singleton] at hm
  exact this (by rw [hm]; ring)

lemma big_mem (hR : 1 / 2 < R) (t : unitInterval) :
    bigPath R t ∈ (Set.univ : Set ℂ) ∧ bigPath R t ∉ ({0, 1} : Finset ℂ) := by
  refine ⟨Set.mem_univ _, fun hm ↦ ?_⟩
  have hs := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  have key : ∀ c : ℝ, (bigPath R t : ℂ) = c → c = 0 ∨ c = 1 → False := by
    intro c h hc
    have h1 : 1 / 2 + R * Real.sin (2 * Real.pi * t) = c := by
      simpa [bigPath] using congrArg Complex.re h
    have h2 : R = 0 ∨ Real.cos (2 * Real.pi * t) = 0 := by
      simpa [bigPath] using congrArg Complex.im h
    rcases h2 with h2 | h2
    · linarith
    rw [h2] at hs
    have e : R * Real.sin (2 * Real.pi * t) = c - 1 / 2 := by linarith
    have e2 : R ^ 2 * Real.sin (2 * Real.pi * t) ^ 2 = (c - 1 / 2) ^ 2 := by
      rw [← mul_pow, e]
    have hs1 : Real.sin (2 * Real.pi * t) ^ 2 = 1 := by linarith
    rw [hs1, mul_one] at e2
    rcases hc with rfl | rfl <;> nlinarith
  rcases Finset.mem_insert.1 hm with h | h
  · exact key 0 (by simpa using h) (Or.inl rfl)
  · exact key 1 (by simpa using h) (Or.inr rfl)

/-- The loop `ℓ₀ = σ · l` (segment up, then the left half circle) in `{Re z < 2/3} ∖ {0}`. -/
noncomputable def loop₀ (hR : 1 / 2 < R) : Path (⟨bot R, by simpa using seg_mem₁ (R := R) 0⟩ :
    Region P₁ {0}) ⟨bot R, by simpa using seg_mem₁ (R := R) 0⟩ :=
  (restrictPath (segPath R) seg_mem₁).trans (restrictPath (leftPath R) (left_mem₁ hR))

/-- The loop `ℓ₁ = r · σ⁻¹` (the right half circle, then the segment down) in
`{Re z > 1/3} ∖ {1}`. -/
noncomputable def loop₁ (hR : 1 / 2 < R) : Path (⟨bot R, by simpa using right_mem₂ hR 0⟩ :
    Region P₂ {1}) ⟨bot R, by simpa using right_mem₂ hR 0⟩ :=
  (restrictPath (rightPath R) (right_mem₂ hR)).trans (restrictPath (segPath R).symm segSymm_mem₂)

lemma isLoopAround_loop₀ (hR : 1 / 2 < R) :
    IsLoopAround (FundamentalGroup.fromPath (.mk (loop₀ hR))) 0 ∧
      Function.Bijective (FreeGroup.lift fun _ : ({0} : Finset ℂ) ↦
        FundamentalGroup.fromPath (.mk (loop₀ hR))) := by
  have hR0 : 0 < R := by linarith
  let Γ : Path (Complex.log (bot R - 0)) (Complex.log (bot R - 0) + 2 * Real.pi * Complex.I) :=
    (logPath (segPath R) 0 seg_sub_zero_mem).trans ((negLogPath (leftPath R) 0
      (neg_left_sub_zero_mem hR)).cast
      (log_neg_add_pi_of_im_pos (by simpa [top] using hR0)).symm
      (log_neg_add_pi_of_im_neg (by simp [bot]; linarith)).symm)
  refine isLoopAround_of_lift isOpen_P₁ convex_P₁ (show (0 : ℂ).re < 2 / 3 by norm_num)
    (loop₀ hR) Γ ?_
  exact exp_trans_apply (fun z : Region P₁ {0} ↦ (z : ℂ) - 0)
    (exp_logPath (segPath R) 0 seg_sub_zero_mem)
    (exp_negLogPath (leftPath R) 0 (neg_left_sub_zero_mem hR))

lemma isLoopAround_loop₁ (hR : 1 / 2 < R) :
    IsLoopAround (FundamentalGroup.fromPath (.mk (loop₁ hR))) 1 ∧
      Function.Bijective (FreeGroup.lift fun _ : ({1} : Finset ℂ) ↦
        FundamentalGroup.fromPath (.mk (loop₁ hR))) := by
  have hR0 : 0 < R := by linarith
  let Γ : Path (Complex.log (bot R - 1)) (Complex.log (bot R - 1) + 2 * Real.pi * Complex.I) :=
    (logPath (rightPath R) 1 (right_sub_one_mem hR)).trans ((negLogPath (segPath R).symm 1
      neg_segSymm_sub_one_mem).cast
      (log_neg_add_pi_of_im_pos (by simpa [top] using hR0)).symm
      (log_neg_add_pi_of_im_neg (by simp [bot]; linarith)).symm)
  refine isLoopAround_of_lift isOpen_P₂ convex_P₂ (show 1 / 3 < (1 : ℂ).re by norm_num)
    (loop₁ hR) Γ ?_
  exact exp_trans_apply (fun z : Region P₂ {1} ↦ (z : ℂ) - 1)
    (exp_logPath (rightPath R) 1 (right_sub_one_mem hR))
    (exp_negLogPath (segPath R).symm 1 neg_segSymm_sub_one_mem)

/-! ### Seifert–van Kampen for `ℂ ∖ {0, 1}` -/

/-- `ℂ ∖ {0, 1}`. -/
abbrev X01 : Type := Region Set.univ ({0, 1} : Finset ℂ)

/-- `P ∖ {a}` as the subspace `{x ∈ ℂ ∖ {0, 1} | x ∈ P}`, when `P` avoids the other point. -/
def pieceHomeomorph {P : Set ℂ} {a : ℂ}
    (hP : ∀ z ∈ P, z ∉ ({0, 1} : Finset ℂ) ↔ z ∉ ({a} : Finset ℂ)) :
    Region P {a} ≃ₜ {x : X01 | x.1 ∈ P} where
  toFun z := ⟨⟨z.1, Set.mem_univ _, (hP z.1 z.2.1).2 z.2.2⟩, z.2.1⟩
  invFun u := ⟨u.1.1, u.2, (hP _ u.2).1 u.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

lemma notMem_iff_of_mem_P₁ : ∀ z ∈ P₁, z ∉ ({0, 1} : Finset ℂ) ↔ z ∉ ({0} : Finset ℂ) := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨And.left, fun h ↦ ⟨h, fun h1 ↦ ?_⟩⟩
  rw [h1] at hz
  change (1 : ℂ).re < 2 / 3 at hz
  norm_num at hz

lemma notMem_iff_of_mem_P₂ : ∀ z ∈ P₂, z ∉ ({0, 1} : Finset ℂ) ↔ z ∉ ({1} : Finset ℂ) := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨And.right, fun h ↦ ⟨fun h0 ↦ ?_, h⟩⟩
  rw [h0] at hz
  change 1 / 3 < (0 : ℂ).re at hz
  norm_num at hz

/-- The inclusion `{Re z < 2/3} ∖ {0} → ℂ ∖ {0, 1}`. -/
noncomputable def incl₀ : C(Region P₁ {0}, X01) :=
  ⟨fun z ↦ (pieceHomeomorph notMem_iff_of_mem_P₁ z : X01),
    continuous_subtype_val.comp (pieceHomeomorph notMem_iff_of_mem_P₁).continuous⟩

/-- The inclusion `{Re z > 1/3} ∖ {1} → ℂ ∖ {0, 1}`. -/
noncomputable def incl₁ : C(Region P₂ {1}, X01) :=
  ⟨fun z ↦ (pieceHomeomorph notMem_iff_of_mem_P₂ z : X01),
    continuous_subtype_val.comp (pieceHomeomorph notMem_iff_of_mem_P₂).continuous⟩

variable {R : ℝ}

/-- The base point `1/2 - R i ∈ ℂ ∖ {0, 1}`. -/
noncomputable def bigBase (hR : 1 / 2 < R) : X01 := ⟨bot R, by simpa using big_mem hR 0⟩

/-- The circle of radius `R` around `1/2` as a loop in `ℂ ∖ {0, 1}`. -/
noncomputable def bigLoop (hR : 1 / 2 < R) : Path (bigBase hR) (bigBase hR) :=
  restrictPath (bigPath R) (big_mem hR)

/-- The class of the circle of radius `R` around `1/2` (a loop around `∞`). -/
noncomputable def bigArrow (hR : 1 / 2 < R) :
    FundamentalGroupoid.mk (bigBase hR) ⟶ FundamentalGroupoid.mk (bigBase hR) :=
  ⟦bigLoop hR⟧

lemma mk_trans_symm_trans {Y : Type*} [TopologicalSpace Y] {a b d : Y} (p q : Path a b)
    (l : Path b d) :
    Path.Homotopic.Quotient.mk ((p.trans q.symm).trans (q.trans l)) =
      Path.Homotopic.Quotient.mk (p.trans l) := by
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.symm _),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- The product of the two loops is the circle: `[ℓ₀] * [ℓ₁] = [ℓ₁ · ℓ₀] = [r · l] = [B_R]`. -/
theorem map_loop₀_mul_map_loop₁ (hR : 1 / 2 < R) :
    (show FundamentalGroup X01 (bigBase hR) from
      FundamentalGroup.map incl₀ _ (FundamentalGroup.fromPath (.mk (loop₀ hR)))) *
      (show FundamentalGroup X01 (bigBase hR) from
        FundamentalGroup.map incl₁ _ (FundamentalGroup.fromPath (.mk (loop₁ hR)))) =
      (show FundamentalGroup X01 (bigBase hR) from bigArrow hR) := by
  have hs : ∀ t, segPath R t ∈ (Set.univ : Set ℂ) ∧ segPath R t ∉ ({0, 1} : Finset ℂ) :=
    fun t ↦ ⟨Set.mem_univ _, (notMem_iff_of_mem_P₁ _ (seg_mem₁ t).1).2 (seg_mem₁ t).2⟩
  have hl : ∀ t, leftPath R t ∈ (Set.univ : Set ℂ) ∧ leftPath R t ∉ ({0, 1} : Finset ℂ) :=
    fun t ↦ ⟨Set.mem_univ _, (notMem_iff_of_mem_P₁ _ (left_mem₁ hR t).1).2 (left_mem₁ hR t).2⟩
  have hr : ∀ t, rightPath R t ∈ (Set.univ : Set ℂ) ∧ rightPath R t ∉ ({0, 1} : Finset ℂ) :=
    fun t ↦ ⟨Set.mem_univ _, (notMem_iff_of_mem_P₂ _ (right_mem₂ hR t).1).2 (right_mem₂ hR t).2⟩
  have h₀ : (loop₀ hR).map incl₀.continuous =
      (restrictPath (segPath R) hs).trans (restrictPath (leftPath R) hl) := by
    rw [loop₀, Path.map_trans]
    rfl
  have h₁ : (loop₁ hR).map incl₁.continuous =
      (restrictPath (rightPath R) hr).trans (restrictPath (segPath R) hs).symm := by
    rw [loop₁, Path.map_trans]
    rfl
  have hb : bigLoop hR = (restrictPath (rightPath R) hr).trans (restrictPath (leftPath R) hl) := by
    have e : (bigLoop hR).map continuous_subtype_val =
        ((restrictPath (rightPath R) hr).trans (restrictPath (leftPath R) hl)).map
          continuous_subtype_val := by
      rw [Path.map_trans]
      exact bigPath_eq_trans R
    apply Path.ext
    funext t
    apply Subtype.ext
    exact congrArg (fun p : Path (bot R) (bot R) ↦ p t) e
  rw [FundamentalGroup.mul_def]
  change Path.Homotopic.Quotient.trans (.mk ((loop₁ hR).map incl₁.continuous))
    (.mk ((loop₀ hR).map incl₀.continuous)) = Path.Homotopic.Quotient.mk (bigLoop hR)
  rw [h₀, h₁, hb, ← Path.Homotopic.Quotient.mk_trans]
  exact mk_trans_symm_trans _ _ _

/-- **A geometric basis of `π₁(ℂ ∖ {0, 1})` at `1/2 - R i`**: loops `g 0`, `g 1` around `0` and
`1` forming a free basis, with `g 0 * g 1` the circle of radius `R` around `1/2`. -/
theorem exists_basis_bigBase (hR : 1 / 2 < R) :
    ∃ g : Fin 2 → FundamentalGroup X01 (bigBase hR),
      IsLoopAround (g 0) 0 ∧ IsLoopAround (g 1) 1 ∧ Function.Bijective (FreeGroup.lift g) ∧
        g 0 * g 1 = bigArrow hR := by
  classical
  set xb := bigBase hR
  let U : Set X01 := {x | x.1 ∈ P₁}
  let V : Set X01 := {x | x.1 ∈ P₂}
  have hxU : xb ∈ U := show (bot R).re < 2 / 3 by norm_num [bot]
  have hxV : xb ∈ V := show 1 / 3 < (bot R).re by norm_num [bot]
  have hx : xb ∈ U ∩ V := ⟨hxU, hxV⟩
  let φ₀ := pieceHomeomorph notMem_iff_of_mem_P₁
  let φ₁ := pieceHomeomorph notMem_iff_of_mem_P₂
  have hpc₀ : PathConnectedSpace (Region P₁ {0}) :=
    (loopStatement_one P₁ isOpen_P₁ convex_P₁ {0} (by norm_num [P₁]) (by simp)
      ((pieceHomeomorph notMem_iff_of_mem_P₁).symm ⟨xb, hxU⟩)).1
  have hpc₁ : PathConnectedSpace (Region P₂ {1}) :=
    (loopStatement_one P₂ isOpen_P₂ convex_P₂ {1} (by norm_num [P₂]) (by simp)
      ((pieceHomeomorph notMem_iff_of_mem_P₂).symm ⟨xb, hxV⟩)).1
  have hU : IsPathConnected U :=
    isPathConnected_iff_pathConnectedSpace.2 (φ₀.surjective.pathConnectedSpace φ₀.continuous)
  have hV : IsPathConnected V :=
    isPathConnected_iff_pathConnectedSpace.2 (φ₁.surjective.pathConnectedSpace φ₁.continuous)
  have hstrip : IsSimplyConnected (U ∩ V) := by
    rw [← Topology.IsEmbedding.subtypeVal.isSimplyConnected_image]
    have himg : Subtype.val '' (U ∩ V) = P₁ ∩ P₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · rintro ⟨h1, h2⟩
        exact ⟨⟨z, Set.mem_univ _, (notMem_iff_of_mem_P₁ z h1).2 (fun h0 ↦ by
          rw [Finset.mem_singleton] at h0
          rw [h0] at h2
          change 1 / 3 < (0 : ℂ).re at h2
          norm_num at h2)⟩, ⟨h1, h2⟩, rfl⟩
    rw [himg]
    haveI := (convex_P₁.inter convex_P₂).contractibleSpace ⟨xb.1, hxU, hxV⟩
    exact SimplyConnectedSpace.ofContractible _
  have h : VanKampen.Hypotheses U V xb :=
    { isOpen_left := isOpen_P₁.preimage continuous_subtype_val
      isOpen_right := isOpen_P₂.preimage continuous_subtype_val
      union_eq := by
        ext y
        simp only [Set.mem_union, Set.mem_univ, iff_true]
        by_cases hy : y.1.re < 2 / 3
        · exact Or.inl hy
        · exact Or.inr (show 1 / 3 < y.1.re by linarith)
      mem_inter := hx
      isPathConnected_left := hU
      isPathConnected_right := hV
      isPathConnected_inter := hstrip.isPathConnected }
  let ι : Bool → Type := fun b ↦ (cond b ({0} : Finset ℂ) {1} : Finset ℂ)
  let gg : ∀ b, ι b → FundamentalGroup (VanKampen.piece U V b)
      ⟨xb, VanKampen.mem_piece_of_mem_inter h.mem_inter b⟩ := fun b ↦
    match b with
    | true => fun _ ↦ FundamentalGroup.map φ₀.toHomotopyEquiv.toFun _
        (FundamentalGroup.fromPath (.mk (loop₀ hR)))
    | false => fun _ ↦ FundamentalGroup.map φ₁.toHomotopyEquiv.toFun _
        (FundamentalGroup.fromPath (.mk (loop₁ hR)))
  have hG := bijective_lift_vanKampen h hstrip gg fun b ↦ match b with
    | true => bijective_lift_map _ _ (map_bijective_of_homotopyEquiv φ₀.toHomotopyEquiv _)
        (isLoopAround_loop₀ hR).2
    | false => bijective_lift_map _ _ (map_bijective_of_homotopyEquiv φ₁.toHomotopyEquiv _)
        (isLoopAround_loop₁ hR).2
  let G : (Σ b, ι b) → FundamentalGroup X01 xb := fun p ↦
    VanKampen.pieceMap U V h.mem_inter p.1 (gg p.1 p.2)
  let σ : Fin 2 ≃ Σ b, ι b :=
    { toFun := fun i ↦ if i = 0 then ⟨true, ⟨0, by simp⟩⟩ else ⟨false, ⟨1, by simp⟩⟩
      invFun := fun p ↦ cond p.1 0 1
      left_inv := fun i ↦ by fin_cases i <;> rfl
      right_inv := by
        rintro ⟨b, s, hs⟩
        cases b
        · obtain rfl : s = 1 := Finset.mem_singleton.1 hs
          rfl
        · obtain rfl : s = 0 := Finset.mem_singleton.1 hs
          rfl }
  have hg0 : G (σ 0) = FundamentalGroup.map incl₀ _ (FundamentalGroup.fromPath (.mk (loop₀ hR))) :=
    rfl
  have hg1 : G (σ 1) = FundamentalGroup.map incl₁ _ (FundamentalGroup.fromPath (.mk (loop₁ hR))) :=
    rfl
  refine ⟨G ∘ σ, ?_, ?_, bijective_lift_comp_equiv G σ hG, ?_⟩
  · change IsLoopAround (G (σ 0)) 0
    rw [hg0]
    refine (isLoopAround_loop₀ hR).1.map (Set.subset_univ _) (fun s hs hsP ↦ ?_) incl₀
      fun _ ↦ rfl
    by_contra hs0
    exact (notMem_iff_of_mem_P₁ s hsP).2 hs0 hs
  · change IsLoopAround (G (σ 1)) 1
    rw [hg1]
    refine (isLoopAround_loop₁ hR).1.map (Set.subset_univ _) (fun s hs hsP ↦ ?_) incl₁
      fun _ ↦ rfl
    by_contra hs1
    exact (notMem_iff_of_mem_P₂ s hsP).2 hs1 hs
  · change G (σ 0) * G (σ 1) = _
    rw [hg0, hg1]
    exact map_loop₀_mul_map_loop₁ hR

end ZeroOne

end Complex.PuncturedPlane

namespace Complex

open PuncturedPlane PuncturedPlane.ZeroOne in
/-- **A geometric basis of `π₁(ℂ ∖ {0, 1})` whose product is a loop around `∞`**: for every
`R > 1/2` and every base point `x`, there are loops `g 0`, `g 1` around `0` and `1`
(`IsLoopAround`) forming a free basis of `π₁(ℂ ∖ {0, 1}, x)`, such that `g 0 * g 1` (that is,
`g 1` followed by `g 0`) is `δ · B_R · δ⁻¹` for the counterclockwise circle `B_R` of radius `R`
around `1/2` (`PuncturedPlane.ZeroOne.bigArrow`) and a path class `δ` from `x` to its base point
`1/2 - R i`. -/
theorem exists_isLoopAround_basis_zero_one {R : ℝ} (hR : 1 / 2 < R) (x : X01) :
    ∃ g : Fin 2 → FundamentalGroup X01 x,
      IsLoopAround (g 0) 0 ∧ IsLoopAround (g 1) 1 ∧ Function.Bijective (FreeGroup.lift g) ∧
        ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (bigBase hR),
          g 0 * g 1 = δ ≫ bigArrow hR ≫ Groupoid.inv δ := by
  obtain ⟨g, h0, h1, hbij, hmul⟩ := exists_basis_bigBase hR
  haveI : PathConnectedSpace X01 :=
    (loopStatement 2 Set.univ isOpen_univ convex_univ _ (Set.subset_univ _) (by simp) x).1
  let δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (bigBase hR) :=
    ⟦PathConnectedSpace.somePath x (bigBase hR)⟧
  refine ⟨conjArrow δ ∘ g, h0.conj _, h1.conj _,
    bijective_lift_map g (conjArrow δ).toMonoidHom (conjArrow δ).bijective hbij, δ, ?_⟩
  change conjArrow δ (g 0) * conjArrow δ (g 1) = _
  rw [← map_mul, hmul, conjArrow_apply]

open PuncturedPlane PuncturedPlane.ZeroOne in
/-- `exists_isLoopAround_basis_zero_one` as an isomorphism `ψ : π₁(ℂ ∖ {0, 1}, x) ≃* F(S)`,
`S = {0, 1}`, in the form used by `BranchedCover.ker_eq_comap_cuspSubgroup`: `ψ⁻¹(s)` is a loop
around `s`, and `ψ⁻¹(0 · 1)` is conjugate to the circle of radius `R` around `1/2`. -/
theorem exists_mulEquiv_freeGroup_zero_one {R : ℝ} (hR : 1 / 2 < R) (x : X01) :
    ∃ ψ : FundamentalGroup X01 x ≃* FreeGroup ({0, 1} : Finset ℂ),
      (∀ s : ({0, 1} : Finset ℂ), IsLoopAround (ψ.symm (FreeGroup.of s)) s) ∧
        ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (bigBase hR),
          ψ.symm (FreeGroup.of ⟨0, by simp⟩ * FreeGroup.of ⟨1, by simp⟩) =
            δ ≫ bigArrow hR ≫ Groupoid.inv δ := by
  classical
  obtain ⟨g, h0, h1, hbij, δ, hmul⟩ := exists_isLoopAround_basis_zero_one hR x
  let e : Fin 2 ≃ ({0, 1} : Finset ℂ) :=
    { toFun := fun i ↦ if i = 0 then ⟨0, by simp⟩ else ⟨1, by simp⟩
      invFun := fun s ↦ if (s : ℂ) = 0 then 0 else 1
      left_inv := fun i ↦ by fin_cases i <;> simp
      right_inv := by
        rintro ⟨s, hs⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · simp
        · obtain rfl := Finset.mem_singleton.1 hs
          simp }
  let ψ : FundamentalGroup X01 x ≃* FreeGroup ({0, 1} : Finset ℂ) :=
    (MulEquiv.ofBijective _ hbij).symm.trans (FreeGroup.freeGroupCongr e)
  have hψ : ∀ i, ψ.symm (FreeGroup.of (e i)) = g i := fun i ↦ by
    simp [ψ, MulEquiv.ofBijective_apply]
  refine ⟨ψ, fun s ↦ ?_, δ, ?_⟩
  · obtain ⟨i, rfl⟩ := e.surjective s
    rw [hψ]
    fin_cases i
    · exact h0
    · exact h1
  · have e0 : (⟨0, by simp⟩ : ({0, 1} : Finset ℂ)) = e 0 := rfl
    have e1 : (⟨1, by simp⟩ : ({0, 1} : Finset ℂ)) = e 1 := by simp [e]
    rw [map_mul, e0, e1, hψ, hψ, hmul]

end Complex

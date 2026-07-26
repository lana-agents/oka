import Mathlib

/-!
# Analyticity of parametric circle integrals

Work in progress: SCV foundations for the local Weierstrass division theorem.
-/

open Complex

theorem analyticAt_of_differentiableOn {m : ℕ} {f : (Fin m → ℂ) → ℂ}
    {s : Set (Fin m → ℂ)} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s)
    {x₀ : Fin m → ℂ} (hx₀ : x₀ ∈ s) : AnalyticAt ℂ f x₀ :=
  sorry

lemma differentiableOn_cons_slice {m : ℕ} {f : (Fin (m + 1) → ℂ) → ℂ}
    {c : Fin (m + 1) → ℂ} {R : Fin (m + 1) → ℝ}
    (hf : DifferentiableOn ℂ f (Set.univ.pi fun i ↦ Metric.closedBall (c i) (R i)))
    {x : ℂ} (hx : x ∈ Metric.closedBall (c 0) (R 0)) :
    DifferentiableOn ℂ (fun y : Fin m → ℂ ↦ f (Fin.cons x y))
      (Set.univ.pi fun i ↦ Metric.closedBall (c i.succ) (R i.succ)) := by
  have hg : Differentiable ℂ (fun y : Fin m → ℂ ↦ (Fin.cons x y : Fin (m + 1) → ℂ)) := by
    refine differentiable_pi.mpr fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simpa using differentiable_apply (𝕜 := ℂ) j
  refine hf.comp hg.differentiableOn ?_
  intro y hy
  simp only [Set.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using hx
  · simpa using hy j

theorem cauchy_torus_formula {m : ℕ} (f : (Fin m → ℂ) → ℂ) (c : Fin m → ℂ) (R : Fin m → ℝ)
    (hR : ∀ i, 0 < R i)
    (hf : DifferentiableOn ℂ f (Set.univ.pi fun i ↦ Metric.closedBall (c i) (R i)))
    (w : Fin m → ℂ) (hw : ∀ i, w i ∈ Metric.ball (c i) (R i)) :
    f w = (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
      ∯ ζ in T(c, R), (∏ i, (ζ i - w i)⁻¹) • f ζ := by
  induction m with
  | zero =>
    rw [torusIntegral_dim0, Subsingleton.elim w c]
    simp
  | succ m ih =>
    -- tail of w
    set w' : Fin m → ℂ := fun i ↦ w i.succ with hw'
    -- (c) the (m+1)-dimensional integrand is torus-integrable
    have hint : TorusIntegrable (fun ζ ↦ (∏ i, (ζ i - w i)⁻¹) • f ζ) c R := by
      unfold TorusIntegrable
      have hnorm : ∀ (θ : Fin (m + 1) → ℝ) (i), ‖torusMap c R θ i - c i‖ = R i := by
        intro θ i
        simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos (hR i)]
      have htm : Continuous (fun θ : Fin (m + 1) → ℝ ↦ torusMap c R θ) := by
        unfold torusMap; fun_prop
      have hne : ∀ (θ : Fin (m + 1) → ℝ) (i), torusMap c R θ i - w i ≠ 0 := by
        intro θ i hz
        have heq : torusMap c R θ i = w i := sub_eq_zero.mp hz
        have hlt := Metric.mem_ball.mp (hw i)
        rw [Complex.dist_eq, ← heq, hnorm] at hlt
        exact lt_irrefl _ hlt
      have hker : Continuous (fun θ : Fin (m + 1) → ℝ ↦ ∏ i, (torusMap c R θ i - w i)⁻¹) := by
        apply continuous_finsetProd
        intro i _
        exact (((continuous_apply i).comp htm).sub continuous_const).inv₀ (fun θ ↦ hne θ i)
      have hmaps : Set.MapsTo (fun θ : Fin (m + 1) → ℝ ↦ torusMap c R θ)
          (Set.Icc 0 fun _ ↦ 2 * Real.pi)
          (Set.univ.pi fun i ↦ Metric.closedBall (c i) (R i)) := by
        intro θ _
        simp only [Set.mem_pi, Set.mem_univ, true_implies]
        intro i
        simp only [Metric.mem_closedBall, Complex.dist_eq, hnorm, le_refl]
      exact ContinuousOn.integrableOn_compact isCompact_Icc
        (hker.continuousOn.smul (hf.continuousOn.comp htm.continuousOn hmaps))
    -- (d) the Cauchy kernel factors along the first coordinate
    have hker : ∀ (x : ℂ) (y : Fin m → ℂ),
        (∏ i, ((Fin.cons x y : Fin (m + 1) → ℂ) i - w i)⁻¹)
          = (x - w 0)⁻¹ * ∏ i, (y i - w' i)⁻¹ := by
      intro x y
      rw [Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ, hw']
    -- (b-inner) inner torus integral evaluated by ih, for x in the closed disk
    have h2pi : (2 * ↑Real.pi * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hinner : ∀ x ∈ Metric.closedBall (c 0) (R 0),
        (∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ), (∏ i, (y i - w' i)⁻¹) • f (Fin.cons x y))
          = (2 * ↑Real.pi * Complex.I) ^ m • f (Fin.cons x w') := by
      intro x hx
      have hih := ih (fun y ↦ f (Fin.cons x y)) (c ∘ Fin.succ) (R ∘ Fin.succ)
        (fun i ↦ hR i.succ)
        (differentiableOn_cons_slice hf hx)
        w' (fun i ↦ by simpa [hw'] using hw i.succ)
      rw [hih, smul_smul, ← mul_pow, mul_inv_cancel₀ h2pi, one_pow, one_smul]
    -- (b-outer) the outer slice is continuous on the closed disk, holomorphic on the open disk
    have hcons : Differentiable ℂ (fun x : ℂ ↦ (Fin.cons x w' : Fin (m + 1) → ℂ)) := by
      refine differentiable_pi.mpr fun i ↦ ?_
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
      · simp
    have hmaps : ∀ x ∈ Metric.closedBall (c 0) (R 0),
        (Fin.cons x w' : Fin (m + 1) → ℂ) ∈ Set.univ.pi fun i ↦ Metric.closedBall (c i) (R i) := by
      intro x hx i _
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using hx
      · have := hw j.succ
        simp only [hw']
        exact Metric.ball_subset_closedBall this
    have hgcont : ContinuousOn (fun x ↦ f (Fin.cons x w')) (Metric.closedBall (c 0) (R 0)) :=
      hf.continuousOn.comp hcons.continuous.continuousOn hmaps
    have hgdiff : ∀ x ∈ Metric.ball (c 0) (R 0),
        DifferentiableAt ℂ (fun x ↦ f (Fin.cons x w')) x := by
      intro x hx
      have hmem : (Fin.cons x w' : Fin (m + 1) → ℂ)
          ∈ Set.univ.pi fun i ↦ Metric.ball (c i) (R i) := by
        intro i _
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa using hx
        · simpa [hw'] using hw j.succ
      have hnhds : Set.univ.pi (fun i ↦ Metric.closedBall (c i) (R i))
          ∈ nhds (Fin.cons x w' : Fin (m + 1) → ℂ) :=
        Filter.mem_of_superset
          ((isOpen_set_pi Set.finite_univ (fun i _ ↦ Metric.isOpen_ball)).mem_nhds hmem)
          (Set.pi_mono fun i _ ↦ Metric.ball_subset_closedBall)
      exact (hf.differentiableAt hnhds).comp x hcons.differentiableAt
    -- (e) assemble: torusIntegral_succ → kernel split → pull constant → hinner
    --     → 1-var Cauchy on the outer slice → Fin.cons_self_tail → power arithmetic
    have hval : (∯ ζ in T(c, R), (∏ i, (ζ i - w i)⁻¹) • f ζ)
        = (2 * ↑Real.pi * Complex.I) ^ (m + 1) • f w := by
      rw [torusIntegral_succ hint]
      have hEq : Set.EqOn
          (fun x : ℂ ↦ ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
              (∏ i, ((Fin.cons x y : Fin (m + 1) → ℂ) i - w i)⁻¹) • f (Fin.cons x y))
          (fun x ↦ (x - w 0)⁻¹ • ((2 * ↑Real.pi * Complex.I) ^ m • f (Fin.cons x w')))
          (Metric.sphere (c 0) (R 0)) := by
        intro x hx
        dsimp only
        simp only [hker, mul_smul]
        rw [torusIntegral_smul, hinner x (Metric.sphere_subset_closedBall hx)]
      rw [circleIntegral.integral_congr (le_of_lt (hR 0)) hEq,
        show (fun x : ℂ ↦ (x - w 0)⁻¹ • ((2 * ↑Real.pi * Complex.I) ^ m • f (Fin.cons x w')))
            = (fun x ↦ (2 * ↑Real.pi * Complex.I) ^ m • ((x - w 0)⁻¹ • f (Fin.cons x w')))
          from funext fun x ↦ smul_comm _ _ _,
        circleIntegral.integral_smul]
      have hcauchy :=
        two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          (s := (∅ : Set ℂ)) Set.countable_empty (hw 0) hgcont (fun x hx ↦ hgdiff x hx.1)
      have hcw : (Fin.cons (w 0) w' : Fin (m + 1) → ℂ) = w := by
        rw [hw']; exact Fin.cons_self_tail w
      rw [hcw] at hcauchy
      have hJ : (∮ x in C(c 0, R 0), (x - w 0)⁻¹ • f (Fin.cons x w'))
          = (2 * ↑Real.pi * Complex.I) • f w := by
        rw [← hcauchy, smul_smul, mul_inv_cancel₀ h2pi, one_smul]
      rw [hJ, smul_smul, ← pow_succ]
    rw [hval, smul_smul, ← mul_pow, inv_mul_cancel₀ h2pi, one_pow, one_smul]

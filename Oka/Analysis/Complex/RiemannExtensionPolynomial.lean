/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.MetricSpace.Thickening
import Oka.Analytification.GAGA.ParametricIntervalIntegral

/-!
# Riemann extension across the zero set of a polynomial

Let `U ⊆ ℂ^d` be open, `Δ` a nonzero polynomial with zero set `Z(Δ)`, and `f` holomorphic on
`U ∖ Z(Δ)` and locally bounded near every point of `U`. Then `f` extends holomorphically to `U`.

Near `a ∈ U` pick a direction `v` such that `t ↦ Δ (a + t v)` is a nonzero polynomial and a
radius `r` such that it has no zero on the circle `‖t‖ = r`. For `x` near `a` the circle
`s ↦ x + s v` still avoids `Z(Δ)`, and
`F x = (2πi)⁻¹ ∮_{‖s‖ = r} s⁻¹ f (x + s v) ds`
is holomorphic in `x` (holomorphy of parametric integrals). For `x ∉ Z(Δ)`, the function
`s ↦ f (x + s v)` is holomorphic off the finitely many zeros of `s ↦ Δ (x + s v)` and bounded
near them, hence extends across them (one-variable removable singularities), and the Cauchy
integral formula gives `F x = f x`. The local extensions agree on overlaps since `U ∖ Z(Δ)` is
dense in `U`, and glue.

## Main definitions

- `MvPolynomial.restrictLine Δ x v`: the one-variable polynomial `t ↦ Δ (x + t v)`.

## Main results

- `Complex.exists_differentiableOn_eqOn_of_bddAbove`: removable singularities at finitely many
  points in one variable.
- `MvPolynomial.dense_setOf_eval_ne_zero`: the complement of the zero set of a nonzero
  polynomial is dense.
- `MvPolynomial.exists_differentiableOn_eqOn_of_bddAbove`: the Riemann extension theorem across
  `Z(Δ)`.
-/

open Metric Set Filter Topology Complex Real

/-- **Removable singularities at finitely many points.** A function holomorphic on `O ∖ S`
(`O` open, `S` finite) and bounded near each point of `S ∩ O` agrees on `O ∖ S` with a function
holomorphic on `O`. -/
theorem Complex.exists_differentiableOn_eqOn_of_bddAbove {O : Set ℂ} (hO : IsOpen O)
    (S : Finset ℂ) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (O \ S))
    (hb : ∀ c ∈ S, c ∈ O → ∃ V ∈ 𝓝 c, BddAbove (norm ∘ g '' (V \ S))) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G O ∧ EqOn G g (O \ S) := by
  classical
  induction S using Finset.induction_on generalizing g with
  | empty => exact ⟨g, by simpa using hg, fun _ _ ↦ rfl⟩
  | insert c S hcS ih =>
    by_cases hcO : c ∈ O
    · have hO' : IsOpen (O \ (S : Set ℂ)) := hO.sdiff S.finite_toSet.isClosed
      have hOc : IsOpen (O \ ((insert c S : Finset ℂ) : Set ℂ)) :=
        hO.sdiff (insert c S).finite_toSet.isClosed
      have hcO' : c ∈ O \ (S : Set ℂ) := ⟨hcO, by exact_mod_cast hcS⟩
      obtain ⟨V, hV, hVb⟩ := hb c (Finset.mem_insert_self c S) hcO
      obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hO'.mem_nhds hcO'))
      have hsub : ball c δ \ {c} ⊆ O \ ((insert c S : Finset ℂ) : Set ℂ) := by
        rintro y ⟨hy, hyc⟩
        have hy' := hδV hy
        refine ⟨hy'.2.1, ?_⟩
        rw [Finset.coe_insert, mem_insert_iff, not_or]
        exact ⟨hyc, hy'.2.2⟩
      have hsubV : ball c δ \ {c} ⊆ V \ ((insert c S : Finset ℂ) : Set ℂ) :=
        fun y hy ↦ ⟨(hδV hy.1).1, (hsub hy).2⟩
      have hd1 := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds c hδ)
        (hg.mono hsub) (hVb.mono (image_mono hsubV))
      set g' := Function.update g c (limUnder (𝓝[≠] c) g) with hg'_def
      have hg' : DifferentiableOn ℂ g' (O \ S) := by
        intro y hy
        by_cases hyc : y ∈ ball c δ
        · exact (hd1.differentiableAt (isOpen_ball.mem_nhds hyc)).differentiableWithinAt
        · have hyc' : y ≠ c := fun h ↦ hyc (h ▸ mem_ball_self hδ)
          have hmem : y ∈ O \ ((insert c S : Finset ℂ) : Set ℂ) := by
            refine ⟨hy.1, ?_⟩
            rw [Finset.coe_insert, mem_insert_iff, not_or]
            exact ⟨hyc', hy.2⟩
          have hda : DifferentiableAt ℂ g y := hg.differentiableAt (hOc.mem_nhds hmem)
          have heq : g' =ᶠ[𝓝 y] g := by
            filter_upwards [isOpen_compl_singleton.mem_nhds hyc'] with z hz
            exact Function.update_of_ne hz _ _
          exact (hda.congr_of_eventuallyEq heq).differentiableWithinAt
      obtain ⟨G, hG, hGeq⟩ := ih hg' fun c' hc' hc'O ↦ by
        have hne : c' ≠ c := fun h ↦ hcS (h ▸ hc')
        obtain ⟨V', hV', hV'b⟩ := hb c' (Finset.mem_insert_of_mem hc') hc'O
        refine ⟨V' ∩ {c}ᶜ, Filter.inter_mem hV' (isOpen_compl_singleton.mem_nhds hne),
          hV'b.mono ?_⟩
        rintro _ ⟨y, ⟨⟨hyV, hyc⟩, hyS⟩, rfl⟩
        refine ⟨y, ⟨hyV, ?_⟩, ?_⟩
        · rw [Finset.coe_insert, mem_insert_iff, not_or]
          exact ⟨hyc, hyS⟩
        · simp [hg'_def, Function.update_of_ne (show y ≠ c from hyc)]
      refine ⟨G, hG, fun y hy ↦ ?_⟩
      rw [Finset.coe_insert, Set.mem_sdiff, mem_insert_iff, not_or] at hy
      rw [hGeq ⟨hy.1, hy.2.2⟩, hg'_def, Function.update_of_ne hy.2.1]
    · have hOS : O \ ((insert c S : Finset ℂ) : Set ℂ) = O \ S := by
        ext y
        simp only [Finset.coe_insert, Set.mem_sdiff, mem_insert_iff, not_or]
        exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, fun hyc ↦ hcO (hyc ▸ h.1), h.2⟩⟩
      rw [hOS] at hg ⊢
      refine ih hg fun c' hc' hc'O ↦ ?_
      obtain ⟨V', hV', hV'b⟩ := hb c' (Finset.mem_insert_of_mem hc') hc'O
      refine ⟨V' ∩ O, Filter.inter_mem hV' (hO.mem_nhds hc'O), hV'b.mono ?_⟩
      rintro _ ⟨y, ⟨⟨hyV, hyO⟩, hyS⟩, rfl⟩
      refine ⟨y, ⟨hyV, ?_⟩, rfl⟩
      rw [Finset.coe_insert, mem_insert_iff, not_or]
      exact ⟨fun hyc ↦ hcO (hyc ▸ hyO), hyS⟩

/-- A nonzero complex polynomial has no root on the circle `‖t‖ = r` for some `r ∈ (0, r₀)`. -/
theorem Polynomial.exists_pos_lt_forall_norm_eq_eval_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀) : ∃ r, 0 < r ∧ r < r₀ ∧ ∀ t : ℂ, ‖t‖ = r → q.eval t ≠ 0 := by
  classical
  obtain ⟨r, ⟨hr0, hr1⟩, hr⟩ :=
    (Set.Ioo_infinite hr₀).exists_notMem_finset (q.roots.toFinset.image (‖·‖))
  refine ⟨r, hr0, hr1, fun t ht h ↦ hr ?_⟩
  rw [Finset.mem_image]
  exact ⟨t, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr h), ht⟩

namespace MvPolynomial

variable {d : ℕ}

/-- The restriction of `Δ` to the complex line `t ↦ x + t • v`, as a one-variable polynomial. -/
noncomputable def restrictLine (Δ : MvPolynomial (Fin d) ℂ) (x v : Fin d → ℂ) : Polynomial ℂ :=
  aeval (fun i ↦ Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) Δ

theorem eval_restrictLine (Δ : MvPolynomial (Fin d) ℂ) (x v : Fin d → ℂ) (t : ℂ) :
    (Δ.restrictLine x v).eval t = eval (x + t • v) Δ := by
  have h : (fun i ↦ Polynomial.aeval t
      (Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X)) = x + t • v := by
    funext i
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [restrictLine, ← Polynomial.coe_aeval_eq_eval, comp_aeval_apply, h]
  rfl

theorem restrictLine_ne_zero {Δ : MvPolynomial (Fin d) ℂ} {x v : Fin d → ℂ} {t : ℂ}
    (h : eval (x + t • v) Δ ≠ 0) : Δ.restrictLine x v ≠ 0 := by
  intro h0
  apply h
  rw [← eval_restrictLine, h0, Polynomial.eval_zero]

theorem exists_eval_ne_zero {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0) :
    ∃ b, eval b Δ ≠ 0 := by
  by_contra! h
  exact hΔ (MvPolynomial.funext fun x ↦ by simp [h x])

/-- The complement of the zero set of a nonzero polynomial on `ℂ^d` is dense. -/
theorem dense_setOf_eval_ne_zero {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0) :
    Dense {z : Fin d → ℂ | eval z Δ ≠ 0} := by
  obtain ⟨b, hb⟩ := exists_eval_ne_zero hΔ
  rw [Metric.dense_iff]
  intro x ρ hρ
  have hq : Δ.restrictLine x (b - x) ≠ 0 :=
    restrictLine_ne_zero (t := 1) (by simpa using hb)
  obtain ⟨r, hr0, hr, hne⟩ :=
    Polynomial.exists_pos_lt_forall_norm_eq_eval_ne_zero hq (r₀ := ρ / (‖b - x‖ + 1))
      (by positivity)
  refine ⟨x + (r : ℂ) • (b - x), ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hr0.le]
    rw [lt_div_iff₀ (by positivity)] at hr
    nlinarith [norm_nonneg (b - x)]
  · change eval _ Δ ≠ 0
    rw [← eval_restrictLine]
    exact hne _ (by simp [hr0.le])

/-- The local step of the Riemann extension theorem: near each point of `U`, a function that is
holomorphic on `U ∖ Z(Δ)` and locally bounded near `U` agrees off `Z(Δ)` with a holomorphic
function on a ball. -/
theorem exists_ball_differentiableOn_eqOn_of_bddAbove {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0) {f : (Fin d → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (U \ {z | eval z Δ = 0}))
    (hb : ∀ a ∈ U, ∃ V ∈ 𝓝 a, BddAbove (norm ∘ f '' (V \ {z | eval z Δ = 0})))
    {a : Fin d → ℂ} (ha : a ∈ U) :
    ∃ ε > 0, ball a ε ⊆ U ∧ ∃ F : (Fin d → ℂ) → ℂ,
      DifferentiableOn ℂ F (ball a ε) ∧ EqOn F f (ball a ε \ {z | eval z Δ = 0}) := by
  set Z := {z : Fin d → ℂ | eval z Δ = 0} with hZ_def
  have hZ : IsClosed Z := isClosed_eq (MvPolynomial.continuous_eval Δ) continuous_const
  obtain ⟨b, hb0⟩ := exists_eval_ne_zero hΔ
  set v := b - a with hv
  have hq : Δ.restrictLine a v ≠ 0 := restrictLine_ne_zero (t := 1) (by simpa [hv] using hb0)
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU a ha
  obtain ⟨r, hr0, hrδ, hne⟩ :=
    Polynomial.exists_pos_lt_forall_norm_eq_eval_ne_zero hq (r₀ := δ / (‖v‖ + 1))
      (by positivity)
  set φ : ℂ → (Fin d → ℂ) := fun s ↦ a + s • v with hφ_def
  have hφ : Continuous φ := by fun_prop
  have hK1 : φ '' closedBall 0 r ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    apply hδU
    rw [mem_closedBall, dist_zero_right] at hs
    rw [mem_ball, hφ_def, dist_eq_norm, add_sub_cancel_left, norm_smul]
    rw [lt_div_iff₀ (by positivity)] at hrδ
    nlinarith [norm_nonneg v, norm_nonneg s]
  have hK2 : φ '' sphere 0 r ⊆ U \ Z := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨hK1 ⟨s, sphere_subset_closedBall hs, rfl⟩, ?_⟩
    change eval _ Δ ≠ 0
    rw [← eval_restrictLine]
    exact hne s (by simpa using hs)
  obtain ⟨ε₁, hε₁, h1⟩ :=
    ((isCompact_closedBall (0 : ℂ) r).image hφ).exists_thickening_subset_open hU hK1
  obtain ⟨ε₂, hε₂, h2⟩ :=
    ((isCompact_sphere (0 : ℂ) r).image hφ).exists_thickening_subset_open (hU.sdiff hZ) hK2
  set ε := min ε₁ ε₂ with hε
  have hdist : ∀ x ∈ ball a ε, ∀ s : ℂ, dist (x + s • v) (φ s) < ε := by
    intro x hx s
    rw [hφ_def]
    simp only
    rw [dist_add_right]
    exact hx
  have key1 : ∀ x ∈ ball a ε, ∀ s : ℂ, ‖s‖ ≤ r → x + s • v ∈ U := fun x hx s hs ↦
    h1 (mem_thickening_iff.mpr ⟨φ s, mem_image_of_mem _ (by simpa using hs),
      (hdist x hx s).trans_le (min_le_left _ _)⟩)
  have key2 : ∀ x ∈ ball a ε, ∀ s : ℂ, ‖s‖ = r → x + s • v ∈ U \ Z := fun x hx s hs ↦
    h2 (mem_thickening_iff.mpr ⟨φ s, mem_image_of_mem _ (by simpa using hs),
      (hdist x hx s).trans_le (min_le_right _ _)⟩)
  refine ⟨ε, lt_min hε₁ hε₂, fun x hx ↦ by
    simpa using key1 x hx 0 (by simp [hr0.le]), ?_⟩
  refine ⟨fun x ↦ (2 * π * I : ℂ)⁻¹ • ∮ s in C(0, r), s⁻¹ • f (x + s • v), ?_, ?_⟩
  · -- holomorphy of the parametric Cauchy integral
    refine DifferentiableOn.const_smul ?_ _
    have hnorm : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = r := fun θ ↦ by
      simp [norm_circleMap_zero, abs_of_pos hr0]
    simp only [circleIntegral]
    refine differentiableOn_intervalIntegral (G := fun x θ ↦ deriv (circleMap 0 r) θ •
      (circleMap 0 r θ)⁻¹ • f (x + circleMap 0 r θ • v)) isOpen_ball (fun θ _ ↦ ?_) ?_
    · refine DifferentiableOn.const_smul (DifferentiableOn.const_smul ?_ _) _
      exact hf.comp (by fun_prop : Differentiable ℂ fun x ↦ x + circleMap 0 r θ • v)
        |>.differentiableOn fun x hx ↦ key2 x hx _ (hnorm θ)
    · have hc : Continuous fun p : (Fin d → ℂ) × ℝ ↦ circleMap 0 r p.2 :=
        (continuous_circleMap 0 r).comp continuous_snd
      simp only [deriv_circleMap]
      refine ((hc.mul continuous_const).continuousOn).smul
        ((hc.inv₀ fun p ↦ circleMap_ne_center hr0.ne').continuousOn.smul ?_)
      · refine hf.continuousOn.comp (by fun_prop : Continuous fun p : (Fin d → ℂ) × ℝ ↦
          p.1 + circleMap 0 r p.2 • v).continuousOn ?_
        rintro p ⟨hp, -⟩
        exact key2 p.1 hp _ (hnorm p.2)
  · -- the Cauchy integral reproduces `f` off `Z`
    rintro x ⟨hx, hxZ⟩
    set O := {s : ℂ | x + s • v ∈ U} with hO_def
    have hO : IsOpen O := hU.preimage (by fun_prop)
    have hq' : Δ.restrictLine x v ≠ 0 :=
      restrictLine_ne_zero (t := r) (key2 x hx r (by simp [hr0.le])).2
    set S := (Δ.restrictLine x v).roots.toFinset with hS_def
    have hS : ∀ s : ℂ, s ∈ (S : Set ℂ) ↔ x + s • v ∈ Z := by
      intro s
      rw [Finset.mem_coe, hS_def, Multiset.mem_toFinset, Polynomial.mem_roots hq',
        Polynomial.IsRoot.def, eval_restrictLine]
      rfl
    have hg : DifferentiableOn ℂ (fun s : ℂ ↦ f (x + s • v)) (O \ S) :=
      hf.comp (by fun_prop : Differentiable ℂ fun s : ℂ ↦ x + s • v).differentiableOn
        fun s hs ↦ ⟨hs.1, (hS s).not.mp hs.2⟩
    have hgb : ∀ c ∈ S, c ∈ O → ∃ V ∈ 𝓝 c,
        BddAbove (norm ∘ (fun s : ℂ ↦ f (x + s • v)) '' (V \ S)) := by
      intro c _ hcO
      obtain ⟨V, hV, hVb⟩ := hb _ hcO
      refine ⟨(fun s : ℂ ↦ x + s • v) ⁻¹' V,
        (by fun_prop : Continuous fun s : ℂ ↦ x + s • v).continuousAt.preimage_mem_nhds hV,
        hVb.mono ?_⟩
      rintro _ ⟨s, ⟨hsV, hsS⟩, rfl⟩
      exact ⟨x + s • v, ⟨hsV, (hS s).not.mp hsS⟩, rfl⟩
    obtain ⟨G, hG, hGg⟩ := Complex.exists_differentiableOn_eqOn_of_bddAbove hO S hg hgb
    have hball : closedBall (0 : ℂ) r ⊆ O := fun s hs ↦
      key1 x hx s (by simpa using hs)
    have hC := (hG.mono hball).circleIntegral_sub_inv_smul (mem_ball_self hr0)
    have h0 : G 0 = f x := by
      rw [hGg ⟨hball (mem_closedBall_self hr0.le), (hS 0).not.mpr (by simpa using hxZ)⟩]
      simp
    have hcongr : (∮ s in C(0, r), s⁻¹ • f (x + s • v)) = ∮ s in C(0, r), (s - 0)⁻¹ • G s := by
      refine circleIntegral.integral_congr hr0.le fun s hs ↦ ?_
      have hs' : ‖s‖ = r := by simpa using hs
      simp only [sub_zero]
      rw [hGg ⟨hball (sphere_subset_closedBall hs), (hS s).not.mpr (key2 x hx s hs').2⟩]
    simp only
    rw [hcongr, hC, h0, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

/-- **Riemann extension theorem across the zero set of a polynomial.** Let `U ⊆ ℂ^d` be open and
`Δ ≠ 0` a polynomial. A function holomorphic on `U ∖ Z(Δ)` and bounded near every point of `U`
(off `Z(Δ)`) agrees on `U ∖ Z(Δ)` with a function holomorphic on `U`. -/
theorem exists_differentiableOn_eqOn_of_bddAbove {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0) {f : (Fin d → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (U \ {z | eval z Δ = 0}))
    (hb : ∀ a ∈ U, ∃ V ∈ 𝓝 a, BddAbove (norm ∘ f '' (V \ {z | eval z Δ = 0}))) :
    ∃ F : (Fin d → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ EqOn F f (U \ {z | eval z Δ = 0}) := by
  have hloc := fun a (ha : a ∈ U) ↦ exists_ball_differentiableOn_eqOn_of_bddAbove hU hΔ hf hb ha
  choose! ε hε hεU Fl hFl hFlf using hloc
  have hdense := dense_setOf_eval_ne_zero hΔ
  have hcompat : ∀ a ∈ U, ∀ y ∈ U, EqOn (Fl a) (Fl y) (ball a (ε a) ∩ ball y (ε y)) := by
    intro a ha y hy
    have hW : IsOpen (ball a (ε a) ∩ ball y (ε y)) := isOpen_ball.inter isOpen_ball
    refine EqOn.of_subset_closure (s := (ball a (ε a) ∩ ball y (ε y)) ∩
        {z | eval z Δ ≠ 0}) ?_ ((hFl a ha).mono inter_subset_left).continuousOn
      ((hFl y hy).mono inter_subset_right).continuousOn inter_subset_left
      (hdense.open_subset_closure_inter hW)
    rintro z ⟨⟨hza, hzy⟩, hzZ⟩
    rw [hFlf a ha ⟨hza, hzZ⟩, hFlf y hy ⟨hzy, hzZ⟩]
  refine ⟨fun x ↦ Fl x x, fun a ha ↦ ?_, fun x hx ↦ hFlf x hx.1 ⟨mem_ball_self (hε x hx.1), hx.2⟩⟩
  have heq : (fun x ↦ Fl x x) =ᶠ[𝓝 a] Fl a := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hε a ha))] with y hy
    exact (hcompat a ha y (hεU a ha hy) ⟨hy, mem_ball_self (hε y (hεU a ha hy))⟩).symm
  exact (((hFl a ha).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hε a ha)))).congr_of_eventuallyEq
    heq).differentiableWithinAt

end MvPolynomial

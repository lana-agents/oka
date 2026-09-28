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

theorem log_mem_Hr {p : ℂ} (hp : p ∈ Dst t) : Complex.log p ∈ Hr t := by
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp.2
  have hpr : ‖p‖ < r₀ t := mem_ball_zero_iff.mp hp.1
  simp only [Hr, mem_setOf_eq, Complex.log_re]
  exact Real.log_lt_log hp0 hpr

theorem add_int_mem_Hr {s : ℂ} (hs : s ∈ Hr t) (k : ℤ) : s + k * (2 * π * I) ∈ Hr t := by
  simpa [Hr] using hs

/-- **`C` acts nontrivially on `ℍ`.** -/
theorem not_forall_smul_eq_self : ¬ ∀ ν : ℍ, Cm U • ν = ν := by
  intro htriv
  -- `Σ` is `2π i`-periodic
  have hper : ∀ s ∈ Hr t, ∀ k : ℤ, Sig U (s + k * (2 * π * I)) = Sig U s := by
    intro s hs k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have h1 := Sig_add_two_pi U (add_int_mem_Hr hs n)
      rw [htriv] at h1
      rw [← ih, ← h1]; congr 1; push_cast; ring
    | pred n ih =>
      have h1 := Sig_add_two_pi U (add_int_mem_Hr hs (-n - 1))
      rw [htriv] at h1
      rw [← ih, ← h1]; congr 1; push_cast; ring
  set h : ℂ → ℂ := fun p ↦ cayley (Sig U (Complex.log p))
  have hexp : ∀ s ∈ Hr t, h (Complex.exp s) = cayley (Sig U s) := by
    intro s hs
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      (Complex.exp_log (Complex.exp_ne_zero s))
    simp only [h]; rw [hn, hper s hs n]
  have hd : DifferentiableOn ℂ h (Dst t) := by
    intro p hp
    set s₁ := Complex.log p
    have hs₁ := log_mem_Hr hp
    have hps : Complex.exp s₁ = p := Complex.exp_log hp.2
    have hexps : HasStrictDerivAt Complex.exp (Complex.exp s₁) s₁ :=
      Complex.hasStrictDerivAt_exp s₁
    have hne : Complex.exp s₁ ≠ 0 := Complex.exp_ne_zero s₁
    set L := hexps.localInverse Complex.exp (Complex.exp s₁) s₁ hne
    have hL : HasStrictDerivAt L (Complex.exp s₁)⁻¹ (Complex.exp s₁) :=
      hexps.to_localInverse hne
    have hLs : L (Complex.exp s₁) = s₁ := (hexps.eventually_left_inverse hne).self_of_nhds
    have hLc : ContinuousAt L (Complex.exp s₁) := hL.hasDerivAt.continuousAt
    have hev : ∀ᶠ q in 𝓝 (Complex.exp s₁), h q = cayley (Sig U (L q)) := by
      filter_upwards [hexps.eventually_right_inverse hne,
        hLc.preimage_mem_nhds (by rw [hLs]; exact isOpen_Hr.mem_nhds hs₁)] with q hq1 hq2
      rw [← hexp _ hq2, hq1]
    rw [← hps] at hp ⊢
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun s ↦ (Sig U s : ℂ)) (L (Complex.exp s₁)) := by
      rw [hLs]; exact (differentiableOn_Sig U).differentiableAt (isOpen_Hr.mem_nhds hs₁)
    have h2 : DifferentiableAt ℂ cayley ((Sig U (L (Complex.exp s₁)) : ℍ) : ℂ) :=
      differentiableOn_cayley.differentiableAt (isOpen_upper.mem_nhds (Sig U _).im_pos)
    exact h2.comp (Complex.exp s₁) (h1.comp (Complex.exp s₁) hL.hasDerivAt.differentiableAt)
  have hbound : ∀ p, ‖h p‖ < 1 := fun p ↦ mem_ball_zero_iff.mp (cayley_mem_ball (Sig U _).im_pos)
  have hinj : InjOn h (Dst t) := by
    intro p hp q hq hpq
    have h1 : (Sig U (Complex.log p) : ℂ) = Sig U (Complex.log q) := by
      have := congrArg cayleyInv hpq
      simp only [h] at this
      rwa [cayleyInv_cayley (Sig U _).im_pos, cayleyInv_cayley (Sig U _).im_pos] at this
    have h2 := congrArg U.Ψ h1
    change U.ψ (Sig U _) = U.ψ (Sig U _) at h2
    rw [ψ_Sig U (log_mem_Hr hp), ψ_Sig U (log_mem_Hr hq), Complex.exp_log hp.2,
      Complex.exp_log hq.2] at h2
    exact h2
  -- the removable singularity
  set G := Function.update h 0 (limUnder (𝓝[≠] (0 : ℂ)) h)
  have hball : ball (0 : ℂ) (r₀ t) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 r₀_pos
  have hGd : DifferentiableOn ℂ G (ball 0 (r₀ t)) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hd
      ⟨1, by rintro _ ⟨p, -, rfl⟩; exact (hbound p).le⟩
  have hGh : ∀ p ∈ Dst t, G p = h p := fun p hp ↦ Function.update_of_ne hp.2 _ _
  -- `G` is not constant
  have hnc : ¬ ∃ w, ∀ z ∈ ball (0 : ℂ) (r₀ t), G z = w := by
    rintro ⟨w, hw⟩
    have hp : ((r₀ t / 2 : ℝ) : ℂ) ∈ Dst t := ⟨by
      rw [mem_ball_zero_iff]; simp [abs_of_pos r₀_pos]; linarith [r₀_pos (t := t)],
      by simp [r₀_pos.ne']⟩
    have hq : ((r₀ t / 3 : ℝ) : ℂ) ∈ Dst t := ⟨by
      rw [mem_ball_zero_iff]; simp [abs_of_pos r₀_pos]; linarith [r₀_pos (t := t)],
      by simp [r₀_pos.ne']⟩
    have := hinj hp hq (by rw [← hGh _ hp, ← hGh _ hq, hw _ hp.1, hw _ hq.1])
    have := congrArg Complex.re this
    simp at this
    linarith [r₀_pos (t := t)]
  have hopen := ((hGd.analyticOnNhd isOpen_ball).is_constant_or_isOpen
    (convex_ball (0 : ℂ) (r₀ t)).isPreconnected).resolve_left hnc
  have himage : G '' ball 0 (r₀ t) ⊆ closedBall 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hz0 : z = 0
    · subst hz0
      have hGc : ContinuousAt G 0 := (hGd.differentiableAt hball).continuousAt
      have hlim : Tendsto G (𝓝[≠] 0) (𝓝 (G 0)) := hGc.tendsto.mono_left nhdsWithin_le_nhds
      refine isClosed_closedBall.mem_of_tendsto hlim ?_
      filter_upwards [inter_mem_nhdsWithin _ hball] with p hp
      rw [hGh p ⟨hp.2, hp.1⟩]
      exact mem_closedBall_zero_iff.mpr (hbound p).le
    · rw [hGh z ⟨hz, hz0⟩]; exact mem_closedBall_zero_iff.mpr (hbound z).le
  have hG0 : G 0 ∈ ball (0 : ℂ) 1 := by
    have h1 : G '' ball 0 (r₀ t) ⊆ interior (closedBall 0 1) :=
      interior_maximal himage (hopen _ subset_rfl isOpen_ball)
    rw [interior_closedBall _ one_ne_zero] at h1
    exact h1 ⟨0, mem_ball_self r₀_pos, rfl⟩
  -- `Σ (log p)` converges in `ℍ`
  set u : ℂ := cayleyInv (G 0)
  have hu : 0 < u.im := im_cayleyInv_pos hG0
  have hconv : Tendsto (fun p ↦ (Sig U (Complex.log p) : ℂ)) (𝓝[≠] 0) (𝓝 u) := by
    have hGc : ContinuousAt (fun p ↦ cayleyInv (G p)) 0 :=
      (differentiableOn_cayleyInv.continuousOn.continuousAt (isOpen_ball.mem_nhds hG0)).comp
        (hGd.differentiableAt hball).continuousAt
    refine (hGc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [inter_mem_nhdsWithin _ hball] with p hp
    rw [hGh p ⟨hp.2, hp.1⟩]
    exact cayleyInv_cayley (Sig U _).im_pos
  have hΨc : ContinuousAt U.Ψ u :=
    U.differentiableOn.continuousOn.continuousAt (isOpen_upper.mem_nhds hu)
  have hlim1 : Tendsto (fun p ↦ U.Ψ (Sig U (Complex.log p))) (𝓝[≠] 0) (𝓝 (U.Ψ u)) :=
    hΨc.tendsto.comp hconv
  have hlim2 : Tendsto (fun p ↦ U.Ψ (Sig U (Complex.log p))) (𝓝[≠] 0) (𝓝 0) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [inter_mem_nhdsWithin _ hball] with p hp
    change p = U.ψ (Sig U (Complex.log p))
    rw [ψ_Sig U (log_mem_Hr ⟨hp.2, hp.1⟩), Complex.exp_log hp.1]
  have := tendsto_nhds_unique hlim1 hlim2
  exact U.notMem u hu (by rw [this]; exact zero_mem _)

/-- **`C` has no fixed point in `ℍ`.** -/
theorem Cm_smul_ne (ν : ℍ) : Cm U • ν ≠ ν := fun h ↦
  not_forall_smul_eq_self U (U.smul_eq_self_of_fixed (Cm_mem U) h)

/-- **`(tr C)² = 4`.** -/
theorem trace_sq_eq : trSL (Cm U) ^ 2 = 4 := by
  refine le_antisymm (trace_sq_le U) ?_
  by_contra h
  push Not at h
  obtain ⟨ν, hν⟩ := exists_smul_eq_self_of_trace_sq_lt (Cm U) h
  exact Cm_smul_ne U ν hν

/-! ### The sign of the trace -/

theorem A_smul_ne (τ : ℍ) : A U • τ ≠ τ := by
  intro h
  have := ψ_A_smul U τ
  rw [h] at this
  simp at this

theorem trace_sq_A : 4 ≤ trSL (A U) ^ 2 := by
  by_contra h
  push Not at h
  obtain ⟨τ, hτ⟩ := exists_smul_eq_self_of_trace_sq_lt (A U) h
  exact A_smul_ne U τ hτ

theorem trSL_A_ne_zero : trSL (A U) ≠ 0 := by
  intro h
  have := trace_sq_A U
  rw [h] at this; norm_num at this

/-- `ψ` is injective near every point. -/
theorem exists_nhds_injOn (ν : ℍ) : ∃ W ∈ 𝓝 ν, InjOn U.ψ W := by
  obtain ⟨φ, hν, hφ⟩ := U.covering.isLocalHomeomorphOn ν (U.ψ_notMem ν)
  refine ⟨φ.source, φ.open_source.mem_nhds hν, fun a ha b hb hab ↦ φ.injOn ha hb ?_⟩
  rw [← hφ]; exact hab

theorem ψ_conj_smul {X g : SL(2, ℝ)} (hX : X ∈ U.deckGroup) (hg : ∀ ν, U.ψ (g • ν) = U.ψ ν)
    (ν : ℍ) : U.ψ ((X * g * X⁻¹) • ν) = U.ψ ν := by
  obtain ⟨l, -, hl⟩ := hX
  have h1 : U.ψ (X⁻¹ • ν) = U.ψ ν - l := by
    have := hl (X⁻¹ • ν); rw [smul_inv_smul] at this; rw [this]; ring
  rw [mul_smul, mul_smul, hl, hg, h1]; ring

theorem ψ_pow_conj_smul {X : SL(2, ℝ)} (hX : X ∈ U.deckGroup) (n : ℕ) (ν : ℍ) :
    U.ψ ((X ^ n * Cm U * (X ^ n)⁻¹) • ν) = U.ψ ν := by
  induction n generalizing ν with
  | zero => simpa using ψ_Cm_smul U ν
  | succ n ih =>
    have e : X ^ (n + 1) * Cm U * (X ^ (n + 1))⁻¹ = X * (X ^ n * Cm U * (X ^ n)⁻¹) * X⁻¹ := by
      rw [pow_succ', mul_inv_rev]; group
    rw [e]; exact ψ_conj_smul U hX ih ν

/-- The upper unipotent normal form of `C` after conjugation by `M`. -/
def Unipotent (V : SL(2, ℝ)) : Prop := V 1 0 = 0 ∧ V 0 0 = 1 ∧ V 1 1 = 1

/-- **No accumulation**: a deck transformation `X`, upper triangular after conjugation by `M` with
upper left entry of modulus `< 1`, cannot exist when `M⁻¹ C M` is a nontrivial translation. -/
theorem no_accumulation {X M : SL(2, ℝ)} (hX : X ∈ U.deckGroup) (hX0 : (M⁻¹ * X * M) 1 0 = 0)
    (hx : |(M⁻¹ * X * M) 0 0| < 1) (hC : Unipotent (M⁻¹ * Cm U * M))
    (hτ : (M⁻¹ * Cm U * M) 0 1 ≠ 0) : False := by
  set X₀ := M⁻¹ * X * M
  set C₀ := M⁻¹ * Cm U * M
  set x := X₀ 0 0
  set τ := C₀ 0 1
  have hx0 : x ≠ 0 := by
    intro h
    have := det_SL X₀
    rw [hX0, show X₀ 0 0 = x from rfl, h] at this
    simp at this
  have hconj : ∀ n : ℕ, M⁻¹ * (X ^ n * Cm U * (X ^ n)⁻¹) * M = X₀ ^ n * C₀ * (X₀ ^ n)⁻¹ := by
    intro n
    have hpow : X₀ ^ n = M⁻¹ * X ^ n * M := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ih, pow_succ]; simp only [X₀]; group
    rw [hpow]; simp only [C₀]; group
  set ν₀ : ℍ := M • UpperHalfPlane.I
  have hact : ∀ n : ℕ, (X ^ n * Cm U * (X ^ n)⁻¹) • ν₀ =
      M • ((X₀ ^ n * C₀ * (X₀ ^ n)⁻¹) • UpperHalfPlane.I) := by
    intro n
    rw [← hconj n, ← mul_smul, ← mul_smul]
    congr 1
    group
  have hcoe : ∀ n : ℕ, (((X₀ ^ n * C₀ * (X₀ ^ n)⁻¹) • UpperHalfPlane.I : ℍ) : ℂ) =
      I + (x ^ (2 * n) * τ : ℝ) := by
    intro n
    obtain ⟨h1, h2, h3, h4⟩ := pow_conj_unipotent hX0 hC n
    rw [coe_unipotent_smul_I ⟨h1, h2, h3⟩, h4]
  -- convergence
  have hlim0 : Tendsto (fun n : ℕ ↦ x ^ (2 * n) * τ) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ (x ^ 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by
        rw [abs_of_nonneg (sq_nonneg x)]
        nlinarith [abs_nonneg x, sq_abs x, abs_mul_abs_self x])
    have := this.mul_const τ
    simpa [pow_mul] using this
  have hlimH : Tendsto (fun n : ℕ ↦ (X₀ ^ n * C₀ * (X₀ ^ n)⁻¹) • UpperHalfPlane.I) atTop
      (𝓝 UpperHalfPlane.I) := by
    rw [isOpenEmbedding_coe.isInducing.tendsto_nhds_iff]
    simp only [Function.comp_def, hcoe]
    have : Tendsto (fun n : ℕ ↦ I + ((x ^ (2 * n) * τ : ℝ) : ℂ)) atTop (𝓝 (I + ((0 : ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.continuousAt.tendsto.comp hlim0)
    simpa using this
  have hlim : Tendsto (fun n : ℕ ↦ (X ^ n * Cm U * (X ^ n)⁻¹) • ν₀) atTop (𝓝 ν₀) := by
    simp only [hact]
    exact ((continuous_const_smul M).tendsto _).comp hlimH
  obtain ⟨W, hW, hinj⟩ := exists_nhds_injOn U ν₀
  obtain ⟨n, hn⟩ := (hlim.eventually (show W ∈ 𝓝 ν₀ from hW)).exists_forall_of_atTop
  have hmem := hn (n + 1) (by omega)
  have heq := hinj hmem (mem_of_mem_nhds hW) (ψ_pow_conj_smul U hX (n + 1) ν₀)
  rw [hact, smul_left_cancel_iff] at heq
  have := congrArg (fun z : ℍ ↦ (z : ℂ)) heq
  simp only [hcoe, UpperHalfPlane.coe_I] at this
  have h0 : (x ^ (2 * (n + 1)) * τ : ℝ) = 0 := by exact_mod_cast (by simpa using this)
  rcases mul_eq_zero.mp h0 with h | h
  · exact hx0 (pow_eq_zero_iff (by omega) |>.mp h)
  · exact hτ h

end Peripheral

end Uniformization

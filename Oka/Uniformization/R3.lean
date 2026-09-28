/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.Integrality
import Oka.Uniformization.RatFuncPoly
import Oka.Uniformization.R3Count
import Heights.WeierstrassSurjectivity
import Heights.WeierstrassFibers
import Heights.WeierstrassDifferential

/-!
# R3: the commensurator of `Γ̃` is `Γ̃` unless `j ∈ {0, 1728}`

Let `N` be a group with `Γ̃ ≤ N ≤ Comm(Γ̃)` and `[N : Γ̃] < ∞`, where `Γ̃ = pmDeck` is the
`±`-deck group of the uniformisation of `ℂ/Λ ∖ {0}` and `F = ℘ ∘ ψ`.

1. The `N`-invariant polynomials `R_N = {p | p ∘ F is N-invariant}` form a subalgebra of `ℂ[X]`
   containing the coefficients of `∏_{q ∈ N/Γ̃} (X - F ∘ q⁻¹)`; these are not all constant.
2. By Lüroth, `R_N ⊆ ℂ[s]` for a non-constant polynomial `s` with `s ∘ F` `N`-invariant; the
   fibres of `s ∘ F` are the `N`-orbits.
3. Local orders: at `τ` over `w = F τ`, `s ∘ F - s(w)` vanishes to order `e_s(w) m(w)` with
   `m(w) = 2` iff `w` is a root of `4X³ - g₂X - g₃`; this order is `N`-invariant.
4. The orbifold Riemann–Hurwitz count (`RatFuncPoly.orbifold_count`) gives `deg s = 1`, or
   `g₃ = 0`, or `g₂ = 0`; if `deg s = 1`, `F` is `N`-invariant and `N = Γ̃`.
-/

open Complex Metric Set Filter Topology Polynomial
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Pointwise

namespace Uniformization

namespace Unif

variable {L : PeriodPair} {U : Unif L}

/-- Holomorphic functions on `ℍ` form a domain. -/
theorem HolH.eq_zero_of_mul {F G : ℍ → ℂ} (hF : HolH F) (hG : HolH G)
    (h : ∀ τ, F τ * G τ = 0) {τ₀ : ℍ} (hG0 : G τ₀ ≠ 0) (τ : ℍ) : F τ = 0 := by
  set F' : ℂ → ℂ := fun z ↦ F (ofComplex z)
  set G' : ℂ → ℂ := fun z ↦ G (ofComplex z)
  have hFa : AnalyticOnNhd ℂ F' {z | 0 < z.im} := hF.analyticOnNhd isOpen_upper
  have hG'c : ContinuousAt G' τ₀ :=
    (hG.continuousOn.continuousAt (isOpen_upper.mem_nhds τ₀.im_pos))
  have hG'0 : G' τ₀ ≠ 0 := by simp only [G', ofComplex_apply]; exact hG0
  have hev : F' =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hG'c.eventually_ne hG'0, isOpen_upper.mem_nhds τ₀.im_pos] with z hz hzi
    have := h (ofComplex z)
    exact (mul_eq_zero.mp this).resolve_right hz
  have := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hev (τ.im_pos)
  simpa [F', ofComplex_apply] using this

end Unif

namespace Peripheral

open Generators

variable {t : ℍ} {U : Unif (Lt t)}

theorem wpΨ_surjective (U : Unif (Lt t)) : Function.Surjective (wpΨ U) := by
  intro w
  obtain ⟨z, hz, hzw⟩ := Heights.exists_notMem_lattice_weierstrassP_eq (Lt t) w
  obtain ⟨τ, hτ⟩ := U.surj z hz
  exact ⟨τ, by rw [wpΨ, Unif.ψ, hτ, hzw]⟩

/-- The fibres of `℘ ∘ ψ` are the `Γ̃`-orbits. -/
theorem exists_mem_pmDeck_of_wpΨ_eq {τ₁ τ₂ : ℍ} (h : wpΨ U τ₁ = wpΨ U τ₂) :
    ∃ γ ∈ U.pmDeck, γ • τ₁ = τ₂ := by
  rcases (Heights.weierstrassP_eq_iff_sub_mem_or_add_mem (Lt t) (U.ψ τ₂) (U.ψ τ₁)
    (U.ψ_notMem τ₂) (U.ψ_notMem τ₁)).mp h.symm with h1 | h1
  · obtain ⟨γ, hγψ, hγ⟩ := U.exists_mem_pmDeck (ε := 1) (Or.inl rfl) (τ := τ₁) (τ' := τ₂)
      (by simpa using h1)
    exact ⟨γ, U.mem_pmDeck_of (Or.inl rfl) (by simpa using h1) hγψ, hγ⟩
  · obtain ⟨γ, hγψ, hγ⟩ := U.exists_mem_pmDeck (ε := -1) (Or.inr rfl) (τ := τ₁) (τ' := τ₂)
      (by simpa using h1)
    exact ⟨γ, U.mem_pmDeck_of (Or.inr rfl) (by simpa using h1) hγψ, hγ⟩

theorem holH_poly_wpΨ (U : Unif (Lt t)) (p : ℂ[X]) : Unif.HolH fun τ ↦ p.eval (wpΨ U τ) := by
  have h := Unif.holH_weierstrassP_ψ U
  exact (Polynomial.differentiable p).comp_differentiableOn h

section Comm

variable (U) in
/-- The polynomials `p` with `p ∘ ℘ ∘ ψ` invariant under `N`. -/
def invPoly (N : Subgroup SL(2, ℝ)) : Subalgebra ℂ ℂ[X] where
  carrier := {p | ∀ n ∈ N, ∀ τ, p.eval (wpΨ U (n • τ)) = p.eval (wpΨ U τ)}
  mul_mem' {p q} hp hq n hn τ := by simp only [eval_mul, hp n hn τ, hq n hn τ]
  add_mem' {p q} hp hq n hn τ := by simp only [eval_add, hp n hn τ, hq n hn τ]
  algebraMap_mem' c n _ τ := by simp

variable {N : Subgroup SL(2, ℝ)}

theorem mem_invPoly {p : ℂ[X]} :
    p ∈ invPoly U N ↔ ∀ n ∈ N, ∀ τ, p.eval (wpΨ U (n • τ)) = p.eval (wpΨ U τ) := Iff.rfl

/-- **The coset polynomial** `∏_{q ∈ N/Γ̃} (X - F ∘ q⁻¹)`: its coefficients are polynomials in `F`
lying in `R_N`. -/
theorem exists_cosetPoly (hΓN : U.pmDeck ≤ N)
    (hNC : N ≤ Subgroup.Commensurable.commensurator U.pmDeck)
    (hfin : U.pmDeck.relIndex N ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → SL(2, ℝ)) (p : ℕ → ℂ[X]),
      (∀ i, g i ∈ N) ∧ (∀ k, p k ∈ invPoly U N) ∧
      (∀ τ k, (∏ i, (X - C (wpΨ U (g i • τ)))).coeff k = (p k).eval (wpΨ U τ)) ∧
      ∃ i₀, ∀ τ, wpΨ U (g i₀ • τ) = wpΨ U τ := by
  classical
  set Γ := U.pmDeck
  haveI : (Γ.subgroupOf N).FiniteIndex := ⟨hfin⟩
  haveI : Finite (N ⧸ Γ.subgroupOf N) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (N ⧸ Γ.subgroupOf N)
  have hinvΓ : ∀ γ ∈ Γ, ∀ τ, wpΨ U (γ • τ) = wpΨ U τ := fun γ hγ τ ↦ U.wp_ψ_smul_pm hγ τ
  let g : N ⧸ Γ.subgroupOf N → SL(2, ℝ) := fun q ↦ ((q.out : N) : SL(2, ℝ))⁻¹
  let f : N ⧸ Γ.subgroupOf N → ℍ → ℂ := fun q τ ↦ wpΨ U (g q • τ)
  have hf : ∀ x : N, ∀ τ, f (QuotientGroup.mk x) τ = wpΨ U (((x : SL(2, ℝ)))⁻¹ • τ) := by
    intro x τ
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Γ.subgroupOf N) x
    have hmem : ((h : N) : SL(2, ℝ)) ∈ Γ := Subgroup.mem_subgroupOf.mp h.2
    simp only [f, g, hh, Subgroup.coe_mul, mul_inv_rev, mul_smul]
    exact hinvΓ _ (Γ.inv_mem hmem) _
  set P₀ : ℍ → ℂ[X] := fun τ ↦ ∏ q, (X - C (f q τ))
  have hP₀inv : ∀ m ∈ N, ∀ τ, P₀ (m • τ) = P₀ τ := by
    intro m hm τ
    set m' : N := ⟨m, hm⟩
    have hfq : ∀ q, f q (m • τ) = f (m'⁻¹ • q) τ := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAction.Quotient.smul_mk, hf, hf, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        mul_inv_rev, inv_inv, mul_smul]
    simp only [P₀, hfq]
    exact Fintype.prod_equiv (MulAction.toPerm m'⁻¹) _ _ fun q ↦ rfl
  have hσ : ∀ q, g q ∈ Subgroup.Commensurable.commensurator Γ := fun q ↦
    Subgroup.inv_mem _ (hNC (q.out : N).2)
  choose Cq Nq hq using fun q ↦ exists_poly_bound_smul (U := U) (hσ q)
  have hcoeff : ∀ k : ℕ, ∃ p : ℂ[X], ∀ τ, (P₀ τ).coeff k = p.eval (wpΨ U τ) := by
    intro k
    refine eq_poly_of_bound (U := U) (fun γ hγ τ ↦ by rw [hP₀inv γ (hΓN hγ) τ]) ?_
      (C := ∏ q, (1 + |Cq q|)) (N := ∑ q, Nq q) fun τ ↦ ?_
    · refine differentiableOn_coeff_prod_X_sub_C Finset.univ
        (a := fun q z ↦ f q (ofComplex z)) (fun q _ ↦ ?_) k
      exact (Unif.holH_weierstrassP_ψ U).comp_smul _
    · set w := ‖wpΨ U τ‖
      have hw1 : 1 ≤ 2 + w := by linarith [norm_nonneg (wpΨ U τ)]
      refine (norm_coeff_prod_X_sub_C_le _ _ k).trans ?_
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun q _ ↦ by positivity) fun q _ ↦ ?_
      have h1 : 1 ≤ (2 + w) ^ Nq q := one_le_pow₀ hw1
      have h2 := hq q τ
      have h3 : Cq q * (2 + w) ^ Nq q ≤ |Cq q| * (2 + w) ^ Nq q :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      change 1 + ‖wpΨ U (g q • τ)‖ ≤ _
      nlinarith
  choose p hp using hcoeff
  refine ⟨N ⧸ Γ.subgroupOf N, inferInstance, g, p, fun q ↦ inv_mem (q.out : N).2,
    fun k n hn τ ↦ ?_, fun τ k ↦ hp k τ, QuotientGroup.mk 1, fun τ ↦ ?_⟩
  · rw [← hp, ← hp, hP₀inv n hn]
  · change f _ τ = _
    rw [hf, Subgroup.coe_one, inv_one, one_smul]

/-- **The generator**: a non-constant polynomial `s` with `s ∘ F` `N`-invariant, whose fibres are
the `N`-orbits. -/
theorem exists_generator (hΓN : U.pmDeck ≤ N)
    (hNC : N ≤ Subgroup.Commensurable.commensurator U.pmDeck)
    (hfin : U.pmDeck.relIndex N ≠ 0) :
    ∃ s : ℂ[X], 0 < s.natDegree ∧
      (∀ n ∈ N, ∀ τ, s.eval (wpΨ U (n • τ)) = s.eval (wpΨ U τ)) ∧
      ∀ τ τ', s.eval (wpΨ U τ) = s.eval (wpΨ U τ') → ∃ n ∈ N, n • τ = τ' := by
  classical
  obtain ⟨ι, _, g, p, hgN, hpN, hcoef, i₀, hi₀⟩ := exists_cosetPoly hΓN hNC hfin
  set P : ℍ → ℂ[X] := fun τ ↦ ∏ i, (X - C (wpΨ U (g i • τ)))
  have hP0 : ∀ τ, P τ ≠ 0 := fun τ ↦ (monic_prod_X_sub_C _ _).ne_zero
  have hroot : ∀ τ, (P τ).eval (wpΨ U τ) = 0 := fun τ ↦ by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hi₀, sub_self])
  -- some coefficient is non-constant
  have hnc : ∃ k, 0 < (p k).natDegree := by
    by_contra hcon
    push Not at hcon
    have hconst : ∀ τ τ', P τ = P τ' := fun τ τ' ↦ by
      ext k
      rw [hcoef, hcoef, eq_C_of_natDegree_le_zero (hcon k), eval_C, eval_C]
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (P UpperHalfPlane.I).roots.toFinset
    obtain ⟨τ, hτ⟩ := wpΨ_surjective U w
    apply hw
    rw [Multiset.mem_toFinset, mem_roots (hP0 _), IsRoot, ← hτ, hconst _ τ]
    exact hroot τ
  obtain ⟨k, hk⟩ := hnc
  obtain ⟨s, hs, ⟨r, hr, q, hq, hq0, hsq⟩, hcomp⟩ :=
    RatFuncPoly.exists_poly_generator (invPoly U N) ⟨p k, hpN k, hk⟩
  refine ⟨s, hs, fun n hn τ ↦ ?_, fun τ τ' hττ' ↦ ?_⟩
  · -- invariance
    have hmul : ∀ σ, (s.eval (wpΨ U (n • σ)) - s.eval (wpΨ U σ)) * q.eval (wpΨ U σ) = 0 := by
      intro σ
      have h1 := congrArg (eval (wpΨ U (n • σ))) hsq
      have h2 := congrArg (eval (wpΨ U σ)) hsq
      rw [eval_mul] at h1 h2
      linear_combination h1 - h2 + hr n hn σ - s.eval (wpΨ U (n • σ)) * hq n hn σ
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset q.roots.toFinset
    obtain ⟨σ₀, hσ₀⟩ := wpΨ_surjective U w
    have hne : q.eval (wpΨ U σ₀) ≠ 0 := by
      intro h0
      apply hw
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, ← hσ₀, h0]
    have hF : Unif.HolH fun σ ↦ s.eval (wpΨ U (n • σ)) - s.eval (wpΨ U σ) :=
      DifferentiableOn.sub ((holH_poly_wpΨ U s).comp_smul n) (holH_poly_wpΨ U s)
    exact sub_eq_zero.mp (Unif.HolH.eq_zero_of_mul hF (holH_poly_wpΨ U q) hmul hne τ)
  · -- transitivity
    have hPeq : P τ = P τ' := by
      ext j
      obtain ⟨A, hA⟩ := hcomp (p j) (hpN j)
      rw [hcoef, hcoef, hA, eval_comp, eval_comp, hττ']
    have h1 := hroot τ'
    rw [← hPeq] at h1
    simp only [P, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, sub_eq_zero] at h1
    obtain ⟨i, hi⟩ := h1
    obtain ⟨γ, hγ, hγτ⟩ := exists_mem_pmDeck_of_wpΨ_eq hi.symm
    exact ⟨γ * g i, N.mul_mem (hΓN hγ) (hgN i), by rw [mul_smul, hγτ]⟩

end Comm

end Peripheral

end Uniformization

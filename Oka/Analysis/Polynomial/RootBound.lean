/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Oka.Topology.Algebra.Polynomial

/-!
# Root bounds for monic polynomials and for families with polynomial coefficients

Complements to `Polynomial.IsRoot.norm_le_monicRootBound` (every root `t` of a monic
`T^n + a₁ T^{n-1} + ⋯ + a_n` satisfies `‖t‖ ≤ 1 + ∑ ‖a_i‖`):

* over an algebraically closed normed field, a monic polynomial of positive degree `n` has a root
  `t` with `‖t‖ ^ n ≤ ‖a_n‖` (the constant coefficient), since `a_n` is up to sign the product of
  the roots;
* for a monic `μ ∈ (MvPolynomial ι K)[T]` the roots of the specialisations `μ_z` grow at most
  polynomially in `z`, are bounded over bounded sets of parameters, and the projection of the
  zero locus `{(z, t) | μ_z(t) = 0}` to the parameters is proper.

## Main results

- `Polynomial.exists_isRoot_norm_pow_le_norm_coeff_zero`
- `MvPolynomial.norm_eval_le_mul_one_add_pow`
- `Polynomial.exists_norm_le_mul_one_add_pow_of_isRoot_map_eval`
- `Polynomial.isBounded_setOf_isRoot_map_eval`
- `Polynomial.isProperMap_fst_zeroLocus_map_eval`
-/

open Finset Metric

namespace Polynomial

/-- A monic polynomial of positive degree `n` over an algebraically closed normed field has a
root `t` with `‖t‖ ^ n ≤ ‖a_0‖`, where `a_0` is the constant coefficient: the root of smallest
norm, as `a_0 = ± ∏ roots`. -/
theorem exists_isRoot_norm_pow_le_norm_coeff_zero {K : Type*} [NormedField K] [IsAlgClosed K]
    {q : K[X]} (hm : q.Monic) (hd : 0 < q.natDegree) :
    ∃ t, q.IsRoot t ∧ ‖t‖ ^ q.natDegree ≤ ‖q.coeff 0‖ := by
  classical
  have hcard : Multiset.card q.roots = q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hne : q.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  obtain ⟨t, ht, hmin⟩ := q.roots.toFinset.exists_min_image (‖·‖) hne
  rw [Multiset.mem_toFinset] at ht
  refine ⟨t, (mem_roots hm.ne_zero).1 ht, ?_⟩
  rw [(IsAlgClosed.splits q).coeff_zero_eq_prod_roots_of_monic hm, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul]
  have hprod : ‖q.roots.prod‖ = (q.roots.map (‖·‖)).prod :=
    map_multiset_prod (normHom : K →*₀ ℝ) q.roots
  rw [hprod]
  have h := Multiset.prod_map_le_prod_map₀ (s := q.roots) (fun _ ↦ ‖t‖) (fun a ↦ ‖a‖)
    (fun _ _ ↦ norm_nonneg _) (fun a ha ↦ hmin a (Multiset.mem_toFinset.2 ha))
  simpa [hcard] using h

end Polynomial

namespace MvPolynomial

variable {ι K : Type*} [Fintype ι] [NormedField K]

/-- A polynomial function on `ι → K` (sup norm) grows at most like `(1 + ‖z‖) ^ totalDegree`. -/
theorem norm_eval_le_mul_one_add_pow (q : MvPolynomial ι K) (z : ι → K) :
    ‖eval z q‖ ≤ (∑ m ∈ q.support, ‖coeff m q‖) * (1 + ‖z‖) ^ q.totalDegree := by
  rw [eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  rw [norm_mul, norm_prod]
  gcongr
  have h1 : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg _)
  calc ∏ i, ‖z i ^ m i‖ ≤ ∏ i, (1 + ‖z‖) ^ m i := by
        gcongr with i
        rw [norm_pow]
        gcongr
        exact (norm_le_pi_norm z i).trans (le_add_of_nonneg_left zero_le_one)
    _ = (1 + ‖z‖) ^ ∑ i, m i := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (1 + ‖z‖) ^ q.totalDegree := by
        refine pow_le_pow_right₀ h1 ?_
        rw [← Finsupp.sum_fintype m (fun _ e ↦ e) (fun _ ↦ rfl)]
        exact le_totalDegree hm

end MvPolynomial

namespace Polynomial

variable {ι K : Type*} [Fintype ι] [NormedField K]

/-- **Polynomial growth of the roots** of a monic polynomial with polynomial coefficients: there
are `C, N` with `‖t‖ ≤ C (1 + ‖z‖) ^ N` whenever `μ_z(t) = 0`. -/
theorem exists_norm_le_mul_one_add_pow_of_isRoot_map_eval {μ : (MvPolynomial ι K)[X]}
    (hm : μ.Monic) : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ z t, (μ.map (MvPolynomial.eval z)).IsRoot t → ‖t‖ ≤ C * (1 + ‖z‖) ^ N := by
  set d := μ.natDegree
  let C i := ∑ m ∈ (μ.coeff i).support, ‖MvPolynomial.coeff m (μ.coeff i)‖
  let N := ∑ i ∈ range d, (μ.coeff i).totalDegree
  refine ⟨(∑ i ∈ range d, C i) + 1, N, by positivity, fun z t ht ↦ ?_⟩
  have hmz : (μ.map (MvPolynomial.eval z)).Monic := hm.map _
  have hdz : (μ.map (MvPolynomial.eval z)).natDegree = d := hm.natDegree_map _
  have h := IsRoot.norm_le_monicRootBound hmz hdz ht
  have h1 : 1 ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg _)
  refine h.trans ?_
  rw [monicRootBound, add_mul, one_mul, Finset.sum_mul]
  gcongr with i hi
  · rw [coeff_map]
    refine (MvPolynomial.norm_eval_le_mul_one_add_pow _ z).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 ?_) (by positivity)
    exact Finset.single_le_sum (f := fun i ↦ (μ.coeff i).totalDegree)
      (fun _ _ ↦ Nat.zero_le _) hi
  · exact one_le_pow₀ h1

/-- The roots of `μ_z`, `z` ranging over a bounded set of parameters, form a bounded set. -/
theorem isBounded_setOf_isRoot_map_eval {μ : (MvPolynomial ι K)[X]} (hm : μ.Monic)
    {S : Set (ι → K)} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded {t | ∃ z ∈ S, (μ.map (MvPolynomial.eval z)).IsRoot t} := by
  obtain ⟨C, N, hC0, hC⟩ := exists_norm_le_mul_one_add_pow_of_isRoot_map_eval hm
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  refine (isBounded_iff_forall_norm_le).2 ⟨C * (1 + max R 0) ^ N, ?_⟩
  rintro t ⟨z, hz, ht⟩
  refine (hC z t ht).trans ?_
  have hz' : ‖z‖ ≤ max R 0 := (mem_closedBall_zero_iff.1 (hR hz)).trans (le_max_left _ _)
  gcongr

omit [Fintype ι] in
/-- The projection `{(z, t) | μ_z(t) = 0} → ι → K` is proper for monic `μ`. -/
theorem isProperMap_fst_zeroLocus_map_eval [ProperSpace K] {μ : (MvPolynomial ι K)[X]}
    (hm : μ.Monic) :
    IsProperMap fun q : {q : (ι → K) × K // (μ.map (MvPolynomial.eval q.1)).eval q.2 = 0} ↦
      (q : (ι → K) × K).1 :=
  isProperMap_fst_zeroLocus (p := fun z ↦ μ.map (MvPolynomial.eval z)) (fun _ ↦ hm.map _)
    (fun _ ↦ hm.natDegree_map _) fun i ↦ by
      simp only [coeff_map]
      exact MvPolynomial.continuous_eval _

end Polynomial

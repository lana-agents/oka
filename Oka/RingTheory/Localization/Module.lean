/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Localization.Integer

/-!
# Relations between elements of a ring localise

Material for `Mathlib/RingTheory/Localization/Module.lean`; see `README.md` on the mirror tree.
Nothing here is complex-analytic.

Let `S` be a localisation of `R` at a submonoid `M`, let `f : ι → R` be a finite family, and let
`g : κ → (ι → R)` be a finite family of relations between the `f i` which generates *all* of
them, in the sense that every `b` with `∑ i, b i * f i = 0` lies in the `R`-span of the `g l`.
Then the images of the `g l` generate the relations between the images of the `f i` over `S`.

The proof is clearing denominators twice and is the reason no flatness is needed: given a
relation `a` over `S`, one `M`-multiple of it comes from `R`
(`IsLocalization.exist_integer_multiples`), a second `M`-multiple makes the resulting family an
honest relation over `R` (`IsLocalization.map_eq_zero_iff`), and both multipliers become units
in `S`.

## Import cost

Both imports above — `Mathlib.LinearAlgebra.Finsupp.LinearCombination` and
`Mathlib.RingTheory.Localization.Integer` — are already in the transitive closure of
`Mathlib/RingTheory/Localization/Module.lean`, so upstreaming this file adds **0 files** to it.
Measured by breadth-first search over `(public )?import` in `.lake/packages/mathlib`, against the
**total** closure of the Mathlib target rather than a marginal baseline: 1460 modules before and
1460 after. The same instrument reproduces the two figures already recorded elsewhere in this
tree — `Mathlib.RingTheory.Localization.Finiteness` costs
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` 2, and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` costs
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` 3.

## Main results

- `IsLocalization.exists_fun_eq_sum_of_sum_mul_eq_zero`: a relation over the localisation is a
  combination of the images of generating relations over the base.
-/

open scoped BigOperators

namespace IsLocalization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Generating relations stay generating in a localisation.**

If every `R`-relation between the `f i` is an `R`-combination of the `g l`, then every
`S`-relation between the images of the `f i` is an `S`-combination of the images of the `g l`,
for `S` a localisation of `R`.

Note that neither `f` nor `g` is assumed to have any property beyond finiteness of the index
types: the hypothesis `hgen` is the only thing that ties them together, and it is exactly what
noetherianity of `R` supplies for a suitable finite `g`. -/
theorem exists_fun_eq_sum_of_sum_mul_eq_zero (M : Submonoid R) [IsLocalization M S]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → R) (g : κ → (ι → R))
    (hgen : ∀ b : ι → R, ∑ i, b i * f i = 0 → b ∈ Submodule.span R (Set.range g))
    (a : ι → S) (ha : ∑ i, a i * algebraMap R S (f i) = 0) :
    ∃ c : κ → S, ∀ i, a i = ∑ l, c l * algebraMap R S (g l i) := by
  classical
  -- one `M`-multiple of `a` comes from `R`
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ a
  choose b' hb' using fun i ↦ hb i (Finset.mem_univ i)
  -- the resulting combination of the `f i` dies in `S` …
  have hzero : algebraMap R S (∑ i, b' i * f i) = 0 := by
    rw [map_sum]
    have h : ∀ i, algebraMap R S (b' i * f i) = (b : R) • (a i * algebraMap R S (f i)) := by
      intro i
      rw [map_mul, hb' i, smul_mul_assoc]
    simp_rw [h, ← Finset.smul_sum, ha, smul_zero]
  -- … hence is killed by a second element of `M`
  obtain ⟨u, hu⟩ := (map_eq_zero_iff M S _).1 hzero
  have hrel : ∑ i, ((u : R) * b' i) * f i = 0 := by
    rw [← hu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hgen _ hrel)
  -- both multipliers are units downstairs, so they can be divided out
  have hunit : IsUnit (algebraMap R S ((u : R) * (b : R))) := by
    rw [map_mul]
    exact (map_units S u).mul (map_units S b)
  refine ⟨fun l ↦ ↑hunit.unit⁻¹ * algebraMap R S (d l), fun i ↦ ?_⟩
  have key : algebraMap R S ((u : R) * (b : R)) * a i =
      ∑ l, algebraMap R S (d l) * algebraMap R S (g l i) := by
    have h := congrFun hd i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    calc algebraMap R S ((u : R) * (b : R)) * a i
        = algebraMap R S (u : R) * ((b : R) • a i) := by
          rw [map_mul, Algebra.smul_def]; ring
      _ = algebraMap R S ((u : R) * b' i) := by rw [← hb' i, map_mul]
      _ = algebraMap R S (∑ l, d l * g l i) := by rw [h]
      _ = ∑ l, algebraMap R S (d l) * algebraMap R S (g l i) := by
          rw [map_sum]; exact Finset.sum_congr rfl fun l _ ↦ map_mul _ _ _
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) ↦ mul_assoc (↑hunit.unit⁻¹ : S)
    (algebraMap R S (d l)) (algebraMap R S (g l i)), ← Finset.mul_sum, ← key,
    ← mul_assoc, IsUnit.val_inv_mul, one_mul]

end IsLocalization

/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.Covering.Monodromy
import Oka.Topology.Covering.Stabilizer
import Pi1.Surface.SchreierCusps

/-!
# Finite coverings of spaces with free fundamental group

Let `p : E → X` be a covering map with `E` path connected and `π₁(X, x) ≅ F(α)` free. Transporting
the monodromy action along the isomorphism (an action of `F(α)` on the fibre with `g • e =
monodromy (φ⁻¹ g) e`, e.g. `MulAction.compHom`), `π₁(E, e)` is the stabiliser of `e` for this
action of `F(α)` on the fibre (`IsCoveringMap.fundamentalGroupEquivStabilizer`), transitive
because `E` is path connected (`IsCoveringMap.exists_monodromy_eq`). The Reidemeister–Schreier
theorem (pi1 `Pi1.ReidemeisterSchreier.Transversal.basis`) then gives:

* `IsCoveringMap.exists_fundamentalGroup_mulEquiv_freeGroup`: for a fibre with `d` points and
  `α` finite, `π₁(E, e)` is free of rank `d (|α| - 1) + 1` (Schreier's index formula);
* `IsCoveringMap.exists_quotient_mulEquiv_freeGroup`: for a finite set `A ⊆ α` of letters, the
  quotient of `π₁(E, e)` by the normal closure of the lifts of conjugates of powers of the loops
  in `A` is free of rank `d (|α| - 1) + 1 - ∑_{a ∈ A} #(⟨a⟩-orbits on the fibre)`.

For `X = ℂ ∖ {0, 1}` with the free basis of loops around `0` and `1`
(`Complex.exists_isLoopAround_basis`), the second statement is the computation of `π₁` of the
affine curve obtained from a finite covering of `ℂ ∖ {0, 1}` by filling in the punctures over
`0` and `1`, once filling a puncture is known to kill exactly its local loop.
-/

open Pi1.ReidemeisterSchreier

namespace IsCoveringMap

universe u v w

variable {E : Type v} {X : Type w} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p) {x : X} {α : Type u} (φ : FundamentalGroup X x ≃* FreeGroup α)

section

variable [MulAction (FreeGroup α) (p ⁻¹' {x})]
  (hφ : ∀ (g : FreeGroup α) (e : p ⁻¹' {x}), g • e = cov.monodromy (φ.symm g) e)
include hφ

theorem map_monodromyStabilizer (e : p ⁻¹' {x}) :
    (cov.monodromyStabilizer e).map φ.toMonoidHom = MulAction.stabilizer (FreeGroup α) e := by
  ext g
  rw [Subgroup.mem_map_equiv]
  change cov.monodromy (φ.symm g) e = e ↔ g • e = e
  rw [hφ]

/-- `π₁(E, e)` as the stabiliser of `e` in the free group. -/
noncomputable def fundamentalGroupEquivFreeStabilizer (e : p ⁻¹' {x}) :
    FundamentalGroup E e.1 ≃* MulAction.stabilizer (FreeGroup α) e :=
  (cov.fundamentalGroupEquivStabilizer e).trans
    ((Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (cov.map_monodromyStabilizer φ hφ e)))

theorem exists_free_smul_eq [PathConnectedSpace E] (e e' : p ⁻¹' {x}) :
    ∃ g : FreeGroup α, g • e = e' := by
  obtain ⟨γ, hγ⟩ := cov.exists_monodromy_eq e e'
  exact ⟨φ γ, by rw [hφ, MulEquiv.symm_apply_apply, hγ]⟩

/-- **Schreier's formula for coverings**: a path-connected covering with `d` sheets of a space
with free fundamental group of rank `n` has free fundamental group of rank `d (n - 1) + 1`. -/
theorem exists_fundamentalGroup_mulEquiv_freeGroup [PathConnectedSpace E] [Finite α]
    [Finite (p ⁻¹' {x})] (e : p ⁻¹' {x}) :
    ∃ (ι : Type (max u v)) (_ : Finite ι), Nonempty (FundamentalGroup E e.1 ≃* FreeGroup ι) ∧
      Nat.card ι + Nat.card (p ⁻¹' {x}) = Nat.card (p ⁻¹' {x}) * Nat.card α + 1 := by
  obtain ⟨T, hT⟩ := exists_transversal_card (ω₀ := e) (cov.exists_free_smul_eq φ hφ e)
  exact ⟨T.Gens, inferInstance,
    ⟨(cov.fundamentalGroupEquivFreeStabilizer φ hφ e).trans T.basis.repr⟩, hT⟩

/-- **Filling cusps, group-theoretically**: the quotient of `π₁(E, e)` by the normal closure of
the elements whose image in `π₁(X, x) ≅ F(α)` is conjugate to a power of a letter of `A` is free
of rank `d (|α| - 1) + 1 - ∑_{a ∈ A} #(⟨a⟩-orbits)`. -/
theorem exists_quotient_mulEquiv_freeGroup [PathConnectedSpace E] [Finite α]
    [Finite (p ⁻¹' {x})] (e : p ⁻¹' {x}) (A : Finset α) :
    ∃ (ι : Type (max u v)) (_ : Finite ι),
      Nonempty (FundamentalGroup E e.1 ⧸
          (cuspSubgroup (A : Set α) e).comap
            (cov.fundamentalGroupEquivFreeStabilizer φ hφ e).toMonoidHom ≃* FreeGroup ι) ∧
      Nat.card ι + Nat.card (p ⁻¹' {x}) +
        ∑ a ∈ A, Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (FreeGroup.of a))
          (p ⁻¹' {x})) =
        Nat.card (p ⁻¹' {x}) * Nat.card α + 1 := by
  obtain ⟨ι, hι, ⟨ψ⟩, hcard⟩ := exists_quotient_cuspSubgroup_mulEquiv (ω₀ := e) A
    (cov.exists_free_smul_eq φ hφ e)
  refine ⟨ι, hι, ⟨?_⟩, hcard⟩
  exact (QuotientGroup.congr _ _ (cov.fundamentalGroupEquivFreeStabilizer φ hφ e)
    (Subgroup.map_comap_eq_self_of_surjective
      (cov.fundamentalGroupEquivFreeStabilizer φ hφ e).surjective _)).trans ψ

end

end IsCoveringMap

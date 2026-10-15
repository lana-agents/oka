/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Uniformization.Uniqueness
import Oka.Uniformization.FrickeFree
import Mathlib.Topology.Homotopy.Lifting

/-!
# The fundamental group of a once-punctured elliptic curve is free of rank two

Let `W` be an elliptic curve over `ℂ` and `V W ⊆ ℂ²` its affine points, i.e. `E(ℂ) ∖ {O}`. A
uniformisation `π : ℍ → V W` with deck group `⟨A, B⟩` (`Uniformization.IsUniformization`) is a
covering map (`IsUniformization.isCoveringMap`), and by the ping-pong argument of
`Oka/Uniformization/FrickeFree.lean` the free group `F(a, b)`, acting on `ℍ` through
`a ↦ A`, `b ↦ B`, acts **freely** with quotient `V W` (`IsUniformization.isQuotientCoveringMap`).
Since `ℍ` is simply connected, Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` gives

  `π₁(E(ℂ) ∖ {O}, x) ≃* F₂`   (`Uniformization.fundamentalGroupEquivFreeGroup`),

the topological fundamental group of a once-punctured elliptic curve is the surface group
`Π_{1,1} = ⟨a, b, c | [a, b] c = 1⟩ ≅ F(a, b)`.
-/

open UpperHalfPlane Topology
open scoped MatrixGroups

namespace Uniformization

variable {W : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- The action of the free group `F(a, b)` on `ℍ` through `a ↦ A`, `b ↦ B`. -/
@[reducible] noncomputable def freeAction (A B : SL(2, ℝ)) : MulAction (FreeGroup (Fin 2)) ℍ :=
  MulAction.compHom ℍ (FreeGroup.lift ![A, B])

namespace IsUniformization

/-- The deck transformations of `ℍ → V W` with a fixed point act trivially. -/
theorem smul_eq_self_of_fixed [W.IsElliptic] (h : IsUniformization W A B π) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {A, B}) {τ : ℍ} (hτ : γ • τ = τ) (σ : ℍ) : γ • σ = σ := by
  have := h.isCoveringMap.eq_of_comp_eq (g₁ := fun σ : ℍ ↦ γ • σ) (g₂ := id)
    (continuous_const_smul γ) continuous_id (funext fun σ ↦ h.toV_smul hγ σ) τ hτ
  exact congrFun this σ

/-- **The free group `F(a, b)` acts freely on `ℍ` with quotient `V W`.** -/
theorem isQuotientCoveringMap [W.IsElliptic] (h : IsUniformization W A B π)
    (hcomm : Fricke.tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : Fricke.tr A ≠ 0) :
    letI := freeAction A B
    IsQuotientCoveringMap h.toV (FreeGroup (Fin 2)) := by
  letI := freeAction A B
  have hrange : (FreeGroup.lift ![A, B]).range = Subgroup.closure {A, B} := by
    rw [FreeGroup.range_lift_eq_closure]
    congr 1
    ext g
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hmem : ∀ w : FreeGroup (Fin 2), FreeGroup.lift ![A, B] w ∈ Subgroup.closure {A, B} :=
    fun w ↦ hrange ▸ ⟨w, rfl⟩
  have hsmul : ∀ (w : FreeGroup (Fin 2)) (τ : ℍ), w • τ = FreeGroup.lift ![A, B] w • τ :=
    fun _ _ ↦ rfl
  refine (isQuotientCoveringMap_iff_isCoveringMap_and _ _).2
    ⟨h.isCoveringMap, fun x ↦ ?_, ⟨fun w ↦ ?_⟩, ?_, fun {e₁ e₂} ↦ ?_⟩
  · obtain ⟨z, hz⟩ := h.surj x.1.1 x.1.2 x.2
    exact ⟨z, Subtype.ext hz⟩
  · simp only [hsmul]
    exact continuous_const_smul _
  · rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro w τ hτ
    have htriv := h.smul_eq_self_of_fixed (hmem w) hτ
    exact Fricke.eq_one_of_lift_eq_pm_one hcomm hA (Unif.eq_one_or_neg_one_of_forall htriv)
  · constructor
    · intro he
      obtain ⟨γ, hγ, hγe⟩ := (h.fibre e₂ e₁).1 (congrArg Subtype.val he).symm
      rw [← hrange] at hγ
      obtain ⟨w, rfl⟩ := hγ
      exact ⟨w, hγe⟩
    · rintro ⟨w, rfl⟩
      exact h.toV_smul (hmem w) e₂

end IsUniformization

/-- **The fundamental group of a once-punctured elliptic curve is free of rank two**: for a
uniformisation `π : ℍ → V W` with deck group `⟨A, B⟩`, `π₁(V W, x) ≃* F(a, b)`. -/
noncomputable def IsUniformization.fundamentalGroupEquiv [W.IsElliptic]
    (h : IsUniformization W A B π) (hcomm : Fricke.tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : Fricke.tr A ≠ 0) (x : V W) : FundamentalGroup (V W) x ≃* FreeGroup (Fin 2) :=
  letI := freeAction A B
  let e : h.toV ⁻¹' {x} := ⟨(h.isQuotientCoveringMap hcomm hA).surjective x |>.choose,
    (h.isQuotientCoveringMap hcomm hA).surjective x |>.choose_spec⟩
  ((h.isQuotientCoveringMap hcomm hA).fundamentalGroupEquiv e).trans
    (MulEquiv.inv' (FreeGroup (Fin 2))).symm

/-- **`π₁(E(ℂ) ∖ {O}) ≅ F₂`** for every elliptic curve `W` over `ℂ` and every affine point `x`. -/
theorem nonempty_fundamentalGroup_mulEquiv (W : WeierstrassCurve ℂ) [W.IsElliptic] (x : V W) :
    Nonempty (FundamentalGroup (V W) x ≃* FreeGroup (Fin 2)) := by
  obtain ⟨A, B, π, h1, h2, h⟩ := exists_isUniformization W
  exact ⟨h.fundamentalGroupEquiv (by rwa [Fricke.tr]) (by rwa [Fricke.tr]) x⟩

end Uniformization

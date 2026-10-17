/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Homotopy.Lifting

/-!
# The fundamental group of a covering space is a stabiliser

For a covering map `p : E → X` and `e` in the fibre over `x`, the induced map
`π₁(E, e) → π₁(X, x)` is injective (Mathlib's `IsCoveringMap.injective_path_homotopic_map`) and
its image is the stabiliser of `e` for the monodromy action of `π₁(X, x)` on the fibre
(Hatcher, *Algebraic Topology*, Prop. 1.31 and the proof of Prop. 1.32: a loop at `x` lifts to a
loop at `e` iff its class lies in `p_*(π₁(E, e))`). Mathlib proves the image statement only for
quotient coverings (`IsQuotientCoveringMap.ker_monodromyPerm`); the argument is the same.

## Main results

- `IsCoveringMap.mem_monodromyStabilizer_iff_mem_range`: `γ • e = e ↔ γ ∈ range p_*`;
- `IsCoveringMap.fundamentalGroupEquivStabilizer`: `π₁(E, e) ≃* Stab(e)`.
-/

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p) {x : X}

/-- The stabiliser of a point of the fibre for the monodromy action. -/
noncomputable abbrev monodromyStabilizer (e : p ⁻¹' {x}) : Subgroup (FundamentalGroup X x) :=
  @MulAction.stabilizer (FundamentalGroup X x) _ _ (cov.fundamentalGroupMulAction x) e

theorem mem_monodromyStabilizer_iff (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    γ ∈ cov.monodromyStabilizer e ↔ cov.monodromy γ e = e :=
  Iff.rfl

/-- **The image of `π₁(E, e)` is the stabiliser of `e`.** -/
theorem mem_monodromyStabilizer_iff_mem_range (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    γ ∈ cov.monodromyStabilizer e ↔
      γ ∈ (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.2).range := by
  rw [mem_monodromyStabilizer_iff]
  constructor
  · intro h
    refine ⟨(cov.liftPathQuotient γ e).cast rfl (congrArg Subtype.val h).symm, ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
      IsCoveringMap.map_liftPathQuotient]
    aesop
  · rintro ⟨γ, rfl⟩
    exact cov.monodromy_eq_of_map_eq γ (by aesop (add simp FundamentalGroup.mapOfEq_apply))

theorem mapOfEq_injective (e : p ⁻¹' {x}) :
    Function.Injective (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.2) := by
  intro a b hab
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply] at hab
  have hab' : Path.Homotopic.Quotient.map a ⟨p, cov.continuous⟩ =
      Path.Homotopic.Quotient.map b ⟨p, cov.continuous⟩ := by
    have := congrArg (fun q ↦ Path.Homotopic.Quotient.cast q e.2 e.2) hab
    simpa using this
  exact cov.injective_path_homotopic_map _ _ hab'

/-- **`π₁` of a covering space is the stabiliser of the base point** under monodromy. -/
noncomputable def fundamentalGroupEquivStabilizer (e : p ⁻¹' {x}) :
    FundamentalGroup E e.1 ≃* cov.monodromyStabilizer e :=
  MulEquiv.ofBijective
    ((FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.2).codRestrict _
      fun γ ↦ (cov.mem_monodromyStabilizer_iff_mem_range e _).mpr ⟨γ, rfl⟩)
    ⟨fun a b hab ↦ cov.mapOfEq_injective e (congrArg Subtype.val hab), by
      rintro ⟨γ, hγ⟩
      obtain ⟨δ, rfl⟩ := (cov.mem_monodromyStabilizer_iff_mem_range e _).mp hγ
      exact ⟨δ, rfl⟩⟩

@[simp] theorem coe_fundamentalGroupEquivStabilizer (e : p ⁻¹' {x})
    (γ : FundamentalGroup E e.1) :
    (cov.fundamentalGroupEquivStabilizer e γ : FundamentalGroup X x) =
      FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.2 γ :=
  rfl

end IsCoveringMap

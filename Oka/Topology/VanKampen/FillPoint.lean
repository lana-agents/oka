/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.Fill
import Oka.Topology.VanKampen.PuncturedLoops
import Mathlib.Analysis.Convex.Contractible

/-!
# Filling in a point with a disc neighbourhood

Let `X` be a `T₁` space, `P ∈ X` a point with an open neighbourhood `V` homeomorphic to the unit
disc by a homeomorphism sending `P` to `0`, and assume `X ∖ {P}` path connected. For a base point
`x₀ ∈ V ∖ {P}` the inclusion `X ∖ {P} ⊆ X` induces

  `π₁(X ∖ {P}, x₀) ⧸ ⟨⟨im π₁(V ∖ {P}, x₀)⟩⟩ ≃* π₁(X, x₀)`

(`VanKampen.fillPointEquiv`): Seifert–van Kampen for the cover `X = (X ∖ {P}) ∪ V` with `V` simply
connected (`VanKampen.Hypotheses.fillEquiv`). The punctured disc `V ∖ {P}` is path connected
(`VanKampen.isPathConnected_diff_of_disc`, from the punctured-disc case of
`Complex.PuncturedPlane.loopStatement`), and its fundamental group is infinite cyclic, generated
by a loop around `P`, by the same statement.

This is the step "fill in one puncture" of the computation of `π₁` of a smooth affine curve from a
finite covering of `ℂ ∖ {0, 1}` (Hatcher, *Algebraic Topology*, Thm. 1.20 and Prop. 1.26).
-/

open Set Metric Complex.PuncturedPlane

namespace VanKampen

variable {X : Type*} [TopologicalSpace X]

variable {P : X} {V : Set X} (e : V ≃ₜ ball (0 : ℂ) 1)

include e in
/-- A disc neighbourhood is simply connected. -/
theorem simplyConnectedSpace_of_disc : SimplyConnectedSpace V := by
  haveI : ContractibleSpace (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, mem_ball_self one_pos⟩
  haveI : ContractibleSpace V := e.contractibleSpace_iff.mpr inferInstance
  infer_instance

include e in
theorem isPathConnected_of_disc : IsPathConnected V := by
  haveI := simplyConnectedSpace_of_disc e
  have h := isPathConnected_range (X := V) (f := Subtype.val) continuous_subtype_val
  rwa [Subtype.range_coe] at h

/-- A disc neighbourhood with its centre removed is path connected. -/
theorem isPathConnected_diff_of_disc (hP : P ∈ V) (he : (e ⟨P, hP⟩ : ℂ) = 0) :
    IsPathConnected (V \ {P}) := by
  have hx : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 ∧ (1 / 2 : ℂ) ∉ ({0} : Finset ℂ) := by
    refine ⟨?_, by simp⟩
    rw [mem_ball, dist_zero_right]
    norm_num
  obtain ⟨hpc, -⟩ := loopStatement 1 (ball (0 : ℂ) 1) isOpen_ball (convex_ball 0 1)
    {0} (by simp) (by simp) ⟨1 / 2, hx⟩
  have h := isPathConnected_range (X := Region (ball (0 : ℂ) 1) {0})
    (f := fun z ↦ (e.symm ⟨z.1, z.2.1⟩ : X))
    (continuous_subtype_val.comp (e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)))
  convert h using 1
  ext y
  constructor
  · rintro ⟨hyV, hyP⟩
    refine ⟨⟨(e ⟨y, hyV⟩ : ℂ), (e ⟨y, hyV⟩).2, ?_⟩, by simp⟩
    rw [Finset.mem_singleton]
    intro h0
    apply hyP
    have : e ⟨y, hyV⟩ = e ⟨P, hP⟩ := Subtype.ext (h0.trans he.symm)
    exact congrArg Subtype.val (e.injective this)
  · rintro ⟨z, rfl⟩
    refine ⟨(e.symm _).2, fun hzP ↦ z.2.2 ?_⟩
    rw [Finset.mem_singleton]
    have : e.symm ⟨z.1, z.2.1⟩ = ⟨P, hP⟩ := Subtype.ext hzP
    rw [e.symm_apply_eq] at this
    exact (congrArg Subtype.val this).trans he

/-- The Seifert–van Kampen hypotheses for `X = (X ∖ {P}) ∪ V`. -/
theorem hypotheses_fillPoint [T1Space X] (hV : IsOpen V) (hP : P ∈ V) (he : (e ⟨P, hP⟩ : ℂ) = 0)
    (hU : IsPathConnected ({P}ᶜ : Set X)) {x₀ : X} (hx₀ : x₀ ∈ V \ {P}) :
    Hypotheses ({P}ᶜ) V x₀ where
  isOpen_left := isOpen_compl_singleton
  isOpen_right := hV
  union_eq := by
    ext y
    by_cases hy : y = P
    · subst hy; simp [hP]
    · simp [hy]
  mem_inter := ⟨hx₀.2, hx₀.1⟩
  isPathConnected_left := hU
  isPathConnected_right := isPathConnected_of_disc e
  isPathConnected_inter := by
    rw [Set.inter_comm, ← Set.sdiff_eq]
    exact isPathConnected_diff_of_disc e hP he

/-- **Filling in a point with a disc neighbourhood**:
`π₁(X ∖ {P}, x₀) ⧸ ⟨⟨im π₁(V ∖ {P}, x₀)⟩⟩ ≃* π₁(X, x₀)`. -/
noncomputable def fillPointEquiv [T1Space X] (hV : IsOpen V) (hP : P ∈ V) (he : (e ⟨P, hP⟩ : ℂ) = 0)
    (hU : IsPathConnected ({P}ᶜ : Set X)) {x₀ : X} (hx₀ : x₀ ∈ V \ {P}) :
    FundamentalGroup (piece ({P}ᶜ) V true)
        ⟨x₀, mem_piece_of_mem_inter (hypotheses_fillPoint e hV hP he hU hx₀).mem_inter true⟩ ⧸
      (hypotheses_fillPoint e hV hP he hU hx₀).fillSubgroup ≃* FundamentalGroup X x₀ :=
  haveI : SimplyConnectedSpace (piece ({P}ᶜ) V false) := simplyConnectedSpace_of_disc e
  (hypotheses_fillPoint e hV hP he hU hx₀).fillEquiv

end VanKampen

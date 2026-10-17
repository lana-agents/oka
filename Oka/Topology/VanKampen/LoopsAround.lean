/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.PuncturedLoops

/-!
# Loops around a puncture are determined up to conjugacy

In `ℂ ∖ S` (more generally an open region `C ∖ S`), the circles of two admissible radii around
`s ∈ S` are conjugate along a path (`Complex.PuncturedPlane.circleArrow_eq_conj`), and every loop
contained in a punctured disc `B(s, ρ) ∖ {s}` free of other points of `S` is conjugate to a power
of any given loop around `s` (`Complex.PuncturedPlane.exists_eq_conj_zpow`).

In a one-point convex region `C ∖ {a}` all loops `δ · c · δ⁻¹` around `a` (any admissible radius,
any `δ`) are equal (`Complex.PuncturedPlane.conj_circle_eq`): each acts on the fibre of
`exp : ℂ → ℂ ∖ {0}` by the period `2πi` (`fundamentalGroupToMulOpposite_conj_circle`), and this
action is faithful.
-/

open Set Topology Metric CategoryTheory

namespace Complex.PuncturedPlane

/-- Conjugation by an arrow `α : z ⟶ x` of the fundamental groupoid, `X ↦ α ≫ X ≫ α⁻¹`. -/
noncomputable def conjArrow {Y : Type*} [TopologicalSpace Y] {z x : Y}
    (α : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk x) :
    FundamentalGroup Y x ≃* FundamentalGroup Y z :=
  ((Groupoid.isoEquivHom _ _).symm α).symm.conj

theorem conjArrow_apply {Y : Type*} [TopologicalSpace Y] {z x : Y}
    (α : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk x) (X : FundamentalGroup Y x) :
    conjArrow α X = α ≫ X ≫ Groupoid.inv α :=
  rfl

/-- **All loops around the puncture of a convex region `C ∖ {a}` agree.** -/
theorem conj_circle_eq {C : Set ℂ} {a : ℂ} (hCc : Convex ℝ C) {r₁ r₂ : ℝ}
    (h₁ : Admissible C {a} a r₁) (h₂ : Admissible C {a} a r₂) {x : Region C {a}}
    (δ₁ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (circleBase h₁))
    (δ₂ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (circleBase h₂)) :
    δ₁ ≫ circleArrow h₁ ≫ Groupoid.inv δ₁ = δ₂ ≫ circleArrow h₂ ≫ Groupoid.inv δ₂ := by
  have hJ := map_bijective_of_homotopyEquiv (homotopyEquiv hCc h₁) x
  let e : expMap ⁻¹' {shiftMap x} :=
    ⟨Complex.log (shiftMap x), Subtype.ext (Complex.exp_log (shiftMap x).2)⟩
  let Φ := Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e
  have key : ∀ (r : ℝ) (h : Admissible C {a} a r)
      (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (circleBase h)),
      Φ (FundamentalGroup.map shiftMap x (δ ≫ circleArrow h ≫ Groupoid.inv δ)) =
        MulOpposite.op (Multiplicative.ofAdd twoPiI) := by
    intro r h δ
    change Complex.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e
      ((FundamentalGroupoid.map shiftMap).map (δ ≫ circleArrow h ≫ Groupoid.inv δ)) = _
    rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Functor.map_inv,
      ← Groupoid.inv_eq_inv]
    refine fundamentalGroupToMulOpposite_conj_circle e _ ((circlePath h).map shiftMap.continuous)
      fun t ↦ ?_
    change circleFun a r t - a = ((a + (r : ℂ)) - a) * _
    simp only [circleFun]
    ring
  apply hJ.1
  apply Φ.injective
  change Φ (FundamentalGroup.map shiftMap x _) = Φ (FundamentalGroup.map shiftMap x _)
  rw [key, key]

/-- **Circles of two admissible radii around `s` are conjugate.** -/
theorem circleArrow_eq_conj {S : Finset ℂ} {s : ℂ} {r₁ r₂ : ℝ}
    (h₁ : Admissible Set.univ S s r₁) (h₂ : Admissible Set.univ S s r₂) :
    ∃ β : FundamentalGroupoid.mk (circleBase h₁) ⟶ FundamentalGroupoid.mk (circleBase h₂),
      circleArrow h₁ = β ≫ circleArrow h₂ ≫ Groupoid.inv β := by
  classical
  -- a ball around `s` containing both circles and no other point of `S`
  set r := max r₁ r₂
  have hr : Admissible Set.univ S s r := by
    rcases le_total r₁ r₂ with h | h
    · rwa [show r = r₂ from max_eq_right h]
    · rwa [show r = r₁ from max_eq_left h]
  have hopen : IsOpen ((↑(S.erase s) : Set ℂ)ᶜ) := (S.erase s).finite_toSet.isClosed.isOpen_compl
  have hsub : closedBall s r ⊆ ((↑(S.erase s) : Set ℂ)ᶜ) := fun z hz hzS ↦ by
    have := hr.isolated z (Finset.mem_of_mem_erase hzS) hz
    exact (Finset.ne_of_mem_erase hzS) this
  obtain ⟨ε, hε, hthick⟩ := (isCompact_closedBall s r).exists_thickening_subset_open hopen hsub
  rw [thickening_closedBall hε hr.pos.le] at hthick
  set C' := ball s (ε + r)
  have hC' : ∀ {r'}, Admissible Set.univ S s r' → r' ≤ r → Admissible C' {s} s r' :=
    fun h hle ↦ ⟨h.pos, closedBall_subset_ball (by linarith), fun s' hs' _ ↦
      Finset.mem_singleton.1 hs'⟩
  have h₁' := hC' h₁ (le_max_left _ _)
  have h₂' := hC' h₂ (le_max_right _ _)
  haveI := pathConnectedSpace_region_single (convex_ball s (ε + r)) h₁'
  -- the inclusion `C' ∖ {s} → ℂ ∖ S`
  let ι : C(Region C' {s}, Region Set.univ S) :=
    ⟨fun z ↦ ⟨z.1, trivial, fun hz ↦ by
      by_cases hzs : z.1 = s
      · exact z.2.2 (by rw [hzs]; exact Finset.mem_singleton_self s)
      · exact hthick z.2.1 (Finset.mem_erase.2 ⟨hzs, hz⟩)⟩, by fun_prop⟩
  let δ₂ : FundamentalGroupoid.mk (circleBase h₁') ⟶ FundamentalGroupoid.mk (circleBase h₂') :=
    ⟦PathConnectedSpace.somePath _ _⟧
  have heq := conj_circle_eq (convex_ball s (ε + r)) h₁' h₂' (𝟙 _) δ₂
  have hmap : ∀ {r'} (h : Admissible Set.univ S s r') (h' : Admissible C' {s} s r'),
      (FundamentalGroupoid.map ι).map (circleArrow h') = circleArrow h := by
    intro r' h h'
    change Path.Homotopic.Quotient.mk ((circlePath h').map ι.continuous) = _
    have : (circlePath h').map ι.continuous = circlePath h := by ext t; rfl
    rw [this]
    rfl
  refine ⟨(FundamentalGroupoid.map ι).map δ₂, ?_⟩
  have := congrArg (FundamentalGroupoid.map ι).map heq
  simp only [Groupoid.inv_eq_inv, Functor.map_comp, Functor.map_inv,
    Category.id_comp, IsIso.inv_id, Category.comp_id, hmap h₁ h₁', hmap h₂ h₂'] at this
  rw [Groupoid.inv_eq_inv]
  exact this

/-- Elements of the free group on one generator are its powers. -/
theorem FreeGroup.eq_of_zpow_of_subsingleton {α : Type*} [Subsingleton α] (a : α)
    (w : FreeGroup α) : ∃ k : ℤ, w = FreeGroup.of a ^ k := by
  induction w using FreeGroup.induction_on with
  | C1 => exact ⟨0, by simp⟩
  | of b => exact ⟨1, by rw [Subsingleton.elim b a, zpow_one]⟩
  | inv_of b h =>
    obtain ⟨k, hk⟩ := h
    exact ⟨-k, by rw [hk, zpow_neg]⟩
  | mul x y hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    exact ⟨k + l, by rw [hk, hl, zpow_add]⟩

/-- **Loops in a punctured disc around `s` are conjugate to powers of a loop around `s`.** -/
theorem exists_eq_conj_zpow {S : Finset ℂ} {s : ℂ} (hs : s ∈ S) {ρ : ℝ}
    (hρ : ∀ s' ∈ S, s' ∈ ball s ρ → s' = s) {x₀ : Region Set.univ S}
    {X : FundamentalGroup (Region Set.univ S) x₀} (hX : IsLoopAround X s)
    {z : Region Set.univ S} (c : Path z z) (hc : ∀ t, (c t : ℂ) ∈ ball s ρ) :
    ∃ (k : ℤ) (α : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk x₀),
      (⟦c⟧ : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk z) = conjArrow α (X ^ k) := by
  classical
  -- `c` as a loop in `B(s, ρ) ∖ {s}`
  have hzB : (z : ℂ) ∈ ball s ρ := c.source ▸ hc 0
  have hne : ∀ y : Region Set.univ S, (y : ℂ) ∉ ({s} : Finset ℂ) := fun y h ↦ y.2.2 (by
    rw [Finset.mem_singleton] at h; rw [h]; exact hs)
  let z' : Region (ball s ρ) {s} := ⟨z, hzB, hne z⟩
  let ι : C(Region (ball s ρ) {s}, Region Set.univ S) :=
    ⟨fun w ↦ ⟨w.1, trivial, fun hw ↦ w.2.2 (by
      rw [Finset.mem_singleton]; exact hρ _ hw w.2.1)⟩, by fun_prop⟩
  let c' : Path z' z' :=
    { toFun := fun t ↦ ⟨c t, hc t, hne (c t)⟩
      continuous_toFun := (continuous_subtype_val.comp c.continuous).subtype_mk _
      source' := by ext; simp [z']
      target' := by ext; simp [z'] }
  have hc'c : (FundamentalGroupoid.map ι).map
      (⟦c'⟧ : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk z') = ⟦c⟧ := by
    change Path.Homotopic.Quotient.mk (c'.map ι.continuous) = _
    have : c'.map ι.continuous = c := by ext t; rfl
    rw [this]
    rfl
  obtain ⟨-, g, hg, hb⟩ := loopStatement 1 (ball s ρ) isOpen_ball (convex_ball s ρ) {s}
    (by
      intro y hy
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hy
      rw [hy]
      exact mem_ball_self (pos_of_mem_ball hzB)) (by simp) z'
  let s₀ : ({s} : Finset ℂ) := ⟨s, Finset.mem_singleton_self s⟩
  obtain ⟨w, hw⟩ := hb.2 (⟦c'⟧ : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk z')
  obtain ⟨k, rfl⟩ := FreeGroup.eq_of_zpow_of_subsingleton s₀ w
  rw [map_zpow, FreeGroup.lift_apply_of] at hw
  -- `g s₀` maps to a loop around `s` in `ℂ ∖ S`, conjugate to `X`
  have hgS : IsLoopAround (FundamentalGroup.map ι z' (g s₀)) s :=
    (hg s₀).map (subset_univ _) (fun s' hs' hB ↦ by
      rw [Finset.mem_singleton]; exact hρ s' hs' hB) ι (fun _ ↦ rfl)
  obtain ⟨r₁, h₁, δ₁, hδ₁⟩ := hgS
  obtain ⟨r₂, h₂, δ₂, rfl⟩ := hX
  obtain ⟨β, hβ⟩ := circleArrow_eq_conj h₁ h₂
  refine ⟨k, δ₁ ≫ β ≫ Groupoid.inv δ₂, ?_⟩
  have hgX : FundamentalGroup.map ι z' (g s₀) =
      conjArrow (δ₁ ≫ β ≫ Groupoid.inv δ₂) (δ₂ ≫ circleArrow h₂ ≫ Groupoid.inv δ₂) := by
    rw [hδ₁, hβ, conjArrow_apply]
    simp [Groupoid.inv_eq_inv]
  rw [map_zpow, ← hgX, ← map_zpow, hw]
  exact hc'c.symm

end Complex.PuncturedPlane

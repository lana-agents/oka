/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.FillPoint

/-!
# Filling in finitely many points with disc neighbourhoods

Let `Y` be a `T₁` space, `Z ⊆ Y` a finite set of points, each `P ∈ Z` with an open neighbourhood
`V P` homeomorphic to the unit disc (by a homeomorphism sending `P` to `0`) with `V P ∩ Z = {P}`,
and let `j : W → Y` be an embedding with image `Y ∖ Z` and `W` path connected. Then
`j_* : π₁(W, w₀) → π₁(Y, j w₀)` is surjective and its kernel is the normal closure of the classes
`γ c γ⁻¹`, `γ` a path class from `w₀` and `c` a loop whose image lies in one of the discs
(`VanKampen.fill_finite`). This iterates the one-point step `VanKampen.fillPointEquiv`
(Seifert–van Kampen with a disc, Hatcher, *Algebraic Topology*, Thm. 1.20 and Prop. 1.26),
after moving the base point out of the disc (`VanKampen.fill_one`).

The loops are recorded base-point-free, as the set `VanKampen.conjLoops j V w₀` of classes
`γ ≫ ⟦c⟧ ≫ γ⁻¹` with `j ∘ c ⊆ V`.
-/

open CategoryTheory Set Metric Topology

namespace VanKampen

section ConjLoops

variable {W Y : Type*} [TopologicalSpace W] [TopologicalSpace Y]

/-- The classes `γ ≫ ⟦c⟧ ≫ γ⁻¹ ∈ π₁(W, w₀)` of loops `c` (at any point `w`) whose image under `j`
lies in `V`, conjugated back to `w₀` along a path class `γ`. -/
def conjLoops (j : W → Y) (V : Set Y) (w₀ : W) : Set (FundamentalGroup W w₀) :=
  {g | ∃ (w : W) (γ : FundamentalGroupoid.mk w₀ ⟶ FundamentalGroupoid.mk w) (c : Path w w),
    (∀ t, j (c t) ∈ V) ∧
      g = γ ≫ (⟦c⟧ : FundamentalGroupoid.mk w ⟶ FundamentalGroupoid.mk w) ≫ Groupoid.inv γ}

omit [TopologicalSpace Y] in
/-- Images of `conjLoops` under a continuous map over `Y`. -/
theorem map_mem_conjLoops {W' : Type*} [TopologicalSpace W'] (j : W → Y) (j' : W' → Y)
    (f : C(W, W')) (hf : ∀ w, j' (f w) = j w) {V : Set Y} {w₀ : W} {g : FundamentalGroup W w₀}
    (hg : g ∈ conjLoops j V w₀) : FundamentalGroup.map f w₀ g ∈ conjLoops j' V (f w₀) := by
  obtain ⟨w, γ, c, hc, rfl⟩ := hg
  refine ⟨f w, (FundamentalGroupoid.map f).map γ, c.map f.continuous, fun t ↦ ?_, ?_⟩
  · simpa [hf] using hc t
  · change (FundamentalGroupoid.map f).map (γ ≫ _ ≫ Groupoid.inv γ) = _
    rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
      Functor.map_inv]
    rfl

end ConjLoops

section FillOne

variable {Y : Type*} [TopologicalSpace Y] [T1Space Y] {P : Y} {V : Set Y}
  (e : V ≃ₜ ball (0 : ℂ) 1)

/-- The inclusion `Y ∖ {P} ⟶ Y`. -/
abbrev complIncl (P : Y) : C(({P}ᶜ : Set Y), Y) := ⟨Subtype.val, continuous_subtype_val⟩

/-- Naturality of the change of base point along a path. -/
theorem map_fundamentalGroupMulEquivOfPath {X X' : Type*} [TopologicalSpace X]
    [TopologicalSpace X'] (f : C(X, X')) {x x₁ : X} (β : Path x x₁) (g : FundamentalGroup X x) :
    FundamentalGroup.map f x₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath β g) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (β.map f.continuous)
        (FundamentalGroup.map f x g) := by
  change (FundamentalGroupoid.map f).map (Groupoid.inv (⟦β⟧ : FundamentalGroupoid.mk x ⟶ _) ≫
    g ≫ ⟦β⟧) = Groupoid.inv (⟦β.map f.continuous⟧ : FundamentalGroupoid.mk (f x) ⟶ _) ≫
      (FundamentalGroupoid.map f).map g ≫ ⟦β.map f.continuous⟧
  rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
    Functor.map_inv]
  rfl

theorem fundamentalGroupMulEquivOfPath_apply' {X : Type*} [TopologicalSpace X] {x x₁ : X}
    (β : Path x x₁) (g : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath β g =
      Groupoid.inv (⟦β⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x₁) ≫ g ≫ ⟦β⟧ :=
  rfl

theorem fundamentalGroupMulEquivOfPath_symm_apply' {X : Type*} [TopologicalSpace X] {x x₁ : X}
    (β : Path x x₁) (g : FundamentalGroup X x₁) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath β).symm g =
      (⟦β⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x₁) ≫ g ≫ Groupoid.inv ⟦β⟧ := by
  rw [MulEquiv.symm_apply_eq, fundamentalGroupMulEquivOfPath_apply']
  simp [Groupoid.inv_eq_inv]

/-- **Filling in one point, at any base point**: for `x ∈ Y ∖ {P}`, the map
`π₁(Y ∖ {P}, x) → π₁(Y, x)` is surjective with kernel the normal closure of the conjugates of
loops in the disc. -/
theorem fill_one (hV : IsOpen V) (hP : P ∈ V) (he : (e ⟨P, hP⟩ : ℂ) = 0)
    (hU : IsPathConnected ({P}ᶜ : Set Y)) (x : ({P}ᶜ : Set Y)) :
    Function.Surjective (FundamentalGroup.map (complIncl P) x) ∧
      (FundamentalGroup.map (complIncl P) x).ker =
        Subgroup.normalClosure (conjLoops Subtype.val V x) := by
  obtain ⟨x₁, hx₁⟩ := (isPathConnected_diff_of_disc e hP he).nonempty
  have h := hypotheses_fillPoint e hV hP he hU hx₁
  haveI : SimplyConnectedSpace (piece ({P}ᶜ) V false) := simplyConnectedSpace_of_disc e
  haveI : PathConnectedSpace ({P}ᶜ : Set Y) := isPathConnected_iff_pathConnectedSpace.mp hU
  haveI : PathConnectedSpace ({P}ᶜ ∩ V : Set Y) :=
    isPathConnected_iff_pathConnectedSpace.mp h.isPathConnected_inter
  let x₁' : ({P}ᶜ : Set Y) := ⟨x₁, hx₁.2⟩
  let x₁'' : ({P}ᶜ ∩ V : Set Y) := ⟨x₁, h.mem_inter⟩
  let ι : C(({P}ᶜ ∩ V : Set Y), ({P}ᶜ : Set Y)) :=
    ⟨inclusion inter_subset_left, continuous_inclusion _⟩
  let β : Path x x₁' := PathConnectedSpace.somePath x x₁'
  set A := FundamentalGroup.fundamentalGroupMulEquivOfPath β
  set A' := FundamentalGroup.fundamentalGroupMulEquivOfPath (β.map (complIncl P).continuous)
  -- the map at `x₁` is the van Kampen piece map
  have hsurj₁ : Function.Surjective (FundamentalGroup.map (complIncl P) x₁') :=
    h.pieceMap_true_surjective
  have hker₁ : (FundamentalGroup.map (complIncl P) x₁').ker =
      Subgroup.normalClosure (Set.range (FundamentalGroup.map ι x₁'')) :=
    h.ker_pieceMap_true
  have hcomm : ∀ g, FundamentalGroup.map (complIncl P) x₁' (A g) =
      A' (FundamentalGroup.map (complIncl P) x g) :=
    map_fundamentalGroupMulEquivOfPath (complIncl P) β
  refine ⟨fun g ↦ ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hsurj₁ (A' g)
    refine ⟨A.symm y, A'.injective ?_⟩
    rw [← hcomm, MulEquiv.apply_symm_apply, hy]
  have hker : (FundamentalGroup.map (complIncl P) x).ker =
      (FundamentalGroup.map (complIncl P) x₁').ker.comap A.toMonoidHom := by
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hcomm]
    exact ⟨fun h ↦ by rw [h, map_one], fun h ↦ A'.injective (by rw [h, map_one])⟩
  rw [hker, hker₁, MulEquiv.toMonoidHom_eq_coe, ← Subgroup.comap_normalClosure]
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal fun g hg ↦ ?_
    obtain ⟨c, hc⟩ := hg
    induction c using Quotient.inductionOn with | h c =>
    apply Subgroup.subset_normalClosure
    refine ⟨x₁', ⟦β⟧, c.map ι.continuous, fun t ↦ (c t).2.2, A.injective ?_⟩
    rw [← hc, fundamentalGroupMulEquivOfPath_apply']
    simp [Groupoid.inv_eq_inv]
    rfl
  · refine Subgroup.normalClosure_le_normal fun g hg ↦ ?_
    obtain ⟨w, γ, c, hc, rfl⟩ := hg
    -- `c` is a loop in `U ∩ V`; join `x₁` to `w` inside `U ∩ V`.
    have hw : (w : Y) ∈ ({P}ᶜ ∩ V : Set Y) := by
      have := c.source ▸ hc 0
      exact ⟨w.2, this⟩
    let α : Path x₁'' ⟨w, hw⟩ := PathConnectedSpace.somePath _ _
    let c' : Path (⟨w, hw⟩ : ({P}ᶜ ∩ V : Set Y)) ⟨w, hw⟩ :=
      { toFun := fun t ↦ ⟨c t, (c t).2, hc t⟩
        continuous_toFun := (continuous_subtype_val.comp c.continuous).subtype_mk _
        source' := by ext; simp
        target' := by ext; simp }
    let k : FundamentalGroup ({P}ᶜ ∩ V : Set Y) x₁'' :=
      (⟦α⟧ : FundamentalGroupoid.mk _ ⟶ _) ≫ ⟦c'⟧ ≫ Groupoid.inv ⟦α⟧
    have hαc : FundamentalGroup.map ι x₁'' k =
        (⟦α.map ι.continuous⟧ : FundamentalGroupoid.mk x₁' ⟶ FundamentalGroupoid.mk w) ≫ ⟦c⟧ ≫
          Groupoid.inv ⟦α.map ι.continuous⟧ := by
      change (FundamentalGroupoid.map ι).map ((⟦α⟧ : FundamentalGroupoid.mk _ ⟶ _) ≫ ⟦c'⟧ ≫
        Groupoid.inv ⟦α⟧) = _
      rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
        Functor.map_inv]
      have hmapc : (FundamentalGroupoid.map ι).map
          (⟦c'⟧ : FundamentalGroupoid.mk (⟨w, hw⟩ : ({P}ᶜ ∩ V : Set Y)) ⟶
            FundamentalGroupoid.mk ⟨w, hw⟩) =
          (⟦c⟧ : FundamentalGroupoid.mk w ⟶ FundamentalGroupoid.mk w) := by
        have : c'.map ι.continuous = c := by ext t; rfl
        rw [← this]
        rfl
      rw [hmapc]
      rfl
    -- `γ c γ⁻¹ = h⁻¹ (β α c α⁻¹ β⁻¹) h` with `h = γ ≫ α⁻¹ ≫ β⁻¹`.
    let hh : FundamentalGroup ({P}ᶜ : Set Y) x :=
      γ ≫ Groupoid.inv ⟦α.map ι.continuous⟧ ≫ Groupoid.inv ⟦β⟧
    have hmem : A.symm (FundamentalGroup.map ι x₁'' k) ∈
        Subgroup.normalClosure (A ⁻¹' Set.range (FundamentalGroup.map ι x₁'')) :=
      Subgroup.subset_normalClosure (by simp)
    have := (Subgroup.normalClosure_normal (s := A ⁻¹' Set.range
      (FundamentalGroup.map ι x₁''))).conj_mem _ hmem hh⁻¹
    have heq : γ ≫ (⟦c⟧ : FundamentalGroupoid.mk w ⟶ _) ≫ Groupoid.inv γ =
        hh⁻¹ * A.symm (FundamentalGroup.map ι x₁'' k) * hh⁻¹⁻¹ := by
      rw [hαc, fundamentalGroupMulEquivOfPath_symm_apply']
      change _ = Groupoid.inv (Groupoid.inv hh) ≫ (⟦β⟧ ≫ (_ ≫ _ ≫ _) ≫ Groupoid.inv ⟦β⟧) ≫
        Groupoid.inv hh
      simp [hh, Groupoid.inv_eq_inv]
    rw [heq]
    exact this

end FillOne

section FillFinite

variable {W : Type*} [TopologicalSpace W] [PathConnectedSpace W]

/-- `Y ∖ {P}` is path connected if `Y ∖ Z` is (the image of `j`) and the other points of `Z` have
disc neighbourhoods. -/
theorem isPathConnected_compl_singleton {Y : Type*} [TopologicalSpace Y] (j : C(W, Y))
    {Z : Set Y} (hrange : range j = Zᶜ) (V : Y → Set Y) (hPV : ∀ P ∈ Z, P ∈ V P)
    (e : ∀ P ∈ Z, V P ≃ₜ ball (0 : ℂ) 1) (he : ∀ P (hP : P ∈ Z), (e P hP ⟨P, hPV P hP⟩ : ℂ) = 0)
    (hVZ : ∀ P ∈ Z, ∀ Q ∈ Z, Q ∈ V P → Q = P) {P : Y} (hP : P ∈ Z) (w₀ : W) :
    IsPathConnected ({P}ᶜ : Set Y) := by
  have hjP : ∀ w, j w ≠ P := fun w h ↦ by
    have : j w ∈ Zᶜ := hrange ▸ mem_range_self w
    exact this (h ▸ hP)
  have hjoin : ∀ w, JoinedIn ({P}ᶜ : Set Y) (j w₀) (j w) := fun w ↦
    ⟨(PathConnectedSpace.somePath w₀ w).map j.continuous, fun t ↦ hjP _⟩
  refine ⟨j w₀, hjP w₀, fun {y} hy ↦ ?_⟩
  by_cases hyZ : y ∈ Z
  · obtain ⟨v, hv⟩ := (isPathConnected_diff_of_disc (e y hyZ) (hPV y hyZ) (he y hyZ)).nonempty
    have hvZ : v ∉ Z := fun h ↦ hv.2 (hVZ y hyZ v h hv.1)
    obtain ⟨w, rfl⟩ : v ∈ range j := hrange ▸ hvZ
    have hVP : V y ⊆ ({P}ᶜ : Set Y) := fun z hz hzP ↦ by
      rw [mem_singleton_iff] at hzP
      subst hzP
      exact hy (hVZ y hyZ z hP hz).symm
    exact (hjoin w).trans (((isPathConnected_of_disc (e y hyZ)).joinedIn _ hv.1 y
      (hPV y hyZ)).mono hVP)
  · obtain ⟨w, rfl⟩ : y ∈ range j := hrange ▸ hyZ
    exact hjoin w

/-- The homeomorphism `V' ≃ₜ V` between `V ⊆ Y` seen in `Y ∖ {P}` and in `Y` (for `P ∉ V`). -/
def homeomorphPreimageVal {Y : Type*} [TopologicalSpace Y] {P : Y} (V : Set Y) (hV : P ∉ V) :
    (Subtype.val ⁻¹' V : Set ({P}ᶜ : Set Y)) ≃ₜ V where
  toFun y := ⟨y.1.1, y.2⟩
  invFun v := ⟨⟨v.1, fun h ↦ hV (h ▸ v.2)⟩, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem fill_finite_aux (n : ℕ) {Y : Type*} [TopologicalSpace Y] [T1Space Y] (j : C(W, Y))
    (hj : IsEmbedding j) (Z : Set Y) (hZ : Z.Finite) (hn : Z.ncard = n) (hrange : range j = Zᶜ)
    (V : Y → Set Y) (hVo : ∀ P ∈ Z, IsOpen (V P)) (hPV : ∀ P ∈ Z, P ∈ V P)
    (e : ∀ P ∈ Z, V P ≃ₜ ball (0 : ℂ) 1) (he : ∀ P (hP : P ∈ Z), (e P hP ⟨P, hPV P hP⟩ : ℂ) = 0)
    (hVZ : ∀ P ∈ Z, ∀ Q ∈ Z, Q ∈ V P → Q = P) (w₀ : W) :
    Function.Surjective (FundamentalGroup.map j w₀) ∧
      (FundamentalGroup.map j w₀).ker =
        Subgroup.normalClosure (⋃ P ∈ Z, conjLoops j (V P) w₀) := by
  induction n generalizing Y with
  | zero =>
    have hZe : Z = ∅ := (Set.ncard_eq_zero hZ).mp hn
    subst hZe
    have hsurj : Function.Surjective j := fun y ↦ by
      have : y ∈ range j := by rw [hrange]; simp
      exact this
    let H := hj.toHomeomorphOfSurjective hsurj
    have hb := Complex.PuncturedPlane.map_bijective_of_homotopyEquiv H.toHomotopyEquiv w₀
    have hHj : H.toHomotopyEquiv.toFun = j := by ext; rfl
    rw [hHj] at hb
    refine ⟨hb.2, ?_⟩
    simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Subgroup.normalClosure_empty]
    exact (MonoidHom.ker_eq_bot_iff _).mpr hb.1
  | succ n ih =>
    obtain ⟨P, hP⟩ : Z.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    have hjP : ∀ w, j w ≠ P := fun w h ↦ by
      have : j w ∈ Zᶜ := hrange ▸ mem_range_self w
      exact this (h ▸ hP)
    have hjZ : ∀ w, j w ∉ Z := fun w ↦ by
      have : j w ∈ Zᶜ := hrange ▸ mem_range_self w
      exact this
    -- the space `Y' = Y ∖ {P}` and the remaining punctures
    let j' : C(W, ({P}ᶜ : Set Y)) := ⟨fun w ↦ ⟨j w, hjP w⟩, by fun_prop⟩
    have hj' : IsEmbedding j' := hj.codRestrict ({P}ᶜ : Set Y) hjP
    let Z' : Set ({P}ᶜ : Set Y) := Subtype.val ⁻¹' Z
    have hZ' : Z'.Finite := hZ.preimage Subtype.val_injective.injOn
    have hn' : Z'.ncard = n := by
      have h1 : Z' = Subtype.val ⁻¹' (Z \ {P}) := by
        ext y; simp [Z']
      rw [h1, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
        (fun y hy ↦ ⟨⟨y, hy.2⟩, rfl⟩), Set.ncard_sdiff_singleton_of_mem hP, hn]
      rfl
    have hrange' : range j' = Z'ᶜ := by
      ext y
      simp only [mem_compl_iff, mem_preimage, Z']
      rw [← mem_compl_iff, ← hrange]
      exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, congrArg Subtype.val hw⟩,
        fun ⟨w, hw⟩ ↦ ⟨w, Subtype.ext hw⟩⟩
    have hPV' : ∀ Q ∈ Z', P ∉ V Q.1 := fun Q hQ hPQ ↦ Q.2 (hVZ Q.1 hQ P hP hPQ).symm
    let V' : ({P}ᶜ : Set Y) → Set ({P}ᶜ : Set Y) := fun Q ↦ Subtype.val ⁻¹' V Q.1
    let e' : ∀ Q ∈ Z', V' Q ≃ₜ ball (0 : ℂ) 1 := fun Q hQ ↦
      (homeomorphPreimageVal (V Q.1) (hPV' Q hQ)).trans (e Q.1 hQ)
    obtain ⟨hsurj', hker'⟩ := ih j' hj' Z' hZ' hn' hrange' V'
      (fun Q hQ ↦ (hVo Q.1 hQ).preimage continuous_subtype_val) (fun Q hQ ↦ hPV Q.1 hQ) e'
      (fun Q hQ ↦ he Q.1 hQ)
      (fun Q hQ R hR hRQ ↦ Subtype.ext (hVZ Q.1 hQ R.1 hR hRQ))
    -- filling `P`
    have hU := isPathConnected_compl_singleton j hrange V hPV e he hVZ hP w₀
    obtain ⟨hsurjP, hkerP⟩ := fill_one (e P hP) (hVo P hP) (hPV P hP) (he P hP) hU (j' w₀)
    set φ := FundamentalGroup.map j' w₀
    set ψ := FundamentalGroup.map (complIncl P) (j' w₀)
    have hcomp : ∀ g, FundamentalGroup.map j w₀ g = ψ (φ g) := by
      intro g
      induction g using Quotient.inductionOn
      rfl
    have hcompHom : FundamentalGroup.map j w₀ = ψ.comp φ := MonoidHom.ext hcomp
    refine ⟨fun g ↦ ?_, ?_⟩
    · obtain ⟨y, rfl⟩ := hsurjP g
      obtain ⟨x, rfl⟩ := hsurj' y
      exact ⟨x, hcomp x⟩
    -- the kernel of `ψ` is generated by images of loops of `W`
    have hLP : Subgroup.normalClosure (conjLoops Subtype.val (V P) (j' w₀)) =
        (Subgroup.normalClosure (conjLoops j (V P) w₀)).map φ := by
      rw [Subgroup.map_normalClosure _ _ hsurj']
      apply le_antisymm
      · refine Subgroup.normalClosure_le_normal fun g hg ↦ ?_
        obtain ⟨y, γ, c, hc, rfl⟩ := hg
        have hcZ : ∀ t, (c t : Y) ∉ Z := fun t hct ↦ (c t).2 (hVZ P hP _ hct (hc t))
        obtain ⟨w, rfl⟩ : y ∈ range j' := by
          rw [hrange']
          have := hcZ 0
          rwa [c.source] at this
        let H := hj.toHomeomorph
        have hcr : ∀ t, (c t : Y) ∈ range j := fun t ↦ hrange ▸ hcZ t
        let c₀ : Path w w :=
          { toFun := fun t ↦ H.symm ⟨c t, hcr t⟩
            continuous_toFun := H.symm.continuous.comp
              ((continuous_subtype_val.comp c.continuous).subtype_mk _)
            source' := by
              apply H.injective
              ext
              simp [H, c.source, j']
            target' := by
              apply H.injective
              ext
              simp [H, c.target, j'] }
        have hc₀ : c₀.map j'.continuous = c := by
          ext t
          change ((H (H.symm ⟨c t, hcr t⟩) : range j) : Y) = c t
          rw [Homeomorph.apply_symm_apply]
        let γ₀ : Path w₀ w := PathConnectedSpace.somePath w₀ w
        let m : FundamentalGroup W w₀ :=
          (⟦γ₀⟧ : FundamentalGroupoid.mk w₀ ⟶ FundamentalGroupoid.mk w) ≫ ⟦c₀⟧ ≫ Groupoid.inv ⟦γ₀⟧
        have hm : m ∈ conjLoops j (V P) w₀ := ⟨w, ⟦γ₀⟧, c₀, fun t ↦ by
          change ((H (H.symm ⟨c t, hcr t⟩) : range j) : Y) ∈ V P
          rw [Homeomorph.apply_symm_apply]
          exact hc t, rfl⟩
        have hφm : φ m = (⟦γ₀.map j'.continuous⟧ : FundamentalGroupoid.mk (j' w₀) ⟶
            FundamentalGroupoid.mk (j' w)) ≫ ⟦c⟧ ≫ Groupoid.inv ⟦γ₀.map j'.continuous⟧ := by
          change (FundamentalGroupoid.map j').map ((⟦γ₀⟧ : FundamentalGroupoid.mk w₀ ⟶
            FundamentalGroupoid.mk w) ≫ ⟦c₀⟧ ≫ Groupoid.inv ⟦γ₀⟧) = _
          rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
            Functor.map_inv, ← hc₀]
          rfl
        let hh : FundamentalGroup ({P}ᶜ : Set Y) (j' w₀) :=
          γ ≫ Groupoid.inv ⟦γ₀.map j'.continuous⟧
        have hmem : φ m ∈ Subgroup.normalClosure (φ '' conjLoops j (V P) w₀) :=
          Subgroup.subset_normalClosure ⟨m, hm, rfl⟩
        have := (Subgroup.normalClosure_normal (s := φ '' conjLoops j (V P) w₀)).conj_mem _
          hmem hh⁻¹
        have heq : γ ≫ (⟦c⟧ : FundamentalGroupoid.mk (j' w) ⟶ _) ≫ Groupoid.inv γ =
            hh⁻¹ * φ m * hh⁻¹⁻¹ := by
          rw [hφm]
          change _ = Groupoid.inv (Groupoid.inv hh) ≫ (_ ≫ _ ≫ _) ≫ Groupoid.inv hh
          simp [hh, Groupoid.inv_eq_inv]
        rw [heq]
        exact this
      · exact Subgroup.normalClosure_le_normal fun g ⟨m, hm, hg⟩ ↦
          Subgroup.subset_normalClosure (hg ▸ map_mem_conjLoops j Subtype.val j'
            (fun _ ↦ rfl) hm)
    have hcl' : (⋃ Q ∈ Z', conjLoops j' (V' Q) w₀) = ⋃ Q ∈ Z \ {P}, conjLoops j (V Q) w₀ := by
      ext g
      simp only [mem_iUnion, mem_sdiff, mem_singleton_iff, exists_prop]
      constructor
      · rintro ⟨Q, hQ, hg⟩
        exact ⟨Q.1, ⟨hQ, Q.2⟩, hg⟩
      · rintro ⟨Q, ⟨hQ, hQP⟩, hg⟩
        exact ⟨⟨Q, hQP⟩, hQ, hg⟩
    rw [hcompHom, ← MonoidHom.comap_ker, hkerP, hLP, Subgroup.comap_map_eq, hker', hcl',
      ← Subgroup.normalClosure_union]
    congr 1
    ext g
    simp only [mem_union, mem_iUnion, mem_sdiff, mem_singleton_iff, exists_prop]
    constructor
    · rintro (hg | ⟨Q, ⟨hQ, -⟩, hg⟩)
      · exact ⟨P, hP, hg⟩
      · exact ⟨Q, hQ, hg⟩
    · rintro ⟨Q, hQ, hg⟩
      by_cases hQP : Q = P
      · subst hQP; exact Or.inl hg
      · exact Or.inr ⟨Q, ⟨hQ, hQP⟩, hg⟩

/-- **Filling in finitely many points with disc neighbourhoods.** For an embedding `j : W → Y`
of a path-connected space onto `Y ∖ Z`, `Z` finite, each `P ∈ Z` with an open disc
neighbourhood `V P` (centre `P`, `V P ∩ Z = {P}`), the map `π₁(W, w₀) → π₁(Y, j w₀)` is
surjective with kernel the normal closure of the loops conjugate to loops in the discs. -/
theorem fill_finite {Y : Type*} [TopologicalSpace Y] [T1Space Y] (j : C(W, Y))
    (hj : IsEmbedding j) (Z : Set Y) (hZ : Z.Finite) (hrange : range j = Zᶜ)
    (V : Y → Set Y) (hVo : ∀ P ∈ Z, IsOpen (V P)) (hPV : ∀ P ∈ Z, P ∈ V P)
    (e : ∀ P ∈ Z, V P ≃ₜ ball (0 : ℂ) 1) (he : ∀ P (hP : P ∈ Z), (e P hP ⟨P, hPV P hP⟩ : ℂ) = 0)
    (hVZ : ∀ P ∈ Z, ∀ Q ∈ Z, Q ∈ V P → Q = P) (w₀ : W) :
    Function.Surjective (FundamentalGroup.map j w₀) ∧
      (FundamentalGroup.map j w₀).ker =
        Subgroup.normalClosure (⋃ P ∈ Z, conjLoops j (V P) w₀) :=
  fill_finite_aux _ j hj Z hZ rfl hrange V hVo hPV e he hVZ w₀

end FillFinite

end VanKampen

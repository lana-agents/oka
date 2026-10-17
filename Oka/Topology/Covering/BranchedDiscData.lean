/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.Covering.BranchedOrbits

/-!
# Disc data of a branched covering from charts and properness

Let `X` be a Hausdorff space and `f : X → ℂ` a continuous closed map with finite fibres. Let
`S ⊆ ℂ` be finite, and assume that `f` is a local homeomorphism at every point outside `f⁻¹(S)`
and that every point over `S` has a chart, i.e. lies in the source of a partial homeomorphism
`X → ℂ` with open source and target (for instance `X` the analytification of a smooth curve).
This is the topological situation of a finite branched covering of the plane, and this file
produces the input of `Oka/Topology/Covering/BranchedFill.lean` and
`Oka/Topology/Covering/BranchedOrbits.lean` from it:

* `BranchedCover.nonempty_discData`: disc data (`BranchedCover.DiscData`). Small chart discs
  around the points over `s ∈ S` are pairwise disjoint and mapped into a disc `B(s, ρ)` isolating
  `s`; since `f` is closed, `f⁻¹(B(s, σ))` lies in their union for some `σ ≤ ρ`.
* `BranchedCover.isCoveringMap_punctMap`: `X ∖ f⁻¹(S) → ℂ ∖ S` is a covering map (a closed local
  homeomorphism with finite fibres, `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`).
* `BranchedCover.pathConnectedSpace_punct`: if `X` is connected and locally path connected, so is
  `X ∖ f⁻¹(S)`, since each punctured disc `V P ∖ {P}` is connected. A space covered by charts
  is locally path connected (`BranchedCover.locallyPathConnectedSpace_of_charts`).
* `BranchedCover.exists_fundamentalGroup_mulEquiv_freeGroup_of_charts`: **`π₁(X)` is free of rank
  `d (|S| - 1) + 1 - #f⁻¹(S)`**, `d` the number of points of a fibre over `ℂ ∖ S`
  (`BranchedCover.exists_fundamentalGroup_mulEquiv_freeGroup_card` with the loop basis
  `Complex.exists_isLoopAround_basis` of `π₁(ℂ ∖ S)`).
-/

open Set Metric Topology Complex.PuncturedPlane

namespace BranchedCover

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The affine homeomorphism of a ball `B(c, r)` with the unit ball. -/
noncomputable def ballHomeomorph (c : ℂ) {r : ℝ} (hr : 0 < r) : ball c r ≃ₜ ball (0 : ℂ) 1 where
  toFun z := ⟨(z - c) / r, by
    have hr' : (0 : ℝ) < ‖(r : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]; exact hr
    rw [mem_ball, dist_zero_right, norm_div, div_lt_one hr', Complex.norm_real,
      Real.norm_of_nonneg hr.le, ← dist_eq_norm]
    exact z.2⟩
  invFun w := ⟨c + r * w, by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    have := w.2
    rw [mem_ball, dist_zero_right] at this
    nlinarith⟩
  left_inv z := by
    apply Subtype.ext
    have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    simp only
    field_simp
    ring
  right_inv w := by
    apply Subtype.ext
    have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    simp only
    field_simp
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Chart discs.** A point in the source of a chart `φ : X ⇀ ℂ` has arbitrarily small open
neighbourhoods homeomorphic to the unit disc, with the point at the centre. -/
theorem exists_disc_subset (φ : OpenPartialHomeomorph X ℂ) {P : X} (hP : P ∈ φ.source)
    {U : Set X} (hU : U ∈ 𝓝 P) :
    ∃ (V : Set X) (hPV : P ∈ V), V ⊆ U ∧ IsOpen V ∧
      ∃ e : V ≃ₜ ball (0 : ℂ) 1, (e ⟨P, hPV⟩ : ℂ) = 0 := by
  have hN : φ '' (φ.source ∩ U) ∈ 𝓝 (φ P) := φ.image_mem_nhds hP (Filter.inter_mem
    (φ.open_source.mem_nhds hP) hU)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hN
    (φ.open_target.mem_nhds (φ.map_source hP)))
  set V := φ.source ∩ φ ⁻¹' ball (φ P) r
  have hPV : P ∈ V := ⟨hP, mem_ball_self hr⟩
  have hVU : V ⊆ U := by
    rintro y ⟨hy, hyB⟩
    obtain ⟨y', ⟨hy', hy'U⟩, hyy'⟩ := (hrN hyB).1
    rw [← φ.injOn hy' hy hyy']
    exact hy'U
  have himg : φ '' V = ball (φ P) r := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy.2
    · intro z hz
      refine ⟨φ.symm z, ⟨φ.map_target (hrN hz).2, ?_⟩, φ.right_inv (hrN hz).2⟩
      change φ (φ.symm z) ∈ ball (φ P) r
      rw [φ.right_inv (hrN hz).2]
      exact hz
  let e₁ : V ≃ₜ ball (φ P) r := φ.homeomorphOfImageSubsetSource inter_subset_left himg
  refine ⟨V, hPV, hVU, φ.isOpen_inter_preimage isOpen_ball, e₁.trans (ballHomeomorph _ hr), ?_⟩
  change ((φ P - φ P) / r : ℂ) = 0
  rw [sub_self, zero_div]

/-- **A space covered by charts to `ℂ` is locally path connected.** -/
theorem locallyPathConnectedSpace_of_charts
    (hchart : ∀ P : X, ∃ φ : OpenPartialHomeomorph X ℂ, P ∈ φ.source) :
    LocallyPathConnectedSpace X := by
  choose φ hφ using hchart
  haveI (P : X) : LocallyPathConnectedSpace (φ P).source :=
    haveI : LocallyPathConnectedSpace (φ P).target := (φ P).open_target.locallyPathConnectedSpace
    (φ P).toHomeomorphSourceTarget.isOpenEmbedding.locallyPathConnectedSpace
  let F : (Σ P : X, (φ P).source) → X := fun p ↦ p.2.1
  have hF : Topology.IsQuotientMap F :=
    IsOpenMap.isQuotientMap (isOpenMap_sigma.2 fun P ↦ (φ P).open_source.isOpenMap_subtype_val)
      (continuous_sigma fun P ↦ continuous_subtype_val) (fun P ↦ ⟨⟨P, P, hφ P⟩, rfl⟩)
  exact hF.locallyPathConnectedSpace

variable {f : C(X, ℂ)} {S : Finset ℂ}

/-- Radii isolating the points of a finite set. -/
theorem exists_radius_isolated (S : Finset ℂ) (s : ℂ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s' ∈ S, s' ∈ ball s ρ → s' = s := by
  have hc : IsClosed ((S.erase s : Finset ℂ) : Set ℂ) := (S.erase s).finite_toSet.isClosed
  obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hc.isOpen_compl s (by simp)
  refine ⟨ρ, hρ, fun s' hs' hb ↦ ?_⟩
  by_contra hne
  exact hB hb (Finset.mem_erase.2 ⟨hne, hs'⟩)

/-- **Disc data from charts and properness**: for `X` Hausdorff, `f` closed, `f⁻¹(S)` finite and
charts at the points over `S`, `f` has disc data over `S`. -/
theorem nonempty_discData [T2Space X] (hcl : IsClosedMap f) (hfin : {P | f P ∈ S}.Finite)
    (hchart : ∀ P, f P ∈ S → ∃ φ : OpenPartialHomeomorph X ℂ, P ∈ φ.source) :
    Nonempty (DiscData f S) := by
  classical
  set Z := {P | f P ∈ S}
  choose ρ hρ hρS using exists_radius_isolated S
  obtain ⟨U, hU, hUd⟩ := hfin.t2_separation
  -- neighbourhoods in which the discs are chosen
  let N : X → Set X := fun P ↦ U P ∩ (Z \ {P})ᶜ ∩ f ⁻¹' ball (f P) (ρ (f P))
  have hN : ∀ P, N P ∈ 𝓝 P := fun P ↦ by
    refine IsOpen.mem_nhds ?_ ⟨⟨(hU P).1, fun h ↦ h.2 rfl⟩, mem_ball_self (hρ _)⟩
    exact ((hU P).2.inter (hfin.sdiff.isClosed.isOpen_compl)).inter
      (isOpen_ball.preimage f.continuous)
  have hV : ∀ P, ∃ V : Set X, f P ∈ S → ∃ (hPV : P ∈ V), V ⊆ N P ∧ IsOpen V ∧
      ∃ e : V ≃ₜ ball (0 : ℂ) 1, (e ⟨P, hPV⟩ : ℂ) = 0 := fun P ↦ by
    by_cases hP : f P ∈ S
    · obtain ⟨φ, hφ⟩ := hchart P hP
      obtain ⟨V, hPV, hVN, hVo, e, he⟩ := exists_disc_subset φ hφ (hN P)
      exact ⟨V, fun _ ↦ ⟨hPV, hVN, hVo, e, he⟩⟩
    · exact ⟨∅, fun h ↦ (hP h).elim⟩
  choose V hV using hV
  -- the inner radii, from closedness of `f`
  have hσ : ∀ s, ∃ σ : ℝ, s ∈ S → 0 < σ ∧ σ ≤ ρ s ∧
      ∀ y, f y ∈ ball s σ → ∃ P, f P = s ∧ y ∈ V P := fun s ↦ by
    by_cases hs : s ∈ S
    · let W := ⋃ P ∈ {P | f P = s}, V P
      have hW : IsOpen W := isOpen_biUnion fun P (hP : f P = s) ↦ (hV P (hP ▸ hs)).2.2.1
      have hsW : s ∉ f '' Wᶜ := by
        rintro ⟨y, hyW, hys⟩
        exact hyW (mem_biUnion (x := y) hys (hV y (hys ▸ hs)).1)
      obtain ⟨σ, hσ, hσW⟩ := Metric.isOpen_iff.1 (hcl _ hW.isClosed_compl).isOpen_compl s hsW
      refine ⟨min σ (ρ s), fun _ ↦ ⟨lt_min hσ (hρ s), min_le_right _ _, fun y hy ↦ ?_⟩⟩
      by_contra hne
      push Not at hne
      refine hσW (ball_subset_ball (min_le_left _ _) hy) ⟨y, fun hyW ↦ ?_, rfl⟩
      obtain ⟨P, hP, hyP⟩ := mem_iUnion₂.1 hyW
      exact hne P hP hyP
    · exact ⟨0, fun h ↦ (hs h).elim⟩
  choose σ hσ using hσ
  exact ⟨{
    V := V
    e := fun P hP ↦ ((hV P hP).2.2.2).choose
    ρ := ρ
    finite := hfin
    isOpen := fun P hP ↦ (hV P hP).2.2.1
    mem := fun P hP ↦ (hV P hP).1
    e_center := fun P hP ↦ ((hV P hP).2.2.2).choose_spec
    eq_of_mem := fun P hP y hy hyS ↦ by
      by_contra hne
      exact ((hV P hP).2.1 hy).1.2 ⟨hyS, hne⟩
    disjoint := fun P Q hP hQ hPQ ↦ (hUd hP hQ hPQ).mono
      (fun y hy ↦ ((hV P hP).2.1 hy).1.1) (fun y hy ↦ ((hV Q hQ).2.1 hy).1.1)
    ρ_pos := fun s _ ↦ hρ s
    ρ_isolated := fun s _ ↦ hρS s
    mapsTo := fun P hP y hy ↦ ((hV P hP).2.1 hy).2
    σ := σ
    σ_pos := fun s hs ↦ (hσ s hs).1
    σ_le := fun s hs ↦ (hσ s hs).2.1
    cover := fun y s hs hy ↦ (hσ s hs).2.2 y hy }⟩

/-- **The étale part of a branched covering is a covering map**: for `X` Hausdorff and `f`
closed with finite fibres and a local homeomorphism outside `f⁻¹(S)`, the restriction
`X ∖ f⁻¹(S) → ℂ ∖ S` is a covering map. -/
theorem isCoveringMap_punctMap [T2Space X] (hcl : IsClosedMap f)
    (hfib : ∀ z, (f ⁻¹' {z}).Finite) (hloc : IsLocalHomeomorphOn f {y | f y ∉ S}) :
    IsCoveringMap (punctMap f S) := by
  have hon : IsCoveringMapOn f {z | z ∉ S} :=
    hcl.isCoveringMapOn_of_isLocalHomeomorphOn (fun z _ ↦ hfib z) hloc
  have h₁ := hon.isCoveringMap_restrictPreimage
  let g : ({z | z ∉ S} : Set ℂ) ≃ₜ Region Set.univ S :=
    { toFun := fun z ↦ ⟨z.1, trivial, z.2⟩
      invFun := fun z ↦ ⟨z.1, z.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact h₁.homeomorph_comp g

variable (D : DiscData f S)

include D in
/-- A punctured disc `V P ∖ {P}` lies outside `f⁻¹(S)`. -/
theorem notMem_of_mem_disc_diff {P : X} (hP : f P ∈ S) {y : X} (hy : y ∈ D.V P \ {P}) :
    f y ∉ S :=
  fun hS ↦ hy.2 (D.eq_of_mem P hP y hy.1 hS)

include D in
/-- **Removing the branch points keeps a connected space connected**: if `X` is connected, so is
`X ∖ f⁻¹(S)`. -/
theorem isConnected_punct [ConnectedSpace X] : IsConnected {y : X | f y ∉ S} := by
  classical
  set O := {y : X | f y ∉ S}
  have hO : IsOpen O := (S.finite_toSet.isClosed.preimage f.continuous).isOpen_compl
  have hdisc : ∀ P, f P ∈ S → (D.V P \ {P}).Nonempty ∧ IsConnected (D.V P \ {P}) ∧
      D.V P \ {P} ⊆ O := fun P hP ↦
    ⟨(exists_mem_disc_ne_of_mem D hP isOpen_univ (mem_univ P)).imp fun _ h ↦ h.1,
      (VanKampen.isPathConnected_diff_of_disc (D.e P hP) (D.mem P hP)
        (D.e_center P hP)).isConnected,
      fun _ hy ↦ notMem_of_mem_disc_diff D hP hy⟩
  have hne : O.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    by_cases hx : f x ∈ S
    · obtain ⟨y, hy⟩ := (hdisc x hx).1
      exact ⟨y, (hdisc x hx).2.2 hy⟩
    · exact ⟨x, hx⟩
  refine ⟨hne, fun u v hu hv hOuv hOu hOv ↦ ?_⟩
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  set u₀ := u ∩ O
  set v₀ := v ∩ O
  have hd₀ : Disjoint u₀ v₀ := by
    rw [Set.disjoint_iff_inter_eq_empty]
    rw [← hempty]
    ext y
    simp only [u₀, v₀, mem_inter_iff]
    tauto
  have hsplit : ∀ P, f P ∈ S → D.V P \ {P} ⊆ u₀ ∨ D.V P \ {P} ⊆ v₀ := fun P hP ↦ by
    obtain ⟨hn, hc, hsub⟩ := hdisc P hP
    have hcov : D.V P \ {P} ⊆ u₀ ∪ v₀ := fun y hy ↦ by
      rcases hOuv (hsub hy) with h | h
      · exact Or.inl ⟨h, hsub hy⟩
      · exact Or.inr ⟨h, hsub hy⟩
    obtain ⟨y, hy⟩ := hn
    rcases hcov hy with h | h
    · exact Or.inl (hc.isPreconnected.subset_left_of_subset_union (hu.inter hO) (hv.inter hO)
        hd₀ hcov ⟨y, hy, h⟩)
    · exact Or.inr (hc.isPreconnected.subset_right_of_subset_union (hu.inter hO) (hv.inter hO)
        hd₀ hcov ⟨y, hy, h⟩)
  let u' := u₀ ∪ ⋃ P ∈ {P | f P ∈ S ∧ D.V P \ {P} ⊆ u₀}, D.V P
  let v' := v₀ ∪ ⋃ P ∈ {P | f P ∈ S ∧ D.V P \ {P} ⊆ v₀}, D.V P
  have hu' : IsOpen u' := (hu.inter hO).union (isOpen_biUnion fun P hP ↦ D.isOpen P hP.1)
  have hv' : IsOpen v' := (hv.inter hO).union (isOpen_biUnion fun P hP ↦ D.isOpen P hP.1)
  have hcover : univ ⊆ u' ∪ v' := fun y _ ↦ by
    by_cases hy : f y ∈ S
    · rcases hsplit y hy with h | h
      · exact Or.inl (Or.inr (mem_biUnion ⟨hy, h⟩ (D.mem y hy)))
      · exact Or.inr (Or.inr (mem_biUnion ⟨hy, h⟩ (D.mem y hy)))
    · rcases hOuv hy with h | h
      · exact Or.inl (Or.inl ⟨h, hy⟩)
      · exact Or.inr (Or.inl ⟨h, hy⟩)
  -- a punctured disc cannot lie in both halves
  have hboth : ∀ P, f P ∈ S → D.V P \ {P} ⊆ u₀ → D.V P \ {P} ⊆ v₀ → False := fun P hP h₁ h₂ ↦ by
    obtain ⟨y, hy⟩ := (hdisc P hP).1
    exact Set.disjoint_left.1 hd₀ (h₁ hy) (h₂ hy)
  -- a point of `O` in a disc lies in its punctured part
  have hmemO : ∀ P, f P ∈ S → ∀ y ∈ D.V P, y ∈ O → y ∈ D.V P \ {P} := fun P hP y hy hyO ↦
    ⟨hy, fun h ↦ hyO (h ▸ hP)⟩
  have hdisj : (univ ∩ (u' ∩ v')).Nonempty → False := by
    rintro ⟨y, -, hyu, hyv⟩
    rcases hyu with hyu | hyu <;> rcases hyv with hyv | hyv
    · exact Set.disjoint_left.1 hd₀ hyu hyv
    · obtain ⟨Q, ⟨hQ, hQv⟩, hyQ⟩ := mem_iUnion₂.1 hyv
      exact Set.disjoint_left.1 hd₀ hyu (hQv (hmemO Q hQ y hyQ hyu.2))
    · obtain ⟨P, ⟨hP, hPu⟩, hyP⟩ := mem_iUnion₂.1 hyu
      exact Set.disjoint_left.1 hd₀ (hPu (hmemO P hP y hyP hyv.2)) hyv
    · obtain ⟨P, ⟨hP, hPu⟩, hyP⟩ := mem_iUnion₂.1 hyu
      obtain ⟨Q, ⟨hQ, hQv⟩, hyQ⟩ := mem_iUnion₂.1 hyv
      by_cases hPQ : P = Q
      · subst hPQ
        exact hboth P hP hPu hQv
      · exact Set.disjoint_left.1 (D.disjoint P Q hP hQ hPQ) hyP hyQ
  obtain ⟨y, hyO, hyu⟩ := hOu
  obtain ⟨z, hzO, hzv⟩ := hOv
  exact hdisj (isPreconnected_univ u' v' hu' hv' hcover ⟨y, trivial, Or.inl ⟨hyu, hyO⟩⟩
    ⟨z, trivial, Or.inl ⟨hzv, hzO⟩⟩)

include D in
/-- If `X` is connected and locally path connected, `X ∖ f⁻¹(S)` is path connected. -/
theorem pathConnectedSpace_punct [ConnectedSpace X] [LocallyPathConnectedSpace X] :
    PathConnectedSpace (Punct f S) := by
  have hO : IsOpen {y : X | f y ∉ S} :=
    (S.finite_toSet.isClosed.preimage f.continuous).isOpen_compl
  have := (hO.isConnected_iff_isPathConnected.1 (isConnected_punct D))
  exact isPathConnected_iff_pathConnectedSpace.1 this

/-- **`π₁` of a finite branched covering of the plane, from charts**: let `X` be Hausdorff,
connected and locally path connected, `f : X → ℂ` closed with finite fibres, a local
homeomorphism outside `f⁻¹(S)`, with charts at the points over `S`. Then for every base point
`e₀` outside `f⁻¹(S)`, `π₁(X, e₀)` is free of rank `d (|S| - 1) + 1 - #f⁻¹(S)`, where `d` is the
number of points of the fibre through `e₀`. -/
theorem exists_fundamentalGroup_mulEquiv_freeGroup_of_charts [T2Space X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hcl : IsClosedMap f) (hfib : ∀ z, (f ⁻¹' {z}).Finite)
    (hloc : IsLocalHomeomorphOn f {y | f y ∉ S})
    (hchart : ∀ P, f P ∈ S → ∃ φ : OpenPartialHomeomorph X ℂ, P ∈ φ.source)
    (e₀ : X) (he₀ : f e₀ ∉ S) :
    ∃ (ι : Type u) (_ : Finite ι), Nonempty (FundamentalGroup X e₀ ≃* FreeGroup ι) ∧
      Nat.card ι + Nat.card (f ⁻¹' {f e₀}) + Nat.card {P : X // f P ∈ S} =
        Nat.card (f ⁻¹' {f e₀}) * S.card + 1 := by
  have hfin : {P | f P ∈ S}.Finite := by
    have : {P | f P ∈ S} = ⋃ s ∈ S, f ⁻¹' {s} := by ext; simp
    rw [this]
    exact S.finite_toSet.biUnion fun s _ ↦ hfib s
  obtain ⟨D⟩ := nonempty_discData hcl hfin hchart
  have cov := isCoveringMap_punctMap hcl hfib hloc
  haveI := pathConnectedSpace_punct D
  let x : Region Set.univ S := punctMap f S ⟨e₀, he₀⟩
  obtain ⟨g, hg, hbij⟩ := Complex.exists_isLoopAround_basis S x
  let ψ := (MulEquiv.ofBijective (FreeGroup.lift g) hbij).symm
  letI := cov.fundamentalGroupMulAction x
  letI : MulAction (FreeGroup S) (punctMap f S ⁻¹' {x}) := MulAction.compHom _ ψ.symm.toMonoidHom
  have hφ : ∀ (γ : FreeGroup S) (e : punctMap f S ⁻¹' {x}), γ • e = cov.monodromy (ψ.symm γ) e :=
    fun _ _ ↦ rfl
  have hψ : ∀ s : S, IsLoopAround (ψ.symm (FreeGroup.of s)) s := fun s ↦ by
    simp only [ψ, MulEquiv.symm_symm, MulEquiv.ofBijective_apply, FreeGroup.lift_apply_of]
    exact hg s
  -- the fibre of `punctMap` is the fibre of `f`
  let F : punctMap f S ⁻¹' {x} ≃ f ⁻¹' {f e₀} :=
    { toFun := fun e ↦ ⟨e.1.1, congrArg Subtype.val e.2⟩
      invFun := fun y ↦ ⟨⟨y.1, by rw [show f y.1 = f e₀ from y.2]; exact he₀⟩,
        Subtype.ext (show f y.1 = f e₀ from y.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  haveI : Finite (f ⁻¹' {f e₀}) := (hfib _).to_subtype
  haveI : Finite (punctMap f S ⁻¹' {x}) := Finite.of_equiv _ F.symm
  obtain ⟨ι, hι, hiso, hcard⟩ := exists_fundamentalGroup_mulEquiv_freeGroup_card D cov ψ hφ hψ
    ⟨⟨e₀, he₀⟩, rfl⟩
  refine ⟨ι, hι, hiso, ?_⟩
  rw [Nat.card_congr F, Nat.card_eq_fintype_card (α := S), Fintype.card_coe] at hcard
  exact hcard

end BranchedCover

/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.Covering.FreeRank
import Oka.Topology.VanKampen.FillFinite
import Oka.Topology.VanKampen.LoopsAround

/-!
# Filling the punctures of a branched covering of the plane

Let `f : X → ℂ` be continuous, `S ⊆ ℂ` finite, and assume that `f` restricts to a covering map
`p : X ∖ f⁻¹(S) → ℂ ∖ S` with path-connected total space, and that every point `P` over `S` has a
disc neighbourhood `V P` (`BranchedCover.DiscData`) mapped by `f` into a disc `B(f P, ρ)` around
`f P` containing no other point of `S`, such that `f⁻¹(B(s, σ))` is covered by the (pairwise
disjoint) discs `V P` over `s` for some smaller radius `0 < σ ≤ ρ`. This is the topological
situation of a finite branched covering `X → ℂ` (e.g. the analytification of a finite morphism of
smooth curves to `𝔸¹`, étale over `𝔸¹ ∖ S`).

Choose free generators of `π₁(ℂ ∖ S, x) ≅ F(S)` that are loops around the points of `S`
(`Complex.exists_isLoopAround_basis`). Then the kernel of `π₁(X ∖ f⁻¹(S), e₀) → π₁(X, e₀)` is the
preimage of pi1's cusp subgroup (`Pi1.ReidemeisterSchreier.cuspSubgroup`, the normal closure in
the stabiliser of `e₀` of the conjugates of powers of the generators) under
`π₁(X ∖ f⁻¹(S), e₀) ≃* Stab(e₀) ≤ F(S)` (`IsCoveringMap.fundamentalGroupEquivFreeStabilizer`):
`BranchedCover.ker_eq_comap_cuspSubgroup`. Combined with
`IsCoveringMap.exists_quotient_mulEquiv_freeGroup` this computes `π₁(X)` as a free group.

The proof: by `VanKampen.fill_finite` the kernel is the normal closure of the classes of loops
conjugate to loops in the discs `V P ∖ {P}`. Such a loop maps to a loop in the punctured disc
`B(s, ρ) ∖ {s}`, hence to a conjugate of a power of the generator at `s`
(`Complex.PuncturedPlane.exists_eq_conj_zpow`). Conversely, a conjugate `g aᵏ g⁻¹` of a power of
the generator `a` (a loop around `s`, whose circle we may shrink into `B(s, ρ)` by
`Complex.PuncturedPlane.circleArrow_eq_conj`) lying in the stabiliser lifts to `γ' c' γ'⁻¹`, where
`c'` is the closed lift of the `k`-th power of the small circle; `c'` lies in `f⁻¹(B(s, σ))`, hence
(by connectedness) in a single disc `V P`.
-/

open Set Metric Topology CategoryTheory Complex.PuncturedPlane Pi1.ReidemeisterSchreier

namespace Path

variable {Y : Type*} [TopologicalSpace Y] {a : Y} (q : Path a a)

/-- The `n`-th power of a loop for `n : ℕ`, as the path `q ⬝ (q ⬝ ⋯)`. -/
noncomputable def npowLoop : ℕ → Path a a
  | 0 => Path.refl a
  | n + 1 => q.trans (npowLoop n)

/-- The `k`-th power of a loop for `k : ℤ`, as a path. -/
noncomputable def zpowLoop : ℤ → Path a a
  | .ofNat n => q.npowLoop n
  | .negSucc n => (q.npowLoop (n + 1)).symm

theorem zpowLoop_ofNat (n : ℕ) : q.zpowLoop (Int.ofNat n) = q.npowLoop n := rfl

theorem zpowLoop_negSucc (n : ℕ) : q.zpowLoop (Int.negSucc n) = (q.npowLoop (n + 1)).symm := rfl

theorem mem_range_npowLoop (n : ℕ) (t : unitInterval) : q.npowLoop n t ∈ range q := by
  induction n generalizing t with
  | zero => exact ⟨0, by simp [npowLoop]⟩
  | succ n ih =>
    change (q.trans (q.npowLoop n)) t ∈ range q
    rw [Path.trans_apply]
    split_ifs
    · exact mem_range_self _
    · exact ih _

theorem mem_range_zpowLoop (k : ℤ) (t : unitInterval) : q.zpowLoop k t ∈ range q := by
  rcases k with n | n
  · rw [zpowLoop_ofNat]; exact q.mem_range_npowLoop n t
  · rw [zpowLoop_negSucc, Path.symm_apply]; exact q.mem_range_npowLoop _ _

theorem class_npowLoop (n : ℕ) :
    (⟦q.npowLoop n⟧ : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk a) =
      (show FundamentalGroup Y a from ⟦q⟧) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Path.Homotopic.Quotient.mk (q.trans (q.npowLoop n)) = _
    rw [pow_succ, End.mul_def, ← ih]
    rfl

theorem class_zpowLoop (k : ℤ) :
    (⟦q.zpowLoop k⟧ : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk a) =
      (show FundamentalGroup Y a from ⟦q⟧) ^ k := by
  rcases k with n | n
  · rw [zpowLoop_ofNat, class_npowLoop, Int.ofNat_eq_natCast, zpow_natCast]
  · rw [zpowLoop_negSucc, zpow_negSucc, ← class_npowLoop]
    rfl

end Path

namespace BranchedCover

theorem eqToHom_sandwich {C : Type*} [Category C] {a a' b b' : C} (A : a ⟶ b) (M : b ⟶ b)
    (N : b ⟶ a) (ha : a = a') (hb : b = b') :
    eqToHom ha ≫ ((eqToHom ha.symm ≫ A ≫ eqToHom hb) ≫ (eqToHom hb.symm ≫ M ≫ eqToHom hb) ≫
      eqToHom hb.symm ≫ N ≫ eqToHom ha) ≫ eqToHom ha.symm = A ≫ M ≫ N := by
  subst hb ha
  simp

theorem groupoid_inv_eqToHom_conj {C : Type*} [Groupoid C] {a b c d : C} (h₁ : a = b)
    (g : b ⟶ c) (h₂ : c = d) :
    Groupoid.inv (eqToHom h₁ ≫ g ≫ eqToHom h₂) =
      eqToHom h₂.symm ≫ Groupoid.inv g ≫ eqToHom h₁.symm := by
  subst h₁ h₂
  simp

universe u

variable {X : Type u} [TopologicalSpace X] (f : C(X, ℂ)) (S : Finset ℂ)

/-- The complement `X ∖ f⁻¹(S)`. -/
abbrev Punct : Type _ := {y : X // f y ∉ S}

/-- `f` on `X ∖ f⁻¹(S)`, with values in `ℂ ∖ S`. -/
noncomputable def punctMap : C(Punct f S, Region Set.univ S) :=
  ⟨fun y ↦ ⟨f y.1, trivial, y.2⟩, by fun_prop⟩

/-- **Disc data of a branched covering**: disc neighbourhoods `V P` of the points over `S`, and
radii `σ s ≤ ρ s` such that `f` maps `V P` into `B(f P, ρ (f P))`, these discs contain no other
point of `S`, and `f⁻¹(B(s, σ s))` is covered by the pairwise disjoint `V P` with `f P = s`.

(The two radii make the data constructible from disc charts and properness alone,
`BranchedCover.nonempty_discData`: with a single radius, `V P` would have to be a whole
connected component of `f⁻¹(B(s, ρ))`.) -/
structure DiscData where
  /-- The disc neighbourhoods. -/
  V : X → Set X
  /-- The homeomorphisms with the unit disc. -/
  e : ∀ P, f P ∈ S → V P ≃ₜ ball (0 : ℂ) 1
  /-- The radii around the points of `S`. -/
  ρ : ℂ → ℝ
  finite : {P | f P ∈ S}.Finite
  isOpen : ∀ P, f P ∈ S → IsOpen (V P)
  mem : ∀ P, f P ∈ S → P ∈ V P
  e_center : ∀ P (hP : f P ∈ S), (e P hP ⟨P, mem P hP⟩ : ℂ) = 0
  eq_of_mem : ∀ P, f P ∈ S → ∀ y ∈ V P, f y ∈ S → y = P
  disjoint : ∀ P Q, f P ∈ S → f Q ∈ S → P ≠ Q → Disjoint (V P) (V Q)
  ρ_pos : ∀ s ∈ S, 0 < ρ s
  ρ_isolated : ∀ s ∈ S, ∀ s' ∈ S, s' ∈ ball s (ρ s) → s' = s
  mapsTo : ∀ P, f P ∈ S → ∀ y ∈ V P, f y ∈ ball (f P) (ρ (f P))
  /-- The inner radii around the points of `S`. -/
  σ : ℂ → ℝ
  σ_pos : ∀ s ∈ S, 0 < σ s
  σ_le : ∀ s ∈ S, σ s ≤ ρ s
  cover : ∀ y, ∀ s ∈ S, f y ∈ ball s (σ s) → ∃ P, f P = s ∧ y ∈ V P

variable {f S}

/-- `π₁(X ∖ f⁻¹(S)) → π₁(X)` is surjective with kernel the normal closure of the loops in the
discs (`VanKampen.fill_finite`). -/
theorem fill [T1Space X] [PathConnectedSpace (Punct f S)] (D : DiscData f S) (e₀ : Punct f S) :
    Function.Surjective
        (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ e₀) ∧
      (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ e₀).ker =
        Subgroup.normalClosure (⋃ P ∈ {P | f P ∈ S}, VanKampen.conjLoops Subtype.val (D.V P) e₀) :=
  VanKampen.fill_finite ⟨Subtype.val, continuous_subtype_val⟩ IsEmbedding.subtypeVal
    {P | f P ∈ S} D.finite (by ext y; simp) D.V D.isOpen D.mem D.e D.e_center
    (fun P hP Q hQ hQV ↦ D.eq_of_mem P hP Q hQV hQ) e₀

section Main

variable (D : DiscData f S) (cov : IsCoveringMap (punctMap f S)) {x : Region Set.univ S}
  (ψ : FundamentalGroup (Region Set.univ S) x ≃* FreeGroup S)
  (hψ : ∀ s : S, IsLoopAround (ψ.symm (FreeGroup.of s)) s)
  [MulAction (FreeGroup S) (punctMap f S ⁻¹' {x})]
  (hφ : ∀ (g : FreeGroup S) (e : punctMap f S ⁻¹' {x}), g • e = cov.monodromy (ψ.symm g) e)

theorem coe_fundamentalGroupEquivFreeStabilizer (e₀ : punctMap f S ⁻¹' {x})
    (γ : FundamentalGroup (Punct f S) e₀.1) :
    (cov.fundamentalGroupEquivFreeStabilizer ψ hφ e₀ γ : FreeGroup S) =
      ψ (FundamentalGroup.mapOfEq ⟨punctMap f S, cov.continuous⟩ e₀.2 γ) :=
  rfl

/-- The image in `π₁(ℂ ∖ S, x)` of a loop `γ c γ⁻¹` with `c` in a disc over `s` is conjugate to
a power of the generator at `s`. -/
theorem exists_eq_conj_of_mem_conjLoops (hψ : ∀ s : S, IsLoopAround (ψ.symm (FreeGroup.of s)) s)
    (e₀ : punctMap f S ⁻¹' {x}) {P : X} (hP : f P ∈ S) {g : FundamentalGroup (Punct f S) e₀.1}
    (hg : g ∈ VanKampen.conjLoops Subtype.val (D.V P) e₀.1) :
    ∃ (G : FreeGroup S) (k : ℤ),
      (cov.fundamentalGroupEquivFreeStabilizer ψ hφ e₀ g : FreeGroup S) =
        G * FreeGroup.of ⟨f P, hP⟩ ^ k * G⁻¹ := by
  obtain ⟨w, γ, c, hc, rfl⟩ := hg
  let pc : Path (punctMap f S w) (punctMap f S w) := c.map (punctMap f S).continuous
  have hpc : ∀ t, (pc t : ℂ) ∈ ball (f P) (D.ρ (f P)) := fun t ↦ D.mapsTo P hP _ (hc t)
  obtain ⟨k, α, hk⟩ := exists_eq_conj_zpow hP (D.ρ_isolated (f P) hP) (hψ ⟨f P, hP⟩) pc hpc
  set Xs := ψ.symm (FreeGroup.of ⟨f P, hP⟩)
  have hx : FundamentalGroupoid.mk x = FundamentalGroupoid.mk (punctMap f S e₀.1) :=
    congrArg FundamentalGroupoid.mk e₀.2.symm
  let Dd : FundamentalGroup (Region Set.univ S) x :=
    eqToHom hx ≫ (FundamentalGroupoid.map (punctMap f S)).map γ ≫ α
  have hmap : FundamentalGroup.mapOfEq ⟨punctMap f S, cov.continuous⟩ e₀.2
      (γ ≫ ⟦c⟧ ≫ Groupoid.inv γ) = Dd⁻¹ * Xs ^ k * Dd := by
    change eqToHom hx ≫ (FundamentalGroupoid.map (punctMap f S)).map (γ ≫ ⟦c⟧ ≫ Groupoid.inv γ) ≫
      eqToHom hx.symm = Dd ≫ (Xs ^ k) ≫ Groupoid.inv Dd
    have hc' : (FundamentalGroupoid.map (punctMap f S)).map
        (⟦c⟧ : FundamentalGroupoid.mk w ⟶ FundamentalGroupoid.mk w) =
          α ≫ (Xs ^ k) ≫ Groupoid.inv α := hk.trans (conjArrow_apply _ _)
    rw [Functor.map_comp, Functor.map_comp, hc', Groupoid.inv_eq_inv γ, Functor.map_inv]
    simp only [Dd, Groupoid.inv_eq_inv, IsIso.inv_comp, inv_eqToHom, Category.assoc]
    erw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]
    rfl
  refine ⟨(ψ Dd)⁻¹, k, ?_⟩
  rw [coe_fundamentalGroupEquivFreeStabilizer, hmap, map_mul, map_mul, map_inv, map_zpow,
    MulEquiv.apply_symm_apply, inv_inv]

/-- A conjugate of a power of the generator at `s` lying in the stabiliser comes from a loop
`γ c γ⁻¹` with `c` in one of the discs over `s`. -/
theorem exists_mem_conjLoops_of_eq (hψ : ∀ s : S, IsLoopAround (ψ.symm (FreeGroup.of s)) s)
    (e₀ : punctMap f S ⁻¹' {x}) {g : FundamentalGroup (Punct f S) e₀.1} {a : S}
    {G : FreeGroup S} {k : ℤ}
    (hg : (cov.fundamentalGroupEquivFreeStabilizer ψ hφ e₀ g : FreeGroup S) =
      G * FreeGroup.of a ^ k * G⁻¹) :
    ∃ P, f P = a ∧ g ∈ VanKampen.conjLoops Subtype.val (D.V P) e₀.1 := by
  obtain ⟨s, hs⟩ := a
  obtain ⟨r, h, δ, hX⟩ := hψ ⟨s, hs⟩
  -- shrink the circle into `B(s, σ s)`
  have hρ := D.σ_pos s hs
  set r' := min r (D.σ s / 2) with hr'
  have h' : Admissible Set.univ S s r' := ⟨lt_min h.pos (half_pos hρ), subset_univ _,
    fun s' hs' hb ↦ h.isolated s' hs' (closedBall_subset_closedBall (min_le_left _ _) hb)⟩
  obtain ⟨β, hβ⟩ := circleArrow_eq_conj h h'
  let C' : FundamentalGroup (Region Set.univ S) (circleBase h') := circleArrow h'
  set Gh := ψ.symm G
  let A : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (circleBase h') :=
    Groupoid.inv Gh ≫ δ ≫ β
  -- the image of `g` in `π₁(ℂ ∖ S, x)`
  have hpg : FundamentalGroup.mapOfEq ⟨punctMap f S, cov.continuous⟩ e₀.2 g =
      A ≫ (C' ^ k) ≫ Groupoid.inv A := by
    have h1 : FundamentalGroup.mapOfEq ⟨punctMap f S, cov.continuous⟩ e₀.2 g =
        Gh * ψ.symm (FreeGroup.of ⟨s, hs⟩) ^ k * Gh⁻¹ := by
      apply ψ.injective
      rw [← coe_fundamentalGroupEquivFreeStabilizer cov ψ hφ, hg, map_mul, map_mul, map_zpow,
        map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have h2 : ψ.symm (FreeGroup.of ⟨s, hs⟩) = Complex.PuncturedPlane.conjArrow (δ ≫ β) C' := by
      rw [hX, hβ, conjArrow_apply]
      simp [Groupoid.inv_eq_inv]
      rfl
    rw [h1, h2, ← map_zpow, conjArrow_apply]
    change Groupoid.inv Gh ≫ ((δ ≫ β) ≫ (C' ^ k) ≫ Groupoid.inv (δ ≫ β)) ≫ Gh = _
    simp only [A, Groupoid.inv_eq_inv, IsIso.inv_comp, IsIso.inv_inv, Category.assoc]
  clear_value A
  -- the lift `e₁` of the base point of the circle and the closed lift of `C'ᵏ`
  set e₁ := cov.monodromy A e₀
  have hstab : cov.monodromy (FundamentalGroup.mapOfEq ⟨punctMap f S, cov.continuous⟩ e₀.2 g)
      e₀ = e₀ :=
    (cov.mem_monodromyStabilizer_iff_mem_range e₀ _).mpr ⟨g, rfl⟩
  have hinv : cov.monodromy (Groupoid.inv A) e₁ = e₀ := by
    rw [← cov.monodromy_trans_apply]
    change cov.monodromy (A ≫ Groupoid.inv A) e₀ = e₀
    rw [Groupoid.comp_inv]
    exact congrFun cov.monodromy_refl e₀
  have hmono : cov.monodromy (C' ^ k) e₁ = e₁ := by
    apply (cov.monodromy_bijective (Groupoid.inv A)).1
    rw [hinv, ← cov.monodromy_trans_apply, ← cov.monodromy_trans_apply]
    change cov.monodromy (A ≫ (C' ^ k) ≫ Groupoid.inv A) e₀ = e₀
    rw [← hpg]
    exact hstab
  let cpk : Path (circleBase h') (circleBase h') := (circlePath h').zpowLoop k
  have hcpk : (⟦cpk⟧ : FundamentalGroupoid.mk (circleBase h') ⟶ _) = C' ^ k :=
    (circlePath h').class_zpowLoop k
  have hcpkB : ∀ t, (cpk t : ℂ) ∈ ball s (D.σ s) := by
    intro t
    obtain ⟨t', ht'⟩ := (circlePath h').mem_range_zpowLoop k t
    rw [← ht', coe_circlePath, mem_ball, dist_eq_norm, norm_circleFun_sub s h'.pos.le]
    exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ)
  have h0 : cpk.toContinuousMap 0 = punctMap f S e₁.1 := cpk.source.trans e₁.2.symm
  let L₀ := cov.liftPath cpk.toContinuousMap e₁.1 h0
  have hL₀ : ∀ t, punctMap f S (L₀ t) = cpk t := fun t ↦
    congrFun (cov.liftPath_lifts cpk.toContinuousMap e₁.1 h0) t
  have hL₁ : L₀ 1 = e₁.1 := by
    have : (cov.monodromy (⟦cpk⟧ : Path.Homotopic.Quotient _ (circleBase h')) e₁).1 = L₀ 1 := rfl
    rw [← this]
    change (cov.monodromy (⟦cpk⟧ : FundamentalGroupoid.mk (circleBase h') ⟶ _) e₁).1 =
      e₁.1
    rw [hcpk]
    exact congrArg Subtype.val hmono
  let L : Path e₁.1 e₁.1 := ⟨L₀, cov.liftPath_zero .., hL₁⟩
  have hLf : ∀ t, f (L t).1 ∈ ball s (D.σ s) := fun t ↦ by
    have := hL₀ t
    have hfe : (punctMap f S (L₀ t) : ℂ) = f (L₀ t).1 := rfl
    change f (L₀ t).1 ∈ _
    rw [← hfe, this]
    exact hcpkB t
  -- `L` stays in one disc
  obtain ⟨P₀, hP₀s, hP₀⟩ := D.cover (L 0).1 s hs (hLf 0)
  have hP₀S : f P₀ ∈ S := hP₀s ▸ hs
  have hall : ∀ t, (L t).1 ∈ D.V P₀ := by
    let T := {t | (L t).1 ∈ D.V P₀}
    have hTo : IsOpen T := (D.isOpen P₀ hP₀S).preimage (continuous_subtype_val.comp L.continuous)
    have hTc : IsClosed T := by
      rw [← isOpen_compl_iff]
      have : Tᶜ = ⋃ Q ∈ {Q | f Q = s ∧ Q ≠ P₀}, {t | (L t).1 ∈ D.V Q} := by
        ext t
        simp only [mem_compl_iff, mem_setOf_eq, mem_iUnion, exists_prop, T]
        constructor
        · intro ht
          obtain ⟨Q, hQs, hQ⟩ := D.cover (L t).1 s hs (hLf t)
          exact ⟨Q, ⟨hQs, fun hQP ↦ ht (hQP ▸ hQ)⟩, hQ⟩
        · rintro ⟨Q, ⟨hQs, hQP⟩, hQ⟩ ht
          exact Set.disjoint_left.mp (D.disjoint Q P₀ (hQs ▸ hs) hP₀S hQP) hQ ht
      rw [this]
      exact isOpen_biUnion fun Q hQ ↦
        (D.isOpen Q (hQ.1 ▸ hs)).preimage (continuous_subtype_val.comp L.continuous)
    have := IsClopen.eq_univ ⟨hTc, hTo⟩ ⟨0, hP₀⟩
    exact fun t ↦ (this ▸ mem_univ t : t ∈ T)
  refine ⟨P₀, hP₀s, ?_⟩
  -- `g` is the lift `Ã ≫ L ≫ Ã⁻¹`
  let Ã : FundamentalGroupoid.mk e₀.1 ⟶ FundamentalGroupoid.mk e₁.1 := cov.liftPathQuotient A e₀
  have he₀ : punctMap f S e₀.1 = x := e₀.2
  have he₁ : punctMap f S e₁.1 = circleBase h' := e₁.2
  have hgL : g = Ã ≫ ⟦L⟧ ≫ Groupoid.inv Ã := by
    apply cov.mapOfEq_injective e₀
    rw [hpg]
    have hÃ : (FundamentalGroupoid.map ⟨punctMap f S, cov.continuous⟩).map Ã =
        eqToHom (congrArg FundamentalGroupoid.mk he₀) ≫ A ≫
          eqToHom (congrArg FundamentalGroupoid.mk he₁.symm) := by
      rw [FundamentalGroupoid.conj_eqToHom]
      exact cov.map_liftPathQuotient A e₀
    have hLm : (FundamentalGroupoid.map ⟨punctMap f S, cov.continuous⟩).map
        (⟦L⟧ : FundamentalGroupoid.mk e₁.1 ⟶ FundamentalGroupoid.mk e₁.1) =
        eqToHom (congrArg FundamentalGroupoid.mk he₁) ≫ (C' ^ k) ≫
          eqToHom (congrArg FundamentalGroupoid.mk he₁.symm) := by
      rw [← hcpk]
      refine Eq.trans ?_ (FundamentalGroupoid.conj_eqToHom
        (p := (⟦cpk⟧ : Path.Homotopic.Quotient _ _)) e₁.2 e₁.2).symm
      change Path.Homotopic.Quotient.mk (L.map cov.continuous) =
        (Path.Homotopic.Quotient.mk cpk).cast e₁.2 e₁.2
      rw [← Path.Homotopic.Quotient.mk_cast]
      congr 1
      ext t
      exact congrArg Subtype.val (hL₀ t)
    have hÃinv : (FundamentalGroupoid.map ⟨punctMap f S, cov.continuous⟩).map
        (Groupoid.inv Ã) = eqToHom (congrArg FundamentalGroupoid.mk he₁) ≫ Groupoid.inv A ≫
          eqToHom (congrArg FundamentalGroupoid.mk he₀.symm) := by
      have : (FundamentalGroupoid.map ⟨punctMap f S, cov.continuous⟩).map (Groupoid.inv Ã) =
          Groupoid.inv ((FundamentalGroupoid.map ⟨punctMap f S, cov.continuous⟩).map Ã) := by
        rw [Groupoid.inv_eq_inv, Functor.map_inv, Groupoid.inv_eq_inv]
      rw [this, hÃ]
      exact groupoid_inv_eqToHom_conj _ _ _
    change _ = eqToHom (congrArg FundamentalGroupoid.mk he₀.symm) ≫
      (FundamentalGroupoid.map ⟨punctMap f S, cov.continuous⟩).map
        (Ã ≫ ⟦L⟧ ≫ Groupoid.inv Ã) ≫ eqToHom (congrArg FundamentalGroupoid.mk he₀)
    rw [Functor.map_comp, Functor.map_comp, hÃ, hLm, hÃinv]
    exact (eqToHom_sandwich (C := FundamentalGroupoid (Region Set.univ S)) A (C' ^ k)
      (Groupoid.inv A) _ _).symm
  exact ⟨e₁.1, Ã, L, hall, hgL⟩

include D in
/-- **Filling the punctures of a branched covering kills exactly the cusp subgroup**: the kernel
of `π₁(X ∖ f⁻¹(S), e₀) → π₁(X, e₀)` is the preimage of `cuspSubgroup S e₀` under
`π₁(X ∖ f⁻¹(S), e₀) ≃* Stab(e₀) ≤ F(S)`. -/
theorem ker_eq_comap_cuspSubgroup [T1Space X] [PathConnectedSpace (Punct f S)]
    (hψ : ∀ s : S, IsLoopAround (ψ.symm (FreeGroup.of s)) s) (e₀ : punctMap f S ⁻¹' {x}) :
    (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ e₀.1).ker =
      (cuspSubgroup (Set.univ : Set S) e₀).comap
        (cov.fundamentalGroupEquivFreeStabilizer ψ hφ e₀).toMonoidHom := by
  rw [(fill D e₀.1).2, MulEquiv.toMonoidHom_eq_coe, cuspSubgroup, ← Subgroup.comap_normalClosure]
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal fun g hg ↦ ?_
    simp only [mem_iUnion, mem_setOf_eq, exists_prop] at hg
    obtain ⟨P, hP, hg⟩ := hg
    obtain ⟨G, k, hk⟩ := exists_eq_conj_of_mem_conjLoops D cov ψ hφ hψ e₀ hP hg
    exact Subgroup.subset_normalClosure ⟨⟨f P, hP⟩, mem_univ _, G, k, hk⟩
  · refine Subgroup.normalClosure_le_normal fun g hg ↦ ?_
    obtain ⟨a, -, G, k, hk⟩ := hg
    obtain ⟨P, hPa, hgP⟩ := exists_mem_conjLoops_of_eq D cov ψ hφ hψ e₀ hk
    refine Subgroup.subset_normalClosure ?_
    simp only [mem_iUnion, mem_setOf_eq, exists_prop]
    exact ⟨P, hPa ▸ a.2, hgP⟩

include D cov hφ in
/-- **`π₁` of a finite branched covering of the plane is free**: with `d` sheets over `ℂ ∖ S`,
`π₁(X, e₀)` is free of rank `d (|S| - 1) + 1 - ∑_{s ∈ S} #(⟨x_s⟩-orbits on the fibre)`. -/
theorem exists_fundamentalGroup_mulEquiv_freeGroup [T1Space X] [PathConnectedSpace (Punct f S)]
    [Finite (punctMap f S ⁻¹' {x})]
    (hψ : ∀ s : S, IsLoopAround (ψ.symm (FreeGroup.of s)) s) (e₀ : punctMap f S ⁻¹' {x}) :
    ∃ (ι : Type u) (_ : Finite ι), Nonempty (FundamentalGroup X e₀.1.1 ≃* FreeGroup ι) ∧
      Nat.card ι + Nat.card (punctMap f S ⁻¹' {x}) +
        ∑ a : S, Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (FreeGroup.of a))
          (punctMap f S ⁻¹' {x})) =
        Nat.card (punctMap f S ⁻¹' {x}) * Nat.card S + 1 := by
  obtain ⟨ι, hι, ⟨Φ⟩, hcard⟩ := cov.exists_quotient_mulEquiv_freeGroup ψ hφ e₀ Finset.univ
  obtain ⟨hsurj, -⟩ := fill D e₀.1
  have hker := ker_eq_comap_cuspSubgroup D cov ψ hφ hψ e₀
  rw [Finset.coe_univ] at Φ
  refine ⟨ι, hι, ⟨?_⟩, hcard⟩
  exact ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans Φ

end Main

end BranchedCover

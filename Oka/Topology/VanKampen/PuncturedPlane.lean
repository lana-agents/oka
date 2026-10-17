/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.Basic
import Oka.Analysis.Complex.FundamentalGroup
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The fundamental group of the plane minus finitely many points is free

For a finite set `S ⊆ ℂ` with `n` elements and any base point `x ∈ ℂ ∖ S`,
`π₁(ℂ ∖ S, x) ≅ F_n`, the free group of rank `n`
(`Complex.nonempty_fundamentalGroup_compl_finset_mulEquiv`).

## Proof

Induction on `n` (milestone T2 of the PI1TOP plan). For `n = 0` the plane is contractible; for
`n = 1` the translation `z ↦ z - a` identifies `ℂ ∖ {a}` with `ℂ ∖ {0}`, whose fundamental group
is `ℤ` (`Complex.fundamentalGroupPuncturedEquivInt`). For `n ≥ 2` choose two points `a ≠ b` of
`S` and the linear form `ℓ z = Re (w z)` with `w = conj (b - a)`, which separates `a` from `b`.
Between two consecutive values of `ℓ` on `S` there is an open strip `c₁ < ℓ < c₂` free of points
of `S`, and the Seifert–van Kampen theorem in the form `VanKampen.coprodEquiv` applies to the
cover of `ℂ ∖ S` by `{ℓ < c₂} ∖ S` and `{ℓ > c₁} ∖ S`, whose intersection is the (convex, hence
simply connected) strip. Each half plane is homeomorphic to `ℂ` (`ℓ ↦ -log (c - ℓ)` in the
`ℓ`-direction), carrying the points of `S` in it to a finite set with fewer points; and the free
product of free groups of ranks `n₁`, `n₂` is free of rank `n₁ + n₂`
(`Complex.PuncturedPlane.coprodFreeGroupEquiv`).

## References

* [A. Hatcher, *Algebraic Topology*, §1.2][hatcher02]
-/

open Set Topology

namespace Complex.PuncturedPlane

/-! ### Transport along homeomorphisms and base point changes -/

/-- Homeomorphic spaces have isomorphic fundamental groups. -/
noncomputable def fundamentalGroupMulEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MonoidHom.toMulEquiv (FundamentalGroup.map (e : C(X, Y)) x)
    (FundamentalGroup.mapOfEq (e.symm : C(Y, X)) (e.symm_apply_apply x))
    (by
      ext p
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, FundamentalGroup.mapOfEq_apply]
      induction p using Quotient.inductionOn with
      | h γ =>
        change (⟦((γ.map e.continuous).map e.symm.continuous).cast _ _⟧ :
          Path.Homotopic.Quotient x x) = ⟦γ⟧
        congr 1
        ext t
        exact e.symm_apply_apply (γ t))
    (by
      ext p
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      induction p using Quotient.inductionOn with
      | h γ =>
        rw [FundamentalGroup.mapOfEq_apply]
        change (⟦(((γ.map e.symm.continuous).cast _ _).map e.continuous)⟧ :
          Path.Homotopic.Quotient (e x) (e x)) = ⟦γ⟧
        congr 1
        ext t
        simp)

/-- In a path connected space, the fundamental groups at any two points are isomorphic. -/
theorem nonempty_mulEquiv_of_isPathConnected {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x y : X) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup X y) :=
  ⟨FundamentalGroup.fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x y)⟩

/-! ### Free groups -/

/-- `F_1 ≅ ℤ`. -/
noncomputable def freeGroupFinOneEquiv : FreeGroup (Fin 1) ≃* Multiplicative ℤ :=
  MonoidHom.toMulEquiv (FreeGroup.lift fun _ => Multiplicative.ofAdd 1)
    (zpowersHom _ (FreeGroup.of 0))
    (FreeGroup.ext_hom _ _ fun i => by
      fin_cases i
      simp)
    (MonoidHom.ext_mint (by simp))

/-- The free product of free groups is free on the disjoint union of the bases. -/
noncomputable def coprodFreeGroupEquiv {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
    {ι : I → Type*} (e : ∀ i, G i ≃* FreeGroup (ι i)) :
    Monoid.CoprodI G ≃* FreeGroup (Σ i, ι i) :=
  MonoidHom.toMulEquiv
    (Monoid.CoprodI.lift fun i => (FreeGroup.map (Sigma.mk i)).comp (e i).toMonoidHom)
    (FreeGroup.lift fun p => Monoid.CoprodI.of ((e p.1).symm (FreeGroup.of p.2)))
    (Monoid.CoprodI.ext_hom _ _ fun i => by
      apply MonoidHom.ext
      intro g
      obtain ⟨w, rfl⟩ := (e i).symm.surjective g
      simp only [MonoidHom.comp_apply, Monoid.CoprodI.lift_of, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, MonoidHom.id_apply]
      induction w using FreeGroup.induction_on with
      | C1 => simp
      | of x => simp
      | inv_of x _ => simp
      | mul x y hx hy => simp only [map_mul, hx, hy])
    (FreeGroup.ext_hom _ _ fun p => by simp)

/-- The free product of free groups of finite ranks `n i` is free of rank `∑ n i`. -/
theorem nonempty_coprod_mulEquiv {G : Bool → Type*} [∀ i, Group (G i)] (n : Bool → ℕ)
    (e : ∀ i, G i ≃* FreeGroup (Fin (n i))) :
    Nonempty (Monoid.CoprodI G ≃* FreeGroup (Fin (n true + n false))) := by
  have hc : Fintype.card (Σ i, Fin (n i)) = n true + n false := by
    simp [Fintype.card_sigma, add_comm]
  exact ⟨(coprodFreeGroupEquiv e).trans
    (FreeGroup.freeGroupCongr (Fintype.equivFinOfCardEq hc))⟩

/-! ### Half planes and punctured pieces -/

lemma continuous_mk : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) :=
  Complex.equivRealProdCLM.symm.continuous

/-- The open half plane `{Re (w z) < c}` is homeomorphic to `ℂ`. -/
noncomputable def halfPlaneHomeomorph (w : ℂ) (hw : w ≠ 0) (c : ℝ) :
    {z : ℂ // (w * z).re < c} ≃ₜ ℂ where
  toFun z := ⟨-Real.log (c - (w * z.1).re), (w * z.1).im⟩
  invFun y := ⟨w⁻¹ * ⟨c - Real.exp (-y.re), y.im⟩, by
    rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
    simp [Real.exp_pos]⟩
  left_inv z := by
    apply Subtype.ext
    have h : 0 < c - (w * z.1).re := sub_pos.mpr z.2
    simp only [neg_neg, Real.exp_log h, sub_sub_cancel]
    rw [Complex.eta, inv_mul_cancel_left₀ hw]
  right_inv y := by
    have h : w * (w⁻¹ * (⟨c - Real.exp (-y.re), y.im⟩ : ℂ)) = ⟨c - Real.exp (-y.re), y.im⟩ := by
      rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
    simp only [h, sub_sub_cancel, Real.log_exp, neg_neg]
  continuous_toFun := by
    refine Continuous.comp continuous_mk
      (Continuous.prodMk ?_ ?_)
    · refine (Continuous.log (by fun_prop) fun z => ?_).neg
      exact (sub_pos.mpr z.2).ne'
    · fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    refine continuous_const.mul ?_
    exact continuous_mk.comp
      (Continuous.prodMk (by fun_prop) (by fun_prop))

open Classical in
/-- Removing finitely many points from a space homeomorphic to `ℂ`. -/
theorem exists_compl_homeomorph {A : Set ℂ} (Φ : A ≃ₜ ℂ) (S : Finset ℂ) :
    ∃ S' : Finset ℂ, S'.card = (S.filter (· ∈ A)).card ∧
      Nonempty ({z : A // (z : ℂ) ∉ S} ≃ₜ {y : ℂ // y ∉ S'}) := by
  let f : (S.filter (· ∈ A)) → ℂ := fun s => Φ ⟨s.1, (Finset.mem_filter.1 s.2).2⟩
  have hf : Function.Injective f := fun s t h =>
    Subtype.ext (congrArg (Subtype.val : A → ℂ) (Φ.injective h))
  refine ⟨(S.filter (· ∈ A)).attach.image f, ?_, ⟨Φ.subtype fun z => ?_⟩⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
  · simp only [Finset.mem_image, Finset.mem_attach, true_and, not_exists]
    constructor
    · intro hz s hs
      apply hz
      have := Φ.injective hs
      rw [← this]
      exact (Finset.mem_filter.1 s.2).1
    · intro h hz
      exact h ⟨(z : ℂ), Finset.mem_filter.2 ⟨hz, z.2⟩⟩ rfl

/-- `{x : {z // p z} // q x} ≃ₜ {x : {z // q z} // p x}` for predicates on a space. -/
def subtypeSwap {Y : Type*} [TopologicalSpace Y] (p q : Y → Prop) :
    {x : {z : Y // p z} // q x.1} ≃ₜ {x : {z : Y // q z} // p x.1} where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `ℂ` minus a finite set is path connected. -/
theorem pathConnectedSpace_compl (S : Finset ℂ) : PathConnectedSpace {z : ℂ // z ∉ S} := by
  have h := (S.countable_toSet).isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
  exact isPathConnected_iff_pathConnectedSpace.mp h

/-! ### The induction -/

/-- The statement for `n` points: `π₁(ℂ ∖ S, x) ≅ F_n` whenever `|S| = n`. -/
def Statement (n : ℕ) : Prop :=
  ∀ S : Finset ℂ, S.card = n → ∀ x : {z : ℂ // z ∉ S},
    Nonempty (FundamentalGroup {z : ℂ // z ∉ S} x ≃* FreeGroup (Fin n))

theorem statement_zero : Statement 0 := by
  intro S hS x
  rw [Finset.card_eq_zero] at hS
  subst hS
  haveI : ContractibleSpace {z : ℂ // z ∉ (∅ : Finset ℂ)} :=
    Convex.contractibleSpace (s := {z : ℂ | z ∉ (∅ : Finset ℂ)}) (by simpa using convex_univ)
      ⟨0, by simp⟩
  haveI : SimplyConnectedSpace {z : ℂ // z ∉ (∅ : Finset ℂ)} :=
    SimplyConnectedSpace.ofContractible _
  letI : Unique (FundamentalGroup {z : ℂ // z ∉ (∅ : Finset ℂ)} x) := uniqueOfSubsingleton 1
  exact ⟨MulEquiv.ofUnique⟩

theorem statement_one : Statement 1 := by
  intro S hS x
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
  let T : {z : ℂ // z ∉ ({a} : Finset ℂ)} ≃ₜ {z : ℂ // z ≠ 0} :=
    (Homeomorph.addRight (-a)).subtype fun z => by
      simp [Finset.mem_singleton, ← sub_eq_add_neg, sub_eq_zero]
  let y := T x
  have hy : (⟨Complex.exp (Complex.log y), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) = y :=
    Subtype.ext (Complex.exp_log y.2)
  exact ⟨(fundamentalGroupMulEquiv T x).trans
    ((Complex.fundamentalGroupPuncturedEquivInt y ⟨Complex.log y, hy⟩).trans
      freeGroupFinOneEquiv.symm)⟩

/-- The linear form `z ↦ Re (w z)` is `ℝ`-linear. -/
lemma isLinearMap_re_mul (w : ℂ) : IsLinearMap ℝ fun z : ℂ => (w * z).re :=
  ⟨fun z₁ z₂ => by simp [mul_add], fun r z => by simp [mul_left_comm w (r : ℂ) z]⟩

lemma continuous_re_mul (w : ℂ) : Continuous fun z : ℂ => (w * z).re := by fun_prop

/-- `π₁` of `{Re (w z) < c} ∖ S` (as a subspace of `ℂ ∖ S`) is free, by induction. -/
theorem piece_lt {n : ℕ} (ih : ∀ m < n, Statement m) (S : Finset ℂ) (w : ℂ) (hw : w ≠ 0)
    (c : ℝ) (hc : (S.filter fun s => (w * s).re < c).card < n)
    (U : Set {z : ℂ // z ∉ S}) (hU : U = {x | (w * x.1).re < c}) (x : U) :
    PathConnectedSpace U ∧ Nonempty (FundamentalGroup U x ≃*
      FreeGroup (Fin (S.filter fun s => (w * s).re < c).card)) := by
  subst hU
  obtain ⟨S', hS', ⟨Ψ⟩⟩ := exists_compl_homeomorph (halfPlaneHomeomorph w hw c) S
  let A : {x : {z : ℂ // z ∉ S} // (w * x.1).re < c} ≃ₜ
      {z : {z : ℂ // (w * z).re < c} // (z : ℂ) ∉ S} :=
    subtypeSwap (fun z : ℂ => z ∉ S) (fun z : ℂ => (w * z).re < c)
  let B := A.trans Ψ
  have hcard : S'.card = (S.filter fun s => (w * s).re < c).card := by
    rw [hS']
    rfl
  haveI := pathConnectedSpace_compl S'
  refine ⟨B.symm.surjective.pathConnectedSpace B.symm.continuous, ?_⟩
  obtain ⟨e⟩ := ih _ hc S' hcard (B x)
  exact ⟨(fundamentalGroupMulEquiv B x).trans (hcard ▸ e)⟩

theorem piece_gt {n : ℕ} (ih : ∀ m < n, Statement m) (S : Finset ℂ) (w : ℂ) (hw : w ≠ 0)
    (c : ℝ) (hc : (S.filter fun s => c < (w * s).re).card < n)
    (U : Set {z : ℂ // z ∉ S}) (hU : U = {x | c < (w * x.1).re}) (x : U) :
    PathConnectedSpace U ∧ Nonempty (FundamentalGroup U x ≃*
      FreeGroup (Fin (S.filter fun s => c < (w * s).re).card)) := by
  have hf : (S.filter fun s => c < (w * s).re) = S.filter fun s => (-w * s).re < -c := by
    apply Finset.filter_congr
    intro s _
    rw [neg_mul, Complex.neg_re, neg_lt_neg_iff]
  have hU' : U = {x | (-w * x.1).re < -c} := by
    rw [hU]
    ext x
    simp only [Set.mem_setOf_eq]
    rw [neg_mul, Complex.neg_re, neg_lt_neg_iff]
  rw [hf] at hc ⊢
  exact piece_lt ih S (-w) (neg_ne_zero.mpr hw) (-c) hc U hU' x

/-- **The induction step**: `n ≥ 2` points are split by a strip into two smaller sets. -/
theorem statement_step {n : ℕ} (hn : 2 ≤ n) (ih : ∀ m < n, Statement m) : Statement n := by
  intro S hS x
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  set w := (starRingEnd ℂ) (b - a) with hwdef
  have hw : w ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr hab.symm)
  set ℓ : ℂ → ℝ := fun z => (w * z).re with hℓ
  have hℓab : ℓ a < ℓ b := by
    have : ℓ b - ℓ a = Complex.normSq (b - a) := by
      have h1 : ℓ b - ℓ a = (w * (b - a)).re := by simp [hℓ, mul_sub]
      rw [h1, hwdef, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    have hpos : 0 < Complex.normSq (b - a) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hab.symm)
    linarith
  set T := S.filter fun s => ℓ s < ℓ b with hT
  have haT : a ∈ T := Finset.mem_filter.mpr ⟨ha, hℓab⟩
  set t₀ := T.sup' ⟨a, haT⟩ ℓ with ht₀
  have ht₀b : t₀ < ℓ b := by
    obtain ⟨s, hs, hst⟩ := Finset.exists_mem_eq_sup' ⟨a, haT⟩ ℓ
    rw [← ht₀] at hst
    rw [hst]
    exact (Finset.mem_filter.mp hs).2
  have hgap : ∀ s ∈ S, ℓ s ≤ t₀ ∨ ℓ b ≤ ℓ s := by
    intro s hs
    by_cases h : ℓ s < ℓ b
    · exact Or.inl (Finset.le_sup' ℓ (Finset.mem_filter.mpr ⟨hs, h⟩))
    · exact Or.inr (not_lt.mp h)
  set c₁ := (2 * t₀ + ℓ b) / 3 with hc₁
  set c₂ := (t₀ + 2 * ℓ b) / 3 with hc₂
  have h01 : t₀ < c₁ := by rw [hc₁]; linarith
  have h12 : c₁ < c₂ := by rw [hc₁, hc₂]; linarith
  have h2b : c₂ < ℓ b := by rw [hc₂]; linarith
  -- the two pieces
  have hS₁ : (S.filter fun s => ℓ s < c₂) = T := by
    apply Finset.filter_congr
    intro s hs
    rcases hgap s hs with h | h <;> constructor <;> intro h' <;> linarith
  have hS₂ : (S.filter fun s => c₁ < ℓ s) = S.filter fun s => ¬ ℓ s < ℓ b := by
    apply Finset.filter_congr
    intro s hs
    rcases hgap s hs with h | h
    · exact ⟨fun h' => absurd h' (not_lt.mpr (by linarith)),
        fun h' => absurd (by linarith : ℓ s < ℓ b) h'⟩
    · exact ⟨fun _ => not_lt.mpr h, fun _ => by linarith⟩
  have hcard : T.card + (S.filter fun s => ¬ ℓ s < ℓ b).card = n := by
    rw [hT, Finset.card_filter_add_card_filter_not, hS]
  have hbT : b ∉ T := fun h => lt_irrefl _ (Finset.mem_filter.mp h).2
  have haT' : a ∉ S.filter fun s => ¬ ℓ s < ℓ b := fun h => (Finset.mem_filter.mp h).2 hℓab
  have hT1 : 0 < (S.filter fun s => ¬ ℓ s < ℓ b).card :=
    Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, lt_irrefl _⟩⟩
  have hT2 : 0 < T.card := Finset.card_pos.mpr ⟨a, haT⟩
  -- the cover
  let X := {z : ℂ // z ∉ S}
  let U : Set X := {x | ℓ x.1 < c₂}
  let V : Set X := {x | c₁ < ℓ x.1}
  set m := (c₁ + c₂) / 2 with hm
  have hz₀ : ℓ ((m : ℂ) / w) = m := by
    simp only [hℓ, mul_div_cancel₀ _ hw, Complex.ofReal_re]
  have hz₀S : (m : ℂ) / w ∉ S := by
    intro h
    rcases hgap _ h with h' | h' <;> rw [hz₀] at h' <;> rw [hm] at h' <;> linarith
  let x₀ : X := ⟨(m : ℂ) / w, hz₀S⟩
  have hx₀ : x₀ ∈ U ∩ V := by
    have h0 : ℓ x₀.1 = m := hz₀
    exact ⟨show ℓ x₀.1 < c₂ by rw [h0, hm]; linarith,
      show c₁ < ℓ x₀.1 by rw [h0, hm]; linarith⟩
  have hcont : Continuous fun x : X => ℓ x.1 := (continuous_re_mul w).comp continuous_subtype_val
  obtain ⟨hUc, ⟨eU⟩⟩ := piece_lt ih S w hw c₂ (by rw [hS₁]; omega) U rfl ⟨x₀, hx₀.1⟩
  obtain ⟨hVc, ⟨eV⟩⟩ := piece_gt ih S w hw c₁ (by rw [hS₂]; omega) V rfl ⟨x₀, hx₀.2⟩
  -- the strip
  have hstrip : IsSimplyConnected (U ∩ V) := by
    rw [← Topology.IsEmbedding.subtypeVal.isSimplyConnected_image]
    have himg : Subtype.val '' (U ∩ V) = {z : ℂ | ℓ z < c₂} ∩ {z : ℂ | c₁ < ℓ z} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · rintro ⟨h1, h2⟩
        have h1' : ℓ z < c₂ := h1
        have h2' : c₁ < ℓ z := h2
        refine ⟨⟨z, fun hz => ?_⟩, ⟨h1, h2⟩, rfl⟩
        rcases hgap z hz with h | h <;> linarith
    rw [himg]
    have hconv : Convex ℝ ({z : ℂ | ℓ z < c₂} ∩ {z : ℂ | c₁ < ℓ z}) :=
      (convex_halfSpace_lt (isLinearMap_re_mul w) c₂).inter
        (convex_halfSpace_gt (isLinearMap_re_mul w) c₁)
    haveI := hconv.contractibleSpace ⟨_, (hx₀.1 : ℓ x₀.1 < c₂), (hx₀.2 : c₁ < ℓ x₀.1)⟩
    exact SimplyConnectedSpace.ofContractible _
  have h : VanKampen.Hypotheses U V x₀ :=
    { isOpen_left := isOpen_lt hcont continuous_const
      isOpen_right := isOpen_lt continuous_const hcont
      union_eq := by
        ext x
        simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true, U, V]
        by_contra h'
        rw [not_or, not_lt, not_lt] at h'
        linarith [h'.1, h'.2]
      mem_inter := hx₀
      isPathConnected_left := isPathConnected_iff_pathConnectedSpace.mpr hUc
      isPathConnected_right := isPathConnected_iff_pathConnectedSpace.mpr hVc
      isPathConnected_inter := hstrip.isPathConnected }
  let nn : Bool → ℕ := fun i => cond i T.card (S.filter fun s => ¬ ℓ s < ℓ b).card
  let e : ∀ i, FundamentalGroup (VanKampen.piece U V i)
      ⟨x₀, VanKampen.mem_piece_of_mem_inter h.mem_inter i⟩ ≃* FreeGroup (Fin (nn i)) :=
    fun i => match i with
    | true => eU.trans (FreeGroup.freeGroupCongr (finCongr (by rw [hS₁]; rfl)))
    | false => eV.trans (FreeGroup.freeGroupCongr (finCongr (by rw [hS₂]; rfl)))
  obtain ⟨E⟩ := nonempty_coprod_mulEquiv nn e
  haveI := pathConnectedSpace_compl S
  obtain ⟨P⟩ := nonempty_mulEquiv_of_isPathConnected x x₀
  exact ⟨P.trans ((VanKampen.coprodEquiv h hstrip).symm.trans
    (E.trans (FreeGroup.freeGroupCongr (finCongr hcard))))⟩

theorem statement (n : ℕ) : Statement n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · exact statement_zero
    · exact statement_one
    · exact statement_step (by omega) ih

end Complex.PuncturedPlane

namespace Complex

/-- **`π₁(ℂ ∖ S) ≅ F_n`**: the fundamental group of the plane minus a finite set `S` of `n`
points is free of rank `n`, at every base point. -/
theorem nonempty_fundamentalGroup_compl_finset_mulEquiv (S : Finset ℂ) (x : {z : ℂ // z ∉ S}) :
    Nonempty (FundamentalGroup {z : ℂ // z ∉ S} x ≃* FreeGroup (Fin S.card)) :=
  PuncturedPlane.statement S.card S rfl x

end Complex

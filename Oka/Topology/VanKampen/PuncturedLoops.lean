/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.PuncturedPlane

/-!
# Free generators of `π₁(ℂ ∖ S)` are loops around the points of `S`

For a finite set `S ⊆ ℂ` and a base point `x ∈ ℂ ∖ S`, there are elements `γ_s ∈ π₁(ℂ ∖ S, x)`,
`s ∈ S`, forming a free basis (`FreeGroup S → π₁(ℂ ∖ S, x)` is an isomorphism), such that each
`γ_s` is a **loop around `s`** (`Complex.PuncturedPlane.IsLoopAround`): the class of
`δ · c · δ⁻¹`, where `c` is the circle `t ↦ s + r e^{2π i t}` of a radius `r > 0` whose closed
disc contains no other point of `S`, traversed once counterclockwise, and `δ` is a path from `x`
to `s + r` (`Complex.exists_isLoopAround_basis`).

## Proof

As for `Complex.nonempty_fundamentalGroup_compl_finset_mulEquiv` (milestone T2), by induction on
`|S|` and Seifert–van Kampen along a strip free of `S`, but for an arbitrary **open convex**
region `C ⊇ S` in place of `ℂ` (`Complex.PuncturedPlane.Region C S = C ∖ S`), so that the two
pieces `C ∩ {ℓ < c₂}`, `C ∩ {ℓ > c₁}` are again regions of the same kind and no homeomorphism
(which would not preserve circles) is needed:

* `|S| = 0`: `C` is contractible;
* `|S| = 1`, `S = {a}`: `C ∖ {a}` is homotopy equivalent to `ℂ ∖ {0}` (radial retraction onto
  a small circle around `a`), and under `π₁(ℂ ∖ {0}) ≅ ℤ` (lifting along `exp`) the circle goes
  to a generator: its lift starting at `e` ends at `e + 2πi` (monodromy computation);
* `|S| ≥ 2`: `VanKampen.coprodEquiv`; loops around `s` in a piece map to loops around `s` in
  `C ∖ S` (`Complex.PuncturedPlane.IsLoopAround.map`), and changing the base point along a path preserves loops around
  `s` (`Complex.PuncturedPlane.IsLoopAround.conj`).

## References

* [A. Hatcher, *Algebraic Topology*, §1.2, Example 1.22][hatcher02]
-/

open Set Topology Metric CategoryTheory

namespace Complex.PuncturedPlane

/-- An open convex region `C` minus a finite set `S`, as a type. -/
abbrev Region (C : Set ℂ) (S : Finset ℂ) : Type := {z : ℂ // z ∈ C ∧ z ∉ S}

section Circle

/-- The circle `t ↦ s + r e^{2π i t}`. -/
noncomputable def circleFun (s : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  s + r * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

lemma norm_circleFun_sub (s : ℂ) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : ‖circleFun s r t - s‖ = r := by
  simp only [circleFun, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

lemma continuous_circleFun (s : ℂ) (r : ℝ) : Continuous (circleFun s r) := by
  unfold circleFun
  fun_prop

lemma circleFun_zero (s : ℂ) (r : ℝ) : circleFun s r 0 = s + r := by
  simp [circleFun]

lemma circleFun_one (s : ℂ) (r : ℝ) : circleFun s r 1 = s + r := by
  simp only [circleFun, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_one,
    Complex.exp_two_pi_mul_I]

/-- An **admissible radius** for `s` in `C ∖ S`: the closed disc of radius `r` around `s` lies in
`C` and meets `S` at most in `s`. -/
structure Admissible (C : Set ℂ) (S : Finset ℂ) (s : ℂ) (r : ℝ) : Prop where
  pos : 0 < r
  subset : closedBall s r ⊆ C
  isolated : ∀ s' ∈ S, s' ∈ closedBall s r → s' = s

variable {C : Set ℂ} {S : Finset ℂ} {s : ℂ} {r : ℝ}

lemma Admissible.mem (h : Admissible C S s r) (t : ℝ) :
    circleFun s r t ∈ C ∧ circleFun s r t ∉ S := by
  have hn := norm_circleFun_sub s h.pos.le t
  have hb : circleFun s r t ∈ closedBall s r := by
    rw [mem_closedBall, dist_eq_norm, hn]
  refine ⟨h.subset hb, fun hS ↦ ?_⟩
  have := h.isolated _ hS hb
  rw [this, sub_self, norm_zero] at hn
  exact h.pos.ne hn

/-- The base point `s + r` of the circle. -/
def circleBase (h : Admissible C S s r) : Region C S :=
  ⟨s + r, by simpa [circleFun_zero] using h.mem 0⟩

/-- The circle of an admissible radius, as a loop in `C ∖ S` at `s + r`. -/
noncomputable def circlePath (h : Admissible C S s r) : Path (circleBase h) (circleBase h) where
  toFun t := ⟨circleFun s r t, h.mem t⟩
  continuous_toFun := ((continuous_circleFun s r).comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (circleFun_zero s r)
  target' := Subtype.ext (circleFun_one s r)

@[simp] lemma coe_circlePath (h : Admissible C S s r) (t : unitInterval) :
    (circlePath h t : ℂ) = circleFun s r t := rfl

/-- The circle of an admissible radius as an arrow of the fundamental groupoid. -/
noncomputable def circleArrow (h : Admissible C S s r) :
    FundamentalGroupoid.mk (circleBase h) ⟶ FundamentalGroupoid.mk (circleBase h) :=
  ⟦circlePath h⟧

/-- **A loop around `s`**: `γ` is the class of `δ · c · δ⁻¹` for the circle `c` of an admissible
radius around `s` and a path class `δ` from the base point to `s + r`. -/
def IsLoopAround {x : Region C S} (γ : FundamentalGroup (Region C S) x) (s : ℂ) : Prop :=
  ∃ (r : ℝ) (h : Admissible C S s r)
    (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (circleBase h)),
    γ = δ ≫ circleArrow h ≫ Groupoid.inv δ

/-- Loops around `s` are preserved by conjugation (change of base point). -/
lemma IsLoopAround.conj {x y : Region C S}
    (α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk y)
    {γ : FundamentalGroup (Region C S) x} {s : ℂ} (hγ : IsLoopAround γ s) :
    IsLoopAround (α.conj γ) s := by
  obtain ⟨r, h, δ, rfl⟩ := hγ
  refine ⟨r, h, α.inv ≫ δ, ?_⟩
  simp [Iso.conj_apply, Groupoid.inv_eq_inv, IsIso.inv_comp]

/-- Loops around `s` are preserved by change of base point along a path. -/
lemma IsLoopAround.ofPath {x y : Region C S} (P : Path x y)
    {γ : FundamentalGroup (Region C S) x} {s : ℂ} (hγ : IsLoopAround γ s) :
    IsLoopAround (FundamentalGroup.fundamentalGroupMulEquivOfPath P γ) s :=
  hγ.conj _

/-- Loops around `s` are preserved by maps of regions over `ℂ` (with `C ⊆ C'` and
`S' ∩ C ⊆ S`). -/
lemma IsLoopAround.map {C' : Set ℂ} {S' : Finset ℂ} (hC : C ⊆ C')
    (hS : ∀ s' ∈ S', s' ∈ C → s' ∈ S) (f : C(Region C S, Region C' S'))
    (hf : ∀ z, (f z : ℂ) = z) {x : Region C S} {γ : FundamentalGroup (Region C S) x}
    (hγ : IsLoopAround γ s) : IsLoopAround (FundamentalGroup.map f x γ) s := by
  obtain ⟨r, h, δ, rfl⟩ := hγ
  have h' : Admissible C' S' s r :=
    ⟨h.pos, h.subset.trans hC, fun s' hs' hb ↦ h.isolated s' (hS s' hs' (h.subset hb)) hb⟩
  have hb : f (circleBase h) = circleBase h' := Subtype.ext (hf _)
  have e : (FundamentalGroupoid.map f).obj (FundamentalGroupoid.mk (circleBase h)) =
      FundamentalGroupoid.mk (circleBase h') := congrArg FundamentalGroupoid.mk hb
  have hc : (FundamentalGroupoid.map f).map (circleArrow h) =
      eqToHom e ≫ circleArrow h' ≫ eqToHom e.symm := by
    rw [FundamentalGroupoid.conj_eqToHom]
    change Path.Homotopic.Quotient.mk ((circlePath h).map f.continuous) = _
    have : (circlePath h).map f.continuous = (circlePath h').cast hb hb := by
      ext t
      exact hf _
    rw [this]
    rfl
  refine ⟨r, h', (FundamentalGroupoid.map f).map δ ≫ eqToHom e, ?_⟩
  change (FundamentalGroupoid.map f).map (δ ≫ circleArrow h ≫ Groupoid.inv δ) = _
  rw [Functor.map_comp, Functor.map_comp, hc, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
    Functor.map_inv, IsIso.inv_comp, inv_eqToHom]
  simp only [Category.assoc]
  rfl

end Circle

/-! ### The statement -/

/-- The statement for `n` points in an open convex region. -/
def LoopStatement (n : ℕ) : Prop :=
  ∀ (C : Set ℂ), IsOpen C → Convex ℝ C → ∀ S : Finset ℂ, (S : Set ℂ) ⊆ C → S.card = n →
    ∀ x : Region C S, PathConnectedSpace (Region C S) ∧
      ∃ g : S → FundamentalGroup (Region C S) x,
        (∀ s : S, IsLoopAround (g s) s) ∧ Function.Bijective (FreeGroup.lift g)

lemma freeGroup_eq_one_of_isEmpty {α : Type*} [IsEmpty α] (w : FreeGroup α) : w = 1 := by
  induction w using FreeGroup.induction_on with
  | C1 => rfl
  | of x => exact isEmptyElim x
  | inv_of x _ => exact isEmptyElim x
  | mul x y hx hy => rw [hx, hy, mul_one]

theorem loopStatement_zero : LoopStatement 0 := by
  intro C hCo hCc S hSC hS x
  rw [Finset.card_eq_zero] at hS
  subst hS
  haveI : ContractibleSpace (Region C ∅) :=
    Convex.contractibleSpace (s := {z : ℂ | z ∈ C ∧ z ∉ (∅ : Finset ℂ)}) (by simpa using hCc)
      ⟨x.1, x.2⟩
  haveI : SimplyConnectedSpace (Region C ∅) := SimplyConnectedSpace.ofContractible _
  haveI : IsEmpty (∅ : Finset ℂ) := ⟨fun s ↦ Finset.notMem_empty _ s.2⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨isEmptyElim, isEmptyElim, fun a b _ ↦ ?_, fun γ ↦ ⟨1, ?_⟩⟩
  · rw [freeGroup_eq_one_of_isEmpty a, freeGroup_eq_one_of_isEmpty b]
  · exact Subsingleton.elim _ _

/-! ### One point -/

/-- `π₁` of a homotopy equivalence is bijective. -/
theorem map_bijective_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  have hF : ∀ {a b : FundamentalGroupoid X} (p : a ⟶ b),
      (FundamentalGroupoid.map e.toFun).map p = E.functor.map p := fun _ ↦ rfl
  refine ⟨fun p q hpq ↦ E.functor.map_injective ?_, fun q ↦ ?_⟩
  · rw [← hF, ← hF]
    exact hpq
  · obtain ⟨p, hp⟩ := E.functor.map_surjective (X := FundamentalGroupoid.mk x)
      (Y := FundamentalGroupoid.mk x) q
    exact ⟨p, (hF p).trans hp⟩

section One

variable {C : Set ℂ} {a : ℂ} {r : ℝ} (hCc : Convex ℝ C) (h : Admissible C {a} a r)

lemma ne_of_mem_region (z : Region C {a}) : (z : ℂ) - a ≠ 0 :=
  sub_ne_zero.2 fun he ↦ z.2.2 (by rw [he]; exact Finset.mem_singleton_self a)

/-- `C ∖ {a} → ℂ ∖ {0}`, `z ↦ z - a`. -/
noncomputable def shiftMap : C(Region C {a}, {z : ℂ // z ≠ 0}) where
  toFun z := ⟨z.1 - a, ne_of_mem_region z⟩
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

include h in
lemma mem_of_norm_le {w : ℂ} (hw : ‖w‖ ≤ r) : a + w ∈ C ∧ a + w ∉ ({a} : Finset ℂ) ∨ w = 0 := by
  by_cases hw0 : w = 0
  · exact Or.inr hw0
  · refine Or.inl ⟨h.subset ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hw
    · rw [Finset.mem_singleton]
      intro he
      exact hw0 (by simpa using he)

/-- The radial retraction `ℂ ∖ {0} → C ∖ {a}` onto the circle of radius `r` around `a`. -/
noncomputable def retractMap : C({z : ℂ // z ≠ 0}, Region C {a}) where
  toFun w := ⟨a + ((r / ‖(w : ℂ)‖ : ℝ) : ℂ) * w, by
    have hw : ‖((r / ‖(w : ℂ)‖ : ℝ) : ℂ) * w‖ ≤ r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg h.pos.le (norm_nonneg _)), div_mul_cancel₀ _ (norm_ne_zero_iff.2 w.2)]
    rcases mem_of_norm_le h hw with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero (Complex.ofReal_ne_zero.2
        (div_ne_zero h.pos.ne' (norm_ne_zero_iff.2 w.2))) w.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_const.add (Continuous.mul ?_ continuous_subtype_val)) _
    refine Complex.continuous_ofReal.comp (continuous_const.div ?_ fun w ↦ norm_ne_zero_iff.2 w.2)
    exact continuous_norm.comp continuous_subtype_val

end One

lemma exists_admissible_single {C : Set ℂ} (hCo : IsOpen C) {a : ℂ} (ha : a ∈ C) :
    ∃ r, Admissible C {a} a r := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hCo a ha
  exact ⟨ε / 2, ⟨by positivity, (closedBall_subset_ball (by linarith)).trans hball,
    fun s' hs' _ ↦ Finset.mem_singleton.1 hs'⟩⟩

lemma coeff_pos {q t : ℝ} (hq : 0 < q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < (1 - t) * q + t := by
  rcases eq_or_lt_of_le ht0 with ht | ht
  · subst ht; simpa using hq
  · nlinarith [mul_nonneg (sub_nonneg.2 ht1) hq.le]

section Homotopy

variable {C : Set ℂ} {a : ℂ} {r : ℝ} (hCc : Convex ℝ C) (h : Admissible C {a} a r)

include hCc h in
lemma homotopy₁_mem (t : unitInterval) (z : Region C {a}) :
    a + ((((1 - (t : ℝ)) * (r / ‖(z : ℂ) - a‖) + t : ℝ)) : ℂ) * ((z : ℂ) - a) ∈ C ∧
      a + ((((1 - (t : ℝ)) * (r / ‖(z : ℂ) - a‖) + t : ℝ)) : ℂ) * ((z : ℂ) - a) ∉
        ({a} : Finset ℂ) := by
  have hu := ne_of_mem_region z
  have hρ : 0 < ‖(z : ℂ) - a‖ := norm_pos_iff.2 hu
  have hc := coeff_pos (div_pos h.pos hρ) t.2.1 t.2.2
  refine ⟨?_, ?_⟩
  · have hp : a + ((r / ‖(z : ℂ) - a‖ : ℝ) : ℂ) * ((z : ℂ) - a) ∈ C := by
      apply h.subset
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (div_pos h.pos hρ), div_mul_cancel₀ _ hρ.ne']
    have := hCc hp z.2.1 (sub_nonneg.2 t.2.2) t.2.1 (by ring)
    convert this using 1
    simp only [Complex.real_smul]
    push_cast
    ring
  · rw [Finset.mem_singleton]
    intro he
    have : ((((1 - (t : ℝ)) * (r / ‖(z : ℂ) - a‖) + t : ℝ)) : ℂ) * ((z : ℂ) - a) = 0 := by
      linear_combination he
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') hu this

/-- The straight-line homotopy `retract ∘ shift ≃ id` on `C ∖ {a}`. -/
noncomputable def homotopy₁ :
    ContinuousMap.Homotopy ((retractMap h).comp shiftMap) (ContinuousMap.id (Region C {a})) where
  toFun p := ⟨_, homotopy₁_mem hCc h p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_const.add (Continuous.mul ?_ ?_)) _
    · refine Complex.continuous_ofReal.comp (Continuous.add (Continuous.mul ?_ ?_) ?_)
      · exact continuous_const.sub (continuous_subtype_val.comp continuous_fst)
      · exact continuous_const.div (continuous_norm.comp ((continuous_subtype_val.comp
          continuous_snd).sub continuous_const)) fun p ↦ norm_ne_zero_iff.2 (ne_of_mem_region p.2)
      · exact continuous_subtype_val.comp continuous_fst
    · exact (continuous_subtype_val.comp continuous_snd).sub continuous_const
  map_zero_left z := by
    apply Subtype.ext
    simp [retractMap, shiftMap]
  map_one_left z := by
    apply Subtype.ext
    simp

lemma homotopy₂_ne (t : unitInterval) (w : {z : ℂ // z ≠ 0}) (hr : 0 < r) :
    ((((1 - (t : ℝ)) * (r / ‖(w : ℂ)‖) + t : ℝ)) : ℂ) * (w : ℂ) ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2
    (coeff_pos (div_pos hr (norm_pos_iff.2 w.2)) t.2.1 t.2.2).ne') w.2

/-- The straight-line homotopy `shift ∘ retract ≃ id` on `ℂ ∖ {0}`. -/
noncomputable def homotopy₂ :
    ContinuousMap.Homotopy (shiftMap.comp (retractMap h)) (ContinuousMap.id {z : ℂ // z ≠ 0}) where
  toFun p := ⟨_, homotopy₂_ne p.1 p.2 h.pos⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.mul ?_ (continuous_subtype_val.comp continuous_snd)) _
    refine Complex.continuous_ofReal.comp (Continuous.add (Continuous.mul ?_ ?_) ?_)
    · exact continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    · exact continuous_const.div (continuous_norm.comp (continuous_subtype_val.comp
          continuous_snd)) fun p ↦ norm_ne_zero_iff.2 p.2.2
    · exact continuous_subtype_val.comp continuous_fst
  map_zero_left w := by
    apply Subtype.ext
    simp [retractMap, shiftMap]
  map_one_left w := by
    apply Subtype.ext
    simp

/-- `C ∖ {a}` is homotopy equivalent to `ℂ ∖ {0}`. -/
noncomputable def homotopyEquiv : ContinuousMap.HomotopyEquiv (Region C {a}) {z : ℂ // z ≠ 0} where
  toFun := shiftMap
  invFun := retractMap h
  left_inv := ⟨homotopy₁ hCc h⟩
  right_inv := ⟨homotopy₂ h⟩

end Homotopy

section Monodromy

/-- `exp : ℂ → ℂ ∖ {0}`. -/
noncomputable abbrev expMap : ℂ → {z : ℂ // z ≠ 0} := fun z ↦ ⟨Complex.exp z, Complex.exp_ne_zero z⟩

/-- `2πi` as a period. -/
noncomputable def twoPiI : AddSubgroup.zmultiples (2 * Real.pi * Complex.I) :=
  ⟨2 * Real.pi * Complex.I, AddSubgroup.mem_zmultiples _⟩

/-- The segment from `e` to `e + 2πi`. -/
noncomputable def periodPath (e : ℂ) : Path e (e + 2 * Real.pi * Complex.I) where
  toFun t := e + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- **The circle generates**: the loop `β · c · β⁻¹`, where `c` is a loop `t ↦ b e^{2π i t}` at
`b ∈ ℂ ∖ {0}`, acts on the fibre of `exp` by the period `2πi`. -/
theorem fundamentalGroupToMulOpposite_conj_circle {y b : {z : ℂ // z ≠ 0}}
    (e : expMap ⁻¹' {y}) (β : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk b)
    (c : Path b b)
    (hc : ∀ t : unitInterval, (c t : ℂ) = (b : ℂ) *
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)) :
    Complex.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e
      (β ≫ ⟦c⟧ ≫ Groupoid.inv β) = MulOpposite.op (Multiplicative.ofAdd twoPiI) := by
  set hp := Complex.isAddQuotientCoveringMap_exp
  rw [IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff]
  set e₁ := hp.isCoveringMap.monodromy β e
  have hcoe : ∀ {z : {z : ℂ // z ≠ 0}} (e' : expMap ⁻¹' {z}),
      ((hp.toMultiplicative.toPermFiber z (Multiplicative.ofAdd twoPiI) e' : _) : ℂ) =
        e'.1 + 2 * Real.pi * Complex.I := by
    intro z e'
    change (2 * Real.pi * Complex.I : ℂ) + e'.1 = _
    ring
  have h₁ : hp.isCoveringMap.monodromy (⟦c⟧ : Path.Homotopic.Quotient b b) e₁ =
      hp.toMultiplicative.toPermFiber b (Multiplicative.ofAdd twoPiI) e₁ := by
    refine hp.isCoveringMap.monodromy_eq_of_map_eq
      ⟦(periodPath e₁.1).cast rfl (hcoe e₁)⟧ ?_
    have hb : Complex.exp e₁.1 = b := congrArg Subtype.val e₁.2
    change Path.Homotopic.Quotient.mk (((periodPath e₁.1).cast rfl (hcoe e₁)).map _) =
      Path.Homotopic.Quotient.mk (c.cast _ _)
    congr 1
    ext t
    simp only [Path.map_coe, Path.cast_coe, Function.comp_apply, ContinuousMap.coe_mk,
      periodPath, Path.coe_mk_mk, hc, Complex.exp_add, hb]
  have h₂ : hp.isCoveringMap.monodromy (Groupoid.inv β) e₁ = e := by
    have hβ : Path.Homotopic.Quotient.trans β (Groupoid.inv β) =
        Path.Homotopic.Quotient.refl y := Groupoid.comp_inv β
    change hp.isCoveringMap.monodromy (Groupoid.inv β) (hp.isCoveringMap.monodromy β e) = e
    rw [← hp.isCoveringMap.monodromy_trans_apply, hβ, hp.isCoveringMap.monodromy_refl]
    rfl
  have hm : hp.isCoveringMap.monodromy (β ≫ ⟦c⟧ ≫ Groupoid.inv β) e =
      hp.toMultiplicative.toPermFiber y (Multiplicative.ofAdd twoPiI) e := by
    change hp.isCoveringMap.monodromy (β.trans (Path.Homotopic.Quotient.trans ⟦c⟧
      (Groupoid.inv β))) e = _
    rw [hp.isCoveringMap.monodromy_trans_apply, hp.isCoveringMap.monodromy_trans_apply, h₁,
      hp.monodromy_toPermFiber, h₂]
  rw [hm, hcoe]
  change (2 * Real.pi * Complex.I : ℂ) + e.1 = _
  ring

end Monodromy

section OneProof

lemma pathConnectedSpace_punctured : PathConnectedSpace {z : ℂ // z ≠ 0} := by
  have h := isPathConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ) (0 : ℂ)
  exact isPathConnected_iff_pathConnectedSpace.mp h

lemma pathConnectedSpace_region_single {C : Set ℂ} {a : ℂ} {r : ℝ} (hCc : Convex ℝ C)
    (h : Admissible C {a} a r) : PathConnectedSpace (Region C {a}) := by
  haveI := pathConnectedSpace_punctured
  have key : ∀ x : Region C {a}, Joined (retractMap h (shiftMap x)) x := fun x ↦
    ⟨(homotopy₁ hCc h).evalAt x⟩
  refine ⟨⟨circleBase h⟩, fun x y ↦ ?_⟩
  refine ((key x).symm.trans ?_).trans (key y)
  exact ⟨(PathConnectedSpace.somePath (shiftMap x) (shiftMap y)).map (retractMap h).continuous⟩

/-- The value of `2πi` under `ℤ ≅ zmultiples (2πi)`. -/
lemma intEquivZMultiplesTwoPiI_one : Complex.intEquivZMultiplesTwoPiI 1 = twoPiI := by
  simp [Complex.intEquivZMultiplesTwoPiI, intEquivOfZMultiplesEqTop, twoPiI]

theorem loopStatement_one : LoopStatement 1 := by
  intro C hCo hCc S hSC hS x
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hS
  have ha : a ∈ C := hSC (Finset.mem_singleton_self a)
  obtain ⟨r, h⟩ := exists_admissible_single hCo ha
  haveI := pathConnectedSpace_region_single hCc h
  refine ⟨inferInstance, ?_⟩
  let δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (circleBase h) :=
    ⟦PathConnectedSpace.somePath x (circleBase h)⟧
  let γ : FundamentalGroup (Region C {a}) x := δ ≫ circleArrow h ≫ Groupoid.inv δ
  refine ⟨fun _ ↦ γ, fun s ↦ ?_, ?_⟩
  · obtain ⟨s, hs⟩ := s
    obtain rfl : s = a := Finset.mem_singleton.1 hs
    exact ⟨r, h, δ, rfl⟩
  -- `C ∖ {a} ≃ₕ ℂ ∖ {0}` and `π₁(ℂ ∖ {0}) ≅ zmultiples (2πi)`
  let E := homotopyEquiv hCc h
  have hJ := map_bijective_of_homotopyEquiv E x
  let J := FundamentalGroup.map E.toFun x
  let e : expMap ⁻¹' {E.toFun x} :=
    ⟨Complex.log (E.toFun x), Subtype.ext (Complex.exp_log (E.toFun x).2)⟩
  let Φ := Complex.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv e
  have hγ : Φ (J γ) = MulOpposite.op (Multiplicative.ofAdd twoPiI) := by
    change Complex.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite e
      ((FundamentalGroupoid.map shiftMap).map (δ ≫ circleArrow h ≫ Groupoid.inv δ)) = _
    rw [Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Functor.map_inv,
      ← Groupoid.inv_eq_inv]
    refine fundamentalGroupToMulOpposite_conj_circle e _ ((circlePath h).map shiftMap.continuous)
      fun t ↦ ?_
    change circleFun a r t - a = ((a + (r : ℂ)) - a) * _
    simp only [circleFun]
    ring
  let e1 : (({a} : Finset ℂ) : Type) ≃ Fin 1 := Fintype.equivFinOfCardEq (by simp)
  let M : FreeGroup (({a} : Finset ℂ) : Type) ≃* (Multiplicative _)ᵐᵒᵖ :=
    (FreeGroup.freeGroupCongr e1).trans (freeGroupFinOneEquiv.trans
      ((AddEquiv.toMultiplicative Complex.intEquivZMultiplesTwoPiI).trans
        MulOpposite.opMulEquiv))
  have hK : (Φ.toMonoidHom.comp J).comp (FreeGroup.lift fun _ ↦ γ) = M.toMonoidHom := by
    refine FreeGroup.ext_hom _ _ fun s ↦ ?_
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, MulEquiv.coe_toMonoidHom, hγ, M]
    simp [freeGroupFinOneEquiv, intEquivZMultiplesTwoPiI_one, Subsingleton.elim (e1 s) 0]
  have hinj : Function.Injective (Φ.toMonoidHom.comp J) := Φ.injective.comp hJ.1
  refine ⟨fun p q hpq ↦ M.injective ?_, fun γ' ↦ ⟨M.symm (Φ (J γ')), hinj ?_⟩⟩
  · rw [← MulEquiv.coe_toMonoidHom, ← hK, MonoidHom.comp_apply, MonoidHom.comp_apply, hpq]
    rfl
  · rw [← MonoidHom.comp_apply, hK]
    simp
end OneProof

/-! ### The induction step -/

/-- Reindexing a free basis. -/
lemma bijective_lift_comp_equiv {α β G : Type*} [Group G] (g : β → G) (σ : α ≃ β)
    (hg : Function.Bijective (FreeGroup.lift g)) : Function.Bijective (FreeGroup.lift (g ∘ σ)) := by
  have : FreeGroup.lift (g ∘ σ) =
      (FreeGroup.lift g).comp (FreeGroup.freeGroupCongr σ).toMonoidHom :=
    FreeGroup.ext_hom _ _ fun a ↦ by simp
  rw [this, MonoidHom.coe_comp]
  exact hg.comp (FreeGroup.freeGroupCongr σ).bijective

/-- Composing a free basis with an isomorphism. -/
lemma bijective_lift_map {α G H : Type*} [Group G] [Group H] (g : α → G) (φ : G →* H)
    (hφ : Function.Bijective φ) (hg : Function.Bijective (FreeGroup.lift g)) :
    Function.Bijective (FreeGroup.lift (φ ∘ g)) := by
  have : FreeGroup.lift (φ ∘ g) = φ.comp (FreeGroup.lift g) :=
    FreeGroup.ext_hom _ _ fun a ↦ by simp
  rw [this, MonoidHom.coe_comp]
  exact hφ.comp hg

/-- **Assembly**: free bases of the two pieces of a van Kampen cover with simply connected
intersection give a free basis of the whole space. -/
lemma bijective_lift_vanKampen {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (h : VanKampen.Hypotheses U V x₀) (hUV : IsSimplyConnected (U ∩ V)) {ι : Bool → Type*}
    (g : ∀ b, ι b → FundamentalGroup (VanKampen.piece U V b)
      ⟨x₀, VanKampen.mem_piece_of_mem_inter h.mem_inter b⟩)
    (hg : ∀ b, Function.Bijective (FreeGroup.lift (g b))) :
    Function.Bijective (FreeGroup.lift fun p : Σ b, ι b ↦
      VanKampen.pieceMap U V h.mem_inter p.1 (g p.1 p.2)) := by
  let e : ∀ b, FundamentalGroup (VanKampen.piece U V b)
      ⟨x₀, VanKampen.mem_piece_of_mem_inter h.mem_inter b⟩ ≃* FreeGroup (ι b) :=
    fun b ↦ (MulEquiv.ofBijective _ (hg b)).symm
  let N := (coprodFreeGroupEquiv e).symm.trans (VanKampen.coprodEquiv h hUV)
  have : FreeGroup.lift (fun p : Σ b, ι b ↦
      VanKampen.pieceMap U V h.mem_inter p.1 (g p.1 p.2)) = N.toMonoidHom := by
    refine FreeGroup.ext_hom _ _ fun p ↦ ?_
    simp only [FreeGroup.lift_apply_of, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, N]
    have h1 : (coprodFreeGroupEquiv e).symm (FreeGroup.of p) =
        Monoid.CoprodI.of (M := fun b ↦ FundamentalGroup (VanKampen.piece U V b)
          ⟨x₀, VanKampen.mem_piece_of_mem_inter h.mem_inter b⟩) (i := p.1)
          ((e p.1).symm (FreeGroup.of p.2)) := by
      rw [MulEquiv.symm_apply_eq]
      simp [coprodFreeGroupEquiv]
    rw [h1, VanKampen.coprodEquiv_apply, Monoid.CoprodI.lift_of]
    congr 1
    simp [e]
  rw [this]
  exact N.bijective

open Classical in
/-- One piece of the van Kampen cover: `{x ∈ C ∖ S | x ∈ P}` (for `P` open convex) is path
connected and its `π₁` has a free basis of loops around the points of `S ∩ P`. -/
lemma exists_basis_piece {n : ℕ} (ih : ∀ m < n, LoopStatement m) {C : Set ℂ} (hCo : IsOpen C)
    (hCc : Convex ℝ C) {S : Finset ℂ} (hSC : (S : Set ℂ) ⊆ C) {P : Set ℂ} (hPo : IsOpen P)
    (hPc : Convex ℝ P) (hcard : (S.filter (· ∈ P)).card < n) (x₀ : Region C S)
    (hx₀ : x₀.1 ∈ P) :
    IsPathConnected {x : Region C S | x.1 ∈ P} ∧
    ∃ g : (S.filter (· ∈ P)) → FundamentalGroup {x : Region C S | x.1 ∈ P} ⟨x₀, hx₀⟩,
      (∀ t, IsLoopAround (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ _ (g t))
        t) ∧ Function.Bijective (FreeGroup.lift g) := by
  have hS'C : ((S.filter (· ∈ P) : Finset ℂ) : Set ℂ) ⊆ C ∩ P := fun z hz ↦ by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hz
    exact ⟨hSC h1, h2⟩
  let y : Region (C ∩ P) (S.filter (· ∈ P)) :=
    ⟨x₀.1, ⟨x₀.2.1, hx₀⟩, fun h ↦ x₀.2.2 (Finset.mem_filter.1 h).1⟩
  obtain ⟨hpc, g', hloop, hbij⟩ :=
    ih _ hcard (C ∩ P) (hCo.inter hPo) (hCc.inter hPc) _ hS'C rfl y
  let φ : Region (C ∩ P) (S.filter (· ∈ P)) ≃ₜ {x : Region C S | x.1 ∈ P} :=
    { toFun := fun z ↦ ⟨⟨z.1, z.2.1.1, fun h ↦ z.2.2 (Finset.mem_filter.2 ⟨h, z.2.1.2⟩)⟩,
        z.2.1.2⟩
      invFun := fun u ↦ ⟨u.1.1, ⟨u.1.2.1, u.2⟩, fun h ↦ u.1.2.2 (Finset.mem_filter.1 h).1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) }
  refine ⟨isPathConnected_iff_pathConnectedSpace.2
    (φ.surjective.pathConnectedSpace φ.continuous), ?_⟩
  let ψ : C(Region (C ∩ P) (S.filter (· ∈ P)), Region C S) :=
    ⟨fun z ↦ ⟨z.1, z.2.1.1, fun h ↦ z.2.2 (Finset.mem_filter.2 ⟨h, z.2.1.2⟩)⟩,
      continuous_subtype_val.subtype_mk _⟩
  refine ⟨fun t ↦ (FundamentalGroup.map φ.toHomotopyEquiv.toFun y (g' t) :), fun t ↦ ?_, ?_⟩
  · have := (hloop t).map (C' := C) (S' := S) Set.inter_subset_left
      (fun s' hs' hC ↦ Finset.mem_filter.2 ⟨hs', hC.2⟩) ψ (fun _ ↦ rfl)
    have key : (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ ⟨x₀, hx₀⟩
        (FundamentalGroup.map φ.toHomotopyEquiv.toFun y (g' t)) : FundamentalGroup _ x₀) =
        FundamentalGroup.map ψ y (g' t) := by
      generalize g' t = p
      induction p using Quotient.inductionOn
      rfl
    dsimp only
    rw [key]
    exact this
  · exact bijective_lift_map g' (FundamentalGroup.map φ.toHomotopyEquiv.toFun y)
      (map_bijective_of_homotopyEquiv φ.toHomotopyEquiv y) hbij

open Classical in
/-- **The induction step**: `n ≥ 2` points are split by a strip `c₁ < ℓ < c₂` free of `S`. -/
theorem loopStatement_step {n : ℕ} (hn : 2 ≤ n) (ih : ∀ m < n, LoopStatement m) :
    LoopStatement n := by
  intro C hCo hCc S hSC hS x
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
  have hat₀ : ℓ a ≤ t₀ := Finset.le_sup' ℓ haT
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
  let P₁ : Set ℂ := {z | ℓ z < c₂}
  let P₂ : Set ℂ := {z | c₁ < ℓ z}
  have hP₁o : IsOpen P₁ := isOpen_lt (continuous_re_mul w) continuous_const
  have hP₂o : IsOpen P₂ := isOpen_lt continuous_const (continuous_re_mul w)
  have hP₁c : Convex ℝ P₁ := convex_halfSpace_lt (isLinearMap_re_mul w) c₂
  have hP₂c : Convex ℝ P₂ := convex_halfSpace_gt (isLinearMap_re_mul w) c₁
  have hcard₁ : (S.filter (· ∈ P₁)).card < n := by
    rw [← hS]
    exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨b, hb, fun h ↦ by
      change ℓ b < c₂ at h; linarith⟩)
  have hcard₂ : (S.filter (· ∈ P₂)).card < n := by
    rw [← hS]
    exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, ha, fun h ↦ by
      change c₁ < ℓ a at h; linarith⟩)
  -- a base point in the strip, on the segment `[a, b]`
  set m := (c₁ + c₂) / 2 with hm
  set lam := (m - ℓ a) / (ℓ b - ℓ a) with hlam
  have hba : 0 < ℓ b - ℓ a := by linarith
  have hlam0 : 0 ≤ lam := div_nonneg (by rw [hm]; linarith) hba.le
  have hlam1 : lam ≤ 1 := (div_le_one hba).2 (by rw [hm]; linarith)
  set z₀ : ℂ := (1 - lam) • a + lam • b with hz₀
  have hℓz₀ : ℓ z₀ = m := by
    have : ℓ z₀ = ℓ a + lam * (ℓ b - ℓ a) := by
      simp only [hℓ, hz₀, Complex.real_smul, mul_add, Complex.add_re]
      simp only [mul_left_comm w, Complex.re_ofReal_mul]
      ring
    rw [this, hlam, div_mul_cancel₀ _ hba.ne']
    ring
  have hz₀C : z₀ ∈ C := hCc (hSC ha) (hSC hb) (by linarith) hlam0 (by ring)
  have hz₀S : z₀ ∉ S := fun h ↦ by
    rcases hgap _ h with h' | h' <;> rw [hℓz₀, hm] at h' <;> linarith
  let x₀ : Region C S := ⟨z₀, hz₀C, hz₀S⟩
  have hx₀₁ : x₀.1 ∈ P₁ := show ℓ z₀ < c₂ by rw [hℓz₀, hm]; linarith
  have hx₀₂ : x₀.1 ∈ P₂ := show c₁ < ℓ z₀ by rw [hℓz₀, hm]; linarith
  obtain ⟨hU, g₁, hl₁, hb₁⟩ := exists_basis_piece ih hCo hCc hSC hP₁o hP₁c hcard₁ x₀ hx₀₁
  obtain ⟨hV, g₂, hl₂, hb₂⟩ := exists_basis_piece ih hCo hCc hSC hP₂o hP₂c hcard₂ x₀ hx₀₂
  let U : Set (Region C S) := {x | x.1 ∈ P₁}
  let V : Set (Region C S) := {x | x.1 ∈ P₂}
  -- the strip
  have hstrip : IsSimplyConnected (U ∩ V) := by
    rw [← Topology.IsEmbedding.subtypeVal.isSimplyConnected_image]
    have himg : Subtype.val '' (U ∩ V) = C ∩ P₁ ∩ P₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x.2.1, hx.1⟩, hx.2⟩
      · rintro ⟨⟨hzC, h1⟩, h2⟩
        refine ⟨⟨z, hzC, fun hz ↦ ?_⟩, ⟨h1, h2⟩, rfl⟩
        change ℓ z < c₂ at h1
        change c₁ < ℓ z at h2
        rcases hgap z hz with h | h <;> linarith
    rw [himg]
    haveI := ((hCc.inter hP₁c).inter hP₂c).contractibleSpace ⟨z₀, ⟨hz₀C, hx₀₁⟩, hx₀₂⟩
    exact SimplyConnectedSpace.ofContractible _
  have h : VanKampen.Hypotheses U V x₀ :=
    { isOpen_left := hP₁o.preimage continuous_subtype_val
      isOpen_right := hP₂o.preimage continuous_subtype_val
      union_eq := by
        ext y
        simp only [Set.mem_union, Set.mem_univ, iff_true]
        by_contra h'
        rw [not_or] at h'
        exact h'.1 (show ℓ y.1 < c₂ from lt_of_not_ge fun h3 ↦ h'.2 (show c₁ < ℓ y.1 by linarith))
      mem_inter := ⟨hx₀₁, hx₀₂⟩
      isPathConnected_left := hU
      isPathConnected_right := hV
      isPathConnected_inter := hstrip.isPathConnected }
  haveI : PathConnectedSpace (Region C S) := by
    rw [pathConnectedSpace_iff_univ, ← h.union_eq]
    exact hU.union hV ⟨x₀, ⟨hx₀₁, hx₀₂⟩⟩
  -- the assembled basis
  let ι : Bool → Type := fun c ↦ (S.filter (· ∈ cond c P₁ P₂) : Finset ℂ)
  let gg : ∀ c, ι c → FundamentalGroup (VanKampen.piece U V c)
      ⟨x₀, VanKampen.mem_piece_of_mem_inter h.mem_inter c⟩ := fun c ↦
    match c with
    | true => g₁
    | false => g₂
  have hG := bijective_lift_vanKampen h hstrip gg fun c ↦ match c with
    | true => hb₁
    | false => hb₂
  let G : (Σ c, ι c) → FundamentalGroup (Region C S) x₀ := fun p ↦
    VanKampen.pieceMap U V h.mem_inter p.1 (gg p.1 p.2)
  let σf : S → Σ c, ι c := fun s ↦
    if hs : ℓ s.1 < c₂ then ⟨true, ⟨s.1, Finset.mem_filter.2 ⟨s.2, hs⟩⟩⟩
    else ⟨false, ⟨s.1, Finset.mem_filter.2 ⟨s.2, show c₁ < ℓ s.1 by linarith⟩⟩⟩
  have hσval : ∀ s : S, (((σf s).2 : ι (σf s).1) : ℂ) = s.1 := by
    intro s
    by_cases hs : ℓ s.1 < c₂
    · have e : σf s = ⟨true, ⟨s.1, Finset.mem_filter.2 ⟨s.2, hs⟩⟩⟩ := dif_pos hs
      rw [e]
    · have e : σf s = ⟨false, ⟨s.1, Finset.mem_filter.2 ⟨s.2,
          show c₁ < ℓ s.1 by linarith⟩⟩⟩ := dif_neg hs
      rw [e]
  have hσ : Function.Bijective σf := by
    refine ⟨fun s s' hss ↦ Subtype.ext ?_, fun p ↦ ?_⟩
    · rw [← hσval s, ← hσval s', hss]
    · obtain ⟨c, t, ht⟩ := p
      have htS := (Finset.mem_filter.1 ht).1
      refine ⟨⟨t, htS⟩, ?_⟩
      cases c with
      | true =>
        have h1 : ℓ t < c₂ := (Finset.mem_filter.1 ht).2
        simp only [σf, dif_pos h1]
      | false =>
        have h1 : c₁ < ℓ t := (Finset.mem_filter.1 ht).2
        have h2 : ¬ ℓ t < c₂ := by
          rcases hgap t htS with h3 | h3 <;> intro h4 <;> linarith
        simp only [σf, dif_neg h2]
  let σ := Equiv.ofBijective σf hσ
  let P := PathConnectedSpace.somePath x₀ x
  let Pe := FundamentalGroup.fundamentalGroupMulEquivOfPath P
  refine ⟨inferInstance, fun s ↦ Pe (G (σ s)), fun s ↦ ?_, ?_⟩
  · refine IsLoopAround.ofPath P ?_
    change IsLoopAround (G (σf s)) s
    by_cases hs : ℓ s.1 < c₂
    · have e : σf s = ⟨true, ⟨s.1, Finset.mem_filter.2 ⟨s.2, hs⟩⟩⟩ := dif_pos hs
      rw [e]
      exact hl₁ ⟨s.1, Finset.mem_filter.2 ⟨s.2, hs⟩⟩
    · have e : σf s = ⟨false, ⟨s.1, Finset.mem_filter.2 ⟨s.2, show c₁ < ℓ s.1 by linarith⟩⟩⟩ :=
        dif_neg hs
      rw [e]
      exact hl₂ _
  · exact bijective_lift_map (G ∘ σ) Pe.toMonoidHom Pe.bijective
      (bijective_lift_comp_equiv G σ hG)

theorem loopStatement (n : ℕ) : LoopStatement n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · exact loopStatement_zero
    · exact loopStatement_one
    · exact loopStatement_step (by omega) ih

end Complex.PuncturedPlane

namespace Complex

open PuncturedPlane in
/-- **Free generators of `π₁(ℂ ∖ S)` are loops around the points of `S`**: for a finite set
`S ⊆ ℂ` and `x ∈ ℂ ∖ S` there are loops `γ_s ∈ π₁(ℂ ∖ S, x)` around the points `s ∈ S`
(`IsLoopAround`: `δ · c_s · δ⁻¹` with `c_s` a small counterclockwise circle around `s` whose
disc contains no other point of `S`) such that `FreeGroup S → π₁(ℂ ∖ S, x)`, `s ↦ γ_s`, is an
isomorphism. -/
theorem exists_isLoopAround_basis (S : Finset ℂ) (x : Region Set.univ S) :
    ∃ g : S → FundamentalGroup (Region Set.univ S) x,
      (∀ s : S, IsLoopAround (g s) s) ∧ Function.Bijective (FreeGroup.lift g) :=
  (loopStatement S.card Set.univ isOpen_univ convex_univ S (Set.subset_univ _) rfl x).2

end Complex

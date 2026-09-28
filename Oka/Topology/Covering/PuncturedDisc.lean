/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting

/-!
# Finite coverings of a punctured disc

Let `D* = {z : ℂ | z ≠ 0 ∧ ‖z‖ < r}` and let `p : E → D*` be a covering map with finite fibres.
Then `E` is homeomorphic over `D*` to a finite disjoint union of the coverings
`w ↦ w ^ e` from `{w | w ≠ 0 ∧ ‖w‖ ^ e < r}` to `D*`, with `e ≥ 1`.

The proof lifts the universal covering `exp : H → D*`, `H = exp ⁻¹' D*` (a half-plane, hence
simply connected), through `p`. For a lift `L : H → E`, the integers `k` with
`L (s + 2πik) = L s` form a subgroup `e ℤ` of `ℤ`, and `e > 0` because the fibres of `p` are finite.
Then `w ↦ L (e log w)` is a homeomorphism from `{w | w ≠ 0 ∧ ‖w‖ ^ e < r}` onto the range of `L`,
and the ranges of the lifts partition `E` into finitely many open pieces.

## Main results

- `Complex.puncturedDisc r`: the punctured disc of radius `r` about `0`.
- `IsCoveringMap.exists_homeomorph_sigma_pow_puncturedDisc`: the classification above.
-/

open Set Function Topology

namespace Complex

/-- The punctured disc `{z | z ≠ 0 ∧ ‖z‖ < r}` of radius `r` about `0`. -/
def puncturedDisc (r : ℝ) : Set ℂ := {z | z ≠ 0 ∧ ‖z‖ < r}

theorem mem_puncturedDisc {r : ℝ} {z : ℂ} : z ∈ puncturedDisc r ↔ z ≠ 0 ∧ ‖z‖ < r := Iff.rfl

theorem isOpen_puncturedDisc (r : ℝ) : IsOpen (puncturedDisc r) :=
  isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)

theorem puncturedDisc_subset_compl_zero (r : ℝ) : puncturedDisc r ⊆ {0}ᶜ := fun _ h ↦ h.1

theorem pow_mem_puncturedDisc_iff {r : ℝ} {w : ℂ} {e : ℕ} (he : e ≠ 0) :
    w ^ e ∈ puncturedDisc r ↔ w ≠ 0 ∧ ‖w‖ ^ e < r := by
  simp [mem_puncturedDisc, norm_pow, he]

theorem exp_mem_puncturedDisc_iff {r : ℝ} {s : ℂ} :
    exp s ∈ puncturedDisc r ↔ Real.exp s.re < r := by
  simp [mem_puncturedDisc, exp_ne_zero, norm_exp]

namespace PuncturedDisc

variable {r : ℝ}

/-- The half-plane `exp ⁻¹' D*`, the universal covering space of the punctured disc `D*`. -/
def halfPlane (r : ℝ) : Set ℂ := exp ⁻¹' puncturedDisc r

/-- The universal covering `exp : exp ⁻¹' D* → D*` of the punctured disc `D*`. -/
noncomputable def expCover (r : ℝ) : halfPlane r → puncturedDisc r :=
  (puncturedDisc r).restrictPreimage exp

theorem isCoveringMap_expCover (r : ℝ) : IsCoveringMap (expCover r) :=
  (isCoveringMapOn_exp.mono (puncturedDisc_subset_compl_zero r)).isCoveringMap_restrictPreimage

theorem convex_halfPlane (r : ℝ) : Convex ℝ (halfPlane r) := by
  rcases le_or_gt r 0 with hr | hr
  · convert convex_empty (𝕜 := ℝ) (E := ℂ)
    refine eq_empty_iff_forall_notMem.2 fun s hs ↦ ?_
    have := exp_mem_puncturedDisc_iff.1 hs
    linarith [Real.exp_pos s.re]
  · convert convex_halfSpace_re_lt (Real.log r) using 1
    ext s
    simp [halfPlane, exp_mem_puncturedDisc_iff, Real.lt_log_iff_exp_lt hr]

theorem isOpen_halfPlane (r : ℝ) : IsOpen (halfPlane r) :=
  (isOpen_puncturedDisc r).preimage continuous_exp

instance : LocallyPathConnectedSpace (halfPlane r) :=
  (convex_halfPlane r).locallyPathConnectedSpace

theorem preconnectedSpace_halfPlane : PreconnectedSpace (halfPlane r) :=
  Subtype.preconnectedSpace (convex_halfPlane r).isPreconnected

theorem simplyConnectedSpace_halfPlane [Nonempty (halfPlane r)] :
    SimplyConnectedSpace (halfPlane r) :=
  haveI := (convex_halfPlane r).contractibleSpace (nonempty_coe_sort.1 inferInstance)
  inferInstance

theorem add_mem_halfPlane {s : ℂ} (hs : s ∈ halfPlane r) (k : ℤ) :
    s + k * (2 * Real.pi * I) ∈ halfPlane r := by
  have : exp (s + k * (2 * Real.pi * I)) = exp s := exp_eq_exp_iff_exists_int.2 ⟨k, rfl⟩
  simpa [halfPlane, this] using hs

/-- Translation by `2πik` on the half-plane `exp ⁻¹' D*`, a deck transformation of `exp`. -/
noncomputable def shift (k : ℤ) (s : halfPlane r) : halfPlane r :=
  ⟨s + k * (2 * Real.pi * I), add_mem_halfPlane s.2 k⟩

theorem continuous_shift (k : ℤ) : Continuous (shift (r := r) k) := by
  unfold shift; fun_prop

theorem expCover_shift (k : ℤ) (s : halfPlane r) : expCover r (shift k s) = expCover r s :=
  Subtype.ext (exp_eq_exp_iff_exists_int.2 ⟨k, rfl⟩)

theorem shift_shift (a b : ℤ) (s : halfPlane r) : shift a (shift b s) = shift (a + b) s := by
  ext; simp only [shift]; push_cast; ring

theorem shift_zero (s : halfPlane r) : shift 0 s = s := by
  ext; simp [shift]

theorem exists_shift_eq_of_expCover_eq {s t : halfPlane r} (h : expCover r s = expCover r t) :
    ∃ k : ℤ, s = shift k t := by
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 (congrArg Subtype.val h)
  exact ⟨k, Subtype.ext hk⟩

variable {E : Type*} [TopologicalSpace E] {p : E → puncturedDisc r}

/-- A continuous `L : exp ⁻¹' D* → E` lifting `exp` through `p`. -/
structure IsLift (p : E → puncturedDisc r) (L : halfPlane r → E) : Prop where
  continuous : Continuous L
  comp_eq : p ∘ L = expCover r

theorem exists_isLift (hp : IsCoveringMap p) (s : halfPlane r) (x : E)
    (h : p x = expCover r s) : ∃ L, IsLift p L ∧ L s = x := by
  haveI : Nonempty (halfPlane r) := ⟨s⟩
  haveI := simplyConnectedSpace_halfPlane (r := r)
  obtain ⟨F, ⟨hF, hpF⟩, -⟩ := hp.existsUnique_continuousMap_lifts
    ⟨expCover r, (isCoveringMap_expCover r).continuous⟩ s x h
  exact ⟨F, ⟨F.continuous, hpF⟩, hF⟩

theorem IsLift.ext (hp : IsCoveringMap p) {L L' : halfPlane r → E} (hL : IsLift p L)
    (hL' : IsLift p L') (s : halfPlane r) (h : L s = L' s) : L = L' :=
  haveI := preconnectedSpace_halfPlane (r := r)
  hp.eq_of_comp_eq hL.continuous hL'.continuous (hL.comp_eq.trans hL'.comp_eq.symm) s h

theorem IsLift.comp_shift {L : halfPlane r → E} (hL : IsLift p L) (k : ℤ) :
    IsLift p (L ∘ shift k) where
  continuous := hL.continuous.comp (continuous_shift k)
  comp_eq := by
    funext s
    have := congrFun hL.comp_eq (shift k s)
    simp only [comp_apply] at this ⊢
    rw [this, expCover_shift]

/-- The periods of a lift `L`: the `k : ℤ` with `L (s + 2πik) = L s` for all `s`. -/
def periods (L : halfPlane r → E) : AddSubgroup ℤ where
  carrier := {k | ∀ s, L (shift k s) = L s}
  zero_mem' := by simp [shift_zero]
  add_mem' {a b} ha hb s := by
    simp only [mem_setOf_eq] at *
    rw [← shift_shift, ha, hb]
  neg_mem' {a} ha s := by
    simp only [mem_setOf_eq] at *
    conv_lhs => rw [← ha (shift (-a) s)]
    rw [shift_shift, add_neg_cancel, shift_zero]

theorem mem_periods_of_eq (hp : IsCoveringMap p) {L : halfPlane r → E} (hL : IsLift p L)
    {a b : ℤ} (s : halfPlane r) (h : L (shift a s) = L (shift b s)) :
    a - b ∈ periods L := by
  have := IsLift.ext hp (hL.comp_shift a) (hL.comp_shift b) s h
  intro t
  have ht := congrFun this (shift (-b) t)
  simp only [comp_apply, shift_shift] at ht
  rwa [add_neg_cancel, shift_zero, ← sub_eq_add_neg] at ht

theorem exists_pos_mem_periods (hp : IsCoveringMap p) (hfin : ∀ z, (p ⁻¹' {z}).Finite)
    {L : halfPlane r → E} (hL : IsLift p L) (s : halfPlane r) :
    ∃ n : ℕ, 0 < n ∧ (n : ℤ) ∈ periods L := by
  haveI := (hfin (p (L s))).to_subtype
  let f : ℕ → p ⁻¹' {p (L s)} := fun n ↦ ⟨L (shift n s), by
    simp only [mem_preimage, mem_singleton_iff, ← comp_apply (f := p), hL.comp_eq,
      expCover_shift]⟩
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h := congrArg Subtype.val he
  rcases lt_or_gt_of_ne hab with hab | hab
  · refine ⟨b - a, by omega, ?_⟩
    have := mem_periods_of_eq hp hL s h.symm
    push_cast [Nat.cast_sub hab.le]
    exact this
  · refine ⟨a - b, by omega, ?_⟩
    have := mem_periods_of_eq hp hL s h
    push_cast [Nat.cast_sub hab.le]
    exact this

theorem exists_periods_eq_zmultiples (hp : IsCoveringMap p) (hfin : ∀ z, (p ⁻¹' {z}).Finite)
    {L : halfPlane r → E} (hL : IsLift p L) (s : halfPlane r) :
    ∃ e : ℕ, 0 < e ∧ periods L = AddSubgroup.zmultiples (e : ℤ) := by
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic (periods L)
  rw [← AddSubgroup.zmultiples_eq_closure] at ha
  refine ⟨a.natAbs, ?_, by rw [ha, Int.zmultiples_natAbs]⟩
  obtain ⟨n, hn, hmem⟩ := exists_pos_mem_periods hp hfin hL s
  rw [ha, AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨m, hm⟩ := hmem
  rw [Int.natAbs_pos]
  rintro rfl
  simp at hm
  omega

theorem range_eq_of_mem (hp : IsCoveringMap p) {L L' : halfPlane r → E} (hL : IsLift p L)
    (hL' : IsLift p L') {x : E} (hx : x ∈ range L) (hx' : x ∈ range L') : range L = range L' := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, hb⟩ := hx'
  have h : expCover r a = expCover r b := by
    rw [← congrFun hL.comp_eq a, ← congrFun hL'.comp_eq b, comp_apply, comp_apply, hb]
  obtain ⟨k, rfl⟩ := exists_shift_eq_of_expCover_eq h
  have := IsLift.ext hp hL' (hL.comp_shift k) b hb
  rw [this, range_comp, (show Surjective (shift (r := r) k) from fun t ↦
    ⟨shift (-k) t, by rw [shift_shift, add_neg_cancel, shift_zero]⟩).range_eq, image_univ]

theorem log_mem_halfPlane (z : puncturedDisc r) : log (z : ℂ) ∈ halfPlane r := by
  simpa [halfPlane, exp_log z.2.1] using z.2

theorem expCover_log (z : puncturedDisc r) : expCover r ⟨_, log_mem_halfPlane z⟩ = z :=
  Subtype.ext (exp_log z.2.1)

theorem ne_zero_of_pow_mem {e : ℕ} (he : e ≠ 0) {w : ℂ} (hw : w ^ e ∈ puncturedDisc r) :
    w ≠ 0 := by
  rintro rfl
  exact hw.1 (zero_pow he)

theorem mul_mem_halfPlane {e : ℕ} {s : ℂ} (hs : exp s ^ e ∈ puncturedDisc r) :
    (e : ℂ) * s ∈ halfPlane r := by
  simpa [halfPlane, exp_nat_mul] using hs

/-- The map `w ↦ L (e log w)` from `(· ^ e) ⁻¹' D*` to `E`, for a lift `L` of `exp` with
period `e`. -/
noncomputable def piece (L : halfPlane r → E) {e : ℕ} (he : e ≠ 0)
    (w : (fun w : ℂ ↦ w ^ e) ⁻¹' puncturedDisc r) : E :=
  L ⟨e * log w, mul_mem_halfPlane (by rw [exp_log (ne_zero_of_pow_mem he w.2)]; exact w.2)⟩

theorem piece_exp {L : halfPlane r → E} {e : ℕ} (he : e ≠ 0) (hper : (e : ℤ) ∈ periods L) (s : ℂ)
    (hs : exp s ∈ (fun w : ℂ ↦ w ^ e) ⁻¹' puncturedDisc r) :
    piece L he ⟨exp s, hs⟩ = L ⟨e * s, mul_mem_halfPlane hs⟩ := by
  obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 (exp_log (exp_ne_zero s))
  have hmem : ((e : ℤ) * k) ∈ periods L := by
    simpa [mul_comm] using AddSubgroup.zsmul_mem _ hper k
  unfold piece
  rw [← hmem ⟨e * s, mul_mem_halfPlane hs⟩]
  congr 1
  ext
  simp only [shift, hk]
  push_cast
  ring

theorem comp_piece {L : halfPlane r → E} (hL : IsLift p L) {e : ℕ} (he : e ≠ 0) :
    p ∘ piece L he = (puncturedDisc r).restrictPreimage (fun w : ℂ ↦ w ^ e) := by
  funext w
  have := congrFun hL.comp_eq ⟨e * log w, mul_mem_halfPlane
    (by rw [exp_log (ne_zero_of_pow_mem he w.2)]; exact w.2)⟩
  rw [comp_apply] at this ⊢
  unfold piece
  rw [this]
  ext
  simp [expCover, exp_nat_mul, exp_log (ne_zero_of_pow_mem he w.2)]

theorem continuous_piece {L : halfPlane r → E} (hL : IsLift p L) {e : ℕ} (he : e ≠ 0)
    (hper : (e : ℤ) ∈ periods L) : Continuous (piece L he) := by
  set M := (fun w : ℂ ↦ w ^ e) ⁻¹' puncturedDisc r
  have hM : M ⊆ {0}ᶜ := fun w hw ↦ ne_zero_of_pow_mem he hw
  have hg := (isCoveringMapOn_exp.mono hM).isCoveringMap_restrictPreimage
  have hq := hg.isQuotientMap fun w ↦ ⟨⟨log w, by
    simpa [exp_log (ne_zero_of_pow_mem he w.2)] using w.2⟩,
    Subtype.ext (exp_log (ne_zero_of_pow_mem he w.2))⟩
  rw [hq.continuous_iff]
  have : piece L he ∘ M.restrictPreimage exp =
      fun s ↦ L ⟨e * s.1, mul_mem_halfPlane s.2⟩ := by
    funext s
    exact piece_exp he hper s.1 s.2
  rw [this]
  exact hL.continuous.comp (Continuous.subtype_mk (by fun_prop) _)

theorem isLocalHomeomorph_piece (hp : IsCoveringMap p) {L : halfPlane r → E} (hL : IsLift p L)
    {e : ℕ} (he : e ≠ 0) (hper : (e : ℤ) ∈ periods L) : IsLocalHomeomorph (piece L he) := by
  refine IsLocalHomeomorph.of_comp ?_ hp.isLocalHomeomorph (continuous_piece hL he hper)
  rw [comp_piece hL he]
  exact ((isCoveringMapOn_npow e (by exact_mod_cast he)).mono
    (puncturedDisc_subset_compl_zero r)).isCoveringMap_restrictPreimage.isLocalHomeomorph

theorem injective_piece (hp : IsCoveringMap p) {L : halfPlane r → E} (hL : IsLift p L)
    {e : ℕ} (he : e ≠ 0) (hper : periods L = AddSubgroup.zmultiples (e : ℤ)) :
    Injective (piece L he) := by
  intro w w' h
  have hexp := congrFun (comp_piece hL he) w
  rw [comp_apply, h, ← comp_apply (f := p), comp_piece hL he] at hexp
  unfold piece at h
  set a : halfPlane r := ⟨e * log w, _⟩
  set b : halfPlane r := ⟨e * log w', _⟩
  have hab : expCover r a = expCover r b := by
    rw [← congrFun hL.comp_eq a, ← congrFun hL.comp_eq b, comp_apply, comp_apply, h]
  obtain ⟨k, hk⟩ := exists_shift_eq_of_expCover_eq hab
  have hk' : k - 0 ∈ periods L := mem_periods_of_eq hp hL b (by rw [← hk, shift_zero, h])
  rw [sub_zero, hper, AddSubgroup.mem_zmultiples_iff] at hk'
  obtain ⟨m, rfl⟩ := hk'
  have hlog : log w = log w' + m * (2 * Real.pi * I) := by
    have := congrArg Subtype.val hk
    simp only [a, b, shift, smul_eq_mul] at this
    have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
    apply mul_left_cancel₀ he'
    rw [this]
    simp only [Int.cast_mul, Int.cast_natCast]
    ring
  ext
  rw [← exp_log (ne_zero_of_pow_mem he w.2), ← exp_log (ne_zero_of_pow_mem he w'.2), hlog]
  exact exp_eq_exp_iff_exists_int.2 ⟨m, rfl⟩

theorem range_piece {L : halfPlane r → E} {e : ℕ} (he : e ≠ 0) (hper : (e : ℤ) ∈ periods L) :
    range (piece L he) = range L := by
  refine subset_antisymm (range_subset_iff.2 fun w ↦ ⟨_, rfl⟩) (range_subset_iff.2 fun s ↦ ?_)
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
  have hs : exp (s / e) ∈ (fun w : ℂ ↦ w ^ e) ⁻¹' puncturedDisc r := by
    show exp (s / e) ^ e ∈ _
    rw [← exp_nat_mul, mul_div_cancel₀ _ he']
    exact s.2
  refine ⟨⟨exp (s / e), hs⟩, ?_⟩
  rw [piece_exp he hper]
  congr 1
  ext
  simp [mul_div_cancel₀ _ he']

end PuncturedDisc

end Complex

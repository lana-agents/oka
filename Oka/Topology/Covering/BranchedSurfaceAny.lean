/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.LinearAlgebra.Lagrange
import Oka.Topology.Covering.BranchedSurfaceGen

/-!
# A compact branched covering of the sphere with one point over `∞`, any branch locus

Every finite nonempty `S ⊆ ℂ` is moved onto `{0, 1, …, |S| - 1}` by a self-homeomorphism of `ℂ`
(`BranchedCover.Gen.exists_homeomorph_image_eq_pts`: a shear making the real parts distinct, a
vertical shift by a Lagrange interpolation polynomial moving the points to the real line, and a
piecewise linear homeomorphism of the real line), so the computation of `π₁` of
`Oka/Topology/Covering/BranchedSurfaceGen.lean` applies to every branched covering of the plane
with finite branch locus and one point over `∞`
(`BranchedCover.Gen.exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_finset`).
-/

open Set Metric Topology Complex.PuncturedPlane.LineBasis

namespace BranchedCover.Gen

/-! ### Homeomorphisms of the real line -/

/-- The piecewise linear homeomorphism `t ↦ t` for `t ≤ a`, `t ↦ a + λ (t - a)` for `t ≥ a`. -/
noncomputable def stretch (a l : ℝ) (hl : 0 < l) : ℝ ≃ₜ ℝ where
  toFun t := min t a + l * max (t - a) 0
  invFun t := min t a + max (t - a) 0 / l
  left_inv t := by
    rcases le_total t a with h | h
    · simp [min_eq_left h, max_eq_right (sub_nonpos.2 h)]
    · have h1 : a ≤ a + l * (t - a) := le_add_of_nonneg_right (mul_nonneg hl.le (by linarith))
      simp only [min_eq_right h, max_eq_left (sub_nonneg.2 h)]
      rw [min_eq_right h1, max_eq_left (by linarith)]
      field_simp
      ring
  right_inv t := by
    rcases le_total t a with h | h
    · simp [min_eq_left h, max_eq_right (sub_nonpos.2 h)]
    · have h1 : a ≤ a + (t - a) / l := le_add_of_nonneg_right (div_nonneg (by linarith) hl.le)
      simp only [min_eq_right h, max_eq_left (sub_nonneg.2 h)]
      rw [min_eq_right h1, max_eq_left (by linarith)]
      field_simp
      ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma stretch_apply_of_le {a l : ℝ} (hl : 0 < l) {t : ℝ} (h : t ≤ a) : stretch a l hl t = t := by
  change min t a + l * max (t - a) 0 = t
  simp [min_eq_left h, max_eq_right (sub_nonpos.2 h)]

lemma stretch_apply_of_ge {a l : ℝ} (hl : 0 < l) {t : ℝ} (h : a ≤ t) :
    stretch a l hl t = a + l * (t - a) := by
  change min t a + l * max (t - a) 0 = _
  simp [min_eq_right h, max_eq_left (sub_nonneg.2 h)]

lemma strictMono_stretch {a l : ℝ} (hl : 0 < l) : StrictMono (stretch a l hl) := by
  intro t t' htt'
  rcases le_total t' a with h' | h'
  · rw [stretch_apply_of_le hl h', stretch_apply_of_le hl (htt'.le.trans h')]; exact htt'
  · rw [stretch_apply_of_ge hl h']
    rcases le_total t a with h | h
    · rw [stretch_apply_of_le hl h]
      rcases h.lt_or_eq with h | rfl
      · nlinarith
      · nlinarith
    · rw [stretch_apply_of_ge hl h]; nlinarith

/-- **A strictly increasing homeomorphism of `ℝ` moving a finite set onto `{0, …, k - 1}`.** -/
theorem exists_strictMono_image_eq (T : Finset ℝ) :
    ∃ ψ : ℝ ≃ₜ ℝ, StrictMono ψ ∧
      T.image ψ = (Finset.range T.card).image fun i : ℕ ↦ (i : ℝ) := by
  classical
  induction T using Finset.induction_on_max with
  | empty => exact ⟨Homeomorph.refl ℝ, strictMono_id, by simp⟩
  | insert m T hlt ih =>
    obtain ⟨ψ, hψ, himg⟩ := ih
    have hm : m ∉ T := fun h ↦ lt_irrefl _ (hlt m h)
    rw [Finset.card_insert_of_notMem hm]
    rcases T.eq_empty_or_nonempty with rfl | hne
    · refine ⟨ψ.trans (Homeomorph.addRight (-ψ m)), hψ.add_const _, ?_⟩
      simp
    · set k := T.card
      have hk : 0 < k := Finset.card_pos.2 hne
      -- `ψ m` lies to the right of `k - 1`, the largest point of `ψ(T)`
      have hmax : ∃ x ∈ T, ψ x = ((k - 1 : ℕ) : ℝ) := by
        have : ((k - 1 : ℕ) : ℝ) ∈ T.image ψ := by
          rw [himg]; exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))
        simpa using this
      obtain ⟨x, hx, hxk⟩ := hmax
      have hgt : ((k - 1 : ℕ) : ℝ) < ψ m := hxk ▸ hψ (hlt x hx)
      set a : ℝ := ((k - 1 : ℕ) : ℝ)
      have hl : 0 < 1 / (ψ m - a) := one_div_pos.2 (by linarith)
      refine ⟨ψ.trans (stretch a _ hl), (strictMono_stretch hl).comp hψ, ?_⟩
      have hfix : ∀ y ∈ T, stretch a _ hl (ψ y) = ψ y := fun y hy ↦ by
        refine stretch_apply_of_le hl ?_
        have : ψ y ∈ T.image ψ := Finset.mem_image_of_mem _ hy
        rw [himg, Finset.mem_image] at this
        obtain ⟨i, hi, hie⟩ := this
        rw [← hie]
        simp only [a]
        exact_mod_cast (Nat.le_sub_one_of_lt (Finset.mem_range.1 hi))
      have hmk : stretch a _ hl (ψ m) = ((k : ℕ) : ℝ) := by
        rw [stretch_apply_of_ge hl hgt.le]
        field_simp [(by linarith : ψ m - a ≠ 0)]
        simp only [a]
        push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
        ring
      rw [Finset.image_insert, Finset.range_add_one, Finset.image_insert]
      congr 1
      all_goals first
        | exact hmk
        | (rw [← himg]; exact Finset.image_congr fun y hy ↦ hfix y hy)

/-! ### Moving a finite subset of `ℂ` onto `{0, …, n}` -/

lemma pts_eq (n : ℕ) : pts n = (Finset.range (n + 1)).image fun i : ℕ ↦ (i : ℂ) := by
  ext z
  simp only [mem_pts, Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨i, hi, he⟩ ↦ ⟨i, by omega, he⟩, fun ⟨i, hi, he⟩ ↦ ⟨i, by omega, he⟩⟩

/-- `z ↦ ⟨u(Re z, Im z), v(Re z, Im z)⟩` for an inverse pair of continuous maps of `ℝ²`. -/
noncomputable def homeomorphOfReIm (u v u' v' : ℝ → ℝ → ℝ)
    (hu : Continuous fun p : ℝ × ℝ ↦ u p.1 p.2)
    (hv : Continuous fun p : ℝ × ℝ ↦ v p.1 p.2) (hu' : Continuous fun p : ℝ × ℝ ↦ u' p.1 p.2)
    (hv' : Continuous fun p : ℝ × ℝ ↦ v' p.1 p.2)
    (h1 : ∀ x y, u' (u x y) (v x y) = x ∧ v' (u x y) (v x y) = y)
    (h2 : ∀ x y, u (u' x y) (v' x y) = x ∧ v (u' x y) (v' x y) = y) : ℂ ≃ₜ ℂ where
  toFun z := ⟨u z.re z.im, v z.re z.im⟩
  invFun z := ⟨u' z.re z.im, v' z.re z.im⟩
  left_inv z := by apply Complex.ext <;> simp [h1]
  right_inv z := by apply Complex.ext <;> simp [h2]
  continuous_toFun := Complex.PuncturedPlane.continuous_mk.comp
    ((hu.comp (Complex.continuous_re.prodMk Complex.continuous_im)).prodMk
      (hv.comp (Complex.continuous_re.prodMk Complex.continuous_im)))
  continuous_invFun := Complex.PuncturedPlane.continuous_mk.comp
    ((hu'.comp (Complex.continuous_re.prodMk Complex.continuous_im)).prodMk
      (hv'.comp (Complex.continuous_re.prodMk Complex.continuous_im)))

/-- **Every finite nonempty subset of `ℂ` is moved onto `{0, …, n}` by a homeomorphism.** -/
theorem exists_homeomorph_image_eq_pts (S : Finset ℂ) {n : ℕ} (hS : S.card = n + 1) :
    ∃ h : ℂ ≃ₜ ℂ, S.image h = pts n := by
  classical
  -- a shear making the real parts distinct
  let bad : Finset ℝ := (S ×ˢ S).image fun q ↦ -((q.1.re - q.2.re) / (q.1.im - q.2.im))
  obtain ⟨ε, hε⟩ := Infinite.exists_notMem_finset bad
  let x : ℂ → ℝ := fun z ↦ z.re + ε * z.im
  have hx : Set.InjOn x S := by
    intro s hs s' hs' hss
    simp only [x] at hss
    by_cases him : s.im = s'.im
    · apply Complex.ext _ him
      rw [him] at hss
      linarith
    · exfalso
      apply hε
      refine Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, ?_⟩
      have hd : s.im - s'.im ≠ 0 := sub_ne_zero.2 him
      field_simp
      linarith
  -- the Lagrange polynomial through the points `(x s, Im s)`
  let P : Polynomial ℝ := Lagrange.interpolate S x fun s ↦ s.im
  have hP : ∀ s ∈ S, P.eval (x s) = s.im := fun s hs ↦
    Lagrange.eval_interpolate_at_node _ hx hs
  -- the real line
  obtain ⟨ψ, hψm, hψ⟩ := exists_strictMono_image_eq (S.image x)
  rw [Finset.card_image_of_injOn hx, hS] at hψ
  let h : ℂ ≃ₜ ℂ := homeomorphOfReIm (fun a b ↦ ψ (a + ε * b)) (fun a b ↦ b - P.eval (a + ε * b))
    (fun a b ↦ ψ.symm a - ε * (b + P.eval (ψ.symm a))) (fun a b ↦ b + P.eval (ψ.symm a))
    (ψ.continuous.comp (by fun_prop)) (by
      have := P.continuous
      fun_prop) (by
      have := ψ.symm.continuous
      have := P.continuous
      fun_prop) (by
      have := ψ.symm.continuous
      have := P.continuous
      fun_prop)
    (fun a b ↦ by simp) (fun a b ↦ by simp)
  refine ⟨h, ?_⟩
  have hval : ∀ s ∈ S, h s = ((ψ (x s) : ℝ) : ℂ) := fun s hs ↦ by
    apply Complex.ext
    · rfl
    · change s.im - P.eval (s.re + ε * s.im) = 0
      rw [show s.re + ε * s.im = x s from rfl, hP s hs, sub_self]
  have e : S.image (fun s ↦ ((ψ (x s) : ℝ) : ℂ)) =
      ((S.image x).image ψ).image fun t : ℝ ↦ (t : ℂ) := by
    rw [Finset.image_image, Finset.image_image]
    rfl
  rw [Finset.image_congr hval, e, hψ, Finset.image_image, pts_eq]
  congr 1

/-! ### The fundamental group for any finite branch locus -/

universe u v

/-- **A compact branched covering of `ℙ¹` with finite branch locus `S ∪ {∞}` and one point over
`∞` has a closed surface group as fundamental group.** Let `f : X → ℂ` be closed with finite
fibres, a local homeomorphism outside `f⁻¹(S)` (`S ⊆ ℂ` finite and nonempty), with charts at the
points over `S`, `X` connected and locally path connected, and `j : X → Y` an open embedding
onto `Y ∖ {p}`, `Y` compact Hausdorff with a chart at `p`. Then for every `e₀ ∈ X ∖ f⁻¹(S)`,
`π₁(Y, j e₀) ≃* Π_{g,0}` with `2g + #f⁻¹(S) + d = d |S| + 1`, `d = #f⁻¹(f e₀)`. -/
theorem exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_finset {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, ℂ)} {j : C(X, Y)} {p : Y}
    (S : Finset ℂ) (hSne : S.Nonempty) [T2Space X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [T2Space Y] [CompactSpace Y] (hcl : IsClosedMap f)
    (hfib : ∀ z, (f ⁻¹' {z}).Finite) (hloc : IsLocalHomeomorphOn f {y | f y ∉ S})
    (hchart : ∀ P, f P ∈ S → ∃ φ : OpenPartialHomeomorph X ℂ, P ∈ φ.source)
    (hj : IsOpenEmbedding j) (hrange : range j = {p}ᶜ)
    (hpchart : ∃ φ : OpenPartialHomeomorph Y ℂ, p ∈ φ.source) (e₀ : X) (he₀ : f e₀ ∉ S) :
    ∃ g : ℕ, Nonempty (FundamentalGroup Y (j e₀) ≃* Pi1.SurfaceGroup g 0) ∧
      2 * g + Nat.card {P : X // f P ∈ S} + Nat.card (f ⁻¹' {f e₀}) =
        Nat.card (f ⁻¹' {f e₀}) * S.card + 1 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by have := hSne.card_pos; omega⟩
  obtain ⟨h, hh⟩ := exists_homeomorph_image_eq_pts S hn
  have hmem : ∀ z, h z ∈ pts n ↔ z ∈ S := fun z ↦ by
    rw [← hh, Finset.mem_image]
    exact ⟨fun ⟨a, ha, he⟩ ↦ h.injective he ▸ ha, fun hz ↦ ⟨z, hz, rfl⟩⟩
  let f' : C(X, ℂ) := ⟨h ∘ f, h.continuous.comp f.continuous⟩
  have hcl' : IsClosedMap f' := h.isClosedMap.comp hcl
  have hpre : ∀ z, f' ⁻¹' {z} = f ⁻¹' {h.symm z} := fun z ↦ by
    ext P
    simp only [mem_preimage, mem_singleton_iff, f', ContinuousMap.coe_mk, Function.comp_apply]
    exact ⟨fun hP ↦ by rw [← hP, Homeomorph.symm_apply_apply], fun hP ↦ by
      rw [hP, Homeomorph.apply_symm_apply]⟩
  have hfib' : ∀ z, (f' ⁻¹' {z}).Finite := fun z ↦ by rw [hpre]; exact hfib _
  have hset : {y | f' y ∉ pts n} = {y | f y ∉ S} := by
    ext y; exact not_congr (hmem (f y))
  have hloc' : IsLocalHomeomorphOn f' {y | f' y ∉ pts n} := by
    rw [hset]
    exact (h.isLocalHomeomorph.isLocalHomeomorphOn (s := univ)).comp hloc (mapsTo_univ _ _)
  have hchart' : ∀ P, f' P ∈ pts n → ∃ φ : OpenPartialHomeomorph X ℂ, P ∈ φ.source :=
    fun P hP ↦ hchart P ((hmem _).1 hP)
  obtain ⟨φ, hφ⟩ := hpchart
  obtain ⟨I⟩ := nonempty_inftyData (f := f') (cen n) (ρ := (n : ℝ) / 2) hcl' hfib' hj hrange φ hφ
  have he₀' : f' e₀ ∉ pts n := fun h' ↦ he₀ ((hmem _).1 h')
  obtain ⟨g, hiso, hcard⟩ := exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_charts n hcl'
    hfib' hloc' hchart' hj.isEmbedding hrange I e₀ he₀'
  have c1 : Nat.card {P : X // f' P ∈ pts n} = Nat.card {P : X // f P ∈ S} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P ↦ hmem (f P))
  have c2 : Nat.card (f' ⁻¹' {f' e₀}) = Nat.card (f ⁻¹' {f e₀}) := by
    rw [hpre]
    change Nat.card (f ⁻¹' {h.symm (h (f e₀))}) = _
    rw [Homeomorph.symm_apply_apply]
  rw [c1, c2] at hcard
  refine ⟨g, hiso, ?_⟩
  rw [hn]
  exact hcard

end BranchedCover.Gen

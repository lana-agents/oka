/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.ZeroOneBasis

/-!
# Loops near `∞` in `ℂ ∖ {0, 1}`

A loop in `ℂ ∖ {0, 1}` contained in the exterior `{z | R < ‖z - 1/2‖}` of a disc around `1/2`
of radius `R > 1/2` is conjugate to a power of the circle of radius `R' > R` around `1/2`
(`Complex.PuncturedPlane.ZeroOne.bigArrow`):
`Complex.PuncturedPlane.ZeroOne.exists_eq_conj_zpow_bigArrow`.
With the geometric basis of `Complex.exists_isLoopAround_basis_zero_one` it is therefore
conjugate to a power of `g₀ g₁` (`Complex.PuncturedPlane.ZeroOne.exists_eq_conjArrow_zpow`).

## Proof

The map `w ↦ 1/2 + w⁻¹` (`Complex.PuncturedPlane.ZeroOne.invIncl`) identifies the punctured disc
`B(0, R⁻¹) ∖ {0}` with the exterior, and sends the clockwise circle
`Complex.PuncturedPlane.ZeroOne.smallLoop` to the big circle. The reversed small circle has the
explicit lift `t ↦ log w₀ + 2πit` along `exp`, so it generates `π₁(B(0, R⁻¹) ∖ {0})`
(`Complex.PuncturedPlane.isLoopAround_of_lift`); a loop in the exterior is the image of a loop in
the punctured disc, hence conjugate to a power of the image of the small circle.
-/

open Set Topology Metric CategoryTheory

namespace Complex.PuncturedPlane.ZeroOne

variable {R R' : ℝ}

lemma norm_sub_half_eq_of_mem {z : ℂ} (hz : z ∈ ({0, 1} : Finset ℂ)) : ‖z - 1 / 2‖ = 1 / 2 := by
  rcases Finset.mem_insert.1 hz with rfl | hz
  · rw [zero_sub, norm_neg, norm_div, norm_one, Complex.norm_two]
  · rw [Finset.mem_singleton.1 hz, show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, norm_div, norm_one,
      Complex.norm_two]

lemma pos_of_half_lt (hR : 1 / 2 < R) : 0 < R := by linarith

lemma notMem_of_lt (hR : 1 / 2 < R) {z : ℂ} (hz : R < ‖z - 1 / 2‖) :
    z ∉ ({0, 1} : Finset ℂ) :=
  fun h ↦ by linarith [norm_sub_half_eq_of_mem h]

lemma norm_bigPath_sub (hR : 0 ≤ R) (t : unitInterval) : ‖(bigPath R t : ℂ) - 1 / 2‖ = R := by
  rw [bigPath_apply, sub_sub_cancel_left, norm_neg, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR, mul_one,
    mul_one]

/-- The punctured disc `B(0, R⁻¹) ∖ {0}`, the image of the exterior `{z | R < ‖z - 1/2‖}` under
`z ↦ (z - 1/2)⁻¹`. -/
abbrev Disc (R : ℝ) : Type := Region (ball (0 : ℂ) R⁻¹) {0}

lemma inv_mem_disc (hR : 0 < R) {z : ℂ} (hz : R < ‖z - 1 / 2‖) :
    (z - 1 / 2)⁻¹ ∈ ball (0 : ℂ) R⁻¹ ∧ (z - 1 / 2)⁻¹ ∉ ({0} : Finset ℂ) := by
  have h0 : z - 1 / 2 ≠ 0 := norm_pos_iff.1 (hR.trans hz)
  refine ⟨?_, by simpa using h0⟩
  rw [mem_ball_zero_iff, norm_inv]
  exact (inv_lt_inv₀ (hR.trans hz) hR).2 hz

/-- The point `(z - 1/2)⁻¹` of the punctured disc. -/
noncomputable def discPt (hR : 0 < R) (z : ℂ) (hz : R < ‖z - 1 / 2‖) : Disc R :=
  ⟨(z - 1 / 2)⁻¹, inv_mem_disc hR hz⟩

lemma lt_norm_inv_sub (hR : 0 < R) (w : Disc R) : R < ‖(1 / 2 + (w : ℂ)⁻¹) - 1 / 2‖ := by
  have hw : (w : ℂ) ≠ 0 := fun h ↦ w.2.2 (by simp [h])
  rw [add_sub_cancel_left, norm_inv]
  exact (lt_inv_comm₀ (norm_pos_iff.2 hw) hR).1 (mem_ball_zero_iff.1 w.2.1)

/-- `w ↦ 1/2 + w⁻¹`, from the punctured disc `B(0, R⁻¹) ∖ {0}` onto the exterior
`{z | R < ‖z - 1/2‖}` in `ℂ ∖ {0, 1}`. -/
noncomputable def invIncl (hR : 1 / 2 < R) : C(Disc R, X01) where
  toFun w := ⟨1 / 2 + (w : ℂ)⁻¹, trivial,
    notMem_of_lt hR (lt_norm_inv_sub (pos_of_half_lt hR) w)⟩
  continuous_toFun := (continuous_const.add (continuous_subtype_val.inv₀ fun w h ↦
    w.2.2 (by simp [h]))).subtype_mk _

lemma invIncl_discPt (hR : 1 / 2 < R) (z : X01) (hz : R < ‖(z : ℂ) - 1 / 2‖) :
    invIncl hR (discPt (pos_of_half_lt hR) z hz) = z :=
  Subtype.ext (by simp [invIncl, discPt])

lemma src_lt {y z : X01} (c : Path y z) (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) :
    R < ‖(y : ℂ) - 1 / 2‖ := by
  simpa using hc 0

lemma tgt_lt {y z : X01} (c : Path y z) (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) :
    R < ‖(z : ℂ) - 1 / 2‖ := by
  simpa using hc 1

/-- A path in the exterior `{z | R < ‖z - 1/2‖}`, transported to the punctured disc by
`z ↦ (z - 1/2)⁻¹`. -/
noncomputable def toDisc (hR : 0 < R) {y z : X01} (c : Path y z)
    (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) :
    Path (discPt hR y (src_lt c hc)) (discPt hR z (tgt_lt c hc)) where
  toFun t := discPt hR (c t) (hc t)
  continuous_toFun := (((continuous_subtype_val.comp c.continuous).sub continuous_const).inv₀
    fun t ↦ norm_pos_iff.1 (hR.trans (hc t))).subtype_mk _
  source' := Subtype.ext (by simp [discPt])
  target' := Subtype.ext (by simp [discPt])

@[simp] lemma coe_toDisc (hR : 0 < R) {y z : X01} (c : Path y z)
    (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) (t : unitInterval) :
    (toDisc hR c hc t : ℂ) = ((c t : ℂ) - 1 / 2)⁻¹ :=
  rfl

lemma toDisc_map (hR : 1 / 2 < R) {y z : X01} (c : Path y z)
    (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) :
    (toDisc (pos_of_half_lt hR) c hc).map (invIncl hR).continuous =
      c.cast (invIncl_discPt hR y (src_lt c hc))
        (invIncl_discPt hR z (tgt_lt c hc)) := by
  ext t
  change 1 / 2 + (((c t : ℂ) - 1 / 2)⁻¹)⁻¹ = (c t : ℂ)
  simp

/-- The image of the class of `toDisc c` under `w ↦ 1/2 + w⁻¹` is the class of `c`. -/
lemma map_toDisc (hR : 1 / 2 < R) {y z : X01} (c : Path y z)
    (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) :
    (FundamentalGroupoid.map (invIncl hR)).map
        (⟦toDisc (pos_of_half_lt hR) c hc⟧ : FundamentalGroupoid.mk _ ⟶ FundamentalGroupoid.mk _) =
      eqToHom (congrArg FundamentalGroupoid.mk (invIncl_discPt hR y (src_lt c hc))) ≫
        (⟦c⟧ : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z) ≫
          eqToHom (congrArg FundamentalGroupoid.mk
            (invIncl_discPt hR z (tgt_lt c hc)).symm) := by
  refine Eq.trans ?_ (FundamentalGroupoid.conj_eqToHom
    (p := (⟦c⟧ : Path.Homotopic.Quotient y z)) (invIncl_discPt hR y (src_lt c hc))
      (invIncl_discPt hR z (tgt_lt c hc))).symm
  change Path.Homotopic.Quotient.mk
    ((toDisc (pos_of_half_lt hR) c hc).map (invIncl hR).continuous) = _
  rw [toDisc_map]
  rfl

lemma lt_norm_bigLoop_sub (hR' : 1 / 2 < R') (hRR' : R < R') (t : unitInterval) :
    R < ‖(bigLoop hR' t : ℂ) - 1 / 2‖ := by
  change R < ‖(bigPath R' t : ℂ) - 1 / 2‖
  rw [norm_bigPath_sub (pos_of_half_lt hR').le]
  exact hRR'

/-- The clockwise circle of radius `R'⁻¹` around `0`, the image of the big circle under
`z ↦ (z - 1/2)⁻¹`. -/
noncomputable abbrev smallLoop (hR : 0 < R) (hR' : 1 / 2 < R') (hRR' : R < R') :=
  toDisc hR (bigLoop hR') (lt_norm_bigLoop_sub hR' hRR')

lemma exp_two_pi_sub (t : ℝ) :
    Complex.exp (((2 * Real.pi * (1 - t) : ℝ) : ℂ) * Complex.I) =
      (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Complex.exp_add, ← Complex.exp_two_pi_mul_I]
  congr 1
  push_cast
  ring

lemma groupoid_conj_cancel {C : Type*} [Groupoid C] {a b : C} (β : a ⟶ b) (g : a ⟶ a) :
    g = β ≫ (Groupoid.inv β ≫ g ≫ β) ≫ Groupoid.inv β := by
  simp

lemma groupoid_conj_eq {C : Type*} [Groupoid C] {a a' b b' : C} (e : a = a') (β : a ⟶ b)
    (e₂ : b = b') (g : a' ⟶ a') (B : b' ⟶ b')
    (h : eqToHom e ≫ g ≫ eqToHom e.symm =
      β ≫ (eqToHom e₂ ≫ B ≫ Groupoid.inv (eqToHom e₂)) ≫ Groupoid.inv β) :
    g = (eqToHom e.symm ≫ β ≫ eqToHom e₂) ≫ B ≫
      Groupoid.inv (eqToHom e.symm ≫ β ≫ eqToHom e₂) := by
  subst e e₂
  simpa [Groupoid.inv_eq_inv] using h

/-- **The reversed small circle generates `π₁(B(0, R⁻¹) ∖ {0})`**, and the punctured disc is
path connected. -/
theorem pathConnectedSpace_disc_and_bijective (hR : 1 / 2 < R) (hR' : 1 / 2 < R')
    (hRR' : R < R') :
    PathConnectedSpace (Disc R) ∧ Function.Bijective (FreeGroup.lift fun _ : ({0} : Finset ℂ) ↦
      FundamentalGroup.fromPath (.mk (smallLoop (pos_of_half_lt hR) hR' hRR').symm)) := by
  have hR0 : 0 < R := pos_of_half_lt hR
  set s := smallLoop (pos_of_half_lt hR) hR' hRR'
  -- the reversed small circle has a lift of winding one along `exp`
  set L : ℂ := Complex.log ((-(R' : ℂ) * Complex.I)⁻¹)
  let Γ : Path L (L + 2 * Real.pi * Complex.I) :=
    { toFun := fun t ↦ L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp only [Set.Icc.coe_one, mul_one]; push_cast; ring }
  have hne : (-(R' : ℂ) * Complex.I)⁻¹ ≠ 0 := by
    have : (R' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pos_of_half_lt hR').ne'
    simp [this]
  have hΓ : ∀ t, Complex.exp (Γ t) = (s.symm t : ℂ) - 0 := by
    intro t
    change Complex.exp (L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) =
      (((bigPath R' (unitInterval.symm t) : ℂ) - 1 / 2))⁻¹ - 0
    rw [Complex.exp_add, Complex.exp_log hne, bigPath_apply, sub_sub_cancel_left, sub_zero,
      unitInterval.coe_symm_eq, exp_two_pi_sub]
    have hE := Complex.exp_ne_zero (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
    field_simp
  refine ⟨(loopStatement 1 (ball (0 : ℂ) R⁻¹) isOpen_ball (convex_ball _ _) {0}
      (by simpa using inv_pos.2 hR0) (by simp) (s 0)).1, ?_⟩
  exact (isLoopAround_of_lift isOpen_ball (convex_ball (0 : ℂ) R⁻¹)
    (mem_ball_self (inv_pos.2 hR0)) s.symm Γ hΓ).2

/-- The image of a power of the small circle under `w ↦ 1/2 + w⁻¹` is the conjugate (by the
equality of base points) of the same power of the big circle. -/
theorem map_smallLoop_zpow (hR : 1 / 2 < R) (hR' : 1 / 2 < R') (hRR' : R < R') (n : ℤ) :
    FundamentalGroup.map (invIncl hR) _
        (FundamentalGroup.fromPath (.mk (smallLoop (pos_of_half_lt hR) hR' hRR')) ^ n) =
      conjArrow (eqToHom (congrArg FundamentalGroupoid.mk
        (invIncl_discPt hR (bigBase hR') (src_lt (bigLoop hR') (lt_norm_bigLoop_sub hR' hRR')))))
        (FundamentalGroup.fromArrow (bigArrow hR') ^ n) := by
  rw [map_zpow, map_zpow]
  congr 1
  rw [conjArrow_apply, Groupoid.inv_eq_inv, inv_eqToHom]
  exact map_toDisc hR (bigLoop hR') (lt_norm_bigLoop_sub hR' hRR')

lemma eqToHom_conj_cancel {C : Type*} [Groupoid C] {a b : C} (e : a = b) (g g' : b ⟶ b)
    (h : eqToHom e ≫ g ≫ eqToHom e.symm = eqToHom e ≫ g' ≫ Groupoid.inv (eqToHom e)) :
    g = g' := by
  subst e
  simpa [Groupoid.inv_eq_inv] using h

/-- **Loops at `1/2 - R' i` in the exterior of a disc around `1/2` are powers of the big
circle.** -/
theorem exists_eq_zpow_bigArrow_of_base (hR : 1 / 2 < R) (hR' : 1 / 2 < R') (hRR' : R < R')
    (c : Path (bigBase hR') (bigBase hR')) (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) :
    ∃ k : ℤ, (⟦c⟧ : FundamentalGroupoid.mk (bigBase hR') ⟶ FundamentalGroupoid.mk _) =
      FundamentalGroup.toArrow (FundamentalGroup.fromArrow (bigArrow hR') ^ k) := by
  obtain ⟨-, hbij⟩ := pathConnectedSpace_disc_and_bijective hR hR' hRR'
  set s := smallLoop (pos_of_half_lt hR) hR' hRR'
  obtain ⟨w, hw⟩ := hbij.2 (FundamentalGroup.fromPath (.mk (toDisc (pos_of_half_lt hR) c hc)))
  obtain ⟨m, rfl⟩ := FreeGroup.eq_of_zpow_of_subsingleton
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset ℂ)) w
  rw [map_zpow, FreeGroup.lift_apply_of] at hw
  have hsymm : FundamentalGroup.fromPath (.mk s.symm) = (FundamentalGroup.fromPath (.mk s))⁻¹ :=
    rfl
  rw [hsymm, inv_zpow, ← zpow_neg] at hw
  have key := congrArg (FundamentalGroup.map (invIncl hR) _) hw
  rw [map_smallLoop_zpow] at key
  refine ⟨-m, eqToHom_conj_cancel (congrArg FundamentalGroupoid.mk
    (invIncl_discPt hR (bigBase hR') (src_lt c hc))) _ _ ?_⟩
  exact (map_toDisc hR c hc).symm.trans (key.symm.trans (conjArrow_apply _ _))

/-- **Loops in the exterior of a disc around `1/2` are conjugate to powers of the big circle.**
-/
theorem exists_eq_conj_zpow_bigArrow (hR : 1 / 2 < R) (hR' : 1 / 2 < R') (hRR' : R < R')
    {z : X01} (c : Path z z) (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) :
    ∃ (k : ℤ) (α : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk (bigBase hR')),
      (⟦c⟧ : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk z) =
        α ≫ FundamentalGroup.toArrow (FundamentalGroup.fromArrow (bigArrow hR') ^ k) ≫
          Groupoid.inv α := by
  have hR0 : 0 < R := pos_of_half_lt hR
  obtain ⟨hpc, hbij⟩ := pathConnectedSpace_disc_and_bijective hR hR' hRR'
  haveI := hpc
  set s := smallLoop (pos_of_half_lt hR) hR' hRR'
  -- `c` in the punctured disc is conjugate to a power of the small circle
  have hb := lt_norm_bigLoop_sub hR' hRR'
  let z' := discPt hR0 z (src_lt c hc)
  let sb := discPt hR0 (bigBase hR') (src_lt (bigLoop hR') hb)
  let c' := toDisc hR0 c hc
  let β : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk sb :=
    ⟦PathConnectedSpace.somePath z' sb⟧
  obtain ⟨w, hw⟩ := hbij.2 (Groupoid.inv β ≫ ⟦c'⟧ ≫ β : FundamentalGroup (Disc R) sb)
  obtain ⟨m, rfl⟩ := FreeGroup.eq_of_zpow_of_subsingleton
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset ℂ)) w
  rw [map_zpow, FreeGroup.lift_apply_of] at hw
  let S : FundamentalGroup (Disc R) sb := FundamentalGroup.fromPath (.mk s)
  have hsymm : FundamentalGroup.fromPath (.mk s.symm) = S⁻¹ := rfl
  have hc' : (⟦c'⟧ : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk z') =
      β ≫ FundamentalGroup.toArrow (S ^ (-m)) ≫ Groupoid.inv β := by
    rw [zpow_neg, ← inv_zpow, ← hsymm, hw]
    exact groupoid_conj_cancel β _
  -- map back to the exterior
  let F := FundamentalGroupoid.map (invIncl hR)
  have h0 := invIncl_discPt hR z (src_lt c hc)
  have hbase : invIncl hR sb = bigBase hR' := invIncl_discPt hR _ _
  have hFc : F.map (⟦c'⟧ : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk z') =
      eqToHom (congrArg FundamentalGroupoid.mk h0) ≫ ⟦c⟧ ≫
        eqToHom (congrArg FundamentalGroupoid.mk h0.symm) :=
    map_toDisc hR c hc
  have hS : FundamentalGroup.map (invIncl hR) sb S =
      conjArrow (eqToHom (congrArg FundamentalGroupoid.mk hbase)) (bigArrow hR') := by
    rw [conjArrow_apply, Groupoid.inv_eq_inv, inv_eqToHom]
    exact map_toDisc hR (bigLoop hR') hb
  have hpow : FundamentalGroup.map (invIncl hR) sb (S ^ (-m)) =
      conjArrow (eqToHom (congrArg FundamentalGroupoid.mk hbase))
        (FundamentalGroup.fromArrow (bigArrow hR') ^ (-m)) := by
    rw [map_zpow, hS, map_zpow]
  have key : F.map (⟦c'⟧ : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk z') =
      F.map β ≫ FundamentalGroup.toArrow (FundamentalGroup.map (invIncl hR) sb (S ^ (-m))) ≫
        Groupoid.inv (F.map β) := by
    rw [hc', Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
      Functor.map_inv]
    rfl
  rw [hFc, hpow, conjArrow_apply] at key
  exact ⟨-m, _, groupoid_conj_eq _ _ _ _ _ key⟩

/-- **Loops in the exterior of a disc around `1/2` are conjugate to powers of `g₀ g₁`**: if `X`
is conjugate to the big circle of radius `R' > R` (as `g₀ g₁` is, by
`Complex.exists_isLoopAround_basis_zero_one`), every loop in `{z | R < ‖z - 1/2‖}` is
conjugate along some path to a power of `X`. -/
theorem exists_eq_conjArrow_zpow (hR : 1 / 2 < R) (hR' : 1 / 2 < R') (hRR' : R < R')
    {x : X01} {X : FundamentalGroup X01 x}
    (hX : ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (bigBase hR'),
      X = δ ≫ bigArrow hR' ≫ Groupoid.inv δ)
    {z : X01} (c : Path z z) (hc : ∀ t, R < ‖(c t : ℂ) - 1 / 2‖) :
    ∃ (k : ℤ) (α : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk x),
      (⟦c⟧ : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk z) = conjArrow α (X ^ k) := by
  obtain ⟨δ, rfl⟩ := hX
  obtain ⟨k, α, hk⟩ := exists_eq_conj_zpow_bigArrow hR hR' hRR' c hc
  refine ⟨k, α ≫ Groupoid.inv δ, ?_⟩
  rw [← conjArrow_apply, ← map_zpow, conjArrow_apply, conjArrow_apply, hk]
  simp [Groupoid.inv_eq_inv, Category.assoc]

end Complex.PuncturedPlane.ZeroOne

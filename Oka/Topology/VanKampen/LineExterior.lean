/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.ExteriorLoops
import Oka.Topology.VanKampen.LineBasis

/-!
# Loops near `∞` in `ℂ ∖ S`

Let `S ⊆ ℂ` be finite with `‖s - c‖ ≤ ρ` for all `s ∈ S`, and `ρ < R < R'`. A loop in
`ℂ ∖ S` contained in the exterior `{z | R < ‖z - c‖}` is conjugate to a power of the circle of
radius `R'` around `c` (`Complex.PuncturedPlane.Exterior.exists_eq_conj_zpow_circ`), and a power of
it if it is based on that circle (`Complex.PuncturedPlane.Exterior.exists_eq_zpow_circ_of_base`).
This generalises `Oka/Topology/VanKampen/ExteriorLoops.lean` (the case `S = {0, 1}`, `c = 1/2`):
the map `w ↦ c + w⁻¹` identifies the punctured disc `B(0, R⁻¹) ∖ {0}` with the exterior, and the
reversed image of the circle has an explicit lift of winding one along `exp`.
-/

open Set Topology Metric CategoryTheory Complex.PuncturedPlane.LineBasis
  Complex.PuncturedPlane.ZeroOne

namespace Complex.PuncturedPlane.Exterior

variable {S : Finset ℂ} {c : ℂ} {ρ R R' : ℝ}

lemma notMem_of_lt (hS : ∀ s ∈ S, ‖s - c‖ ≤ ρ) (hR : ρ < R) {z : ℂ} (hz : R < ‖z - c‖) :
    z ∉ S :=
  fun h ↦ by linarith [hS z h]

lemma inv_mem_disc (hR : 0 < R) {z : ℂ} (hz : R < ‖z - c‖) :
    (z - c)⁻¹ ∈ ball (0 : ℂ) R⁻¹ ∧ (z - c)⁻¹ ∉ ({0} : Finset ℂ) := by
  have h0 : z - c ≠ 0 := norm_pos_iff.1 (hR.trans hz)
  refine ⟨?_, by simpa using h0⟩
  rw [mem_ball_zero_iff, norm_inv]
  exact (inv_lt_inv₀ (hR.trans hz) hR).2 hz

/-- The point `(z - c)⁻¹` of the punctured disc. -/
noncomputable def discPt (c : ℂ) (hR : 0 < R) (z : ℂ) (hz : R < ‖z - c‖) : Disc R :=
  ⟨(z - c)⁻¹, inv_mem_disc hR hz⟩

lemma lt_norm_inv_sub (hR : 0 < R) (w : Disc R) : R < ‖(c + (w : ℂ)⁻¹) - c‖ := by
  have hw : (w : ℂ) ≠ 0 := fun h ↦ w.2.2 (by simp [h])
  rw [add_sub_cancel_left, norm_inv]
  exact (lt_inv_comm₀ (norm_pos_iff.2 hw) hR).1 (mem_ball_zero_iff.1 w.2.1)

lemma pos_R (hρ : 0 ≤ ρ) (hR : ρ < R) : 0 < R := lt_of_le_of_lt hρ hR

variable (hS : ∀ s ∈ S, ‖s - c‖ ≤ ρ) (hρ : 0 ≤ ρ) (hR : ρ < R)
include hS hρ hR


/-- `w ↦ c + w⁻¹`, from the punctured disc `B(0, R⁻¹) ∖ {0}` onto the exterior
`{z | R < ‖z - c‖}` in `ℂ ∖ S`. -/
noncomputable def invIncl : C(Disc R, Region Set.univ S) where
  toFun w := ⟨c + (w : ℂ)⁻¹, trivial,
    notMem_of_lt hS hR (lt_norm_inv_sub (pos_R hρ hR) w)⟩
  continuous_toFun := (continuous_const.add (continuous_subtype_val.inv₀ fun w h ↦
    w.2.2 (by simp [h]))).subtype_mk _

lemma invIncl_discPt (z : Region Set.univ S) (hz : R < ‖(z : ℂ) - c‖) :
    invIncl hS hρ hR (discPt c (pos_R hρ hR) z hz) = z :=
  Subtype.ext (by simp [invIncl, discPt])

omit hS hρ hR in
lemma src_lt {y z : Region Set.univ S} (γ : Path y z) (hγ : ∀ t, R < ‖(γ t : ℂ) - c‖) :
    R < ‖(y : ℂ) - c‖ := by
  simpa using hγ 0

omit hS hρ hR in
lemma tgt_lt {y z : Region Set.univ S} (γ : Path y z) (hγ : ∀ t, R < ‖(γ t : ℂ) - c‖) :
    R < ‖(z : ℂ) - c‖ := by
  simpa using hγ 1

omit hS in
/-- A path in the exterior, transported to the punctured disc by `z ↦ (z - c)⁻¹`. -/
noncomputable def toDisc {y z : Region Set.univ S} (γ : Path y z)
    (hγ : ∀ t, R < ‖(γ t : ℂ) - c‖) :
    Path (discPt c (pos_R hρ hR) y (src_lt γ hγ))
      (discPt c (pos_R hρ hR) z (tgt_lt γ hγ)) where
  toFun t := discPt c (pos_R hρ hR) (γ t) (hγ t)
  continuous_toFun := (((continuous_subtype_val.comp γ.continuous).sub continuous_const).inv₀
    fun t ↦ norm_pos_iff.1 ((pos_R hρ hR).trans (hγ t))).subtype_mk _
  source' := Subtype.ext (by simp [discPt])
  target' := Subtype.ext (by simp [discPt])

lemma toDisc_map {y z : Region Set.univ S} (γ : Path y z) (hγ : ∀ t, R < ‖(γ t : ℂ) - c‖) :
    (toDisc hρ hR γ hγ).map (invIncl hS hρ hR).continuous =
      γ.cast (invIncl_discPt hS hρ hR y (src_lt γ hγ))
        (invIncl_discPt hS hρ hR z (tgt_lt γ hγ)) := by
  ext t
  change c + (((γ t : ℂ) - c)⁻¹)⁻¹ = (γ t : ℂ)
  simp

lemma map_toDisc {y z : Region Set.univ S} (γ : Path y z) (hγ : ∀ t, R < ‖(γ t : ℂ) - c‖) :
    (FundamentalGroupoid.map (invIncl hS hρ hR)).map
        (⟦toDisc hρ hR γ hγ⟧ : FundamentalGroupoid.mk _ ⟶ FundamentalGroupoid.mk _) =
      eqToHom (congrArg FundamentalGroupoid.mk (invIncl_discPt hS hρ hR y (src_lt γ hγ))) ≫
        (⟦γ⟧ : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z) ≫
          eqToHom (congrArg FundamentalGroupoid.mk
            (invIncl_discPt hS hρ hR z (tgt_lt γ hγ)).symm) := by
  refine Eq.trans ?_ (FundamentalGroupoid.conj_eqToHom
    (p := (⟦γ⟧ : Path.Homotopic.Quotient y z)) (invIncl_discPt hS hρ hR y (src_lt γ hγ))
      (invIncl_discPt hS hρ hR z (tgt_lt γ hγ))).symm
  change Path.Homotopic.Quotient.mk ((toDisc hρ hR γ hγ).map (invIncl hS hρ hR).continuous) = _
  rw [toDisc_map]
  rfl

variable (hRR' : R < R') (h' : CircleIn Set.univ S c R') (φ : ℝ)
include hRR'

omit hS in
lemma lt_norm_circ (t : unitInterval) : R < ‖(circ h' φ t : ℂ) - c‖ := by
  change R < ‖thetaFun c R' (φ + 2 * Real.pi * t) - c‖
  rw [norm_thetaFun_sub c (by linarith) _]
  exact hRR'

omit hS in
/-- The image of the circle in the punctured disc. -/
noncomputable abbrev smallLoop := toDisc hρ hR (circ h' φ) (lt_norm_circ hρ hR hRR' h' φ)

omit hS in
theorem pathConnectedSpace_disc_and_bijective :
    PathConnectedSpace (Disc R) ∧ Function.Bijective (FreeGroup.lift fun _ : ({0} : Finset ℂ) ↦
      FundamentalGroup.fromPath (.mk (smallLoop hρ hR hRR' h' φ).symm)) := by
  have hR0 : 0 < R := pos_R hρ hR
  have hR'0 : 0 < R' := hR0.trans hRR'
  set s := smallLoop hρ hR hRR' h' φ
  set L : ℂ := ((-Real.log R' : ℝ) : ℂ) + ((-(φ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I
  let Γ : Path L (L + 2 * Real.pi * Complex.I) :=
    { toFun := fun t ↦ L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp only [Set.Icc.coe_one, mul_one]; push_cast; ring }
  have hΓ : ∀ t, Complex.exp (Γ t) = (s.symm t : ℂ) - 0 := by
    intro t
    change Complex.exp (L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) =
      (thetaFun c R' (φ + 2 * Real.pi * (unitInterval.symm t : ℝ)) - c)⁻¹ - 0
    rw [sub_zero, thetaFun, add_sub_cancel_left, unitInterval.coe_symm_eq,
      show L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I = ((-Real.log R' : ℝ) : ℂ) +
        ((-(φ + 2 * Real.pi * (1 - (t : ℝ))) : ℝ) : ℂ) * Complex.I by
          simp only [L]; push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hR'0, mul_inv,
      ← Complex.exp_neg]
    push_cast
    ring_nf
  refine ⟨(loopStatement 1 (ball (0 : ℂ) R⁻¹) isOpen_ball (convex_ball _ _) {0}
      (by simpa using inv_pos.2 hR0) (by simp) (s 0)).1, ?_⟩
  exact (isLoopAround_of_lift isOpen_ball (convex_ball (0 : ℂ) R⁻¹)
    (mem_ball_self (inv_pos.2 hR0)) s.symm Γ hΓ).2

theorem map_smallLoop_zpow (m : ℤ) :
    FundamentalGroup.map (invIncl hS hρ hR) _
        (FundamentalGroup.fromPath (.mk (smallLoop hρ hR hRR' h' φ)) ^ m) =
      conjArrow (eqToHom (congrArg FundamentalGroupoid.mk
        (invIncl_discPt hS hρ hR (theta h' φ) (src_lt (circ h' φ)
          (lt_norm_circ hρ hR hRR' h' φ)))))
        (FundamentalGroup.fromPath (.mk (circ h' φ)) ^ m) := by
  rw [map_zpow, map_zpow]
  congr 1
  rw [conjArrow_apply, Groupoid.inv_eq_inv, inv_eqToHom]
  exact map_toDisc hS hρ hR (circ h' φ) (lt_norm_circ hρ hR hRR' h' φ)

/-- **Loops based on the circle, in the exterior, are powers of the circle.** -/
theorem exists_eq_zpow_circ_of_base (γ : Path (theta h' φ) (theta h' φ))
    (hγ : ∀ t, R < ‖(γ t : ℂ) - c‖) :
    ∃ k : ℤ, FundamentalGroup.fromPath (.mk γ) =
      FundamentalGroup.fromPath (.mk (circ h' φ)) ^ k := by
  obtain ⟨-, hbij⟩ := pathConnectedSpace_disc_and_bijective hρ hR hRR' h' φ
  set s := smallLoop hρ hR hRR' h' φ
  obtain ⟨w, hw⟩ := hbij.2 (FundamentalGroup.fromPath (.mk (toDisc hρ hR γ hγ)))
  obtain ⟨m, rfl⟩ := FreeGroup.eq_of_zpow_of_subsingleton
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset ℂ)) w
  rw [map_zpow, FreeGroup.lift_apply_of] at hw
  have hsymm : FundamentalGroup.fromPath (.mk s.symm) = (FundamentalGroup.fromPath (.mk s))⁻¹ :=
    rfl
  rw [hsymm, inv_zpow, ← zpow_neg] at hw
  have key := congrArg (FundamentalGroup.map (invIncl hS hρ hR) _) hw
  rw [map_smallLoop_zpow] at key
  refine ⟨-m, eqToHom_conj_cancel (congrArg FundamentalGroupoid.mk
    (invIncl_discPt hS hρ hR (theta h' φ) (src_lt γ hγ))) _ _ ?_⟩
  exact (map_toDisc hS hρ hR γ hγ).symm.trans (key.symm.trans (conjArrow_apply _ _))

/-- **Loops in the exterior are conjugate to powers of the circle.** -/
theorem exists_eq_conj_zpow_circ {z : Region Set.univ S} (γ : Path z z)
    (hγ : ∀ t, R < ‖(γ t : ℂ) - c‖) :
    ∃ (k : ℤ) (α : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk (theta h' φ)),
      (⟦γ⟧ : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk z) =
        α ≫ FundamentalGroup.toArrow (FundamentalGroup.fromPath (.mk (circ h' φ)) ^ k) ≫
          Groupoid.inv α := by
  have hR0 : 0 < R := pos_R hρ hR
  obtain ⟨hpc, hbij⟩ := pathConnectedSpace_disc_and_bijective hρ hR hRR' h' φ
  haveI := hpc
  set s := smallLoop hρ hR hRR' h' φ
  have hb := lt_norm_circ hρ hR hRR' h' φ
  let z' := discPt c hR0 z (src_lt γ hγ)
  let sb := discPt c hR0 (theta h' φ) (src_lt (circ h' φ) hb)
  let c' := toDisc hρ hR γ hγ
  let β : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk sb :=
    ⟦PathConnectedSpace.somePath z' sb⟧
  obtain ⟨w, hw⟩ := hbij.2 (Groupoid.inv β ≫ ⟦c'⟧ ≫ β : FundamentalGroup (Disc R) sb)
  obtain ⟨m, rfl⟩ := FreeGroup.eq_of_zpow_of_subsingleton
    (⟨0, Finset.mem_singleton_self 0⟩ : ({0} : Finset ℂ)) w
  rw [map_zpow, FreeGroup.lift_apply_of] at hw
  let Sg : FundamentalGroup (Disc R) sb := FundamentalGroup.fromPath (.mk s)
  have hsymm : FundamentalGroup.fromPath (.mk s.symm) = Sg⁻¹ := rfl
  have hc' : (⟦c'⟧ : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk z') =
      β ≫ FundamentalGroup.toArrow (Sg ^ (-m)) ≫ Groupoid.inv β := by
    rw [zpow_neg, ← inv_zpow, ← hsymm, hw]
    exact groupoid_conj_cancel β _
  let F := FundamentalGroupoid.map (invIncl hS hρ hR)
  have h0 := invIncl_discPt hS hρ hR z (src_lt γ hγ)
  have hbase : invIncl hS hρ hR sb = theta h' φ := invIncl_discPt hS hρ hR _ _
  have hFc : F.map (⟦c'⟧ : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk z') =
      eqToHom (congrArg FundamentalGroupoid.mk h0) ≫ ⟦γ⟧ ≫
        eqToHom (congrArg FundamentalGroupoid.mk h0.symm) :=
    map_toDisc hS hρ hR γ hγ
  have hpow : FundamentalGroup.map (invIncl hS hρ hR) sb (Sg ^ (-m)) =
      conjArrow (eqToHom (congrArg FundamentalGroupoid.mk hbase))
        (FundamentalGroup.fromPath (.mk (circ h' φ)) ^ (-m)) :=
    map_smallLoop_zpow hS hρ hR hRR' h' φ (-m)
  have key : F.map (⟦c'⟧ : FundamentalGroupoid.mk z' ⟶ FundamentalGroupoid.mk z') =
      F.map β ≫ FundamentalGroup.toArrow (FundamentalGroup.map (invIncl hS hρ hR) sb
        (Sg ^ (-m))) ≫ Groupoid.inv (F.map β) := by
    rw [hc', Functor.map_comp, Functor.map_comp, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv,
      Functor.map_inv]
    rfl
  rw [hFc, hpow, conjArrow_apply] at key
  exact ⟨-m, _, groupoid_conj_eq _ _ _ _ _ key⟩

end Complex.PuncturedPlane.Exterior

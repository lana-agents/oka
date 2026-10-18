/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.VanKampen.ZeroOneBasis

/-!
# A geometric basis of `π₁(ℂ ∖ {0, 1, …, n})`

For the points `0, 1, …, n` of the real line (`Complex.PuncturedPlane.LineBasis.pts n`) and a
convex open `C` containing the closed disc of radius `rad n` around `n/2`, every base point `x`
of `C ∖ {0, …, n}` carries a free basis `g 0, …, g n` of `π₁(C ∖ {0, …, n}, x)` with `g i` a loop
around `i` (`IsLoopAround`), such that the ordered product `g 0 * g 1 * ⋯ * g n` is conjugate to
the circle of radius `rad n` around `n/2` (from any starting angle)
(`Complex.PuncturedPlane.LineBasis.exists_basis`; for `C = ℂ` and any radius `R ≥ rad n`,
`Complex.PuncturedPlane.LineBasis.exists_basis_univ`).

## Proof

Induction on `n`, generalising `Complex.exists_isLoopAround_basis_zero_one`. The step cuts
`C ∖ {0, …, n + 1}` by the strip `n + 1/3 < Re z < n + 2/3` into `U = (C ∩ {Re z < n + 2/3}) ∖
{0, …, n}` and `V = (C ∩ {Re z > n + 1/3}) ∖ {n + 1}` (Seifert–van Kampen,
`Complex.PuncturedPlane.bijective_lift_vanKampen`). The new circle `B` (radius `rad (n + 1)`
around `(n + 1)/2`) is cut by the vertical chord `σ` at `Re z = n + 1/2` into a right arc `r` and
a left arc `l`; `r · σ⁻¹` is a loop around `n + 1` in `V` (explicit lift along `exp`), and `σ · l`
is freely homotopic in `U`, by the straight-line homotopy along the rays from `n/2`
(`Complex.PuncturedPlane.LineBasis.eq_conj_of_lerp`), to its radial projection to the circle of
the induction hypothesis, which is a reparametrisation of that circle
(`Complex.PuncturedPlane.LineBasis.homotopic_of_eq_theta`).
-/

open Set Topology Metric CategoryTheory

namespace Complex.PuncturedPlane.LineBasis

/-! ### Paths in `ℝ` mapped to circles -/

section Theta

variable {C : Set ℂ} {S : Finset ℂ} {c : ℂ} {r : ℝ}

/-- The point `c + r e^{iθ}`. -/
noncomputable def thetaFun (c : ℂ) (r : ℝ) (θ : ℝ) : ℂ := c + r * Complex.exp ((θ : ℂ) * Complex.I)

lemma continuous_thetaFun (c : ℂ) (r : ℝ) : Continuous (thetaFun c r) := by
  unfold thetaFun; fun_prop

lemma thetaFun_add_two_pi (c : ℂ) (r θ : ℝ) :
    thetaFun c r (θ + 2 * Real.pi) = thetaFun c r θ := by
  simp only [thetaFun]
  congr 2
  rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I +
    2 * Real.pi * Complex.I by push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I,
    mul_one]

lemma norm_thetaFun_sub (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖thetaFun c r θ - c‖ = r := by
  simp [thetaFun, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr]

/-- A circle contained in `C ∖ S`. -/
def CircleIn (C : Set ℂ) (S : Finset ℂ) (c : ℂ) (r : ℝ) : Prop :=
  ∀ θ : ℝ, thetaFun c r θ ∈ C ∧ thetaFun c r θ ∉ S

/-- `θ ↦ c + r e^{iθ}`, as a map to `C ∖ S`. -/
noncomputable def theta (h : CircleIn C S c r) : C(ℝ, Region C S) :=
  ⟨fun θ ↦ ⟨thetaFun c r θ, h θ⟩, (continuous_thetaFun c r).subtype_mk _⟩

@[simp] lemma coe_theta (h : CircleIn C S c r) (θ : ℝ) : (theta h θ : ℂ) = thetaFun c r θ := rfl

lemma theta_add_two_pi (h : CircleIn C S c r) (θ : ℝ) :
    theta h (θ + 2 * Real.pi) = theta h θ :=
  Subtype.ext (thetaFun_add_two_pi c r θ)

/-- The circle `t ↦ c + r e^{i(φ + 2πt)}`, as a loop in `C ∖ S` at `c + r e^{iφ}`. -/
noncomputable def circ (h : CircleIn C S c r) (φ : ℝ) : Path (theta h φ) (theta h φ) where
  toFun t := theta h (φ + 2 * Real.pi * t)
  continuous_toFun := (theta h).continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp [theta_add_two_pi]

/-- Two paths which are pointwise images under `θ ↦ c + r e^{iθ}` of paths in `ℝ` with the same
endpoints are homotopic. -/
theorem homotopic_of_eq_theta {X : Type*} [TopologicalSpace X] (Θ : C(ℝ, X)) {x y : X}
    (γ₁ γ₂ : Path x y) (f₁ f₂ : C(unitInterval, ℝ)) (h₁ : ∀ t, γ₁ t = Θ (f₁ t))
    (h₂ : ∀ t, γ₂ t = Θ (f₂ t)) (h0 : f₁ 0 = f₂ 0) (h1 : f₁ 1 = f₂ 1) : γ₁.Homotopic γ₂ := by
  haveI := SimplyConnectedSpace.ofContractible ℝ
  let p₁ : Path (f₁ 0) (f₁ 1) := ⟨f₁, rfl, rfl⟩
  let p₂ : Path (f₁ 0) (f₁ 1) := ⟨f₂, h0.symm, h1.symm⟩
  have hp : (p₁.map Θ.continuous).Homotopic (p₂.map Θ.continuous) :=
    (SimplyConnectedSpace.paths_homotopic p₁ p₂).map Θ
  have e0 : x = Θ (f₁ 0) := by rw [← h₁ 0, γ₁.source]
  have e1 : y = Θ (f₁ 1) := by rw [← h₁ 1, γ₁.target]
  have q₁ : γ₁ = (p₁.map Θ.continuous).cast e0 e1 := by
    ext t; exact h₁ t
  have q₂ : γ₂ = (p₂.map Θ.continuous).cast e0 e1 := by
    ext t; exact h₂ t
  have : Path.Homotopic.Quotient.mk γ₁ = Path.Homotopic.Quotient.mk γ₂ := by
    rw [q₁, q₂, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_cast]
    congr 1
    exact Quotient.sound hp
  exact Quotient.exact this

/-- The class of a loop which is pointwise the image of a path in `ℝ` depends only on the
endpoints of that path. -/
theorem mk_eq_of_eq_theta {X : Type*} [TopologicalSpace X] (Θ : C(ℝ, X)) {x y : X}
    (γ₁ γ₂ : Path x y) (f₁ f₂ : C(unitInterval, ℝ)) (h₁ : ∀ t, γ₁ t = Θ (f₁ t))
    (h₂ : ∀ t, γ₂ t = Θ (f₂ t)) (h0 : f₁ 0 = f₂ 0) (h1 : f₁ 1 = f₂ 1) :
    (⟦γ₁⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) = ⟦γ₂⟧ :=
  Quotient.sound (homotopic_of_eq_theta Θ γ₁ γ₂ f₁ f₂ h₁ h₂ h0 h1)

/-- Pointwise lifts of two paths give a pointwise lift of their concatenation. -/
lemma trans_apply_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {y z w : X}
    {e₀ e₁ e₂ : Y} (Θ : Y → X) {p₁ : Path y z} {p₂ : Path z w} {Γ₁ : Path e₀ e₁}
    {Γ₂ : Path e₁ e₂} (h₁ : ∀ t, p₁ t = Θ (Γ₁ t)) (h₂ : ∀ t, p₂ t = Θ (Γ₂ t))
    (t : unitInterval) : (p₁.trans p₂) t = Θ ((Γ₁.trans Γ₂) t) := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact h₁ _
  · exact h₂ _

/-- The affine path from `a` to `b` in `ℝ`. -/
noncomputable def linPath (a b : ℝ) : Path a b where
  toFun t := a + (b - a) * t
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp] lemma linPath_apply (a b : ℝ) (t : unitInterval) : linPath a b t = a + (b - a) * t := rfl

/-- **Circles from different starting angles are conjugate.** -/
theorem circ_conj (h : CircleIn C S c r) (φ ψ : ℝ) :
    ∃ β : FundamentalGroupoid.mk (theta h φ) ⟶ FundamentalGroupoid.mk (theta h ψ),
      (⟦circ h φ⟧ : FundamentalGroupoid.mk _ ⟶ FundamentalGroupoid.mk _) =
        β ≫ ⟦circ h ψ⟧ ≫ Groupoid.inv β := by
  let a : Path (theta h φ) (theta h ψ) := (linPath φ ψ).map (theta h).continuous
  refine ⟨⟦a⟧, ?_⟩
  have e : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (a.trans ((circ h ψ).trans a.symm))) =
      (⟦a⟧ : FundamentalGroupoid.mk (theta h φ) ⟶ FundamentalGroupoid.mk (theta h ψ)) ≫
      (⟦circ h ψ⟧ : FundamentalGroupoid.mk (theta h ψ) ⟶ FundamentalGroupoid.mk (theta h ψ)) ≫
      Groupoid.inv (⟦a⟧ : FundamentalGroupoid.mk (theta h φ) ⟶ FundamentalGroupoid.mk (theta h ψ))
      := rfl
  rw [← e]
  refine mk_eq_of_eq_theta (theta h) _ _ (linPath φ (φ + 2 * Real.pi))
    ((linPath φ ψ).trans ((linPath ψ (ψ + 2 * Real.pi)).trans
      (linPath (ψ + 2 * Real.pi) (φ + 2 * Real.pi)))) (fun t ↦ ?_) (fun t ↦ ?_) (by simp)
    (by simp)
  · change theta h (φ + 2 * Real.pi * t) = _
    simp only [ContinuousMap.coe_mk, linPath_apply]
    congr 1
    ring
  · refine trans_apply_eq (theta h) (fun _ ↦ rfl)
      (trans_apply_eq (theta h) (fun t ↦ ?_) (fun t ↦ ?_)) t
    · change theta h (ψ + 2 * Real.pi * t) = theta h (ψ + (ψ + 2 * Real.pi - ψ) * t)
      congr 1
      ring
    · change theta h (φ + (ψ - φ) * (unitInterval.symm t : ℝ)) =
        theta h (ψ + 2 * Real.pi + (φ + 2 * Real.pi - (ψ + 2 * Real.pi)) * t)
      rw [unitInterval.coe_symm_eq, show ψ + 2 * Real.pi + (φ + 2 * Real.pi -
        (ψ + 2 * Real.pi)) * (t : ℝ) = (φ + (ψ - φ) * (1 - (t : ℝ))) + 2 * Real.pi by ring,
        theta_add_two_pi]

end Theta

/-! ### Straight-line homotopies -/

section Lerp

lemma conj_of_comm {D : Type*} [Groupoid D] {x y : D} (g : x ⟶ x) (β : x ⟶ y) (g' : y ⟶ y)
    (h : g ≫ β = β ≫ g') : g = β ≫ g' ≫ Groupoid.inv β := by
  rw [← Category.assoc, ← h]
  simp

lemma mk_cast_eq {X : Type*} [TopologicalSpace X] {x y x' y' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) :
    FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (p.cast hx hy)) =
      eqToHom (congrArg FundamentalGroupoid.mk hx) ≫
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p) ≫
          eqToHom (congrArg FundamentalGroupoid.mk hy.symm) := by
  rw [FundamentalGroupoid.conj_eqToHom]
  rfl

/-- **Straight-line free homotopy**: if the straight-line homotopy between two loops in `ℂ`
stays in `C ∖ S`, their classes are conjugate. -/
theorem eq_conj_of_lerp {C : Set ℂ} {S : Finset ℂ} {a b : Region C S} (γ₀ : Path a a)
    (γ₁ : Path b b)
    (h : ∀ s t : unitInterval, (1 - (s : ℝ)) • (γ₀ t : ℂ) + (s : ℝ) • (γ₁ t : ℂ) ∈ C ∧
      (1 - (s : ℝ)) • (γ₀ t : ℂ) + (s : ℝ) • (γ₁ t : ℂ) ∉ S) :
    ∃ β : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b,
      (⟦γ₀⟧ : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk a) =
        β ≫ ⟦γ₁⟧ ≫ Groupoid.inv β := by
  let F : ContinuousMap.Homotopy γ₀.toContinuousMap γ₁.toContinuousMap :=
    { toFun := fun p ↦ ⟨(1 - (p.1 : ℝ)) • (γ₀ p.2 : ℂ) + (p.1 : ℝ) • (γ₁ p.2 : ℂ), h p.1 p.2⟩
      continuous_toFun := Continuous.subtype_mk (by fun_prop) _
      map_zero_left := fun t ↦ Subtype.ext (by simp)
      map_one_left := fun t ↦ Subtype.ext (by simp) }
  let I01 : Path (0 : unitInterval) 1 := ⟨ContinuousMap.id _, rfl, rfl⟩
  have H := Path.Homotopic.map_trans_evalAt F I01
  have hA₀ : I01.map (map_continuous γ₀.toContinuousMap) = γ₀.cast γ₀.source γ₀.target := by
    ext; rfl
  have hA₁ : I01.map (map_continuous γ₁.toContinuousMap) = γ₁.cast γ₁.source γ₁.target := by
    ext; rfl
  have e0 : γ₀ 1 = γ₀ 0 := by rw [γ₀.source, γ₀.target]
  have e1 : γ₁ 1 = γ₁ 0 := by rw [γ₁.source, γ₁.target]
  have hE : F.evalAt 1 = (F.evalAt 0).cast e0 e1 := by
    ext s
    change (1 - (s : ℝ)) • (γ₀ 1 : ℂ) + (s : ℝ) • (γ₁ 1 : ℂ) =
      (1 - (s : ℝ)) • (γ₀ 0 : ℂ) + (s : ℝ) • (γ₁ 0 : ℂ)
    rw [e0, e1]
  rw [hA₀, hA₁, hE] at H
  have Q := @Quotient.sound _ (Path.Homotopic.setoid _ _) _ _ H
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _ at Q
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans] at Q
  have Q' : FundamentalGroupoid.fromPath (.mk (γ₀.cast γ₀.source γ₀.target)) ≫
      FundamentalGroupoid.fromPath (.mk ((F.evalAt 0).cast e0 e1)) =
      FundamentalGroupoid.fromPath (.mk (F.evalAt 0)) ≫
        FundamentalGroupoid.fromPath (.mk (γ₁.cast γ₁.source γ₁.target)) := Q
  rw [mk_cast_eq, mk_cast_eq, mk_cast_eq] at Q'
  refine ⟨eqToHom (congrArg FundamentalGroupoid.mk γ₀.source.symm) ≫
    FundamentalGroupoid.fromPath (.mk (F.evalAt 0)) ≫
    eqToHom (congrArg FundamentalGroupoid.mk γ₁.source),
    conj_of_comm (D := FundamentalGroupoid (Region C S)) (FundamentalGroupoid.fromPath (.mk γ₀)) _
      (FundamentalGroupoid.fromPath (.mk γ₁)) ?_⟩
  simp only [Category.assoc] at Q' ⊢
  rw [← cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk γ₀.source)),
    ← cancel_mono (eqToHom (congrArg FundamentalGroupoid.mk γ₁.target.symm))]
  simpa using Q'

end Lerp

/-! ### The points `0, 1, …, n` and their circles -/

section Config

/-- The points `0, 1, …, n` of `ℂ`. -/
noncomputable def pts : ℕ → Finset ℂ
  | 0 => {0}
  | n + 1 => insert (((n + 1 : ℕ) : ℂ)) (pts n)

lemma mem_pts {n : ℕ} {z : ℂ} : z ∈ pts n ↔ ∃ i : ℕ, i ≤ n ∧ (i : ℂ) = z := by
  induction n with
  | zero =>
    simp only [pts, Finset.mem_singleton, nonpos_iff_eq_zero, exists_eq_left, Nat.cast_zero]
    exact eq_comm
  | succ n ih =>
    simp only [pts, Finset.mem_insert, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨n + 1, le_rfl, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact Or.inr ⟨i, by omega, rfl⟩
      · left; rw [show i = n + 1 by omega]

lemma natCast_mem_pts {n i : ℕ} (h : i ≤ n) : (i : ℂ) ∈ pts n := mem_pts.2 ⟨i, h, rfl⟩

lemma card_pts (n : ℕ) : (pts n).card = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pts, Finset.card_insert_of_notMem, ih]
    intro h
    obtain ⟨i, hi, he⟩ := mem_pts.1 h
    have := congrArg Complex.re he
    simp at this
    norm_cast at this
    omega

lemma re_mem_pts {n : ℕ} {z : ℂ} (hz : z ∈ pts n) : ∃ i : ℕ, i ≤ n ∧ z.re = i ∧ z.im = 0 := by
  obtain ⟨i, hi, rfl⟩ := mem_pts.1 hz
  exact ⟨i, hi, by simp, by simp⟩

/-- The centre `n/2`. -/
noncomputable def cen (n : ℕ) : ℂ := (((n : ℝ) / 2 : ℝ) : ℂ)

/-- The radius `n/2 + 1/2 - 1/(n + 4)`. -/
noncomputable def rad (n : ℕ) : ℝ := n / 2 + 1 / 2 - 1 / (n + 4)

lemma half_lt_rad (n : ℕ) : (n : ℝ) / 2 < rad n := by
  have : 1 / ((n : ℝ) + 4) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  unfold rad; linarith

lemma rad_lt (n : ℕ) : rad n < n / 2 + 1 / 2 := by
  have : 0 < 1 / ((n : ℝ) + 4) := by positivity
  unfold rad; linarith

lemma rad_add_half_lt (n : ℕ) : rad n + 1 / 2 < rad (n + 1) := by
  have : 1 / ((n : ℝ) + 1 + 4) < 1 / ((n : ℝ) + 4) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  unfold rad; push_cast; linarith

lemma rad_pos (n : ℕ) : 0 < rad n :=
  lt_of_le_of_lt (by positivity) (half_lt_rad n)

lemma norm_sub_cen_le {n : ℕ} {z : ℂ} (hz : z ∈ pts n) : ‖z - cen n‖ ≤ n / 2 := by
  obtain ⟨i, hi, rfl⟩ := mem_pts.1 hz
  have : (i : ℂ) - cen n = (((i : ℝ) - n / 2 : ℝ) : ℂ) := by simp [cen]
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have : (i : ℝ) ≤ n := by exact_mod_cast hi
  constructor <;> linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]

lemma notMem_pts_of_lt {n : ℕ} {z : ℂ} (h : (n : ℝ) / 2 < ‖z - cen n‖) : z ∉ pts n :=
  fun hz ↦ by linarith [norm_sub_cen_le hz]

lemma circleIn_of_ball {n : ℕ} {C : Set ℂ} (hB : closedBall (cen n) (rad n) ⊆ C) :
    CircleIn C (pts n) (cen n) (rad n) := fun θ ↦ by
  have hn := norm_thetaFun_sub (cen n) (rad_pos n).le θ
  refine ⟨hB (by rw [mem_closedBall, dist_eq_norm, hn]), notMem_pts_of_lt ?_⟩
  rw [hn]; exact half_lt_rad n

end Config

/-! ### Changing the base point and the starting angle -/

section Transport

variable {n : ℕ} {C : Set ℂ} {r : ℝ} (h : CircleIn C (pts n) (cen n) r)

/-- The conclusion of `Complex.PuncturedPlane.LineBasis.exists_basis` at `x` and angle `φ`. -/
def BasisAt (x : Region C (pts n)) (φ : ℝ) : Prop :=
  ∃ g : Fin (n + 1) → FundamentalGroup (Region C (pts n)) x,
    (∀ i, IsLoopAround (g i) ((i : ℕ) : ℂ)) ∧ Function.Bijective (FreeGroup.lift g) ∧
    ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (theta h φ),
      (List.ofFn g).prod = δ ≫ ⟦circ h φ⟧ ≫ Groupoid.inv δ

theorem BasisAt.transport {x y : Region C (pts n)} {φ : ℝ} (hb : BasisAt h y φ)
    (β : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) (ψ : ℝ) : BasisAt h x ψ := by
  obtain ⟨g, hl, hbij, δ, hp⟩ := hb
  obtain ⟨γ, hγ⟩ := circ_conj h φ ψ
  refine ⟨conjArrow β ∘ g, fun i ↦ (hl i).conj _,
    bijective_lift_map g (conjArrow β).toMonoidHom (conjArrow β).bijective hbij,
    β ≫ δ ≫ γ, ?_⟩
  have e : (List.ofFn (conjArrow β ∘ g)).prod = conjArrow β (List.ofFn g).prod := by
    rw [map_list_prod, List.map_ofFn]
  rw [e, hp, conjArrow_apply, hγ]
  simp [Groupoid.inv_eq_inv, Category.assoc]

end Transport

/-! ### The base case: one point -/

theorem basisAt_zero {C : Set ℂ} (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hB : closedBall (cen 0) (rad 0) ⊆ C) (φ : ℝ) :
    BasisAt (circleIn_of_ball hB) (theta (circleIn_of_ball hB) φ) φ := by
  set h := circleIn_of_ball hB
  have hcen : cen 0 = 0 := by simp [cen]
  have h0C : (0 : ℂ) ∈ C := hB (by rw [mem_closedBall, ← hcen, dist_self]; exact (rad_pos 0).le)
  set L : ℂ := (Real.log (rad 0) : ℂ) + (φ : ℂ) * Complex.I
  let Γ : Path L (L + 2 * Real.pi * Complex.I) :=
    { toFun := fun t ↦ L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp only [Set.Icc.coe_one, mul_one]; push_cast; ring }
  have hΓ : ∀ t, Complex.exp (Γ t) = (circ h φ t : ℂ) - 0 := by
    intro t
    change Complex.exp (L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) =
      thetaFun (cen 0) (rad 0) (φ + 2 * Real.pi * t) - 0
    rw [thetaFun, hcen, zero_add, sub_zero,
      show L + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I = (Real.log (rad 0) : ℂ) +
        ((φ + 2 * Real.pi * t : ℝ) : ℂ) * Complex.I by simp only [L]; push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (rad_pos 0)]
  obtain ⟨hl, hbij⟩ := isLoopAround_of_lift hCo hCc h0C (circ h φ) Γ hΓ
  let e : Fin 1 ≃ ({0} : Finset ℂ) :=
    { toFun := fun _ ↦ ⟨0, Finset.mem_singleton_self 0⟩
      invFun := fun _ ↦ 0
      left_inv := fun i ↦ Subsingleton.elim _ _
      right_inv := fun s ↦ Subsingleton.elim _ _ }
  refine ⟨fun _ ↦ FundamentalGroup.fromPath (.mk (circ h φ)), fun i ↦ ?_,
    bijective_lift_comp_equiv _ e hbij, 𝟙 _, ?_⟩
  · fin_cases i
    change IsLoopAround (FundamentalGroup.fromPath _) ((0 : ℕ) : ℂ)
    rw [Nat.cast_zero]
    exact hl
  · simp

/-! ### The geometry of the induction step -/

section Geometry

variable (n : ℕ)

lemma ratio_nonneg : 0 ≤ ((n : ℝ) / 2) / rad (n + 1) :=
  div_nonneg (by positivity) (rad_pos _).le

lemma ratio_lt_one : ((n : ℝ) / 2) / rad (n + 1) < 1 := by
  rw [div_lt_one (rad_pos _)]
  have := half_lt_rad (n + 1)
  push_cast at this
  linarith

/-- The angle of the chord `Re z = n + 1/2` on the circle around `(n + 1)/2`. -/
noncomputable def alpha : ℝ := Real.arccos (((n : ℝ) / 2) / rad (n + 1))

/-- Half the length of the chord. -/
noncomputable def hgt : ℝ := rad (n + 1) * Real.sin (alpha n)

lemma cos_alpha : Real.cos (alpha n) = ((n : ℝ) / 2) / rad (n + 1) :=
  Real.cos_arccos (by linarith [ratio_nonneg n]) (ratio_lt_one n).le

lemma alpha_pos : 0 < alpha n := Real.arccos_pos.2 (ratio_lt_one n)

lemma alpha_le : alpha n ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 (ratio_nonneg n)

lemma hgt_pos : 0 < hgt n :=
  mul_pos (rad_pos _) (Real.sin_pos_of_pos_of_lt_pi (alpha_pos n)
    (by linarith [alpha_le n, Real.pi_pos]))

lemma re_thetaFun (c : ℂ) (r θ : ℝ) : (thetaFun c r θ).re = c.re + r * Real.cos θ := by
  simp [thetaFun, Complex.exp_ofReal_mul_I_re]

lemma im_thetaFun (c : ℂ) (r θ : ℝ) : (thetaFun c r θ).im = c.im + r * Real.sin θ := by
  simp [thetaFun, Complex.exp_ofReal_mul_I_im]

lemma re_cen (m : ℕ) : (cen m).re = m / 2 := by simp [cen]

lemma im_cen (m : ℕ) : (cen m).im = 0 := by simp [cen]

lemma rad_mul_cos_alpha : rad (n + 1) * Real.cos (alpha n) = n / 2 := by
  rw [cos_alpha]; field_simp [(rad_pos (n + 1)).ne']

/-- The lower end `n + 1/2 - i h` of the chord. -/
noncomputable def botP : ℂ := ⟨n + 1 / 2, -hgt n⟩

/-- The upper end `n + 1/2 + i h` of the chord. -/
noncomputable def topP : ℂ := ⟨n + 1 / 2, hgt n⟩

lemma thetaFun_alpha : thetaFun (cen (n + 1)) (rad (n + 1)) (alpha n) = topP n := by
  apply Complex.ext
  · rw [re_thetaFun, re_cen, rad_mul_cos_alpha]; simp [topP]; ring
  · rw [im_thetaFun, im_cen]; simp [topP, hgt]

lemma thetaFun_neg_alpha : thetaFun (cen (n + 1)) (rad (n + 1)) (-alpha n) = botP n := by
  apply Complex.ext
  · rw [re_thetaFun, re_cen, Real.cos_neg, rad_mul_cos_alpha]; simp [botP]; ring
  · rw [im_thetaFun, im_cen, Real.sin_neg]; simp [botP, hgt]

/-- The vertical chord from `botP` to `topP`. -/
noncomputable def chord : Path (botP n) (topP n) where
  toFun t := ⟨n + 1 / 2, hgt n * (2 * t - 1)⟩
  continuous_toFun := continuous_mk.comp (continuous_const.prodMk (by fun_prop))
  source' := by apply Complex.ext <;> simp [botP]
  target' := by apply Complex.ext <;> simp [topP]; ring

/-- The right arc of the circle around `(n + 1)/2`, from `botP` to `topP`. -/
noncomputable def rArc : Path (botP n) (topP n) where
  toFun t := thetaFun (cen (n + 1)) (rad (n + 1)) (-alpha n + 2 * alpha n * t)
  continuous_toFun := (continuous_thetaFun _ _).comp (by fun_prop)
  source' := by simp [thetaFun_neg_alpha]
  target' := by
    rw [show -alpha n + 2 * alpha n * ((1 : unitInterval) : ℝ) = alpha n by simp; ring]
    exact thetaFun_alpha n

/-- The left arc of the circle around `(n + 1)/2`, from `topP` to `botP`. -/
noncomputable def lArc : Path (topP n) (botP n) where
  toFun t := thetaFun (cen (n + 1)) (rad (n + 1)) (alpha n + (2 * Real.pi - 2 * alpha n) * t)
  continuous_toFun := (continuous_thetaFun _ _).comp (by fun_prop)
  source' := by simp [thetaFun_alpha]
  target' := by
    rw [show alpha n + (2 * Real.pi - 2 * alpha n) * ((1 : unitInterval) : ℝ) =
      -alpha n + 2 * Real.pi by simp; ring, thetaFun_add_two_pi]
    exact thetaFun_neg_alpha n

lemma chord_re (t : unitInterval) : (chord n t).re = n + 1 / 2 := rfl

lemma chord_im (t : unitInterval) : (chord n t).im = hgt n * (2 * t - 1) := rfl

lemma rArc_re (t : unitInterval) : n + 1 / 2 ≤ (rArc n t).re := by
  change n + 1 / 2 ≤ (thetaFun _ _ _).re
  rw [re_thetaFun, re_cen]
  have hc : Real.cos (alpha n) ≤ Real.cos (-alpha n + 2 * alpha n * t) := by
    rw [← Real.cos_abs (-alpha n + 2 * alpha n * t)]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [alpha_le n, Real.pi_pos]) ?_
    rw [abs_le]
    have := alpha_pos n
    constructor <;> nlinarith [t.2.1, t.2.2]
  have := mul_le_mul_of_nonneg_left hc (rad_pos (n + 1)).le
  rw [rad_mul_cos_alpha] at this
  push_cast
  linarith

lemma lArc_re (t : unitInterval) : (lArc n t).re ≤ n + 1 / 2 := by
  change (thetaFun _ _ _).re ≤ n + 1 / 2
  rw [re_thetaFun, re_cen]
  set θ := alpha n + (2 * Real.pi - 2 * alpha n) * t
  have ha := alpha_pos n
  have hap := alpha_le n
  have hθ1 : alpha n ≤ θ := by
    have : 0 ≤ (2 * Real.pi - 2 * alpha n) * t :=
      mul_nonneg (by linarith [Real.pi_pos]) t.2.1
    linarith
  have hθ2 : θ ≤ 2 * Real.pi - alpha n := by
    have : (2 * Real.pi - 2 * alpha n) * t ≤ 2 * Real.pi - 2 * alpha n :=
      mul_le_of_le_one_right (by linarith [Real.pi_pos]) t.2.2
    linarith
  have hc : Real.cos θ ≤ Real.cos (alpha n) := by
    rcases le_total θ Real.pi with h | h
    · exact Real.cos_le_cos_of_nonneg_of_le_pi ha.le h hθ1
    · rw [← Real.cos_two_pi_sub θ]
      exact Real.cos_le_cos_of_nonneg_of_le_pi ha.le (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left hc (rad_pos (n + 1)).le
  rw [rad_mul_cos_alpha] at this
  push_cast
  linarith

lemma norm_thetaFun_cen (θ : ℝ) :
    ‖thetaFun (cen (n + 1)) (rad (n + 1)) θ - cen (n + 1)‖ = rad (n + 1) :=
  norm_thetaFun_sub _ (rad_pos _).le θ

lemma norm_chord_sub_le (t : unitInterval) : ‖chord n t - cen (n + 1)‖ ≤ rad (n + 1) := by
  have hr := rad_pos (n + 1)
  rw [← abs_of_pos hr, ← Real.sqrt_sq_eq_abs, Complex.norm_def, Complex.normSq_apply]
  refine Real.sqrt_le_sqrt ?_
  have hs := Real.sin_sq_add_cos_sq (alpha n)
  have hcos := rad_mul_cos_alpha n
  have h2 : (hgt n * (2 * t - 1)) ^ 2 ≤ hgt n ^ 2 := by
    rw [mul_pow]
    have : (2 * (t : ℝ) - 1) ^ 2 ≤ 1 := by nlinarith [t.2.1, t.2.2]
    nlinarith [sq_nonneg (hgt n)]
  simp only [Complex.sub_re, Complex.sub_im, chord_re, chord_im, re_cen, im_cen, sub_zero]
  have e : rad (n + 1) ^ 2 = (n / 2) ^ 2 + hgt n ^ 2 := by
    rw [← hcos, hgt]; nlinarith
  push_cast at e ⊢
  nlinarith

end Geometry

/-! ### The induction step -/

section Step

/-- `{x ∈ C ∖ S | x ∈ P}` is `(C ∩ P) ∖ T` if `S` and `T` agree on `C ∩ P`. -/
noncomputable def pieceEquiv {C P : Set ℂ} {S T : Finset ℂ}
    (hST : ∀ z ∈ C, z ∈ P → (z ∈ S ↔ z ∈ T)) :
    Region (C ∩ P) T ≃ₜ {x : Region C S | x.1 ∈ P} where
  toFun z := ⟨⟨z.1, z.2.1.1, fun h ↦ z.2.2 ((hST _ z.2.1.1 z.2.1.2).1 h)⟩, z.2.1.2⟩
  invFun u := ⟨u.1.1, ⟨u.1.2.1, u.2⟩, fun h ↦ u.1.2.2 ((hST _ u.1.2.1 u.2).2 h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The inclusion `(C ∩ P) ∖ T → C ∖ S`. -/
noncomputable def pieceIncl {C P : Set ℂ} {S T : Finset ℂ}
    (hST : ∀ z ∈ C, z ∈ P → (z ∈ S ↔ z ∈ T)) :
    C(Region (C ∩ P) T, Region C S) :=
  ⟨fun z ↦ (pieceEquiv hST z).1, continuous_subtype_val.comp (pieceEquiv hST).continuous⟩

lemma pathConnectedSpace_pts {n : ℕ} {C : Set ℂ} (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hB : closedBall (cen n) (rad n) ⊆ C) (x : Region C (pts n)) :
    PathConnectedSpace (Region C (pts n)) :=
  (loopStatement (n + 1) C hCo hCc (pts n) (fun z hz ↦ hB (by
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_cen_le hz).trans (half_lt_rad n).le)) (card_pts n) x).1

lemma natCast_ne_of_re {n : ℕ} {z : ℂ} (hz : z.re = n + 1 / 2) (i : ℕ) : (i : ℂ) ≠ z := by
  intro h
  have := congrArg Complex.re h
  rw [hz, Complex.natCast_re] at this
  rcases Nat.lt_or_ge i (n + 1) with hi | hi
  · have : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 hi
    linarith
  · have : ((n + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hi
    push_cast at this
    linarith

theorem basisAt_succ {n : ℕ}
    (ih : ∀ {C : Set ℂ} (_ : IsOpen C) (_ : Convex ℝ C) (hB : closedBall (cen n) (rad n) ⊆ C)
      (x : Region C (pts n)) (φ : ℝ), BasisAt (circleIn_of_ball hB) x φ)
    {C : Set ℂ} (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hB : closedBall (cen (n + 1)) (rad (n + 1)) ⊆ C) :
    ∃ x₀ : Region C (pts (n + 1)), BasisAt (circleIn_of_ball hB) x₀ (-alpha n) := by
  classical
  set h := circleIn_of_ball hB
  set N : ℕ := n + 1 with hN
  let P₁ : Set ℂ := {z | z.re < n + 2 / 3}
  let P₂ : Set ℂ := {z | n + 1 / 3 < z.re}
  have hP₁o : IsOpen P₁ := isOpen_lt Complex.continuous_re continuous_const
  have hP₂o : IsOpen P₂ := isOpen_lt continuous_const Complex.continuous_re
  have hP₁c : Convex ℝ P₁ := convex_halfSpace_lt Complex.reLm.isLinear _
  have hP₂c : Convex ℝ P₂ := convex_halfSpace_gt Complex.reLm.isLinear _
  set C₁ := C ∩ P₁
  set C₂ := C ∩ P₂
  have hcen : ‖cen n - cen N‖ = 1 / 2 := by
    rw [show cen n - cen N = ((-(1 / 2) : ℝ) : ℂ) by simp [cen, hN]; ring]
    simp
  have hB₁ : closedBall (cen n) (rad n) ⊆ C₁ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    refine ⟨hB ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      calc ‖z - cen N‖ ≤ ‖z - cen n‖ + ‖cen n - cen N‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ rad n + 1 / 2 := by rw [hcen]; linarith
        _ ≤ rad N := (rad_add_half_lt n).le
    · change z.re < n + 2 / 3
      have h1 : z.re - (cen n).re ≤ ‖z - cen n‖ := by
        rw [← Complex.sub_re]; exact Complex.re_le_norm _
      rw [re_cen] at h1
      linarith [rad_lt n]
  set h₁ := circleIn_of_ball hB₁
  have hsub : pts n ⊆ pts N := Finset.subset_insert _ _
  -- points of the new pictures
  have hθ : ∀ θ, thetaFun (cen N) (rad N) θ ∈ C ∧ thetaFun (cen N) (rad N) θ ∉ pts N := h
  have hchC : ∀ t, chord n t ∈ C := fun t ↦ hB (by
    rw [mem_closedBall, dist_eq_norm]; exact norm_chord_sub_le n t)
  have hchS : ∀ t, chord n t ∉ pts N := fun t hz ↦ by
    obtain ⟨i, -, he⟩ := mem_pts.1 hz
    exact natCast_ne_of_re (chord_re n t) i he
  have hrA : ∀ t, rArc n t ∈ C ∧ rArc n t ∉ pts N := fun t ↦ hθ _
  have hlA : ∀ t, lArc n t ∈ C ∧ lArc n t ∉ pts N := fun t ↦ hθ _
  have hNC₂ : ((N : ℕ) : ℂ) ∈ C₂ := by
    refine ⟨hB ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, show ((N : ℕ) : ℂ) - cen N = (((N : ℝ) / 2 : ℝ) : ℂ) by
        simp [cen]; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (half_lt_rad N).le
    · change n + 1 / 3 < ((N : ℕ) : ℂ).re
      simp [hN]
      linarith
  have hnN : ∀ z, z ∉ pts N → z ∉ ({((N : ℕ) : ℂ)} : Finset ℂ) := fun z hz h' ↦ by
    rw [Finset.mem_singleton] at h'
    exact hz (h' ▸ natCast_mem_pts le_rfl)
  -- the loops in the pieces
  have hU_ch : ∀ t, chord n t ∈ C₁ ∧ chord n t ∉ pts n := fun t ↦
    ⟨⟨hchC t, show (chord n t).re < n + 2 / 3 by rw [chord_re]; linarith⟩,
      fun h' ↦ hchS t (hsub h')⟩
  have hU_l : ∀ t, lArc n t ∈ C₁ ∧ lArc n t ∉ pts n := fun t ↦
    ⟨⟨(hlA t).1, show (lArc n t).re < n + 2 / 3 by linarith [lArc_re n t]⟩,
      fun h' ↦ (hlA t).2 (hsub h')⟩
  have hV_r : ∀ t, rArc n t ∈ C₂ ∧ rArc n t ∉ ({((N : ℕ) : ℂ)} : Finset ℂ) := fun t ↦
    ⟨⟨(hrA t).1, show n + 1 / 3 < (rArc n t).re by linarith [rArc_re n t]⟩, hnN _ (hrA t).2⟩
  have hV_ch : ∀ t, (chord n).symm t ∈ C₂ ∧
      (chord n).symm t ∉ ({((N : ℕ) : ℂ)} : Finset ℂ) := fun t ↦
    ⟨⟨hchC _, show n + 1 / 3 < (chord n (unitInterval.symm t)).re by
      rw [chord_re]; linarith⟩, hnN _ (hchS _)⟩
  let b₁ : Region C₁ (pts n) := ⟨botP n, by simpa using hU_ch 0⟩
  let b₂ : Region C₂ {((N : ℕ) : ℂ)} := ⟨botP n, by simpa using hV_r 0⟩
  let Dl : Path b₁ b₁ :=
    (restrictPath (chord n) hU_ch).trans (restrictPath (lArc n) hU_l)
  let Dr : Path b₂ b₂ :=
    (restrictPath (rArc n) hV_r).trans (restrictPath (chord n).symm hV_ch)
  -- the right loop is a loop around `n + 1`
  have hE1 : ∀ t, rArc n t - ((N : ℕ) : ℂ) ∈ slitPlane := by
    intro t
    rw [Complex.mem_slitPlane_iff]
    by_cases hs : Real.sin (-alpha n + 2 * alpha n * t) = 0
    · left
      have hθ0 : -alpha n + 2 * alpha n * t = 0 := by
        have ha := alpha_le n
        have hlo : -Real.pi < -alpha n + 2 * alpha n * t := by
          nlinarith [alpha_pos n, t.2.1, Real.pi_pos]
        have hhi : -alpha n + 2 * alpha n * t < Real.pi := by
          nlinarith [alpha_pos n, t.2.2, Real.pi_pos]
        exact (Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).1 hs
      change 0 < (thetaFun (cen N) (rad N) (-alpha n + 2 * alpha n * t) - ((N : ℕ) : ℂ)).re
      rw [hθ0, Complex.sub_re, re_thetaFun, re_cen, Real.cos_zero, Complex.natCast_re]
      have := half_lt_rad N
      linarith
    · right
      change (thetaFun (cen N) (rad N) (-alpha n + 2 * alpha n * t) - ((N : ℕ) : ℂ)).im ≠ 0
      rw [Complex.sub_im, im_thetaFun, im_cen, Complex.natCast_im]
      simpa using mul_ne_zero (rad_pos N).ne' hs
  have hE2 : ∀ t, -((chord n).symm t - ((N : ℕ) : ℂ)) ∈ slitPlane := fun t ↦
    Complex.mem_slitPlane_iff.2 (Or.inl (by
      change 0 < (-(chord n (unitInterval.symm t) - ((N : ℕ) : ℂ))).re
      rw [Complex.neg_re, Complex.sub_re, chord_re, Complex.natCast_re, hN]
      push_cast
      linarith))
  have htop : 0 < (topP n - ((N : ℕ) : ℂ)).im := by simp [topP, hgt_pos]
  have hbot : (botP n - ((N : ℕ) : ℂ)).im < 0 := by simp [botP, hgt_pos]
  let ΓR : Path (Complex.log (botP n - ((N : ℕ) : ℂ)))
      (Complex.log (botP n - ((N : ℕ) : ℂ)) + 2 * Real.pi * Complex.I) :=
    (logPath (rArc n) _ hE1).trans ((negLogPath (chord n).symm _ hE2).cast
      (log_neg_add_pi_of_im_pos htop).symm (log_neg_add_pi_of_im_neg hbot).symm)
  have hΓR : ∀ t, Complex.exp (ΓR t) = (Dr t : ℂ) - ((N : ℕ) : ℂ) :=
    exp_trans_apply (fun z : Region C₂ {((N : ℕ) : ℂ)} ↦ (z : ℂ) - ((N : ℕ) : ℂ))
      (exp_logPath (rArc n) _ hE1) (exp_negLogPath (chord n).symm _ hE2)
  obtain ⟨hlR, hbR⟩ := isLoopAround_of_lift (hCo.inter hP₂o) (hCc.inter hP₂c) hNC₂ Dr ΓR hΓR
  -- the left loop, lifted around `n/2`
  have hE3 : ∀ t, chord n t - cen n ∈ slitPlane := fun t ↦
    Complex.mem_slitPlane_iff.2 (Or.inl (by
      rw [Complex.sub_re, chord_re, re_cen]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
  have hE4 : ∀ t, -(lArc n t - cen n) ∈ slitPlane := by
    intro t
    rw [Complex.mem_slitPlane_iff]
    set θ := alpha n + (2 * Real.pi - 2 * alpha n) * t with hθdef
    by_cases hs : Real.sin θ = 0
    · left
      have hθπ : θ = Real.pi := by
        have hlo : 0 < θ := by
          have : 0 ≤ (2 * Real.pi - 2 * alpha n) * t :=
            mul_nonneg (by linarith [alpha_le n, Real.pi_pos]) t.2.1
          linarith [alpha_pos n]
        have hhi : θ < 2 * Real.pi := by
          have : (2 * Real.pi - 2 * alpha n) * t ≤ 2 * Real.pi - 2 * alpha n :=
            mul_le_of_le_one_right (by linarith [alpha_le n, Real.pi_pos]) t.2.2
          linarith [alpha_pos n]
        rcases (Real.sin_eq_zero_iff_of_lt_of_lt (x := θ - Real.pi) (by linarith)
          (by linarith)).1 (by rw [Real.sin_sub_pi]; simp [hs]) with h'
        linarith
      change 0 < (-(thetaFun (cen N) (rad N) θ - cen n)).re
      rw [Complex.neg_re, Complex.sub_re, re_thetaFun, re_cen, re_cen, hθπ, Real.cos_pi]
      have := half_lt_rad N
      rw [hN] at this ⊢
      push_cast at this ⊢
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · right
      change (-(thetaFun (cen N) (rad N) θ - cen n)).im ≠ 0
      rw [Complex.neg_im, Complex.sub_im, im_thetaFun, im_cen, im_cen]
      simpa using mul_ne_zero (rad_pos N).ne' hs
  have htop' : 0 < (topP n - cen n).im := by simp [topP, hgt_pos, im_cen]
  have hbot' : (botP n - cen n).im < 0 := by simp [botP, hgt_pos, im_cen]
  let ΓL : Path (Complex.log (botP n - cen n))
      (Complex.log (botP n - cen n) + 2 * Real.pi * Complex.I) :=
    (logPath (chord n) _ hE3).trans ((negLogPath (lArc n) _ hE4).cast
      (log_neg_add_pi_of_im_pos htop').symm (log_neg_add_pi_of_im_neg hbot').symm)
  have hΓL : ∀ t, Complex.exp (ΓL t) = (Dl t : ℂ) - cen n :=
    exp_trans_apply (fun z : Region C₁ (pts n) ↦ (z : ℂ) - cen n)
      (exp_logPath (chord n) _ hE3) (exp_negLogPath (lArc n) _ hE4)
  -- the radial projection `E` of the left loop to the circle around `n/2`
  set θ₀ := (Complex.log (botP n - cen n)).im with hθ₀
  have hΓL0 : (ΓL 0).im = θ₀ := by rw [ΓL.source]
  have hΓL1 : (ΓL 1).im = θ₀ + 2 * Real.pi := by
    rw [ΓL.target]; simp [hθ₀]
  let E : Path (theta h₁ θ₀) (theta h₁ θ₀) :=
    { toFun := fun t ↦ theta h₁ (ΓL t).im
      continuous_toFun := (theta h₁).continuous.comp
        (Complex.continuous_im.comp ΓL.continuous)
      source' := by simp only [hΓL0]
      target' := by simp only [hΓL1, theta_add_two_pi] }
  have hEc :=
    mk_eq_of_eq_theta (theta h₁) E (circ h₁ θ₀)
      ⟨fun t ↦ (ΓL t).im, Complex.continuous_im.comp ΓL.continuous⟩
      ⟨fun t ↦ θ₀ + 2 * Real.pi * t, by fun_prop⟩ (fun _ ↦ rfl) (fun _ ↦ rfl)
      (by simpa using hΓL0) (by simpa using hΓL1)
  -- the left loop stays outside the disc of radius `n/2` around `n/2`
  have hlout : ∀ t, (n : ℝ) / 2 < ‖lArc n t - cen n‖ := by
    intro t
    have h1 := norm_sub_norm_le (lArc n t - cen N) (cen n - cen N)
    have h2 : ‖lArc n t - cen N‖ = rad N := norm_thetaFun_cen n _
    rw [show lArc n t - cen N - (cen n - cen N) = lArc n t - cen n by ring, hcen, h2] at h1
    linarith [rad_add_half_lt n, half_lt_rad n]
  have hout : ∀ t, (n : ℝ) / 2 < ‖(Dl t : ℂ) - cen n‖ := by
    intro t
    have hval : (Dl t : ℂ) = ((chord n).trans (lArc n)) t := by
      simp only [Dl, Path.trans_apply]
      split_ifs <;> rfl
    rw [hval, Path.trans_apply]
    split_ifs
    · refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, chord_re, re_cen, abs_of_pos (by
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
      linarith
    · exact hlout _
  obtain ⟨β, hβ⟩ := eq_conj_of_lerp Dl E fun s t ↦ by
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    refine ⟨hCc.inter hP₁c (Dl t).2.1 (E t).2.1 (by linarith) hs0 (by ring), ?_⟩
    refine notMem_pts_of_lt ?_
    set w := ΓL t
    have hD : (Dl t : ℂ) - cen n = (Real.exp w.re : ℂ) * Complex.exp ((w.im : ℂ) * Complex.I) := by
      rw [← hΓL, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      exact (Complex.re_add_im w).symm
    have hEv : (E t : ℂ) - cen n = (rad n : ℂ) * Complex.exp ((w.im : ℂ) * Complex.I) := by
      change thetaFun (cen n) (rad n) w.im - cen n = _
      simp [thetaFun]
    have hρ : (n : ℝ) / 2 < Real.exp w.re := by
      have := hout t
      rw [hD, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le] at this
      exact this
    have e : (1 - (s : ℝ)) • (Dl t : ℂ) + (s : ℝ) • (E t : ℂ) - cen n =
        (((1 - (s : ℝ)) * Real.exp w.re + s * rad n : ℝ) : ℂ) *
          Complex.exp ((w.im : ℂ) * Complex.I) := by
      have e1 : (Dl t : ℂ) = cen n + ((Dl t : ℂ) - cen n) := by ring
      have e2 : (E t : ℂ) = cen n + ((E t : ℂ) - cen n) := by ring
      rw [e1, e2, hD, hEv]
      simp only [Complex.real_smul]
      push_cast
      ring
    set m := min (Real.exp w.re - n / 2) (rad n - n / 2)
    have hm : 0 < m := lt_min (by linarith) (by linarith [half_lt_rad n])
    have a1 : (1 - (s : ℝ)) * m ≤ (1 - s) * (Real.exp w.re - n / 2) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have a2 : (s : ℝ) * m ≤ s * (rad n - n / 2) := mul_le_mul_of_nonneg_left (min_le_right _ _) hs0
    have hX : (n : ℝ) / 2 < (1 - (s : ℝ)) * Real.exp w.re + s * rad n := by nlinarith
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
    exact hX
  -- the induction hypothesis at the lower end of the chord, with angle `θ₀`
  obtain ⟨g', hl', hb', δ₁, hp'⟩ := ih (hCo.inter hP₁o) (hCc.inter hP₁c) hB₁
    b₁ θ₀
  set u : FundamentalGroupoid.mk b₁ ⟶ FundamentalGroupoid.mk b₁ := β ≫ Groupoid.inv δ₁
  set g'' := conjArrow u ∘ g'
  have hp'' : (List.ofFn g'').prod =
      (⟦Dl⟧ : FundamentalGroupoid.mk b₁ ⟶ FundamentalGroupoid.mk b₁) := by
    have e : (List.ofFn g'').prod = conjArrow u (List.ofFn g').prod := by
      rw [map_list_prod, List.map_ofFn]
    rw [e, hp', conjArrow_apply, hβ, hEc]
    simp [u, Groupoid.inv_eq_inv, Category.assoc]
  -- Seifert–van Kampen for the two pieces
  let X := Region C (pts N)
  have hx₀ : botP n ∈ C ∧ botP n ∉ pts N := by
    have h1 := hchC 0
    have h2 := hchS 0
    rw [(chord n).source] at h1 h2
    exact ⟨h1, h2⟩
  let x₀ : X := ⟨botP n, hx₀⟩
  let U : Set X := {x | x.1 ∈ P₁}
  let V : Set X := {x | x.1 ∈ P₂}
  have hre₀ : (botP n).re = n + 1 / 2 := rfl
  have hxU : x₀ ∈ U := show (botP n).re < n + 2 / 3 by rw [hre₀]; linarith
  have hxV : x₀ ∈ V := show n + 1 / 3 < (botP n).re by rw [hre₀]; linarith
  have hST₁ : ∀ z ∈ C, z ∈ P₁ → (z ∈ pts N ↔ z ∈ pts n) := by
    intro z _ hz
    refine ⟨fun h' ↦ ?_, fun h' ↦ hsub h'⟩
    rcases Finset.mem_insert.1 h' with h' | h'
    · exfalso
      change z.re < n + 2 / 3 at hz
      rw [h'] at hz
      simp at hz
      linarith
    · exact h'
  have hST₂ : ∀ z ∈ C, z ∈ P₂ → (z ∈ pts N ↔ z ∈ ({((N : ℕ) : ℂ)} : Finset ℂ)) := by
    intro z _ hz
    refine ⟨fun h' ↦ ?_, fun h' ↦ by
      rw [Finset.mem_singleton] at h'; rw [h']; exact natCast_mem_pts le_rfl⟩
    rcases Finset.mem_insert.1 h' with h' | h'
    · rw [h']; exact Finset.mem_singleton_self _
    · exfalso
      obtain ⟨i, hi, hre, -⟩ := re_mem_pts h'
      change n + 1 / 3 < z.re at hz
      have : (i : ℝ) ≤ n := by exact_mod_cast hi
      linarith
  let φ₁ := pieceEquiv hST₁
  let φ₂ := pieceEquiv hST₂
  haveI hpc₁ : PathConnectedSpace (Region C₁ (pts n)) :=
    pathConnectedSpace_pts (hCo.inter hP₁o) (hCc.inter hP₁c) hB₁ b₁
  haveI hpc₂ : PathConnectedSpace (Region C₂ {((N : ℕ) : ℂ)}) :=
    (loopStatement_one C₂ (hCo.inter hP₂o) (hCc.inter hP₂c) _ (by simpa using hNC₂)
      (Finset.card_singleton _) b₂).1
  have hU : IsPathConnected U :=
    isPathConnected_iff_pathConnectedSpace.2 (φ₁.surjective.pathConnectedSpace φ₁.continuous)
  have hV : IsPathConnected V :=
    isPathConnected_iff_pathConnectedSpace.2 (φ₂.surjective.pathConnectedSpace φ₂.continuous)
  have hstrip : IsSimplyConnected (U ∩ V) := by
    rw [← Topology.IsEmbedding.subtypeVal.isSimplyConnected_image]
    have himg : Subtype.val '' (U ∩ V) = C ∩ P₁ ∩ P₂ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x.2.1, hx.1⟩, hx.2⟩
      · rintro ⟨⟨hzC, h1⟩, h2⟩
        refine ⟨⟨z, hzC, fun hz ↦ ?_⟩, ⟨h1, h2⟩, rfl⟩
        obtain ⟨i, hi, hre, -⟩ := re_mem_pts hz
        change z.re < n + 2 / 3 at h1
        change n + 1 / 3 < z.re at h2
        rw [hre] at h1 h2
        rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
        · have : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 hi'
          linarith
        · have : ((n + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hi'
          push_cast at this
          linarith
    rw [himg]
    haveI := ((hCc.inter hP₁c).inter hP₂c).contractibleSpace ⟨botP n, ⟨hx₀.1, hxU⟩, hxV⟩
    exact SimplyConnectedSpace.ofContractible _
  have hvk : VanKampen.Hypotheses U V x₀ :=
    { isOpen_left := hP₁o.preimage continuous_subtype_val
      isOpen_right := hP₂o.preimage continuous_subtype_val
      union_eq := by
        ext y
        simp only [Set.mem_union, Set.mem_univ, iff_true]
        by_cases hy : y.1.re < n + 2 / 3
        · exact Or.inl hy
        · exact Or.inr (show n + 1 / 3 < y.1.re by linarith)
      mem_inter := ⟨hxU, hxV⟩
      isPathConnected_left := hU
      isPathConnected_right := hV
      isPathConnected_inter := hstrip.isPathConnected }
  let ι : Bool → Type := fun b ↦ cond b (Fin (n + 1)) Unit
  let gg : ∀ b, ι b → FundamentalGroup (VanKampen.piece U V b)
      ⟨x₀, VanKampen.mem_piece_of_mem_inter hvk.mem_inter b⟩ := fun b ↦
    match b with
    | true => fun i ↦ FundamentalGroup.map φ₁.toHomotopyEquiv.toFun b₁ (g'' i)
    | false => fun _ ↦ FundamentalGroup.map φ₂.toHomotopyEquiv.toFun b₂
        (FundamentalGroup.fromPath (.mk Dr))
  have hb'' : Function.Bijective (FreeGroup.lift g'') :=
    bijective_lift_map g' (conjArrow u).toMonoidHom (conjArrow u).bijective hb'
  let eN : Unit ≃ ({((N : ℕ) : ℂ)} : Finset ℂ) :=
    { toFun := fun _ ↦ ⟨_, Finset.mem_singleton_self _⟩
      invFun := fun _ ↦ ()
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  have hG := bijective_lift_vanKampen hvk hstrip gg fun b ↦ match b with
    | true => bijective_lift_map _ _ (map_bijective_of_homotopyEquiv φ₁.toHomotopyEquiv _) hb''
    | false => bijective_lift_map _ _ (map_bijective_of_homotopyEquiv φ₂.toHomotopyEquiv _)
        (bijective_lift_comp_equiv _ eN hbR)
  let G : (Σ b, ι b) → FundamentalGroup X x₀ := fun p ↦
    VanKampen.pieceMap U V hvk.mem_inter p.1 (gg p.1 p.2)
  let σ : Fin (n + 2) ≃ Σ b, ι b :=
    { toFun := fun i ↦ if hi : (i : ℕ) < n + 1 then ⟨true, ⟨i, hi⟩⟩ else ⟨false, ()⟩
      invFun := fun p ↦ match p with
        | ⟨true, j⟩ => Fin.castSucc j
        | ⟨false, _⟩ => Fin.last _
      left_inv := fun i ↦ by
        by_cases hi : (i : ℕ) < n + 1
        · simp only [dif_pos hi]; rfl
        · simp only [dif_neg hi]
          ext
          simp only [Fin.val_last]
          omega
      right_inv := by
        rintro ⟨b, j⟩
        cases b with
        | true => simp [Nat.le_of_lt_succ j.2]
        | false => cases j; simp }
  have hσt : ∀ j : Fin (n + 1), σ j.castSucc = ⟨true, j⟩ := fun j ↦ by
    simp [σ, Nat.le_of_lt_succ j.2]
  have hσl : σ (Fin.last (n + 1)) = ⟨false, ()⟩ := by simp [σ]
  have key₁ : ∀ p : FundamentalGroup (Region C₁ (pts n)) b₁,
      VanKampen.pieceMap U V hvk.mem_inter true
        (FundamentalGroup.map φ₁.toHomotopyEquiv.toFun b₁ p) =
      FundamentalGroup.map (pieceIncl hST₁) b₁ p := fun p ↦ by
    induction p using Quotient.inductionOn
    rfl
  have key₂ : ∀ p : FundamentalGroup (Region C₂ {((N : ℕ) : ℂ)}) b₂,
      VanKampen.pieceMap U V hvk.mem_inter false
        (FundamentalGroup.map φ₂.toHomotopyEquiv.toFun b₂ p) =
      FundamentalGroup.map (pieceIncl hST₂) b₂ p := fun p ↦ by
    induction p using Quotient.inductionOn
    rfl
  have hGt : ∀ j, G ⟨true, j⟩ = FundamentalGroup.map (pieceIncl hST₁) b₁ (g'' j) :=
    fun j ↦ key₁ _
  have hGf : G ⟨false, ()⟩ =
      FundamentalGroup.map (pieceIncl hST₂) b₂ (FundamentalGroup.fromPath (.mk Dr)) := key₂ _
  -- the circle in `X` at `x₀`
  have hXch : ∀ t, chord n t ∈ C ∧ chord n t ∉ pts N := fun t ↦ ⟨hchC t, hchS t⟩
  let BX : Path x₀ x₀ := (restrictPath (rArc n) hrA).trans (restrictPath (lArc n) hlA)
  have hDl : Dl.map (pieceIncl hST₁).continuous =
      (restrictPath (chord n) hXch).trans (restrictPath (lArc n) hlA) := by
    rw [Path.map_trans]
    rfl
  have hDr : Dr.map (pieceIncl hST₂).continuous =
      (restrictPath (rArc n) hrA).trans (restrictPath (chord n) hXch).symm := by
    rw [Path.map_trans]
    rfl
  have hprodX : (show FundamentalGroup X x₀ from FundamentalGroup.map (pieceIncl hST₁) b₁
      (FundamentalGroup.fromPath (.mk Dl))) * (show FundamentalGroup X x₀ from
      FundamentalGroup.map (pieceIncl hST₂) b₂ (FundamentalGroup.fromPath (.mk Dr))) =
        FundamentalGroup.fromPath (.mk BX) := by
    rw [FundamentalGroup.mul_def]
    change Path.Homotopic.Quotient.trans (.mk (Dr.map (pieceIncl hST₂).continuous))
      (.mk (Dl.map (pieceIncl hST₁).continuous)) = Path.Homotopic.Quotient.mk BX
    rw [hDl, hDr, ← Path.Homotopic.Quotient.mk_trans]
    exact ZeroOne.mk_trans_symm_trans _ _ _
  have e₀ : x₀ = theta h (-alpha n) := Subtype.ext (thetaFun_neg_alpha n).symm
  have hBX : FundamentalGroupoid.fromPath (.mk BX) =
      FundamentalGroupoid.fromPath (.mk ((circ h (-alpha n)).cast e₀ e₀)) := by
    refine mk_eq_of_eq_theta (theta h) _ _
      ((linPath (-alpha n) (alpha n)).trans (linPath (alpha n) (2 * Real.pi - alpha n)))
      (linPath (-alpha n) (-alpha n + 2 * Real.pi))
      (trans_apply_eq (theta h) (fun t ↦ Subtype.ext ?_) (fun t ↦ Subtype.ext ?_))
      (fun t ↦ Subtype.ext ?_) (by simp) (by simp; ring)
    · change thetaFun _ _ (-alpha n + 2 * alpha n * t) = thetaFun _ _ (-alpha n + _ * t)
      congr 1; ring
    · change thetaFun _ _ (alpha n + (2 * Real.pi - 2 * alpha n) * t) =
        thetaFun _ _ (alpha n + _ * t)
      congr 1; ring
    · change thetaFun _ _ (-alpha n + 2 * Real.pi * t) = thetaFun _ _ (-alpha n + _ * t)
      congr 1; ring
  refine ⟨x₀, G ∘ σ, fun i ↦ ?_, bijective_lift_comp_equiv G σ hG,
    eqToHom (congrArg FundamentalGroupoid.mk e₀), ?_⟩
  · by_cases hi : (i : ℕ) < n + 1
    · have hσi : σ i = ⟨true, ⟨i, hi⟩⟩ := dif_pos hi
      change IsLoopAround (G (σ i)) _
      rw [hσi, hGt]
      exact ((hl' ⟨i, hi⟩).conj _).map (C' := C) (S' := pts N) Set.inter_subset_left
        (fun s' hs' hC ↦ (hST₁ s' hC.1 hC.2).1 hs') (pieceIncl hST₁) (fun _ ↦ rfl)
    · have hiN : (i : ℕ) = n + 1 := by omega
      have hσi : σ i = ⟨false, ()⟩ := dif_neg hi
      change IsLoopAround (G (σ i)) _
      rw [hσi, hGf, hiN]
      exact hlR.map (C' := C) (S' := pts N) Set.inter_subset_left
        (fun s' hs' hC ↦ (hST₂ s' hC.1 hC.2).1 hs') (pieceIncl hST₂) (fun _ ↦ rfl)
  · let M : FundamentalGroup (Region C₁ (pts n)) b₁ →* FundamentalGroup X x₀ :=
      FundamentalGroup.map (pieceIncl hST₁) b₁
    have hl1 : (List.ofFn fun j : Fin (n + 1) ↦ (G ∘ σ) j.castSucc) = (List.ofFn g'').map M := by
      rw [List.map_ofFn]
      congr 1
      funext j
      simp only [Function.comp_apply, hσt, hGt]
      rfl
    rw [List.ofFn_succ', List.prod_concat, hl1, ← map_list_prod, hp'']
    simp only [Function.comp_apply, hσl, hGf]
    refine Eq.trans hprodX ?_
    change FundamentalGroupoid.fromPath (.mk BX) = _
    rw [hBX, mk_cast_eq]
    simp [Groupoid.inv_eq_inv]

end Step

/-! ### The main theorem -/

/-- **A geometric basis of `π₁(C ∖ {0, …, n})`**: for `C` convex open containing the closed disc
of radius `rad n` around `n/2`, every base point `x` and every starting angle `φ`, there are loops
`g i` around `i` forming a free basis of `π₁(C ∖ {0, …, n}, x)` whose ordered product
`g 0 * ⋯ * g n` is conjugate to the circle of radius `rad n` around `n/2`. -/
theorem exists_basis (n : ℕ) : ∀ {C : Set ℂ} (_ : IsOpen C) (_ : Convex ℝ C)
    (hB : closedBall (cen n) (rad n) ⊆ C) (x : Region C (pts n)) (φ : ℝ),
    BasisAt (circleIn_of_ball hB) x φ := by
  induction n with
  | zero =>
    intro C hCo hCc hB x φ
    haveI := pathConnectedSpace_pts hCo hCc hB x
    exact (basisAt_zero hCo hCc hB φ).transport _ ⟦PathConnectedSpace.somePath x _⟧ φ
  | succ n ih =>
    intro C hCo hCc hB x φ
    obtain ⟨x₀, hx₀⟩ := basisAt_succ (fun hCo hCc hB x φ ↦ ih hCo hCc hB x φ) hCo hCc hB
    haveI := pathConnectedSpace_pts hCo hCc hB x
    exact hx₀.transport _ ⟦PathConnectedSpace.somePath x x₀⟧ φ

lemma circleIn_univ {n : ℕ} {R : ℝ} (hR : rad n ≤ R) : CircleIn Set.univ (pts n) (cen n) R :=
  fun θ ↦ ⟨trivial, notMem_pts_of_lt (by
    rw [norm_thetaFun_sub _ ((rad_pos n).le.trans hR)]; linarith [half_lt_rad n])⟩

/-- **A geometric basis of `π₁(ℂ ∖ {0, …, n})` whose product is a big circle**: for every
`R ≥ rad n`, every base point and every starting angle `φ`, there is a free basis of loops `g i`
around `i` with `g 0 * ⋯ * g n` conjugate to the circle of radius `R` around `n/2`. -/
theorem exists_basis_univ (n : ℕ) {R : ℝ} (hR : rad n ≤ R) (x : Region Set.univ (pts n))
    (φ : ℝ) : BasisAt (circleIn_univ hR) x φ := by
  obtain ⟨g, hl, hb, δ, hp⟩ := exists_basis n isOpen_univ convex_univ (subset_univ _) x φ
  obtain ⟨β, hβ⟩ := eq_conj_of_lerp (circ (circleIn_of_ball (subset_univ _)) φ)
    (circ (circleIn_univ hR) φ) fun s t ↦ by
      refine ⟨trivial, notMem_pts_of_lt ?_⟩
      change (n : ℝ) / 2 < ‖(1 - (s : ℝ)) • thetaFun (cen n) (rad n) (φ + 2 * Real.pi * t) +
        (s : ℝ) • thetaFun (cen n) R (φ + 2 * Real.pi * t) - cen n‖
      have e : (1 - (s : ℝ)) • thetaFun (cen n) (rad n) (φ + 2 * Real.pi * t) +
          (s : ℝ) • thetaFun (cen n) R (φ + 2 * Real.pi * t) - cen n =
          (((1 - (s : ℝ)) * rad n + s * R : ℝ) : ℂ) *
            Complex.exp (((φ + 2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
        simp only [thetaFun, Complex.real_smul]
        push_cast
        ring
      have hs0 : 0 ≤ (s : ℝ) := s.2.1
      have hs1 : (s : ℝ) ≤ 1 := s.2.2
      have hX : (n : ℝ) / 2 < (1 - (s : ℝ)) * rad n + s * R := by
        nlinarith [half_lt_rad n]
      rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
      exact hX
  refine ⟨g, hl, hb, δ ≫ β, ?_⟩
  rw [hp, hβ]
  simp [Groupoid.inv_eq_inv, Category.assoc]

end Complex.PuncturedPlane.LineBasis

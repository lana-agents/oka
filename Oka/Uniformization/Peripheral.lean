/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Uniformization.Generators
import Oka.Uniformization.SL2Facts

/-!
# The monodromy around a lattice point is the commutator of the edge pairings

Let `Λ = ℤ t + ℤ` and `ψ : ℍ → ℂ ∖ Λ` with deck group `Γ` and edge pairings `A`, `B`
(`Oka/Uniformization/Generators.lean`). Near the lattice point `0`, the four parallelograms meeting
at `0` are the quadrants `Q₁ = {x, y ≥ 0}`, `Q₂ = {x ≤ 0 ≤ y}`, `Q₃ = {x, y ≤ 0}`,
`Q₄ = {y ≤ 0 ≤ x}` of the lattice coordinates, and over a small punctured disc `D*` the lifts
`σ₁ = sK`, `σ₂ = A⁻¹ sK(· + 1)`, `σ₃ = A⁻¹ B⁻¹ sK(· + 1 + t)`, `σ₄ = A⁻¹ B⁻¹ A sK(· + t)` of the
four pieces glue along the rays `Q₁ ∩ Q₂`, `Q₂ ∩ Q₃`, `Q₃ ∩ Q₄`, while `σ₄ = C σ₁` on `Q₄ ∩ Q₁`,
where `C = A⁻¹ B⁻¹ A B`.

Lifting `exp : {Re s < log r₀} → D*` through `ψ` to `Σ`, and following it across the five strips
`0 ≤ Im s ≤ α`, `α ≤ Im s ≤ π`, …, `2π ≤ Im s ≤ 2π + α` (`α = arg t`, the angle of the lattice
direction `t`), gives the monodromy relation (`Peripheral.Σ_add_two_pi`)

`Σ (s + 2π i) = C • Σ s`,

and `Σ` is holomorphic (`Peripheral.differentiableOn_Σ`).
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups Real

namespace Uniformization

namespace Peripheral

open Generators

variable {t : ℍ} (U : Unif (Lt t))

/-! ### A small disc about `0` -/

theorem exists_r₀ (t : ℍ) :
    ∃ r > 0, ∀ z ∈ ball (0 : ℂ) r, |cx t z| < 1 / 2 ∧ |cy t z| < 1 / 2 := by
  have hO : IsOpen {z : ℂ | |cx t z| < 1 / 2 ∧ |cy t z| < 1 / 2} :=
    (isOpen_lt (continuous_abs.comp (continuous_cx t)) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_cy t)) continuous_const)
  have h0 : (0 : ℂ) ∈ {z : ℂ | |cx t z| < 1 / 2 ∧ |cy t z| < 1 / 2} := by
    simp [cx, cy]
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hO 0 h0
  exact ⟨r, hr, fun z hz ↦ hsub hz⟩

/-- A radius `r₀` such that `ball 0 r₀` lies in the box `|x|, |y| < 1/2`. -/
noncomputable def r₀ (t : ℍ) : ℝ := (exists_r₀ t).choose

theorem r₀_pos : 0 < r₀ t := (exists_r₀ t).choose_spec.1

theorem box {z : ℂ} (hz : z ∈ ball (0 : ℂ) (r₀ t)) : |cx t z| < 1 / 2 ∧ |cy t z| < 1 / 2 :=
  (exists_r₀ t).choose_spec.2 z hz

/-- The punctured disc `D*`. -/
def Dst (t : ℍ) : Set ℂ := ball 0 (r₀ t) \ {0}

theorem eq_zero_of_cx_cy {z : ℂ} (hx : cx t z = 0) (hy : cy t z = 0) : z = 0 := by
  rw [eq_cx_cy t z, hx, hy]; simp

theorem Dst_notMem {z : ℂ} (hz : z ∈ Dst t) : z ∉ (Lt t).lattice := by
  intro hl
  obtain ⟨m, n, hm, hn⟩ := (mem_lattice_iff t z).mp hl
  obtain ⟨hx, hy⟩ := box hz.1
  rw [hm] at hy; rw [hn] at hx
  have hm0 : m = 0 := by
    have : |(m : ℝ)| < 1 := by linarith
    have : |m| < 1 := by exact_mod_cast this
    have := abs_lt.mp this
    omega
  have hn0 : n = 0 := by
    have : |(n : ℝ)| < 1 := by linarith
    have : |n| < 1 := by exact_mod_cast this
    have := abs_lt.mp this
    omega
  subst hm0; subst hn0
  exact hz.2 (eq_zero_of_cx_cy (by simpa using hn) (by simpa using hm))

/-! ### The four quadrants and the lifts over them -/

/-- `Q₁ = {x ≥ 0, y ≥ 0}`. -/
def Q₁ (t : ℍ) : Set ℂ := {z | 0 ≤ cx t z ∧ 0 ≤ cy t z}
/-- `Q₂ = {x ≤ 0, y ≥ 0}`. -/
def Q₂ (t : ℍ) : Set ℂ := {z | cx t z ≤ 0 ∧ 0 ≤ cy t z}
/-- `Q₃ = {x ≤ 0, y ≤ 0}`. -/
def Q₃ (t : ℍ) : Set ℂ := {z | cx t z ≤ 0 ∧ cy t z ≤ 0}
/-- `Q₄ = {x ≥ 0, y ≤ 0}`. -/
def Q₄ (t : ℍ) : Set ℂ := {z | 0 ≤ cx t z ∧ cy t z ≤ 0}

theorem mem_K₁ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₁ t) : z ∈ K t := by
  obtain ⟨hx, hy⟩ := box hz.1
  rw [abs_lt] at hx hy
  obtain ⟨h1, h2⟩ := hq
  rcases h2.lt_or_eq with h2 | h2
  · exact Or.inl ⟨h1, by linarith, h2, by linarith⟩
  · rcases h1.lt_or_eq with h1 | h1
    · exact Or.inr ⟨h1, by linarith, h2.le, by linarith⟩
    · exact absurd (eq_zero_of_cx_cy h1.symm h2.symm) hz.2

theorem mem_K₂ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₂ t) : z + 1 ∈ K t := by
  obtain ⟨hx, hy⟩ := box hz.1
  rw [abs_lt] at hx hy
  obtain ⟨h1, h2⟩ := hq
  have ex : cx t (z + 1) = cx t z + 1 := by rw [cx_add, cx_one]
  have ey : cy t (z + 1) = cy t z := by rw [cy_add, cy_one, add_zero]
  rcases h2.lt_or_eq with h2 | h2
  · exact Or.inl ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
      by rw [ey]; linarith⟩
  · rcases h1.lt_or_eq with h1 | h1
    · exact Or.inr ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
        by rw [ey]; linarith⟩
    · exact absurd (eq_zero_of_cx_cy h1 h2.symm) hz.2

theorem mem_K₃ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₃ t) : z + 1 + t ∈ K t := by
  obtain ⟨hx, hy⟩ := box hz.1
  rw [abs_lt] at hx hy
  obtain ⟨h1, h2⟩ := hq
  have ex : cx t (z + 1 + t) = cx t z + 1 := by rw [cx_add, cx_add, cx_one, cx_t]; ring
  have ey : cy t (z + 1 + t) = cy t z + 1 := by rw [cy_add, cy_add, cy_one, cy_t]; ring
  rcases h2.lt_or_eq with h2 | h2
  · exact Or.inl ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
      by rw [ey]; linarith⟩
  · rcases h1.lt_or_eq with h1 | h1
    · exact Or.inr ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
        by rw [ey]; linarith⟩
    · exact absurd (eq_zero_of_cx_cy h1 h2) hz.2

theorem mem_K₄ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₄ t) : z + t ∈ K t := by
  obtain ⟨hx, hy⟩ := box hz.1
  rw [abs_lt] at hx hy
  obtain ⟨h1, h2⟩ := hq
  have ex : cx t (z + t) = cx t z := by rw [cx_add, cx_t, add_zero]
  have ey : cy t (z + t) = cy t z + 1 := by rw [cy_add, cy_t]
  rcases h2.lt_or_eq with h2 | h2
  · exact Or.inl ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
      by rw [ey]; linarith⟩
  · rcases h1.lt_or_eq with h1 | h1
    · exact Or.inr ⟨by rw [ex]; linarith, by rw [ex]; linarith, by rw [ey]; linarith,
        by rw [ey]; linarith⟩
    · exact absurd (eq_zero_of_cx_cy h1.symm h2) hz.2

/-- The monodromy candidate `C = A⁻¹ B⁻¹ A B`. -/
noncomputable def Cm : SL(2, ℝ) := (A U)⁻¹ * (B U)⁻¹ * A U * B U

/-- The lift over `Q₁`. -/
noncomputable def σ₁ (z : ℂ) : ℍ := sK U z
/-- The lift over `Q₂`. -/
noncomputable def σ₂ (z : ℂ) : ℍ := (A U)⁻¹ • sK U (z + 1)
/-- The lift over `Q₃`. -/
noncomputable def σ₃ (z : ℂ) : ℍ := (A U)⁻¹ • (B U)⁻¹ • sK U (z + 1 + t)
/-- The lift over `Q₄`. -/
noncomputable def σ₄ (z : ℂ) : ℍ := (A U)⁻¹ • (B U)⁻¹ • A U • sK U (z + t)

theorem ψ_σ₁ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₁ t) : U.ψ (σ₁ U z) = z :=
  ψ_sK U (mem_K₁ hz hq)

theorem ψ_σ₂ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₂ t) : U.ψ (σ₂ U z) = z := by
  rw [σ₂, ψ_A_inv_smul, ψ_sK U (mem_K₂ hz hq)]; ring

theorem ψ_σ₃ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₃ t) : U.ψ (σ₃ U z) = z := by
  rw [σ₃, ψ_A_inv_smul, ψ_B_inv_smul, ψ_sK U (mem_K₃ hz hq)]; ring

theorem ψ_σ₄ {z : ℂ} (hz : z ∈ Dst t) (hq : z ∈ Q₄ t) : U.ψ (σ₄ U z) = z := by
  rw [σ₄, ψ_A_inv_smul, ψ_B_inv_smul, ψ_A_smul, ψ_sK U (mem_K₄ hz hq)]; ring

theorem ψ_Cm_smul (τ : ℍ) : U.ψ (Cm U • τ) = U.ψ τ := by
  rw [Cm, mul_smul, mul_smul, mul_smul, ψ_A_inv_smul, ψ_B_inv_smul, ψ_A_smul, ψ_B_smul]; ring

theorem Cm_mem : Cm U ∈ U.deckGroup := ⟨0, zero_mem _, fun τ ↦ by rw [ψ_Cm_smul, add_zero]⟩

/-- `sK` is continuous on the whole of `K`. -/
theorem continuousOn_sK : ContinuousOn (sK U) (K t) := by
  intro k hk
  rcases hk with hk | hk
  · refine ((continuousOn_sK₁ U) k hk).mono_of_mem_nhdsWithin ?_
    refine mem_nhdsWithin.mpr ⟨{z | 0 < cy t z ∧ cy t z < 1},
      (isOpen_lt continuous_const (continuous_cy t)).inter
        (isOpen_lt (continuous_cy t) continuous_const), ⟨hk.2.2.1, hk.2.2.2⟩, ?_⟩
    rintro z ⟨⟨h1, h2⟩, hz⟩
    rcases hz with hz | hz
    · exact hz
    · exact ⟨hz.1.le, hz.2.1.le, h1, h2⟩
  · refine ((continuousOn_sK₂ U) k hk).mono_of_mem_nhdsWithin ?_
    refine mem_nhdsWithin.mpr ⟨{z | 0 < cx t z ∧ cx t z < 1},
      (isOpen_lt continuous_const (continuous_cx t)).inter
        (isOpen_lt (continuous_cx t) continuous_const), ⟨hk.1, hk.2.1⟩, ?_⟩
    rintro z ⟨⟨h1, h2⟩, hz⟩
    rcases hz with hz | hz
    · exact ⟨h1, h2, hz.2.2.1.le, hz.2.2.2.le⟩
    · exact hz

theorem continuousOn_σ₁ : ContinuousOn (σ₁ U) (Dst t ∩ Q₁ t) :=
  (continuousOn_sK U).mono fun _ hz ↦ mem_K₁ hz.1 hz.2

theorem continuousOn_σ₂ : ContinuousOn (σ₂ U) (Dst t ∩ Q₂ t) :=
  (continuous_const_smul _).comp_continuousOn ((continuousOn_sK U).comp
    (continuous_add_const 1).continuousOn fun _ hz ↦ mem_K₂ hz.1 hz.2)

theorem continuousOn_σ₃ : ContinuousOn (σ₃ U) (Dst t ∩ Q₃ t) :=
  (continuous_const_smul _).comp_continuousOn ((continuous_const_smul _).comp_continuousOn
    ((continuousOn_sK U).comp ((continuous_add_const 1).add continuous_const).continuousOn
      fun _ hz ↦ mem_K₃ hz.1 hz.2))

theorem continuousOn_σ₄ : ContinuousOn (σ₄ U) (Dst t ∩ Q₄ t) :=
  (continuous_const_smul _).comp_continuousOn ((continuous_const_smul _).comp_continuousOn
    ((continuous_const_smul _).comp_continuousOn ((continuousOn_sK U).comp
      (continuous_add_const _).continuousOn fun _ hz ↦ mem_K₄ hz.1 hz.2)))

/-! ### The seams -/

theorem seam₁₂ {z : ℂ} (hz : z ∈ Dst t) (hx : cx t z = 0) (hy : 0 ≤ cy t z) :
    σ₂ U z = σ₁ U z := by
  obtain ⟨-, hby⟩ := box hz.1
  rw [abs_lt] at hby
  have hy' : 0 < cy t z := hy.lt_of_ne fun h ↦ hz.2 (eq_zero_of_cx_cy hx h.symm)
  have hE : z ∈ EL t := ⟨hx, hy', by linarith⟩
  rw [σ₂, σ₁, ← A_smul_sK U hE, inv_smul_smul]

theorem seam₂₃ {z : ℂ} (hz : z ∈ Dst t) (hx : cx t z ≤ 0) (hy : cy t z = 0) :
    σ₃ U z = σ₂ U z := by
  obtain ⟨hbx, -⟩ := box hz.1
  rw [abs_lt] at hbx
  have hx' : cx t z < 0 := hx.lt_of_ne fun h ↦ hz.2 (eq_zero_of_cx_cy h hy)
  have hE : z + 1 ∈ EB t := ⟨by rw [cy_add, cy_one, hy, add_zero],
    by rw [cx_add, cx_one]; linarith, by rw [cx_add, cx_one]; linarith⟩
  rw [σ₃, σ₂, ← B_smul_sK U hE, inv_smul_smul]

theorem seam₃₄ {z : ℂ} (hz : z ∈ Dst t) (hx : cx t z = 0) (hy : cy t z ≤ 0) :
    σ₄ U z = σ₃ U z := by
  obtain ⟨-, hby⟩ := box hz.1
  rw [abs_lt] at hby
  have hy' : cy t z < 0 := hy.lt_of_ne fun h ↦ hz.2 (eq_zero_of_cx_cy hx h)
  have hE : z + t ∈ EL t := ⟨by rw [cx_add, cx_t, hx, add_zero],
    by rw [cy_add, cy_t]; linarith, by rw [cy_add, cy_t]; linarith⟩
  rw [σ₄, σ₃, A_smul_sK U hE, show z + t + 1 = z + 1 + t by ring]

theorem seam₄₁ {z : ℂ} (hz : z ∈ Dst t) (hx : 0 ≤ cx t z) (hy : cy t z = 0) :
    σ₄ U z = Cm U • σ₁ U z := by
  obtain ⟨hbx, -⟩ := box hz.1
  rw [abs_lt] at hbx
  have hx' : 0 < cx t z := hx.lt_of_ne fun h ↦ hz.2 (eq_zero_of_cx_cy h.symm hy)
  have hE : z ∈ EB t := ⟨hy, hx', by linarith⟩
  rw [σ₄, σ₁, Cm, ← B_smul_sK U hE, mul_smul, mul_smul, mul_smul]

end Peripheral

end Uniformization

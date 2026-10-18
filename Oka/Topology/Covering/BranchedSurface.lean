/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.Covering.BranchedDiscData
import Oka.Topology.Covering.BranchedFillInfty
import Pi1.Surface.SchreierSurface

/-!
# A compact branched covering of the sphere with one point over `∞` has a surface group

In the situation of `Oka/Topology/Covering/BranchedFillInfty.lean` (a branched covering
`f : X → ℂ`, unramified over `ℂ ∖ {0, 1}`, and `X = Y ∖ {p}` with disc data at `p` near `∞`),
`π₁(Y)` is the closed surface group `Π_{g,0}`, with
`2g + #f⁻¹{0, 1} + d = 2d + 1` for `d` the number of sheets
(`BranchedCover.exists_mulEquiv_surfaceGroup_zero`).

## Proof

`BranchedCover.ker_eq_comap_cuspSubgroup_sup_infty` identifies `π₁(Y)` with the quotient of the
stabiliser `H ≤ F(x₀, x₁)` of a point of the fibre by the cusp subgroup and the cusp loops at
infinity. After renaming the letters `{0, 1} ≃ Fin 2` (`BranchedCover.stabEquiv`), this is the
quotient computed by pi1's
`Pi1.ReidemeisterSchreier.exists_quotient_sup_mulEquiv_surfaceGroup_zero`, since the cusp loops
at infinity normally generate the same subgroup as the elements `γ⁻¹ x_∞^m γ`
(`BranchedCover.normalClosure_conjPowSet_eq`). The orbit counts are
`#⟨xₐ⟩-orbits = #f⁻¹(a)` (`BranchedCover.card_orbits_eq`) and `#⟨x_∞⟩-orbits = 1`: the group
`⟨x₀ x₁⟩` acts transitively on the fibre, because the lifts of the base point of a big circle lie
in the punctured disc `V ∖ {p}`, which is path connected, and a loop in the exterior of a big
disc based on the big circle is a power of it
(`Complex.PuncturedPlane.ZeroOne.exists_eq_zpow_bigArrow_of_base`).
-/

open Set Metric Topology CategoryTheory Complex.PuncturedPlane Complex.PuncturedPlane.ZeroOne
  Pi1.ReidemeisterSchreier

namespace BranchedCover

universe u v

/-! ### Renaming the letters of a free group acting on a set -/

section Transfer

variable {α β Ω : Type*} [MulAction (FreeGroup α) Ω] [MulAction (FreeGroup β) Ω]

/-- The elements of the stabiliser of `ω₀` conjugate in `F(α)` to a power of an element of
`A`. -/
def conjPowSet (A : Set (FreeGroup α)) (ω₀ : Ω) : Set (MulAction.stabilizer (FreeGroup α) ω₀) :=
  {h | ∃ a ∈ A, ∃ (G : FreeGroup α) (k : ℤ), (h : FreeGroup α) = G * a ^ k * G⁻¹}

theorem cuspSubgroup_eq_normalClosure_conjPowSet (A : Set α) (ω₀ : Ω) :
    cuspSubgroup A ω₀ = Subgroup.normalClosure (conjPowSet (FreeGroup.of '' A) ω₀) := by
  rw [cuspSubgroup]
  congr 1
  ext h
  simp only [conjPowSet, mem_setOf_eq, mem_image, exists_exists_and_eq_and]

theorem conjPowSet_inv (w : FreeGroup α) (ω₀ : Ω) :
    conjPowSet {w⁻¹} ω₀ = conjPowSet {w} ω₀ := by
  ext h
  simp only [conjPowSet, mem_singleton_iff, exists_eq_left, mem_setOf_eq]
  constructor
  · rintro ⟨G, k, hk⟩
    exact ⟨G, -k, by rw [hk, inv_zpow']⟩
  · rintro ⟨G, k, hk⟩
    exact ⟨G, -k, by rw [hk, inv_zpow', neg_neg]⟩

variable (σ : α ≃ β)
  (hσ : ∀ (g : FreeGroup α) (ω : Ω), FreeGroup.freeGroupCongr σ g • ω = g • ω)
include hσ

/-- Renaming the letters identifies the stabilisers. -/
noncomputable def stabEquiv (ω₀ : Ω) :
    MulAction.stabilizer (FreeGroup α) ω₀ ≃* MulAction.stabilizer (FreeGroup β) ω₀ where
  toFun h := ⟨FreeGroup.freeGroupCongr σ h, by
    rw [MulAction.mem_stabilizer_iff, hσ]; exact h.2⟩
  invFun h := ⟨(FreeGroup.freeGroupCongr σ).symm h, by
    rw [MulAction.mem_stabilizer_iff, ← hσ, MulEquiv.apply_symm_apply]; exact h.2⟩
  left_inv h := Subtype.ext ((FreeGroup.freeGroupCongr σ).symm_apply_apply h)
  right_inv h := Subtype.ext ((FreeGroup.freeGroupCongr σ).apply_symm_apply h)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

theorem coe_stabEquiv (ω₀ : Ω) (h : MulAction.stabilizer (FreeGroup α) ω₀) :
    (stabEquiv σ hσ ω₀ h : FreeGroup β) = FreeGroup.freeGroupCongr σ h :=
  rfl

theorem image_stabEquiv_conjPowSet (A : Set (FreeGroup α)) (ω₀ : Ω) :
    stabEquiv σ hσ ω₀ '' conjPowSet A ω₀ =
      conjPowSet (FreeGroup.freeGroupCongr σ '' A) ω₀ := by
  ext h
  constructor
  · rintro ⟨h, ⟨a, ha, G, k, hk⟩, rfl⟩
    exact ⟨_, mem_image_of_mem _ ha, FreeGroup.freeGroupCongr σ G, k, by
      rw [coe_stabEquiv, hk, map_mul, map_mul, map_zpow, map_inv]⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, G, k, hk⟩
    refine ⟨(stabEquiv σ hσ ω₀).symm h, ⟨a, ha, (FreeGroup.freeGroupCongr σ).symm G, k, ?_⟩,
      MulEquiv.apply_symm_apply _ _⟩
    change (FreeGroup.freeGroupCongr σ).symm h = _
    rw [hk, map_mul, map_mul, map_zpow, map_inv, MulEquiv.symm_apply_apply]

theorem map_stabEquiv_normalClosure (A : Set (FreeGroup α)) (ω₀ : Ω) :
    (Subgroup.normalClosure (conjPowSet A ω₀)).map (stabEquiv σ hσ ω₀).toMonoidHom =
      Subgroup.normalClosure (conjPowSet (FreeGroup.freeGroupCongr σ '' A) ω₀) := by
  rw [Subgroup.map_normalClosure _ _ (stabEquiv σ hσ ω₀).surjective]
  exact congrArg _ (image_stabEquiv_conjPowSet σ hσ A ω₀)

omit hσ in
/-- Two elements acting in the same way have the same number of orbits. -/
theorem card_orbits_zpowers_eq {g : FreeGroup α} {g' : FreeGroup β}
    (h : ∀ (k : ℤ) (ω : Ω), g' ^ k • ω = g ^ k • ω) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g') Ω) =
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) Ω) := by
  refine Nat.card_congr (Quotient.congr (Equiv.refl Ω) fun a b ↦ ?_)
  change a ∈ MulAction.orbit _ b ↔ a ∈ MulAction.orbit _ b
  simp only [MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mem_zpowers_iff]
  simp only [Subgroup.smul_def]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, hk⟩
    exact ⟨_, ⟨k, rfl⟩, by rwa [← h]⟩
  · rintro ⟨_, ⟨k, rfl⟩, hk⟩
    exact ⟨_, ⟨k, rfl⟩, by rwa [h]⟩

end Transfer

/-! ### The cusp loops at infinity in pi1's form -/

section Infinity

variable {α Ω : Type*} [MulAction (FreeGroup α) Ω]

/-- The conjugates of powers of `w` in the stabiliser normally generate the same subgroup as the
elements `γ⁻¹ wᵐ γ`, `m` the length of the `⟨w⟩`-orbit of `γ ω₀`. -/
theorem normalClosure_conjPowSet_eq (w : FreeGroup α) (ω₀ : Ω) :
    Subgroup.normalClosure (conjPowSet {w} ω₀) =
      Subgroup.normalClosure {h : MulAction.stabilizer (FreeGroup α) ω₀ |
        ∃ γ : FreeGroup α, (h : FreeGroup α) =
          γ⁻¹ * w ^ Function.minimalPeriod (w • ·) (γ • ω₀) * γ} := by
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal fun h hh ↦ ?_
    obtain ⟨a, ha, G, k, hk⟩ := hh
    rw [mem_singleton_iff] at ha
    rw [ha] at hk
    set γ := G⁻¹
    set m := Function.minimalPeriod (w • ·) (γ • ω₀)
    have hfix : w ^ k • (γ • ω₀) = γ • ω₀ := by
      have h2 : (h : FreeGroup α) • ω₀ = ω₀ := h.2
      rw [hk, mul_smul, mul_smul, smul_eq_iff_eq_inv_smul] at h2
      exact h2
    obtain ⟨l, hl⟩ := (MulAction.zpow_smul_eq_iff_minimalPeriod_dvd).1 hfix
    let h₀ : MulAction.stabilizer (FreeGroup α) ω₀ := ⟨γ⁻¹ * w ^ m * γ, by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul,
        MulAction.pow_smul_eq_iff_minimalPeriod_dvd.2 dvd_rfl, inv_smul_smul]⟩
    have : h = h₀ ^ l := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, hk, hl]
      simp only [h₀, γ, inv_inv]
      rw [conj_zpow, zpow_mul, zpow_natCast]
    rw [this]
    exact zpow_mem (Subgroup.subset_normalClosure (show h₀ ∈ {h : MulAction.stabilizer
      (FreeGroup α) ω₀ | ∃ γ : FreeGroup α, (h : FreeGroup α) =
        γ⁻¹ * w ^ Function.minimalPeriod (w • ·) (γ • ω₀) * γ} from ⟨γ, rfl⟩)) l
  · refine Subgroup.normalClosure_le_normal fun h hh ↦ ?_
    obtain ⟨γ, hγ⟩ := hh
    exact Subgroup.subset_normalClosure (show h ∈ conjPowSet {w} ω₀ from
      ⟨w, rfl, γ⁻¹, _, by rw [hγ, inv_inv, zpow_natCast]⟩)

end Infinity

/-! ### The fibre over the big circle and the orbits of `⟨x₀ x₁⟩` -/

section Main

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : C(X, ℂ)} {j : C(X, Y)} {p : Y} (I : InftyData f j p)
  (cov : IsCoveringMap (punctMap f ({0, 1} : Finset ℂ))) {x : X01}
  (ψ : FundamentalGroup X01 x ≃* FreeGroup ({0, 1} : Finset ℂ))
  [MulAction (FreeGroup ({0, 1} : Finset ℂ)) (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x})]
  (hφ : ∀ (g : FreeGroup ({0, 1} : Finset ℂ)) (e : punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}),
    g • e = cov.monodromy (ψ.symm g) e)

include I hφ in
/-- **`⟨x₀ x₁⟩` acts transitively on the fibre** when there is a single point over `∞`. -/
theorem exists_zpow_loop01_smul_eq (hj : IsEmbedding j) (hrange : range j = {p}ᶜ)
    {R : ℝ} (hR : 1 / 2 < R) (hR₀ : I.R₀ < R) (hR₁ : I.R₁ < R)
    (hψinf : ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (bigBase hR),
      ψ.symm loop01 = δ ≫ bigArrow hR ≫ Groupoid.inv δ)
    (e e' : punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}) : ∃ k : ℤ, loop01 ^ k • e = e' := by
  obtain ⟨δ, hX⟩ := hψinf
  set e₁ := cov.monodromy δ e
  set e₂ := cov.monodromy δ e'
  have hpj : ∀ u, j u ≠ p := fun u h ↦ by
    have : j u ∈ range j := mem_range_self u
    rw [hrange, h] at this
    exact this rfl
  have hnorm : ∀ u : punctMap f ({0, 1} : Finset ℂ) ⁻¹' {bigBase hR},
      I.R₁ < ‖f u.1.1 - 1 / 2‖ := fun u ↦ by
    have h := lt_norm_bigLoop_sub hR hR₁ 0
    rw [(bigLoop hR).source] at h
    have hu : (bigBase hR : ℂ) = f u.1.1 := (congrArg Subtype.val u.2).symm
    rwa [hu] at h
  have hmem : ∀ u : punctMap f ({0, 1} : Finset ℂ) ⁻¹' {bigBase hR},
      punctIncl f j u.1 ∈ I.V \ {p} := fun u ↦ ⟨I.cover _ (hnorm u), hpj _⟩
  -- a path from `e₁` to `e₂` in `V ∖ {p}`
  have hJ := (VanKampen.isPathConnected_diff_of_disc I.e I.mem I.e_center).joinedIn _ (hmem e₁)
    _ (hmem e₂)
  set γY := hJ.somePath
  have hrng : ∀ t, γY t ∈ range (punctIncl f j) := fun t ↦ by
    obtain ⟨hV, hp⟩ := hJ.somePath_mem t
    have : γY t ∈ range j := by rw [hrange]; exact hp
    obtain ⟨u, hu⟩ := this
    have hfu : f u ∉ ({0, 1} : Finset ℂ) := notMem_of_lt I.half_lt (I.mapsTo u (hu ▸ hV))
    exact ⟨⟨u, hfu⟩, hu⟩
  have hemb : IsEmbedding (punctIncl f j) := hj.comp IsEmbedding.subtypeVal
  let γW : Path e₁.1 e₂.1 :=
    { toFun := fun t ↦ hemb.toHomeomorph.symm ⟨γY t, hrng t⟩
      continuous_toFun := hemb.toHomeomorph.symm.continuous.comp
        (γY.continuous.subtype_mk _)
      source' := by
        rw [show (⟨γY 0, hrng 0⟩ : range (punctIncl f j)) =
          ⟨punctIncl f j e₁.1, mem_range_self _⟩ from Subtype.ext γY.source]
        exact hemb.toHomeomorph_symm_apply _
      target' := by
        rw [show (⟨γY 1, hrng 1⟩ : range (punctIncl f j)) =
          ⟨punctIncl f j e₂.1, mem_range_self _⟩ from Subtype.ext γY.target]
        exact hemb.toHomeomorph_symm_apply _ }
  have hγW : ∀ t, punctIncl f j (γW t) = γY t := fun t ↦
    congrArg Subtype.val (hemb.toHomeomorph.apply_symm_apply ⟨γY t, hrng t⟩)
  -- its image is a loop at the base point of the big circle in the exterior
  let ℓ : Path (bigBase hR) (bigBase hR) :=
    (γW.map (punctMap f _).continuous).cast e₁.2.symm e₂.2.symm
  have hℓ : ∀ t, I.R₀ < ‖(ℓ t : ℂ) - 1 / 2‖ := fun t ↦ by
    refine I.mapsTo _ ?_
    change punctIncl f j (γW t) ∈ I.V
    rw [hγW]
    exact (hJ.somePath_mem t).1
  obtain ⟨k, hk⟩ := exists_eq_zpow_bigArrow_of_base I.half_lt hR hR₀ ℓ hℓ
  have hmono : cov.monodromy (⟦ℓ⟧ : Path.Homotopic.Quotient _ _) e₁ = e₂ := by
    refine cov.monodromy_eq_of_map_eq ⟦γW⟧ ?_
    change Path.Homotopic.Quotient.mk (γW.map _) =
      (Path.Homotopic.Quotient.mk ℓ).cast e₁.2 e₂.2
    rw [← Path.Homotopic.Quotient.mk_cast]
    rfl
  refine ⟨k, ?_⟩
  have hX' : ψ.symm loop01 = conjArrow δ (FundamentalGroup.fromArrow (bigArrow hR)) := by
    rw [hX, conjArrow_apply]
  rw [hφ, map_zpow, hX', ← map_zpow, conjArrow_apply]
  change cov.monodromy (δ ≫ (FundamentalGroup.fromArrow (bigArrow hR) ^ k) ≫
    Groupoid.inv δ) e = e'
  have hk' : (FundamentalGroup.fromArrow (bigArrow hR) ^ k : FundamentalGroup X01 _) =
      ⟦ℓ⟧ := hk.symm
  rw [hk']
  change cov.monodromy (Path.Homotopic.Quotient.trans δ
    (Path.Homotopic.Quotient.trans ⟦ℓ⟧ (Groupoid.inv δ))) e = e'
  rw [cov.monodromy_trans_apply, cov.monodromy_trans_apply]
  change cov.monodromy (Groupoid.inv δ) (cov.monodromy ⟦ℓ⟧ e₁) = e'
  rw [hmono, ← cov.monodromy_trans_apply]
  change cov.monodromy (δ ≫ Groupoid.inv δ) e' = e'
  rw [Groupoid.comp_inv]
  exact congrFun cov.monodromy_refl e'

include I hφ in
/-- With a single point over `∞`, `⟨x₀ x₁⟩` has a single orbit on the fibre. -/
theorem card_orbits_loop01 (hj : IsEmbedding j) (hrange : range j = {p}ᶜ)
    {R : ℝ} (hR : 1 / 2 < R) (hR₀ : I.R₀ < R) (hR₁ : I.R₁ < R)
    (hψinf : ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (bigBase hR),
      ψ.symm loop01 = δ ≫ bigArrow hR ≫ Groupoid.inv δ)
    (e₀ : punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers loop01)
      (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x})) = 1 := by
  refine Nat.card_eq_one_iff_exists.2 ⟨Quotient.mk _ e₀, fun q ↦ ?_⟩
  induction q using Quotient.inductionOn with | h e => ?_
  obtain ⟨k, hk⟩ := exists_zpow_loop01_smul_eq I cov ψ hφ hj hrange hR hR₀ hR₁ hψinf e₀ e
  exact Quotient.sound ⟨⟨loop01 ^ k, Subgroup.zpow_mem_zpowers _ _⟩, hk⟩


/-- `{0, 1} ≃ Fin 2`, `0 ↦ 0`, `1 ↦ 1`. -/
noncomputable def finTwoEquiv : ({0, 1} : Finset ℂ) ≃ Fin (1 + 1) where
  toFun s := if (s : ℂ) = 0 then 0 else 1
  invFun i := if i = 0 then ⟨0, by simp⟩ else ⟨1, by simp⟩
  left_inv := by
    rintro ⟨s, hs⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · simp
    · obtain rfl := Finset.mem_singleton.1 hs
      simp
  right_inv i := by fin_cases i <;> simp

theorem freeGroupCongr_loop01 :
    FreeGroup.freeGroupCongr finTwoEquiv loop01 = (xInf 1)⁻¹ := by
  simp [loop01, xInf, finTwoEquiv, FreeGroup.freeGroupCongr, List.ofFn_succ]

include hφ in
theorem sum_card_orbits_eq (D : DiscData f ({0, 1} : Finset ℂ))
    (hψ : ∀ s : ({0, 1} : Finset ℂ), IsLoopAround (ψ.symm (FreeGroup.of s)) s) :
    ∑ a : ({0, 1} : Finset ℂ), Nat.card (MulAction.orbitRel.Quotient
      (Subgroup.zpowers (FreeGroup.of a)) (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x})) =
        Nat.card {P : X // f P ∈ ({0, 1} : Finset ℂ)} := by
  rw [Finset.sum_congr rfl fun a _ ↦ card_orbits_eq D cov ψ hφ hψ a]
  haveI : ∀ a : ({0, 1} : Finset ℂ), Finite {P : X // f P = a} := fun a ↦
    (D.finite.subset fun P (hP : f P = a) ↦ by
      change f P ∈ ({0, 1} : Finset ℂ); rw [hP]; exact a.2).to_subtype
  haveI : ∀ a : ({0, 1} : Finset ℂ), Fintype {P : X // f P = a} := fun a ↦ Fintype.ofFinite _
  rw [← Nat.card_sigma]
  exact Nat.card_congr
    { toFun := fun p ↦ ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
      invFun := fun P ↦ ⟨⟨f P.1, P.2⟩, P.1, rfl⟩
      left_inv := by
        rintro ⟨⟨a, ha⟩, P, hP⟩
        dsimp only at hP
        subst hP
        rfl
      right_inv := fun _ ↦ rfl }

instance (e₀ : punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}) : (inftySubgroup e₀).Normal :=
  Subgroup.normalClosure_normal

include I hφ in
/-- **A branched covering of the sphere with one point over `∞` has a closed surface group**:
`π₁(Y) ≃* Π_{g,0}` with `2g + #f⁻¹{0, 1} + d = 2d + 1`, `d` the number of sheets. -/
theorem exists_mulEquiv_surfaceGroup_zero [T1Space Y]
    [PathConnectedSpace (Punct f ({0, 1} : Finset ℂ))] (D : DiscData f ({0, 1} : Finset ℂ))
    (hj : IsEmbedding j) (hrange : range j = {p}ᶜ)
    (hψ : ∀ s : ({0, 1} : Finset ℂ), IsLoopAround (ψ.symm (FreeGroup.of s)) s)
    {R : ℝ} (hR : 1 / 2 < R) (hR₀ : I.R₀ < R) (hR₁ : I.R₁ < R)
    (hψinf : ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (bigBase hR),
      ψ.symm loop01 = δ ≫ bigArrow hR ≫ Groupoid.inv δ)
    [Finite (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x})]
    (e₀ : punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}) :
    ∃ g : ℕ, Nonempty (FundamentalGroup Y (punctIncl f j e₀.1) ≃* Pi1.SurfaceGroup g 0) ∧
      2 * g + Nat.card {P : X // f P ∈ ({0, 1} : Finset ℂ)} +
          Nat.card (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}) =
        2 * Nat.card (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}) + 1 := by
  classical
  haveI : T1Space X := hj.t1Space
  set σ := finTwoEquiv
  letI : MulAction (FreeGroup (Fin (1 + 1))) (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}) :=
    MulAction.compHom _ (FreeGroup.freeGroupCongr σ.symm).toMonoidHom
  have hact : ∀ (g : FreeGroup (Fin (1 + 1))) (ω : (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x})),
      g • ω = FreeGroup.freeGroupCongr σ.symm g • ω := fun _ _ ↦ rfl
  have hσ : ∀ (g : FreeGroup ({0, 1} : Finset ℂ)) (ω : (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x})),
      FreeGroup.freeGroupCongr σ g • ω = g • ω := by
    intro g ω
    rw [hact, ← FreeGroup.freeGroupCongr_symm, MulEquiv.symm_apply_apply]
  have htrans : ∀ ω : (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}),
      ∃ g : FreeGroup (Fin (1 + 1)), g • e₀ = ω := fun ω ↦ by
    obtain ⟨g, hg⟩ := cov.exists_free_smul_eq ψ hφ e₀ ω
    exact ⟨FreeGroup.freeGroupCongr σ g, by rw [hσ, hg]⟩
  obtain ⟨g, ⟨Θ⟩, hcount⟩ := exists_quotient_sup_mulEquiv_surfaceGroup_zero (n := 1) htrans
  -- the kernel of `π₁(X ∖ f⁻¹{0,1}) → π₁(Y)`
  have hsurj := (fill_infty D hj hrange I e₀.1).1
  have hker := ker_eq_comap_cuspSubgroup_sup_infty I cov ψ hφ D hj hrange hψ hR hR₀ hR₁ hψinf e₀
  set Φ := cov.fundamentalGroupEquivFreeStabilizer ψ hφ e₀
  set M := cuspSubgroup (Set.univ : Set ({0, 1} : Finset ℂ)) e₀ ⊔ inftySubgroup e₀
  have hM : (FundamentalGroup.map (punctIncl f j) e₀.1).ker.map Φ.toMonoidHom = M := by
    rw [hker]
    exact Subgroup.map_comap_eq_self_of_surjective Φ.surjective _
  -- renaming the letters
  have hmap : M.map (stabEquiv σ hσ e₀ : _ →* _) =
      cuspSubgroup (Set.univ : Set (Fin (1 + 1))) e₀ ⊔ Subgroup.normalClosure
        {h : MulAction.stabilizer (FreeGroup (Fin (1 + 1))) e₀ | ∃ γ : FreeGroup (Fin (1 + 1)),
          (h : FreeGroup (Fin (1 + 1))) = γ⁻¹ * xInf 1 ^ SchreierRibbon.perInf 1 (γ • e₀) * γ} := by
    have hinf : inftySubgroup e₀ = Subgroup.normalClosure (conjPowSet {loop01} e₀) := by
      rw [inftySubgroup]
      congr 1
      ext h
      simp [conjPowSet]
    rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.map_sup,
      cuspSubgroup_eq_normalClosure_conjPowSet, cuspSubgroup_eq_normalClosure_conjPowSet,
      map_stabEquiv_normalClosure, hinf,
      map_stabEquiv_normalClosure, image_singleton, freeGroupCongr_loop01, conjPowSet_inv,
      normalClosure_conjPowSet_eq]
    congr 3
    ext w
    simp only [mem_image, mem_univ, true_and, exists_exists_eq_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨σ a, by simp [FreeGroup.freeGroupCongr]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨σ.symm b, by simp [FreeGroup.freeGroupCongr]⟩
  have hM' : (FundamentalGroup.map (punctIncl f j) e₀.1).ker.map (Φ : _ →* _) = M := hM
  refine ⟨g, ⟨(((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).symm.trans
    (QuotientGroup.congr _ M Φ hM')).trans (QuotientGroup.congr M _ _ hmap)).trans Θ⟩, ?_⟩
  -- the counts
  have hx : FreeGroup.freeGroupCongr σ.symm (xInf 1) = loop01⁻¹ := by
    rw [← FreeGroup.freeGroupCongr_symm, MulEquiv.symm_apply_eq, map_inv, freeGroupCongr_loop01,
      inv_inv]
  have hinfc : Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (xInf 1))
      (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x})) = 1 := by
    rw [card_orbits_zpowers_eq (g := loop01⁻¹) fun k ω ↦ by rw [hact, map_zpow, hx],
      Subgroup.zpowers_inv]
    exact card_orbits_loop01 I cov ψ hφ hj hrange hR hR₀ hR₁ hψinf e₀
  have hfin : ∑ a : Fin (1 + 1), Nat.card (MulAction.orbitRel.Quotient
      (Subgroup.zpowers (FreeGroup.of a)) (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x})) =
        Nat.card {P : X // f P ∈ ({0, 1} : Finset ℂ)} := by
    rw [← sum_card_orbits_eq cov ψ hφ D hψ, ← Equiv.sum_comp σ.symm]
    refine Finset.sum_congr rfl fun a _ ↦ card_orbits_zpowers_eq fun k ω ↦ ?_
    rw [hact, map_zpow]
    simp [FreeGroup.freeGroupCongr]
  rw [hinfc, hfin] at hcount
  omega

end Main

/-! ### The statement for a closed local homeomorphism with charts -/

section Charts

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : C(X, ℂ)} {j : C(X, Y)} {p : Y}

/-- **Disc data at infinity from compactness**: if `Y` is compact Hausdorff, `j` an open embedding
onto `Y ∖ {p}`, `f` proper (closed with finite fibres) and `p` in the source of a chart, then
`f` has disc data at `p`. -/
theorem nonempty_inftyData [T2Space Y] [CompactSpace Y] (hcl : IsClosedMap f)
    (hfib : ∀ z, (f ⁻¹' {z}).Finite) (hj : IsOpenEmbedding j) (hrange : range j = {p}ᶜ)
    (φ : OpenPartialHomeomorph Y ℂ) (hp : p ∈ φ.source) : Nonempty (InftyData f j p) := by
  have hproper : IsProperMap f :=
    isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨f.continuous, hcl, fun z ↦ (hfib z).isCompact⟩
  -- the preimage of a closed disc around `1/2` is compact; its image avoids a neighbourhood of `p`
  set K := f ⁻¹' closedBall (1 / 2 : ℂ) 1
  have hK : IsCompact K := hproper.isCompact_preimage (isCompact_closedBall _ _)
  have hjK : IsClosed (j '' K) := (hK.image j.continuous).isClosed
  have hpK : p ∉ j '' K := by
    rintro ⟨u, -, hu⟩
    have : j u ∈ range j := mem_range_self u
    rw [hrange, hu] at this
    exact this rfl
  obtain ⟨V, hpV, hVW, hVo, e, he⟩ := exists_disc_subset φ hp (hjK.isOpen_compl.mem_nhds hpK)
  -- the complement of the disc is compact, so `f` is bounded on its preimage
  have hC : IsCompact (j ⁻¹' Vᶜ) := by
    refine (hj.isInducing.isCompact_preimage_iff fun y hy ↦ ?_).2 hVo.isClosed_compl.isCompact
    rw [hrange]
    exact fun hyp ↦ hy (hyp ▸ hpV)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hC.image f.continuous).isBounded
  refine ⟨⟨V, e, hVo, hpV, he, 1, by norm_num, fun u hu ↦ ?_, B + 1 / 2, fun u hu ↦ ?_⟩⟩
  · have hu' : u ∉ K := fun h ↦ hVW hu ⟨u, h, rfl⟩
    simpa [K, dist_eq_norm] using hu'
  · by_contra h
    have := hB (f u) ⟨u, h, rfl⟩
    have h2 : ‖f u - 1 / 2‖ ≤ ‖f u‖ + 1 / 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_div, norm_one, Complex.norm_two]
    linarith

/-- **A compact branched covering of `ℙ¹`, unramified over `ℙ¹ ∖ {0, 1, ∞}`, with one point over
`∞`, has a closed surface group as fundamental group.** Let `f : X → ℂ` be closed, with finite
fibres, a local homeomorphism outside `f⁻¹{0, 1}`, with charts at the points over `{0, 1}`, `X`
connected and locally path connected, and `j : X → Y` an embedding onto `Y ∖ {p}` with disc data
at `p` near `∞` (`BranchedCover.InftyData`). Then for every `e₀ ∈ X ∖ f⁻¹{0, 1}`,
`π₁(Y, j e₀) ≃* Π_{g,0}` with `2g + #f⁻¹{0, 1} + d = 2d + 1`, `d = #f⁻¹(f e₀)`. -/
theorem exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_charts [T2Space X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [T1Space Y] (hcl : IsClosedMap f)
    (hfib : ∀ z, (f ⁻¹' {z}).Finite)
    (hloc : IsLocalHomeomorphOn f {y | f y ∉ ({0, 1} : Finset ℂ)})
    (hchart : ∀ P, f P ∈ ({0, 1} : Finset ℂ) → ∃ φ : OpenPartialHomeomorph X ℂ, P ∈ φ.source)
    (hj : IsEmbedding j) (hrange : range j = {p}ᶜ) (I : InftyData f j p)
    (e₀ : X) (he₀ : f e₀ ∉ ({0, 1} : Finset ℂ)) :
    ∃ g : ℕ, Nonempty (FundamentalGroup Y (j e₀) ≃* Pi1.SurfaceGroup g 0) ∧
      2 * g + Nat.card {P : X // f P ∈ ({0, 1} : Finset ℂ)} + Nat.card (f ⁻¹' {f e₀}) =
        2 * Nat.card (f ⁻¹' {f e₀}) + 1 := by
  have hfin : {P | f P ∈ ({0, 1} : Finset ℂ)}.Finite := by
    have : {P | f P ∈ ({0, 1} : Finset ℂ)} = ⋃ s ∈ ({0, 1} : Finset ℂ), f ⁻¹' {s} := by
      ext; simp
    rw [this]
    exact Finset.finite_toSet _ |>.biUnion fun s _ ↦ hfib s
  obtain ⟨D⟩ := nonempty_discData hcl hfin hchart
  have cov := isCoveringMap_punctMap hcl hfib hloc
  haveI := pathConnectedSpace_punct D
  let x : X01 := punctMap f _ ⟨e₀, he₀⟩
  set R := max I.R₀ I.R₁ + 1
  have hR₀ : I.R₀ < R := by have := le_max_left I.R₀ I.R₁; linarith
  have hR₁ : I.R₁ < R := by have := le_max_right I.R₀ I.R₁; linarith
  have hR : 1 / 2 < R := I.half_lt.trans hR₀
  obtain ⟨ψ, hψ, δ, hδ⟩ := Complex.exists_mulEquiv_freeGroup_zero_one hR x
  letI := cov.fundamentalGroupMulAction x
  letI : MulAction (FreeGroup ({0, 1} : Finset ℂ)) (punctMap f _ ⁻¹' {x}) :=
    MulAction.compHom _ ψ.symm.toMonoidHom
  have hφ : ∀ (γ : FreeGroup ({0, 1} : Finset ℂ)) (e : punctMap f _ ⁻¹' {x}),
      γ • e = cov.monodromy (ψ.symm γ) e := fun _ _ ↦ rfl
  -- the fibre of `punctMap` is the fibre of `f`
  let F : punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x} ≃ f ⁻¹' {f e₀} :=
    { toFun := fun e ↦ ⟨e.1.1, congrArg Subtype.val e.2⟩
      invFun := fun y ↦ ⟨⟨y.1, by rw [show f y.1 = f e₀ from y.2]; exact he₀⟩,
        Subtype.ext (show f y.1 = f e₀ from y.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  haveI : Finite (f ⁻¹' {f e₀}) := (hfib _).to_subtype
  haveI : Finite (punctMap f ({0, 1} : Finset ℂ) ⁻¹' {x}) := Finite.of_equiv _ F.symm
  obtain ⟨g, hiso, hcard⟩ := exists_mulEquiv_surfaceGroup_zero I cov ψ hφ D hj hrange hψ hR hR₀
    hR₁ ⟨δ, hδ⟩ ⟨⟨e₀, he₀⟩, rfl⟩
  rw [Nat.card_congr F] at hcard
  exact ⟨g, hiso, hcard⟩

end Charts

end BranchedCover

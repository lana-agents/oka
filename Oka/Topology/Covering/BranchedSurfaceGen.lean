/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.Topology.Covering.BranchedSurface
import Oka.Topology.Covering.BranchedFillInftyGen

/-!
# A compact branched covering of the sphere with one point over `∞`, general branch locus

The analogue of `Oka/Topology/Covering/BranchedSurface.lean` for a branched covering
`f : X → ℂ`, unramified over `ℂ ∖ S` for a finite set `S` of `n + 1` points within distance `ρ` of
`c`, with letters ordered by an equivalence `σ : S ≃ Fin (n + 1)` and a free basis of loops
around the points of `S` whose ordered product `w` is conjugate to a big circle around `c`:
`π₁(Y) ≃* Π_{g,0}` with `2g + #f⁻¹(S) + d = d (n + 1) + 1`
(`BranchedCover.Gen.exists_mulEquiv_surfaceGroup_zero`). For the points `S = {0, 1, …, n}` the
basis is `Complex.PuncturedPlane.LineBasis.exists_basis_univ`
(`BranchedCover.Gen.exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_charts`).
-/

open Set Metric Topology CategoryTheory Complex.PuncturedPlane Complex.PuncturedPlane.LineBasis
  Pi1.ReidemeisterSchreier BranchedCover

namespace BranchedCover.Gen

universe u v

section Main

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {S : Finset ℂ} {c : ℂ}
  {ρ : ℝ} (hS : ∀ s ∈ S, ‖s - c‖ ≤ ρ) (hρ : 0 ≤ ρ) (w : FreeGroup S)
  {f : C(X, ℂ)} {j : C(X, Y)} {p : Y} (I : InftyData f j p c ρ)
  (cov : IsCoveringMap (punctMap f S)) {x : (Region Set.univ S)}
  (ψ : FundamentalGroup (Region Set.univ S) x ≃* FreeGroup S)
  [MulAction (FreeGroup S) (punctMap f S ⁻¹' {x})]
  (hφ : ∀ (g : FreeGroup S) (e : punctMap f S ⁻¹' {x}),
    g • e = cov.monodromy (ψ.symm g) e)

include I hφ hS hρ in
/-- **`⟨w⟩` acts transitively on the fibre** when there is a single point over `∞`. -/
theorem exists_zpow_smul_eq (hj : IsEmbedding j) (hrange : range j = {p}ᶜ)
    {R : ℝ} (hρR : ρ < R) (h' : CircleIn Set.univ S c R) (φ : ℝ) (hR₀ : I.R₀ < R) (hR₁ : I.R₁ < R)
    (hψinf : ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (theta h' φ),
      ψ.symm w = δ ≫ ⟦circ h' φ⟧ ≫ Groupoid.inv δ)
    (e e' : punctMap f S ⁻¹' {x}) : ∃ k : ℤ, w ^ k • e = e' := by
  obtain ⟨δ, hX⟩ := hψinf
  set e₁ := cov.monodromy δ e
  set e₂ := cov.monodromy δ e'
  have hpj : ∀ u, j u ≠ p := fun u h ↦ by
    have : j u ∈ range j := mem_range_self u
    rw [hrange, h] at this
    exact this rfl
  have hnorm : ∀ u : punctMap f S ⁻¹' {theta h' φ},
      I.R₁ < ‖f u.1.1 - c‖ := fun u ↦ by
    have hu : thetaFun c R φ = f u.1.1 := (congrArg Subtype.val u.2).symm
    rw [← hu, norm_thetaFun_sub c (hρ.trans hρR.le)]
    exact hR₁
  have hmem : ∀ u : punctMap f S ⁻¹' {theta h' φ},
      punctIncl f S j u.1 ∈ I.V \ {p} := fun u ↦ ⟨I.cover _ (hnorm u), hpj _⟩
  -- a path from `e₁` to `e₂` in `V ∖ {p}`
  have hJ := (VanKampen.isPathConnected_diff_of_disc I.e I.mem I.e_center).joinedIn _ (hmem e₁)
    _ (hmem e₂)
  set γY := hJ.somePath
  have hrng : ∀ t, γY t ∈ range (punctIncl f S j) := fun t ↦ by
    obtain ⟨hV, hp⟩ := hJ.somePath_mem t
    have : γY t ∈ range j := by rw [hrange]; exact hp
    obtain ⟨u, hu⟩ := this
    have hfu : f u ∉ S := Exterior.notMem_of_lt hS I.lt_R₀ (I.mapsTo u (hu ▸ hV))
    exact ⟨⟨u, hfu⟩, hu⟩
  have hemb : IsEmbedding (punctIncl f S j) := hj.comp IsEmbedding.subtypeVal
  let γW : Path e₁.1 e₂.1 :=
    { toFun := fun t ↦ hemb.toHomeomorph.symm ⟨γY t, hrng t⟩
      continuous_toFun := hemb.toHomeomorph.symm.continuous.comp
        (γY.continuous.subtype_mk _)
      source' := by
        rw [show (⟨γY 0, hrng 0⟩ : range (punctIncl f S j)) =
          ⟨punctIncl f S j e₁.1, mem_range_self _⟩ from Subtype.ext γY.source]
        exact hemb.toHomeomorph_symm_apply _
      target' := by
        rw [show (⟨γY 1, hrng 1⟩ : range (punctIncl f S j)) =
          ⟨punctIncl f S j e₂.1, mem_range_self _⟩ from Subtype.ext γY.target]
        exact hemb.toHomeomorph_symm_apply _ }
  have hγW : ∀ t, punctIncl f S j (γW t) = γY t := fun t ↦
    congrArg Subtype.val (hemb.toHomeomorph.apply_symm_apply ⟨γY t, hrng t⟩)
  -- its image is a loop at the base point of the big circle in the exterior
  let ℓ : Path (theta h' φ) (theta h' φ) :=
    (γW.map (punctMap f _).continuous).cast e₁.2.symm e₂.2.symm
  have hℓ : ∀ t, I.R₀ < ‖(ℓ t : ℂ) - c‖ := fun t ↦ by
    refine I.mapsTo _ ?_
    change punctIncl f S j (γW t) ∈ I.V
    rw [hγW]
    exact (hJ.somePath_mem t).1
  obtain ⟨k, hk⟩ := Exterior.exists_eq_zpow_circ_of_base hS hρ I.lt_R₀ hR₀ h' φ ℓ hℓ
  have hmono : cov.monodromy (⟦ℓ⟧ : Path.Homotopic.Quotient _ _) e₁ = e₂ := by
    refine cov.monodromy_eq_of_map_eq ⟦γW⟧ ?_
    change Path.Homotopic.Quotient.mk (γW.map _) =
      (Path.Homotopic.Quotient.mk ℓ).cast e₁.2 e₂.2
    rw [← Path.Homotopic.Quotient.mk_cast]
    rfl
  refine ⟨k, ?_⟩
  have hX' : ψ.symm w = conjArrow δ (FundamentalGroup.fromPath (.mk (circ h' φ))) := by
    rw [hX, conjArrow_apply]
    rfl
  rw [hφ, map_zpow, hX', ← map_zpow, conjArrow_apply]
  change cov.monodromy (δ ≫ (FundamentalGroup.fromPath (.mk (circ h' φ)) ^ k) ≫
    Groupoid.inv δ) e = e'
  have hk' : (FundamentalGroup.fromPath (.mk (circ h' φ)) ^ k :
      FundamentalGroup (Region Set.univ S) _) =
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

include I hφ hS hρ in
/-- With a single point over `∞`, `⟨w⟩` has a single orbit on the fibre. -/
theorem card_orbits_infty (hj : IsEmbedding j) (hrange : range j = {p}ᶜ)
    {R : ℝ} (hρR : ρ < R) (h' : CircleIn Set.univ S c R) (φ : ℝ) (hR₀ : I.R₀ < R) (hR₁ : I.R₁ < R)
    (hψinf : ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (theta h' φ),
      ψ.symm w = δ ≫ ⟦circ h' φ⟧ ≫ Groupoid.inv δ)
    (e₀ : punctMap f S ⁻¹' {x}) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers w)
      (punctMap f S ⁻¹' {x})) = 1 := by
  refine Nat.card_eq_one_iff_exists.2 ⟨Quotient.mk _ e₀, fun q ↦ ?_⟩
  induction q using Quotient.inductionOn with | h e => ?_
  obtain ⟨k, hk⟩ := exists_zpow_smul_eq hS hρ w I cov ψ hφ hj hrange hρR h' φ hR₀ hR₁ hψinf e₀ e
  exact Quotient.sound ⟨⟨w ^ k, Subgroup.zpow_mem_zpowers _ _⟩, hk⟩



include hφ in
theorem sum_card_orbits_eq (D : DiscData f S)
    (hψ : ∀ s : S, IsLoopAround (ψ.symm (FreeGroup.of s)) s) :
    ∑ a : S, Nat.card (MulAction.orbitRel.Quotient
      (Subgroup.zpowers (FreeGroup.of a)) (punctMap f S ⁻¹' {x})) =
        Nat.card {P : X // f P ∈ S} := by
  rw [Finset.sum_congr rfl fun a _ ↦ card_orbits_eq D cov ψ hφ hψ a]
  haveI : ∀ a : S, Finite {P : X // f P = a} := fun a ↦
    (D.finite.subset fun P (hP : f P = a) ↦ by
      change f P ∈ S; rw [hP]; exact a.2).to_subtype
  haveI : ∀ a : S, Fintype {P : X // f P = a} := fun a ↦ Fintype.ofFinite _
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

instance (e₀ : punctMap f S ⁻¹' {x}) : (inftySubgroup w e₀).Normal :=
  Subgroup.normalClosure_normal

theorem freeGroupCongr_prod {n : ℕ} (σ : S ≃ Fin (n + 1)) :
    FreeGroup.freeGroupCongr σ (List.ofFn fun i ↦ FreeGroup.of (σ.symm i)).prod =
      (xInf n)⁻¹ := by
  rw [map_list_prod, List.map_ofFn, xInf, inv_inv]
  congr 1
  refine List.ofFn_inj.2 (funext fun i ↦ ?_)
  simp [FreeGroup.freeGroupCongr]

include I hφ hS hρ in
/-- **A branched covering of the sphere with one point over `∞` has a closed surface group**,
general branch locus `S` with `n + 1` points. -/
theorem exists_mulEquiv_surfaceGroup_zero [T1Space Y]
    [PathConnectedSpace (Punct f S)] (D : DiscData f S)
    (hj : IsEmbedding j) (hrange : range j = {p}ᶜ)
    (hψ : ∀ s : S, IsLoopAround (ψ.symm (FreeGroup.of s)) s)
    {n : ℕ} (σ : S ≃ Fin (n + 1)) (hw : w = (List.ofFn fun i ↦ FreeGroup.of (σ.symm i)).prod)
    {R : ℝ} (hρR : ρ < R) (h' : CircleIn Set.univ S c R) (φ : ℝ) (hR₀ : I.R₀ < R)
    (hR₁ : I.R₁ < R)
    (hψinf : ∃ δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (theta h' φ),
      ψ.symm w = δ ≫ ⟦circ h' φ⟧ ≫ Groupoid.inv δ)
    [Finite (punctMap f S ⁻¹' {x})] (e₀ : punctMap f S ⁻¹' {x}) :
    ∃ g : ℕ, Nonempty (FundamentalGroup Y (punctIncl f S j e₀.1) ≃* Pi1.SurfaceGroup g 0) ∧
      2 * g + Nat.card {P : X // f P ∈ S} + Nat.card (punctMap f S ⁻¹' {x}) =
        Nat.card (punctMap f S ⁻¹' {x}) * (n + 1) + 1 := by
  classical
  haveI : T1Space X := hj.t1Space
  letI : MulAction (FreeGroup (Fin (n + 1))) (punctMap f S ⁻¹' {x}) :=
    MulAction.compHom _ (FreeGroup.freeGroupCongr σ.symm).toMonoidHom
  have hact : ∀ (g : FreeGroup (Fin (n + 1))) (ω : punctMap f S ⁻¹' {x}),
      g • ω = FreeGroup.freeGroupCongr σ.symm g • ω := fun _ _ ↦ rfl
  have hσ : ∀ (g : FreeGroup S) (ω : punctMap f S ⁻¹' {x}),
      FreeGroup.freeGroupCongr σ g • ω = g • ω := by
    intro g ω
    rw [hact, ← FreeGroup.freeGroupCongr_symm, MulEquiv.symm_apply_apply]
  have htrans : ∀ ω : punctMap f S ⁻¹' {x},
      ∃ g : FreeGroup (Fin (n + 1)), g • e₀ = ω := fun ω ↦ by
    obtain ⟨g, hg⟩ := cov.exists_free_smul_eq ψ hφ e₀ ω
    exact ⟨FreeGroup.freeGroupCongr σ g, by rw [hσ, hg]⟩
  obtain ⟨g, ⟨Θ⟩, hcount⟩ := exists_quotient_sup_mulEquiv_surfaceGroup_zero (n := n) htrans
  have hsurj := (fill_infty hS D hj hrange I e₀.1).1
  have hker := ker_eq_comap_cuspSubgroup_sup_infty hS hρ w I cov ψ hφ D hj hrange hψ hρR h' φ
    hR₀ hR₁ hψinf e₀
  set Φ := cov.fundamentalGroupEquivFreeStabilizer ψ hφ e₀
  set M := cuspSubgroup (Set.univ : Set S) e₀ ⊔ inftySubgroup w e₀
  have hM : (FundamentalGroup.map (punctIncl f S j) e₀.1).ker.map (Φ : _ →* _) = M := by
    rw [hker]
    exact Subgroup.map_comap_eq_self_of_surjective Φ.surjective _
  have hwσ : FreeGroup.freeGroupCongr σ w = (xInf n)⁻¹ := by rw [hw]; exact freeGroupCongr_prod σ
  have hmap : M.map (stabEquiv σ hσ e₀ : _ →* _) =
      cuspSubgroup (Set.univ : Set (Fin (n + 1))) e₀ ⊔ Subgroup.normalClosure
        {h : MulAction.stabilizer (FreeGroup (Fin (n + 1))) e₀ | ∃ γ : FreeGroup (Fin (n + 1)),
          (h : FreeGroup (Fin (n + 1))) = γ⁻¹ * xInf n ^ SchreierRibbon.perInf n (γ • e₀) * γ} := by
    have hinf : inftySubgroup w e₀ = Subgroup.normalClosure (conjPowSet {w} e₀) := by
      rw [inftySubgroup]
      congr 1
      ext h
      simp [conjPowSet]
    rw [← MulEquiv.toMonoidHom_eq_coe, Subgroup.map_sup,
      cuspSubgroup_eq_normalClosure_conjPowSet, cuspSubgroup_eq_normalClosure_conjPowSet,
      map_stabEquiv_normalClosure, hinf,
      map_stabEquiv_normalClosure, image_singleton, hwσ, conjPowSet_inv,
      normalClosure_conjPowSet_eq]
    congr 3
    ext v
    simp only [mem_image, mem_univ, true_and, exists_exists_eq_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨σ a, by simp [FreeGroup.freeGroupCongr]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨σ.symm b, by simp [FreeGroup.freeGroupCongr]⟩
  have hM' : (FundamentalGroup.map (punctIncl f S j) e₀.1).ker.map (Φ : _ →* _) = M := hM
  refine ⟨g, ⟨(((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).symm.trans
    (QuotientGroup.congr _ M Φ hM')).trans (QuotientGroup.congr M _ _ hmap)).trans Θ⟩, ?_⟩
  have hx : FreeGroup.freeGroupCongr σ.symm (xInf n) = w⁻¹ := by
    rw [← FreeGroup.freeGroupCongr_symm, MulEquiv.symm_apply_eq, map_inv, hwσ, inv_inv]
  have hinfc : Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (xInf n))
      (punctMap f S ⁻¹' {x})) = 1 := by
    rw [card_orbits_zpowers_eq (g := w⁻¹) fun k ω ↦ by rw [hact, map_zpow, hx],
      Subgroup.zpowers_inv]
    exact card_orbits_infty hS hρ w I cov ψ hφ hj hrange hρR h' φ hR₀ hR₁ hψinf e₀
  have hfin : ∑ a : Fin (n + 1), Nat.card (MulAction.orbitRel.Quotient
      (Subgroup.zpowers (FreeGroup.of a)) (punctMap f S ⁻¹' {x})) =
        Nat.card {P : X // f P ∈ S} := by
    rw [← sum_card_orbits_eq cov ψ hφ D hψ, ← Equiv.sum_comp σ.symm]
    refine Finset.sum_congr rfl fun a _ ↦ card_orbits_zpowers_eq fun k ω ↦ ?_
    rw [hact, map_zpow]
    simp [FreeGroup.freeGroupCongr]
  rw [hinfc, hfin] at hcount
  omega

end Main

/-! ### The statement for a closed local homeomorphism with charts, points `0, …, n` -/

section Charts

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f : C(X, ℂ)} {j : C(X, Y)} {p : Y}

/-- **Disc data at infinity from compactness**, centre `c`, radius `ρ`. -/
theorem nonempty_inftyData [T2Space Y] [CompactSpace Y] (c : ℂ) {ρ : ℝ} (hcl : IsClosedMap f)
    (hfib : ∀ z, (f ⁻¹' {z}).Finite) (hj : IsOpenEmbedding j) (hrange : range j = {p}ᶜ)
    (φ : OpenPartialHomeomorph Y ℂ) (hp : p ∈ φ.source) : Nonempty (InftyData f j p c ρ) := by
  have hproper : IsProperMap f :=
    isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨f.continuous, hcl, fun z ↦ (hfib z).isCompact⟩
  set K := f ⁻¹' closedBall c (ρ + 1)
  have hK : IsCompact K := hproper.isCompact_preimage (isCompact_closedBall _ _)
  have hjK : IsClosed (j '' K) := (hK.image j.continuous).isClosed
  have hpK : p ∉ j '' K := by
    rintro ⟨u, -, hu⟩
    have : j u ∈ range j := mem_range_self u
    rw [hrange, hu] at this
    exact this rfl
  obtain ⟨V, hpV, hVW, hVo, e, he⟩ := exists_disc_subset φ hp (hjK.isOpen_compl.mem_nhds hpK)
  have hC : IsCompact (j ⁻¹' Vᶜ) := by
    refine (hj.isInducing.isCompact_preimage_iff fun y hy ↦ ?_).2 hVo.isClosed_compl.isCompact
    rw [hrange]
    exact fun hyp ↦ hy (hyp ▸ hpV)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hC.image f.continuous).isBounded
  refine ⟨⟨V, e, hVo, hpV, he, ρ + 1, by linarith, fun u hu ↦ ?_, B + ‖c‖, fun u hu ↦ ?_⟩⟩
  · have hu' : u ∉ K := fun h ↦ hVW hu ⟨u, h, rfl⟩
    simpa [K, dist_eq_norm] using hu'
  · by_contra h
    have := hB (f u) ⟨u, h, rfl⟩
    have h2 : ‖f u - c‖ ≤ ‖f u‖ + ‖c‖ := norm_sub_le _ _
    linarith

/-- The points `0, …, n` indexed by `Fin (n + 1)`. -/
noncomputable def ptsEquiv (n : ℕ) : pts n ≃ Fin (n + 1) :=
  (Equiv.ofBijective (fun i : Fin (n + 1) ↦ (⟨((i : ℕ) : ℂ), natCast_mem_pts i.is_le⟩ : pts n))
    ⟨fun i i' h ↦ Fin.ext (Nat.cast_injective (R := ℂ) (by simpa using congrArg Subtype.val h)),
      fun s ↦ by
      obtain ⟨i, hi, he⟩ := mem_pts.1 s.2
      exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, Subtype.ext he⟩⟩).symm

lemma ptsEquiv_symm_apply (n : ℕ) (i : Fin (n + 1)) :
    ((ptsEquiv n).symm i : ℂ) = ((i : ℕ) : ℂ) := rfl

lemma coe_ptsEquiv (n : ℕ) (s : pts n) : (((ptsEquiv n s : ℕ)) : ℂ) = s := by
  conv_rhs => rw [← (ptsEquiv n).symm_apply_apply s]
  rfl

/-- **A compact branched covering of `ℙ¹`, unramified over `ℙ¹ ∖ {0, 1, …, n, ∞}`, with one
point over `∞`, has a closed surface group as fundamental group**, with
`2g + #f⁻¹{0, …, n} + d = d (n + 1) + 1`, `d = #f⁻¹(f e₀)`. -/
theorem exists_fundamentalGroup_mulEquiv_surfaceGroup_zero_of_charts (n : ℕ) [T2Space X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [T1Space Y] (hcl : IsClosedMap f)
    (hfib : ∀ z, (f ⁻¹' {z}).Finite)
    (hloc : IsLocalHomeomorphOn f {y | f y ∉ pts n})
    (hchart : ∀ P, f P ∈ pts n → ∃ φ : OpenPartialHomeomorph X ℂ, P ∈ φ.source)
    (hj : IsEmbedding j) (hrange : range j = {p}ᶜ) (I : InftyData f j p (cen n) ((n : ℝ) / 2))
    (e₀ : X) (he₀ : f e₀ ∉ pts n) :
    ∃ g : ℕ, Nonempty (FundamentalGroup Y (j e₀) ≃* Pi1.SurfaceGroup g 0) ∧
      2 * g + Nat.card {P : X // f P ∈ pts n} + Nat.card (f ⁻¹' {f e₀}) =
        Nat.card (f ⁻¹' {f e₀}) * (n + 1) + 1 := by
  have hfin : {P | f P ∈ pts n}.Finite := by
    have : {P | f P ∈ pts n} = ⋃ s ∈ pts n, f ⁻¹' {s} := by ext; simp
    rw [this]
    exact Finset.finite_toSet _ |>.biUnion fun s _ ↦ hfib s
  obtain ⟨D⟩ := nonempty_discData hcl hfin hchart
  have cov := isCoveringMap_punctMap hcl hfib hloc
  haveI := pathConnectedSpace_punct D
  let x : Region Set.univ (pts n) := punctMap f _ ⟨e₀, he₀⟩
  set R := max I.R₀ I.R₁ + rad n + 1
  have hrad := rad_pos n
  have hR₀ : I.R₀ < R := by have := le_max_left I.R₀ I.R₁; linarith
  have hR₁ : I.R₁ < R := by have := le_max_right I.R₀ I.R₁; linarith
  have hRr : rad n ≤ R := by
    have : (n : ℝ) / 2 < I.R₀ := I.lt_R₀
    have := le_max_left I.R₀ I.R₁
    linarith [half_lt_rad n, (n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hρR : (n : ℝ) / 2 < R := lt_of_lt_of_le (half_lt_rad n) hRr
  obtain ⟨g, hl, hb, δ, hp⟩ := exists_basis_univ n hRr x 0
  set e := ptsEquiv n
  let ψ : FundamentalGroup (Region Set.univ (pts n)) x ≃* FreeGroup (pts n) :=
    (MulEquiv.ofBijective (FreeGroup.lift g) hb).symm.trans (FreeGroup.freeGroupCongr e.symm)
  have hψs : ∀ i, ψ.symm (FreeGroup.of (e.symm i)) = g i := fun i ↦ by
    simp [ψ, MulEquiv.ofBijective_apply, FreeGroup.freeGroupCongr]
  have hψ : ∀ s : pts n, IsLoopAround (ψ.symm (FreeGroup.of s)) s := fun s ↦ by
    have := hl (e s)
    rw [coe_ptsEquiv] at this
    rw [show s = e.symm (e s) from (e.symm_apply_apply s).symm, hψs]
    simpa using this
  set w : FreeGroup (pts n) := (List.ofFn fun i ↦ FreeGroup.of (e.symm i)).prod
  have hψw : ψ.symm w = δ ≫ ⟦circ (circleIn_univ hRr) 0⟧ ≫ Groupoid.inv δ := by
    rw [map_list_prod, List.map_ofFn, ← hp]
    congr 1
    exact List.ofFn_inj.2 (funext hψs)
  letI := cov.fundamentalGroupMulAction x
  letI : MulAction (FreeGroup (pts n)) (punctMap f _ ⁻¹' {x}) :=
    MulAction.compHom _ ψ.symm.toMonoidHom
  have hφ : ∀ (γ : FreeGroup (pts n)) (e : punctMap f _ ⁻¹' {x}),
      γ • e = cov.monodromy (ψ.symm γ) e := fun _ _ ↦ rfl
  let F : punctMap f (pts n) ⁻¹' {x} ≃ f ⁻¹' {f e₀} :=
    { toFun := fun e ↦ ⟨e.1.1, congrArg Subtype.val e.2⟩
      invFun := fun y ↦ ⟨⟨y.1, by rw [show f y.1 = f e₀ from y.2]; exact he₀⟩,
        Subtype.ext (show f y.1 = f e₀ from y.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  haveI : Finite (f ⁻¹' {f e₀}) := (hfib _).to_subtype
  haveI : Finite (punctMap f (pts n) ⁻¹' {x}) := Finite.of_equiv _ F.symm
  obtain ⟨g, hiso, hcard⟩ := exists_mulEquiv_surfaceGroup_zero (fun s hs ↦ norm_sub_cen_le hs)
    (by positivity) w I cov ψ hφ D hj hrange hψ e rfl hρR (circleIn_univ hRr) 0 hR₀ hR₁
    ⟨δ, hψw⟩ ⟨⟨e₀, he₀⟩, rfl⟩
  rw [Nat.card_congr F] at hcard
  exact ⟨g, hiso, hcard⟩

end Charts

end BranchedCover.Gen

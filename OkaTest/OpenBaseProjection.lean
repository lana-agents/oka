/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.FiniteMorphism
import OkaTest.MonicProjection

/-!
# Non-vacuity of the projection of a cylinder over a *proper* open subset of the base

`Oka/AnalyticSpace/OpenBaseProjection.lean` carries the finiteness half of *the projection of a
monic hypersurface to its base is finite* across a restriction of the base, and its hypotheses are
six. Nothing in its statement says they can all hold at once over an open subset that is not the
whole of `ℂ^n`, and if they could not the theorem would be
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` in disguise. This file exhibits one morphism at
which they hold, over a base that is measurably proper.

**The parabola `z = w²` above the punctured `z`-line.** The ambient open set is
`ComplexAnalytic.cylinder ComplexAnalytic.punctured`, the cylinder over `ℂ ∖ {0}`; the curve is
`ComplexAnalytic.parabolaIncl` of `OkaTest/MonicProjection.lean` restricted to the part of it
lying over that base, which `ComplexAnalytic.AnalyticSpace.restrictHom` builds with nothing to
prove; and the family is `ComplexAnalytic.parabolaPoly` read on the subtype.

## What each check is for

* `ComplexAnalytic.cylinder_punctured_ne_top` — **the base is a proper open subset.** Without it
  every statement below would be compatible with `V = ⊤`, where the restricted theorem is the
  unrestricted one and this file would be measuring nothing new. The witness is the origin of
  `ℂ²`, which is in the cylinder over `⊤` and not in this one.
* `ComplexAnalytic.not_isFinite_projRestrict_punctured` — **the projection over `V` is itself not
  finite**, so `ComplexAnalytic.AnalyticSpace.isFinite_comp` does not reach the theorem and the
  criterion `ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` is doing work.
  This is the restricted analogue of `ComplexAnalytic.not_isFinite_proj` in
  `OkaTest/FiniteMorphism.lean`, and it is proved from
  `ComplexAnalytic.infinite_fiber_projRestrict_punctured`: every fibre is a whole copy of `ℂ`,
  which `ComplexAnalytic.cylinderHomeo` exhibits in one line rather than by a coordinate
  computation.
* `ComplexAnalytic.not_injective_base_parabolaPunctured_comp_projRestrict` — **the composite is
  not injective**, so it is not a closed embedding and
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` does not reach it either. Both
  square roots of `1` survive the puncture, which is why this example still works after the base
  has been cut down.
* `ComplexAnalytic.isFinite_parabolaPunctured_comp_projRestrict` — the theorem itself.

## What is not checked here

* **Nothing about stalks, so nothing here is finite étale.** The parabola over the *punctured*
  line is exactly where the germ of `X² - C z` does have a simple zero along the last axis — that
  is the point of the puncture, and it is why the punctured base is the right one to test —
  but the hypothesis of `ComplexAnalytic.isIso_stalkMap_comp_projRestrict` is
  `PowerSeries.order (MvPowerSeries.partialEval …) = 1` on a germ, and computing that order for
  this germ is a Weierstrass computation nothing in this repository does. So the two halves are
  still not exhibited at one morphism, here or in `OkaTest/MonicProjection.lean`.
* **Nothing about `ComplexAnalytic.IsCutOutBy`.** The morphism is built by restricting a
  hand-built one and its image is computed from `ComplexAnalytic.range_base_parabolaIncl`, so
  `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` is what is applied and
  `ComplexAnalytic.isFinite_comp_projRestrict_of_isCutOutBy` and
  `ComplexAnalytic.range_base_eq_of_isCutOutBy_resΓ` are exercised nowhere. The reason is the one
  `OkaTest/FiniteMorphism.lean` gives: cut-out data for a morphism of *analytic* spaces is never
  produced in this repository, only assumed.
* **No second example.** One instance is what makes the hypotheses jointly satisfiable over a
  proper open base; nothing here says the theorem is sharp in any hypothesis, and in particular
  nothing degenerates the degree.
-/
open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

/-! ### The parabola above the punctured `z`-line -/

/-- **The parabola, restricted to the part of it lying over the punctured `z`-line.**

Nothing is proved to build it: the source is the preimage of the cylinder, which is what
`ComplexAnalytic.AnalyticSpace.restrictHom` takes, and the `ℂ`-linearity comes with it. -/
def parabolaPunctured :
    (AnalyticSpace.complexAffineSpace.{u} 1).restrict
        ((Opens.map (parabolaIncl.{u}).toLRSHom.base).obj (cylinder punctured.{u})) ⟶
      (AnalyticSpace.complexAffineSpace.{u} 2).restrict (cylinder punctured.{u}) :=
  AnalyticSpace.restrictHom parabolaIncl.{u} (cylinder punctured.{u})

/-- The family `X² - C z`, over the punctured `z`-line rather than over the whole of it. -/
def parabolaPolyPunctured (s : ↥(punctured.{u})) : Polynomial ℂ :=
  parabolaPoly.{u} s.1

/-- **Its image is the zero locus of that family**, which is
`ComplexAnalytic.range_base_parabolaIncl_eq_zeroLocus` intersected with the cylinder — and that
intersection is `ComplexAnalytic.mem_range_base_restrictHom_iff`, so there is nothing to compute:
the two set-builders are the same after `ComplexAnalytic.cylinderHomeo` is unfolded. -/
theorem range_base_parabolaPunctured :
    Set.range ((parabolaPunctured.{u}).toLRSHom.base) =
      {z | (parabolaPolyPunctured.{u} (cylinderHomeo punctured.{u} z).1).eval
        (cylinderHomeo punctured.{u} z).2 = 0} :=
  Set.ext fun z ↦
    (mem_range_base_restrictHom_iff parabolaIncl.{u}.toLRSHom (cylinder punctured.{u}) z).trans
      (by
        rw [range_base_parabolaIncl_eq_zeroLocus]
        simp only [Set.mem_setOf_eq, cylinderHomeo_apply, parabolaPolyPunctured]
        exact Iff.rfl)

/-- **The projection of the parabola above the punctured line to that line is finite** — the
hypotheses of `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` all hold at once over a
base that is not the whole of `ℂ`. -/
theorem isFinite_parabolaPunctured_comp_projRestrict :
    AnalyticSpace.IsFinite
      (parabolaPunctured.{u} ≫ AnalyticSpace.projRestrict punctured.{u}) :=
  isFinite_comp_projRestrict_of_range_eq (d := 2) parabolaPunctured.{u}
    (isClosedEmbedding_base_restrictHom isClosedEmbedding_base_parabolaIncl.{u} _)
    (q := parabolaPolyPunctured.{u})
    (fun _ ↦ monic_parabolaPoly _) (fun _ ↦ natDegree_parabolaPoly _)
    (fun j ↦ (continuous_coeff_parabolaPoly.{u} j).comp continuous_subtype_val)
    range_base_parabolaPunctured.{u}

/-! ### Why the two easy routes to finiteness are unavailable -/

/-- **The cylinder over the punctured line is a proper open subset of `ℂ²`**, so the theorem
applied above is the restricted one and not the unrestricted one in disguise. -/
theorem cylinder_punctured_ne_top : cylinder punctured.{u} ≠ ⊤ := by
  intro h
  have hmem : (0 : ULift.{u} (Fin 2) → ℂ) ∈ cylinder punctured.{u} := by rw [h]; trivial
  rw [mem_cylinder] at hmem
  exact ((mem_punctured_iff.{u} _).1 hmem) rfl

/-- **Every fibre of the projection over the punctured line is infinite**: it is a whole copy of
`ℂ`, which `ComplexAnalytic.cylinderHomeo` exhibits. -/
theorem infinite_fiber_projRestrict_punctured (s : ↥(punctured.{u})) :
    Infinite ((AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base ⁻¹' {s}) := by
  refine Infinite.of_injective
    (fun c : ℂ ↦ (⟨(cylinderHomeo punctured.{u}).symm (s, c), ?_⟩ :
      ((AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base ⁻¹' {s}))) ?_
  · change (AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base _ = s
    rw [base_projRestrict_eq]
    exact congrArg Prod.fst ((cylinderHomeo punctured.{u}).apply_symm_apply (s, c))
  · intro c₁ c₂ hc
    have h : (cylinderHomeo punctured.{u}) ((cylinderHomeo punctured.{u}).symm (s, c₁)) =
        (cylinderHomeo punctured.{u}) ((cylinderHomeo punctured.{u}).symm (s, c₂)) :=
      congrArg _ (congrArg Subtype.val hc)
    rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at h
    exact congrArg Prod.snd h

/-- **The projection over the punctured line is not finite**, so
`ComplexAnalytic.AnalyticSpace.isFinite_comp` does not prove the theorem above and
`ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` is being used for something no
composition lemma reaches. The unrestricted statement is
`ComplexAnalytic.not_isFinite_proj`. -/
theorem not_isFinite_projRestrict_punctured :
    ¬ AnalyticSpace.IsFinite (AnalyticSpace.projRestrict punctured.{u}) :=
  AnalyticSpace.not_isFinite_of_infinite_fiber _ ⟨fun _ ↦ (1 : ℂ), (mem_punctured_iff.{u} _).2
    one_ne_zero⟩ (infinite_fiber_projRestrict_punctured.{u} _)

section NotInjective

/-- A nonzero constant `c`, as a point of the source of `ComplexAnalytic.parabolaPunctured`: the
source is where `c²` is nonzero, so a nonzero `c` lies in it. -/
def parabolaSource {c : ℂ} (hc : c ≠ 0) :
    (AnalyticSpace.complexAffineSpace.{u} 1).restrict
      ((Opens.map (parabolaIncl.{u}).toLRSHom.base).obj (cylinder punctured.{u})) :=
  ⟨fun _ ↦ c, by
    change (AnalyticSpace.proj.{u} 1).toLRSHom.base
      ((parabolaIncl.{u}).toLRSHom.base (fun _ ↦ c)) ∈ punctured.{u}
    refine (mem_punctured_iff.{u} _).2 fun hzero ↦ ?_
    have key := congrFun
      (uliftSnocHomeo_fst.{u} ((parabolaIncl.{u}).toLRSHom.base (fun _ ↦ c))) (ULift.up 0)
    have h2 : ((parabolaIncl.{u}).toLRSHom.base (fun _ ↦ c) : ULift.{u} (Fin 2) → ℂ)
        (ULift.up (Fin.castSucc 0)) = 0 := key.trans hzero
    rw [base_parabolaIncl] at h2
    simp only [if_pos (by rfl : (ULift.up (Fin.castSucc 0) : ULift.{u} (Fin 2)) = ULift.up 0)] at h2
    exact pow_ne_zero 2 hc h2⟩

/-- **The composite sends `c` to `c²`**, in the one coordinate of the base. -/
theorem base_parabolaSource_comp {c : ℂ} (hc : c ≠ 0) :
    (((parabolaPunctured.{u} ≫ AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base
      (parabolaSource.{u} hc)).1 : ULift.{u} (Fin 1) → ℂ) = fun _ ↦ c ^ 2 := by
  have h1 : ((parabolaPunctured.{u} ≫ AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base
      (parabolaSource.{u} hc)).1 =
      (uliftSnocHomeo.{u} 1 ((parabolaIncl.{u}).toLRSHom.base (fun _ ↦ c))).1 := by
    change ((AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base
      ((parabolaPunctured.{u}).toLRSHom.base (parabolaSource.{u} hc))).1 = _
    rw [base_projRestrict_eq]
    exact congrArg (fun w ↦ (uliftSnocHomeo.{u} 1 w).1)
      (base_restrictHom (parabolaIncl.{u}).toLRSHom (cylinder punctured.{u}) _)
  rw [h1]
  refine funext fun j ↦ ?_
  change ((parabolaIncl.{u}).toLRSHom.base (fun _ ↦ c) : ULift.{u} (Fin 2) → ℂ)
    (ULift.up j.down.castSucc) = c ^ 2
  rw [base_parabolaIncl]
  simp [Fin.castSucc, Subsingleton.elim j.down 0]

/-- **The composite is not injective**, so it is not a closed embedding and
`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` does not prove the theorem above
either: the two square roots of `1` lie over the same point. -/
theorem not_injective_base_parabolaPunctured_comp_projRestrict :
    ¬ Function.Injective
      ((parabolaPunctured.{u} ≫ AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base) := by
  intro hinj
  have hne : (parabolaSource.{u} (one_ne_zero (α := ℂ))) ≠
      parabolaSource.{u} (neg_ne_zero.2 (one_ne_zero (α := ℂ))) := by
    intro h
    have := congrArg (fun p ↦ (p.1 : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)) h
    simp only [parabolaSource] at this
    exact one_ne_zero (α := ℂ) (by linear_combination this / 2)
  refine hne (hinj (Subtype.ext ?_))
  rw [base_parabolaSource_comp, base_parabolaSource_comp]
  norm_num

end NotInjective

end ComplexAnalytic

end

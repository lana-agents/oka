/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.MonicProjection

/-!
# Non-vacuity of the monic-hypersurface bridge

`Oka/Analytification/MonicHypersurface.lean` turns a polynomial `G` monic in the last variable
into the family of monic polynomials that `ComplexAnalytic.isFinite_comp_proj_of_range_eq` asks
for. Four things could be wrong with it that its type does not show, and this file rules all four
out at `G = X² - x₀`, the parabola `OkaTest/MonicProjection.lean` already builds by hand:

* **The equivalence could split off the wrong variable.**
  `ComplexAnalytic.lastVarPolyEquiv_symm_parabolaG` names both variables: the polynomial
  variable of `G` comes back as the coordinate `1` of `ℂ²` and its coefficient variable as the
  coordinate `0`. Split them the other way and this is false.
* **The family could be the wrong family.** `ComplexAnalytic.polyFamily_parabolaG` is that the
  bridge produces `ComplexAnalytic.parabolaPoly` on the nose — the family
  `OkaTest/MonicProjection.lean` writes down by hand, whose three hypotheses are proved there by
  hand. So the two routes to the same finiteness statement agree, and
  `ComplexAnalytic.isFinite_parabolaIncl_comp_proj_of_polyFamily` runs the second one.
* **The section could be the wrong function.**
  `ComplexAnalytic.evalHom_lastVarSection_parabolaG` evaluates it: `z₁² - z₀`.
* **The analytification statement could be about the empty space, or true for the trivial
  reason.** `ComplexAnalytic.range_base_analytificationIncl_parabolaG` says its points are the
  parabola, so `ComplexAnalytic.isFinite_analytification_parabolaG` is not vacuous; and
  `ComplexAnalytic.not_injective_base_analytification_parabolaG_comp_proj` says the composite it
  is about is not injective, so finiteness there is not an instance of
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`. That second one is proved here
  **for the analytification's own composite**, from two points of the analytification itself,
  rather than borrowed from `ComplexAnalytic.not_injective_base_parabolaIncl_comp_proj` over in
  `OkaTest/MonicProjection.lean`: that theorem is about `ComplexAnalytic.parabolaIncl`, and
  nothing below relates the two composites — see `## What is not checked here`.

## What is not checked here

* **That the hand-built parabola and the analytification of `G` are the same analytic space.**
  They have the same image in `ℂ²` — that is `ComplexAnalytic.range_base_parabolaIncl` against
  `ComplexAnalytic.range_base_analytificationIncl_parabolaG` — and nothing below claims more.
  Comparing their structure sheaves is `ComplexAnalytic.IsCutOutBy.uniqueIso`'s business and
  needs cut-out data for `ComplexAnalytic.parabolaIncl`, which
  `OkaTest/MonicProjection.lean`'s `## What is not checked here` explains this repository does
  not produce.
* **Nothing about degeneration or about a bound in place of a fixed degree**, exactly as in
  `OkaTest/MonicProjection.lean`; the family here has constant degree by construction because
  `G` is monic.
* **Nothing standard étale.** `G` is one relation in two variables, and
  `ComplexAnalytic.etalePresentation` is `k + 2` relations in `n + 2` — read the arity off its
  type, `Fin (k + 2) → MvPolynomial (ULift (Fin (n + 2))) ℂ`, and not off the *"two more variables
  and two more relations"* of its docstring, which is right but counts **relative to**
  `ComplexAnalytic.polyPresentation` applied twice, whose `k` relations it keeps. Those `k` are
  the presentation `g` of the base algebra `ComplexAnalytic.PresentedAlgebra`, and they are why
  the base of a standard étale morphism is that algebra's analytification rather than `ℂ^n`; the
  two new relations are `Y·G - 1` and `F`. See
  `Oka/Analytification/MonicHypersurface.lean`'s `## What is not here` for why the second is not
  an instance of the theorem tested here.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

/-! ### The parabola as a polynomial monic in the last variable -/

/-- **`X² - x₀`, as a polynomial in the last variable of `ℂ²` over `ℂ¹`.** -/
def parabolaG : Polynomial (MvPolynomial (ULift.{u} (Fin 1)) ℂ) :=
  Polynomial.X ^ 2 - Polynomial.C (MvPolynomial.X (ULift.up 0))

theorem monic_parabolaG : (parabolaG.{u}).Monic :=
  Polynomial.monic_X_pow_sub_C _ two_ne_zero

theorem natDegree_parabolaG : (parabolaG.{u}).natDegree = 2 :=
  Polynomial.natDegree_X_pow_sub_C

/-- **Both variables are the ones the names say they are**: the polynomial variable of `G` is the
last coordinate of `ℂ²` and its coefficient variable is the first. -/
theorem lastVarPolyEquiv_symm_parabolaG :
    (lastVarPolyEquiv.{u} 1).symm parabolaG.{u} =
      MvPolynomial.X (ULift.up 1) ^ 2 - MvPolynomial.X (ULift.up 0) := by
  rw [AlgEquiv.symm_apply_eq]
  have h0 : (ULift.up 0 : ULift.{u} (Fin 2)) = localisationIncl.{u} 1 (ULift.up 0) := rfl
  have h1 : (ULift.up 1 : ULift.{u} (Fin 2)) = localisationVar.{u} 1 := rfl
  rw [h0, h1]
  simp [parabolaG]

/-! ### The family the bridge produces is the hand-built one -/

/-- **`ComplexAnalytic.polyFamily` at `parabolaG` is `ComplexAnalytic.parabolaPoly`.** -/
theorem polyFamily_parabolaG (w : ULift.{u} (Fin 1) → ℂ) :
    polyFamily.{u} parabolaG.{u} w = parabolaPoly.{u} w := by
  simp [polyFamily, parabolaG, parabolaPoly]

/-- **The parabola is finite over the `z`-line, with all three hypotheses on the family supplied
by the bridge** rather than by the three hand proofs in `OkaTest/MonicProjection.lean`.

`ComplexAnalytic.isFinite_parabolaIncl_comp_proj` is the same conclusion by the other route, so
this is the check that the bridge composes with
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` and not only that it typechecks. -/
theorem isFinite_parabolaIncl_comp_proj_of_polyFamily :
    AnalyticSpace.IsFinite (parabolaIncl.{u} ≫ AnalyticSpace.proj.{u} 1) := by
  refine isFinite_comp_proj_of_range_eq parabolaIncl.{u} isClosedEmbedding_base_parabolaIncl.{u}
    (monic_polyFamily.{u} parabolaG.{u} monic_parabolaG.{u})
    (natDegree_polyFamily.{u} parabolaG.{u} monic_parabolaG.{u})
    (continuous_coeff_polyFamily.{u} parabolaG.{u}) ?_
  simp only [polyFamily_parabolaG]
  exact range_base_parabolaIncl_eq_zeroLocus.{u}

/-! ### The global section -/

/-- **The entire function of `parabolaG` is `z₁² - z₀`.** -/
theorem evalHom_lastVarSection_parabolaG (z : ULift.{u} (Fin 2) → ℂ) :
    OkaRing.evalHom (U := ⊤) (x := z) trivial (lastVarSection.{u} parabolaG.{u}) =
      z (ULift.up 1) ^ 2 - z (ULift.up 0) := by
  rw [evalHom_lastVarSection, polyFamily_parabolaG]
  simp [parabolaPoly]

/-! ### The analytification -/

/-- **The analytification of `ℂ[x, X] ⧸ (X² - x)` is the parabola**, as a subset of `ℂ²`. -/
theorem range_base_analytificationIncl_parabolaG :
    Set.range ⇑(analytificationIncl.{u} ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}]).base =
      {z : complexAffineSpace.{u} 2 |
        (z : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) ^ 2 = (z : ULift.{u} (Fin 2) → ℂ)
          (ULift.up 0)} := by
  rw [range_base_analytificationIncl]
  ext z
  simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Matrix.cons_val_zero,
    lastVarPolyEquiv_symm_parabolaG, map_sub, map_pow, MvPolynomial.eval_X, sub_eq_zero]

/-- **And it is finite over the `z`-line**, by the theorem that takes no cut-out datum. -/
theorem isFinite_analytification_parabolaG :
    AnalyticSpace.IsFinite
      (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}] ≫
        AnalyticSpace.proj.{u} 1) :=
  isFinite_analytification_comp_proj.{u} parabolaG.{u} monic_parabolaG.{u}

/-- **The composite's underlying map reads off the first coordinate of the ambient point.**

`ComplexAnalytic.base_proj_eq` at `n = 1`, with `ComplexAnalytic.analytificationInclHom` unfolded
to `ComplexAnalytic.analytificationIncl` definitionally. -/
theorem base_analytification_parabolaG_comp_proj
    (p : AnalyticSpace.analytification.{u} ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}]) :
    (((analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}] ≫
        AnalyticSpace.proj.{u} 1).toLRSHom.base p) : ULift.{u} (Fin 1) → ℂ) =
      fun _ ↦ (((analytificationIncl.{u}
        ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}]).base p) :
          ULift.{u} (Fin 2) → ℂ) (ULift.up 0) := by
  refine funext fun l ↦ ?_
  have hl : l.down = (0 : Fin 1) := Subsingleton.elim _ _
  rw [show (((analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}] ≫
      AnalyticSpace.proj.{u} 1).toLRSHom.base p) : ULift.{u} (Fin 1) → ℂ) = _ from
    congrFun (base_proj_eq.{u} 1) _]
  change (((analytificationIncl.{u} ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}]).base p) :
    ULift.{u} (Fin 2) → ℂ) (ULift.up l.down.castSucc) = _
  rw [hl]
  rfl

/-- **And the composite it is about is not injective**, so
`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` cannot produce
`ComplexAnalytic.isFinite_analytification_parabolaG` either, and the finiteness there is doing
work no closed-embedding argument reaches.

Proved for the analytification's own composite rather than transported from
`ComplexAnalytic.not_injective_base_parabolaIncl_comp_proj`, which is about
`ComplexAnalytic.parabolaIncl`: this file does not claim the two spaces are the same, so there is
nothing to transport along.

The two ambient points `(1, 1)` and `(1, -1)` are in the image by
`ComplexAnalytic.range_base_analytificationIncl_parabolaG`, and both project to `1` by
`ComplexAnalytic.base_analytification_parabolaG_comp_proj`, so an injective composite would
identify their two preimages — and then their *images* would be equal too, which they are not.
**The closed-embedding property of the inclusion is not used here**: the contradiction is read
off the images, so `ComplexAnalytic.range_base_analytificationIncl_parabolaG` is the only thing
about the inclusion this needs. -/
theorem not_injective_base_analytification_parabolaG_comp_proj :
    ¬ Function.Injective
      ((analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}] ≫
          AnalyticSpace.proj.{u} 1).toLRSHom.base :
        AnalyticSpace.analytification.{u} ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}] →
          AnalyticSpace.complexAffineSpace.{u} 1) := by
  intro hinj
  have hmem : ∀ c : ℂ, c ^ 2 = 1 →
      ((fun j ↦ ![(1 : ℂ), c] j.down) : AnalyticSpace.complexAffineSpace.{u} 2) ∈
        Set.range ⇑(analytificationIncl.{u}
          ![(lastVarPolyEquiv.{u} 1).symm parabolaG.{u}]).base := by
    intro c hc
    rw [range_base_analytificationIncl_parabolaG.{u}]
    exact hc
  obtain ⟨p, hp⟩ := hmem 1 (by norm_num)
  obtain ⟨q, hq⟩ := hmem (-1) (by norm_num)
  have hpq : p = q := by
    refine hinj (funext fun l ↦ ?_)
    rw [congrFun (base_analytification_parabolaG_comp_proj.{u} p) l,
      congrFun (base_analytification_parabolaG_comp_proj.{u} q) l, hp, hq]
    norm_num
  rw [hpq, hq] at hp
  have h := congrFun hp (ULift.up 1)
  norm_num at h

end ComplexAnalytic

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of `Hom(ℂ^n|V, ℂ) ≃ Γ(ℂ^n|V, 𝒪)`

`Oka/AnalyticSpace/HolomorphicMapOpen.lean` builds a morphism of complex analytic spaces
`ℂ^n|V ⟶ ℂ` from a global section of `𝒪_{ℂ^n|V}`. The way that could be true and empty is
unusual and it is **not** that the hom-set or the section ring is trivial: it is that the
theorem could be **no stronger than the case `V = ⊤`** already on `master`, which is what would
happen if every global section on `V` were the restriction of an entire function.

`not_restrict_eq_invCoord` is the statement that rules that out, and everything else in this
file exists to make it meaningful.

* `punctured` is `{z₀ ≠ 0} ⊆ ℂ`, and `punctured_ne_top` says it is a *proper* open subset, so
  the construction is not being run at `⊤` in disguise.
* `invCoord` is `1/z₀`, a global section of `𝒪_{ℂ|punctured}`. That it is one is the only place
  in this development where `OkaAnalytic.comp_analyticOn`'s hypothesis — analyticity **on an
  open set** rather than everywhere — is what is available.
* `not_restrict_eq_invCoord`: **no entire function restricts to `1/z₀`.** So the morphism
  `invHom` below is not the restriction of a morphism `ℂ ⟶ ℂ`, and
  `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict` is strictly stronger than
  `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine` followed by restriction.
* `base_invHom` computes the base map of the morphism the theorem produces — it is `z ↦ 1/z`,
  not something the construction could have returned by ignoring its input — and
  `base_invHom_two` puts a number on it. `base_invHom_via_eval` computes the same map by a route
  sharing no lemma, which is what pins the extension-by-zero convention of
  `ComplexAnalytic.okaMapOpenFun`; `base_invHom` alone cannot, since it is `rfl`.

**What this does not check.** That the construction is ever applied to a `V` which is not an
open subset of `ℂ^n` — that is taxis #654's general `Z`, which needs the chart step and a
gluing theorem and is not done. See the module docstring of the library file.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-! ### The punctured plane and `1/z` -/

/-- The punctured plane `{z₀ ≠ 0} ⊆ ℂ`, as an open subspace of `ℂ¹`. -/
def punctured : (AnalyticSpace.complexAffineSpace.{u} 1).Opens where
  carrier := {z : ULift.{u} (Fin 1) → ℂ | z (ULift.up 0) ≠ 0}
  is_open' := isOpen_compl_singleton.preimage (continuous_apply (ULift.up 0))

theorem mem_punctured_iff (z : ULift.{u} (Fin 1) → ℂ) :
    z ∈ punctured.{u} ↔ z (ULift.up 0) ≠ 0 := Iff.rfl

/-- The same, for the open which indexes the *global sections* of `ℂ|punctured`. The two opens
have the same points and are not definitionally equal; this is the only conversion the file
needs, and `ComplexAnalytic.mem_functor_obj_top_iff` is where it lives. -/
theorem mem_puncturedTop_iff (z : ULift.{u} (Fin 1) → ℂ) :
    z ∈ punctured.{u}.isOpenEmbedding.isOpenMap.functor.obj ⊤ ↔ z (ULift.up 0) ≠ 0 :=
  mem_functor_obj_top_iff punctured.{u} z

/-- **`punctured` is a proper open subset**, so nothing below is the `V = ⊤` case in disguise:
the origin is not in it. -/
theorem punctured_ne_top : punctured.{u} ≠ ⊤ := fun hcon ↦
  (show (fun _ ↦ (0 : ℂ)) ∈ punctured.{u} from hcon ▸ trivial) rfl

/-- **`1/z₀`, as a global section of `𝒪_{ℂ|punctured}`.**

Holomorphy is `AnalyticAt.inv` at each point of the open set, transported to the extension by
zero along the eventual equality the openness of `punctured` supplies. -/
def invCoord : OkaRing (punctured.{u}.isOpenEmbedding.isOpenMap.functor.obj ⊤) :=
  OkaRing.mk (fun p ↦ (p.1 (ULift.up 0))⁻¹) (by
    refine (okaAnalytic_iff _).2 fun x hx ↦ ?_
    refine AnalyticAt.congr (f := fun z : ULift.{u} (Fin 1) → ℂ ↦ (z (ULift.up 0))⁻¹) ?_ ?_
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin 1) ↦ ℂ)
        (ULift.up 0)).analyticAt x).inv ((mem_puncturedTop_iff x).1 hx)
    · refine Filter.eventuallyEq_of_mem
        (((punctured.{u}.isOpenEmbedding.isOpenMap.functor.obj ⊤).2).mem_nhds hx) fun z hz ↦ ?_
      exact (Subtype.val_injective.extend_apply
        (fun p : ↥(punctured.{u}.isOpenEmbedding.isOpenMap.functor.obj ⊤) ↦
          (p.1 (ULift.up 0))⁻¹) 0 ⟨z, hz⟩).symm)

/-- The value of `invCoord` at a point is what its name says. -/
theorem evalHom_invCoord {z : ULift.{u} (Fin 1) → ℂ}
    (hz : z ∈ punctured.{u}.isOpenEmbedding.isOpenMap.functor.obj ⊤) :
    OkaRing.evalHom hz invCoord.{u} = (z (ULift.up 0))⁻¹ :=
  rfl

/-! ### `1/z` does not extend -/

/-- If an entire function restricts to `invCoord`, its values on `punctured` are `1/z₀`. -/
theorem toGlobalFun_of_restrict_eq (f : OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)))
    (hcon : OkaRing.restrict le_top f = invCoord.{u})
    {z : ULift.{u} (Fin 1) → ℂ} (hz : z (ULift.up 0) ≠ 0) :
    f.toGlobalFun ⊤ z = (z (ULift.up 0))⁻¹ := by
  have h := congrFun (congrArg (OkaRing.toFun _) hcon)
    ⟨z, (mem_puncturedTop_iff z).2 hz⟩
  rw [OkaRing.restrict_toFun] at h
  exact (f.toGlobalFun_apply trivial).trans h

/-- **No entire function on `ℂ` restricts to `1/z₀`.**

This is the statement that makes the open case a genuinely new theorem rather than the `V = ⊤`
case composed with restriction. The argument is the only analysis in this file:
`t ↦ f(t)·t − 1` is continuous, vanishes at every `t ≠ 0` by the hypothesis, and equals `−1` at
`t = 0`; since `𝓝[≠] 0` is not the bottom filter on `ℂ`, the two limits along it must agree. -/
theorem not_restrict_eq_invCoord (f : OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ))) :
    OkaRing.restrict le_top f ≠ invCoord.{u} := by
  intro hcon
  have hzero : ∀ t : ℂ, t ≠ 0 → f.toGlobalFun ⊤ (fun _ ↦ t) * t - 1 = 0 := fun t ht ↦ by
    rw [toGlobalFun_of_restrict_eq f hcon (z := fun _ ↦ t) ht, inv_mul_cancel₀ ht, sub_self]
  have hcont : Continuous fun t : ℂ ↦ f.toGlobalFun ⊤ (fun _ ↦ t) * t - 1 := by
    refine Continuous.sub (Continuous.mul ?_ continuous_id) continuous_const
    exact (continuousOn_univ.1 fun z _ ↦ f.continuousOn_toGlobalFun z trivial).comp
      (continuous_pi fun _ ↦ continuous_id)
  have h1 : Filter.Tendsto (fun t : ℂ ↦ f.toGlobalFun ⊤ (fun _ ↦ t) * t - 1)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (f.toGlobalFun ⊤ (fun _ ↦ (0 : ℂ)) * 0 - 1)) :=
    hcont.continuousAt.continuousWithinAt
  have h2 : Filter.Tendsto (fun t : ℂ ↦ f.toGlobalFun ⊤ (fun _ ↦ t) * t - 1)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) :=
    Filter.Tendsto.congr'
      (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun t ht ↦ (hzero t ht).symm)
      tendsto_const_nhds
  have h3 := tendsto_nhds_unique h1 h2
  simp at h3

/-! ### The morphism the theorem produces -/

/-- The morphism of complex analytic spaces `ℂ∖{0} ⟶ ℂ` attached to `1/z`. -/
def invHom : (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} ⟶
    AnalyticSpace.complexAffineSpace.{u} 1 :=
  AnalyticSpace.okaMapOpen fun _ ↦ invCoord.{u}

/-- Its coordinate pullback is the section it was built from. -/
theorem coordPullback_invHom (j : ULift.{u} (Fin 1)) :
    AnalyticSpace.coordPullback invHom.{u} j = invCoord.{u} :=
  AnalyticSpace.coordPullback_okaMapOpen _ j

/-- **Its base map is `z ↦ 1/z`**, named as a function rather than sampled: a construction that
ignored its input could not satisfy this. -/
theorem base_invHom (y : ↥punctured.{u}) (j : ULift.{u} (Fin 1)) :
    (invHom.{u}.toLRSHom.base y : ULift.{u} (Fin 1) → ℂ) j = (y.1 (ULift.up 0))⁻¹ :=
  (congrFun (base_okaMapOpenHom (fun _ ↦ invCoord.{u}) y) j).trans
    ((okaMapOpenFun_apply (fun _ ↦ invCoord.{u})
      ((mem_puncturedTop_iff y.1).2 y.2) j).trans
      (evalHom_invCoord ((mem_puncturedTop_iff y.1).2 y.2)))

/-- …and a number on it: the point `2` goes to `1/2`. -/
theorem base_invHom_two :
    (invHom.{u}.toLRSHom.base ⟨fun _ ↦ (2 : ℂ), two_ne_zero⟩ : ULift.{u} (Fin 1) → ℂ)
        (ULift.up 0) = 2⁻¹ :=
  base_invHom _ _

/-- **The same base map, by a route sharing no lemma with `base_invHom`.**

`base_invHom` goes through `ComplexAnalytic.base_okaMapOpenHom`, which is `rfl`, so on its own it
cannot be evidence: it reads the base map off the construction. This reads it off
`coordPullback_invHom` instead, through naturality of evaluation
(`ComplexAnalytic.AnalyticSpace.eval_c_app`), the value of a coordinate on `ℂ¹`
(`ComplexAnalytic.AnalyticSpace.eval_coord`) and the value of a global section on `ℂ¹|V`
(`ComplexAnalytic.eval_restrict_complexAffineSpace`).

**The two agreeing is what pins `ComplexAnalytic.okaMapOpenFun`'s extension-by-zero
convention**: an error in it breaks this route and not the `rfl` one. Do not replace this proof
with `base_invHom`; the content is that both elaborate. -/
theorem base_invHom_via_eval (y : ↥punctured.{u}) (j : ULift.{u} (Fin 1)) :
    (invHom.{u}.toLRSHom.base y : ULift.{u} (Fin 1) → ℂ) j = (y.1 (ULift.up 0))⁻¹ :=
  (AnalyticSpace.eval_coord (invHom.{u}.toLRSHom.base y) j).symm.trans
    ((AnalyticSpace.eval_c_app
        (Z := (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u})
        (W := AnalyticSpace.complexAffineSpace.{u} 1) invHom.{u}.toLRSHom
        invHom.{u}.isCLinear (U := ⊤) y trivial (coord j)).symm.trans
      ((congrArg (((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}).eval
          (U := ⊤) y trivial) (coordPullback_invHom.{u} j)).trans
        ((eval_restrict_complexAffineSpace punctured.{u} y invCoord.{u}).trans
          (evalHom_invCoord _))))

/-- The bijection is not a bijection onto nothing: it sends `invHom` to `1/z₀`.

There is no separate `ℂ^n|V` bijection: this is
`ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral` at the open subspace, which is where
`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_restrict` is now consumed. -/
theorem homComplexLineEquivGeneral_invHom :
    AnalyticSpace.homComplexLineEquivGeneral.{u}
      ((AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}) invHom.{u} =
        invCoord.{u} :=
  coordPullback_invHom _

end

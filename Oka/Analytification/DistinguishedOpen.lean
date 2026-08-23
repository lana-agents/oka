/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Nonvanishing
import Oka.Analytification.UniversalProperty

/-!
# The analytification of a distinguished open is a distinguished open of the analytification

For `A = ℂ[x₁, …, x_n] ⧸ (g₁, …, g_k)` and `f ∈ ℂ[x]`, the localisation `A_f` is presented by
adjoining one variable and one equation,

  `A_f = ℂ[x₁, …, x_n, t] ⧸ (g₁, …, g_k, t·f - 1)`,

and this file proves that the analytification of that presentation **is** the open subspace of
`X^an = A^an` on which `f` does not vanish:

  `ComplexAnalytic.localisationIso : (A_f)^an ≅ X^an|D(f)`,

**over `X^an`** — `ComplexAnalytic.localisationIso_hom_ofRestrict` and
`ComplexAnalytic.localisationIso_inv_localisationProj` say the isomorphism commutes with the
projection `(A_f)^an ⟶ X^an` and with the inclusion of the open subspace. Without that the
statement would only compare two spaces that happen to be isomorphic, and would say nothing
about the immersion.

This is the input the analytification of a *non-affine* scheme needs, and the reason it is worth
stating on its own. `Oka/AnalyticSpace/Glue.lean` already glues an analytic space out of a glue
data of analytic pieces; what a glue data needs from *this* side is that the transition maps are
open immersions, and a scheme locally of finite type over `ℂ` is covered by affines whose pairwise
intersections are covered by opens distinguished in both. So it is the **distinguished** case
that is needed, and the analytification of a general open immersion is neither needed for it nor
proved here. Assembling the analytification of a non-affine scheme is a further step and is not
taken in this file.

## The route: the universal property, twice

Both maps are `ComplexAnalytic.liftHom`, which is why this is one file rather than a construction
plus a comparison.

* **Forwards.** `ComplexAnalytic.localisationProj` is the universal property of `X^an` applied to
  the first `n` coordinates of `(A_f)^an`; they satisfy the `gⱼ` because the `gⱼ` occur among the
  equations of the larger presentation, renamed along the inclusion of the variables. Its image
  lies in `D(f)` because the last equation says that `f`, pulled back, is invertible in
  `Γ((A_f)^an, 𝒪)`, so its *value* at every point is invertible in `ℂ`, hence nonzero — this is
  `ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff`, and it is the only genuinely geometric
  step in the file. `ComplexAnalytic.AnalyticSpace.liftOpen` then factors it through `X^an|D(f)`.

* **Backwards.** `ComplexAnalytic.restrictToLocalisation` is the universal property of
  `(A_f)^an` applied to the tuple which is the restriction of the coordinates of `X^an` on the
  old variables and the **inverse** of the restriction of `f` on the new one. That inverse exists
  by `ComplexAnalytic.AnalyticSpace.isUnit_resΓ_nonvanishing`, which is why that statement has to
  be about a unit rather than about non-vanishing.

* **The round trips** are `ComplexAnalytic.hom_ext_analytification` on one side and
  `ComplexAnalytic.AnalyticSpace.hom_ext_restrict` followed by it on the other: a morphism into
  an open subspace is determined by its composite with the inclusion, and a morphism into an
  analytification by the pullbacks of the coordinates.

## Non-vacuity

An isomorphism of analytifications is weak evidence on its own —
`ComplexAnalytic.analytificationIsoOfPresentationIdealEq` already produces plenty, and every
statement here is satisfied by `D(f) = ⊤` and the identity. What rules that reading out is
`ComplexAnalytic.localisationOpen_ne_top`: if `f` vanishes at some point of `X^an` then `D(f)` is
a **proper** open subset. `OkaTest/AnalytificationDistinguishedOpen.lean` runs it at the node,
where `D(z₀)` is the punctured axis that `OkaTest/OpenSubspace.lean` builds by hand.

## Main definitions

- `ComplexAnalytic.localisationPresentation`: **the presentation of `A_f`** — the `gⱼ` in one more
  variable, together with `t·f - 1`.
- `ComplexAnalytic.localisationProj`: **the projection `(A_f)^an ⟶ X^an`.**
- `ComplexAnalytic.localisationOpen`: `D(f) ⊆ X^an`, the non-vanishing locus of `f`.
- `ComplexAnalytic.localisationIso`: **the isomorphism `(A_f)^an ≅ X^an|D(f)`.**

## Main results

- `ComplexAnalytic.localisationIso_hom_ofRestrict` and
  `ComplexAnalytic.localisationIso_inv_localisationProj`: **the isomorphism is one over `X^an`.**
- `ComplexAnalytic.eval_localisationProj` and `ComplexAnalytic.base_localisationProj`: the
  projection forgets the last coordinate.
- `ComplexAnalytic.mem_localisationOpen_iff`: a point lies in `D(f)` exactly when `f` does not
  vanish there.
- `ComplexAnalytic.localisationOpen_ne_top`: **`D(f)` is a proper open subset** whenever `f` has a
  zero on `X^an`.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ}

/-! ### The presentation of `A_f` -/

/-- The old variables, read inside the polynomial ring with one more variable. -/
def localisationIncl (n : ℕ) : ULift.{u} (Fin n) → ULift.{u} (Fin (n + 1)) :=
  fun i ↦ ULift.up i.down.castSucc

/-- The new variable, the one that becomes `1/f`. -/
def localisationVar (n : ℕ) : ULift.{u} (Fin (n + 1)) := ULift.up (Fin.last n)

/-- **The presentation of `A_f` obtained from a presentation of `A`**: the old equations in one
more variable, together with `t·f - 1`.

Packaged with `Fin.snoc` because `Fin.lastCases` is then the way to check a statement for every
equation, and the two `simp` lemmas below are the whole interface. Any family with the same span
would do — `ComplexAnalytic.analytificationIsoOfPresentationIdealEq` says the analytification
sees only the ideal — so nothing below depends on this packaging beyond those two lemmas. -/
def localisationPresentation (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (f : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    Fin (k + 1) → MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  Fin.snoc (fun j ↦ MvPolynomial.rename (localisationIncl.{u} n) (g j))
    (MvPolynomial.X (localisationVar.{u} n) *
      MvPolynomial.rename (localisationIncl.{u} n) f - 1)

variable (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

@[simp]
theorem localisationPresentation_castSucc (j : Fin k) :
    localisationPresentation.{u} g f j.castSucc =
      MvPolynomial.rename (localisationIncl.{u} n) (g j) :=
  Fin.snoc_castSucc _ _ j

@[simp]
theorem localisationPresentation_last :
    localisationPresentation.{u} g f (Fin.last k) =
      MvPolynomial.X (localisationVar.{u} n) *
        MvPolynomial.rename (localisationIncl.{u} n) f - 1 :=
  Fin.snoc_last _ _

/-! ### The projection to `X^an` -/

/-- **The coordinates of `(A_f)^an` on the old variables satisfy the old equations.**

`ComplexAnalytic.eval₂_analytificationCoord_eq_zero` at the equation `gⱼ`, moved across
`MvPolynomial.eval₂_rename`: substituting a tuple into a renamed polynomial is substituting the
renamed tuple into the original. -/
theorem eval₂_analytificationCoord_comp_incl_eq_zero (j : Fin k) :
    MvPolynomial.eval₂
        (AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f)).algebraMap
        (analytificationCoord.{u} (localisationPresentation.{u} g f) ∘ localisationIncl.{u} n)
        (g j) = 0 := by
  have h := eval₂_analytificationCoord_eq_zero (localisationPresentation.{u} g f) j.castSucc
  rwa [localisationPresentation_castSucc, MvPolynomial.eval₂_rename] at h

/-- **The projection `(A_f)^an ⟶ X^an`**, the universal property of `X^an` applied to the
coordinates of `(A_f)^an` on the old variables. -/
def localisationProj :
    AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f) ⟶
      AnalyticSpace.analytification.{u} g :=
  liftHom.{u} g _ _ (eval₂_analytificationCoord_comp_incl_eq_zero.{u} g f)

@[simp]
theorem coordPullback_localisationProj_comp (i : ULift.{u} (Fin n)) :
    AnalyticSpace.coordPullback
        (localisationProj.{u} g f ≫ analytificationInclHom.{u} g) i =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationIncl.{u} n i) :=
  coordPullback_liftHom_comp.{u} g _ _ _ i

/-- **The projection carries the `i`-th coordinate of `X^an` to the `i`-th coordinate of
`(A_f)^an`**, which is what the universal property was applied to. -/
@[simp]
theorem pullbackΓ_localisationProj_analytificationCoord (i : ULift.{u} (Fin n)) :
    (localisationProj.{u} g f).pullbackΓ (analytificationCoord.{u} g i) =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationIncl.{u} n i) :=
  (AnalyticSpace.coordPullback_comp (localisationProj.{u} g f)
    (analytificationInclHom.{u} g) i).symm.trans
      (coordPullback_localisationProj_comp.{u} g f i)

/-- **The projection carries a polynomial section to the renamed polynomial section**, the
statement of which the previous lemma is the case `p = xᵢ`. -/
theorem pullbackΓ_localisationProj_polyToGlobal (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (localisationProj.{u} g f).pullbackΓ (polyToGlobal.{u} g p) =
      MvPolynomial.eval₂
        (AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f)).algebraMap
        (analytificationCoord.{u} (localisationPresentation.{u} g f))
        (MvPolynomial.rename (localisationIncl.{u} n) p) :=
  (congrArg (localisationProj.{u} g f).pullbackΓ
      (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) p)).trans
    ((AnalyticSpace.pullbackΓ_eval₂ (localisationProj.{u} g f) (analytificationCoord.{u} g) p).trans
      ((congrArg (fun a ↦ MvPolynomial.eval₂ _ a p)
          (funext (pullbackΓ_localisationProj_analytificationCoord.{u} g f))).trans
        (MvPolynomial.eval₂_rename _ _ _ p).symm))

/-- **The last equation, read on `(A_f)^an`**: the new coordinate is inverse to the pullback of
`f`. This is the whole content of adjoining the variable, and everything below is a consequence
of it. -/
theorem analytificationCoord_localisationVar_mul :
    analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationVar.{u} n) *
        (localisationProj.{u} g f).pullbackΓ (polyToGlobal.{u} g f) = 1 := by
  have h := eval₂_analytificationCoord_eq_zero (localisationPresentation.{u} g f) (Fin.last k)
  rw [localisationPresentation_last, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_one, sub_eq_zero] at h
  rw [pullbackΓ_localisationProj_polyToGlobal]
  exact h

theorem isUnit_pullbackΓ_localisationProj_polyToGlobal :
    IsUnit ((localisationProj.{u} g f).pullbackΓ (polyToGlobal.{u} g f)) :=
  IsUnit.of_mul_eq_one_right _ (analytificationCoord_localisationVar_mul.{u} g f)

/-! ### The open subspace `D(f)` and the isomorphism -/

/-- **`D(f) ⊆ X^an`**, the locus on which the section attached to `f` does not vanish.

An `abbrev` for `ComplexAnalytic.AnalyticSpace.nonvanishing` at
`ComplexAnalytic.polyToGlobal`, so that every lemma about the non-vanishing locus applies to it
unchanged; it exists because that expression occurs in the statement of almost everything
below. -/
abbrev localisationOpen : (AnalyticSpace.analytification.{u} g).Opens :=
  (AnalyticSpace.analytification.{u} g).nonvanishing (polyToGlobal.{u} g f)

/-- **The image of the projection lies in `D(f)`.**

The pullback of `f` is a unit in `Γ((A_f)^an, 𝒪)`, so its value at any point is a unit in `ℂ`,
hence nonzero; and the value of the pullback at a point is the value of `f` at the image point,
which is `ComplexAnalytic.AnalyticSpace.eval_c_app`. This is the step that turns the algebraic
equation `t·f = 1` into a topological containment. -/
theorem range_base_localisationProj_subset :
    Set.range (localisationProj.{u} g f).toLRSHom.base ⊆
      (localisationOpen.{u} g f : Set (AnalyticSpace.analytification.{u} g)) := by
  rintro _ ⟨z, rfl⟩
  refine (AnalyticSpace.mem_nonvanishing_iff _ _).2 ?_
  rw [← AnalyticSpace.eval_c_app (localisationProj.{u} g f).toLRSHom
    (localisationProj.{u} g f).isCLinear (U := ⊤) z trivial (polyToGlobal.{u} g f)]
  exact ((isUnit_pullbackΓ_localisationProj_polyToGlobal.{u} g f).map
    ((AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f)).eval
      (U := ⊤) z trivial)).ne_zero

/-- **The projection, factored through the open subspace `X^an|D(f)`.** -/
def localisationToRestrict :
    AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f) ⟶
      (AnalyticSpace.analytification.{u} g).restrict (localisationOpen.{u} g f) :=
  AnalyticSpace.liftOpen (localisationProj.{u} g f) _
    (range_base_localisationProj_subset.{u} g f)

@[reassoc (attr := simp)]
theorem localisationToRestrict_fac :
    localisationToRestrict.{u} g f ≫
        (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f) =
      localisationProj.{u} g f :=
  AnalyticSpace.liftOpen_fac _ _ _

/-- **The tuple of `n + 1` sections of `𝒪` on `X^an|D(f)` that the inverse map is built from**:
the restrictions of the coordinates of `X^an` on the old variables, and the inverse of the
restriction of `f` on the new one.

The inverse is `ComplexAnalytic.AnalyticSpace.isUnit_resΓ_nonvanishing`, and this is the place
where that statement has to be about a *unit*: a section which merely does not vanish on `D(f)`
would give no element to put here. -/
def localisationSection : ULift.{u} (Fin (n + 1)) →
    ((AnalyticSpace.analytification.{u} g).restrict
      (localisationOpen.{u} g f)).presheaf.obj (op ⊤) :=
  fun i ↦ Fin.lastCases
    (((AnalyticSpace.analytification.{u} g).isUnit_resΓ_nonvanishing
      (polyToGlobal.{u} g f)).unit⁻¹ : _)
    (fun i' ↦ (AnalyticSpace.analytification.{u} g).resΓ (localisationOpen.{u} g f)
      (analytificationCoord.{u} g (ULift.up i')))
    i.down

@[simp]
theorem localisationSection_incl (i : ULift.{u} (Fin n)) :
    localisationSection.{u} g f (localisationIncl.{u} n i) =
      (AnalyticSpace.analytification.{u} g).resΓ (localisationOpen.{u} g f)
        (analytificationCoord.{u} g i) :=
  Fin.lastCases_castSucc i.down

@[simp]
theorem localisationSection_var :
    localisationSection.{u} g f (localisationVar.{u} n) =
      (((AnalyticSpace.analytification.{u} g).isUnit_resΓ_nonvanishing
        (polyToGlobal.{u} g f)).unit⁻¹ : _) :=
  Fin.lastCases_last

/-- **Restricting a polynomial section to `D(f)` substitutes the restricted coordinates.**

`ComplexAnalytic.AnalyticSpace.pullbackΓ_eval₂` at the inclusion of the open subspace: the
`ℂ`-algebra structure on `X^an|D(f)` is the ambient one restricted, so no transport is
involved. -/
theorem resΓ_polyToGlobal (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (AnalyticSpace.analytification.{u} g).resΓ (localisationOpen.{u} g f)
        (polyToGlobal.{u} g p) =
      MvPolynomial.eval₂ ((AnalyticSpace.analytification.{u} g).restrict
          (localisationOpen.{u} g f)).algebraMap
        (localisationSection.{u} g f ∘ localisationIncl.{u} n) p :=
  (congrArg _ (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) p)).trans
    ((AnalyticSpace.pullbackΓ_eval₂
        ((AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f))
        (analytificationCoord.{u} g) p).trans
      (congrArg (fun a ↦ MvPolynomial.eval₂ _ a p)
        (funext fun i ↦ (localisationSection_incl.{u} g f i).symm)))

/-- **The tuple on `X^an|D(f)` satisfies the equations of the larger presentation.** The old ones
because restriction is a ring homomorphism compatible with the constants and `gⱼ` is already zero
upstairs; the new one because the last entry was chosen to be an inverse. -/
theorem eval₂_localisationSection_eq_zero (j : Fin (k + 1)) :
    MvPolynomial.eval₂ ((AnalyticSpace.analytification.{u} g).restrict
        (localisationOpen.{u} g f)).algebraMap (localisationSection.{u} g f)
      (localisationPresentation.{u} g f j) = 0 := by
  refine Fin.lastCases ?_ (fun j' ↦ ?_) j
  · rw [localisationPresentation_last, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_one, MvPolynomial.eval₂_rename,
      localisationSection_var, ← resΓ_polyToGlobal, sub_eq_zero]
    exact Units.inv_mul_of_eq (IsUnit.unit_spec _)
  · rw [localisationPresentation_castSucc, MvPolynomial.eval₂_rename, ← resΓ_polyToGlobal,
      polyToGlobal_apply_eq_zero]
    exact map_zero _

/-- **The inverse map `X^an|D(f) ⟶ (A_f)^an`**, the universal property of `(A_f)^an` applied to
`ComplexAnalytic.localisationSection`. -/
def restrictToLocalisation :
    (AnalyticSpace.analytification.{u} g).restrict (localisationOpen.{u} g f) ⟶
      AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f) :=
  liftHom.{u} (localisationPresentation.{u} g f) _ (localisationSection.{u} g f)
    (eval₂_localisationSection_eq_zero.{u} g f)

@[simp]
theorem coordPullback_restrictToLocalisation_comp (i : ULift.{u} (Fin (n + 1))) :
    AnalyticSpace.coordPullback (restrictToLocalisation.{u} g f ≫
        analytificationInclHom.{u} (localisationPresentation.{u} g f)) i =
      localisationSection.{u} g f i :=
  coordPullback_liftHom_comp.{u} (localisationPresentation.{u} g f) _ _ _ i

@[simp]
theorem pullbackΓ_restrictToLocalisation_analytificationCoord (i : ULift.{u} (Fin (n + 1))) :
    (restrictToLocalisation.{u} g f).pullbackΓ
        (analytificationCoord.{u} (localisationPresentation.{u} g f) i) =
      localisationSection.{u} g f i :=
  (AnalyticSpace.coordPullback_comp (restrictToLocalisation.{u} g f)
    (analytificationInclHom.{u} (localisationPresentation.{u} g f)) i).symm.trans
      (coordPullback_restrictToLocalisation_comp.{u} g f i)

/-- **Restricting to `D(f)` and then pulling back along the factored projection is pulling back
along the projection.**

Spelled at the level of locally ringed spaces, and proved from
`AlgebraicGeometry.LocallyRingedSpace.liftRestrict_fac` rather than from
`ComplexAnalytic.localisationToRestrict_fac`, for the reason
`ComplexAnalytic.AnalyticSpace.resΓ_restrictLE` records: a `congrArg` over morphisms of *analytic*
spaces forces the unification of `(f ≫ g).toLRSHom` with `f.toLRSHom ≫ g.toLRSHom` and does not
elaborate in a million heartbeats. -/
@[simp]
theorem pullbackΓ_localisationToRestrict_resΓ
    (s : (AnalyticSpace.analytification.{u} g).presheaf.obj (op ⊤)) :
    (localisationToRestrict.{u} g f).pullbackΓ
        ((AnalyticSpace.analytification.{u} g).resΓ (localisationOpen.{u} g f) s) =
      (localisationProj.{u} g f).pullbackΓ s :=
  (LocallyRingedSpace.Γ_map_comp_apply (localisationToRestrict.{u} g f).toLRSHom
      ((AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.ofRestrict
        (localisationOpen.{u} g f).isOpenEmbedding) s).symm.trans
    (congrArg (fun m : (AnalyticSpace.analytification.{u}
          (localisationPresentation.{u} g f)).toLocallyRingedSpace ⟶
        (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace ↦
      (LocallyRingedSpace.Γ.map m.op).hom s)
      (LocallyRingedSpace.liftRestrict_fac (localisationProj.{u} g f).toLRSHom
        (localisationOpen.{u} g f) (range_base_localisationProj_subset.{u} g f)))

/-- **The factored projection carries the tuple back to the coordinates of `(A_f)^an`.**

On an old variable this is `ComplexAnalytic.pullbackΓ_localisationProj_analytificationCoord`; on
the new one both the image of the inverse and the new coordinate are inverses of the pullback of
`f`, so they agree by cancellation. This is the half of the round trips that is not
bookkeeping. -/
theorem pullbackΓ_localisationToRestrict_localisationSection (i : ULift.{u} (Fin (n + 1))) :
    (localisationToRestrict.{u} g f).pullbackΓ (localisationSection.{u} g f i) =
      analytificationCoord.{u} (localisationPresentation.{u} g f) i := by
  refine Fin.lastCases (motive := fun d ↦
    (localisationToRestrict.{u} g f).pullbackΓ
        (localisationSection.{u} g f (ULift.up d)) =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (ULift.up d)) ?_ ?_ i.down
  · change (localisationToRestrict.{u} g f).pullbackΓ
        (localisationSection.{u} g f (localisationVar.{u} n)) =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationVar.{u} n)
    rw [localisationSection_var]
    refine ((isUnit_pullbackΓ_localisationProj_polyToGlobal.{u} g f).mul_right_cancel ?_).symm
    rw [analytificationCoord_localisationVar_mul, ← pullbackΓ_localisationToRestrict_resΓ]
    exact ((congrArg (fun s ↦ (localisationToRestrict.{u} g f).pullbackΓ
            (((AnalyticSpace.analytification.{u} g).isUnit_resΓ_nonvanishing
              (polyToGlobal.{u} g f)).unit⁻¹ : _) *
            (localisationToRestrict.{u} g f).pullbackΓ s)
          (IsUnit.unit_spec _).symm).trans
        ((map_mul _ _ _).symm.trans ((congrArg _ (Units.inv_mul _)).trans (map_one _)))).symm
  · intro i'
    change (localisationToRestrict.{u} g f).pullbackΓ
        (localisationSection.{u} g f (localisationIncl.{u} n (ULift.up i'))) =
      analytificationCoord.{u} (localisationPresentation.{u} g f)
        (localisationIncl.{u} n (ULift.up i'))
    rw [localisationSection_incl, pullbackΓ_localisationToRestrict_resΓ,
      pullbackΓ_localisationProj_analytificationCoord]

theorem localisationToRestrict_restrictToLocalisation :
    localisationToRestrict.{u} g f ≫ restrictToLocalisation.{u} g f = 𝟙 _ := by
  refine hom_ext_analytification.{u} (localisationPresentation.{u} g f) _ _ fun i ↦ ?_
  rw [Category.assoc, AnalyticSpace.coordPullback_comp,
    coordPullback_restrictToLocalisation_comp, Category.id_comp]
  exact pullbackΓ_localisationToRestrict_localisationSection.{u} g f i

theorem restrictToLocalisation_localisationToRestrict :
    restrictToLocalisation.{u} g f ≫ localisationToRestrict.{u} g f = 𝟙 _ := by
  refine AnalyticSpace.hom_ext_restrict _ _ _ ?_
  rw [Category.id_comp, Category.assoc, localisationToRestrict_fac]
  refine hom_ext_analytification.{u} g _ _ fun i ↦ ?_
  rw [Category.assoc, AnalyticSpace.coordPullback_comp, coordPullback_localisationProj_comp,
    AnalyticSpace.coordPullback_comp]
  exact (pullbackΓ_restrictToLocalisation_analytificationCoord.{u} g f _).trans
    (localisationSection_incl.{u} g f i)

/-- **The analytification of `A_f` is the non-vanishing locus of `f` in `X^an`.**

The two factorisation lemmas below are what makes this a statement about the open immersion
rather than an accidental isomorphism of spaces. -/
def localisationIso :
    AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f) ≅
      (AnalyticSpace.analytification.{u} g).restrict (localisationOpen.{u} g f) where
  hom := localisationToRestrict.{u} g f
  inv := restrictToLocalisation.{u} g f
  hom_inv_id := localisationToRestrict_restrictToLocalisation.{u} g f
  inv_hom_id := restrictToLocalisation_localisationToRestrict.{u} g f

/-- **The isomorphism is one over `X^an`**: followed by the inclusion of the open subspace it is
the projection. -/
@[simp]
theorem localisationIso_hom_ofRestrict :
    (localisationIso.{u} g f).hom ≫
        (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f) =
      localisationProj.{u} g f :=
  localisationToRestrict_fac.{u} g f

/-- **The inverse is a morphism over `X^an` too**: followed by the projection it is the inclusion
of the open subspace. -/
@[simp]
theorem localisationIso_inv_localisationProj :
    (localisationIso.{u} g f).inv ≫ localisationProj.{u} g f =
      (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f) :=
  (congrArg (fun m ↦ (localisationIso.{u} g f).inv ≫ m)
      (localisationToRestrict_fac.{u} g f)).symm.trans
    ((localisationIso.{u} g f).inv_hom_id_assoc _)

/-! ### What the projection does on points -/

/-- **The projection forgets the last coordinate**, in the form in which the value of every
polynomial can be read off: the value of `p` at the image of `w` is the value of `p` with its
variables renamed at `w` itself.

At `p = xᵢ` this says the `i`-th coordinate of the image point is the `i`-th coordinate of `w`,
which is the concrete description of the projection; `ComplexAnalytic.eval_polyToGlobal` is what
turns a section into a value at both ends. -/
theorem eval_localisationProj
    (w : AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f))
    (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    MvPolynomial.eval
        (((localisationProj.{u} g f).toLRSHom.base w).1.1 : ULift.{u} (Fin n) → ℂ) p =
      MvPolynomial.eval (w.1.1 : ULift.{u} (Fin (n + 1)) → ℂ)
        (MvPolynomial.rename (localisationIncl.{u} n) p) := by
  rw [← eval_polyToGlobal, ← eval_polyToGlobal,
    ← AnalyticSpace.eval_c_app (localisationProj.{u} g f).toLRSHom
      (localisationProj.{u} g f).isCLinear (U := ⊤) w trivial (polyToGlobal.{u} g p)]
  exact congrArg _ ((pullbackΓ_localisationProj_polyToGlobal.{u} g f p).trans
    (RingHom.congr_fun
      (polyToGlobal_eq_eval₂Hom.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) p)).symm)

/-- **The projection is the first `n` coordinates**, which is the concrete description of it:
`ComplexAnalytic.eval_localisationProj` at `p = xᵢ`. -/
@[simp]
theorem base_localisationProj
    (w : AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f))
    (i : ULift.{u} (Fin n)) :
    (((localisationProj.{u} g f).toLRSHom.base w).1.1 : ULift.{u} (Fin n) → ℂ) i =
      (w.1.1 : ULift.{u} (Fin (n + 1)) → ℂ) (localisationIncl.{u} n i) :=
  (MvPolynomial.eval_X i).symm.trans
    ((eval_localisationProj.{u} g f w (MvPolynomial.X i)).trans
      ((congrArg (MvPolynomial.eval (w.1.1 : ULift.{u} (Fin (n + 1)) → ℂ))
        (MvPolynomial.rename_X (localisationIncl.{u} n) i)).trans
          (MvPolynomial.eval_X (localisationIncl.{u} n i))))

/-- **A point of `X^an` lies in `D(f)` exactly when `f` does not vanish there.**

`ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff` decides membership by the value of the
*section*; this says that value is the value of the *polynomial*, which is the form in which a
caller holds it. -/
theorem mem_localisationOpen_iff {y : AnalyticSpace.analytification.{u} g} :
    y ∈ localisationOpen.{u} g f ↔
      MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) f ≠ 0 := by
  rw [AnalyticSpace.mem_nonvanishing_iff, eval_polyToGlobal]

/-- **`D(f)` is a proper open subset whenever `f` vanishes somewhere on `X^an`.**

This is what stops every statement in this file from being satisfied by `D(f) = ⊤` and the
identity, and it is the reason `ComplexAnalytic.eval_polyToGlobal` is quoted here at all: the
hypothesis is about the polynomial, and the conclusion about the open subset. -/
theorem localisationOpen_ne_top (y : AnalyticSpace.analytification.{u} g)
    (hy : MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) f = 0) :
    localisationOpen.{u} g f ≠ ⊤ := by
  intro hcon
  refine (mem_localisationOpen_iff.{u} g f).1 ?_ hy
  rw [hcon]
  trivial

end

end ComplexAnalytic

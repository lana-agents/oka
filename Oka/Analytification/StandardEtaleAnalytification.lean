/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.StandardEtale

/-!
# The analytification of a standard étale presentation is a distinguished open of a hypersurface

`ComplexAnalytic.etalePresentation` carries **two** extra variables over the base presentation `g`:
one adjoined root of `F`, and one `Y` inverting `G`. Mathlib's
`StandardEtalePair.equivAwayAdjoinRoot` says the `Y` is bookkeeping — `P.Ring` is `(A[X]/f)[1/g]`
— but the presentation does not say so, and every statement anyone wants to quote about the
hypersurface is stated for the **one**-variable presentation `ComplexAnalytic.polyPresentation g`
with `F` appended. This file says the two agree after analytification: the `n + 2`-variable
presentation analytifies to the distinguished open `D(G)` inside the `n + 1`-variable one's
analytification, **over the base**.

## The route, and why it is not a computation

`ComplexAnalytic.etalePresentation` adjoins `X`, inverts `G`, then imposes `F`;
`ComplexAnalytic.localisationIso` wants impose `F`, then invert `G`. Those are different tuples
generating **the same ideal**, and `ComplexAnalytic.analytificationIsoOfPresentationIdealEq` is
exactly the bridge — `ComplexAnalytic.localisationPresentation`'s own docstring says so. So the
whole content of `ComplexAnalytic.presentationIdeal_etalePresentation_eq_localisation` is that the
two `Fin.snoc`s unfold to the same three spans in a different association, and the lattice step is
`a ⊔ (b ⊔ c) = a ⊔ c ⊔ b`.

## Over the base, which is the half worth having

A bare `≅` between two analytifications is worth much less than it looks:
`Oka/Analytification/DistinguishedOpen.lean` says why in terms — *"without that the statement
would only compare two spaces that happen to be isomorphic, and would say nothing about the
immersion"*. So the file does not stop at the isomorphism.
`ComplexAnalytic.etaleAnalytificationIso_hom_comp` says that the isomorphism, followed by the
inclusion of `D(G)` and then by the hypersurface's own projection to `A^an`, **is** the projection
of the étale cover — `ComplexAnalytic.analytificationMap` of `ComplexAnalytic.etalePresHom`. Mind
the direction: a `ComplexAnalytic.PresHom (etalePresentation g F G) g` has ring map `A → A_ét` and
induces the morphism of analytic spaces the other way.

The proof is `ComplexAnalytic.hom_ext_analytification` and four coordinate computations, none of
which is about the étale hypothesis: `ComplexAnalytic.transported` of a
`ComplexAnalytic.PresHom.ofRename` is a coordinate, the projection carries coordinates to
coordinates, and so does the comparison. **Nothing here reads `StandardEtalePair.cond`, `F` or `G`
beyond their names**, which is why the statement holds for every `F` and `G` and not only for a
standard étale pair.

## Main definitions

- `ComplexAnalytic.hypersurfacePresentation`: `Fin.snoc (polyPresentation g) F`, the `n + 1`
  variable presentation of `A[X] ⧸ (F)` — the object every statement about the hypersurface is
  stated for, given a name here because it appears four times in the comparison below.
- `ComplexAnalytic.hypersurfacePresHom`: its structure map `A ⟶ A[X] ⧸ (F)`, as a
  `ComplexAnalytic.PresHom`, by `ComplexAnalytic.PresHom.ofRename` at the inclusion of the old
  variables.
- `ComplexAnalytic.etaleAnalytificationIso`: the isomorphism of the title.

## Main results

- `ComplexAnalytic.presentationIdeal_etalePresentation_eq_localisation`: **the étale presentation
  and the localisation of the hypersurface presentation span the same ideal.**
- `ComplexAnalytic.etaleAnalytificationIso_hom_ofRestrict`: the isomorphism followed by the open
  immersion is the localisation projection, composed with the comparison.
- `ComplexAnalytic.etaleAnalytificationIso_hom_comp`: **the isomorphism is one over `A^an`** — the
  composite down to the base is the projection of the étale cover.

## What is not here

* **Nothing reads `StandardEtalePair.cond`, and the simple-zero lemma is not here.** The step a
  local-isomorphism statement needs is that at a point where `F` vanishes and `G` does not, the
  germ of `F` has `PowerSeries.order (MvPowerSeries.partialEval (Fin.last n) …) = 1` — the
  hypothesis `ComplexAnalytic.bijective_stalkMap_comp_uliftProj` takes. **What is missing is the
  derivative and not the order**, which is computed here already and by three different routes,
  none of them a derivative: `order_partialEval_germ`, `order_partialEval_germ_sq` and
  `order_partialEval_germ_ulift` (`OkaTest/SimpleZeroStalk.lean`) read it *at a coordinate*, by
  `MvPowerSeries.partialEval_X_self` and then `PowerSeries.order_X` —
  `PowerSeries.order_X_pow` in `order_partialEval_germ_sq`, which is the control of that file
  and gets `2`, not `1` — with `order_partialEval_germ_ulift` in exactly the
  `LocalOkaRing.uliftEquiv` shape the hypothesis above asks for; `order_partialEval_skewDiagonal`
  (`OkaTest/GermQuotientDegreeOne.lean`) reads it off a **Weierstrass degree**, through
  `LocalOkaRing.order_partialEval_eq_natDegree` (`Oka/Regular.lean`), which is the only such
  computation under `Oka/`; and `order_partialEval_parabola`, in that same test file, reads it off
  `X ^ 2` through `partialEval_coe_fromPolynomial` directly. **`Oka/` still has no
  partial-derivative operator at all**, and that much of what stood here is true — but the
  conclusion drawn from it, that the hypothesis cannot be reached by anything on hand, does not
  follow and is no longer the case. `MvPowerSeries.order_partialEval_eq_one_iff`
  (`Oka/LocalOkaRing.lean`) says the order condition **is** two coefficient conditions, and
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff` takes them directly — and asks for only
  one of the two, since `ComplexAnalytic.IsCutOutBy.evalHom_eq_zero` makes the vanishing half
  free: what is left is that the coefficient of the last variable in the Taylor expansion of `F`
  at the point is nonzero. **It needs no derivative operator to state or to supply**, and for a
  cutting section that comes from a polynomial it is now a derivative outright:
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_pderiv`
  (`Oka/AnalyticSpace/SimpleZeroPolynomial.lean`) asks that `MvPolynomial.pderiv` of that
  polynomial in the last variable be nonzero at the point, which `F` above is and which is the
  shape a presentation supplies. What is still missing is one step further back, and it is a
  bridge between two *polynomial* rings rather than anything about germs: `StandardEtalePair.cond`
  gives `derivative f * p₁ + f * p₂ = g ^ n` in `R[X]`, one variable over
  `R = MvPolynomial (ULift (Fin n)) ℂ` and with `Polynomial.derivative`, and nothing identifies
  the image of that derivative in `MvPolynomial (ULift (Fin (n+1))) ℂ` with `MvPolynomial.pderiv`
  of the image. Until it does, the `∃ p₁ p₂ n` behind `cond` cannot be turned into the hypothesis
  of the theorem above. **No declaration below attempts either half.**
* **No witness in this file that the open is ever non-empty, and the witness is elsewhere.** The
  statements below are hypothesis-free in `F` and `G`, so none of them can be vacuously
  satisfied — but that says nothing about whether the *objects* are degenerate, and for `F = 1`
  or `G = 0` both sides of `ComplexAnalytic.etaleAnalytificationIso` really are empty.
  `OkaTest/StandardEtaleAnalytification.lean` supplies one pair at which they are not: the line
  `z₁ = 0` in `ℂ²` with `z₀` inverted, where
  `ComplexAnalytic.localisationOpen_hyperLinePres_ne_bot` and
  `ComplexAnalytic.localisationOpen_hyperLinePres_ne_top` make `D(G)` a proper non-empty open and
  `ComplexAnalytic.nonempty_analytification_etalePresentation_hyperLine` carries a point back
  along the isomorphism. **It is a construction rather than a quotation**, and in particular not a
  quotation of taxis #1112's `Pex`, which witnesses a non-closed *image* and says nothing about an
  inhabited `D(G)`.
* **No `IsLocalIso` and no `IsFiniteEtale`.** Beside the missing lemma above,
  `Oka/AnalyticSpace/SimpleZeroStalk.lean` records that its stalk statement says **nothing about
  the underlying map** — *"not even that it is open"* — so the topological field of
  `ComplexAnalytic.AnalyticSpace.IsLocalIso` is a separate absence and not a base-restriction
  question.
* **No finiteness.** `IsFiniteEtale` of the unrestricted morphism is **false**: a standard étale
  algebra inverts `g`, and `Spec` of `(ℂ[X][x] ⧸ (x² - X))[1/x]` over `ℂ` has the punctured line
  for image, which is not closed. `Oka/Analytification/MonicHypersurface.lean`'s `## What is not
  here` carries that, and the finiteness that *is* true — over an open subset of the base on which
  the inversion is vacuous — is a construction and is not here.
* **No comparison with `StandardEtalePair.Ring`.** `ComplexAnalytic.etalePresentedAlgebraEquivRing`
  relates the presented algebra to Mathlib's, and the lifts `hF`, `hG` it needs are hypotheses;
  nothing below takes them, because nothing below needs `F` and `G` to come from a pair.
-/

open MvPolynomial CategoryTheory

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-! ### The hypersurface presentation -/

/-- **The relations of `g` in one more variable, with `F` appended**: the `n + 1`-variable
presentation of `A[X] ⧸ (F)`.

**It is not `ComplexAnalytic.etalePresentation` with a variable dropped**, and the difference is
what the comparison below is a theorem about. Unfolded, `etalePresentation g F G` lists the old
relations, then `X · G - 1`, then `F`; localising *this* tuple at `G` lists the old relations,
then `F`, then `X · G - 1`. **The same three blocks with the last two swapped** — which is why
that comparison is a statement about ideals and not a `rfl`, and why its proof is a `Fin.snoc`
reassociation. (The two are not even over the same number of variables until the localisation is
taken: `etalePresentation`'s own `Fin.snoc`-init is over `n + 2` and this is over `n + 1`.)

**Nothing in the repository is stated for this tuple yet**, which is an argument for naming it
rather than against: `ComplexAnalytic.isFinite_comp_proj_of_monic` and
`ComplexAnalytic.bijective_stalkMap_comp_uliftProj` both take an arbitrary morphism carrying an
`ComplexAnalytic.IsCutOutBy` datum, not a presentation, so a statement about the hypersurface *of
a presented algebra* has nothing to quote. The nearest thing in the tree is
`ComplexAnalytic.localisationPresentation_eq_snoc`, which is `rfl` and is this shape at the one
`F` of the form `X · f - 1`. Named rather than written out because it occurs four times in the
comparison below. -/
def hypersurfacePresentation : Fin (k + 1) → MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  Fin.snoc (polyPresentation.{u} g) F

/-- The ideal of `ComplexAnalytic.hypersurfacePresentation`, split as the old relations and `F`. -/
theorem presentationIdeal_hypersurfacePresentation :
    presentationIdeal.{u} (hypersurfacePresentation.{u} g F) =
      presentationIdeal.{u} (polyPresentation.{u} g) ⊔ Ideal.span {F} :=
  presentationIdeal_snoc.{u} _ _

/-- **The structure map `A ⟶ A[X] ⧸ (F)`, as a morphism of presentations.**

The same shape as `ComplexAnalytic.etalePresHom` one variable down, and for the same reason: the
old relations are literally among the new ones, so `ComplexAnalytic.PresHom.ofRename` at the
inclusion of the old variables costs no commutative algebra. -/
def hypersurfacePresHom : PresHom.{u} (hypersurfacePresentation.{u} g F) g :=
  PresHom.ofRename (localisationIncl.{u} n) (by
    intro j
    rw [presentationIdeal_hypersurfacePresentation.{u} g F]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩))

/-- The tuple `ComplexAnalytic.hypersurfacePresHom` names is the coordinates of the hypersurface
on the old variables — `ComplexAnalytic.PresHom.ofRename` renames a variable to a variable, and
`ComplexAnalytic.quotientToGlobal_mk_X` reads the class of a variable as a coordinate. -/
theorem transported_hypersurfacePresHom (i : ULift.{u} (Fin n)) :
    transported.{u} (hypersurfacePresHom.{u} g F) i =
      analytificationCoord.{u} (hypersurfacePresentation.{u} g F) (localisationIncl.{u} n i) := by
  rw [transported]
  change quotientToGlobal.{u} _ (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} n)
    (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]
  exact quotientToGlobal_mk_X.{u} _ _

/-- The same for `ComplexAnalytic.etalePresHom`, whose rename is the two inclusions composed. -/
theorem transported_etalePresHom (i : ULift.{u} (Fin n)) :
    transported.{u} (etalePresHom.{u} g F G) i =
      analytificationCoord.{u} (etalePresentation.{u} g F G)
        (localisationIncl.{u} (n + 1) (localisationIncl.{u} n i)) := by
  rw [transported]
  change quotientToGlobal.{u} _ (Ideal.Quotient.mk _ (MvPolynomial.rename
    (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]
  exact quotientToGlobal_mk_X.{u} _ _

/-! ### The comparison -/

/-- **The `Y` variable is bookkeeping, at the level of ideals**: adjoining a root of `F` and then
inverting `G` spans what inverting `G` and then imposing `F` does.

Both sides unfold to the relations of `g` in two more variables, together with `Y·G - 1` and `F`;
the two `Fin.snoc`s associate them differently and nothing else happens. The lattice step is
`a ⊔ (b ⊔ c) = a ⊔ c ⊔ b`, closed by `← sup_assoc, sup_right_comm`. -/
theorem presentationIdeal_etalePresentation_eq_localisation :
    presentationIdeal.{u} (etalePresentation.{u} g F G) =
      presentationIdeal.{u}
        (localisationPresentation.{u} (hypersurfacePresentation.{u} g F) G) := by
  rw [presentationIdeal_etalePresentation, localisationPresentation, presentationIdeal_snoc]
  have h : (fun j : Fin (k + 1) ↦ MvPolynomial.rename (localisationIncl.{u} (n + 1))
      ((hypersurfacePresentation.{u} g F : Fin (k + 1) →
        MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) j)) =
      Fin.snoc (polyPresentation.{u} (polyPresentation.{u} g))
        (MvPolynomial.rename (localisationIncl.{u} (n + 1)) F) := by
    funext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp [hypersurfacePresentation, Fin.snoc_last]
    · simp [hypersurfacePresentation, Fin.snoc_castSucc, polyPresentation]
  rw [h, presentationIdeal_snoc, Ideal.span_insert, ← sup_assoc, sup_right_comm]

/-- **The analytification of the standard étale presentation is `D(G)` inside the analytification
of the hypersurface presentation.**

`ComplexAnalytic.analytificationIsoOfPresentationIdealEq` on the ideal identity above, then
`ComplexAnalytic.localisationIso`. Neither factor knows anything about `F` and `G` beyond their
being polynomials. -/
def etaleAnalytificationIso :
    AnalyticSpace.analytification.{u} (etalePresentation.{u} g F G) ≅
      (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).restrict
        (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) :=
  (analytificationIsoOfPresentationIdealEq.{u}
      (presentationIdeal_etalePresentation_eq_localisation.{u} g F G)).trans
    (localisationIso.{u} (hypersurfacePresentation.{u} g F) G)

/-- **The isomorphism followed by the open immersion is the localisation projection**, composed
with the comparison of the two presentations.

This is `ComplexAnalytic.localisationIso_hom_ofRestrict` for the second factor and nothing for the
first, and it is what makes the statement below a computation about coordinates rather than about
an opaque isomorphism. -/
theorem etaleAnalytificationIso_hom_ofRestrict :
    (etaleAnalytificationIso.{u} g F G).hom ≫
        (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) =
      analytificationCompare.{u}
          (presentationIdeal_etalePresentation_eq_localisation.{u} g F G).ge ≫
        localisationProj.{u} (hypersurfacePresentation.{u} g F) G := by
  rw [etaleAnalytificationIso, Iso.trans_hom, Category.assoc, localisationIso_hom_ofRestrict]
  rfl

/-- **The isomorphism is one over `A^an`**: followed by the inclusion of `D(G)` and then by the
hypersurface's projection to the base, it is the projection of the étale cover.

This is the half without which the isomorphism above says only that two spaces happen to be
isomorphic. The proof is `ComplexAnalytic.hom_ext_analytification` and then four coordinate
computations that meet in the middle: both sides send the `i`-th coordinate of `A^an` to the
`i`-th coordinate of the étale analytification, read through the two variable inclusions. -/
theorem etaleAnalytificationIso_hom_comp :
    (etaleAnalytificationIso.{u} g F G).hom ≫
        (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
        analytificationMap.{u} (hypersurfacePresHom.{u} g F) =
      analytificationMap.{u} (etalePresHom.{u} g F G) := by
  refine hom_ext_analytification.{u} g _ _ fun i ↦ ?_
  rw [coordPullback_analytificationMap_comp, transported_etalePresHom]
  rw [← Category.assoc, etaleAnalytificationIso_hom_ofRestrict, Category.assoc, Category.assoc,
    AnalyticSpace.coordPullback_comp, AnalyticSpace.coordPullback_comp,
    coordPullback_analytificationMap_comp, transported_hypersurfacePresHom]
  refine Eq.trans (congrArg (CommRingCat.Hom.hom (AlgebraicGeometry.LocallyRingedSpace.Γ.map
      (analytificationCompare.{u}
        (presentationIdeal_etalePresentation_eq_localisation.{u} g F G).ge).toLRSHom.op))
      (pullbackΓ_localisationProj_analytificationCoord.{u}
        (hypersurfacePresentation.{u} g F) G (localisationIncl.{u} n i))) ?_
  exact (AnalyticSpace.coordPullback_comp _ _ _).symm.trans
    (coordPullback_analytificationCompare_comp _ _)

end

end ComplexAnalytic

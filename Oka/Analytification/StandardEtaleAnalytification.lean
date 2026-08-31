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
- `ComplexAnalytic.eval_pderiv_ne_zero_of_mem`: **the derivative does not vanish at a point of the
  hypersurface off the zero locus of `G`** — `StandardEtalePair.cond`, read at a point of the
  analytification of the hypersurface presentation named above. (That presentation is this file's
  own definition and is not backticked here, since `scripts/guard_coverage.py` reads every
  backticked repository name under this heading as a result this file advertises.)

## What is not here

* **The simple-zero lemma is not here, and until `ComplexAnalytic.eval_pderiv_ne_zero_of_mem`
  below nothing in this development read `StandardEtalePair.cond` at all.** The step a
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
  shape a presentation supplies. **The bridge between the two derivative notions now exists** and is
  `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_pderiv` (`Oka/Analytification/StandardEtale.lean`):
  `MvPolynomial.pderiv` of a lift is a lift of the `Polynomial.derivative`, which is the form the
  question takes here because `ComplexAnalytic.exists_lift_polyPresentedAlgebraEquiv` produces
  `F` as a lift and not as the image of anything. So `StandardEtalePair.cond`'s equation
  `derivative f * p₁ + f * p₂ = g ^ n` in `R[X]`, one variable over
  `R = MvPolynomial (ULift (Fin n)) ℂ`, can be read as an equation about
  `MvPolynomial.pderiv (localisationVar n) F`.

  **One step of that chain is here now and one is not, and neither is the identification.** The
  first — turning the `∃ p₁ p₂ n` behind `cond` into a *non-vanishing* derivative at a point — is
  `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` below, on top of
  `ComplexAnalytic.eval_pderiv_ne_zero` (`Oka/Analytification/StandardEtale.lean`): an evaluation
  argument at a point where `F` vanishes and `G` does not, with no analysis and no geometry in
  it. **The second has been priced and is half-answered, and the half that is left is not the one
  this bullet used to name.** The theorem above is about the hypersurface in `ℂ^(n+1)` and the
  étale presentation is that hypersurface met with `D(G)` in `ℂ^(n+2)`. Restating the transport at
  the derivative hypothesis — the part that was unmeasured — is
  `Oka/AnalyticSpace/OpenBaseProjectionPolynomial.lean` and it is two rewrites, because the
  restriction is absorbed once in the coefficient form
  `ComplexAnalytic.bijective_stalkMap_comp_projRestrict_of_coeff`. **What that does not do is
  reach `D(G)`**, and the reason is a difference of shape rather than of cost:
  `ComplexAnalytic.cylinder` is a preimage from the base, a cylinder `V × ℂ`, while `G` involves
  the fibre variable — `Y·G − 1` is a relation of `ComplexAnalytic.etalePresentation` — so
  `{G ≠ 0}` cuts the *source*. A cylinder it is only when `G` does not involve the last variable.
  **Nothing below produces a `V` from a `G`, and no statement anywhere in this repository
  transports the stalk half across a restriction of the source.** A third absence
  was not named here before and is not the same one: all four stalk theorems take an
  `ComplexAnalytic.IsCutOutBy` datum for **one** cutting section, and
  `ComplexAnalytic.hypersurfacePresentation` has `k + 1` relations. **No declaration below
  attempts either of those two.**
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
* **No `IsLocalIso` and no `IsFiniteEtale`, and the reason has changed.** The topological field
  of `ComplexAnalytic.AnalyticSpace.IsLocalIso` is no longer an absence in general:
  `ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv`
  (`Oka/AnalyticSpace/SimpleZeroTopology.lean`) makes the projection of a polynomial hypersurface
  in `ℂ^(n+1)` a local homeomorphism from exactly the derivative hypothesis
  `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` produces. **What is missing is the same thing that
  is missing on the stalk side**: that theorem is about the hypersurface in `ℂ^(n+1)` and the
  étale presentation is that hypersurface met with `D(G)` in `ℂ^(n+2)`, so it is a
  base-restriction question after all, and one nobody has priced for the topological field —
  `Oka/AnalyticSpace/OpenBaseProjection.lean` transports the stalk field and has no topological
  counterpart.
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

/-! ### `StandardEtalePair.cond` at a point of the hypersurface -/

/-- **The two vanishing hypotheses of `ComplexAnalytic.eval_pderiv_ne_zero` are one hypothesis for
a caller: that the point lies on the hypersurface.**

`ComplexAnalytic.hypersurfacePresentation g F` is `Fin.snoc (polyPresentation g) F`, so a point of
its analytification satisfies the relations of `g` read upstairs *and* `F = 0` — which is exactly
`hx` and `hFx` there. `ComplexAnalytic.eval_eq_zero_of_mem` at `Fin.castSucc j` gives the first
and at `Fin.last k` the second, and the two `Fin.snoc` computations are the whole proof.

**This is the form a consumer holds**, because the hypersurface's analytification is the space
`ComplexAnalytic.etaleAnalytificationIso` compares the étale one to, and `G` is the polynomial
whose distinguished open that isomorphism lands in. What is still missing above this is the
restriction to `D(G)` and the cut-out datum; see this file's `## What is not here`.

The `show … from` is not decoration: `rw [hypersurfacePresentation, Fin.snoc_castSucc]` fails with
*"Failed to rewrite using equation theorems for `hypersurfacePresentation`"*, and naming the
instance of `Fin.snoc_castSucc` is also what keeps an equation lemma for that definition out of
the environment. -/
theorem eval_pderiv_ne_zero_of_mem
    (P : StandardEtalePair (PresentedAlgebra.{u} n k g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g)
    (y : AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F))
    (hGy : MvPolynomial.eval (y.1.1 : ULift.{u} (Fin (n + 1)) → ℂ) G ≠ 0) :
    MvPolynomial.eval (y.1.1 : ULift.{u} (Fin (n + 1)) → ℂ)
      (MvPolynomial.pderiv (localisationVar.{u} n) F) ≠ 0 := by
  refine eval_pderiv_ne_zero.{u} g F G P hF hG _ (fun j ↦ ?_) ?_ hGy
  · have hj := eval_eq_zero_of_mem.{u} (hypersurfacePresentation.{u} g F) y j.castSucc
    rwa [show hypersurfacePresentation.{u} g F j.castSucc = polyPresentation.{u} g j from
      Fin.snoc_castSucc _ _ _] at hj
  · have hl := eval_eq_zero_of_mem.{u} (hypersurfacePresentation.{u} g F) y (Fin.last k)
    rwa [show hypersurfacePresentation.{u} g F (Fin.last k) = F from Fin.snoc_last _ _] at hl

end

end ComplexAnalytic

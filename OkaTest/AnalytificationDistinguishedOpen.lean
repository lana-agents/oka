/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.Nonvanishing

/-!
# Non-vacuity of the distinguished-open comparison

`ComplexAnalytic.localisationIso` is an isomorphism of analytifications, and the repository
already produces those in quantity — `ComplexAnalytic.analytificationIsoOfPresentationIdealEq`
gives one whenever two tuples span the same ideal. Every statement in
`Oka/Analytification/DistinguishedOpen.lean` is also satisfied by `D(f) = ⊤`, the identity
presentation and the identity morphism. The checks below rule both readings out, on the node
`z₀ z₁ = 0` with `f = z₀`, where `A_f = ℂ[z₀, z₁]/(z₀z₁)[1/z₀] ≅ ℂ[z₀, 1/z₀]`.

* **The open subspace is one the development already had, by another route.**
  `localisationOpen_nodePres_eq_nodeAxis` says `D(z₀)` is `nodeAxis 0`, the punctured axis that
  `OkaTest/OpenSubspace.lean` builds by hand with its own openness proof. So the analytification
  of `A_{z₀}` is that punctured axis (`nodeLocIso`), and the statement is about a subset of the
  node that was named before this file existed.

* **It is a proper, nonempty open subset.** `localisationOpen_nodePres_ne_top` — the origin lies
  on the node and `z₀` vanishes there — and `localisationOpen_nodePres_ne_bot`. Without the first
  every theorem in the file would be satisfied by `D(f) = ⊤` and the identity.

* **The localisation is nonempty and the projection is the map it should be.** `nodeLocPoint` is
  the point `(1, 0, 1)` — the point `(1, 0)` of the node together with the inverse of its first
  coordinate — constructed from the defining equations rather than transported across the
  isomorphism, and `base_localisationProj_nodeLocPoint` computes its image as `axisPoint 0`. That
  is `ComplexAnalytic.base_localisationProj` at a point where both sides are known independently.

* **The image really does miss the zeros of `f`.**
  `nodeOrigin_notMem_range_base_localisationProj`: the origin of the node is not in the image of
  the projection, which is the containment `ComplexAnalytic.range_base_localisationProj_subset`
  seen at a point that is genuinely outside.

* **The seam behind `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` is recorded rather than
  recalled.** The one-line `example` at the top of the file is the product that motivates that
  declaration; the same expression written at the raw `Γ.map` spelling fails instance search, and
  its docstring quotes the error. A failing elaboration cannot itself be a test, so what is
  recorded is the half that passes.

**What is not checked here.** Nothing says the analytic structure on the punctured axis is the
one a reader would expect beyond its being a restriction of the node's, and nothing here is a
statement about a presentation in which the number of *equations* also matters — the node has
one, and `ComplexAnalytic.localisationPresentation` adds exactly one more.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-! ### The seam `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` exists for -/

/-- **A global section of `X` times a section pulled back along `φ : X ⟶ Y` elaborates**, which
is the whole reason `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` is a declaration rather than a
spelling. Written out as `a * (LocallyRingedSpace.Γ.map φ.toLRSHom.op).hom s` the same expression
is rejected with `failed to synthesize instance of type class HMul ↑(X.presheaf.obj (op ⊤))
↑(LocallyRingedSpace.Γ.obj (op X.toLocallyRingedSpace)) ?m` — the two spellings are definitionally
equal and instance search does not cross the difference. If that ever stops being so, this line
becomes redundant rather than wrong; while it holds, it is what keeps the account in that
declaration's docstring a measurement. -/
example {X Y : AnalyticSpace.{u}} (φ : X ⟶ Y) (a : X.presheaf.obj (op ⊤))
    (s : Y.presheaf.obj (op ⊤)) : X.presheaf.obj (op ⊤) := a * φ.pullbackΓ s

/-! ### The node, presented -/

/-- The node as a presented algebra: `ℂ[z₀, z₁] ⧸ (z₀z₁)`. -/
abbrev nodePres : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ := fun _ ↦ nodePoly.{u}

/-- The polynomial `z₀`, the one being inverted. -/
abbrev nodeX : MvPolynomial (ULift.{u} (Fin 2)) ℂ := MvPolynomial.X (ULift.up 0)

/-- **The analytification of this presentation is the node**, so nothing below is a statement
about a space built for the occasion. -/
example : AnalyticSpace.analytification.{u} nodePres.{u} = AnalyticSpace.node.{u} := rfl

/-- The section attached to a variable is the corresponding coordinate function of the node. -/
theorem polyToGlobal_nodePres_X (j : ULift.{u} (Fin 2)) :
    polyToGlobal.{u} nodePres.{u} (MvPolynomial.X j) = nodeCoord.{u} j :=
  polyToGlobal_X.{u} nodePres.{u} j

/-! ### `D(z₀)` is the punctured axis -/

/-- **The distinguished open of the node along `z₀` is the punctured first axis.**

`nodeAxis` is built by hand in `OkaTest/OpenSubspace.lean`; this says the open subspace that
carries the analytification of `A_{z₀}` is that one. -/
theorem localisationOpen_nodePres_eq_nodeAxis :
    localisationOpen.{u} nodePres.{u} nodeX.{u} = nodeAxis.{u} (ULift.up 0) :=
  (congrArg (AnalyticSpace.node.{u}).nonvanishing (polyToGlobal_nodePres_X.{u} (ULift.up 0))).trans
    (nonvanishing_nodeCoord_eq_nodeAxis.{u} (ULift.up 0))

/-- **It is a proper open subset**: the origin is a point of the node at which `z₀` vanishes. This
is the statement that separates `ComplexAnalytic.localisationIso` from the identity. -/
theorem localisationOpen_nodePres_ne_top : localisationOpen.{u} nodePres.{u} nodeX.{u} ≠ ⊤ :=
  localisationOpen_ne_top.{u} nodePres.{u} nodeX.{u} nodeOrigin.{u} (MvPolynomial.eval_X _)

/-- **It is not empty either**, so the localisation is not the empty space. -/
theorem localisationOpen_nodePres_ne_bot : localisationOpen.{u} nodePres.{u} nodeX.{u} ≠ ⊥ := by
  intro hcon
  have hmem : axisPoint.{u} (ULift.up 0) ∈ localisationOpen.{u} nodePres.{u} nodeX.{u} :=
    (mem_localisationOpen_iff.{u} nodePres.{u} nodeX.{u}).2 (by
      rw [MvPolynomial.eval_X, axisPoint_coord, if_pos rfl]
      exact one_ne_zero)
  rw [hcon] at hmem
  exact hmem

/-- **The analytification of `ℂ[z₀, z₁]/(z₀z₁)[1/z₀]` is the punctured first axis of the node**,
which is `ComplexAnalytic.localisationIso` composed with the equality of open subsets above. -/
def nodeLocIso :
    AnalyticSpace.analytification.{u} (localisationPresentation.{u} nodePres.{u} nodeX.{u}) ≅
      AnalyticSpace.node.{u}.restrict (nodeAxis.{u} (ULift.up 0)) :=
  localisationIso.{u} nodePres.{u} nodeX.{u} ≪≫
    eqToIso (congrArg AnalyticSpace.node.{u}.restrict localisationOpen_nodePres_eq_nodeAxis.{u})

/-! ### A point, and where the projection sends it -/

/-- The point `(1, 0, 1)` of the localisation: the point `(1, 0)` of the node together with the
inverse of its first coordinate. Built from the defining equations of
`ComplexAnalytic.localisationPresentation`, not transported across `nodeLocIso`. -/
def nodeLocPoint : AnalyticSpace.analytification.{u}
    (localisationPresentation.{u} nodePres.{u} nodeX.{u}) := by
  classical
  refine ⟨⟨fun l ↦ if l.down = 1 then 0 else 1, trivial⟩,
    (mem_zeroLocus_polySection_iff _ _).2 (Fin.lastCases ?_ (fun j ↦ ?_))⟩
  · rw [localisationPresentation_last]
    simp [localisationVar, localisationIncl]
  · rw [localisationPresentation_castSucc]
    simp [localisationIncl, nodePoly]

/-- **The projection sends `(1, 0, 1)` to `(1, 0)`**: `ComplexAnalytic.base_localisationProj` at a
point where the image is a point the development already had a name for. -/
theorem base_localisationProj_nodeLocPoint :
    (localisationProj.{u} nodePres.{u} nodeX.{u}).toLRSHom.base nodeLocPoint.{u} =
      axisPoint.{u} (ULift.up 0) := by
  refine Subtype.ext (Subtype.ext (funext fun l ↦ ?_))
  rw [base_localisationProj, axisPoint_coord]
  rcases l with ⟨l⟩
  fin_cases l <;> simp [nodeLocPoint, localisationIncl]

/-- **The origin of the node is not in the image of the projection**, which is what
`ComplexAnalytic.range_base_localisationProj_subset` says at a point genuinely outside `D(z₀)`.
On a space with zero divisors this is not automatic: the origin is a limit of points of the
punctured axis in the ambient `ℂ²` only along the *other* axis. -/
theorem nodeOrigin_notMem_range_base_localisationProj :
    nodeOrigin.{u} ∉
      Set.range (localisationProj.{u} nodePres.{u} nodeX.{u}).toLRSHom.base := fun h ↦
  (mem_localisationOpen_iff.{u} nodePres.{u} nodeX.{u}).1
    (range_base_localisationProj_subset.{u} nodePres.{u} nodeX.{u} h) (MvPolynomial.eval_X _)

end

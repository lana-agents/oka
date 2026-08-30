/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CoverIndependence
import Oka.Analytification.LocalisationComposite

/-!
# Refining one member of a cover by distinguished opens

`Oka/Analytification/CoverIndependence.lean` matches two cover data member for member, first at a
shared index type and then along an `Equiv`. In both, the morphism `σ` on indices and the family
`ψ` of member morphisms are **given by the caller**. A *refinement* is the first case where they
are not, and this file is the smallest such case: the refining members are distinguished opens
`D(f_a)` of **one fixed member** `A`.

## What this file measures, and it corrects an estimate the board had been planning against

`Oka/Analytification/CoverIndependence.lean` says of refinement that it *"is where
`ComplexAnalytic.coverMap`'s `σ` and `ψ` stop being given and have to be built"*, with the
implication that building them is the work. **The second half of that is wrong, and this file is
the measurement.** For a distinguished-open refinement `ψ` is `ComplexAnalytic.localisationHom`
and nothing else — one declaration that has been on `master` since taxis #1006, whose direction
convention (*"from the localisation to `A`"*) is already the one `ComplexAnalytic.coverMap` wants.
`σ` is constant. Neither costs a line.

**The work is the refined cover *datum*.** `ComplexAnalytic.coverMap` takes both sides as complete
data, and a refinement supplies only the members. What has to be built is the polynomial cutting
each overlap out, the isomorphism of the two descriptions of it, and the three laws. This file
builds the first two and one law; the other two are geometric and are not here, for a reason
measured below rather than asserted.

## Why one fixed member is the right first case, and it is not a vacuous one

With `σ` constant every overlap is a *same-member* overlap: `D(f_a) ∩ D(f_b)` inside `D(f_a)`. That
is exactly the configuration `Oka/Analytification/LocalisationComposite.lean` was written for —
localising twice is localising once, at the product — so the overlap has a second description as a
single localisation and the glue isomorphism is that description taken at both ends. **Nothing in
the same-member case needs the original cover's own `glue`**, which is what makes it separable
from the cross-member case rather than merely smaller than it.

It is not vacuous: the refined data is a genuine cover datum shape over any index type `K` and any
family of polynomials, and `ComplexAnalytic.refineGlue_comp` below is a statement with content —
it is the `trans_comp` coherence, and it is the reason the glue isomorphism is the *right* one
rather than merely one of the right type.

## The shape of the two proofs

Both laws below go through the single localisation and not through the double one.
`ComplexAnalytic.refineMulIso` is `ComplexAnalytic.localisationPresentationIsoMul` with its source
recognised as `ComplexAnalytic.coverOverlap` of the refined data — which is `rfl`, and is why
`ComplexAnalytic.refineObj` and `ComplexAnalytic.refinePoly` are `abbrev` and not `def`. As `def`s
the unfolding is not available at `instances` transparency and the coherence proof below fails
with an application type mismatch on a goal that displays correctly.

`ComplexAnalytic.refineGlue_symm` is where the `Iso`s are compared, and `congr 1` is not the way:
it forces the `Category Presentation` instance open on a three-term `Iso.trans` and exhausts the
heartbeat budget, which is the pathology `Oka/Analytification/AffineCover.lean`'s own module
docstring describes at length. Rewriting to a common associated form and finishing with
`ComplexAnalytic.eqToIso_symm'` avoids ever unifying two composites.

`ComplexAnalytic.refineGlue_analytification_comp` meets the *other* recorded pathology:
`rw [← Functor.map_comp]` fails on a goal that displays as if it should apply, because the objects
carry unreduced `ComplexAnalytic.refineObj` projections —
`Oka/CategoryTheory/GlueData.lean`'s module docstring predicts exactly this. The cure here is not
the `mapIso` one `Oka/Analytification/CoverIndependence.lean` records: it is to build the equation
with `congrArg` and simplify the *hypothesis*, which is well-typed by construction, then discharge
the goal with `exact` so that the ascriptions `analytificationFunctor.obj ⟨n, k, g⟩` and
`AnalyticSpace.analytification g` are unified at default transparency. `simpa … using` does **not**
close it, and the difference between the two is the whole of that step.

## Main definitions

- `ComplexAnalytic.refineObj`: **the refined member**, the distinguished open `D(f_a)` of the fixed
  member, as an object of `ComplexAnalytic.Presentation`.
- `ComplexAnalytic.refinePoly`: **the polynomial cutting the overlap out of the `a`-th refined
  member** — the refining polynomial of the `b`-th, read in one more variable.
- `ComplexAnalytic.refineMul`: the single localisation at the product that both descriptions of the
  overlap reduce to.
- `ComplexAnalytic.refineMulIso` and `ComplexAnalytic.refineGlue`: **the overlap's two descriptions
  identified**, and the glue isomorphism of the refined data built out of it.

## Main results

- `ComplexAnalytic.refineGlue_symm`: **the refined glue datum is symmetric**, which is the
  `hsymm` a cover datum asks for. (Named without a citation on purpose:
  `scripts/guard_coverage.py` reads every backticked repository name under this heading as a
  result *this* file advertises, and the declaration that asks for `hsymm` is another file's.)
- `ComplexAnalytic.refineGlue_comp`: **the coherence triangle** — the glue isomorphism commutes
  with the two structure maps down to the fixed member. This is the content of the file.
- `ComplexAnalytic.refineGlue_analytification_comp`: the same, analytified, which is the form the
  two geometric laws would consume.

## What is not here

* **No `hrange` and no `hcocycle`, so no cover datum and no
  `ComplexAnalytic.coverAnalytification` of the refinement, and therefore no
  `ComplexAnalytic.coverMap`.** The two laws left are geometric — statements about images of
  triple overlaps — and `ComplexAnalytic.refineGlue_analytification_comp` is the input they need
  rather than the statement they are.

  **The obstruction is measured and it is one missing lemma, not a general difficulty.** Both laws
  need the refined overlap to be the *preimage* of the refining open along the projection:
  `ComplexAnalytic.localisationOpen (ComplexAnalytic.localisationPresentation g f) (rename …  f')`
  should be the pullback of `ComplexAnalytic.localisationOpen g f'` along
  `ComplexAnalytic.localisationProj g f`. **No such statement exists.**
  `Oka/Analytification/DistinguishedOpen.lean` carries
  `ComplexAnalytic.mem_localisationOpen_iff`, `ComplexAnalytic.localisationOpen_ne_top` and
  `ComplexAnalytic.localisationOpen_mul`, and nothing relating a `localisationOpen` to a preimage
  along anything — checked, not assumed. That lemma is the next thing to build and it belongs in
  that file, not this one.
* **No cross-member refinement.** `σ` is constant here, so no overlap of the refined data ever
  meets two different members of the original. The cross-member case has to transport the original
  `glue` through two localisations, it is the only part that uses the original data's own glue
  isomorphism at all, and **nothing in this file is evidence about its size** — the whole reason
  the same-member case closes cheaply is that `Oka/Analytification/LocalisationComposite.lean`
  had already been written for exactly this configuration.
* **No claim that the induced morphism is an isomorphism.** A refinement gives a morphism in one
  direction; both increments in `Oka/Analytification/CoverIndependence.lean` had both directions
  handed to them by the caller, so neither is evidence here. Nothing below asserts either
  direction, since there is no `ComplexAnalytic.coverMap` yet to assert it of.
* **No scheme, and no `admissible`.** As in the two files this one sits beside, and for the same
  reason: there is no `AlgebraicGeometry.Scheme` in this line of files, and `admissible` is a
  notion this repository does not have.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {K : Type u} {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (fam : K → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The refined members and their overlaps -/

/-- **The `a`-th refined member**: the distinguished open `D(fam a)` of the fixed member, presented
by `ComplexAnalytic.localisationPresentation`.

An `abbrev` rather than a `def` on purpose. `ComplexAnalytic.coverOverlap` of the refined data has
to reduce to a double localisation for `ComplexAnalytic.refineMulIso` to typecheck, and that
reduction has to be available at `instances` transparency — as a `def` the coherence proof below
fails with an application type mismatch against a goal that displays correctly. -/
abbrev refineObj (a : K) : Presentation.{u} :=
  ⟨n + 1, k + 1, localisationPresentation.{u} g (fam a)⟩

/-- **The polynomial cutting the `b`-th overlap out of the `a`-th refined member.**

Inside `D(fam a)` the locus where `fam b` does not vanish is cut out by `fam b` read in the one
extra variable, which is `MvPolynomial.rename` along `ComplexAnalytic.localisationIncl` — the same
renaming `ComplexAnalytic.localisationPresentation` uses on the old equations. -/
abbrev refinePoly (a : K) (b : K) :
    MvPolynomial (ULift.{u} (Fin (refineObj.{u} g fam a).n)) ℂ :=
  MvPolynomial.rename (localisationIncl.{u} n) (fam b)

/-- **The single localisation both descriptions of the overlap reduce to**, at the product of the
two refining polynomials. -/
abbrev refineMul (a b : K) : Presentation.{u} :=
  ⟨n + 1, k + 1, localisationPresentation.{u} g (fam b * fam a)⟩

/-- **The overlap, described twice.**

Localising at `fam a` and then at `fam b` is localising at `fam b * fam a`, which is
`ComplexAnalytic.localisationPresentationIsoMul`. The content of this definition is that its source
*is* `ComplexAnalytic.coverOverlap` of the refined data — by `rfl`, and that is what the `abbrev`s
above buy. -/
def refineMulIso (a b : K) :
    coverOverlap.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b ≅
      refineMul.{u} g fam a b :=
  localisationPresentationIsoMul.{u} g (fam a) (fam b)

/-- **The product is symmetric**, and this is the only place the two orders are compared. -/
theorem refineMul_comm (a b : K) : refineMul.{u} g fam a b = refineMul.{u} g fam b a := by
  rw [refineMul, refineMul, mul_comm]

/-- **The glue isomorphism of the refined data**: each side's description of the overlap, carried
to the single localisation at the product, and the two products identified by `mul_comm`.

This is the `glue` a cover datum asks for, and it is built rather than given — which is the
difference between a refinement and the two increments of
`Oka/Analytification/CoverIndependence.lean`. -/
def refineGlue (a b : K) :
    coverOverlap.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) a b ≅
      coverOverlap.{u} (refineObj.{u} g fam) (refinePoly.{u} g fam) b a :=
  refineMulIso.{u} g fam a b ≪≫ eqToIso (refineMul_comm.{u} g fam a b) ≪≫
    (refineMulIso.{u} g fam b a).symm

/-! ### The two laws that are algebraic -/

/-- **The inverse of a transport is the transport of the inverse**, for objects of
`ComplexAnalytic.Presentation`.

Mathlib has `CategoryTheory.eqToIso.inv` for the underlying morphism; this is the `Iso`-level
statement, and it exists so that `ComplexAnalytic.refineGlue_symm` can be a chain of rewrites. It
is stated here rather than in general because it is one line either way and nothing else needs
it. -/
theorem eqToIso_symm' {X Y : Presentation.{u}} (h : X = Y) :
    (eqToIso h).symm = eqToIso h.symm :=
  Iso.ext (eqToIso.inv h)

/-- **The refined glue datum is symmetric**, which is `hsymm` for this data.

Everything cancels once both sides are associated the same way: the two `refineMulIso` factors
appear in opposite orders on the two sides and the `eqToIso` is its own opposite by
`ComplexAnalytic.eqToIso_symm'`. **`congr 1` is not available here** — it forces the
`Category Presentation` instance open on a three-term `Iso.trans` and runs the heartbeat budget
out, which is the cost `Oka/Analytification/AffineCover.lean`'s module docstring is about. -/
theorem refineGlue_symm (a b : K) :
    refineGlue.{u} g fam b a = (refineGlue.{u} g fam a b).symm := by
  rw [refineGlue, refineGlue, Iso.trans_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, eqToIso_symm']

/-- **A transport along an equality of the localising polynomial cancels against the structure
map.**

`subst` is what does it, and it is available because `f` and `f'` are bound here where in
`ComplexAnalytic.refineGlue_comp` they are `fam b * fam a` and `fam a * fam b` and the transport
sits inside `ComplexAnalytic.localisationPresentation`'s argument. This is the same manoeuvre
`Oka/Analytification/CoverIndependence.lean`'s second increment needed and found in Mathlib as
`CategoryTheory.dcongr_arg`; here the family is `ComplexAnalytic.localisationHom` at a varying
polynomial rather than at a varying index, so `dcongr_arg` does not apply and the one-line
`subst` does. -/
theorem eqToHom_localisationHom {f f' : MvPolynomial (ULift.{u} (Fin n)) ℂ} (h : f = f') :
    eqToHom (show (⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ : Presentation.{u}) =
        ⟨n + 1, k + 1, localisationPresentation.{u} g f'⟩ by rw [h]) ≫
      localisationHom.{u} g f' = localisationHom.{u} g f := by
  subst h; simp

/-- **The coherence triangle, and it is the content of this file.**

Going from the `a`-th description of the overlap to the `b`-th and then down to the fixed member
is going down directly. Without it the glue isomorphism would be an isomorphism of the right
*type* with no recorded relation to the two members it is supposed to identify parts of, which is
the same distinction `ComplexAnalytic.localisationPresentationIsoMul_hom_comp` exists to make one
level down — and that lemma, applied twice at the two orders, is the whole proof. -/
theorem refineGlue_comp (a b : K) :
    (refineGlue.{u} g fam a b).hom ≫
        localisationHom.{u} (refineObj.{u} g fam b).g (refinePoly.{u} g fam b a) ≫
          localisationHom.{u} g (fam b) =
      localisationHom.{u} (refineObj.{u} g fam a).g (refinePoly.{u} g fam a b) ≫
        localisationHom.{u} g (fam a) := by
  rw [← localisationPresentationIsoMul_hom_comp.{u} g (fam a) (fam b),
    ← localisationPresentationIsoMul_hom_comp.{u} g (fam b) (fam a), refineGlue]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, Iso.symm_hom]
  rw [show (refineMulIso.{u} g fam b a).inv ≫ (localisationPresentationIsoMul.{u} g (fam b)
      (fam a)).hom ≫ localisationHom.{u} g (fam a * fam b) =
    localisationHom.{u} g (fam a * fam b) from (refineMulIso.{u} g fam b a).inv_hom_id_assoc _]
  exact congrArg _ (eqToHom_localisationHom.{u} g (mul_comm (fam b) (fam a)))

/-- **The coherence triangle, analytified**, with the structure maps read as
`ComplexAnalytic.localisationProj`. This is the form the two geometric laws would consume, and the
reason it is stated here rather than where they are is that it needs nothing geometric.

**`rw [← Functor.map_comp]` does not close this**, on a goal that displays as if it should: the
objects carry unreduced `ComplexAnalytic.refineObj` projections, which is the pathology
`Oka/CategoryTheory/GlueData.lean`'s module docstring predicts. Building the equation with
`congrArg` and simplifying the *hypothesis* avoids it, because the hypothesis is well-typed by
construction. The final step must be `exact` and not `simpa … using`: what is left is the
ascription `analytificationFunctor.obj ⟨n, k, g⟩` against `AnalyticSpace.analytification g`, which
is a definitional unfolding `simp` will not perform and `exact` will. -/
theorem refineGlue_analytification_comp (a b : K) :
    analytificationFunctor.{u}.map (refineGlue.{u} g fam a b).hom ≫
        localisationProj.{u} (refineObj.{u} g fam b).g (refinePoly.{u} g fam b a) ≫
          localisationProj.{u} g (fam b) =
      localisationProj.{u} (refineObj.{u} g fam a).g (refinePoly.{u} g fam a b) ≫
        localisationProj.{u} g (fam a) := by
  have h := congrArg (analytificationFunctor.{u}.map) (refineGlue_comp.{u} g fam a b)
  simp only [Functor.map_comp, analytificationFunctor_map_localisationPresHom] at h
  exact h

end

end ComplexAnalytic

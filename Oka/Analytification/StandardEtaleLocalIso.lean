/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.HypersurfaceFinite
import Oka.AnalyticSpace.SimpleZeroTopology

/-!
# A standard étale morphism over affine space analytifies to a local isomorphism

`Oka/AnalyticSpace/SimpleZeroTopology.lean` proves that an open subspace of a hypersurface in
`ℂ^(n+1)`, on which a polynomial cutting it out has non-vanishing derivative in the last
variable, projects to `ℂ^n` as a local isomorphism of complex analytic spaces
(`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`).
`Oka/Analytification/StandardEtaleAnalytification.lean` proves that the analytification of a
standard étale presentation **is** such an open subspace — the distinguished open `D(G)` of the
hypersurface `{F = 0}` — and that `StandardEtalePair.cond` supplies exactly that derivative
hypothesis there (`ComplexAnalytic.eval_pderiv_ne_zero_of_mem`). This file joins the two, and it
is the first module to import both subtrees.

## The base is `ℂ^n`, and that is the statement rather than a limitation of the proof

`ComplexAnalytic.hypersurfacePresentation g F` is `Fin.snoc (polyPresentation g) F`: the `k`
relations of the base algebra read upstairs, and `F`. The theorem above takes a cut-out datum for
**one** section, and `Oka/Analytification/StandardEtaleAnalytification.lean` recorded the
mismatch as a missing datum for `k + 1` relations against one section.

**It is not a missing datum.** The conclusion of that theorem is about the projection to `ℂ^n`,
and for `k ≥ 1` it is *false*: a hypersurface lying over a proper closed `X^an ⊆ ℂ^n` does not
project to `ℂ^n` as a local isomorphism, since its image is contained in `X^an`. The `k + 1`
versus one is the signature of a statement whose base is the whole of `ℂ^n`, i.e. `k = 0`, and
that is what everything below is stated at. A statement over a general base is a different
theorem and needs an implicit function theorem relative to `X^an`, which
`Oka/Analysis/Calculus/Implicit.lean` does not have.

At `k = 0` the two families agree on the nose: `ComplexAnalytic.hypersurfacePresentation g F` is
a `Fin 1`-family whose only entry is `F`, and
`ComplexAnalytic.section_hypersurfacePresentation_empty` is the one line that says so. The datum
itself is `ComplexAnalytic.isCutOutBy_analytificationInclHom`
(`Oka/Analytification/UniversalProperty.lean`), which holds for every `k` and needed no new
general lemma: `ComplexAnalytic.IsCutOutBy.iso_comp` was already in the tree.

## What the last theorem's target is, and why it is `ℂ^n`

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` concludes about
`ComplexAnalytic.analytificationMap` of the étale structure map **followed by the inclusion of
the base's analytification into `ℂ^n`**, and not about the structure map alone. At `k = 0` the
inclusion `ComplexAnalytic.analytificationInclHom g` is an isomorphism — the zero locus of the
empty family is everything — but **nothing in this repository says so**; see `## What is not
here`. Composing with it is therefore not a weakening but a choice of spelling: the target is the
`ℂ^n` that `ComplexAnalytic.AnalyticSpace.proj` maps to, named as itself.

The step that makes that composite the right one is
`ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp`
(`Oka/Analytification/HypersurfaceFinite.lean`), which says the analytified structure map
followed by the base's inclusion is the hypersurface's own inclusion followed by the projection.
It holds for every `k` and is the only thing this file takes from that module.

## `localisationVar` and `Fin.last`

`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` differentiates at
`ULift.up (Fin.last n)` and `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` produces a derivative at
`ComplexAnalytic.localisationVar n`. **They are the same term** —
`Oka/Analytification/DistinguishedOpen.lean` defines the second as the first — so the statements
below are written with `ComplexAnalytic.localisationVar` throughout and no bridge lemma appears
anywhere. A reader comparing the two signatures will otherwise go looking for one.

## Main results

- `ComplexAnalytic.section_hypersurfacePresentation_empty`: over an empty base presentation, the
  polynomials cutting the hypersurface out of `ℂ^(n+1)` are the one-element family `![F]`.
- `ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`: **so the hypersurface's
  analytification carries a cut-out datum for a single section**, which is what every theorem on
  this line asks for.
- `ComplexAnalytic.isLocalIso_hypersurface_ofRestrict_comp_proj`: **`D(G)` inside the
  hypersurface `{F = 0} ⊆ ℂ^(n+1)` projects to `ℂ^n` as a local isomorphism**, given that the
  derivative of `F` in the last variable does not vanish on `D(G)`.
- `ComplexAnalytic.isLocalIso_hypersurface_of_standardEtale`: the same with the derivative
  hypothesis discharged from `StandardEtalePair.cond`.
- `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`: **the analytification of a
  standard étale morphism over `ℂ^n` is a local isomorphism onto `ℂ^n`.**

## What is not here

* **No `IsFiniteEtale`, and this file moves the finiteness field nowhere.** For the *unrestricted*
  standard étale morphism finiteness is **false** — inverting `G` destroys it, and
  `Oka/Analytification/MonicHypersurface.lean`'s `## What is not here` carries the counterexample
  in terms. So the two fields of `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` are not two halves
  of one job here: one of them is a theorem and the other is a false statement waiting for a base
  restriction that nothing below constructs.
* **Nothing at `k ≥ 1`**, for the reason at the top of this docstring: not a gap but a different
  statement.
* **Nothing saying `ComplexAnalytic.analytificationInclHom g` is an isomorphism when `g` is the
  empty family**, and the price is measured rather than guessed.
  `ComplexAnalytic.IsCutOutBy.uniqueIso` against
  `ComplexAnalytic.isCutOutBy_id_restrict_top` gives the isomorphism of *locally ringed* spaces,
  and `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful but not full, so the
  inverse would still have to be shown `ℂ`-linear before the conclusion could be moved to
  `ComplexAnalytic.AnalyticSpace.analytification g`. **It is not built here because nothing
  consumes it**: the last theorem below is a complete statement with `ℂ^n` as its target, and the
  thing that would want the other spelling is the assembly of the Riemann existence theorem, not
  this file.
* **No `StandardEtalePair` is constructed anywhere.** The two theorems taking one inherit that
  hypothesis from `ComplexAnalytic.eval_pderiv_ne_zero_of_mem`, which has been on `master`
  without a witness since it landed, and this file adds no new unwitnessed hypothesis.
  `OkaTest/StandardEtaleAnalytification.lean` exercises the *derivative* form instead, on the
  line `z₁ = 0` in `ℂ²` with `z₀` inverted, where the derivative is `1` and no pair is needed —
  so the theorems below are not vacuous, but the `cond` route through them is checked by nothing.
* **Nothing about the image.** A local isomorphism need not be surjective and this one is not:
  the witness in the test library misses the origin. No statement below says anything about the
  image, about fibres, or about degree.
* **Nothing about a general étale morphism.** Every étale morphism of schemes is Zariski-locally
  standard étale; gluing the statement below over such a cover is a separate construction and
  nothing here starts it.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace ComplexAnalytic

noncomputable section

variable {n : ℕ} (g : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-! ### The cut-out datum for a single section -/

/-- **Over an empty base presentation the hypersurface is cut out of `ℂ^(n+1)` by `F` alone.**

`ComplexAnalytic.hypersurfacePresentation g F` is `Fin.snoc (polyPresentation g) F`, so at
`k = 0` it is a `Fin 1`-family and its only index is `Fin.last 0`. The `change` names that index —
`fin_cases` leaves the goal at `(0 : Fin 1)` and `Fin.snoc_last` is stated at `Fin.last`, which
is the same element and not the same term.

**`change` and not `show`, and `lake build --wfail` is what says so.** Mathlib's
`linter.style.show` rejects a `show` that *alters* the goal — which is the whole point of this
one — and the build turns that warning into a failure. The two tactics do the same thing here.

The `show … from Fin.snoc_last _ _` inside the `rw` is a different `show`, is a term and not a
tactic, and is untouched by that linter. It is the shape
`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` uses one file over, **and here it is a choice rather
than a necessity**. This paragraph said it was forced, for the sibling's reason: that a bare
`rw [hypersurfacePresentation, Fin.snoc_last]` fails with *"Failed to rewrite using equation
theorems for `hypersurfacePresentation`"*, and that naming the instance is what keeps an equation
lemma for that definition out of the environment. **Neither holds at this rewrite**, measured in
tree: the bare form compiles, and `scripts/DumpOkaDecls.lean`'s output is byte-identical either
way, so no equation lemma enters the environment on either spelling. The sibling states its
version of the reason at `Fin.snoc_castSucc` under `rwa … at`, which is a different rewrite and
is untouched here; the named form is kept for consistency with it and for nothing else. -/
theorem section_hypersurfacePresentation_empty :
    (fun j ↦ (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))
        (hypersurfacePresentation.{u} g F j) :
      (AnalyticSpace.complexAffineSpace.{u} (n + 1)).presheaf.obj (op ⊤))) =
      ![OkaRing.ofMvPolynomial ⊤ F] := by
  funext j
  fin_cases j
  change OkaRing.ofMvPolynomial ⊤ (hypersurfacePresentation.{u} g F (Fin.last 0)) = _
  rw [show hypersurfacePresentation.{u} g F (Fin.last 0) = F from Fin.snoc_last _ _]
  rfl

/-- **The hypersurface's analytification is cut out of `ℂ^(n+1)` by the single section `F`.**

`ComplexAnalytic.isCutOutBy_analytificationInclHom` at the hypersurface presentation, rewritten
along the family identity above. This is the datum
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` takes, and supplying it is the whole
of what was missing on this line. -/
theorem isCutOutBy_analytificationInclHom_hypersurface :
    IsCutOutBy (analytificationInclHom.{u} (hypersurfacePresentation.{u} g F)).toLRSHom
      ![OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) F] :=
  section_hypersurfacePresentation_empty.{u} g F ▸
    isCutOutBy_analytificationInclHom.{u} (hypersurfacePresentation.{u} g F)

/-! ### The local isomorphism -/

/-- **The distinguished open `D(G)` of the hypersurface `{F = 0} ⊆ ℂ^(n+1)` projects to `ℂ^n` as
a local isomorphism**, provided the derivative of `F` in the last variable does not vanish at any
of its points.

Nothing here reads `G` beyond its naming the open subset: the hypothesis is asked at the points
of `D(G)` and at no others, which is exactly the shape
`ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv` was stated in. -/
theorem isLocalIso_hypersurface_ofRestrict_comp_proj
    (hlin : ∀ y : (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).restrict
        (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G),
      MvPolynomial.eval (y.1.1.1 : ULift.{u} (Fin (n + 1)) → ℂ)
        (MvPolynomial.pderiv (localisationVar.{u} n) F) ≠ 0) :
    AnalyticSpace.IsLocalIso
      ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
        analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
          AnalyticSpace.proj.{u} n) :=
  isLocalIso_ofRestrict_comp_proj_of_pderiv
    (isCutOutBy_analytificationInclHom_hypersurface.{u} g F) _ hlin

/-- **The same, with the derivative hypothesis discharged from `StandardEtalePair.cond`.**

`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` turns `cond` into the non-vanishing of the
derivative at a point of the hypersurface off the zero locus of `G`, and a point of the
restriction is a point of the hypersurface together with the proof that `G` does not vanish
there — `ComplexAnalytic.mem_localisationOpen_iff` read forwards. So the two fit with nothing in
between. -/
theorem isLocalIso_hypersurface_of_standardEtale
    (P : StandardEtalePair (PresentedAlgebra.{u} n 0 g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    AnalyticSpace.IsLocalIso
      ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
          (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
        analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
          AnalyticSpace.proj.{u} n) :=
  isLocalIso_hypersurface_ofRestrict_comp_proj.{u} g F G fun y ↦
    eval_pderiv_ne_zero_of_mem.{u} g F G P hF hG y.1
      ((mem_localisationOpen_iff.{u} _ _).1 y.2)

/-- **The analytification of a standard étale morphism over `ℂ^n` is a local isomorphism onto
`ℂ^n`.**

The statement the whole of this line was for, at the one base the theorems it rests on are about.
Read the composite as a whole: `ComplexAnalytic.analytificationMap` of
`ComplexAnalytic.etalePresHom` lands in the base's analytification, and
`ComplexAnalytic.analytificationInclHom` names that as a subspace of `ℂ^n` — which at `k = 0` it
is the whole of, though nothing here proves that; see `## What is not here`.

Three rewrites and an instance. `ComplexAnalytic.etaleAnalytificationIso_hom_comp` replaces the
étale analytification by `D(G)` in the hypersurface, over the base;
`ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp` turns the remaining map to the base
followed by the base's inclusion into the hypersurface's inclusion followed by the projection;
and then the composite is an isomorphism followed by the theorem above, which
`ComplexAnalytic.AnalyticSpace.isLocalIso_comp` closes.

**`haveI` for both, and that is emphasis rather than necessity.**
`ComplexAnalytic.AnalyticSpace.isLocalIso_comp` is an instance and needs the two facts as local
instances to fire, which a plain `have` supplies as well: the proof compiles unchanged with
`have` twice, measured in tree. This paragraph also called that *"the same reason
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso` is a `theorem` and not an instance — its own
docstring says why"*; that docstring explains a discrimination-tree seam in its own proof and
says nothing about instance-versus-theorem, so the citation is withdrawn rather than replaced. -/
theorem isLocalIso_analytificationMap_etalePresHom_comp
    (P : StandardEtalePair (PresentedAlgebra.{u} n 0 g))
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} g F G) ≫ analytificationInclHom.{u} g) := by
  have hcomp :
      analytificationMap.{u} (etalePresHom.{u} g F G) ≫ analytificationInclHom.{u} g =
        (etaleAnalytificationIso.{u} g F G).hom ≫
          ((AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g F)).ofRestrict
            (localisationOpen.{u} (hypersurfacePresentation.{u} g F) G) ≫
            analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
              AnalyticSpace.proj.{u} n) := by
    rw [← etaleAnalytificationIso_hom_comp.{u} g F G, Category.assoc, Category.assoc,
      analytificationMap_hypersurfacePresHom_comp.{u} g F]
  rw [hcomp]
  haveI := isLocalIso_hypersurface_of_standardEtale.{u} g F G P hF hG
  haveI : AnalyticSpace.IsLocalIso (etaleAnalytificationIso.{u} g F G).hom :=
    AnalyticSpace.isLocalIso_of_isIso _
  infer_instance

end

end ComplexAnalytic

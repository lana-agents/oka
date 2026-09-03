/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.SpecScheme
import Oka.Analytification.SpecDistinguishedOpen

/-!
# A distinguished open of a member is an affine open of the glued scheme

`Oka/Analytification/SpecScheme.lean` glues a cover datum into a scheme `X` and shows that each
member is an affine open of it: `ComplexAnalytic.specSchemeIota` is the inclusion and
`ComplexAnalytic.isAffineOpen_specSchemeIota` is the statement. That file's
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` then says that every point of an overlap
lies in an open **distinguished in each of the two members** — an existential about opens, with
nothing exhibiting those opens as members of anything.

This file exhibits them. For a member `i` and a polynomial `p` in that member's own variables,
`D(p)` carries the presentation `ComplexAnalytic.localisationPresentation (obj i).g p`, and the
composite of `Spec` of the structure map with the member's own inclusion is an open immersion into
`X` whose range is exactly `D(p)` seen in `X`. **So a refined member is the same kind of object as
the member it refines** — an affine open of `X`, presented — and no transport is needed to say so.

## Main definitions

- `ComplexAnalytic.refinedPres`: **`D(p)`'s presentation, as an object of
  `ComplexAnalytic.Presentation`** — the member's presentation with one variable and one equation
  adjoined.
- `ComplexAnalytic.refinedIota`: **its inclusion into `X`**, as `Spec` of the structure map
  followed by `ComplexAnalytic.specSchemeIota`.

## Main results

- `ComplexAnalytic.isOpenImmersion_refinedIota`: **the inclusion is an open immersion**, which is
  what lets the two below be stated at all.
- `ComplexAnalytic.isAffineOpen_refinedIota`: **its range is an affine open of `X`** — the
  statement in the title and the reason the file exists.
- `ComplexAnalytic.opensRange_refinedIota`: **and that range is exactly the image of `D(p)`**, so
  the open is the one a caller named rather than merely some open the construction produced.

## What is not here, and the first two bullets are the operative ones

* **No choice function, and no family.** Taxis #1553 asks for a point-by-point existential —
  `ComplexAnalytic.exists_index_mvPolynomial_basicOpen_specSchemeIotaMap`, which gives at every
  point of `X` and an isomorphism of two cover data two indices and two polynomials in the
  members' own variables — to be turned into four chosen functions by `choose`. **That is one
  tactic and it is deliberately a separate file**, `Oka/Analytification/SpecMemberChoice.lean`,
  which has since landed. It was not merely out of scope when this file
  was written but unwritable: the theorem arrives with
  `Oka/Analytification/SpecMemberSections.lean`, which lana-agents/oka#374 added *after* this
  branch was cut, so there was nothing to `choose` from. Landing that branch removed the obstacle
  and did not put the step here. **This file indexes nothing by the points of `X`**, which is not
  a cover datum's index type and is not claimed to be one.
* **Nothing is said in terms of a polynomial read as a *section* of `X` either**, and that too is
  now a scope decision rather than a blocked one. `ComplexAnalytic.presentationSection` is the
  definition that reads a polynomial as a section over the range of an open immersion, and
  `ComplexAnalytic.basicOpen_presentationSection` says which open of `X` it cuts out; both arrived
  with lana-agents/oka#374, after this branch was cut.
  `ComplexAnalytic.opensRange_refinedIota` below states the range as the image of a
  `PrimeSpectrum.basicOpen` instead — **which is a statement about the open itself, and stays the
  usable one for a reader who has not imported that file.** **The section spelling of this range
  has since been added, and not to this file either**:
  `ComplexAnalytic.opensRange_refinedIota_eq_basicOpen`
  (`Oka/Analytification/SpecRefinedMemberSection.lean`) is
  `ComplexAnalytic.opensRange_refinedIota` composed with
  `ComplexAnalytic.basicOpen_specSchemeIotaSection`, whose right-hand sides are the same term.
  **This bullet used to price that step as *one rewrite* and to say it belonged with the choice
  step; both are corrected rather than deleted.** It is `Eq.trans` and `Eq.symm` and no rewrite at
  all — the `AlgebraicGeometry.Scheme.Hom.opensRange` motive hazard never arises for a term — and
  the choice step landed without it: the file named in the bullet above has the `choose` and not
  this equation. **Keeping it out of this file is the decision that clause above records**, since
  the import would make this file's own reader one who has imported that file.
* **No `poly`, no `glue`, and none of a cover datum's three laws.** That is the rest of
  `Oka/Analytification/SpecScheme.lean`'s third piece and it is taxis #1287's line, not this one —
  `Oka/Analytification/CrossMemberDatum.lean`, `Oka/Analytification/CrossMemberDatumGlue.lean` and
  the `Oka/Analytification/RefineDatum*.lean` files. **Nothing here is a cover datum and nothing
  here claims to refine one.** Two members' distinguished opens are not compared, in either
  direction: `i` and `p` are one member and one polynomial.
* **No common refinement, and no second cover datum.** `ComplexAnalytic.specSchemeIotaMap` and
  `Oka/Analytification/SpecTwoData.lean`'s two-datum vocabulary do not appear.
* **Nothing analytic.** No analytification, no `X^an`, no comparison morphism.
* **Nothing about `p` being non-zero, or `D(p)` being non-empty.** At `p = 0` everything below is
  a statement about the empty open and stays true; nothing here excludes it and nothing here
  needs to.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace ComplexAnalytic

noncomputable section

variable {J : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i)
  (hrange : ∀ i j k : J, i ≠ j → i ≠ k → j ≠ k →
    Set.range (specTripleIncl.{u} obj poly i j k ≫ specTransitionHom.{u} obj poly glue i j).base ⊆
      (specOpen.{u} obj poly j k : Set (specSpace.{u} obj j)))
  (hsymm : ∀ i j : J, glue j i = (glue i j).symm)
  (hcocycle : ∀ i j k : J, ∀ hij : i ≠ j, ∀ hik : i ≠ k, ∀ hjk : j ≠ k,
    specTriple.{u} obj poly glue hrange i j k hij hik hjk ≫
      specTriple.{u} obj poly glue hrange j k i hjk hij.symm hik.symm ≫
      specTriple.{u} obj poly glue hrange k i j hik.symm hjk.symm hij = 𝟙 _)

/-- **The presentation of `D(p)` inside the `i`-th member**, as an object of
`ComplexAnalytic.Presentation`.

`ComplexAnalytic.localisationPresentation` at the member's own relations: one variable and one
equation more. **An `abbrev` and not a `def`**, so that `ComplexAnalytic.localisationRingHom`'s
codomain and this object's `ComplexAnalytic.Presentation.alg` are the same term without a
`change` — the same reason `ComplexAnalytic.refineDatumObj`
(`Oka/Analytification/CrossMemberDatum.lean`) is one, and this is that object at the `Spec`
side's spelling of the same situation.

The tuple is `Fin.snoc`'d with `X_last · p − 1` and **not** with a reduced form of it; see
`ComplexAnalytic.localisationPresentation`'s own docstring. -/
abbrev refinedPres (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) : Presentation.{u} :=
  ⟨(obj i).n + 1, (obj i).k + 1, localisationPresentation.{u} (obj i).g p⟩

/-- **The inclusion of `D(p)` into `X`.**

`Spec` of the structure map `A_i ⟶ (A_i)_p`, followed by the member's own inclusion
`ComplexAnalytic.specSchemeIota`. Both factors are already here — the first is
`Oka/Analytification/SpecDistinguishedOpen.lean`'s and the second is
`Oka/Analytification/SpecScheme.lean`'s — and **the only content is that they compose**, which
they do because `ComplexAnalytic.Presentation.alg` is an `abbrev` and the codomain of
`ComplexAnalytic.localisationRingHom` is `ComplexAnalytic.refinedPres`'s algebra on the nose.

The scheme-level spelling and not `ComplexAnalytic.specFunctor`'s: the target is
`ComplexAnalytic.specScheme`, which is a `AlgebraicGeometry.Scheme`, and
`ComplexAnalytic.specSchemeIota` is the morphism of schemes it has. -/
def refinedIota (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    Spec (CommRingCat.of (refinedPres.{u} obj i p).alg) ⟶
      specScheme.{u} obj poly glue hrange hsymm hcocycle :=
  Spec.map (CommRingCat.ofHom (localisationRingHom.{u} (obj i).g p)) ≫
    specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i

/-- **It is an open immersion**, being a composite of two.

`AlgebraicGeometry.IsOpenImmersion.comp` at
`ComplexAnalytic.isOpenImmersion_Spec_map_localisationRingHom` — which is a *theorem* and not an
instance, so it is supplied by a `haveI` in the proof — and
`ComplexAnalytic.isOpenImmersion_specSchemeIota`, which is an instance and is found.

**A `haveI` here and an `attribute [local instance]` in
`Oka/Analytification/SpecDistinguishedOpen.lean`, and the difference is not a matter of taste**:
there the instance is needed to *state* the theorem, where a `haveI` cannot reach; here it is
needed only inside the proof, and the narrower tool is the right one.

**An `instance` and not a theorem**, because `AlgebraicGeometry.Scheme.Hom.opensRange` takes one
as an argument and the two statements below are about that range: without it neither of them can
be *stated*. -/
instance isOpenImmersion_refinedIota (i : J)
    (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    IsOpenImmersion (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p) :=
  haveI := isOpenImmersion_Spec_map_localisationRingHom.{u} (obj i).g p
  IsOpenImmersion.comp _ _

/-- **A distinguished open of a member is an affine open of `X`** — the statement this file exists
for.

`AlgebraicGeometry.isAffineOpen_opensRange` at the instance above, exactly as
`ComplexAnalytic.isAffineOpen_specSchemeIota` gets the member's own statement: the
`AlgebraicGeometry.IsAffine` side condition is on the *source*, and the source here is a spectrum.

**What this adds to that theorem is that the affine opens of `X` this development can name are
closed under passing to a distinguished open of one of them**, with the presentation carried
along — `ComplexAnalytic.refinedPres` — rather than with the open produced abstractly and its
affineness argued afterwards. -/
theorem isAffineOpen_refinedIota (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    IsAffineOpen (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p).opensRange :=
  isAffineOpen_opensRange _

/-- **And the open it is, is the one the caller named**: the image under the member's inclusion of
the basic open of `p`'s class in the member's algebra.

`AlgebraicGeometry.Scheme.Hom.opensRange_comp` and
`ComplexAnalytic.opensRange_Spec_map_localisationRingHom`. **Without this the two theorems above
say only that *some* affine open of `X` is presented by `ComplexAnalytic.refinedPres`**, and a
caller who chose `p` to cut out a particular open — which is what
`ComplexAnalytic.exists_basicOpen_specSchemeIota_inter` produces — could not tell that it got that
one. This is the statement that makes `ComplexAnalytic.refinedIota` a *refinement* of the member
rather than an unrelated affine open of `X` that happens to sit inside it.

**The image and not a `Set.range`, and that is why
`ComplexAnalytic.opensRange_Spec_map_localisationRingHom` had to be stated**:
`AlgebraicGeometry.Scheme.Hom.opensRange_comp` is at `AlgebraicGeometry.Scheme.Hom.opensRange`
and has no `Set.range` form, so `ComplexAnalytic.range_base_specFunctor_map_localisationHom` — the
spelling `Oka/Analytification/SpecAffineCover.lean`'s glue datum wants — cannot be used here.

**The `have … := rfl` rather than naming `ComplexAnalytic.refinedIota` in the `simp only`.**
`refinedIota` is a `def`, and naming a definition as a rewrite rule generates its equation lemma
into this module, a hazard several files in this tree record. The composite is definitionally the
definition, so `rfl` proves the unfolding and `simp only` consumes it as an ordinary hypothesis. -/
theorem opensRange_refinedIota (i : J) (p : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (refinedIota.{u} obj poly glue hrange hsymm hcocycle i p).opensRange =
      specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i ''ᵁ
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (presentationIdeal.{u} (obj i).g) p) := by
  haveI := isOpenImmersion_Spec_map_localisationRingHom.{u} (obj i).g p
  have h : refinedIota.{u} obj poly glue hrange hsymm hcocycle i p =
      Spec.map (CommRingCat.ofHom (localisationRingHom.{u} (obj i).g p)) ≫
        specSchemeIota.{u} obj poly glue hrange hsymm hcocycle i := rfl
  simp only [h, Scheme.Hom.opensRange_comp, opensRange_Spec_map_localisationRingHom]

end

end ComplexAnalytic

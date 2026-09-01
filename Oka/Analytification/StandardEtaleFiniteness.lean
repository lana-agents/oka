/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.HypersurfaceFinite
import Oka.Analytification.OpenBaseFiniteness

/-!
# The analytification of a standard étale morphism is finite over an open subset of the base

`Oka/Analytification/OpenBaseFiniteness.lean` makes the hypersurface `{F = 0}` finite over every
open `V ⊆ ℂ^n`, and says in terms that the step it does **not** take is the one that would make
that hypersurface the analytification of a *localised* algebra:

> Identifying the source of this theorem with the analytification of a *localised* algebra is the
> step `ComplexAnalytic.etaleAnalytificationIso` would be spent on, and it is not taken.

This file takes it. Over `V ⊆ (ComplexAnalytic.hypersurfaceCommonZeroImage F G)ᶜ` the part of the
hypersurface lying above `V` is already inside `D(G)`, so the standard étale analytification —
which `ComplexAnalytic.etaleAnalytificationIso` identifies with `D(G)` inside that hypersurface,
**over the base** — has the same part above `V`, and the finiteness transports.

Together with `Oka/Analytification/StandardEtaleLocalIso.lean`, which is the local-isomorphism
half, this is the whole of taxis #1112's §1 at `k = 0`.

## The route

Three steps, and only the middle one is about `F` and `G` at all.

* **The hypersurface, in the presentation spelling.**
  `ComplexAnalytic.isFinite_analytification_comp_projRestrict` is stated for the family
  `![(lastVarPolyEquiv n).symm F]` and as `ComplexAnalytic.AnalyticSpace.restrictHom` of the
  inclusion followed by `ComplexAnalytic.AnalyticSpace.projRestrict`; the comparison is stated for
  `ComplexAnalytic.hypersurfacePresentation` and wants the restriction of a single composite.
  `ComplexAnalytic.hypersurfacePresentation_empty` bridges the families and
  `ComplexAnalytic.AnalyticSpace.restrictHom_comp` bridges the two shapes — the projection over
  `V` **is** the projection restricted, `ComplexAnalytic.cylinder V` being the preimage of `V` by
  definition, so no content crosses here.
* **The containment**, which is the geometry: above a `V` avoiding the bad set, `G` vanishes at no
  point of the hypersurface. That is
  `ComplexAnalytic.eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage` and
  `ComplexAnalytic.mem_localisationOpen_iff`, and it is one line because both are quantified over
  *points* and neither crosses an `AnalyticSpace.restrict`.
* **The transport.** `ComplexAnalytic.etaleAnalytificationIso_hom_comp` factors the étale
  projection as the isomorphism, the inclusion of `D(G)`, and the hypersurface's own projection —
  the same factorisation `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` uses,
  regrouped so that the first two are one morphism. Restricting that composite over `V` splits it
  by `restrictHom_comp`, and the first factor is finite by
  `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range`.

## What the two obstacles on record turned out to be

Taxis #1448 sized this item and named two obstacles; both were measured, and what the proof needed
was neither of them.

* **The spelling bridge is real and is here**, as `ComplexAnalytic.hypersurfacePresentation_empty`
  in `Oka/Analytification/StandardEtaleAnalytification.lean`.
* **The `ComplexAnalytic.AnalyticSpace.IsFinite` transport along an isomorphism was recorded as
  missing, and it is not missing**: `ComplexAnalytic.AnalyticSpace.isFinite_comp` is an
  **instance** and `ComplexAnalytic.AnalyticSpace.isFinite_of_isIso` is beside it, so
  `IsFinite p → IsFinite (e.hom ≫ p)` is `haveI := isFinite_of_isIso e.hom; infer_instance`. The
  `exact?` that reported *"could not close the goal"* on
  `Oka/AnalyticSpace/Finite.lean` was asking for a lemma, and the fact is carried by instance
  search instead.
* **And that transport is not the step this file takes**, which is the part worth keeping. The
  composite whose finiteness is wanted is the **restriction over `V`**, and the unrestricted one
  is not finite at all — that is taxis #1112's counterexample. What is needed is that *restricting
  an open immersion over an open subset of its image is finite*, which is a statement about `V`
  and not about the morphism, and which
  `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` now carries. An
  isomorphism appears in the proof only because the open immersion here is
  `etaleAnalytificationIso` followed by the inclusion of `D(G)`; it contributes an embedding and a
  surjection and nothing else.

## Main results

- `ComplexAnalytic.isFinite_restrictHom_hypersurface_comp_proj`: the hypersurface of `ℂ^(n+1)`,
  read as the analytification of `ComplexAnalytic.hypersurfacePresentation` at an empty base
  presentation, is **finite over every open subset of `ℂ^n`**. This is
  `ComplexAnalytic.isFinite_analytification_comp_projRestrict` in the spelling the comparison
  uses, and no geometry is added to it.
- `ComplexAnalytic.map_le_localisationOpen_of_subset_compl`: **above a `V` avoiding the bad set
  the hypersurface is contained in `D(G)`.** The geometric content, at the level of opens.
- `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp`: **the
  analytification of a standard étale morphism, restricted over an open subset of `ℂ^n` on which
  the inversion is vacuous, is finite over that subset.** The theorem the file is for.
- `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp_compl`: the same at
  the largest such subset, the complement of `ComplexAnalytic.hypersurfaceCommonZeroImage`, which
  is open by `ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage`.

## What is not here

* **No `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` *here*, and the lemma this bullet said was
  missing now exists.** It ended *"nothing in the repository transports it — measured, not read:
  no statement anywhere has `IsLocalIso` applied to a `restrictHom`"*, and the sizing was right:
  the transport is a general fact about open subspaces with nothing étale in it, and it is
  `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`
  (`Oka/AnalyticSpace/OpenSubspace.lean`), which asks nothing of the morphism and nothing of the
  open. The class itself is
  `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp`
  (`Oka/Analytification/StandardEtaleFiniteEtale.lean`), whose first field is the theorem below
  verbatim. **It is not here, and that is a placement decision rather than an absence**: the
  bullet below says this file reads no `StandardEtalePair`, and the class does read one.

  **The unrestricted `IsFiniteEtale` stays false forever** and nothing here bears on it:
  `Oka/Analytification/MonicHypersurface.lean` carries the counterexample, in terms, and nothing
  below narrows it. A **different and broader** absence — *the analytification of a finite étale
  morphism of schemes*, the other blocker of the Riemann existence theorem — is what
  `Oka/AnalyticSpace/LocalIso.lean`, `Oka/AnalyticSpace/CoveringMap.lean` and
  `Oka/AnalyticSpace/SigmaFiniteEtale.lean` record, in those words. Nothing below narrows that
  either: everything here is one standard étale presentation over `ℂ^n`, and the general morphism
  is a Zariski-local gluing that nothing starts.
* **Nothing at `k ≥ 1`.** Everything is at an empty base presentation, for the reason
  `Oka/Analytification/StandardEtaleLocalIso.lean` gives for its own restriction: the two sides
  meet only over `ℂ^n`. `ComplexAnalytic.isFinite_analytification_comp_projRestrict`'s base is
  `ℂ^n` and `ComplexAnalytic.etaleAnalytificationIso`'s is `A^an`, and a statement over a
  presented base is a different theorem rather than a missing hypothesis.
* **No `StandardEtalePair`, and no `StandardEtalePair.cond` is read.** The theorems below hold for
  **every** monic `F` and **every** `G` — `G` is read only through the bad set — so nothing here
  says the source is étale, only that it is the analytification of the presentation
  `ComplexAnalytic.etalePresentation` names. That is the same stance
  `ComplexAnalytic.etaleAnalytificationIso` takes, and it is a weaker hypothesis than
  `Oka/Analytification/StandardEtaleLocalIso.lean`'s last two theorems take.
* **No isomorphism of restricted spaces**, and the containment is not turned into one. Finiteness
  needs a closed embedding and no more, which is what
  `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` supplies. The restricted
  morphism is in fact **bijective** on points — `ComplexAnalytic.surjective_base_restrictHom` is
  the surjective half and the embedding is the other — so the two restricted spaces are
  homeomorphic; promoting that to an isomorphism of *analytic* spaces needs an inverse morphism
  together with its `ℂ`-linearity, and nothing here builds one.
  `Oka/AnalyticSpace/OpenSubspace.lean`'s `ComplexAnalytic.AnalyticSpace.liftRestrict` is the
  construction that would, and it is not called.
* **Nothing about how large `V` is**, and that is a hypothesis on the pair `(F, G)` rather than a
  theorem. `Oka/Analytification/OpenBaseFiniteness.lean` bounds it from both ends —
  `ComplexAnalytic.hypersurfaceCommonZeroImage_one` makes the bad set empty at `G = 1`, so `V` may
  be all of `ℂ^n`, and `ComplexAnalytic.hypersurfaceCommonZeroImage_X` makes it everything, so `V`
  may be empty and the theorem below say nothing. **No pair is exhibited anywhere for which `V` is
  proper *and* nonempty**, which is the case the statement is interesting in;
  `OkaTest/OpenBaseFiniteness.lean` exhibits a non-degenerate pair at which `V` is empty. Read
  this file as the transport of a finiteness across `ComplexAnalytic.etaleAnalytificationIso`, and
  read `OkaTest/OpenBaseFiniteness.lean` for what such a statement buys.
* **No stalks, no germs and no derivative.** The local-isomorphism half is
  `Oka/Analytification/StandardEtaleLocalIso.lean` and nothing here is evidence about it.
-/

open CategoryTheory MvPolynomial AlgebraicGeometry TopologicalSpace Opposite Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n : ℕ} (g : Fin 0 → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))

/-! ### The hypersurface over `V`, in the presentation spelling -/

/-- **The hypersurface `{F = 0} ⊆ ℂ^(n+1)`, read as the analytification of
`ComplexAnalytic.hypersurfacePresentation` at an empty base presentation, is finite over every
open subset of `ℂ^n`.**

`ComplexAnalytic.isFinite_analytification_comp_projRestrict` and nothing else. Two spellings are
changed and neither carries content:

* the family — `ComplexAnalytic.hypersurfacePresentation_empty`, which is not `rfl` and is why
  that lemma exists;
* the shape — `ComplexAnalytic.AnalyticSpace.restrictHom_comp`, which splits the restriction of
  `incl ≫ proj` over `V` into the restriction of `incl` over `ComplexAnalytic.cylinder V` followed
  by `ComplexAnalytic.AnalyticSpace.projRestrict V`. Both of those are definitional —
  `ComplexAnalytic.cylinder` **is** the preimage of `V` under the projection and `projRestrict`
  **is** `restrictHom` of the projection — so the lemma is doing the association and nothing more.

**The `rw` on the family is available here and is not available everywhere**: the presentation
occurs only as an argument to `ComplexAnalytic.AnalyticSpace.analytification` and to
`ComplexAnalytic.analytificationInclHom`, and `V` does not mention it, so the motive is a function
of the family and `rw` builds it. -/
theorem isFinite_restrictHom_hypersurface_comp_proj (hF : F.Monic)
    (V : Opens (ULift.{u} (Fin n) → ℂ)) :
    AnalyticSpace.IsFinite (AnalyticSpace.restrictHom
      (analytificationInclHom.{u} (hypersurfacePresentation.{u} g
        ((lastVarPolyEquiv.{u} n).symm F)) ≫ AnalyticSpace.proj.{u} n) V) := by
  rw [hypersurfacePresentation_empty, AnalyticSpace.restrictHom_comp]
  exact isFinite_analytification_comp_projRestrict.{u} F hF V

/-! ### The containment, which is the geometry -/

/-- **Above an open subset of the base avoiding the bad set, the hypersurface lies inside
`D(G)`.**

This is the statement `Oka/Analytification/OpenBaseFiniteness.lean` calls *the vacuity of the
inversion*, moved from points to opens, and it is the one place where `G` does anything.

`ComplexAnalytic.eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage` says exactly that `G` does
not vanish at a point of the hypersurface whose projection avoids the bad set, and
`ComplexAnalytic.mem_localisationOpen_iff` says that not vanishing **is** membership of `D(G)`. So
the proof is those two and the hypothesis, with nothing between them.

**It crosses no `ComplexAnalytic.AnalyticSpace.restrict`, and that is why it is one line.** The
hazard `ComplexAnalytic.isFinite_analytification_comp_projRestrict` records at its own range
step — that a goal mentioning a restricted space is not type-correct at `instances` transparency,
so `rw` fails on a pattern that is visibly present — does not fire here: both facts quoted are
quantified over points of the *unrestricted* analytification, and an inequality of opens is
settled point by point. -/
theorem map_le_localisationOpen_of_subset_compl {V : Opens (ULift.{u} (Fin n) → ℂ)}
    (hV : (V : Set (ULift.{u} (Fin n) → ℂ)) ⊆ (hypersurfaceCommonZeroImage.{u} F G)ᶜ) :
    (Opens.map (analytificationInclHom.{u} (hypersurfacePresentation.{u} g
          ((lastVarPolyEquiv.{u} n).symm F)) ≫
        AnalyticSpace.proj.{u} n).toLRSHom.base).obj V ≤
      localisationOpen.{u} (hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm F))
        ((lastVarPolyEquiv.{u} n).symm G) := by
  rw [hypersurfacePresentation_empty]
  intro y hy
  rw [mem_localisationOpen_iff]
  exact eval_ne_zero_of_notMem_hypersurfaceCommonZeroImage.{u} F G y (hV hy)

/-! ### The finiteness of the standard étale analytification over `V` -/

/-- **The analytification of a standard étale morphism over `ℂ^n`, restricted over an open subset
of the base on which the inversion is vacuous, is finite over that subset.**

The theorem taxis #1112's §1 is named for, and the one place in the development where
`ComplexAnalytic.etaleAnalytificationIso` is spent on a *finiteness*.

**Read the hypothesis first.** `V` is any open subset of `ℂ^n` disjoint from
`ComplexAnalytic.hypersurfaceCommonZeroImage F G` — the image of the points of `{F = 0}` at which
`G` also vanishes. Above such a `V` there is nothing to invert, which is what makes the étale
analytification and the hypersurface agree there; over a `V` meeting the bad set the conclusion is
**false**, since the unrestricted morphism is not finite and `taxis #1112`'s punctured parabola is
the witness.

The proof is the factorisation `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`
uses, regrouped. `ComplexAnalytic.etaleAnalytificationIso_hom_comp` and
`ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp` write the étale projection as

    (iso ≫ inclusion of D(G)) ≫ (inclusion of the hypersurface ≫ projection to ℂ^n)

and `ComplexAnalytic.AnalyticSpace.restrictHom_comp` restricts the two factors separately. The
second is the theorem above. The first is
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range`, whose two hypotheses are
where the isomorphism and the containment are spent: an isomorphism of analytic spaces followed by
an open immersion is an **embedding** on bases, and its **range is `D(G)`**, which the containment
puts the relevant open inside of. Both come from the one homeomorphism
`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso` produces from the isomorphism — the embedding
from its being one, the range from its being surjective.

**`AnalyticSpace.isFinite_comp` is applied by name rather than by `infer_instance`**, and that is
not decoration: the two facts are `have`s about `ComplexAnalytic.AnalyticSpace.restrictHom` at
opens which the goal spells through `Opens.map`, and instance search does not close the goal from
them even as `haveI`s — measured, *"failed to synthesize instance"* on the first factor. Naming
the instance and passing both explicitly is what makes the composite go through. -/
theorem isFinite_restrictHom_analytificationMap_etalePresHom_comp (hF : F.Monic)
    (V : Opens (ULift.{u} (Fin n) → ℂ))
    (hV : (V : Set (ULift.{u} (Fin n) → ℂ)) ⊆ (hypersurfaceCommonZeroImage.{u} F G)ᶜ) :
    AnalyticSpace.IsFinite (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)) ≫ analytificationInclHom.{u} g) V) := by
  have hcomp : analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)) ≫ analytificationInclHom.{u} g =
      ((etaleAnalytificationIso.{u} g ((lastVarPolyEquiv.{u} n).symm F)
            ((lastVarPolyEquiv.{u} n).symm G)).hom ≫
          (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g
            ((lastVarPolyEquiv.{u} n).symm F))).ofRestrict
            (localisationOpen.{u} (hypersurfacePresentation.{u} g
              ((lastVarPolyEquiv.{u} n).symm F)) ((lastVarPolyEquiv.{u} n).symm G))) ≫
        (analytificationInclHom.{u} (hypersurfacePresentation.{u} g
          ((lastVarPolyEquiv.{u} n).symm F)) ≫ AnalyticSpace.proj.{u} n) := by
    rw [← etaleAnalytificationIso_hom_comp.{u} g, Category.assoc, Category.assoc,
      analytificationMap_hypersurfacePresHom_comp.{u} g, Category.assoc]
  rw [hcomp, AnalyticSpace.restrictHom_comp]
  have hbase := isFinite_restrictHom_hypersurface_comp_proj.{u} g F hF V
  have hopen : AnalyticSpace.IsFinite (AnalyticSpace.restrictHom
      ((etaleAnalytificationIso.{u} g ((lastVarPolyEquiv.{u} n).symm F)
            ((lastVarPolyEquiv.{u} n).symm G)).hom ≫
          (AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} g
            ((lastVarPolyEquiv.{u} n).symm F))).ofRestrict
            (localisationOpen.{u} (hypersurfacePresentation.{u} g
              ((lastVarPolyEquiv.{u} n).symm F)) ((lastVarPolyEquiv.{u} n).symm G)))
      ((Opens.map (analytificationInclHom.{u} (hypersurfacePresentation.{u} g
          ((lastVarPolyEquiv.{u} n).symm F)) ≫
        AnalyticSpace.proj.{u} n).toLRSHom.base).obj V)) := by
    refine AnalyticSpace.isFinite_restrictHom_of_subset_range ?_ ?_
    · exact (localisationOpen.{u} (hypersurfacePresentation.{u} g
        ((lastVarPolyEquiv.{u} n).symm F))
          ((lastVarPolyEquiv.{u} n).symm G)).isOpenEmbedding.isEmbedding.comp
        (LocallyRingedSpace.homeoOfIso (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
          (etaleAnalytificationIso.{u} g ((lastVarPolyEquiv.{u} n).symm F)
            ((lastVarPolyEquiv.{u} n).symm G)))).isEmbedding
    · intro y hy
      obtain ⟨z, hz⟩ := (LocallyRingedSpace.homeoOfIso
        (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso
          (etaleAnalytificationIso.{u} g ((lastVarPolyEquiv.{u} n).symm F)
            ((lastVarPolyEquiv.{u} n).symm G)))).surjective
        ⟨y, map_le_localisationOpen_of_subset_compl.{u} g F G hV hy⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  exact @AnalyticSpace.isFinite_comp _ _ _ _ _ hopen hbase

/-- **The same at the largest open subset there is**, the complement of the bad set.

`ComplexAnalytic.isClosed_hypersurfaceCommonZeroImage` is what makes that complement open, and it
is the only place monicity is spent twice: once there and once inside the theorem above.

Stated because the theorem above quantifies over `V` and a reader wants to know that the
quantification is not empty of content — every `V` it applies to is contained in this one, and
this one is an open subset of `ℂ^n` that the development already owns. **It says nothing about
whether that open subset is nonempty**; see this file's `## What is not here`. -/
theorem isFinite_restrictHom_analytificationMap_etalePresHom_comp_compl (hF : F.Monic) :
    AnalyticSpace.IsFinite (AnalyticSpace.restrictHom
      (analytificationMap.{u} (etalePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm F)
        ((lastVarPolyEquiv.{u} n).symm G)) ≫ analytificationInclHom.{u} g)
      ⟨(hypersurfaceCommonZeroImage.{u} F G)ᶜ,
        (isClosed_hypersurfaceCommonZeroImage.{u} F G hF).isOpen_compl⟩) :=
  isFinite_restrictHom_analytificationMap_etalePresHom_comp.{u} g F G hF _ subset_rfl

end

end ComplexAnalytic

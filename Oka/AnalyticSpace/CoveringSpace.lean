/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringMap
import Oka.AnalyticSpace.Glue
import Oka.AnalyticSpace.InverseImageSheet
import Oka.Topology.IsLocalHomeomorph

/-!
# A covering space of a complex analytic space is a complex analytic space

Let `X` be a complex analytic space and `p : E → X` a local homeomorphism of topological spaces.
Then `E` carries a complex analytic structure — the inverse image `p⁻¹𝒪_X` of the structure sheaf
— for which `p` is a morphism of analytic spaces, and that morphism is a local isomorphism. If `p`
is moreover a covering map with finite fibres it is **finite étale**.

This is the Riemann existence theorem's topological input: it is what turns a topological covering
of an analytic space into an object of the category the theorem compares with finite étale
algebras.

## The `ℂ`-algebra structure is not glued, and that is the design

`ComplexAnalytic.HasLocalModels` is a *property* and is local on the space
(`ComplexAnalytic.HasLocalModels.of_iSup_eq_top`), but the `ℂ`-algebra structure is *data* landing
in **global** sections, so it does not restrict from a cover for free —
`Oka/AnalyticSpace/Local.lean`'s docstring is explicit about the difference, and
`ComplexAnalytic.AnalyticSpace.ofOpensCompatible` is the constructor that glues one from
structures on the members.

**Nothing here glues anything.** `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom` is a
morphism `p⁻¹X ⟶ X` defined on the whole of `p⁻¹X`, so `X`'s structure pulled back along it is
already a structure on the global sections of `p⁻¹X`
(`ComplexAnalytic.inverseImageAlgMap`), and `ComplexAnalytic.AnalyticSpace.ofHasLocalModels` is
all that is needed. The cover is used for the *property* and for nothing else.

That is what sidesteps the gap
`Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImageSheet.lean` records under its
`## What is not here`: *"No cocycle and no gluing. Two sheets `V₀`, `V₁` meeting give two
isomorphisms over `p '' (V₀ ∩ V₁)` and nothing here compares them."* Two sheets are never
compared below, so the naive `p '' (V₀ ∩ V₁) = p '' V₀ ∩ p '' V₁` — **false** for a covering map,
as that file's counterexample shows — is never needed.

## The cover, and what each member costs

The members are the **sheets**: `sheetOpens ⇑p`, the opens of `E` on which `p` is an open
embedding, which cover by `IsLocalHomeomorph.sSup_sheetOpens`. Over one sheet `V` the three
inputs compose with nothing left over:

* `AlgebraicGeometry.LocallyRingedSpace.sheetIso` identifies `(p⁻¹X)|V` with `X|(p '' V)` as
  locally ringed spaces;
* `ComplexAnalytic.isCLinearHom_sheetHom` makes that identification `ℂ`-linear — an isomorphism
  of locally ringed spaces between analytic spaces can be antiholomorphic, so this half is not
  decoration. It is not, however, what `ComplexAnalytic.HasLocalModels.of_iso` is handed below:
  after `AlgebraicGeometry.LocallyRingedSpace.sheetIso_hom` that obligation is the by-definition
  `ComplexAnalytic.isCLinearHom_comapAlgMap`, and the sheet linearity reaches the assembly one
  level down, through the next bullet;
* `ComplexAnalytic.comapAlgMap_sheetHom` says the structure the sheet inherits *is* the ambient
  one restricted, which is the side of the seam `of_iSup_eq_top` states its hypothesis on. **This
  is the lemma `ComplexAnalytic.isCLinearHom_sheetHom` is consumed by**: the sheet linearity is
  what makes that equality of structures true.

So the member obligation is `ComplexAnalytic.HasLocalModels.restrict` on `X` and two rewrites.

## Finiteness is the only thing that is not already here

`ComplexAnalytic.AnalyticSpace.IsLocalIso` costs nothing: its topological field is
`IsCoveringMap.isLocalHomeomorph`, or the hypothesis itself, and its stalk field is the instance
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_inverseImageHom` — *every* stalk map of the
inverse image is an isomorphism, for an arbitrary continuous map.

`ComplexAnalytic.AnalyticSpace.IsFinite` is *closed base map* and *finite fibres*. The second is a
hypothesis; the first is not implied by it and is `IsCoveringMap.isClosedMap` in
`Oka/Topology/Covering/Basic.lean`, added for this file. It is the one new piece of mathematics
in this line and it is topology, not analysis.

`Oka/AnalyticSpace/CoveringMap.lean` goes the other way — finite étale implies covering map — and
needs `[T2Space]`, because Mathlib's criterion separates the points of a fibre. **This direction
needs no separation axiom**, and none is assumed below.

## Main definitions

- `ComplexAnalytic.inverseImageAlgMap`: the `ℂ`-algebra structure on `p⁻¹X`, pulled back from `X`
  along the whole of `AlgebraicGeometry.LocallyRingedSpace.inverseImageHom`.
- `ComplexAnalytic.AnalyticSpace.coveringSpace`: **the complex analytic space on the source of a
  local homeomorphism into a complex analytic space.**
- `ComplexAnalytic.AnalyticSpace.coveringSpaceHom`: the morphism of complex analytic spaces it
  carries, whose underlying map is `p`.

## Main results

- `ComplexAnalytic.hasLocalModels_inverseImage`: **the inverse image of a complex analytic space
  along a local homeomorphism has local models**, which is the whole of the object-level content.
- `ComplexAnalytic.AnalyticSpace.base_coveringSpaceHom`: the underlying map is `p` on the nose.
- `ComplexAnalytic.AnalyticSpace.isLocalIso_coveringSpaceHom`: **a local homeomorphism into a
  complex analytic space is a local isomorphism** for this structure.
- `ComplexAnalytic.AnalyticSpace.isFinite_coveringSpaceHom` and
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom`: **a covering map with finite
  fibres is finite étale** for this structure.

## What is not here

* **No uniqueness.** Nothing below says this is the *only* analytic structure on `E` making `p` a
  local isomorphism, and that statement needs deciding before it can be proved: an isomorphism of
  locally ringed spaces between analytic spaces is not on its own an identification of analytic
  spaces, for the antiholomorphy reason `Oka/AnalyticSpace/InverseImageSheet.lean` gives. It is a
  separate issue and the reason this file's results are stated as a *construction* rather than as
  an equivalence.
* **No comparison with `ComplexAnalytic.AnalyticSpace.sigma`.** The trivial `ι`-sheeted cover
  `ComplexAnalytic.AnalyticSpace.sigmaFold` is a covering map with finite fibres, so this file
  puts a structure on its source; whether that structure is `sigma`'s own is exactly the
  uniqueness question above and is **not** answered here. `OkaTest/CoveringSpace.lean` says so
  again where a reader would look for it.
* **Nothing about the number of sheets.**
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` in
  `Oka/AnalyticSpace/CoveringMap.lean` is that statement, over a preconnected base — but it is
  **not** free for the morphism below, and two things stand in the way. It asks `[T2Space]` of the
  *source*, which is Mathlib's hypothesis, used to separate the finitely many points of a fibre,
  and is exactly the separation axiom this direction otherwise does without; `E` is arbitrary
  here, so there is nothing to synthesise. And
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` is a theorem rather than an
  instance, so it has to be supplied by hand. A caller holding `[T2Space E]` gets the statement by
  carrying that instance across the carrier seam with `inferInstanceAs` and supplying the
  finite-étale one; a caller without one does not get it at all. The same barrier stands one file
  further on: `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` in
  `Oka/AnalyticSpace/Degree.lean`, which is where a reader looking for the number of sheets *as a
  number* will land, asks `[T2Space]` of the source for the same reason and through the same
  lemma. Nothing below states either.
* **No sections of `p⁻¹𝒪_X`.** No formula is proved for the sections over an open set, here or in
  either file below — over a sheet the *space* is identified with the base and that is strictly
  weaker than a formula, which is all a chart needs.
* **No converse.** A morphism of analytic spaces that is finite étale has a covering map for its
  underlying map (`Oka/AnalyticSpace/CoveringMap.lean`), but the structure it carries is not
  compared with the one built here — again the uniqueness question.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable (X : AnalyticSpace.{u}) {E : TopCat.{u}} (p : E ⟶ X.toLocallyRingedSpace.toTopCat)

/-- **The `ℂ`-algebra structure on the inverse image**: `X`'s structure pulled back along
`AlgebraicGeometry.LocallyRingedSpace.inverseImageHom`.

There is no choice in it and nothing to glue. `inverseImageHom` is defined on the whole of
`p⁻¹X`, so pulling back along it lands in **global** sections, which is where a
`ComplexAnalytic.AnalyticSpace`'s structure lives; the sheet-by-sheet structures of
`ComplexAnalytic.comapAlgMap_sheetHom` are this one restricted, and not the other way round. See
the module docstring on why that ordering is what makes the construction short. -/
def inverseImageAlgMap :
    ℂ →+* (X.toLocallyRingedSpace.inverseImage p).presheaf.obj (op ⊤) :=
  LocallyRingedSpace.comapAlgMap (X.toLocallyRingedSpace.inverseImageHom p) X.algebraMap

/-- **The inverse image of a complex analytic space along a local homeomorphism has local
models.**

`ComplexAnalytic.HasLocalModels.of_iSup_eq_top` over the sheets of `p`, which cover by
`IsLocalHomeomorph.sSup_sheetOpens`. On one sheet the chart is `X`'s own chart on the image open
`p '' V`, carried back by `ComplexAnalytic.HasLocalModels.of_iso` along
`AlgebraicGeometry.LocallyRingedSpace.sheetIso`, whose `ℂ`-linearity is
`ComplexAnalytic.isCLinearHom_comapAlgMap` — true by definition once
`AlgebraicGeometry.LocallyRingedSpace.sheetIso_hom` has rewritten the goal.
`ComplexAnalytic.comapAlgMap_sheetHom` is what turns the structure that produces into the
restriction of `ComplexAnalytic.inverseImageAlgMap`, which is the spelling the hypothesis of
`of_iSup_eq_top` is written in, and it is the step that consumes
`ComplexAnalytic.isCLinearHom_sheetHom`.

Only a local homeomorphism is needed — not a covering map, and no finiteness. -/
theorem hasLocalModels_inverseImage (hp : IsLocalHomeomorph ⇑p) :
    HasLocalModels (X.toLocallyRingedSpace.inverseImage p) (inverseImageAlgMap X p) := by
  refine HasLocalModels.of_iSup_eq_top
    (U := fun V : ↥(sheetOpens ⇑p) ↦ (V : Opens E)) ?_ ?_
  · -- The carrier of `p⁻¹X` is `E` on the nose, but the two spellings of `Opens` are not
    -- syntactically equal, so the supremum is taken at the `E` one and `change` crosses the seam.
    -- `change` and not `show`: `linter.style.show` together with `--wfail` makes `show` a build
    -- error whenever it moves the goal, which is the whole job here.
    change (⨆ V : ↥(sheetOpens ⇑p), (V : Opens E)) = ⊤
    rw [← sSup_eq_iSup']
    exact hp.sSup_sheetOpens
  · rintro ⟨V, hV⟩
    have hV' : IsOpenEmbedding fun x : V ↦ p x := hV
    have key : HasLocalModels
        ((X.toLocallyRingedSpace.inverseImage p).restrict V.isOpenEmbedding)
        (LocallyRingedSpace.comapAlgMap
          (LocallyRingedSpace.sheetHom X.toLocallyRingedSpace p V hV')
          (X.toLocallyRingedSpace.resAlgMap X.algebraMap
            (LocallyRingedSpace.sheetImage X.toLocallyRingedSpace p V hV'))) := by
      refine HasLocalModels.of_iso
        (LocallyRingedSpace.sheetIso X.toLocallyRingedSpace p V hV') ?_
        (X.hasLocalModels.restrict _)
      rw [LocallyRingedSpace.sheetIso_hom]
      exact isCLinearHom_comapAlgMap _ _
    rwa [comapAlgMap_sheetHom] at key

/-- **The complex analytic space on the source of a local homeomorphism into a complex analytic
space.**

The underlying topological space is `E` on the nose
(`AlgebraicGeometry.LocallyRingedSpace.inverseImage_toTopCat`), the structure sheaf is `p⁻¹𝒪_X`,
and the `ℂ`-algebra structure is `ComplexAnalytic.inverseImageAlgMap`. The hypothesis is a local
homeomorphism and nothing more; a covering map and finite fibres are what make the morphism below
*finite étale* and are not needed for the space to exist. -/
def AnalyticSpace.coveringSpace (hp : IsLocalHomeomorph ⇑p) : AnalyticSpace.{u} :=
  AnalyticSpace.ofHasLocalModels _ _ (hasLocalModels_inverseImage X p hp)

@[simp]
theorem AnalyticSpace.coveringSpace_toLocallyRingedSpace (hp : IsLocalHomeomorph ⇑p) :
    (AnalyticSpace.coveringSpace X p hp).toLocallyRingedSpace =
      X.toLocallyRingedSpace.inverseImage p :=
  rfl

/-- **The morphism of complex analytic spaces carrying a local homeomorphism.**

`AlgebraicGeometry.LocallyRingedSpace.inverseImageHom` with its `ℂ`-linearity, which is
`ComplexAnalytic.isCLinearHom_comapAlgMap` and holds **by definition**: the structure on the
source is the pullback of the structure on the target along this very morphism. -/
def AnalyticSpace.coveringSpaceHom (hp : IsLocalHomeomorph ⇑p) :
    AnalyticSpace.coveringSpace X p hp ⟶ X :=
  ⟨X.toLocallyRingedSpace.inverseImageHom p, isCLinearHom_comapAlgMap _ _⟩

/-- **The underlying map of `ComplexAnalytic.AnalyticSpace.coveringSpaceHom` is `p`**, on the
nose. -/
@[simp]
theorem AnalyticSpace.base_coveringSpaceHom (hp : IsLocalHomeomorph ⇑p) :
    (AnalyticSpace.coveringSpaceHom X p hp).toLRSHom.base = p :=
  rfl

/-- **A local homeomorphism into a complex analytic space is a local isomorphism** for the
structure `ComplexAnalytic.AnalyticSpace.coveringSpace` puts on its source.

Both fields are free. The topological one is the hypothesis, since the underlying map is `p`; the
stalk one is `AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_inverseImageHom`, which holds
for an **arbitrary** continuous map — the stalk of the inverse image at `e` is the stalk of `X` at
`p e` and the stalk map is that identification. So no hypothesis on `p` is used for the stalk
half, and in particular this is not where a covering map would be needed. -/
instance AnalyticSpace.isLocalIso_coveringSpaceHom (hp : IsLocalHomeomorph ⇑p) :
    IsLocalIso (AnalyticSpace.coveringSpaceHom X p hp) where
  isLocalHomeomorph := hp
  isIso_stalkMap _ := LocallyRingedSpace.isIso_stalkMap_inverseImageHom _ _ _

/-- **A covering map with finite fibres into a complex analytic space is finite** for this
structure.

The fibre field is the hypothesis, transported to the class `Finite` by `Set.Finite.to_subtype`;
the closed field is `IsCoveringMap.isClosedMap`, which is where the covering hypothesis is used
and is the only place in this file that it is. -/
theorem AnalyticSpace.isFinite_coveringSpaceHom (hcov : IsCoveringMap ⇑p)
    (hfin : ∀ x : X, (⇑p ⁻¹' {x}).Finite) :
    IsFinite (AnalyticSpace.coveringSpaceHom X p hcov.isLocalHomeomorph) where
  isClosedMap := hcov.isClosedMap hfin
  finite_fiber y := (hfin y).to_subtype

/-- **A covering map with finite fibres into a complex analytic space is finite étale** for the
structure `ComplexAnalytic.AnalyticSpace.coveringSpace` puts on its source.

This is the statement the Riemann existence theorem's analytic side needs: a topological covering
of an analytic space, with finite fibres, *is* an object of the category of finite étale covers.
`Oka/AnalyticSpace/CoveringMap.lean` is the converse at the level of the underlying map, and needs
a separation axiom that this direction does not. -/
theorem AnalyticSpace.isFiniteEtale_coveringSpaceHom (hcov : IsCoveringMap ⇑p)
    (hfin : ∀ x : X, (⇑p ⁻¹' {x}).Finite) :
    IsFiniteEtale (AnalyticSpace.coveringSpaceHom X p hcov.isLocalHomeomorph) where
  isFinite := AnalyticSpace.isFinite_coveringSpaceHom X p hcov hfin
  isLocalIso := inferInstance

end ComplexAnalytic

end

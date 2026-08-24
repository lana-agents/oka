/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Local
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Gluing a complex analytic space out of an open cover by abstract spaces

`ComplexAnalytic.AnalyticSpace.ofOpensCompatible` builds an analytic space from a cover of a
locally ringed space `X` by *open subsets* of `X`. The cover a gluing produces is not of that
shape: the members of an `AlgebraicGeometry.LocallyRingedSpace.OpenCover` — and of an
`AlgebraicGeometry.LocallyRingedSpace.GlueData` — are **arbitrary** locally ringed spaces mapping
into `X` by open immersions. This file bridges the two, and with it a glue data of analytic
pieces glues to an analytic space.

## What the bridge costs, and it is one theorem

Both halves of "is an analytic space" have to cross the identification of a member with the open
subspace on its image:

* the **property** `ComplexAnalytic.HasLocalModels` transports along a `ℂ`-linear isomorphism,
  which is `ComplexAnalytic.HasLocalModels.of_iso` below — the only content in the file. Its
  proof is `ComplexAnalytic.HasLocalModels.of_iSup_eq_top`'s: pull the neighbourhood back along
  the isomorphism, identify the two open subspaces with
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`, and carry the chart across
  with `ComplexAnalytic.IsCutOutBy.comp_iso`;
* the **data** `algebraMap` transports along *any* morphism, by
  `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap`, and no hypothesis is needed for that. What
  the isomorphism buys is that the transport is injective
  (`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_hom_injective`), which is what lets the
  glued structure be *identified* rather than merely constructed.

`ℂ`-linearity of the identification is not a hypothesis anywhere: the structure on the open
subspace is *defined* as the pullback of the structure on the member, so linearity is `rfl`
(`ComplexAnalytic.isCLinearHom_comapAlgMap`). That is the whole reason the file is short.

## The judgement call in `ofGlueData`, since this project has twice named something twice

**There is no bundled glue-data structure for analytic spaces here** — no such declaration
exists, which is why this paragraph does not name one. `ofGlueData` takes an
`AlgebraicGeometry.LocallyRingedSpace.GlueData` together with the analytic structures on its
pieces and their compatibility, and nothing in the development wants those three bundled: the
glue data is what one constructs, and the analytic structures are what one checks afterwards.
Bundling would also force a choice of which of the two spellings of compatibility to fix, and
the one used here — `TopCat.Presheaf.IsCompatible` on the glued space — is the one the sheaf
condition consumes rather than the one a geometric input arrives in. If a caller ever has to
carry the three together, bundle then.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.ofOpenCover`: a locally ringed space with an open cover whose
  members carry compatible analytic structures, as a complex analytic space.
- `ComplexAnalytic.AnalyticSpace.ofGlueData`: the same for the gluing of a glue data, via
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover`.
- `ComplexAnalytic.GlueDataCLinear`: the transitions of a glue data are `ℂ`-linear for the given
  structures on its members — the hypothesis in the form a geometric input arrives in.
- `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear`: `ComplexAnalytic.AnalyticSpace.ofGlueData`
  with that hypothesis in place of the sheaf-condition one.
- `ComplexAnalytic.AnalyticSpace.glueMorphisms`: **a morphism of analytic spaces glued from
  `ℂ`-linear morphisms out of the members of an open cover.** The object-level constructions above
  build the source; this is the morphism-level statement, and it is the first thing a space glued
  out of more than one piece needs.

## Main results

- `ComplexAnalytic.HasLocalModels.of_iso`: **having local models transports along a `ℂ`-linear
  isomorphism.**
- `ComplexAnalytic.IsCLinearHom.eq`: two algebra structures on the source of a morphism which are
  `ℂ`-linear over the same structure on its target are equal.
- `ComplexAnalytic.AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap`: **the glued `ℂ`-algebra
  structure pulls back to the given one on every member of the cover** — the statement that says
  the construction is the right one rather than merely well-typed.
- `ComplexAnalytic.AnalyticSpace.algebraMap_ofOpenCover_comapAlgMap`: on a cover of a space that
  already carries a structure, the gluing returns that structure.
- `ComplexAnalytic.isCompatible_of_glueDataCLinear`: **`ℂ`-linear transitions give
  a compatible family on the gluing** — the step that stood between a glue data and an analytic
  structure on it, and the reason `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` exists.
- `ComplexAnalytic.glueDataCLinear_comapAlgMap` and
  `ComplexAnalytic.AnalyticSpace.algebraMap_ofGlueDataCLinear_comapAlgMap`: the hypothesis is
  automatic when the structures come from the gluing, and in that case the construction returns
  the structure it came from.
- `ComplexAnalytic.IsCLinearHom.of_openCover`: **`ℂ`-linearity is local on the source** — a
  morphism out of a covered space is `ℂ`-linear as soon as its restriction to each member is.
  Nothing is assumed about the morphism, so it applies to one that arrives from a universal
  property rather than from a gluing.
- `ComplexAnalytic.AnalyticSpace.isCLinearHom_glueMorphisms`: **the glued morphism is
  `ℂ`-linear**, which is what makes `ComplexAnalytic.AnalyticSpace.glueMorphisms` possible — the
  previous item at `AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` — and
  `ComplexAnalytic.AnalyticSpace.glueMorphisms_map_comp`: the hypotheses are automatic for the
  restrictions of a single morphism, and the construction returns it.

## What is not here

* **The analytification of a non-affine scheme.** What is missing is no longer a theorem about
  the analytification: `ComplexAnalytic.localisationIso` identifies the analytification of `A_f`
  with `D(f) ⊆ X^an` **over `X^an`**, `ComplexAnalytic.localisationIso_inv_analytificationMap`
  reads that through the functor, and `ComplexAnalytic.isOpenImmersion_localisationProj` supplies
  the `f_open` field of an `AlgebraicGeometry.LocallyRingedSpace.GlueData`. Only the
  **distinguished** case is proved, which is the case a cover of a scheme locally of finite type
  needs; the general open immersion is neither proved nor wanted
  (`Oka/Analytification/DistinguishedOpen.lean` says so). The glue data itself is now built —
  `ComplexAnalytic.coverGlueData` in `Oka/Analytification/AffineCover.lean` — and so is the
  passage from a glue data to an analytic space, below, and the two are put together in
  `OkaTest/AffineCover.lean` and `OkaTest/ProjectiveLine.lean`. The input is still the cover **as
  data** rather than a scheme, since this repository constructs no `AlgebraicGeometry.Scheme`
  beyond Mathlib's `Spec` and has no cover API for one.
* **The analytification of a *morphism* of non-affine spaces.**
  `ComplexAnalytic.AnalyticSpace.glueMorphisms` below now glues a morphism out of a covered
  analytic space, which is the ingredient that was missing; what is still absent is anything that
  produces the pieces from a morphism of presentations covering-wise. Nothing needs it yet.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

/-- **Two `ℂ`-algebra structures on the source of a morphism which are `ℂ`-linear over one and
the same structure on its target are equal.**

`IsCLinearHom i α β` says that `α` *is* `β` pulled back along `i`, so it determines `α`. This is
the uniqueness that makes `ComplexAnalytic.AnalyticSpace.ofOpenCover`'s output identifiable: a
structure recognised as `ℂ`-linear over the ambient one is the restriction of the ambient one,
whatever route produced it. -/
lemma IsCLinearHom.eq {X Y : LocallyRingedSpace.{u}} {i : X ⟶ Y}
    {α α' : ℂ →+* X.presheaf.obj (op ⊤)} {β : ℂ →+* Y.presheaf.obj (op ⊤)}
    (h : IsCLinearHom i α β) (h' : IsCLinearHom i α' β) : α = α' :=
  RingHom.ext fun c ↦ (h c).symm.trans (h' c)

/-- **A pulled-back `ℂ`-algebra structure is `ℂ`-linear**, by definition of
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap`: both sides of `IsCLinearHom` are the same
term. -/
lemma isCLinearHom_comapAlgMap {X Y : LocallyRingedSpace.{u}} (i : X ⟶ Y)
    (β : ℂ →+* Y.presheaf.obj (op ⊤)) :
    IsCLinearHom i (LocallyRingedSpace.comapAlgMap i β) β :=
  fun _ ↦ rfl

/-- **`ℂ`-linearity is local on the source**: a morphism out of a space with an open cover is
`ℂ`-linear as soon as each of its restrictions to a member is, for the structure that member
inherits.

The hypothesis on each member is stated for
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap (𝒰.map j) α`, which is the form in which it
arrives: a member of an `AlgebraicGeometry.LocallyRingedSpace.OpenCover` is an abstract space
mapping in and carries no structure of its own.

`ComplexAnalytic.IsCLinearHom` unfolds to `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap d β`
being `α` — that is `ComplexAnalytic.isCLinearHom_comapAlgMap` and
`ComplexAnalytic.IsCLinearHom.eq` — so the statement is that two algebra structures on the source
agreeing on a cover are equal, which is
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.comapAlgMap_ext`.

**Nothing is assumed about `d`.** In particular it need not be glued from the pieces, and no
agreement of the pieces on the overlaps is required — the pieces here are the restrictions of one
morphism and agree automatically. -/
theorem IsCLinearHom.of_openCover {X Y : LocallyRingedSpace.{u}} (𝒰 : X.OpenCover) {d : X ⟶ Y}
    {α : ℂ →+* X.presheaf.obj (op ⊤)} {β : ℂ →+* Y.presheaf.obj (op ⊤)}
    (h : ∀ j, IsCLinearHom (𝒰.map j ≫ d) (LocallyRingedSpace.comapAlgMap (𝒰.map j) α) β) :
    IsCLinearHom d α β := by
  suffices hd : LocallyRingedSpace.comapAlgMap d β = α from
    fun c ↦ congrArg (fun m : ℂ →+* _ ↦ m c) hd
  refine 𝒰.comapAlgMap_ext fun j ↦ ?_
  rw [← LocallyRingedSpace.comapAlgMap_comp]
  exact ((h j).eq (isCLinearHom_comapAlgMap _ β)).symm

/-- **Pulling the target's structure back along a morphism of *analytic* spaces gives the
source's.**

This is `ComplexAnalytic.AnalyticSpace.Hom.isCLinear` — a field of every morphism of analytic
spaces — restated as an equation of ring homomorphisms rather than as a condition holding at each
constant. That is the form `ComplexAnalytic.GlueDataCLinear` consumes, since it is an equation
between `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap`s, and it is why `ℂ`-linearity costs
nothing for a transition assembled out of analytic morphisms: the algebra was discharged when the
morphisms were built. -/
theorem AnalyticSpace.comapAlgMap_toLRSHom {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) :
    LocallyRingedSpace.comapAlgMap f.toLRSHom Y.algebraMap = X.algebraMap :=
  RingHom.ext f.isCLinear

/-- **Having local models transports along a `ℂ`-linear isomorphism.**

The chart of `X` at `e.hom y` lives on `X|U`; what is wanted is a chart of `Y` at `y`, so the
neighbourhood is pulled back to `U' := e.hom⁻¹ U` and the two open subspaces `Y|U'` and `X|U` are
identified by `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` — they have the
same image in `X`, because `e.hom` is surjective and `U'` is the preimage of `U`. That
identification is `ℂ`-linear by `ComplexAnalytic.IsCLinearHom.of_comp`, since both of its legs
are `ℂ`-linear over `α` on `X`, and `ComplexAnalytic.IsCutOutBy.comp_iso` carries the chart
across it.

This is `ComplexAnalytic.HasLocalModels.of_iSup_eq_top`'s argument with the isomorphism supplied
by hypothesis instead of by a comparison of two restrictions, and it is the only thing between
`ComplexAnalytic.AnalyticSpace.ofOpensCompatible` and a cover by abstract spaces. -/
theorem HasLocalModels.of_iso {X Y : LocallyRingedSpace.{u}} (e : Y ≅ X)
    {α : ℂ →+* X.presheaf.obj (op ⊤)} {β : ℂ →+* Y.presheaf.obj (op ⊤)}
    (he : IsCLinearHom e.hom β α) (h : HasLocalModels X α) : HasLocalModels Y β := by
  intro y
  obtain ⟨U, n, k, V, c, f, hcut, hlin⟩ := h (e.hom.base y)
  set U' : Opens Y := (Opens.map e.hom.base).obj U.1 with hU'
  have hyU' : y ∈ U' := U.2
  have hrange : Set.range (Y.ofRestrict U'.isOpenEmbedding ≫ e.hom).base =
      Set.range (X.ofRestrict U.1.isOpenEmbedding).base := by
    rw [X.range_ofRestrict, show ⇑(Y.ofRestrict U'.isOpenEmbedding ≫ e.hom).base =
      ⇑e.hom.base ∘ ⇑(Y.ofRestrict U'.isOpenEmbedding).base from rfl, Set.range_comp,
      Y.range_ofRestrict]
    exact Set.image_preimage_eq _ (LocallyRingedSpace.homeoOfIso e).surjective
  set e' := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hrange with he'
  have hlin' : IsCLinearHom e'.hom (Y.resAlgMap β U') (X.resAlgMap α U.1) :=
    IsCLinearHom.of_comp
      (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange)
      ((isCLinearHom_ofRestrict Y β U').comp he)
      (isCLinearHom_ofRestrict X α U.1)
  exact ⟨⟨U', hyU'⟩, n, k, V, e'.hom ≫ c, f, hcut.comp_iso e', hlin'.comp hlin⟩

/-- **The transitions of a glue data are `ℂ`-linear**, as a condition on the given structures:
the two structures the overlap `V (i, j)` inherits — from the `i`-th member and, through the
transition, from the `j`-th — agree.

This is `ComplexAnalytic.IsCLinearHom` of the transition `t i j`, unfolded through
`AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp`, and it is the form in which a geometric
input arrives: one is given an isomorphism of the two descriptions of an overlap and knows it is
an isomorphism *of `ℂ`-algebras*. -/
def GlueDataCLinear (D : LocallyRingedSpace.GlueData.{u})
    (α : ∀ j, ℂ →+* (D.U j).presheaf.obj (op ⊤)) : Prop :=
  ∀ i j, LocallyRingedSpace.comapAlgMap (D.f i j) (α i) =
    LocallyRingedSpace.comapAlgMap (D.t i j ≫ D.f j i) (α j)

/-- **`ComplexAnalytic.GlueDataCLinear` is `ℂ`-linearity of the transitions.** -/
theorem glueDataCLinear_iff (D : LocallyRingedSpace.GlueData.{u})
    (α : ∀ j, ℂ →+* (D.U j).presheaf.obj (op ⊤)) :
    GlueDataCLinear D α ↔ ∀ i j, IsCLinearHom (D.t i j)
      (LocallyRingedSpace.comapAlgMap (D.f i j) (α i))
      (LocallyRingedSpace.comapAlgMap (D.f j i) (α j)) := by
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  rw [LocallyRingedSpace.comapAlgMap_comp]
  exact ⟨fun h c ↦ congrArg (fun m : ℂ →+* _ ↦ m c) h.symm,
    fun h ↦ RingHom.ext fun c ↦ (h c).symm⟩

/-- **`ℂ`-linear transitions give a compatible family on the gluing.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap` with `ℂ` lifted into
the universe of the spaces. The lift is forced and is not a choice: that lemma's proof goes
through `Spec R`, so `R` has to live where the spaces do, while `ℂ` is in `Type 0` whatever the
universe of the spaces is. **Nothing is computed by the lift** — `α` composed with
`ULift.ringEquiv` takes the same values, so the two families of sections are the same terms and
the two compatibility conditions are the same proposition, which is why the proof ends in
`exact` and not in a transport. -/
theorem isCompatible_of_glueDataCLinear (D : LocallyRingedSpace.GlueData.{u})
    (α : ∀ j, ℂ →+* (D.U j).presheaf.obj (op ⊤)) (hα : GlueDataCLinear D α) (c : ℂ) :
    TopCat.Presheaf.IsCompatible D.toGlueData.glued.presheaf
      (fun j ↦ (D.openCover.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun j ↦ D.openCover.restrictAlgMap j (α j) c := by
  have H := D.isCompatible_restrictAlgMap (R := ULift.{u} ℂ)
    (fun j ↦ (α j).comp (ULift.ringEquiv : ULift.{u} ℂ ≃+* ℂ).toRingHom)
    (fun i j ↦ RingHom.ext fun x ↦ congrArg (fun m : ℂ →+* _ ↦ m x.down) (hα i j))
    (ULift.up c)
  exact H

/-- **Structures pulled back from the gluing have `ℂ`-linear transitions**, so the hypothesis of
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` is satisfied whenever there is an ambient
structure to begin with.

The proof is the glue data's own `glue_condition`, `f i j ≫ ι i = (t i j ≫ f j i) ≫ ι j`, read
through `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_comp`. This is the analogue for glue
data of `AlgebraicGeometry.LocallyRingedSpace.OpenCover.isCompatible_restrictAlgMap_comapAlgMap`,
and with the round trip below it is what says the construction is not vacuous: the hypothesis is
not merely satisfiable, it is *automatic* in the case where the answer is already known, and in
that case the construction returns it. -/
theorem glueDataCLinear_comapAlgMap (D : LocallyRingedSpace.GlueData.{u})
    (γ : ℂ →+* D.toGlueData.glued.presheaf.obj (op ⊤)) :
    GlueDataCLinear D fun j ↦ LocallyRingedSpace.comapAlgMap (D.toGlueData.ι j) γ := by
  intro i j
  rw [← LocallyRingedSpace.comapAlgMap_comp, ← LocallyRingedSpace.comapAlgMap_comp,
    Category.assoc, D.glue_condition i j]

namespace AnalyticSpace

variable {X : LocallyRingedSpace.{u}} (𝒰 : X.OpenCover)
  (α : ∀ j, ℂ →+* (𝒰.obj j).presheaf.obj (op ⊤))
  (hα : ∀ c : ℂ, TopCat.Presheaf.IsCompatible X.presheaf
    (fun j ↦ (𝒰.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
    fun j ↦ 𝒰.restrictAlgMap j (α j) c)
  (h : ∀ j, HasLocalModels (𝒰.obj j) (α j))

/-- **A locally ringed space with an open cover whose members are analytic, with compatible
`ℂ`-algebra structures, is a complex analytic space.**

`ComplexAnalytic.AnalyticSpace.ofOpensCompatible` is this for a cover by open *subsets*; here the
members are arbitrary spaces mapping in by open immersions, which is the shape a gluing produces.
Each member is identified with the open subspace on its image
(`AlgebraicGeometry.LocallyRingedSpace.OpenCover.isoRestrict`), its `ℂ`-algebra structure is
carried across (`…OpenCover.restrictAlgMap`), and `ComplexAnalytic.HasLocalModels.of_iso` carries
the charts.

The compatibility hypothesis is `TopCat.Presheaf.IsCompatible` on the *carried* structures,
indexed by `(𝒰.opensRange j).functor.obj ⊤` rather than by `𝒰.opensRange j`. That is the indexing
in which `AlgebraicGeometry.LocallyRingedSpace.glueAlgMapRestrict` needs no transport, and it is
the only place in this file where the `functor.obj ⊤`-versus-`U` seam is visible. -/
def ofOpenCover : AnalyticSpace.{u} :=
  AnalyticSpace.ofOpens X
    (LocallyRingedSpace.glueAlgMapRestrict 𝒰.iSup_opensRange (fun j ↦ 𝒰.restrictAlgMap j (α j)) hα)
    𝒰.opensRange 𝒰.iSup_opensRange fun j ↦ by
      rw [LocallyRingedSpace.resAlgMap_glueAlgMapRestrict]
      exact (h j).of_iso (𝒰.isoRestrict j) (isCLinearHom_comapAlgMap _ _)

@[simp]
lemma ofOpenCover_toLocallyRingedSpace :
    (ofOpenCover 𝒰 α hα h).toLocallyRingedSpace = X :=
  rfl

/-- **The glued `ℂ`-algebra structure pulls back to the given one on every member of the
cover.**

This is the statement that the construction is the intended one, and it is the form the
`OpenCover` setting asks for: there is no restriction map to compare against, because a member is
not an open subset of `X`, so what is compared is the pullback along `𝒰.map j`. It is proved by
applying `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap_hom_injective` to the identification
of the member with the open subspace on its image, where the two sides become
`resAlgMap` of the gluing and the carried structure, and those agree by
`AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMapRestrict`. -/
lemma comapAlgMap_ofOpenCover_algebraMap (j : 𝒰.J) :
    LocallyRingedSpace.comapAlgMap (𝒰.map j) (ofOpenCover 𝒰 α hα h).algebraMap = α j :=
  LocallyRingedSpace.comapAlgMap_hom_injective (𝒰.isoRestrict j) <| by
    change 𝒰.restrictAlgMap j (LocallyRingedSpace.comapAlgMap (𝒰.map j)
      (ofOpenCover 𝒰 α hα h).algebraMap) = 𝒰.restrictAlgMap j (α j)
    rw [LocallyRingedSpace.OpenCover.restrictAlgMap_comapAlgMap]
    exact LocallyRingedSpace.resAlgMap_glueAlgMapRestrict 𝒰.iSup_opensRange
      (fun j ↦ 𝒰.restrictAlgMap j (α j)) hα j

/-- **On a cover of a space that already carries a `ℂ`-algebra structure, gluing the induced
structures returns it.**

The round trip, and the form in which `ComplexAnalytic.AnalyticSpace.ofOpenCover` is checkable:
the compatibility hypothesis comes for free
(`AlgebraicGeometry.LocallyRingedSpace.OpenCover.isCompatible_restrictAlgMap_comapAlgMap`) and
the conclusion is
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueAlgMapRestrict_comapAlgMap`,
which holds by the uniqueness half of the sheaf condition.

Note what it does *not* assume: nothing about the members being restrictions of `X`. It applies
verbatim to the gluing of a glue data, where `γ` is a structure on the glued space — which is how
`ComplexAnalytic.AnalyticSpace.ofGlueData` gets tested at all. -/
theorem algebraMap_ofOpenCover_comapAlgMap (γ : ℂ →+* X.presheaf.obj (op ⊤))
    (hγ : ∀ j, HasLocalModels (𝒰.obj j) (LocallyRingedSpace.comapAlgMap (𝒰.map j) γ)) :
    (ofOpenCover 𝒰 (fun j ↦ LocallyRingedSpace.comapAlgMap (𝒰.map j) γ)
      (𝒰.isCompatible_restrictAlgMap_comapAlgMap γ) hγ).algebraMap = γ :=
  𝒰.glueAlgMapRestrict_comapAlgMap γ

/-- **The gluing of a glue data of locally ringed spaces whose pieces are complex analytic
spaces, with compatible `ℂ`-algebra structures, is a complex analytic space.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover` says the pieces of a glue data are an
open cover of the gluing, and this is `ComplexAnalytic.AnalyticSpace.ofOpenCover` at that cover.
Nothing further is checked: `ι_isOpenImmersion` and `ι_jointly_surjective` are Mathlib's, and the
transport of the analytic structure is the content of this file.

See the module docstring on why there is no bundled glue-data structure for analytic spaces. -/
def ofGlueData (D : LocallyRingedSpace.GlueData.{u})
    (α : ∀ j, ℂ →+* (D.U j).presheaf.obj (op ⊤))
    (hα : ∀ c : ℂ, TopCat.Presheaf.IsCompatible D.toGlueData.glued.presheaf
      (fun j ↦ (D.openCover.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun j ↦ D.openCover.restrictAlgMap j (α j) c)
    (h : ∀ j, HasLocalModels (D.U j) (α j)) : AnalyticSpace.{u} :=
  ofOpenCover D.openCover α hα h

/-- **The gluing of a glue data of analytic pieces whose transitions are `ℂ`-linear is a complex
analytic space.**

`ComplexAnalytic.AnalyticSpace.ofGlueData` asks for `TopCat.Presheaf.IsCompatible` on the
**glued** space, which is the spelling the sheaf condition consumes and not the one a geometric
input arrives in; this is the same construction with the hypothesis in the geometric form, and
`AlgebraicGeometry.LocallyRingedSpace.GlueData.isCompatible_restrictAlgMap` is what converts it.

That conversion is the whole content and it is not bookkeeping: the sheaf-condition form asks for
agreement of sections over the *images* of the members in the gluing, and nothing pulls those
back to the overlaps until an ambient structure exists — which is what has to be built. -/
def ofGlueDataCLinear (D : LocallyRingedSpace.GlueData.{u})
    (α : ∀ j, ℂ →+* (D.U j).presheaf.obj (op ⊤)) (hα : GlueDataCLinear D α)
    (h : ∀ j, HasLocalModels (D.U j) (α j)) : AnalyticSpace.{u} :=
  ofGlueData D α (isCompatible_of_glueDataCLinear D α hα) h

@[simp]
lemma ofGlueDataCLinear_toLocallyRingedSpace (D : LocallyRingedSpace.GlueData.{u})
    (α : ∀ j, ℂ →+* (D.U j).presheaf.obj (op ⊤)) (hα : GlueDataCLinear D α)
    (h : ∀ j, HasLocalModels (D.U j) (α j)) :
    (ofGlueDataCLinear D α hα h).toLocallyRingedSpace = D.toGlueData.glued :=
  rfl

/-- **The glued `ℂ`-algebra structure pulls back to the given one on every member**, which is the
statement that `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` is the intended construction
rather than merely a well-typed one.

`ComplexAnalytic.AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap` at
`AlgebraicGeometry.LocallyRingedSpace.GlueData.openCover`, whose `map j` is the inclusion
`ι j` of the `j`-th member into the gluing. -/
lemma comapAlgMap_ofGlueDataCLinear_algebraMap (D : LocallyRingedSpace.GlueData.{u})
    (α : ∀ j, ℂ →+* (D.U j).presheaf.obj (op ⊤)) (hα : GlueDataCLinear D α)
    (h : ∀ j, HasLocalModels (D.U j) (α j)) (j : D.J) :
    LocallyRingedSpace.comapAlgMap (D.toGlueData.ι j)
      (ofGlueDataCLinear D α hα h).algebraMap = α j :=
  comapAlgMap_ofOpenCover_algebraMap D.openCover α _ h j

/-- **On a glue data whose gluing already carries a `ℂ`-algebra structure, the construction
returns it.**

The round trip, and the form in which `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` is
checkable: the `ℂ`-linearity hypothesis is free
(`ComplexAnalytic.glueDataCLinear_comapAlgMap`) and the conclusion is
`ComplexAnalytic.AnalyticSpace.algebraMap_ofOpenCover_comapAlgMap`, whose own docstring says it
applies verbatim to the gluing of a glue data — this is that application. -/
theorem algebraMap_ofGlueDataCLinear_comapAlgMap (D : LocallyRingedSpace.GlueData.{u})
    (γ : ℂ →+* D.toGlueData.glued.presheaf.obj (op ⊤))
    (h : ∀ j, HasLocalModels (D.U j)
      (LocallyRingedSpace.comapAlgMap (D.toGlueData.ι j) γ)) :
    (ofGlueDataCLinear D (fun j ↦ LocallyRingedSpace.comapAlgMap (D.toGlueData.ι j) γ)
      (glueDataCLinear_comapAlgMap D γ) h).algebraMap = γ :=
  algebraMap_ofOpenCover_comapAlgMap D.openCover γ h

@[simp]
lemma ofGlueData_toLocallyRingedSpace (D : LocallyRingedSpace.GlueData.{u})
    (α : ∀ j, ℂ →+* (D.U j).presheaf.obj (op ⊤))
    (hα : ∀ c : ℂ, TopCat.Presheaf.IsCompatible D.toGlueData.glued.presheaf
      (fun j ↦ (D.openCover.opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun j ↦ D.openCover.restrictAlgMap j (α j) c)
    (h : ∀ j, HasLocalModels (D.U j) (α j)) :
    (ofGlueData D α hα h).toLocallyRingedSpace = D.toGlueData.glued :=
  rfl

/-! ### Gluing a morphism

`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` glues morphisms of locally ringed
spaces out of the members of an open cover. What it does not give is the `ℂ`-linearity of the
result, and that is not formal: `ComplexAnalytic.IsCLinearHom` is a condition on **global**
sections, while each piece gives it only after restriction to its member.

**The second gluing that closes the gap is already written.** The two structures to be compared
are `AlgebraicGeometry.LocallyRingedSpace.comapAlgMap` of the morphism and `X.algebraMap`; they
agree after pullback along every `𝒰.map j`, and
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.comapAlgMap_ext` — an algebra structure is
determined by its pullbacks to the members — turns "agree on the cover" into "equal". So no sheaf
argument is written here; the one written for the object-level gluing is reused.
**`ComplexAnalytic.IsCLinearHom.of_comp`, which has discharged every other `ℂ`-linearity
obligation in this development, does *not* apply**: it wants a factorisation through a common
target, and here the cover is on the *source*.

**And none of it is about a glued morphism.** `ComplexAnalytic.IsCLinearHom.of_openCover` says
`ℂ`-linearity is local on the source for an **arbitrary** morphism out of a covered space;
`ComplexAnalytic.AnalyticSpace.isCLinearHom_glueMorphisms` is that lemma at
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms`, and is two lines. The
generality is not decoration: a morphism out of a space that happens to be covered — a
coproduct's descent map, say — arrives from a universal property rather than from
`glueMorphisms`, and it carries no agreement-on-overlaps hypothesis to hand over. `of_openCover`
does not ask for one, which is the whole difference between the two statements.
-/

/-- **The morphism glued from `ℂ`-linear pieces is `ℂ`-linear.**

`ComplexAnalytic.IsCLinearHom.of_openCover` at
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms`, whose restriction to the `j`-th
member is `f j` by `AlgebraicGeometry.LocallyRingedSpace.OpenCover.ι_glueMorphisms`. The `hf`
hypothesis is consumed by the gluing of the underlying morphisms and plays no part in the
`ℂ`-linearity. -/
theorem isCLinearHom_glueMorphisms {X Y : AnalyticSpace.{u}}
    (𝒰 : X.toLocallyRingedSpace.OpenCover) (f : ∀ j, 𝒰.obj j ⟶ Y.toLocallyRingedSpace)
    (hf : ∀ x y, Limits.pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      Limits.pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y)
    (hlin : ∀ j, IsCLinearHom (f j)
      (LocallyRingedSpace.comapAlgMap (𝒰.map j) X.algebraMap) Y.algebraMap) :
    IsCLinearHom (𝒰.glueMorphisms f hf) X.algebraMap Y.algebraMap :=
  IsCLinearHom.of_openCover 𝒰 fun j ↦ by
    rw [𝒰.ι_glueMorphisms f hf j]
    exact hlin j

/-- **A morphism of complex analytic spaces glued from `ℂ`-linear morphisms out of the members of
an open cover of its source.**

The underlying morphism is `AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms`; the
content of this definition is the field, which is
`ComplexAnalytic.AnalyticSpace.isCLinearHom_glueMorphisms`. -/
def glueMorphisms {X Y : AnalyticSpace.{u}} (𝒰 : X.toLocallyRingedSpace.OpenCover)
    (f : ∀ j, 𝒰.obj j ⟶ Y.toLocallyRingedSpace)
    (hf : ∀ x y, Limits.pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      Limits.pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y)
    (hlin : ∀ j, IsCLinearHom (f j)
      (LocallyRingedSpace.comapAlgMap (𝒰.map j) X.algebraMap) Y.algebraMap) : X ⟶ Y :=
  ⟨𝒰.glueMorphisms f hf, isCLinearHom_glueMorphisms 𝒰 f hf hlin⟩

/-- The underlying morphism of locally ringed spaces of
`ComplexAnalytic.AnalyticSpace.glueMorphisms`. -/
lemma toLRSHom_glueMorphisms {X Y : AnalyticSpace.{u}} (𝒰 : X.toLocallyRingedSpace.OpenCover)
    (f : ∀ j, 𝒰.obj j ⟶ Y.toLocallyRingedSpace)
    (hf : ∀ x y, Limits.pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      Limits.pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y)
    (hlin : ∀ j, IsCLinearHom (f j)
      (LocallyRingedSpace.comapAlgMap (𝒰.map j) X.algebraMap) Y.algebraMap) :
    (glueMorphisms 𝒰 f hf hlin).toLRSHom = 𝒰.glueMorphisms f hf :=
  rfl

/-- **It restricts to the given morphism on each member**, which is what a caller consumes.
Uniqueness is `AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms` at the
locally-ringed-space level and needs no `ℂ`-linear version:
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful, so a morphism of analytic
spaces is determined by its underlying one. -/
lemma ι_glueMorphisms {X Y : AnalyticSpace.{u}} (𝒰 : X.toLocallyRingedSpace.OpenCover)
    (f : ∀ j, 𝒰.obj j ⟶ Y.toLocallyRingedSpace)
    (hf : ∀ x y, Limits.pullback.fst (𝒰.map x) (𝒰.map y) ≫ f x =
      Limits.pullback.snd (𝒰.map x) (𝒰.map y) ≫ f y)
    (hlin : ∀ j, IsCLinearHom (f j)
      (LocallyRingedSpace.comapAlgMap (𝒰.map j) X.algebraMap) Y.algebraMap) (j : 𝒰.J) :
    𝒰.map j ≫ (glueMorphisms 𝒰 f hf hlin).toLRSHom = f j :=
  𝒰.ι_glueMorphisms f hf j

/-- **The `ℂ`-linearity hypothesis is automatic for the restrictions of a single morphism.**

`ComplexAnalytic.AnalyticSpace.comapAlgMap_toLRSHom` is the whole content: the structure a member
inherits from `X` is what `φ` pulls back from `Y`. This is the analogue for morphisms of
`ComplexAnalytic.glueDataCLinear_comapAlgMap`. -/
theorem isCLinearHom_map_comp {X Y : AnalyticSpace.{u}} (𝒰 : X.toLocallyRingedSpace.OpenCover)
    (φ : X ⟶ Y) (j : 𝒰.J) :
    IsCLinearHom (𝒰.map j ≫ φ.toLRSHom)
      (LocallyRingedSpace.comapAlgMap (𝒰.map j) X.algebraMap) Y.algebraMap := fun c ↦
  congrArg (fun m : ℂ →+* _ ↦ m c)
    ((LocallyRingedSpace.comapAlgMap_comp (𝒰.map j) φ.toLRSHom Y.algebraMap).trans
      (congrArg (LocallyRingedSpace.comapAlgMap (𝒰.map j)) (comapAlgMap_toLRSHom φ)))

/-- **And in that case the construction returns the morphism it came from** — the round trip, and
what says the output is the intended one rather than merely well-typed. Together with
`ComplexAnalytic.AnalyticSpace.isCLinearHom_map_comp` it says the hypotheses are not merely
satisfiable but automatic where the answer is already known. -/
theorem glueMorphisms_map_comp {X Y : AnalyticSpace.{u}}
    (𝒰 : X.toLocallyRingedSpace.OpenCover) (φ : X ⟶ Y)
    (hf : ∀ x y, Limits.pullback.fst (𝒰.map x) (𝒰.map y) ≫ (𝒰.map x ≫ φ.toLRSHom) =
      Limits.pullback.snd (𝒰.map x) (𝒰.map y) ≫ (𝒰.map y ≫ φ.toLRSHom)) :
    glueMorphisms 𝒰 (fun j ↦ 𝒰.map j ≫ φ.toLRSHom) hf (isCLinearHom_map_comp 𝒰 φ) = φ :=
  forgetToLocallyRingedSpace.map_injective
    (𝒰.hom_ext _ _ fun j ↦ 𝒰.ι_glueMorphisms _ hf j)

end AnalyticSpace

end ComplexAnalytic

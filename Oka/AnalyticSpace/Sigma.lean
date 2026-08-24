/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Glue
import Oka.Geometry.RingedSpace.LocallyRingedSpace.HasColimits

/-!
# The disjoint union of a family of complex analytic spaces

`ComplexAnalytic.AnalyticSpace.ofOpenCover` builds an analytic space from a cover of a locally
ringed space by abstract spaces mapping in by open immersions. The inclusions of a coproduct are
such a cover — `AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover` — so a disjoint union of
analytic spaces is one application of it, once its compatibility hypothesis is discharged.

**That hypothesis is the whole of the work, and disjointness is the whole of the hypothesis.**
`ComplexAnalytic.AnalyticSpace.ofOpenCover` asks for `TopCat.Presheaf.IsCompatible`: the
`ℂ`-algebra structures carried from the members must agree on the pairwise intersections of the
members' images. For a coproduct those intersections are `⊥` for `i ≠ j`
(`AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover`), and the sections of a
sheaf over `⊥` form the terminal ring, so any two of them agree; for `i = j` the two restrictions
are the same map. There is no analysis and no sheaf argument in it.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.sigma`: **the disjoint union**, whose underlying locally ringed
  space is the coproduct on the nose.
- `ComplexAnalytic.AnalyticSpace.sigmaι`: the inclusion of a member, as a morphism of analytic
  spaces.
- `ComplexAnalytic.AnalyticSpace.sigmaDesc`: the morphism out of a disjoint union determined by a
  morphism out of each member.

## Main results

- `ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma`: **the disjoint union's `ℂ`-algebra structure
  pulls back to each member's own**, which is what says the object is the disjoint union and not
  an unrelated space with the right carrier.
- `ComplexAnalytic.isCLinearHom_sigmaDesc`: **a descent map out of a coproduct is `ℂ`-linear as
  soon as its restrictions are**, with no agreement-on-overlaps hypothesis.
- `ComplexAnalytic.AnalyticSpace.isEmpty_sigma` and
  `ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base`: the two non-vacuity statements, at
  the two ends.

## Why the descent map needs a lemma at all

`ComplexAnalytic.AnalyticSpace.Hom` carries an `IsCLinearHom` field, and the universal property of
the coproduct in `AlgebraicGeometry.LocallyRingedSpace` does not supply it: it produces a morphism
of locally ringed spaces and nothing more. `ComplexAnalytic.IsCLinearHom.of_openCover` says
`ℂ`-linearity is local on the source and asks for **no** agreement of the pieces on the overlaps —
which is exactly why it applies here, where the map arrives from a universal property rather than
from `AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms` and so carries no such
hypothesis to hand over.

## Two seams, both recorded because neither is visible from the statements

**State the round trip at `(sigmaCover F).map j`, not at `Sigma.ι`.** The two are equal by `rfl`
but not reducibly so, and `j` is bound at `(sigmaCover F).J` rather than at `ι`.

**Supply `ComplexAnalytic.AnalyticSpace.comapAlgMap_ofOpenCover_algebraMap`'s arguments
explicitly.** With `_`s the unifier works backwards from the goal into the coproduct and does not
come back: elaboration fails with a `whnf` timeout that survives `maxHeartbeats 2000000`. Naming
the cover, the family, the compatibility and the local models makes the same proof elaborate in
seconds. Nothing about the statement is at fault — `#check` on it is instant.

## What is not here

**No `CategoryTheory.Limits.IsColimit`.** The object, the inclusions and one descent map are
what a consumer needs; the universal property as a colimit is a separate decision and nothing
consumes one.

**Nothing about `ComplexAnalytic.AnalyticSpace.IsFinite` or
`ComplexAnalytic.AnalyticSpace.IsLocalIso`** for the inclusions or for `∐_{Fin n} X ⟶ X`, and no
count of sheets. Those need the fibres of the descent map and are not touched here.

**No claim that the disjoint union is not one of its members** beyond
`ComplexAnalytic.AnalyticSpace.not_surjective_sigmaι_base`, which is about the *inclusion* being
non-surjective on points at a two-member family with the other member inhabited. That an analytic
space is not *isomorphic* to another is a statement about an invariant and nothing here computes
one.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.LocallyRingedSpace TopologicalSpace

universe u

namespace ComplexAnalytic

noncomputable section

variable {ι : Type u} (F : ι → AnalyticSpace.{u})

namespace AnalyticSpace

/-- **The inclusions of a family of analytic spaces are an open cover of their coproduct**, taken
in `AlgebraicGeometry.LocallyRingedSpace`. This is
`AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover` at the underlying spaces, named because
every statement below is indexed by it. -/
def sigmaCover : (∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).OpenCover :=
  sigmaOpenCover fun i ↦ (F i).toLocallyRingedSpace

@[simp]
lemma sigmaCover_obj (j : ι) : (sigmaCover F).obj j = (F j).toLocallyRingedSpace := rfl

/-- **The `ℂ`-algebra structures of the members are compatible on the coproduct.**

The hypothesis of `ComplexAnalytic.AnalyticSpace.ofOpenCover`, and the only thing between a
coproduct of analytic spaces and an analytic space. For `i = j` the two restrictions are the same
morphism of `TopologicalSpace.Opens`, which is a proposition-valued category, so the two sides are
the same term. For `i ≠ j` the intersection of the two members' images is `⊥`, by
`AlgebraicGeometry.LocallyRingedSpace.disjoint_opensRange_sigmaOpenCover` and `disjoint_iff`, and
the sections of a sheaf over `⊥` are a terminal ring — `TopCat.Sheaf.isTerminalOfEqEmpty` and
`CommRingCat.subsingleton_of_isTerminal` — so *any* two of them agree and nothing about the
structures is used. -/
theorem isCompatible_sigma (c : ℂ) :
    TopCat.Presheaf.IsCompatible
      (∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).presheaf
      (fun j ↦ ((sigmaCover F).opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)
      fun j ↦ (sigmaCover F).restrictAlgMap j (F j).algebraMap c := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · have hd : ((sigmaCover F).opensRange i) ⊓ ((sigmaCover F).opensRange j) = ⊥ :=
      disjoint_iff.mp (disjoint_opensRange_sigmaOpenCover _ hij)
    have hbot : (((sigmaCover F).opensRange i).isOpenEmbedding.isOpenMap.functor.obj ⊤) ⊓
        (((sigmaCover F).opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤) = ⊥ := by
      simpa using hd
    haveI : Subsingleton
        ((∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).presheaf.obj (op
          ((((sigmaCover F).opensRange i).isOpenEmbedding.isOpenMap.functor.obj ⊤) ⊓
            (((sigmaCover F).opensRange j).isOpenEmbedding.isOpenMap.functor.obj ⊤)))) :=
      CommRingCat.subsingleton_of_isTerminal
        ((∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).sheaf.isTerminalOfEqEmpty
          hbot)
    exact Subsingleton.elim _ _

/-- **The disjoint union of a family of complex analytic spaces.**

`ComplexAnalytic.AnalyticSpace.ofOpenCover` at the coproduct's own open cover, with each member's
`ℂ`-algebra structure and each member's local models. Its underlying locally ringed space is the
coproduct on the nose, which is
`ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace` below. -/
def sigma : AnalyticSpace.{u} :=
  ofOpenCover (sigmaCover F) (fun j ↦ (F j).algebraMap) (isCompatible_sigma F)
    fun j ↦ (F j).hasLocalModels

@[simp]
lemma sigma_toLocallyRingedSpace :
    (sigma F).toLocallyRingedSpace = ∐ fun i ↦ (F i).toLocallyRingedSpace := rfl

/-- **The disjoint union's `ℂ`-algebra structure pulls back to each member's own.**

This is the statement that `ComplexAnalytic.AnalyticSpace.sigma` is the disjoint union rather than
some other analytic space with the right carrier, and it is what makes the inclusions `ℂ`-linear.

**Stated at `(sigmaCover F).map j` and not at `Sigma.ι`**: the two are equal by `rfl` and not
reducibly, and `j` is bound at `(sigmaCover F).J`. -/
theorem comapAlgMap_sigma (j : ι) :
    comapAlgMap ((sigmaCover F).map j) (sigma F).algebraMap = (F j).algebraMap :=
  comapAlgMap_ofOpenCover_algebraMap (sigmaCover F) (fun j ↦ (F j).algebraMap)
    (isCompatible_sigma F) (fun j ↦ (F j).hasLocalModels) j

/-- **The inclusion of a member into the disjoint union**, as a morphism of analytic spaces.

Its underlying morphism of locally ringed spaces is the coproduct inclusion, and its
`ℂ`-linearity is `ComplexAnalytic.AnalyticSpace.comapAlgMap_sigma` read elementwise. -/
def sigmaι (j : ι) : F j ⟶ sigma F where
  toLRSHom' := (sigmaCover F).map j
  isCLinear c := congrArg (fun m : ℂ →+* _ ↦ m c) (comapAlgMap_sigma F j)

@[simp]
lemma sigmaι_toLRSHom (j : ι) :
    (sigmaι F j).toLRSHom = Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) j := rfl

end AnalyticSpace

/-- **A morphism out of a coproduct is `ℂ`-linear as soon as its restrictions to the members
are**, with no agreement of the restrictions on the overlaps required.

`ComplexAnalytic.IsCLinearHom.of_openCover` at
`AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover`. The generality of that lemma is what makes
this possible: a descent map arrives from the universal property of the coproduct, not from
`AlgebraicGeometry.LocallyRingedSpace.OpenCover.glueMorphisms`, and so carries no
agreement-on-overlaps hypothesis to hand over.

The step is stated as a `have … := Sigma.ι_desc …` and used by `▸` rather than by `rw`: `i` is
bound at `(sigmaOpenCover _).J`, so the goal presents `(sigmaOpenCover _).map i ≫ Sigma.desc g`
and `rw [Sigma.ι_desc]` reports *"did not find an occurrence"*. -/
theorem isCLinearHom_sigmaDesc {Y : LocallyRingedSpace.{u}}
    (g : ∀ i, (F i).toLocallyRingedSpace ⟶ Y)
    {α : ℂ →+* (∐ fun i ↦ (F i).toLocallyRingedSpace : LocallyRingedSpace.{u}).presheaf.obj (op ⊤)}
    {β : ℂ →+* Y.presheaf.obj (op ⊤)}
    (h : ∀ i, IsCLinearHom (g i)
      (comapAlgMap (Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) i) α) β) :
    IsCLinearHom (Sigma.desc g) α β :=
  IsCLinearHom.of_openCover (AnalyticSpace.sigmaCover F) fun i ↦ by
    have e : (AnalyticSpace.sigmaCover F).map i ≫ Sigma.desc g = g i := Sigma.ι_desc g i
    exact e ▸ h i

namespace AnalyticSpace

/-- **The morphism out of a disjoint union determined by a morphism out of each member.**

The coproduct's descent map, with its `ℂ`-linearity supplied by
`ComplexAnalytic.isCLinearHom_sigmaDesc`. -/
def sigmaDesc {Y : AnalyticSpace.{u}} (g : ∀ i, F i ⟶ Y) : sigma F ⟶ Y where
  toLRSHom' := Sigma.desc fun i ↦ (g i).toLRSHom
  isCLinear := isCLinearHom_sigmaDesc F (fun i ↦ (g i).toLRSHom) fun i ↦ by
    have e : comapAlgMap (Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) i)
        (sigma F).algebraMap = (F i).algebraMap := comapAlgMap_sigma F i
    exact e ▸ (g i).isCLinear

@[simp]
lemma sigmaι_sigmaDesc {Y : AnalyticSpace.{u}} (g : ∀ i, F i ⟶ Y) (j : ι) :
    sigmaι F j ≫ sigmaDesc F g = g j :=
  forgetToLocallyRingedSpace.map_injective (Sigma.ι_desc (fun i ↦ (g i).toLRSHom) j)

/-! ### Non-vacuity, at the two ends -/

/-- **The disjoint union of the empty family is empty.**

The reading this closes is at the bottom end: a construction that returned some fixed space for
every family would satisfy everything above. Every point of a coproduct is in the image of some
member (`AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq`) and there are no members,
so the carrier is empty. **This is also the only place in this repository that names the empty
analytic space**, and it names it as a property rather than as a definition. -/
theorem isEmpty_sigma [IsEmpty ι] : IsEmpty (sigma F) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨i, _, _⟩ := exists_sigma_ι_base_eq (fun i ↦ (F i).toLocallyRingedSpace) x
  exact IsEmpty.elim ‹IsEmpty ι› i

/-- **With a second member that has a point, an inclusion is not surjective**, so the disjoint
union is not the member in disguise.

The reading this closes is at the top end, and it needs both hypotheses: at a one-member family
the inclusion *is* surjective, and at a family whose other members are empty it is surjective
again. `AlgebraicGeometry.LocallyRingedSpace.eq_of_sigmaι_base_eq` is the whole proof — a point of
the `j`-th member cannot be in the image of the `i`-th.

Note what it is not: two analytic spaces with different carriers can still be isomorphic to a
third, and this says nothing about `ComplexAnalytic.AnalyticSpace.sigma F` being non-isomorphic to
`F i`. That is a statement about an invariant and nothing here computes one. -/
theorem not_surjective_sigmaι_base {i j : ι} (hij : i ≠ j) (y : (F j).toLocallyRingedSpace) :
    ¬ Function.Surjective (sigmaι F i).toLRSHom.base := by
  intro hs
  obtain ⟨x, hx⟩ := hs ((Sigma.ι (fun i ↦ (F i).toLocallyRingedSpace) j).base y)
  exact hij (eq_of_sigmaι_base_eq _ hx)

end AnalyticSpace

end

end ComplexAnalytic

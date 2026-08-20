/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Two open immersions with the same image have isomorphic sources

Material for `Mathlib/Geometry/RingedSpace/OpenImmersion.lean`; see `README.md` on the mirror
tree.

Mathlib has this construction twice — as
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq` and as
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` for schemes — but **not** for locally ringed
spaces, even though the two ingredients it is built from,
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` and its uniqueness, are there. The
definition below is the scheme one transcribed.

It is what identifies two presentations of the same open subspace: `X|S|T` and `X|S'|T'` are
isomorphic as soon as they have the same image in `X`, which is how a chart of an open subspace
of a complex analytic space is compared with a chart of the ambient space
(`Oka/AnalyticSpace/OpenSubspace.lean`).

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`: two open immersions with
  the same image have isomorphic sources.
- `AlgebraicGeometry.LocallyRingedSpace.restrictLE`: the inclusion of a smaller open subspace
  into a larger one. Mathlib has `ofRestrict` for the inclusion into `X` itself and nothing for
  one open subspace inside another, although `IsOpenImmersion.lift` — which is what this is —
  is there. It lives in this file rather than beside `ofRestrict` because `lift` does.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac`: the isomorphism
  commutes with the two immersions. This, rather than the isomorphism itself, is what every use
  of it consumes.
- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_to_base_of_left`: **the
  image of the pullback of two open immersions is the intersection of their images.** Mathlib
  has this for schemes (`Mathlib/AlgebraicGeometry/OpenImmersion.lean`) and for nothing else;
  the proofs below are those transcribed, with `LocallyRingedSpace.forgetToTop` in place of
  `Scheme.forgetToTop`. Together with `isoOfRangeEq` it is what identifies the pullback of two
  open subspace inclusions with the subspace on their intersection.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- **Two open immersions with the same image have isomorphic sources.** -/
noncomputable def isoOfRangeEq (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]
lemma isoOfRangeEq_hom_fac (e : Set.range f.base = Set.range g.base) :
    (isoOfRangeEq f g e).hom ≫ g = f :=
  lift_fac g f (le_of_eq e)

@[reassoc (attr := simp)]
lemma isoOfRangeEq_inv_fac (e : Set.range f.base = Set.range g.base) :
    (isoOfRangeEq f g e).inv ≫ f = g :=
  lift_fac f g (le_of_eq e.symm)

section Pullback

variable {W : LocallyRingedSpace.{u}} (h : W ⟶ Z)

/-- `LocallyRingedSpace.forgetToTop` preserves the pullback of an open immersion.

Mathlib proves this for the composite `forgetToSheafedSpace ⋙ SheafedSpace.forget _`, which
`forgetToTop` is *defined* to be; instance resolution does not unfold the definition, so the
statement in the spelling everything else uses has to be made. -/
instance preservesPullback_forgetToTop :
    PreservesLimit (cospan f h) LocallyRingedSpace.forgetToTop := by
  delta LocallyRingedSpace.forgetToTop
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- **The image of the second projection of a pullback along an open immersion is the preimage
of the image.** Transcribed from `AlgebraicGeometry.range_pullbackSnd`. -/
theorem range_pullbackSnd :
    Set.range (pullback.snd f h).base = h.base ⁻¹' (Set.range f.base) := by
  rw [← show _ = (pullback.snd f h).base from
    PreservesPullback.iso_hom_snd LocallyRingedSpace.forgetToTop f h, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr,
    ← @Set.preimage_univ _ _ (pullback.fst f.base h.base)]
  · erw [TopCat.pullback_snd_image_fst_preimage]
    rw [Set.image_univ]
    rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance

/-- **The image of the pullback of two open immersions is the intersection of their images.**

This is the fact that makes the pullback of two open subspace inclusions identifiable: with
`isoOfRangeEq` it says the pullback of `X|U ⟶ X` and `X|V ⟶ X` is `X|(U ⊓ V)`. -/
theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst f h ≫ f).base = Set.range f.base ∩ Set.range h.base := by
  rw [pullback.condition, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullbackSnd, Set.image_preimage_eq_inter_range]

end Pullback

end AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The image of an open subspace inclusion is that open subset. -/
theorem range_ofRestrict (X : LocallyRingedSpace.{u}) (V : TopologicalSpace.Opens X) :
    Set.range (X.ofRestrict V.isOpenEmbedding).base = (V : Set X) :=
  Subtype.range_val

/-- **The inclusion of a smaller open subspace into a larger one.**

`IsOpenImmersion.lift` gives it: the inclusion of `V` into `X` factors through the inclusion of
`W` because its image is contained in `W`. What makes it usable is `restrictLE_fac` below, which
is the only property of it that anything consumes. -/
noncomputable def restrictLE (X : LocallyRingedSpace.{u}) {V W : TopologicalSpace.Opens X}
    (h : V ≤ W) : X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding :=
  IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding)
    (by rw [range_ofRestrict, range_ofRestrict]; exact h)

/-- **`restrictLE` is a morphism over `X`**: including a smaller open subspace into a larger one
and then into `X` is including it into `X`. -/
@[reassoc (attr := simp)]
theorem restrictLE_fac (X : LocallyRingedSpace.{u}) {V W : TopologicalSpace.Opens X}
    (h : V ≤ W) :
    X.restrictLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding :=
  IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.LocallyRingedSpace

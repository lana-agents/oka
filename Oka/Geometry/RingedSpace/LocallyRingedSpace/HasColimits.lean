/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# The coproduct of locally ringed spaces is covered by its inclusions

Material for `Mathlib/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`; see `README.md`
on the mirror tree. Upstreaming costs that file **nothing**: it is the file's own import, and the
`SheafedSpace` results the proofs run through are already in its closure.

Mathlib builds the coproduct of locally ringed spaces in that file and never says that the
inclusions are open immersions. It says it one level below, for `SheafedSpace` over a category
with strict terminal objects
(`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion`), and one level above,
for `AlgebraicGeometry.Scheme` — where `Mathlib/AlgebraicGeometry/Limits.lean` has the whole
sigma API, which this repository does not import and so cannot name here. Only the middle level
is missing, and

    example (i : Discrete ι) : LocallyRingedSpace.IsOpenImmersion (colimit.ι F i) := by
      infer_instance

fails to synthesise. Everything here is the transport across
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace`, which preserves these colimits.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.sigma_ι_isOpenImmersion`: **the inclusion of a member of
  a coproduct is an open immersion.**
- `AlgebraicGeometry.LocallyRingedSpace.exists_colimit_ι_base_eq`: **every point of a coproduct
  is in the image of some inclusion.**
- `AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover`: the two together, as an
  `AlgebraicGeometry.LocallyRingedSpace.OpenCover`.

## What is not here

**The images of two distinct members are disjoint**, the analogue of
`AlgebraicGeometry.disjoint_opensRange_sigmaι`. It is true and it is not proved here.

The `SheafedSpace` inputs exist —
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty` and the
`sigma_ι_isOpenEmbedding` beside it — and the route is to push a point of the coproduct
through `CategoryTheory.preservesColimitIso`, then
`CategoryTheory.Limits.HasColimit.isoOfNatIso` at `CategoryTheory.Discrete.natIsoFunctor`, then
`TopCat.sigmaIsoSigma`, landing in a `Sigma` type where the index is recoverable. Each step has
its rewrite lemma and **the chain does not go through by `rw` or by `simp`**: the middle step is
blocked on `(F ⋙ G).obj k` against `G.obj (F.obj k)`, which is definitional and not syntactic,
and `simp` unfolds the composite functor's action into
`CategoryTheory.InducedCategory.homMk` before the rewrite can fire. Mathlib proves
`image_preimage_is_empty` by running that same chain under
`set_option backward.isDefEq.respectTransparency false`, which is the shape of what is needed.

Nothing here needs it: an `AlgebraicGeometry.LocallyRingedSpace.OpenCover` asks only that each
member be an open immersion and that the members jointly cover.

## Implementation notes

The index type is taken in `Type u` throughout rather than in a general universe with `Small`,
because `AlgebraicGeometry.LocallyRingedSpace.OpenCover.J` is a `Type u` and the cover is the
point of the file. The two lemmas are stated for a `CategoryTheory.Limits.colimit` of a functor
out of `CategoryTheory.Discrete`, which is what the `SheafedSpace` results are stated for, and the
cover is built for a family, which is the shape `Mathlib/AlgebraicGeometry/Limits.lean` states
its `AlgebraicGeometry.Scheme` version in, and what a consumer has.

Two seams, both recorded because neither is visible from the statements.

**The composition instance has to be handed over positionally.** After rewriting the goal along
`CategoryTheory.ι_preservesColimitIso_inv`, the `colimit.ι` appearing in it carries a
different `CategoryTheory.Limits.HasColimit` instance path from the one a freshly elaborated
`inferInstance` produces. The two terms are definitionally equal and not syntactically equal, and
instance synthesis is syntactic — so `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp` is not
found even with the first factor's instance in context, and is supplied with `@`.

**`AlgebraicGeometry.SheafedSpace` is itself an induced category.** A `SheafedSpace` morphism
needs one `CategoryTheory.InducedCategory.Hom.hom` more than a `LocallyRingedSpace` one before
its `base` can be projected, so the underlying map of the comparison isomorphism is `.hom.hom.base`
where the underlying map of `colimit.ι` at this level is `.base`.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

variable {ι : Type u} (F : Discrete ι ⥤ LocallyRingedSpace.{u})

/-- **The inclusion of a member of a coproduct of locally ringed spaces is an open immersion.**

`AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion` transported along
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace`, which preserves coproducts. -/
instance sigma_ι_isOpenImmersion (i : Discrete ι) :
    LocallyRingedSpace.IsOpenImmersion (colimit.ι F i) := by
  have h := ι_preservesColimitIso_inv forgetToSheafedSpace.{u} F i
  change SheafedSpace.IsOpenImmersion (forgetToSheafedSpace.map (colimit.ι F i))
  rw [← h]
  have h1 : SheafedSpace.IsOpenImmersion (colimit.ι (F ⋙ forgetToSheafedSpace.{u}) i) :=
    inferInstance
  exact @SheafedSpace.IsOpenImmersion.comp _ _ _ _ _ _ _ h1 _

/-- **Every point of a coproduct of locally ringed spaces is in the image of some inclusion.**

`AlgebraicGeometry.SheafedSpace.colimit_exists_rep` for the coproduct of the underlying sheafed
spaces, moved across the comparison isomorphism — which is an isomorphism, hence injective on
points, which is what turns a representative there into one here. -/
theorem exists_colimit_ι_base_eq (x : (colimit F : LocallyRingedSpace.{u})) :
    ∃ (i : Discrete ι) (y : F.obj i), (colimit.ι F i).base y = x := by
  set e := preservesColimitIso forgetToSheafedSpace.{u} F with he
  obtain ⟨i, y, hy⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace.{u})
    (e.hom.hom.base x)
  refine ⟨i, y, ?_⟩
  have hcomp := ι_preservesColimitIso_hom forgetToSheafedSpace.{u} F i
  have key : e.hom.hom.base ((colimit.ι F i).base y) = e.hom.hom.base x := by
    rw [← hy, ← hcomp]
    rfl
  have : IsIso ((SheafedSpace.forget CommRingCat.{u}).map e.hom) := inferInstance
  exact (TopCat.homeoOfIso (asIso ((SheafedSpace.forget CommRingCat.{u}).map e.hom))).injective key

variable (f : ι → LocallyRingedSpace.{u})

/-- **The inclusion of a member of a coproduct is an open immersion**, for a family rather than
for a functor out of `CategoryTheory.Discrete`.

Stated separately because instance search does not see through
`CategoryTheory.Limits.Sigma.ι` to `CategoryTheory.Limits.colimit.ι`, so the cover below cannot
find its `isOpen` field from the functor-indexed instance. -/
instance sigmaι_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (Sigma.ι f i) :=
  sigma_ι_isOpenImmersion (Discrete.functor f) ⟨i⟩

/-- **Every point of a coproduct of locally ringed spaces is in the image of some inclusion**, for
a family rather than for a functor out of `CategoryTheory.Discrete`. -/
theorem exists_sigma_ι_base_eq (x : (∐ f : LocallyRingedSpace.{u})) :
    ∃ (i : ι) (y : f i), (Sigma.ι f i).base y = x := by
  obtain ⟨i, y, hy⟩ := exists_colimit_ι_base_eq (Discrete.functor f) x
  exact ⟨i.as, y, hy⟩

/-- **The members of a coproduct of locally ringed spaces are an open cover of it.**

The analogue of the `AlgebraicGeometry.Scheme` version in
`Mathlib/AlgebraicGeometry/Limits.lean`. The index of a point is chosen by
`Exists.choose` from `AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq`; the members
are disjoint, so the choice is in fact forced, but nothing below needs that. -/
noncomputable def sigmaOpenCover : (∐ f : LocallyRingedSpace.{u}).OpenCover where
  J := ι
  obj := f
  map := Sigma.ι f
  idx x := (exists_sigma_ι_base_eq f x).choose
  covers x := (exists_sigma_ι_base_eq f x).choose_spec

end AlgebraicGeometry.LocallyRingedSpace

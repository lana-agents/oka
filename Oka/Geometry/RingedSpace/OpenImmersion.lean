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

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac`: the isomorphism
  commutes with the two immersions. This, rather than the isomorphism itself, is what every use
  of it consumes.
-/

open CategoryTheory

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

end AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Sheaves.Stalks

/-!
# Naturality of the map on stalks induced by a pushforward

`TopCat.Presheaf.stalkPushforward C g F x : (g _* F).stalk (g x) ⟶ F.stalk x` is natural in `F`.
Mathlib has the definition and its compatibility with germs, identities and composites of `g`,
but not this naturality square, which is what one needs to move a morphism of presheaves on the
source space through a stalk computation on the target space.

There is no analytic content here, so this file is a candidate for upstreaming to Mathlib; it
lives in the `Oka/Topology/` mirror of the Mathlib directory tree for that reason.

## Main results

- `TopCat.Presheaf.stalkPushforward_naturality`
-/

open CategoryTheory Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u v

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] [HasColimits C]

/-- The map on stalks induced by a pushforward is natural in the presheaf: pushing a morphism
`T : F ⟶ G` of presheaves on `X` forward along `g : X ⟶ Y` and then descending to the stalk at
`x` is the same as descending first and applying `T` on stalks. -/
lemma stalkPushforward_naturality {X Y : TopCat.{v}} (g : X ⟶ Y) {F G : X.Presheaf C}
    (T : F ⟶ G) (x : X) :
    (stalkFunctor C (g x)).map ((pushforward C g).map T) ≫ G.stalkPushforward C g x =
      F.stalkPushforward C g x ≫ (stalkFunctor C x).map T := by
  refine TopCat.Presheaf.stalk_hom_ext ((pushforward C g).obj F) fun U hU ↦ ?_
  -- `rw` cannot see through the definition of `TopCat.Presheaf` here, hence `erw`.
  erw [stalkFunctor_map_germ_assoc]
  simp only [pushforward_map_app, stalkFunctor_obj, stalkPushforward_germ,
    stalkPushforward_germ_assoc]
  exact (stalkFunctor_map_germ (C := C) ((Opens.map g).obj U) x hU T).symm

end TopCat.Presheaf

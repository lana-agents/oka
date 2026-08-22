/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Category.TopCat.Opens

/-!
# `TopologicalSpace.Opens.map` is a final functor

Material for `Mathlib/Topology/Category/TopCat/Opens.lean`; see `README.md` on the mirror tree.

For a continuous map `f : X ⟶ Y`, taking preimages is a functor `Opens Y ⥤ Opens X`, and it is
**final**: colimits over `Opens Y` of a diagram pulled back along it agree with colimits over
`Opens X`. Mathlib does not have this — `grep -rn "Opens.map.*Final\|Final.*Opens.map"` over all
of Mathlib returns nothing.

## The content is that `Opens` is filtered

`CategoryTheory.Functor.final_of_exists_of_isFiltered` asks for two things, and over a lattice
both are immediate:

* every `U : Opens X` admits a map to some `(Opens.map f).obj V` — take `V = ⊤`, since
  `U ≤ f ⁻¹' ⊤`;
* any two parallel maps into `(Opens.map f).obj V` are coequalized after a further map — they are
  *equal*, because a preorder has at most one morphism between two objects, so this is
  `Subsingleton.elim`.

`IsFilteredOrEmpty (Opens Y)` is what carries the weight and it is Mathlib's: `Opens Y` has `⊤`
and binary joins.

## What it is for

`SheafOfModules.pullbackObjUnitToUnit` is an isomorphism when the functor between the sites is
final (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`), and for a morphism of
locally ringed spaces that functor is `Opens.map f.base`. So this instance is what makes
`f^* 𝒪_Y ≅ 𝒪_X` — and, with it, "pullback sends free sheaves to free sheaves" — available at all.
-/

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

/-- **`Opens.map f` is final.**

Both conditions of `CategoryTheory.Functor.final_of_exists_of_isFiltered` are immediate over a
lattice: `⊤` receives every open under preimage, and parallel maps in a preorder are equal. -/
instance final_map {X Y : TopCat.{u}} (f : X ⟶ Y) : (Opens.map f).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun _ ↦ ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun {_ _} _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

end TopologicalSpace.Opens

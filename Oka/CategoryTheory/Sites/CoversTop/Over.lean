/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over

/-!
# A family covering the top object covers the top of every slice

Material for `Mathlib/CategoryTheory/Sites/CoversTop/Over.lean`; see `README.md` on the mirror
tree. This file imports its target and nothing else, so upstreaming it adds nothing to that
file's transitive imports.

Mathlib's file of that name has `CategoryTheory.GrothendieckTopology.CoversTop.over`, which is a
*transitivity* statement: a family covering the top, refined by a family covering the top of each
member's own slice, covers the top. The lemma here travels the other way, and it is the one a
localisation argument reaches for: a single family covering the top of `C` already covers the top
of `Over W`, for **every** `W` at once, by taking every object of `Over W` whose underlying object
admits a morphism to some member of the family.

The index type is `(i : I) × (V : C) × (V ⟶ X i) × (V ⟶ W)` and not a family of pullbacks, so no
limits are assumed of the site and no choice is made. The price is a family far larger than
necessary, which `CategoryTheory.GrothendieckTopology.CoversTop` does not mind: it asks only that
the sieve generated over each object be covering.

Its consumer here is `Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Locality.lean`, where the
kernel of a morphism out of a free sheaf has to be seen to be of finite type over every slice of a
covering family.

## Main results

- `CategoryTheory.GrothendieckTopology.CoversTop.over'`
-/

@[expose] public section

universe v' u'

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

/-- A family of objects covering the top induces, for every `W : C`, a family of objects
of `Over W` covering the top: the family of all objects of `Over W` whose underlying
object admits a morphism to some member of the family. -/
lemma CoversTop.over' {I : Type*} {X : I → C} (hX : J.CoversTop X) (W : C) :
    (J.over W).CoversTop
      (fun (t : (i : I) × (V : C) × (V ⟶ X i) × (V ⟶ W)) ↦ Over.mk t.2.2.2) := by
  intro U
  rw [mem_over_iff]
  refine J.superset_covering ?_ (hX U.left)
  rintro V g ⟨i, ⟨f⟩⟩
  exact ⟨Over.mk (g ≫ U.hom), Over.homMk g, 𝟙 _,
    ⟨⟨i, V, f, g ≫ U.hom⟩, ⟨Over.homMk (𝟙 _)⟩⟩, (Category.id_comp _).symm⟩

end CategoryTheory.GrothendieckTopology

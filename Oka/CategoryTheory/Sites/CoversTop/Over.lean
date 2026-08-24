/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# A family covering the top object covers the top of every slice

Material for `Mathlib/CategoryTheory/Sites/CoversTop/Over.lean`; see `README.md` on the mirror
tree. It imports its target and `Mathlib.CategoryTheory.Sites.Spaces`, the latter only for
`coversTop_over` below, so upstreaming it adds **15** modules to that file's closure of **997**.

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

## The second lemma, and why it is here rather than beside the topology it mentions

`coversTop_over` is the same phenomenon for the site of open subsets of a topological space: a
family of opens covering `X` covers the terminal object of the slice site over `X`. It is not a
special case of `CoversTop.over'` — that one produces the family of *all* objects admitting a
morphism to a member, and this one keeps the given family, which is what a consumer holding a
concrete cover has.

The type it is most specifically about is `Opens.grothendieckTopology`, defined
in `Mathlib/CategoryTheory/Sites/Spaces.lean`, and that is the placement the subject suggests and
**the price rules out**: adding `Mathlib.CategoryTheory.Sites.Over` to that file costs it **193**
modules on a closure of 818, against `README.md`'s recorded 96, where the two imports it needs
here cost **15**. `Mathlib/CategoryTheory/Sites/Over.lean` would cost 16 and would do as well;
this file wins by a point and by sitting beside its sibling.

**It is in the root namespace**, which is not where a Mathlib file would want it. That is
inherited from where it was declared — `Oka/Coherent.lean`, now deleted — and renaming it is a
separate change with its own consumers to update; taxis #905, which moved it, asked for no
renames.

## Main results

- `CategoryTheory.GrothendieckTopology.CoversTop.over'`
- `coversTop_over`, whose consumer is
  `Oka/Geometry/RingedSpace/LocallyRingedSpace/Coherent.lean`, where the open cover of a locally
  ringed space on which relations are locally generated has to be read on the slice site.
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

open CategoryTheory TopologicalSpace

/-- A family of open subsets of `X` covering `X` covers the terminal object of the slice site
over `X`. -/
lemma coversTop_over {T : Type u'} [TopologicalSpace T] (X : Opens T) {A : Type u'}
    (V : A → Opens T) (hle : ∀ a, V a ≤ X) (hcov : ∀ x ∈ X, ∃ a, x ∈ V a) :
    ((Opens.grothendieckTopology T).over X).CoversTop (fun a ↦ Over.mk (homOfLE (hle a))) := by
  intro Z
  let S : Sieve Z.left :=
    ⟨fun W _ ↦ ∃ a, W ≤ V a, by rintro W₁ W₂ f ⟨a, ha⟩ g; exact ⟨a, (leOfHom g).trans ha⟩⟩
  have hS : S ∈ Opens.grothendieckTopology T Z.left := by
    intro x hx
    obtain ⟨a, ha⟩ := hcov x (leOfHom Z.hom hx)
    exact ⟨Z.left ⊓ V a, homOfLE inf_le_left, ⟨a, inf_le_right⟩, ⟨hx, ha⟩⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (GrothendieckTopology.overEquiv_symm_mem_over _ Z S hS)
  rintro W g ⟨a, ha⟩
  exact ⟨a, ⟨Over.homMk (homOfLE ha)⟩⟩

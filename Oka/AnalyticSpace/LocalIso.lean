/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.IsLocalHomeomorph
import Oka.AnalyticSpace.Finite

/-!
# Local isomorphisms of complex analytic spaces, and finite étale morphisms

A holomorphic map is a **local isomorphism** when its underlying map is a local homeomorphism and
every stalk map is an isomorphism, and **finite étale** when it is that and finite
(`ComplexAnalytic.AnalyticSpace.IsFinite`). This is the second rung of the Riemann existence
theorem's analytic side; the first is `Oka/AnalyticSpace/Finite.lean`.

## Why two fields, and why one of them is not topological

`ComplexAnalytic.AnalyticSpace.IsFinite` is a condition on the underlying map and nothing else.
**A local isomorphism cannot be**: two analytic spaces with the same underlying space and
different structure sheaves are not locally isomorphic, so the condition has to see the sheaves,
and the two rungs therefore do *not* compose the way `IsFinite`'s two fields do. The definition
below meets that rather than hiding it — one field is topological and one is about stalks, and the
class carries both.

**Why stalks rather than "locally an open immersion".**
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` is available and one could ask for a cover
of the source on which the morphism restricts to one. That is equivalent and worse to *use*: it
quantifies over covers, so every consumer begins by choosing one, whereas the stalk condition is
checkable at a point and this repository already has the machinery for it —
`ComplexAnalytic.IsCutOutBy` carries `surjective_stalkMap` and `ker_stalkMap` as fields, and
`AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` is what makes the composition below one line.

**Why not `IsCoveringMap`.** Mathlib has it, and it is a *global* condition — every point of the
target has an evenly covered neighbourhood — strictly stronger than being a local homeomorphism.
For a **finite** local isomorphism onto a connected base the two agree, and that agreement is a
theorem, of the same kind as properness-versus-finiteness, which `Oka/AnalyticSpace/Finite.lean`
already declines to conflate. It is not in the definition and it is not proved here.

## What is not here

* **The Riemann existence theorem**, and any statement relating covers to field extensions. This
  is the notion RET is *about*; nothing here mentions `ℂ(X)`.
* **That a finite local isomorphism onto a connected base is a covering map.** The third rung.
* **The analytification of a finite étale morphism** — the other blocker of #551, stateable only
  now that this exists.
* **Grauert's finite mapping theorem**, which `Oka/AnalyticSpace/Finite.lean` already records as
  absent.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.IsLocalIso`: **a local homeomorphism whose stalk maps are
  isomorphisms.**
- `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`: finite and a local isomorphism.

## Main results

- `ComplexAnalytic.AnalyticSpace.isLocalIso_id`, `isLocalIso_comp` and `isLocalIso_of_isIso`:
  the local isomorphisms contain the isomorphisms and are closed under composition.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_id` and `isFiniteEtale_comp`: the same for finite
  étale morphisms, from the two rungs' versions.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **A morphism of complex analytic spaces is a local isomorphism when its underlying map is a
local homeomorphism and every stalk map is an isomorphism.**

The underlying map is spelled `f.toLRSHom.base` and the stalk map `f.toLRSHom.stalkMap`, as
everywhere else here: `ComplexAnalytic.AnalyticSpace.Hom` is a
`AlgebraicGeometry.LocallyRingedSpace.Hom` together with a `ℂ`-linearity condition and its
category structure is defined through `toLRSHom`.

**Neither field implies the other.** A closed embedding which is not an isomorphism has
isomorphisms on no stalk outside its image and is not a local homeomorphism either
(`OkaTest/FiniteMorphism.lean` exhibits one); and a homeomorphism of underlying spaces carrying a
non-isomorphism of structure sheaves would satisfy the first and not the second. -/
class IsLocalIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) : Prop where
  /-- The underlying map is a local homeomorphism. -/
  isLocalHomeomorph : IsLocalHomeomorph f.toLRSHom.base
  /-- Every stalk map is an isomorphism. -/
  isIso_stalkMap (x : X) : IsIso (f.toLRSHom.stalkMap x)

attribute [instance] IsLocalIso.isIso_stalkMap

/-- **The identity is a local isomorphism.** -/
instance isLocalIso_id (X : AnalyticSpace.{u}) : IsLocalIso (𝟙 X) where
  isLocalHomeomorph := by
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = id := rfl
    rw [h]
    exact (Homeomorph.refl X).isLocalHomeomorph
  isIso_stalkMap x := by
    have h : (𝟙 X : X ⟶ X).toLRSHom = 𝟙 X.toLocallyRingedSpace := rfl
    rw [h, LocallyRingedSpace.stalkMap_id]
    exact CategoryTheory.IsIso.id _

/-- **A composite of local isomorphisms is a local isomorphism.**

`IsLocalHomeomorph.comp` and `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp`. The two stalk
instances have to be produced by hand rather than left to `infer_instance`: the composite's second
factor is the stalk map of `g` **at the image point**, and search does not find it from the class
field at the spelling the goal is in. -/
instance isLocalIso_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocalIso f] [IsLocalIso g] : IsLocalIso (f ≫ g) where
  isLocalHomeomorph := by
    have h : ((f ≫ g).toLRSHom.base : X → Z) = (g.toLRSHom.base : Y → Z) ∘ f.toLRSHom.base := rfl
    rw [h]
    exact (IsLocalIso.isLocalHomeomorph (f := g)).comp (IsLocalIso.isLocalHomeomorph (f := f))
  isIso_stalkMap x := by
    have h : (f ≫ g).toLRSHom = f.toLRSHom ≫ g.toLRSHom := rfl
    have h1 : IsIso (f.toLRSHom.stalkMap x) := IsLocalIso.isIso_stalkMap _
    have h2 : IsIso (g.toLRSHom.stalkMap ((ConcreteCategory.hom f.toLRSHom.base) x)) :=
      IsLocalIso.isIso_stalkMap _
    rw [h, LocallyRingedSpace.stalkMap_comp]
    exact @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1

/-- **An isomorphism is a local isomorphism.**

Its underlying map is a homeomorphism and its stalk maps are isomorphisms because the whole
morphism is one. The `haveI` has to be ascribed at `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom f`
and **not** at `forgetToLocallyRingedSpace.map f`: the two are `rfl`-equal and are different
discrimination-tree keys, so with the second spelling `infer_instance` fails. That seam is
recorded in `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict`'s docstring and in
`ComplexAnalytic.range_base_localisationProj`'s; this is its third appearance. -/
theorem isLocalIso_of_isIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsIso f] : IsLocalIso f where
  isLocalHomeomorph :=
    (LocallyRingedSpace.homeoOfIso
      (forgetToLocallyRingedSpace.{u}.mapIso (asIso f))).isLocalHomeomorph
  isIso_stalkMap x := by
    haveI : IsIso (AnalyticSpace.Hom.toLRSHom f) :=
      (forgetToLocallyRingedSpace.{u}.mapIso (asIso f)).isIso_hom
    infer_instance

/-- **A morphism is finite étale when it is finite and a local isomorphism.**

This is what the Riemann existence theorem is about on the analytic side. It is stated as a class
of its own rather than as a conjunction so that the instances below are found, and it carries no
field beyond the two.

**It is not `IsCoveringMap` and is not proved to imply it** — see the module docstring. -/
class IsFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) : Prop where
  /-- It is finite. -/
  isFinite : IsFinite f
  /-- It is a local isomorphism. -/
  isLocalIso : IsLocalIso f

attribute [instance] IsFiniteEtale.isFinite IsFiniteEtale.isLocalIso

/-- **The identity is finite étale.** -/
instance isFiniteEtale_id (X : AnalyticSpace.{u}) : IsFiniteEtale (𝟙 X) where
  isFinite := inferInstance
  isLocalIso := inferInstance

/-- **A composite of finite étale morphisms is finite étale**, from the two rungs' composition
lemmas and nothing else. -/
instance isFiniteEtale_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFiniteEtale f] [IsFiniteEtale g] : IsFiniteEtale (f ≫ g) where
  isFinite := inferInstance
  isLocalIso := inferInstance

/-- **An isomorphism is finite étale.** -/
theorem isFiniteEtale_of_isIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsIso f] :
    IsFiniteEtale f where
  isFinite := isFinite_of_isIso f
  isLocalIso := isLocalIso_of_isIso f

end ComplexAnalytic.AnalyticSpace

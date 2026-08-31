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
theorem's analytic side; the first is `Oka/AnalyticSpace/Finite.lean` and the third is
`Oka/AnalyticSpace/CoveringMap.lean`, which deduces from these two that the underlying map of a
finite étale morphism out of a Hausdorff analytic space is a covering map.

## Why two fields, and why one of them is not topological

`ComplexAnalytic.AnalyticSpace.IsFinite` is a condition on the underlying map and nothing else.
**A local isomorphism cannot be**: two analytic spaces with the same underlying space and
different structure sheaves are not locally isomorphic, so the condition has to see the sheaves,
and the two rungs therefore do *not* compose the way `IsFinite`'s two fields do. The definition
below meets that rather than hiding it — one field is topological and one is about stalks, and the
class carries both.

**Why stalks rather than "locally an open immersion".**
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion` is available and one could ask for a cover
of the source on which the morphism restricts to one. That is presumably equivalent — a theorem,
and not proved here — and it is worse to *use* either way: it quantifies over covers, so every
consumer begins by choosing one, whereas the stalk condition is checkable at a point, and this
repository already has the machinery for it: `ComplexAnalytic.IsCutOutBy` carries
`surjective_stalkMap` and `ker_stalkMap` as fields, and
`AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` is what makes the composition below one line.

**Why not `IsCoveringMap`.** Mathlib has it, and it is a *global* condition — every point of the
target has an evenly covered neighbourhood — strictly stronger than being a local homeomorphism.
For a **finite** local isomorphism the two agree, and that agreement is a theorem, of the same
kind as properness-versus-finiteness, which `Oka/AnalyticSpace/Finite.lean` keeps out of its
definition and proves separately as
`ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber`. It is not in the
definition and it is not proved here; it is
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` in
`Oka/AnalyticSpace/CoveringMap.lean`, the third rung, which imports this file.

**This paragraph used to say "onto a connected base", and connectedness is not a hypothesis of
that theorem.** A point outside the range is evenly covered by the empty index type. What
connectedness gives is that the number of sheets is constant — a different statement, and now a
proved one: `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, in the same file as
the rung.

## What is not here

* **The Riemann existence theorem**, and any statement relating covers to field extensions. This
  is the notion RET is *about*; nothing here mentions `ℂ(X)`.
* **A `degree` function on morphisms — this is no longer absent, and it is not in this file.**
  The bullet that used to stand here has been retired in four steps. It first said the constancy
  of the number of sheets over a connected base was not proved anywhere; it is, as
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` in
  `Oka/AnalyticSpace/CoveringMap.lean`. It then said the common value was computed for no morphism;
  it is, and no longer only for one — `ComplexAnalytic.card_fiber_base_sq` puts the fibres of
  `z ↦ z²` on the punctured line at **2**, by a statement about roots in `ℂ` rather than about
  covers, and `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` puts the fibres of the trivial
  `ι`-sheeted cover at `Nat.card ι`, so every value is realised. **The fourth step retires it
  altogether**: `ComplexAnalytic.AnalyticSpace.degree` in `Oka/AnalyticSpace/Degree.lean` is the
  `Nat`-valued invariant, the well-definedness obligation this bullet made the condition of
  having one is `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`, and the consumer it asked
  for is `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`. The two computations
  above are now read as degrees, `ComplexAnalytic.degree_sq` and
  `ComplexAnalytic.AnalyticSpace.degree_sigmaFold`.
* **The analytification of a finite étale morphism** — the other blocker of #551, stateable only
  now that this exists.
* **Cancellation for `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`, and what is missing of it is
  one topological statement.** A Galois-category structure on the finite étale covers of a fixed
  base — `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver`, in
  `Oka/AnalyticSpace/FiniteEtaleOver.lean` — wants *"if `g` and `f ≫ g` are finite étale then `f`
  is"*. Three of the four halves cancel and are below or in `Oka/AnalyticSpace/Finite.lean`:
  `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` is both halves of the local-isomorphism rung,
  and `ComplexAnalytic.AnalyticSpace.finite_fiber_of_comp` is the fibre half of the finite one —
  which does not even use `g`'s finiteness. **The fourth is closedness of `f`**, and it does not
  follow from the other three: for a `Y` that is not separated over `Z` — the real line with two
  origins over the real line, with `f` the inclusion of one branch — `f ≫ g` is the identity and
  `g` is closed with finite fibres, while the image of `f` has a non-open complement. That
  reasoning is about topological spaces, is not compiled anywhere, and is recorded as the reason
  not to expect the statement without a hypothesis rather than as a theorem. The classical proof
  factors `f` through its graph and needs `Y` separated over `Z`; this repository has neither a
  separatedness notion for `ComplexAnalytic.AnalyticSpace` nor the fibre products a graph is built
  from, which is the same absence `Oka/AnalyticSpace/FiniteEtaleOver.lean` records as the reason
  base change is not statable there.
* **Grauert's finite mapping theorem**, which `Oka/AnalyticSpace/Finite.lean` already records as
  absent.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.IsLocalIso`: **a local homeomorphism whose stalk maps are
  isomorphisms.**
- `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`: finite and a local isomorphism.

## Main results

- `ComplexAnalytic.AnalyticSpace.isLocalIso_id`, `isLocalIso_comp` and `isLocalIso_of_isIso`:
  the local isomorphisms contain the isomorphisms and are closed under composition.
- `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp`: **local isomorphism cancels** — if `f ≫ g`
  and `g` are local isomorphisms then so is `f`, and neither half of the proof asks for anything
  this repository had to supply.
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

**Note which points the second field ranges over.** `isIso_stalkMap` is quantified over points
of the **source**, so it says nothing at points of the target outside the image. That is a remark
about how to read the field, not a reason the other one is needed: a local homeomorphism can miss
most of the target too.

**Neither implication between the fields is settled here.** No counterexample to either direction
is exhibited and neither is proved, so the two-field definition is a design choice and not a
theorem. What *is* checked is that the topological field is not idle:
`ComplexAnalytic.not_isLocalIso_axisIncl` (`OkaTest/FiniteMorphism.lean`) rules out the closed
immersion of an axis into
`ℂ²` **using that field alone** — its own docstring records that nothing about stalks enters. That
morphism fails both fields, so it witnesses no implication in either direction. -/
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

`IsLocalHomeomorph.comp` and `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp`.

**Why the two stalk hypotheses are passed explicitly, through
`CategoryTheory.IsIso.comp_isIso'`, rather than left to instance search.** After the rewrite the
goal's first stalk is indexed at `(f ≫ g).base x` while `h2` is indexed at `g.base (f.base x)`.
Those are the same point by `rfl` **at default transparency only**: reducing `(f ≫ g).base` to
`g.base ∘ f.base` unfolds the composition of `AlgebraicGeometry.LocallyRingedSpace.Hom`, which is
not reducible. **Instance search runs at reducible transparency**, so it cannot see that the two
`IsIso` statements are about the same morphism, and neither `infer_instance` with both hypotheses
as local instances nor `apply CategoryTheory.IsIso.comp_isIso` succeeds — the latter unifies the
composite at default transparency and then fails on the very hypothesis in scope, one level down
and by the same cause.

The control is one keyword: `with_reducible exact CategoryTheory.IsIso.comp_isIso' h2 h1` fails
with exactly that mismatch of stalk objects, and removing `with_reducible` compiles. Nothing about
the composite shape is at fault — `CategoryTheory.IsIso.comp_isIso` is an instance and closes the
generic goal; `comp_isIso'` is Mathlib's explicit-argument form, provided for this situation. -/
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
    exact CategoryTheory.IsIso.comp_isIso' h2 h1

/-- **Local isomorphism cancels**: if `f ≫ g` and `g` are local isomorphisms, then so is `f`.

**Both halves are free and neither is this repository's work**, which is the content of the
statement rather than a remark about the proof. The topological one is `IsLocalHomeomorph.of_comp`,
whose third hypothesis is the *continuity* of `f` alone — and a morphism's base map is a `TopCat`
morphism, so it carries that with it. The stalk one is
`AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` read as a factorisation of the composite's
stalk map, plus two-out-of-three in the shape `CategoryTheory.IsIso.of_isIso_comp_left`.

**Nothing is asked of `f` that a morphism does not already have**, so this is a cancellation
statement with no side condition, unlike the finite rung's
`ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp`, which asks for injectivity of the second
factor. The module docstring's `## What is not here` says what that difference costs the finite
étale rung.

**It is a `theorem` and not an `instance`, deliberately.** As an instance it would fire on every
`ComplexAnalytic.AnalyticSpace.IsLocalIso` goal and ask instance search to invent both the object
`Z` and the morphism `g` to factor through, neither of which is determined by the goal.

`ComplexAnalytic.AnalyticSpace.isLocalIso_comp`, directly above, is the composition companion.
**The third position of two-out-of-three — concluding about `g` from `f` and `f ≫ g` — is not
stated here and should not be expected**: both hypotheses see `g` only along the image of `f`, the
stalk field of each being quantified over points of its own source, so `g` is unconstrained away
from that image. No morphism below is asked to witness that, and this sentence is a reading of the
two definitions rather than a theorem. -/
theorem isLocalIso_of_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocalIso (f ≫ g)] [IsLocalIso g] : IsLocalIso f where
  isLocalHomeomorph :=
    IsLocalHomeomorph.of_comp (IsLocalIso.isLocalHomeomorph (f := f ≫ g))
      (IsLocalIso.isLocalHomeomorph (f := g)) f.toLRSHom.base.hom.continuous
  isIso_stalkMap x := by
    haveI : IsIso (g.toLRSHom.stalkMap (f.toLRSHom.base x) ≫ f.toLRSHom.stalkMap x) := by
      rw [← LocallyRingedSpace.stalkMap_comp]
      exact IsLocalIso.isIso_stalkMap (f := f ≫ g) x
    exact IsIso.of_isIso_comp_left (g.toLRSHom.stalkMap (f.toLRSHom.base x))
      (f.toLRSHom.stalkMap x)

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

**It is not `IsCoveringMap`** — that is a condition on the underlying map alone, and this one is
not — but it does imply it for a Hausdorff source:
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` in
`Oka/AnalyticSpace/CoveringMap.lean`. This docstring used to say the implication was unproved; see
the module docstring for why the two notions are still kept apart. -/
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

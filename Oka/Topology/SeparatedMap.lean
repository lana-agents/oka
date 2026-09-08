/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.SeparatedMap

/-!
# A continuous separated map into a Hausdorff space has Hausdorff source, and composites

Material for `Mathlib/Topology/SeparatedMap.lean`; see `README.md` on the mirror tree. Three
statements, and each is a direction that file does not have: `IsSeparatedMap.t2Space`,
`IsSeparatedMap.comp` and `IsSeparatedMap.of_comp` below. **The opening read *One statement, and
it is the direction that file does not have* and named only the first, until 2026-09-08**, when
the two composition statements were added; the record is kept because that sentence was exact for
the file it described.

`Mathlib/Topology/SeparatedMap.lean` has the converse, `T2Space.isSeparatedMap` — a map out of a
Hausdorff space is separated, for any target — and the constant-map biconditional
`t2space_iff_isSeparatedMap`, which says `T2Space X` is separatedness of `fun _ : X ↦ y`. Neither
gives the statement below, and the biconditional is close enough to be worth saying why: it reads
separatedness of a map that forgets its source, so it recovers Hausdorffness from a *constant*
map, where what is wanted here is Hausdorffness from a map with a Hausdorff target.

**And it has two composition statements, neither of which is either of the two below.**
`IsSeparatedMap.comp_left` makes `g ∘ f` separated from `f` separated **and `g` injective**, and
`IsSeparatedMap.comp_right` makes `f ∘ g` separated from `f` separated and `g` continuous **and
injective**. Both spend an injectivity, which is what lets them ask nothing of the other map;
`IsSeparatedMap.comp` below asks separatedness of both maps and injectivity of neither, and
`IsSeparatedMap.of_comp` asks nothing at all of the second map — not continuity, not injectivity,
not separatedness, and not even a topology on its target, which is a `Sort` here as it is in
`IsSeparatedMap`'s own binders. A `git grep` for `IsSeparatedMap` outside
`Mathlib/Topology/SeparatedMap.lean` returns two lines at the commit that adds this, in
`Mathlib/Topology/Homotopy/Lifting.lean` and `Mathlib/Topology/Covering/Basic.lean`, and neither
is a composition statement.

Upstreaming to `Mathlib/Topology/SeparatedMap.lean` costs that file **no** new imports — its
closure of 615 Mathlib modules already contains the one import below, which is that file itself,
measured with `python3 scripts/import_cost.py Oka/Topology/SeparatedMap.lean`.

## Why here and not beside the consumer

What consumes this at the commit that adds it is
`LineTwoOrigins.not_isCoveringMap_fold` in `OkaTest/FiniteEtaleCancel.lean`, and the statement it
makes possible is about `IsClosedMap.isCoveringMap_of_isLocalHomeomorph` in
`Oka/Topology/Covering/Basic.lean`. Neither is where this belongs. `README.md`'s mirror-tree
section says to **split by destination, not by subject**, and the destination is decided by the
imports: `Mathlib/Topology/SeparatedMap.lean`
publicly imports `Mathlib/Topology/Separation/Hausdorff.lean`, so it already has `t2_separation`
and this statement costs it nothing, whereas `Mathlib/Topology/Separation/Hausdorff.lean` — where
`Topology.IsEmbedding.t2Space` and the other transfers of the Hausdorff axiom live — does not
import `IsSeparatedMap` and could not hold this without a new edge in the direction that file's
own imports run against. `Mathlib/Topology/Covering/Basic.lean` is not a destination at all: the
statement mentions no covering map.

## The proof, and the case split is the whole of it

`IsSeparatedMap f` separates two points with the **same** image; a Hausdorff target separates two
points with **different** images, by pulling back a separation downstairs. Those are the two
cases of `f x = f y`, and in the first the hypothesis is the goal — `T2Space`'s field and
`IsSeparatedMap`'s conclusion are the same existential, so no repackaging is needed. Continuity is
spent once, in the second case, on the two preimages being open.

**`IsSeparatedMap.comp` is the same case split with the target's Hausdorffness replaced by `g`'s
separatedness**, and it is the same proof read one hypothesis weaker: two points of `X` with the
same image under `g ∘ f` either have the same image under `f`, where `f`'s separatedness is the
goal, or different ones, where `g`'s separates the two images and the preimages under `f` separate
the points. Continuity of `f` is spent in exactly the one place it is spent above.
`IsSeparatedMap.of_comp` needs no case split and no topology: two points with the same image under
`f` have the same image under `g ∘ f`, so the hypothesis applies to them directly.

## Main results

- `IsSeparatedMap.t2Space`: **a continuous separated map into a Hausdorff space has Hausdorff
  source.**
- `IsSeparatedMap.comp`: **a composite of two separated maps is separated**, when the first is
  continuous.
- `IsSeparatedMap.of_comp`: **and the first factor of a separated composite is separated**, with
  no hypothesis whatever on the second — its target is not even asked to be a topological space.

## What is not here

* **No converse, and no biconditional — although one holds.** The converse is Mathlib's
  `T2Space.isSeparatedMap`: it asks `T2Space` of the *source*, gives `IsSeparatedMap f` for any
  target, and asks neither `[T2Space X]` nor `Continuous f`. Paired with `IsSeparatedMap.t2Space`,
  whose proof spends both, it gives `IsSeparatedMap f ↔ T2Space E` under those two hypotheses.
  That `Iff` is not stated here: each direction is what a caller uses, and its right-hand side is
  a class, which an `Iff` cannot present to instance search.
* **The biconditional that fails is the one with `[T2Space X]` dropped, and it fails forwards.**
  `Function.Injective.isSeparatedMap` is Mathlib's and makes an injective map separated whatever
  its source, so the identity of a space that is not Hausdorff is a separated map whose source is
  not Hausdorff. `LineTwoOrigins.not_t2Space` (`OkaTest/FiniteEtaleCancel.lean`) is such a space
  at the commit that adds this file.
* **Nothing about `IsLocallyInjective`**, the dual notion `Mathlib/Topology/SeparatedMap.lean`
  introduces alongside `IsSeparatedMap`, and nothing about the covering maps that satisfy both.
  The one application in this repository composes this with `IsCoveringMap.isSeparatedMap`, which
  is Mathlib's and is in `Mathlib/Topology/Covering/Basic.lean`.
* **No `instance`.** The *named* hypotheses of all three are explicit arguments and none is a
  class, so instance search could not fire on any of them; a caller supplies them.
  `IsSeparatedMap.t2Space` does carry an instance argument, `[T2Space X]` on the target, and it is
  not one of them: what blocks the `instance` attribute is `hsep` and `hf`, which nothing can
  synthesise.
* **No converse of `IsSeparatedMap.of_comp`, and `IsSeparatedMap.comp` cannot drop `hg`.**
  Separatedness of `f` alone does not give separatedness of `g ∘ f`: take `f` the identity of a
  space that is **not** Hausdorff — separated, because `Function.Injective.isSeparatedMap` asks
  nothing of the source — and `g` the constant map to a point. Then `g ∘ f` is that constant map,
  which `t2space_iff_isSeparatedMap` makes separated exactly when the space is Hausdorff, so it is
  not. Nothing below states that failure; this is a remark about which hypotheses are load-bearing
  and not a theorem of this file.
* **Nothing about the second factor.** `IsSeparatedMap.of_comp` reads separatedness off the
  composite for `f` and says nothing about `g`, and no statement below does: a separated `g ∘ f`
  with `f` surjective does make `g` separated, and that is not proved here because nothing in this
  repository asks for it.
-/

/-- **A continuous separated map into a Hausdorff space has Hausdorff source.**

Two points of the source are separated by the hypothesis when they have the same image, and by the
preimages of a separation downstairs when they do not. `Topology.IsEmbedding.t2Space` is the same
shape at a stronger hypothesis on the map; this asks only that the map separate the points of its
own fibres. -/
theorem IsSeparatedMap.t2Space {E : Type*} {X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space X] {f : E → X} (hsep : IsSeparatedMap f) (hf : Continuous f) : T2Space E := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases h : f x = f y
  · exact hsep x y h hxy
  · obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation h
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hf, hv.preimage hf, hxu, hyv, huv.preimage _⟩

/-- **A composite of two separated maps is separated**, when the first is continuous.

Two points of the source with the same image under `g ∘ f` either have the same image under `f`,
where `hf` separates them, or different ones, where `hg` separates the two images and their
preimages separate the points. **Neither map is asked to be injective**, which is what separates
this from Mathlib's `IsSeparatedMap.comp_left` and `IsSeparatedMap.comp_right`: each of those
spends an injectivity and asks nothing of the other map. -/
theorem IsSeparatedMap.comp {X Y : Type*} {Z : Sort*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : Y → Z} (hf : IsSeparatedMap f) (hg : IsSeparatedMap g)
    (hcont : Continuous f) : IsSeparatedMap (g ∘ f) := by
  intro x₁ x₂ he hne
  rcases eq_or_ne (f x₁) (f x₂) with h | h
  · exact hf x₁ x₂ h hne
  · obtain ⟨u, v, hu, hv, h₁, h₂, huv⟩ := hg _ _ he h
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hcont, hv.preimage hcont, h₁, h₂, huv.preimage f⟩

/-- **The first factor of a separated composite is separated**, with no hypothesis whatever on the
second — not continuity, not injectivity, not separatedness, and not a topology on its target.

Two points with the same image under `f` have the same image under `g ∘ f`, so the hypothesis
applies to them unchanged; `g` is an explicit argument only because it appears in neither the
hypothesis's binder nor the conclusion in a position elaboration could read it from. -/
theorem IsSeparatedMap.of_comp {X : Type*} {Y Z : Sort*} [TopologicalSpace X] {f : X → Y}
    (g : Y → Z) (h : IsSeparatedMap (g ∘ f)) : IsSeparatedMap f :=
  fun x₁ x₂ he hne ↦ h x₁ x₂ (congrArg g he) hne

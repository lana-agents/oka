/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.SeparatedMap

/-!
# A continuous separated map into a Hausdorff space has Hausdorff source

Material for `Mathlib/Topology/SeparatedMap.lean`; see `README.md` on the mirror tree. One
statement, and it is the direction that file does not have: `IsSeparatedMap.t2Space` below.

`Mathlib/Topology/SeparatedMap.lean` has the converse, `T2Space.isSeparatedMap` — a map out of a
Hausdorff space is separated, for any target — and the constant-map biconditional
`t2space_iff_isSeparatedMap`, which says `T2Space X` is separatedness of `fun _ : X ↦ y`. Neither
gives the statement below, and the biconditional is close enough to be worth saying why: it reads
separatedness of a map that forgets its source, so it recovers Hausdorffness from a *constant*
map, where what is wanted here is Hausdorffness from a map with a Hausdorff target.

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

## Main results

- `IsSeparatedMap.t2Space`: **a continuous separated map into a Hausdorff space has Hausdorff
  source.**

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
* **No `instance`.** The hypotheses are two explicit arguments and neither is a class, so instance
  search could not fire on it; a caller supplies both.
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

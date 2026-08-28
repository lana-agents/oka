/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Sets.Opens

/-!
# The sheets of a map, as a family of opens

`IsLocalHomeomorph f` says that every point of the source has *some* neighbourhood on which `f`
restricts to an open embedding. What a construction indexed by opens needs instead is the family
of all such opens together with the statement that it covers, and that is what is here:
`sheetOpens f` is the set of opens on which `f` is an open embedding, and
`IsLocalHomeomorph.sSup_sheetOpens` says its supremum is `⊤`.

There is no analytic content here, so this file is a candidate for upstreaming; it lives in the
`Oka/Topology/` mirror of the Mathlib directory tree for that reason. Upstreaming to
`Mathlib/Topology/IsLocalHomeomorph.lean` costs that file **no** new imports — its closure of 649
Mathlib modules already contains `Mathlib.Topology.Sets.Opens`, measured with
`python3 scripts/import_cost.py --target Mathlib.Topology.IsLocalHomeomorph`.

## Why the `Opens` form rather than Mathlib's

`isLocalHomeomorph_iff_isOpenEmbedding_restrict` gives, for each `x`, some `U ∈ 𝓝 x` with
`IsOpenEmbedding (U.restrict f)`. A neighbourhood is not an open, and a consumer that glues over
a cover — `AlgebraicGeometry.LocallyRingedSpace.sheetIso` is the one this was written for — needs
opens and needs them as a *family with a supremum*, not one at a time. Passing through the
source of the `OpenPartialHomeomorph` that `IsLocalHomeomorph` unfolds to, which is open by
`OpenPartialHomeomorph.open_source`, avoids taking an interior and the proof that restricting an
open embedding to a smaller open is again one.

## Main definitions

- `sheetOpens`: the opens of the source on which the map is an open embedding.

## Main results

- `IsLocalHomeomorph.exists_mem_sheetOpens`: **every point lies in a sheet.**
- `IsLocalHomeomorph.sSup_sheetOpens`: **the sheets cover**, `sSup (sheetOpens f) = ⊤`.

## What is not here

* **Nothing about the fibres.** `sheetOpens f` is a set of opens and says nothing about how many
  of them meet a fibre; finiteness of the fibres is a separate hypothesis everywhere it is needed.
* **No sheet is distinguished and no choice is made.** `IsLocalHomeomorph.exists_mem_sheetOpens`
  is an existence statement; a consumer that wants one sheet per point chooses it itself.
* **No converse.** A map whose sheets cover *is* a local homeomorphism, by
  `isLocalHomeomorph_iff_isOpenEmbedding_restrict` and `Opens.isOpen`, but nothing below needs
  that direction and it is not stated.
-/

open TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)

/-- **The sheets of `f`**: the opens of the source on which `f` restricts to an open embedding. -/
def sheetOpens : Set (Opens X) := {V | IsOpenEmbedding ((V : Set X).restrict f)}

theorem mem_sheetOpens {V : Opens X} :
    V ∈ sheetOpens f ↔ IsOpenEmbedding ((V : Set X).restrict f) := Iff.rfl

/-- **Every point of the source lies in a sheet.**

The sheet produced is the source of the `OpenPartialHomeomorph` that `IsLocalHomeomorph` supplies,
which is open by construction — so no interior has to be taken. -/
theorem IsLocalHomeomorph.exists_mem_sheetOpens (hf : IsLocalHomeomorph f) (x : X) :
    ∃ V ∈ sheetOpens f, x ∈ V := by
  obtain ⟨e, hxe, he⟩ := hf x
  exact ⟨⟨e.source, e.open_source⟩, he ▸ e.isOpenEmbedding_restrict, hxe⟩

/-- **The sheets of a local homeomorphism cover its source.** -/
theorem IsLocalHomeomorph.sSup_sheetOpens (hf : IsLocalHomeomorph f) :
    sSup (sheetOpens f) = ⊤ := by
  refine top_le_iff.1 fun x _ ↦ ?_
  obtain ⟨V, hV, hxV⟩ := IsLocalHomeomorph.exists_mem_sheetOpens f hf x
  exact Opens.mem_sSup.2 ⟨V, hV, hxV⟩

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Covering.Basic

/-!
# A closed local homeomorphism with finite fibres is a covering map

Material for `Mathlib/Topology/Covering/Basic.lean`; see `README.md` on the mirror tree.

Mathlib proves this for `IsCoveringMapOn` — `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`,
which takes a set `s`, finiteness of the fibres over `s`, and a local homeomorphism on `f ⁻¹' s`.
The statement below is that theorem at `s = Set.univ`, packaged as `IsCoveringMap`; Mathlib has
the relative form and not this one. The companion global statement it does have,
`isLocalHomeomorph_iff_isCoveringMap`, assumes the source **compact** instead of the map closed,
and is therefore not applicable to a non-compact source such as the punctured line.

The Hausdorff hypothesis on the source is Mathlib's and is used to separate the finitely many
points of a fibre; it is not removable.

## Main results

- `IsClosedMap.isCoveringMap_of_isLocalHomeomorph`: a closed local homeomorphism with finite
  fibres out of a Hausdorff space is a covering map.
-/

open Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

/-- **A closed local homeomorphism with finite fibres out of a Hausdorff space is a covering
map.**

This is `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` at `Set.univ`. No connectedness of
the target is needed: a point outside the range is evenly covered by the empty index type, which
is how that proof treats it. -/
theorem IsClosedMap.isCoveringMap_of_isLocalHomeomorph [T2Space E] (hf : IsClosedMap f)
    (hfin : ∀ x, (f ⁻¹' {x}).Finite) (h : IsLocalHomeomorph f) : IsCoveringMap f := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact hf.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ ↦ hfin x)
    ((isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp h).mono (Set.subset_univ _))

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Connected.Clopen

/-!
# The connected components of a disjoint union of connected spaces

Material for `Mathlib/Topology/Connected/Clopen.lean`, which is where `isClopen_range_sigmaMk`,
`Sigma.isConnected_iff` and `IsClopen.connectedComponent_subset` — the three facts this proof is
— all live; see `README.md` on the mirror tree. The import above is the target itself, so
upstreaming this costs it **nothing**, measured with
`python3 scripts/import_cost.py Oka/Topology/Connected/Clopen.lean`.

**Mathlib says which sets of a `Sigma` type are connected and does not say which are the
components.** `Sigma.isConnected_iff` characterises the connected subsets as the images of the
connected subsets of the members, and nothing reads it at a whole member: the statement that the
component of a point is the whole of its member — which needs the member *connected*, a
hypothesis `Sigma.isConnected_iff` does not carry — is not there in either direction.

## Main results

- `connectedComponent_sigmaMk`: **in a disjoint union of connected spaces the connected component
  of a point is the whole of the member it lies in.** The two inclusions are the two facts named
  above: the member's range is clopen, which bounds the component above, and it is connected,
  which bounds it below.
-/

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- **In a disjoint union of connected spaces the connected component of a point is the range of
the inclusion of the member it lies in.**

`IsClopen.connectedComponent_subset` at `isClopen_range_sigmaMk` is the upper bound — a clopen set
containing the point contains its component — and `isConnected_range` at `continuous_sigmaMk` is
the lower one, the range of the inclusion being a connected set containing the point.

**`ConnectedSpace` is asked of every member and used at one**, the one the point lies in; the
statement is false without it, a disconnected member having at least two components inside its own
range. -/
theorem connectedComponent_sigmaMk [∀ i, ConnectedSpace (X i)] (i : ι) (x : X i) :
    connectedComponent (Sigma.mk i x) = Set.range (Sigma.mk i) :=
  Set.Subset.antisymm (isClopen_range_sigmaMk.connectedComponent_subset ⟨x, rfl⟩)
    ((isConnected_range continuous_sigmaMk).isPreconnected.subset_connectedComponent ⟨x, rfl⟩)

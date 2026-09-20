/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Oka.Topology.Connected.Clopen

/-!
# What a homeomorphism does to connected components, and the components of a disjoint union

Material for `Mathlib/Topology/Homeomorph/Lemmas.lean`, which is where
`Homeomorph.image_connectedComponentIn` — the relative statement the first result below is the
absolute case of — lives; see `README.md` on the mirror tree. Upstreaming costs that target
**nothing**: `Mathlib.Topology.Connected.Clopen`, which the second and third results read through
`Oka/Topology/Connected/Clopen.lean`, is already in its closure of **624**, measured with
`python3 scripts/import_cost.py --target Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Connected.Clopen`.

**This is the half of the split that the `Sigma` statement is not**, and the direction of the
edge is what decides it. `connectedComponent_sigmaMk` (`Oka/Topology/Connected/Clopen.lean`)
names no `Homeomorph` and goes to `Mathlib/Topology/Connected/Clopen.lean`; everything here names
one, and putting it *there* instead would cost that file **10** modules —
`Mathlib.Topology.Homeomorph.Lemmas` and nine more, `Mathlib.Topology.Baire.Lemmas` and
`Mathlib.Topology.GDelta.Basic` among them — by the same script run the other way round. **Split
by destination, not by subject**, and here the two destinations are ten modules apart.

## Main results

- `Homeomorph.image_connectedComponent`: **the image of a connected component under a
  homeomorphism is the connected component of the image.**
- `Homeomorph.connectedComponent_sigma`: **a space homeomorphic to a disjoint union of
  connected spaces has the images of the members for its connected components.**
- `Homeomorph.finite_connectedComponents_of_sigma`: **and finitely many of them** when the index
  type is finite.

**A continuous bijection has none of these properties**, which is why every statement here asks
for a homeomorphism: the identity from a discrete space to an indiscrete one is a continuous
bijection carrying a point's component onto a proper subset of the image's.
-/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The image of a connected component under a homeomorphism is the connected component of the
image of the point.**

`Homeomorph.image_connectedComponentIn` at `Set.univ`, with `connectedComponentIn_univ` on both
sides and `Set.range_eq_univ` for the image of `Set.univ` under a surjection. -/
theorem Homeomorph.image_connectedComponent (h : X ≃ₜ Y) (x : X) :
    h '' connectedComponent x = connectedComponent (h x) := by
  simpa [connectedComponentIn_univ, Set.image_univ, Set.range_eq_univ.2 h.surjective] using
    h.image_connectedComponentIn (Set.mem_univ x)

variable {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]

/-- **In a space homeomorphic to a disjoint union of connected spaces, the connected component of
a point is the image of the member it comes from.**

`connectedComponent_sigmaMk` transported along the homeomorphism by
`Homeomorph.image_connectedComponent`. **Neither half is about the space `X`**, which carries no
hypothesis: what makes the components the members is the decomposition, and the homeomorphism is
what makes it a decomposition of `X` rather than of the `Sigma` type. -/
theorem Homeomorph.connectedComponent_sigma [∀ i, ConnectedSpace (Z i)]
    (h : (Σ i, Z i) ≃ₜ X) (i : ι) (x : Z i) :
    connectedComponent (h ⟨i, x⟩) = h '' Set.range (Sigma.mk i) := by
  rw [← _root_.connectedComponent_sigmaMk i x, h.image_connectedComponent]

/-- **A space homeomorphic to a disjoint union of finitely many connected spaces has finitely many
connected components.**

The map sending an index to the component of an arbitrary point of that member is surjective, by
the statement above read at a representative of a given component and at that arbitrary point:
the two components are images of the same member's range, so they are equal.
`Classical.arbitrary` is available because a `ConnectedSpace` is nonempty, which is the one place
that half of the class is used. -/
theorem Homeomorph.finite_connectedComponents_of_sigma [Finite ι] [∀ i, ConnectedSpace (Z i)]
    (h : (Σ i, Z i) ≃ₜ X) : Finite (ConnectedComponents X) :=
  Finite.of_surjective (fun i : ι ↦ ConnectedComponents.mk (h ⟨i, Classical.arbitrary (Z i)⟩))
    fun q ↦ by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
      refine ⟨(h.symm x).1, ?_⟩
      conv_rhs => rw [show x = h ⟨(h.symm x).1, (h.symm x).2⟩ by simp]
      rw [ConnectedComponents.coe_eq_coe, h.connectedComponent_sigma, h.connectedComponent_sigma]

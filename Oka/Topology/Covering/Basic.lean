/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Covering.Basic

/-!
# Three statements about covering maps: two criteria, and constancy of the fibre

Material for `Mathlib/Topology/Covering/Basic.lean`; see `README.md` on the mirror tree. Three
independent statements, sharing only their destination.

## A closed local homeomorphism with finite fibres is a covering map

Mathlib proves this for `IsCoveringMapOn` — `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`,
which takes a set `s`, finiteness of the fibres over `s`, and a local homeomorphism on `f ⁻¹' s`.
The statement below is that theorem at `s = Set.univ`, packaged as `IsCoveringMap`; Mathlib has
the relative form and not this one. The companion global statement it does have,
`isLocalHomeomorph_iff_isCoveringMap`, assumes the source **compact** instead of the map closed,
and is therefore not applicable to a non-compact source such as the punctured line.

The Hausdorff hypothesis on the source is Mathlib's and is used to separate the finitely many
points of a fibre; it is not removable.

## A covering map with finite fibres is a closed map

The converse of the criterion above, and the direction Mathlib does not have in any form: across
`Mathlib/Topology/Covering/`, `isClosedMap` occurs only inside proofs. `IsCoveringMap.isClosedMap`
below is what makes a finite covering space *finite* in the sense a morphism of complex analytic
spaces is asked to be: it supplies the closed base map that
`ComplexAnalytic.AnalyticSpace.IsFinite` asks for and that finite fibres do not give.

**That half is what it is the only input for, and not the construction.**
`Oka/AnalyticSpace/CoveringSpace.lean` takes its cover from `IsLocalHomeomorph.sSup_sheetOpens` in
`Oka/Topology/IsLocalHomeomorph.lean`, which Mathlib also does not have, and more of this mirror
tree reaches it through the inverse image sheaf — `TopCat.Presheaf.stalkPushforward_naturality` in
`Oka/Topology/Sheaves/Stalks.lean` is used to prove the stalk isomorphism that construction's local
isomorphism rests on. No number is given here because it is not one this file could keep true.

The proof reads the evenly covered neighbourhood as what the definition literally is — an open
`U ∋ x`, and a homeomorphism `H : f ⁻¹' U ≃ₜ U × I` over `U` — and pushes the closed set across
it. Given `C` closed and `x ∉ f '' C`, the image `H '' C` is closed in `U × I`, and it misses the
slice `{x} × I` because a point of that slice lies over `x`. So each of the finitely many `i : I`
gives an open set of `U` around `x` avoiding the `i`-th sheet of `C`, and their intersection is
the neighbourhood wanted.

**Finiteness of the fibre is used once, for that intersection to be open**, and it is used at the
index type `I = f ⁻¹' {x}`, which is why the hypothesis is about fibres and not about `E`. **No
separation axiom is used at all** — unlike the criterion above, whose `T2Space E` is Mathlib's and
is not removable. And **the empty fibre is not a special case**: the intersection over an empty
index type is `U` itself, which is the right answer, since `f ⁻¹' U` is then empty and `U` misses
`f '' C` outright.

## The fibres of a covering map over a preconnected base

`IsCoveringMap.nonempty_homeomorph_fiber`: over a preconnected base any two fibres of a covering
map are homeomorphic. This is what connectedness of the base buys — the *number of sheets* — and
it is the statement that a covering map itself does not give: `IsCoveringMap` says every point has
an evenly covered neighbourhood, with the fibre over that point as the index type, and says
nothing at all relating the index types at two different points.

The argument is the usual clopen one and the whole of its content is **local constancy**, which in
turn rests on one observation Mathlib does not state:

**`IsEvenlyCovered f x I` mentions `x` only through `x ∈ U`.** Unfolded it is a `U`, its openness,
the openness of `f ⁻¹' U`, a homeomorphism `f ⁻¹' U ≃ₜ U × I` and a compatibility, and none of the
last four depends on `x`. So the *same witness* serves every point of `U`, which is
`IsEvenlyCovered.eventually`. Everything below is that fact plus `IsEvenlyCovered.fiberHomeomorph`,
which is Mathlib's.

Two details of the clopen step are worth stating because each cost a failed attempt:

* **both** halves are the same local-constancy fact. `Sᶜ` is open because `Nonempty (· ≃ₜ ·)` is
  symmetric and transitive, not by a second argument;
* `IsClosed S` is the structure constructor applied to openness of the complement,
  `⟨hclosed⟩`. `isClosed_compl_iff` is about `IsClosed Sᶜ` and is the wrong lemma here.

**`PreconnectedSpace`, not `ConnectedSpace`.** Nonemptiness of the base plays no part, and asking
for it would make the statement fail on the empty space for no reason.

## Main results

- `IsClosedMap.isCoveringMap_of_isLocalHomeomorph`: a closed local homeomorphism with finite
  fibres out of a Hausdorff space is a covering map.
- `IsCoveringMap.isClosedMap`: **a covering map with finite fibres is closed**, which is the
  converse of the previous item with the Hausdorff hypothesis dropped.
- `IsEvenlyCovered.eventually`: an evenly covered point is evenly covered on a neighbourhood, with
  the same index type.
- `IsCoveringMap.eventually_nonempty_homeomorph`: the fibres of a covering map are locally
  constant up to homeomorphism.
- `IsCoveringMap.nonempty_homeomorph_fiber`: **over a preconnected base, any two fibres of a
  covering map are homeomorphic.**
-/

open Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
  {I : Type*} [TopologicalSpace I]

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

/-- **A covering map with finite fibres is a closed map.**

The converse of `IsClosedMap.isCoveringMap_of_isLocalHomeomorph`, with the Hausdorff hypothesis
dropped: nothing below separates two points of a fibre, it only counts them.

Given a closed `C` and a point `x` outside `f '' C`, the evenly covered neighbourhood of `x` is an
open `U` and a homeomorphism `H : f ⁻¹' U ≃ₜ U × (f ⁻¹' {x})` over `U`. The image of `C` under `H`
is closed, and misses every point of the slice over `x`, because such a point is a preimage of `x`
and `x ∉ f '' C`. Intersecting the finitely many slices of the complement gives the neighbourhood.

**Finiteness of the fibre is used exactly once**, for that intersection to be open; the empty
fibre is not a special case, since the empty intersection is `U`, which is then disjoint from
`f '' C` because `f ⁻¹' U` is empty. -/
theorem IsCoveringMap.isClosedMap (hf : IsCoveringMap f) (hfin : ∀ x, (f ⁻¹' {x}).Finite) :
    IsClosedMap f := by
  intro C hC
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨_, U, hxU, hU, hfU, H, hH⟩ := hf x
  have : Finite (f ⁻¹' {x}) := (hfin x).to_subtype
  -- The image of `C` in the trivialisation, a closed subset of `U × (f ⁻¹' {x})`.
  set D : Set (U × (f ⁻¹' {x})) := H '' (Subtype.val ⁻¹' C) with hD
  have hDclosed : IsClosed D := H.isClosedMap _ (hC.preimage continuous_subtype_val)
  -- The points of `U` no sheet of which meets `C`.
  set W : Set U := ⋂ i : (f ⁻¹' {x}), (fun u ↦ (u, i)) ⁻¹' Dᶜ with hW
  have hWopen : IsOpen W :=
    isOpen_iInter_of_finite fun i ↦ hDclosed.isOpen_compl.preimage (by fun_prop)
  have hxW : (⟨x, hxU⟩ : U) ∈ W := by
    refine Set.mem_iInter.2 fun i hmem ↦ ?_
    obtain ⟨e, heC, hey⟩ := hmem
    refine hx ⟨(e : E), heC, ?_⟩
    have := hH e
    rw [hey] at this
    exact this.symm
  refine Filter.mem_of_superset (hU.isOpenMap_subtype_val W hWopen |>.mem_nhds
    ⟨⟨x, hxU⟩, hxW, rfl⟩) ?_
  rintro _ ⟨u, huW, rfl⟩ ⟨c, hcC, hfc⟩
  have hcU : c ∈ f ⁻¹' U := by rw [Set.mem_preimage, hfc]; exact u.2
  have hfst : (H ⟨c, hcU⟩).1 = u := Subtype.ext ((hH ⟨c, hcU⟩).trans hfc)
  exact (Set.mem_iInter.1 huW (H ⟨c, hcU⟩).2) ⟨⟨c, hcU⟩, hcC, by rw [← hfst]⟩

/-- **An evenly covered point is evenly covered on a whole neighbourhood, with the same index
type.**

`IsEvenlyCovered f x I` is a `U` containing `x` together with data over `U` — its openness, the
openness of `f ⁻¹' U`, a homeomorphism `f ⁻¹' U ≃ₜ U × I` and its compatibility with `f` — and
**`x` occurs in none of that data except through `x ∈ U`.** So the witness for `x` is verbatim a
witness for every `y ∈ U`, and the proof destructures it and puts it back together.

Note that the index type is the *same* `I`, which is what makes this usable: applied to
`IsCoveringMap f` at `x`, whose index type is `f ⁻¹' {x}`, it says every nearby point has fibre
`f ⁻¹' {x}` — not merely that every nearby point is evenly covered by something.

Mathlib does not have this; it sits with `IsEvenlyCovered.of_fiber_homeomorph`. -/
theorem IsEvenlyCovered.eventually {x : X} (h : IsEvenlyCovered f x I) :
    ∀ᶠ y in 𝓝 x, IsEvenlyCovered f y I := by
  obtain ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  filter_upwards [hU.mem_nhds hxU] with y hyU
  exact ⟨inst, U, hyU, hU, hfU, H, hH⟩

/-- **The fibres of a covering map are locally constant up to homeomorphism.**

`IsCoveringMap f` is by definition `∀ x, IsEvenlyCovered f x (f ⁻¹' {x})`, so
`IsEvenlyCovered.eventually` at `x` says that every nearby `y` is evenly covered **with index type
`f ⁻¹' {x}`**; `IsEvenlyCovered.fiberHomeomorph` then identifies that index type with `f ⁻¹' {y}`.

The conclusion is `Nonempty (… ≃ₜ …)` rather than a homeomorphism, because there is no canonical
choice: the identification depends on the evenly covered neighbourhood, and a different one gives
a different homeomorphism. Nothing below needs a canonical one. -/
theorem IsCoveringMap.eventually_nonempty_homeomorph (hf : IsCoveringMap f) (x : X) :
    ∀ᶠ y in 𝓝 x, Nonempty ((f ⁻¹' {y}) ≃ₜ (f ⁻¹' {x})) := by
  filter_upwards [(hf x).eventually] with y hy
  exact ⟨hy.fiberHomeomorph.symm⟩

/-- **Over a preconnected base, any two fibres of a covering map are homeomorphic.**

This is what connectedness of the base is for, and `IsCoveringMap` on its own does not give it:
being evenly covered relates the points *near* `x` to `x`, and nothing in the definition relates
two points that are far apart.

The proof is the clopen argument on `S = {z | Nonempty ((f ⁻¹' {z}) ≃ₜ (f ⁻¹' {x}))}`. Both halves
are `IsCoveringMap.eventually_nonempty_homeomorph` and nothing else — `Sᶜ` is open because
`Nonempty (· ≃ₜ ·)` is symmetric and transitive, so a point near a point *not* in `S` cannot be in
`S` either. `S` is nonempty because `x ∈ S` by `Homeomorph.refl`.

`PreconnectedSpace` and not `ConnectedSpace`: the base being nonempty is never used, and over the
empty space the statement is vacuous rather than false. -/
theorem IsCoveringMap.nonempty_homeomorph_fiber [PreconnectedSpace X] (hf : IsCoveringMap f)
    (x y : X) : Nonempty ((f ⁻¹' {x}) ≃ₜ (f ⁻¹' {y})) := by
  set S : Set X := {z | Nonempty ((f ⁻¹' {z}) ≃ₜ (f ⁻¹' {x}))} with hS
  have hopen : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
    filter_upwards [hf.eventually_nonempty_homeomorph z] with w hw
    exact ⟨hw.some.trans hz.some⟩
  have hcompl : IsOpen Sᶜ := by
    refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
    filter_upwards [hf.eventually_nonempty_homeomorph z] with w hw hw'
    exact hz ⟨hw.some.symm.trans hw'.some⟩
  have huniv : S = Set.univ :=
    IsClopen.eq_univ ⟨⟨hcompl⟩, hopen⟩ ⟨x, ⟨Homeomorph.refl _⟩⟩
  exact ⟨(Set.eq_univ_iff_forall.mp huniv y).some.symm⟩

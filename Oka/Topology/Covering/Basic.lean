/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Covering.Basic

/-!
# Four statements about covering maps: two criteria, a cancellation, and constancy of the fibre

Material for `Mathlib/Topology/Covering/Basic.lean`; see `README.md` on the mirror tree. Four
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

## Closedness cancels along a covering map, with no separation axiom

`IsCoveringMap.isClosedMap_of_comp`: if `f` is a covering map and `f ∘ u` is closed then `u` is
closed, for a `u` asked only to be continuous. **Mathlib has no cancellation lemma for
`IsCoveringMap` at all** — `comp_homeomorph` and `homeomorph_comp` conjugate by a homeomorphism,
and there is no composition lemma either.

The classical statement of this shape asks the second map to be **separated** and factors the
first through its graph in a fibre product. Neither is used below. A covering map instead
decomposes `f ⁻¹' U` over an evenly covered `U` into open sheets, and **`f` is injective on each
one**; that injectivity is the whole content, and the rest of the proof is that a sheet is open
with open complement in `f ⁻¹' U`, so that a closed set of the source stays closed after being cut
down to one sheet.

**What earns this its place is the separation axiom it does not ask for, and it is worth being
exact about what that is worth.** Mathlib's three cancellations for proper maps are in
`Mathlib/Topology/Maps/Proper/Basic.lean` and none of them applies: two ask the composite's second
factor to be injective or its first to be surjective, and the third, `isProperMap_of_comp_of_t2`,
asks the **middle space to be Hausdorff**. Where a Hausdorff middle space is available that third
one is both shorter and more general than this — it asks nothing whatever of the second map —
and it is what `Oka/AnalyticSpace/Finite.lean` uses for the analytic statement of this shape.
`IsCoveringMap.isClosedMap_of_comp` is what is left when no separation axiom is available at all,
and Mathlib has nothing there, not even at `IsSeparatedMap`, which a covering map satisfies.

**Nothing in this repository consumes it**, and that is said rather than left to be discovered: it
is mirror-tree material stated for its own sake, in a file whose other statements about closedness
and covering maps are its natural neighbours.

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
- `IsCoveringMap.isClosedMap_of_comp`: **closedness cancels along a covering map** — if `f` is a
  covering map and `f ∘ u` is closed then so is `u`, with no hypothesis on `u` beyond continuity
  and no separation axiom anywhere.
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

/-- **Closedness cancels along a covering map**: if `f` is a covering map and `f ∘ u` is a closed
map, then `u` is closed.

Nothing is asked of `u` beyond continuity — not that it be closed, injective, surjective or a local
homeomorphism — and **no separation axiom is used**, on any of the three spaces.

The classical statement of this shape is *a map whose composite with a separated map is proper is
proper*, proved by factoring `u` through its graph in a fibre product. **Neither ingredient is used
here.** What a covering map supplies instead is a *sheet*: for `y : E` there is an evenly covered
`U ∋ f y` and a decomposition of `f ⁻¹' U` into open pieces on each of which `f` is injective. The
proof is that decomposition and nothing else:

* the sheet `V ∋ y` and the union `V'` of the other sheets are **both open**, because the sheet
  index is `Prod.snd ∘ H` into a discrete type, so `A := C ∩ u ⁻¹' V` is closed *in*
  `u ⁻¹' (f ⁻¹' U)` — which is what `hAcl` says, and is where `V'` is used;
* therefore `closure A` is a closed set on which the hypothesis can be spent, and
  `T := (f ∘ u) '' closure A` is closed;
* `f y ∉ T`: a witness would lie in `A` by the previous point, so its image under `u` lies in `V`
  alongside `y` and has the same image under `f`, and **`f` is injective on `V`** — so it *is* `y`,
  contradicting `y ∉ u '' C`;
* `V ∩ f ⁻¹' Tᶜ` is then an open neighbourhood of `y` missing `u '' C`.

**Injectivity on a sheet is the whole of what the hypothesis buys**, and it is what fails for a
closed local homeomorphism with finite fibres that is not a covering map — the line with two
origins over the line, whose two origins have no disjoint neighbourhoods and hence no sheet
containing exactly one of them. `Oka/AnalyticSpace/Finite.lean` records that example as the reason
this statement is false with `IsCoveringMap f` weakened to *`f` closed with finite fibres*, and
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` (`OkaTest/FiniteEtaleCancel.lean`)
compiles a witness for the weakening — a weaker one, since its second map is not a local
homeomorphism.

**Note what those two witnesses have in common besides failing to be covering maps: their `E` is
not Hausdorff.** That is not an accident, and it means this lemma is *not* the cheapest route to
any statement in which `E` is known to be Hausdorff. There `isProperMap_of_comp_of_t2` applies —
Mathlib's proper-map cancellation, whose separation hypothesis is on `E` and which asks nothing at
all of the first map — and it is both shorter and more general. This lemma is what remains when no
separation axiom is available, which is the case Mathlib does not cover, at `IsCoveringMap` or at
`IsSeparatedMap`; `IsCoveringMap.comp_homeomorph` and `IsCoveringMap.homeomorph_comp` are
conjugation by a homeomorphism and there is no composition lemma either.

**Nothing in this repository consumes this**; see the module docstring. -/
theorem IsCoveringMap.isClosedMap_of_comp {W : Type*} [TopologicalSpace W] {u : W → E}
    (hf : IsCoveringMap f) (hu : Continuous u) (h : IsClosedMap (f ∘ u)) :
    IsClosedMap u := by
  intro C hC
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨inst, U, hyU, hU, hfU, H, hH⟩ := hf (f y)
  have hymem : y ∈ f ⁻¹' U := hyU
  -- The sheet index of a point of `f ⁻¹' U`, a continuous map to a discrete type.
  set p : (f ⁻¹' U) → (f ⁻¹' {f y}) := fun e ↦ (H e).2 with hp
  have hpcont : Continuous p := continuous_snd.comp H.continuous
  set i₀ := p ⟨y, hymem⟩ with hi₀
  -- The sheet through `y`, and the union of all the other sheets.
  set V : Set E := Subtype.val '' (p ⁻¹' {i₀}) with hV
  set V' : Set E := Subtype.val '' (p ⁻¹' {i₀}ᶜ) with hV'
  have hVopen : IsOpen V :=
    hfU.isOpenMap_subtype_val _ (hpcont.isOpen_preimage _ (isOpen_discrete _))
  have hV'open : IsOpen V' :=
    hfU.isOpenMap_subtype_val _ (hpcont.isOpen_preimage _ (isOpen_discrete _))
  have hyV : y ∈ V := ⟨⟨y, hymem⟩, rfl, rfl⟩
  have hcover : ∀ e ∈ f ⁻¹' U, e ∈ V ∨ e ∈ V' := by
    intro e he
    by_cases hcase : p ⟨e, he⟩ = i₀
    · exact Or.inl ⟨⟨e, he⟩, hcase, rfl⟩
    · exact Or.inr ⟨⟨e, he⟩, hcase, rfl⟩
  have hdisj : ∀ e ∈ V, e ∉ V' := by
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    exact hb (by rw [show b = a from Subtype.ext hba]; exact ha)
  -- `f` is injective on a single sheet: two points of it have the same index, and equal images
  -- under `f` make their two `H`-components agree.
  have hinj : ∀ a ∈ V, ∀ b ∈ V, f a = f b → a = b := by
    rintro _ ⟨ea, hea, rfl⟩ _ ⟨eb, heb, rfl⟩ hab
    refine congrArg Subtype.val (H.injective (Prod.ext (Subtype.ext ?_) ?_))
    · rw [hH ea, hH eb]; exact hab
    · exact hea.trans heb.symm
  set A : Set W := C ∩ u ⁻¹' V with hA
  -- `A` is closed in `u ⁻¹' (f ⁻¹' U)`, which is what the other sheets being open gives.
  have hAcl : ∀ w ∈ closure A, u w ∈ f ⁻¹' U → w ∈ A := by
    intro w hw hwU
    refine ⟨hC.closure_subset (closure_mono Set.inter_subset_left hw), ?_⟩
    by_contra hnot
    obtain ⟨z, hz1, hz2⟩ :=
      mem_closure_iff.1 hw _ (hV'open.preimage hu) ((hcover _ hwU).resolve_left hnot)
    exact hdisj _ hz2.2 hz1
  set T : Set X := (f ∘ u) '' (closure A) with hT
  have hfyT : f y ∉ T := by
    rintro ⟨w, hw, hwy⟩
    have hwA : w ∈ A :=
      hAcl w hw (by rw [Set.mem_preimage, show f (u w) = f y from hwy]; exact hyU)
    exact hy ⟨w, hwA.1, hinj _ hwA.2 _ hyV hwy⟩
  refine Filter.mem_of_superset
    ((hVopen.inter (((h _ isClosed_closure).isOpen_compl).preimage hf.continuous)).mem_nhds
      ⟨hyV, hfyT⟩) ?_
  rintro y' ⟨hy'V, hy'T⟩ ⟨c, hcC, rfl⟩
  exact hy'T (Set.mem_image_of_mem _ (subset_closure ⟨hcC, hy'V⟩))

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

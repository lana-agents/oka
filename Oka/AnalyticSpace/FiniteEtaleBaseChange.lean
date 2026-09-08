/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringMap
import Oka.AnalyticSpace.CoveringSpace

/-!
# Base change of a finite étale morphism of complex analytic spaces

Let `q : E ⟶ B` be finite étale with `E` Hausdorff and let `f : B' ⟶ B` be **any** morphism of
complex analytic spaces. Then the fibre product `E ×_B B'` exists, its projection to `B'` is
finite étale again, and the square is a pullback in `ComplexAnalytic.AnalyticSpace`.

`Oka/AnalyticSpace/FiniteEtaleOver.lean` records the absence of this base change in its
`## What is not here` bullet **No base change of the class over a general cospan**, and again in
the docstring of `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fintypeFiberFunctor`. **That bullet
was headed *No pullback over a general cospan, so no base change* when this sentence was written
and until 2026-09-08**, when `Oka/AnalyticSpace/PullbackReduction.lean` made
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` a theorem and the first half of
the heading stopped being true; only the heading moved and what this file narrows is what it
always narrowed. **The bullet is narrowed by this file and is not narrowed to nothing, and this
file does not make that category a Galois category.** Those axioms quantify over cospans of
morphisms *of covers*, and a morphism of
covers is not known to be finite étale without `[T2Space]` of its target, which is taxis #1772's
remaining half; nor is a cover's total space assumed Hausdorff anywhere in that file. The four
further sentences of that file which cite the bullet by its heading are unaffected, and it says
so.

## The route, and why it touches no local model

The construction is the topological one, carried across by `Oka/AnalyticSpace/CoveringSpace.lean`.

1. **The carrier is Mathlib's set-level pullback** `Function.Pullback q.base f.base`, a subspace of
   the product, and its second projection is a covering map with finite fibres — by
   `IsCoveringMap.pullback_snd` and `Function.Pullback.finite_fiber_snd`, both in
   `Oka/Topology/Covering/Basic.lean`, applied to
   `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`.
2. **A covering map of the base carries an analytic structure for free.**
   `ComplexAnalytic.AnalyticSpace.coveringSpace` puts `π₂⁻¹𝒪_{B'}` on that carrier and
   `ComplexAnalytic.AnalyticSpace.isFiniteEtale_coveringSpaceHom` makes the second projection
   finite étale. Nothing is glued: that file's docstring says why the `ℂ`-algebra structure lands
   in global sections and needs no cover.
3. **The first projection is a morphism out of an inverse image**, and that is what
   `AlgebraicGeometry.LocallyRingedSpace.inverseImageMap` is for. Composed with the comparison
   isomorphism `E ≅ q.base⁻¹B`, which exists because `q` is a local isomorphism, it lands in `E`.
4. **The universal property is the uniqueness in
   `AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext`** — twice, once for each half. A
   morphism into `π₂⁻¹B'` is pinned by its base map and its composite to `B'`, and the base map of
   a morphism into a set-level pullback is pinned by its two components.

**No local model, no zero locus, no cutting out and no gluing of spaces occurs anywhere below**,
which is worth saying because the fibre product of analytic spaces is usually built that way and
this repository has a whole ladder of issues doing it that way.

## Where each hypothesis is spent

**`[T2Space E]` is spent exactly once**, in
`ComplexAnalytic.AnalyticSpace.isCoveringMap_baseChangeSndBase`, which is
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale` and nothing else; that lemma's
own docstring says why Mathlib's criterion separates the points of a fibre. **Nothing is assumed
of `B` or of `B'`**, and `f` is an arbitrary morphism — not finite, not étale, not injective.

**`[IsFiniteEtale q]` is spent twice and in two different halves.** Its `IsFinite` field supplies
the finite fibres, through `ComplexAnalytic.AnalyticSpace.finite_fiber_baseChangeSndBase`, which
needs no topology at all; its `IsLocalIso` field supplies the stalk isomorphisms that make
`ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso` an isomorphism. **The first projection
does not need `q` finite** and the second does not need `q` a local isomorphism; both are needed
for the square to be a pullback, because the space is built out of the covering property.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.baseChange`: **the fibre product `E ×_B B'`**, whose carrier is
  `Function.Pullback q.base f.base` on the nose and whose structure sheaf is `π₂⁻¹𝒪_{B'}`.
- `ComplexAnalytic.AnalyticSpace.baseChangeFst` and
  `ComplexAnalytic.AnalyticSpace.baseChangeSnd`: its two projections.
- `ComplexAnalytic.AnalyticSpace.baseChangeLift`: the morphism a commuting square induces into it.
- `ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso`: **the source of a local isomorphism
  is the inverse image of its target along its base map**, as an isomorphism of *locally ringed*
  spaces. `ComplexAnalytic.AnalyticSpace.coveringSpaceIso` is the analytic-space statement of the
  same fact and neither is stated in terms of the other.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_baseChangeSnd`: **the projection to `B'` is finite
  étale.**
- `ComplexAnalytic.AnalyticSpace.baseChange_square`: the square commutes.
- `ComplexAnalytic.AnalyticSpace.baseChange_hom_ext`: **two morphisms into the fibre product
  agreeing on both projections are equal.**
- `ComplexAnalytic.AnalyticSpace.isPullback_baseChange`: **the square is a pullback.**
- `ComplexAnalytic.AnalyticSpace.hasPullback_of_isFiniteEtale`: hence `Limits.HasPullback q f`, as
  an instance.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale`: and hence
  `Limits.pullback.snd q f` is finite étale — **the base-change statement in the spelling
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` is written in**.

## What is not here

* **This is not `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace`.** Every
  statement below has a finite étale leg in its cospan and a general cospan has none.
  `#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` **fails** at the
  commit that adds this file, on my own run, with the category positional so that it is fixed by
  the statement and not by a named argument. Gluing — taxis #1820's rung 3 — is what would close
  that, and this file goes around it rather than through it. **That prediction held**: the class
  became a theorem on 2026-09-08, in `Oka/AnalyticSpace/PullbackReduction.lean`, by gluing and by
  nothing else. The `#synth` sentence above is pinned to the commit that adds *this* file and is
  not retired; what this bullet still says is that no statement below is that class.
* **`[T2Space E]` is not removed and nothing here tries.** It is Mathlib's hypothesis in the
  criterion that turns a proper local homeomorphism into a covering map, and
  `Oka/AnalyticSpace/CoveringMap.lean` records why.
* **No `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` instance.** That class quantifies
  over *all* cospans with a leg in the class, including those whose finite étale leg has a
  non-Hausdorff source, and nothing below reaches one.
* **Nothing about the degree.** `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` would say the
  base change has the same number of sheets; the fibres do correspond, by
  `Function.Pullback.fst`, and no statement below says so.
* **No comparison with `ComplexAnalytic.AnalyticSpace.restrictHom`.** For `f` an open immersion
  `Oka/AnalyticSpace/PullbackOpen.lean` already builds this pullback, by restriction rather than
  by an inverse image, and the two are not compared here.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

variable {E B B' : AnalyticSpace.{u}} (q : E ⟶ B) (f : B' ⟶ B)

/-! ### The carrier, and the two projections as continuous maps -/

/-- **The carrier of the fibre product**: Mathlib's set-level pullback `Function.Pullback`, a
subtype of the product, with the subspace topology. -/
def baseChangeCarrier : TopCat.{u} :=
  TopCat.of (Function.Pullback q.toLRSHom.base f.toLRSHom.base)

/-- The first projection of the carrier, as a morphism of topological spaces. -/
def baseChangeFstBase : baseChangeCarrier q f ⟶ E.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨Function.Pullback.fst, continuous_fst.comp continuous_subtype_val⟩

/-- The second projection of the carrier, as a morphism of topological spaces. -/
def baseChangeSndBase : baseChangeCarrier q f ⟶ B'.toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨Function.Pullback.snd, continuous_snd.comp continuous_subtype_val⟩

/-- **The square of carriers commutes**, which is the defining property of a point of
`Function.Pullback` and is `rfl` at each point. It is stated in this direction — `snd ≫ f` on the
left — because that is the side the analytic structure is built on. -/
theorem baseChange_base_square :
    baseChangeSndBase q f ≫ f.toLRSHom.base = baseChangeFstBase q f ≫ q.toLRSHom.base := by
  ext z
  exact z.2.symm

/-- **The second projection is a covering map.** `IsCoveringMap.pullback_snd` at
`ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`, whose `Continuous` hypothesis
is `f`'s. **This is the one place `[T2Space E]` is used in this file.** -/
theorem isCoveringMap_baseChangeSndBase [IsFiniteEtale q] [T2Space E] :
    IsCoveringMap ⇑(baseChangeSndBase q f) :=
  (isCoveringMap_base_of_isFiniteEtale q).pullback_snd f.toLRSHom.base.hom.continuous

/-- **And its fibres are finite.** `Function.Pullback.finite_fiber_snd` uses neither a topology
nor the covering property, so this asks only for the `IsFinite` half of `IsFiniteEtale` and not
for `[T2Space E]`. -/
theorem finite_fiber_baseChangeSndBase [IsFiniteEtale q] (y : B') :
    (⇑(baseChangeSndBase q f) ⁻¹' {y}).Finite :=
  Function.Pullback.finite_fiber_snd (fun x ↦ IsFinite.finite_fiber (f := q) x) y

variable [IsFiniteEtale q] [T2Space E]

/-! ### The space and the projection to `B'` -/

/-- **The fibre product `E ×_B B'`**, as a complex analytic space: the covering space of `B'`
along the second projection of the carrier. Its structure sheaf is `π₂⁻¹𝒪_{B'}` and nothing is
glued. -/
def baseChange : AnalyticSpace.{u} :=
  AnalyticSpace.coveringSpace B' (baseChangeSndBase q f)
    (isCoveringMap_baseChangeSndBase q f).isLocalHomeomorph

/-- **The projection to `B'`.** -/
def baseChangeSnd : baseChange q f ⟶ B' :=
  AnalyticSpace.coveringSpaceHom B' (baseChangeSndBase q f)
    (isCoveringMap_baseChangeSndBase q f).isLocalHomeomorph

@[simp]
theorem base_baseChangeSnd :
    (baseChangeSnd q f).toLRSHom.base = baseChangeSndBase q f := rfl

/-- **The projection to `B'` is finite étale**, which is the whole of the base-change statement
for the class and needs none of the universal property below. -/
theorem isFiniteEtale_baseChangeSnd : IsFiniteEtale (baseChangeSnd q f) :=
  AnalyticSpace.isFiniteEtale_coveringSpaceHom B' (baseChangeSndBase q f)
    (isCoveringMap_baseChangeSndBase q f) (finite_fiber_baseChangeSndBase q f)

/-! ### The projection to `E` -/

omit [T2Space E] in
/-- **The comparison morphism of a local isomorphism is an isomorphism**, which is
`AlgebraicGeometry.LocallyRingedSpace.isIso_toInverseImage` fed the stalk field of
`ComplexAnalytic.AnalyticSpace.IsLocalIso`. -/
theorem isIso_toInverseImage_of_isLocalIso : IsIso (LocallyRingedSpace.toInverseImage q.toLRSHom) :=
  LocallyRingedSpace.isIso_toInverseImage _ fun z ↦ IsLocalIso.isIso_stalkMap z

omit [T2Space E] in
/-- **The source of a local isomorphism is the inverse image of its target along its base map**,
as an isomorphism of locally ringed spaces over the target.

`ComplexAnalytic.AnalyticSpace.coveringSpaceIso` says the same thing one category up, between
*analytic* spaces, and is not what is wanted here: what the first projection has to be built out
of is a morphism of locally ringed spaces, its `ℂ`-linearity being recovered afterwards from the
commuting square. -/
def inverseImageIsoOfIsLocalIso :
    E.toLocallyRingedSpace ≅
      LocallyRingedSpace.inverseImage B.toLocallyRingedSpace q.toLRSHom.base :=
  @asIso _ _ _ _ _ (isIso_toInverseImage_of_isLocalIso q)

set_option backward.isDefEq.respectTransparency false in
/-- **The fibre product's morphism to `B`**, which is the diagonal of the square and is the
morphism the first projection is built as a factorisation of. It is `π₂` followed by `f`. -/
def baseChangeToBase : (baseChange q f).toLocallyRingedSpace ⟶ B.toLocallyRingedSpace :=
  LocallyRingedSpace.inverseImageHom B'.toLocallyRingedSpace (baseChangeSndBase q f) ≫ f.toLRSHom

set_option backward.isDefEq.respectTransparency false in
/-- **The projection to `E`, as a morphism of locally ringed spaces.**

Three factors, and each is forced. `AlgebraicGeometry.LocallyRingedSpace.toInverseImage` at the
diagonal lands in `q.base⁻¹B` **along the diagonal's own base map**;
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq` at
`ComplexAnalytic.AnalyticSpace.baseChange_base_square` moves that to `q.base⁻¹B` along `q.base`,
which is the step whose base map is the first projection; and the inverse of
`ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso` lands in `E`.

**The `ℂ`-linearity is not proved here and is not proved directly anywhere.** It is
`ComplexAnalytic.IsCLinearHom.of_comp` at the square below, which is the same move
`Oka/AnalyticSpace/Basic.lean` uses for the inverse of an isomorphism. -/
def baseChangeFstLRS : (baseChange q f).toLocallyRingedSpace ⟶ E.toLocallyRingedSpace :=
  LocallyRingedSpace.toInverseImage (baseChangeToBase q f) ≫
    LocallyRingedSpace.inverseImageMapOfEq q.toLRSHom.base (baseChangeFstBase q f)
      (baseChangeToBase q f).base (baseChange_base_square q f) ≫
    (inverseImageIsoOfIsLocalIso q).inv

set_option backward.isDefEq.respectTransparency false in
/-- **The square commutes, at the level of locally ringed spaces.**

Each of the three factors of the first projection contributes one step:
`AlgebraicGeometry.LocallyRingedSpace.toInverseImage_comp` for the outer one,
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_comp` for the middle, and the
factorisation of `q` through its own inverse image for the inner. -/
theorem baseChangeFstLRS_comp :
    baseChangeFstLRS q f ≫ q.toLRSHom = baseChangeToBase q f := by
  have h0 : (inverseImageIsoOfIsLocalIso q).hom ≫
      LocallyRingedSpace.inverseImageHom B.toLocallyRingedSpace q.toLRSHom.base = q.toLRSHom :=
    LocallyRingedSpace.toInverseImage_comp q.toLRSHom
  have h1 := (inverseImageIsoOfIsLocalIso q).inv_hom_id_assoc
    (LocallyRingedSpace.inverseImageHom B.toLocallyRingedSpace q.toLRSHom.base)
  rw [h0] at h1
  rw [baseChangeFstLRS, Category.assoc, Category.assoc, h1,
    LocallyRingedSpace.inverseImageMapOfEq_comp, LocallyRingedSpace.toInverseImage_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **The projection to `E` is `ℂ`-linear**, by `ComplexAnalytic.IsCLinearHom.of_comp` at the
square: both legs into `B` are `ℂ`-linear for the same structure on `B`, so any morphism
factorising one through the other is `ℂ`-linear, whatever it is. -/
theorem isCLinearHom_baseChangeFstLRS :
    IsCLinearHom (baseChangeFstLRS q f) (baseChange q f).algebraMap E.algebraMap :=
  IsCLinearHom.of_comp (baseChangeFstLRS_comp q f)
    (IsCLinearHom.comp (baseChangeSnd q f).isCLinear f.isCLinear) q.isCLinear

/-- **The projection to `E`.** -/
def baseChangeFst : baseChange q f ⟶ E :=
  ⟨baseChangeFstLRS q f, isCLinearHom_baseChangeFstLRS q f⟩

/-- **The square commutes.** -/
theorem baseChange_square : baseChangeFst q f ≫ q = baseChangeSnd q f ≫ f :=
  forgetToLocallyRingedSpace.map_injective (baseChangeFstLRS_comp q f)

omit [T2Space E] in
/-- **The inverse of `ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso` is the identity
on points**, since the comparison morphism's base map is the identity on the nose. -/
theorem inverseImageIsoOfIsLocalIso_inv_base_apply
    (x : LocallyRingedSpace.inverseImage B.toLocallyRingedSpace q.toLRSHom.base) :
    (inverseImageIsoOfIsLocalIso q).inv.base x = x :=
  LocallyRingedSpace.iso_hom_base_inv_base_apply (inverseImageIsoOfIsLocalIso q) x

set_option backward.isDefEq.respectTransparency false in
/-- **The base map of the projection to `E` is the first projection of the carrier.** Of the three
factors two are the identity on points and the middle one is `h` by
`AlgebraicGeometry.LocallyRingedSpace.inverseImageMapOfEq_base`. -/
@[simp]
theorem base_baseChangeFst :
    (baseChangeFst q f).toLRSHom.base = baseChangeFstBase q f := by
  ext z
  change (inverseImageIsoOfIsLocalIso q).inv.base
      ((LocallyRingedSpace.inverseImageMapOfEq q.toLRSHom.base (baseChangeFstBase q f)
          (baseChangeToBase q f).base (baseChange_base_square q f)).base
        ((LocallyRingedSpace.toInverseImage (baseChangeToBase q f)).base z)) = _
  rw [inverseImageIsoOfIsLocalIso_inv_base_apply, LocallyRingedSpace.inverseImageMapOfEq_base]
  rfl

/-! ### The universal property -/

variable {Z : AnalyticSpace.{u}} (a : Z ⟶ E) (b : Z ⟶ B') (hab : a ≫ q = b ≫ f)

/-- **The lift on carriers**: the pair of the two base maps, which lands in the set-level pullback
because the square of analytic spaces commutes. -/
def baseChangeLiftBase : Z.toLocallyRingedSpace.toTopCat ⟶ baseChangeCarrier q f :=
  TopCat.ofHom
    ⟨fun z ↦ ⟨(a.toLRSHom.base z, b.toLRSHom.base z),
        congrFun (congrArg (fun m : Z.toLocallyRingedSpace ⟶ B.toLocallyRingedSpace ↦
          (m.base : Z.toLocallyRingedSpace.toTopCat → B.toLocallyRingedSpace.toTopCat))
          (congrArg Hom.toLRSHom hab)) z⟩,
      Continuous.subtype_mk (Continuous.prodMk a.toLRSHom.base.hom.continuous
        b.toLRSHom.base.hom.continuous) _⟩

omit [IsFiniteEtale q] [T2Space E] in
/-- **The lift is over `B'` on carriers**, by `rfl`. -/
theorem baseChangeLiftBase_snd :
    b.toLRSHom.base = baseChangeLiftBase q f a b hab ≫ baseChangeSndBase q f := rfl

omit [IsFiniteEtale q] [T2Space E] in
/-- **And over `E` on carriers**, by `rfl`. This is the half the universal property below cannot
get from the inverse-image uniqueness and has to have on the nose. -/
theorem baseChangeLiftBase_fst :
    a.toLRSHom.base = baseChangeLiftBase q f a b hab ≫ baseChangeFstBase q f := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The lift, as a morphism of locally ringed spaces**: the comparison morphism of `b` followed
by the functoriality of the inverse image at the carrier-level factorisation of `b`'s base map
through the second projection. -/
def baseChangeLiftLRS : Z.toLocallyRingedSpace ⟶ (baseChange q f).toLocallyRingedSpace :=
  LocallyRingedSpace.toInverseImage b.toLRSHom ≫
    LocallyRingedSpace.inverseImageMapOfEq (baseChangeSndBase q f) (baseChangeLiftBase q f a b hab)
      b.toLRSHom.base (baseChangeLiftBase_snd q f a b hab)

set_option backward.isDefEq.respectTransparency false in
/-- **The lift is over `B'`.** -/
theorem baseChangeLiftLRS_comp :
    baseChangeLiftLRS q f a b hab ≫ (baseChangeSnd q f).toLRSHom = b.toLRSHom := by
  rw [baseChangeLiftLRS, Category.assoc]
  exact (congrArg (fun m ↦ LocallyRingedSpace.toInverseImage b.toLRSHom ≫ m)
    (LocallyRingedSpace.inverseImageMapOfEq_comp (baseChangeSndBase q f)
      (baseChangeLiftBase q f a b hab) b.toLRSHom.base
      (baseChangeLiftBase_snd q f a b hab))).trans
    (LocallyRingedSpace.toInverseImage_comp b.toLRSHom)

set_option backward.isDefEq.respectTransparency false in
/-- **The morphism a commuting square induces into the fibre product.** Its `ℂ`-linearity is
`ComplexAnalytic.IsCLinearHom.of_comp` at the factorisation through `B'`, the same move the first
projection's linearity uses. -/
def baseChangeLift : Z ⟶ baseChange q f :=
  ⟨baseChangeLiftLRS q f a b hab,
    IsCLinearHom.of_comp (baseChangeLiftLRS_comp q f a b hab) b.isCLinear
      (baseChangeSnd q f).isCLinear⟩

/-- **The lift factors the second leg.** -/
theorem baseChangeLift_snd : baseChangeLift q f a b hab ≫ baseChangeSnd q f = b :=
  forgetToLocallyRingedSpace.map_injective (baseChangeLiftLRS_comp q f a b hab)

set_option backward.isDefEq.respectTransparency false in
/-- **The base map of the lift is the pair.** -/
@[simp]
theorem base_baseChangeLift :
    (baseChangeLift q f a b hab).toLRSHom.base = baseChangeLiftBase q f a b hab := by
  change (LocallyRingedSpace.toInverseImage b.toLRSHom).base ≫
    (LocallyRingedSpace.inverseImageMapOfEq (baseChangeSndBase q f) (baseChangeLiftBase q f a b hab)
      b.toLRSHom.base (baseChangeLiftBase_snd q f a b hab)).base = _
  rw [LocallyRingedSpace.inverseImageMapOfEq_base, LocallyRingedSpace.toInverseImage_base]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- **The lift factors the first leg**, which is the half that needs the uniqueness.

Both sides are morphisms `Z ⟶ E`; `ComplexAnalytic.AnalyticSpace.inverseImageIsoOfIsLocalIso` is
a monomorphism, so it is enough to compare them in `q.base⁻¹B`, where
`AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext` applies. Its base hypothesis is
`ComplexAnalytic.AnalyticSpace.baseChangeLiftBase_fst`, which is `rfl`, and its hypothesis over
`B` is the two ways round the square. -/
theorem baseChangeLift_fst : baseChangeLift q f a b hab ≫ baseChangeFst q f = a := by
  refine forgetToLocallyRingedSpace.map_injective ?_
  refine (cancel_mono (inverseImageIsoOfIsLocalIso q).hom).mp ?_
  refine LocallyRingedSpace.inverseImage_hom_ext _ q.toLRSHom.base ?_ ?_
  · change ((baseChangeLift q f a b hab).toLRSHom.base ≫ (baseChangeFst q f).toLRSHom.base) ≫
      (inverseImageIsoOfIsLocalIso q).hom.base
      = a.toLRSHom.base ≫ (inverseImageIsoOfIsLocalIso q).hom.base
    rw [base_baseChangeLift, base_baseChangeFst, ← baseChangeLiftBase_fst]
  · have h1 : (inverseImageIsoOfIsLocalIso q).hom ≫
        LocallyRingedSpace.inverseImageHom B.toLocallyRingedSpace q.toLRSHom.base = q.toLRSHom :=
      LocallyRingedSpace.toInverseImage_comp q.toLRSHom
    rw [Category.assoc, Category.assoc, h1, Functor.map_comp, Category.assoc]
    change baseChangeLiftLRS q f a b hab ≫ baseChangeFstLRS q f ≫ q.toLRSHom
      = a.toLRSHom ≫ q.toLRSHom
    rw [baseChangeFstLRS_comp]
    change baseChangeLiftLRS q f a b hab ≫ (baseChangeSnd q f).toLRSHom ≫ f.toLRSHom
      = a.toLRSHom ≫ q.toLRSHom
    rw [← Category.assoc, baseChangeLiftLRS_comp]
    exact (congrArg Hom.toLRSHom hab).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Two morphisms into the fibre product agreeing on both projections are equal.**

`AlgebraicGeometry.LocallyRingedSpace.inverseImage_hom_ext` again, and it asks for less than the
hypotheses give: the composite to `B'` is the second projection alone, and the two projections are
used only to pin the base map, where a point of `Function.Pullback` is determined by its two
components. -/
theorem baseChange_hom_ext {u v : Z ⟶ baseChange q f}
    (h1 : u ≫ baseChangeFst q f = v ≫ baseChangeFst q f)
    (h2 : u ≫ baseChangeSnd q f = v ≫ baseChangeSnd q f) : u = v := by
  refine forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.inverseImage_hom_ext _ (baseChangeSndBase q f) ?_ ?_)
  · have e1 : u.toLRSHom.base ≫ baseChangeFstBase q f
        = v.toLRSHom.base ≫ baseChangeFstBase q f := by
      rw [← base_baseChangeFst]
      exact congrArg (fun m : Z ⟶ E ↦ m.toLRSHom.base) h1
    have e2 : u.toLRSHom.base ≫ baseChangeSndBase q f
        = v.toLRSHom.base ≫ baseChangeSndBase q f := by
      rw [← base_baseChangeSnd]
      exact congrArg (fun m : Z ⟶ B' ↦ m.toLRSHom.base) h2
    ext z
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg (fun g : Z.toLocallyRingedSpace.toTopCat ⟶
        E.toLocallyRingedSpace.toTopCat ↦ g z) e1
    · exact congrArg (fun g : Z.toLocallyRingedSpace.toTopCat ⟶
        B'.toLocallyRingedSpace.toTopCat ↦ g z) e2
  · exact congrArg Hom.toLRSHom h2

/-- **The square is a pullback.** -/
theorem isPullback_baseChange :
    CategoryTheory.IsPullback (baseChangeFst q f) (baseChangeSnd q f) q f :=
  CategoryTheory.IsPullback.of_isLimit
    (Limits.PullbackCone.IsLimit.mk (baseChange_square q f)
      (fun s ↦ baseChangeLift q f s.fst s.snd s.condition)
      (fun s ↦ baseChangeLift_fst q f s.fst s.snd s.condition)
      (fun s ↦ baseChangeLift_snd q f s.fst s.snd s.condition)
      (fun s _ hm1 hm2 ↦ baseChange_hom_ext q f
        (hm1.trans (baseChangeLift_fst q f s.fst s.snd s.condition).symm)
        (hm2.trans (baseChangeLift_snd q f s.fst s.snd s.condition).symm)))

/-- **So the fibre product exists**, at every cospan one of whose legs is finite étale with
Hausdorff source. An instance, so that `CategoryTheory.Limits.pullback q f` elaborates. -/
instance hasPullback_of_isFiniteEtale : Limits.HasPullback q f :=
  (isPullback_baseChange q f).hasPullback

/-- **And the base change of a finite étale morphism is finite étale**, in the spelling that
mentions `CategoryTheory.Limits.pullback` rather than
`ComplexAnalytic.AnalyticSpace.baseChangeSnd`.

The two differ by `CategoryTheory.IsPullback.isoPullback`, and finite étaleness crosses it by
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_isIso` and
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_comp`. -/
theorem isFiniteEtale_pullback_snd_of_isFiniteEtale :
    IsFiniteEtale (Limits.pullback.snd q f) := by
  haveI := isFiniteEtale_baseChangeSnd q f
  haveI := isFiniteEtale_of_isIso (isPullback_baseChange q f).isoPullback.inv
  rw [← (isPullback_baseChange q f).isoPullback_inv_snd]
  exact isFiniteEtale_comp _ _

end ComplexAnalytic.AnalyticSpace

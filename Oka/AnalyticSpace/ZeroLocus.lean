/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Topology.Sheaves.Sheafify
import Oka.AnalyticSpace.Basic
import Oka.Topology.Sheaves.QuotientPresheaf
import Oka.Topology.Sheaves.Stalks

/-!
# The closed subspace cut out by a family of global sections

Let `Y` be a locally ringed space and `f : κ → Γ(Y, 𝒪_Y)` a family of global sections. Their
**zero locus** is the set of points at which no germ of any `f i` is a unit. This file makes it
a locally ringed space `Y.zeroLocusSubspace f`, constructs the closed immersion
`Y.zeroLocusSubspaceι f` into `Y`, and proves that the immersion satisfies all four conditions
of `ComplexAnalytic.IsCutOutBy` (`Oka/AnalyticSpace/Basic.lean`).

Nothing here is analytic; everything holds for an arbitrary locally ringed space. In particular
the two topological conditions are cheap: the zero locus is closed because the locus where the
germ of a section is *invertible* is open — that is `AlgebraicGeometry.RingedSpace.basicOpen`,
which is an `Opens` by construction — and the zero locus is the complement of the union of those
loci.

## The structure sheaf, and its stalks

Write `ι : Z ⟶ Y` for the inclusion of the zero locus. The structure sheaf of `Z` is
`ι⁻¹` of the sheafification of the quotient presheaf `𝒪_Y ⧸ (f)`, that is,

`𝒪_Z := (sheafify (ι⁻¹ (sheafify (𝒪_Y ⧸ (f)))))`.

Sheafifying twice looks wasteful but is what makes the stalk computation a chain of three
Mathlib isomorphisms with nothing to prove in between: sheafification does not change stalks
(`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, twice) and the inverse image of a
presheaf has the expected stalks (`TopCat.Presheaf.stalkPullbackIso`). Composing them,
`zeroLocusStalkIso` identifies the stalk of `𝒪_Z` at `z` with the stalk at `ι z` of the
quotient *presheaf*, whose surjectivity and kernel over `𝒪_Y` are exactly the content of
`Oka/Topology/Sheaves/QuotientPresheaf.lean`. That yields `stalkMap_zeroLocusιHom`, which
factors the map on stalks as the projection onto the quotient followed by an isomorphism, and
the remaining two conditions of `IsCutOutBy` follow at once.

The stalks are local rings because they are quotients of the local rings of `Y` by ideals which
are proper *precisely at the points of the zero locus* — which is where the description of the
underlying set does its second piece of work.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.zeroLocus`: the set of points at which every germ of
  every `f i` is a non-unit.
- `AlgebraicGeometry.LocallyRingedSpace.zeroLocusSpace` and `zeroLocusι`: that set as a
  topological space, and its inclusion into the ambient space.
- `AlgebraicGeometry.LocallyRingedSpace.zeroLocusPresheaf`: the structure sheaf of the zero
  locus, and `zeroLocusSubspace`: the zero locus as a locally ringed space.
- `AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspaceι`: the closed immersion of the zero
  locus into the ambient space.
- `AlgebraicGeometry.LocallyRingedSpace.zeroLocusStalkQuotientEquiv`: the stalk of `𝒪_Z` at `z`
  as the quotient of the stalk of `𝒪_Y` at `z` by the germs of the `f i`.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.isClosed_zeroLocus`: the zero locus is closed.
- `AlgebraicGeometry.LocallyRingedSpace.isClosedEmbedding_zeroLocusι` and
  `range_zeroLocusι`: the two topological conditions of `ComplexAnalytic.IsCutOutBy`,
  discharged for any candidate structure sheaf on the zero locus.
- `AlgebraicGeometry.LocallyRingedSpace.stalkMap_zeroLocusιHom`: the map on stalks is the
  projection onto the quotient by the germs of the `f i`, followed by an isomorphism; hence
  `surjective_stalkMap_zeroLocusιHom` and `ker_stalkMap_zeroLocusιHom`.
- `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`: **the zero locus of
  finitely many global sections is cut out by them.** This is the first construction in the
  development of a locally ringed space satisfying `ComplexAnalytic.IsCutOutBy` by a family
  which is not empty.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry Topology
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u}) {κ : Type*} (f : κ → Y.presheaf.obj (op ⊤))

section Topology

/-- The **zero locus** of a family of global sections of the structure sheaf: the points at
which every germ of every `f i` fails to be a unit, equivalently lies in the maximal ideal of
the stalk.

This is the underlying set of the closed subspace that the `f i` cut out; it is exactly the set
appearing in `ComplexAnalytic.IsCutOutBy.range_base`. -/
def zeroLocus : Set Y :=
  {y | ∀ i, Y.presheaf.Γgerm y (f i) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)}

/-- Membership in the zero locus, unfolded. -/
lemma mem_zeroLocus_iff {y : Y} :
    y ∈ Y.zeroLocus f ↔
      ∀ i, Y.presheaf.Γgerm y (f i) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
  Iff.rfl

/-- A point lies in the zero locus exactly when no germ there is a unit. -/
lemma mem_zeroLocus_iff_not_isUnit {y : Y} :
    y ∈ Y.zeroLocus f ↔ ∀ i, ¬ IsUnit (Y.presheaf.Γgerm y (f i)) := by
  simp only [mem_zeroLocus_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- The locus where the germ of a global section is a unit is open. This is
`AlgebraicGeometry.RingedSpace.basicOpen`, restated as a statement about a `Set`. -/
lemma isOpen_setOf_isUnit_germ (s : Y.presheaf.obj (op ⊤)) :
    IsOpen {y : Y | IsUnit (Y.presheaf.Γgerm y s)} := by
  have h : {y : Y | IsUnit (Y.presheaf.Γgerm y s)} = (Y.toRingedSpace.basicOpen s).carrier :=
    Set.ext fun y ↦ (Y.toRingedSpace.mem_top_basicOpen s y).symm
  rw [h]
  exact (Y.toRingedSpace.basicOpen s).isOpen

/-- The complement of the zero locus is the union of the loci where some `f i` is invertible. -/
lemma compl_zeroLocus :
    (Y.zeroLocus f)ᶜ = ⋃ i, {y : Y | IsUnit (Y.presheaf.Γgerm y (f i))} := by
  ext y
  simp [zeroLocus, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- **The zero locus of a family of global sections is closed.**

No analyticity is involved: this holds on any locally ringed space, because the locus where a
section is invertible is open. -/
theorem isClosed_zeroLocus : IsClosed (Y.zeroLocus f) := by
  rw [← isOpen_compl_iff, Y.compl_zeroLocus f]
  exact isOpen_iUnion fun i ↦ Y.isOpen_setOf_isUnit_germ (f i)

/-- The zero locus, as a closed subspace of `Y`. -/
def zeroLocusSpace : TopCat.{u} :=
  TopCat.of (Y.zeroLocus f)

/-- The inclusion of the zero locus into the ambient space. -/
def zeroLocusι : Y.zeroLocusSpace f ⟶ Y.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
lemma zeroLocusι_apply (z : Y.zeroLocus f) : Y.zeroLocusι f z = z.1 := rfl

/-- The inclusion of the zero locus is a closed embedding: this is the first of the four
conditions in `ComplexAnalytic.IsCutOutBy`. -/
theorem isClosedEmbedding_zeroLocusι : IsClosedEmbedding (Y.zeroLocusι f) :=
  (Y.isClosed_zeroLocus f).isClosedEmbedding_subtypeVal

/-- The range of the inclusion of the zero locus is the set appearing in
`ComplexAnalytic.IsCutOutBy.range_base`.

Together with `isClosedEmbedding_zeroLocusι` this discharges the two topological conditions of
`IsCutOutBy` for any candidate structure sheaf on the zero locus. -/
theorem range_zeroLocusι :
    Set.range (Y.zeroLocusι f) =
      {y | ∀ i, Y.presheaf.Γgerm y (f i) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)} :=
  Subtype.range_val

end Topology

section StructureSheaf

/-- The sheafification of the quotient of `𝒪_Y` by the ideal generated by the `f i`. -/
def quotientSheafify : Y.toTopCat.Presheaf CommRingCat.{u} :=
  sheafify (Opens.grothendieckTopology Y.toTopCat) (Y.presheaf.quotientSpan f)

/-- The inverse image along the inclusion of the zero locus of the sheafified quotient. -/
def zeroLocusPullback : (Y.zeroLocusSpace f).Presheaf CommRingCat.{u} :=
  (TopCat.Presheaf.pullback CommRingCat.{u} (Y.zeroLocusι f)).obj (Y.quotientSheafify f)

/-- The structure presheaf of the zero locus. -/
def zeroLocusPresheaf : (Y.zeroLocusSpace f).Presheaf CommRingCat.{u} :=
  sheafify (Opens.grothendieckTopology (Y.zeroLocusSpace f)) (Y.zeroLocusPullback f)

/-- The structure presheaf of the zero locus is a sheaf: it is a sheafification. -/
lemma isSheaf_zeroLocusPresheaf : (Y.zeroLocusPresheaf f).IsSheaf :=
  ((presheafToSheaf (Opens.grothendieckTopology (Y.zeroLocusSpace f)) CommRingCat.{u}).obj
    (Y.zeroLocusPullback f)).property

/-- The comparison morphism `𝒪_Y ⟶ ι_* 𝒪_Z`. -/
def zeroLocusC : Y.presheaf ⟶ (Y.zeroLocusι f) _* (Y.zeroLocusPresheaf f) :=
  Y.presheaf.toQuotientSpan f ≫
    toSheafify (Opens.grothendieckTopology Y.toTopCat) (Y.presheaf.quotientSpan f) ≫
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} (Y.zeroLocusι f)).unit.app
      (Y.quotientSheafify f) ≫
    (TopCat.Presheaf.pushforward CommRingCat.{u} (Y.zeroLocusι f)).map
      (toSheafify (Opens.grothendieckTopology (Y.zeroLocusSpace f)) (Y.zeroLocusPullback f))

/-- The zero locus as a sheafed space. -/
def zeroLocusSheafedSpace : SheafedSpace CommRingCat.{u} where
  carrier := Y.zeroLocusSpace f
  presheaf := Y.zeroLocusPresheaf f
  IsSheaf := Y.isSheaf_zeroLocusPresheaf f

/-- The inclusion of the zero locus, as a morphism of presheafed spaces. -/
def zeroLocusιHom :
    (Y.zeroLocusSheafedSpace f).toPresheafedSpace ⟶ Y.toPresheafedSpace where
  base := Y.zeroLocusι f
  c := Y.zeroLocusC f

end StructureSheaf

section Stalks

/-- Sheafification does not change stalks: the stalk of the sheafified quotient at `y` is the
stalk of the quotient presheaf. -/
def quotientSheafifyStalkIso (y : Y.toTopCat) :
    (Y.presheaf.quotientSpan f).stalk y ≅ (Y.quotientSheafify f).stalk y :=
  -- `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` is a theorem, not an instance, and
  -- registering it as one does not let typeclass search find it here: `TopCat.Presheaf` is a
  -- `def`, so the `IsIso` goal is only defeq to the theorem's conclusion, not syntactically
  -- equal to it. Passing it to `asIso` explicitly is the way through.
  @asIso _ _ _ _ _
    (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y CommRingCat.{u}
      (Y.presheaf.quotientSpan f))

/-- `quotientSheafifyStalkIso` is the map induced on stalks by `toSheafify`. -/
@[simp]
lemma quotientSheafifyStalkIso_hom (y : Y.toTopCat) :
    (Y.quotientSheafifyStalkIso f y).hom =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y.toTopCat)
          (Y.presheaf.quotientSpan f)) :=
  rfl

/-- Sheafification does not change stalks: the stalk of the structure sheaf of the zero locus at
`z` is the stalk of the inverse image presheaf. -/
def zeroLocusPullbackStalkIso (z : Y.zeroLocusSpace f) :
    (Y.zeroLocusPullback f).stalk z ≅ (Y.zeroLocusPresheaf f).stalk z :=
  @asIso _ _ _ _ _
    (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z CommRingCat.{u}
      (Y.zeroLocusPullback f))

/-- `zeroLocusPullbackStalkIso` is the map induced on stalks by `toSheafify`. -/
@[simp]
lemma zeroLocusPullbackStalkIso_hom (z : Y.zeroLocusSpace f) :
    (Y.zeroLocusPullbackStalkIso f z).hom =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology (Y.zeroLocusSpace f))
          (Y.zeroLocusPullback f)) :=
  rfl

/-- The stalk at `z` of the structure sheaf of the zero locus is the stalk at `z` of the
quotient presheaf: sheafification and inverse image along the inclusion both preserve stalks. -/
def zeroLocusStalkIso (z : Y.zeroLocusSpace f) :
    (Y.presheaf.quotientSpan f).stalk (Y.zeroLocusι f z) ≅ (Y.zeroLocusPresheaf f).stalk z :=
  Y.quotientSheafifyStalkIso f (Y.zeroLocusι f z) ≪≫
    TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} (Y.zeroLocusι f) (Y.quotientSheafify f) z ≪≫
    Y.zeroLocusPullbackStalkIso f z

/-- **The map on stalks induced by the inclusion of the zero locus is the projection onto the
quotient by the germs of the `f i`, followed by an isomorphism.**

This is the whole content of the construction: the two remaining conditions of
`ComplexAnalytic.IsCutOutBy` are read off from it, since an isomorphism changes neither
surjectivity nor the kernel. -/
theorem stalkMap_zeroLocusιHom (z : Y.zeroLocusSpace f) :
    (Y.zeroLocusιHom f).stalkMap z =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (Y.zeroLocusι f z)).map
        (Y.presheaf.toQuotientSpan f) ≫ (Y.zeroLocusStalkIso f z).hom := by
  change (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (Y.zeroLocusι f z)).map (Y.zeroLocusC f) ≫
      (Y.zeroLocusPresheaf f).stalkPushforward CommRingCat.{u} (Y.zeroLocusι f) z = _
  rw [zeroLocusC]
  -- `TopCat.Presheaf` is a `def`, so `rw` refuses to look inside its category instance; `erw`
  -- does. The final `rfl` is `stalkPullbackHom` unfolding to its definition.
  erw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rw [Category.assoc, Category.assoc, Category.assoc]
  erw [TopCat.Presheaf.stalkPushforward_naturality]
  rfl

/-- The map on stalks induced by the inclusion of the zero locus is surjective: this is the
third condition of `ComplexAnalytic.IsCutOutBy`. -/
theorem surjective_stalkMap_zeroLocusιHom (z : Y.zeroLocusSpace f) :
    Function.Surjective ((Y.zeroLocusιHom f).stalkMap z).hom := by
  rw [stalkMap_zeroLocusιHom]
  exact (ConcreteCategory.bijective_of_isIso (Y.zeroLocusStalkIso f z).hom).surjective.comp
    (Y.presheaf.surjective_stalkFunctor_map_toQuotientSpan f (Y.zeroLocusι f z))

/-- The kernel of the map on stalks induced by the inclusion of the zero locus is the ideal
generated by the germs of the `f i`: this is the fourth condition of
`ComplexAnalytic.IsCutOutBy`. -/
theorem ker_stalkMap_zeroLocusιHom (z : Y.zeroLocusSpace f) :
    RingHom.ker ((Y.zeroLocusιHom f).stalkMap z).hom =
      Ideal.span (Set.range fun i ↦ Y.presheaf.Γgerm (Y.zeroLocusι f z) (f i)) := by
  have hinj : Function.Injective ((Y.zeroLocusStalkIso f z).hom).hom :=
    (ConcreteCategory.bijective_of_isIso (Y.zeroLocusStalkIso f z).hom).injective
  rw [← Y.presheaf.ker_stalkFunctor_map_toQuotientSpan f (Y.zeroLocusι f z),
    stalkMap_zeroLocusιHom]
  ext t
  simp only [RingHom.mem_ker]
  refine ⟨fun h ↦ hinj (h.trans (map_zero _).symm), fun h ↦ ?_⟩
  exact (congrArg ((Y.zeroLocusStalkIso f z).hom).hom (RingHom.mem_ker.mp h)).trans
    (map_zero _)

/-- At a point of the zero locus the germs of the `f i` all lie in the maximal ideal, hence so
does the ideal they generate. -/
lemma span_Γgerm_le_maximalIdeal (z : Y.zeroLocusSpace f) :
    Ideal.span (Set.range fun i ↦ Y.presheaf.Γgerm (Y.zeroLocusι f z) (f i)) ≤
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (Y.zeroLocusι f z)) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact z.2 i

/-- At a point of the zero locus the germs of the `f i` generate a proper ideal, which is what
makes the stalk of the structure sheaf of the zero locus a nonzero ring. -/
lemma span_Γgerm_ne_top (z : Y.zeroLocusSpace f) :
    Ideal.span (Set.range fun i ↦ Y.presheaf.Γgerm (Y.zeroLocusι f z) (f i)) ≠ ⊤ := fun h ↦
  (IsLocalRing.maximalIdeal.isMaximal (Y.presheaf.stalk (Y.zeroLocusι f z))).ne_top
    (eq_top_iff.2 (h ▸ Y.span_Γgerm_le_maximalIdeal f z))

/-- The stalk at `z` of the structure sheaf of the zero locus is the stalk of `𝒪_Y` at `z`
modulo the ideal generated by the germs of the `f i`. -/
def zeroLocusStalkQuotientEquiv (z : Y.zeroLocusSpace f) :
    (Y.presheaf.stalk (Y.zeroLocusι f z) ⧸
        Ideal.span (Set.range fun i ↦ Y.presheaf.Γgerm (Y.zeroLocusι f z) (f i))) ≃+*
      (Y.zeroLocusPresheaf f).stalk z :=
  (Ideal.quotEquivOfEq (Y.ker_stalkMap_zeroLocusιHom f z).symm).trans
    (RingHom.quotientKerEquivOfSurjective (Y.surjective_stalkMap_zeroLocusιHom f z))

/-- The stalks of the structure sheaf of the zero locus are nonzero rings. -/
instance nontrivial_zeroLocusPresheaf_stalk (z : Y.zeroLocusSpace f) :
    Nontrivial ((Y.zeroLocusPresheaf f).stalk z) :=
  haveI : Nontrivial (Y.presheaf.stalk (Y.zeroLocusι f z) ⧸
      Ideal.span (Set.range fun i ↦ Y.presheaf.Γgerm (Y.zeroLocusι f z) (f i))) :=
    Ideal.Quotient.nontrivial_iff.mpr (Y.span_Γgerm_ne_top f z)
  (Y.zeroLocusStalkQuotientEquiv f z).injective.nontrivial

/-- The stalks of the structure sheaf of the zero locus are local rings: they are quotients of
the local rings of `Y` by proper ideals. -/
instance isLocalRing_zeroLocusPresheaf_stalk (z : Y.zeroLocusSpace f) :
    IsLocalRing ((Y.zeroLocusPresheaf f).stalk z) :=
  @IsLocalRing.of_surjective' _ _ _ _ _ (Y.nontrivial_zeroLocusPresheaf_stalk f z)
    ((Y.zeroLocusιHom f).stalkMap z).hom (Y.surjective_stalkMap_zeroLocusιHom f z)

/-- The maps on stalks induced by the inclusion of the zero locus are local ring homomorphisms:
a surjection out of a local ring always is. -/
instance isLocalHom_stalkMap_zeroLocusιHom (z : Y.zeroLocusSpace f) :
    IsLocalHom ((Y.zeroLocusιHom f).stalkMap z).hom :=
  @IsLocalHom.of_surjective _ _ _ _ (Y.nontrivial_zeroLocusPresheaf_stalk f z) _
    ((Y.zeroLocusιHom f).stalkMap z).hom (Y.surjective_stalkMap_zeroLocusιHom f z)

end Stalks

section Subspace

/-- The zero locus of a family of global sections, as a locally ringed space: the closed
subspace `Z` of `Y` cut out by the `f i`, with structure sheaf the inverse image of the
sheafified quotient `𝒪_Y ⧸ (f)`. -/
def zeroLocusSubspace : LocallyRingedSpace.{u} where
  toSheafedSpace := Y.zeroLocusSheafedSpace f
  isLocalRing z := Y.isLocalRing_zeroLocusPresheaf_stalk f z

/-- The closed immersion of the zero locus into the ambient locally ringed space. -/
def zeroLocusSubspaceι : Y.zeroLocusSubspace f ⟶ Y :=
  ⟨Y.zeroLocusιHom f, fun z ↦ Y.isLocalHom_stalkMap_zeroLocusιHom f z⟩

/-- The underlying continuous map of the closed immersion of the zero locus is the inclusion. -/
@[simp]
lemma zeroLocusSubspaceι_base : (Y.zeroLocusSubspaceι f).base = Y.zeroLocusι f := rfl

/-- **The zero locus of finitely many global sections is cut out by them**: the inclusion of
the zero locus, with the quotient structure sheaf, satisfies all four conditions of
`ComplexAnalytic.IsCutOutBy`. -/
theorem isCutOutBy_zeroLocusSubspaceι {k : ℕ} (g : Fin k → Y.presheaf.obj (op ⊤)) :
    ComplexAnalytic.IsCutOutBy (Y.zeroLocusSubspaceι g) g where
  isClosedEmbedding := Y.isClosedEmbedding_zeroLocusι g
  range_base := Y.range_zeroLocusι g
  surjective_stalkMap z := Y.surjective_stalkMap_zeroLocusιHom g z
  ker_stalkMap z := Y.ker_stalkMap_zeroLocusιHom g z

end Subspace

end AlgebraicGeometry.LocallyRingedSpace

end

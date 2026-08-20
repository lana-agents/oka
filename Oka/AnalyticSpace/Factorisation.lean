/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Basic
import Oka.Geometry.RingedSpace.CutOut
import Oka.Topology.Sheaves.Functors
import Oka.Topology.Sheaves.Presheaf

/-!
# The mapping property of a subspace cut out by global sections

`ComplexAnalytic.IsCutOutBy i f` says that the closed immersion `i : X ⟶ Y` exhibits `X` as the
subspace of `Y` cut out by the global sections `f₁, …, f_k`. This file proves that it deserves
the name: **a morphism `φ : Z ⟶ Y` with `φ.c.app ⊤ (f j) = 0` for every `j` factors, uniquely,
through `i`**.

```
ComplexAnalytic.IsCutOutBy.existsUnique_lift :
    ∃! ψ : Z ⟶ X, ψ ≫ i = φ
```

Uniqueness was already available (`ComplexAnalytic.IsCutOutBy.hom_ext`, from
`IsCutOutBy.mono`); what is new here is existence. Together with
`ComplexAnalytic.IsCutOutBy.uniqueIso` below this makes good on the claim in the docstring of
`ComplexAnalytic.IsCutOutBy`, that any two closed immersions cutting out the same sections are
canonically isomorphic — until now that claim was unproved.

## How the map on structure sheaves is produced

The stalkwise conditions of `IsCutOutBy` give a *family* of maps on stalks, and a family of
stalk maps is not a morphism of sheaves. The construction goes the other way round, through two
results that are each about `i_*` rather than about stalks:

1. `ComplexAnalytic.IsCutOutBy.pushforwardIso` (`Oka/Geometry/RingedSpace/CutOut.lean`):
   `i_* 𝒪_X ≅ 𝒪_Y ⧸ (f)`.
2. `TopCat.Presheaf.pushforwardFullyFaithful` (`Oka/Topology/Sheaves/Functors.lean`): pushing
   forward along an embedding is fully faithful, so a morphism out of `i_* 𝒪_X` comes from a
   unique morphism out of `𝒪_X`.

Given those, `φ.c` kills the `f j`, hence factors through the quotient presheaf
(`TopCat.Presheaf.quotientSpanDesc`) and then through its sheafification, giving
`𝒪_Y ⧸ (f) ⟶ φ_* 𝒪_Z`. Composing with (1) and transporting along
`baseLift ≫ i.base = φ.base` gives `i_* 𝒪_X ⟶ i_*(ψ_* 𝒪_Z)`, and (2) descends it to
`𝒪_X ⟶ ψ_* 𝒪_Z`. That the composite is `φ` again is then formal: it unwinds to the two
factorisation identities of the quotient, and the transport cancels by
`TopCat.Presheaf.comp_pushforwardEq_inv_comp_whiskerRight`.

The remaining condition — that the result is a morphism of *locally* ringed spaces — is where
the stalk conditions are used, and only there: `φ` is local on stalks, `i` is *surjective* on
stalks, and a map whose precomposition with a surjection is local is itself local.

## Main definitions

- `ComplexAnalytic.IsCutOutBy.lift`: the factorisation `ψ : Z ⟶ X`.
- `ComplexAnalytic.IsCutOutBy.uniqueIso`: the canonical isomorphism between two subspaces cut
  out by the same sections.

## Main results

- `ComplexAnalytic.IsCutOutBy.lift_comp`: `ψ ≫ i = φ`.
- `ComplexAnalytic.IsCutOutBy.existsUnique_lift`: the factorisation exists and is unique.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry Topology
open scoped AlgebraicGeometry
open AlgebraicGeometry.LocallyRingedSpace

universe u

noncomputable section

namespace ComplexAnalytic.IsCutOutBy

variable {X Y Z : LocallyRingedSpace.{u}} {i : X ⟶ Y} {k : ℕ}
  {f : Fin k → Y.presheaf.obj (op ⊤)} (hcut : IsCutOutBy i f) (φ : Z ⟶ Y)
  (hφ : ∀ j, φ.c.app (op ⊤) (f j) = 0)

section Quotient
-- moved here from `Oka/AnalyticSpace/LocalModel.lean`, which does not use it: it belongs with
-- the factorisation it feeds, and moving it lets that file drop the `CutOut` import.

include hcut in
/-- The image of a closed immersion cutting out the `f j` is their zero locus, in the spelling
`Oka/Geometry/RingedSpace/ZeroLocus.lean` uses. `ComplexAnalytic.IsCutOutBy.range_base` states
the same set by hand, because `IsCutOutBy` is stated without reference to the mirror tree. -/
theorem range_base_eq_zeroLocus :
    Set.range i.base = Y.zeroLocus f :=
  hcut.range_base.trans (Set.ext fun _ ↦ (Y.mem_zeroLocus_iff f).symm)

include hcut in
/-- **The structure sheaf of a subspace cut out by global sections is the quotient sheaf**:
`i_* 𝒪_X ≅ 𝒪_Y ⧸ (f₁, …, f_k)`.

This is the converse of `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`,
and it is what makes `IsCutOutBy` a characterisation rather than a list of properties: a closed
immersion satisfying the four conditions has the same structure sheaf, after pushing forward,
as the one `Oka/Geometry/RingedSpace/ZeroLocus.lean` builds.

On its own it gives neither the mapping property nor uniqueness of `X` up to isomorphism:
descending an isomorphism of the pushforwards to one upstairs needs `i_*` to be fully faithful.
That is `TopCat.Presheaf.pushforwardFullyFaithful`, and the two consequences are
`ComplexAnalytic.IsCutOutBy.existsUnique_lift` and `ComplexAnalytic.IsCutOutBy.uniqueIso`
below. -/
def pushforwardIso :
    Y.quotientSheafify f ≅ i.base _* X.presheaf :=
  LocallyRingedSpace.quotientSheafifyIsoPushforward i f hcut.c_app_eq_zero
    hcut.isClosedEmbedding.isInducing hcut.surjective_stalkMap hcut.ker_stalkMap
    hcut.isClosedEmbedding.isClosed_range hcut.range_base_eq_zeroLocus

/-- The underlying morphism of `ComplexAnalytic.IsCutOutBy.pushforwardIso` is the comparison
morphism, so the isomorphism really is induced by `i.c`. -/
@[simp]
lemma pushforwardIso_hom :
    hcut.pushforwardIso.hom =
      LocallyRingedSpace.quotientSheafifyToPushforward i f hcut.c_app_eq_zero :=
  rfl

end Quotient

section Construction

/-- The underlying continuous map of the factorisation, as a morphism of `TopCat`. -/
def baseLiftHom : Z.toTopCat ⟶ X.toTopCat := TopCat.ofHom (hcut.baseLift φ hφ)

lemma baseLiftHom_comp : hcut.baseLiftHom φ hφ ≫ i.base = φ.base := by
  ext z
  exact hcut.base_baseLift φ hφ z

/-- **The map on structure sheaves of the factorisation.**

`φ.c` factors through `𝒪_Y ⧸ (f)`; composing with `i_* 𝒪_X ≅ 𝒪_Y ⧸ (f)` and transporting along
`baseLift ≫ i.base = φ.base` gives a morphism `i_* 𝒪_X ⟶ i_* (ψ_* 𝒪_Z)`, which descends
because `i_*` is fully faithful. -/
def cLift : X.presheaf ⟶ (hcut.baseLiftHom φ hφ) _* Z.presheaf :=
  (TopCat.Presheaf.pushforwardFullyFaithful i.base
      hcut.isClosedEmbedding.isInducing).preimage
    ((hcut.pushforwardIso.inv ≫ quotientSheafifyToPushforward φ f hφ) ≫
      (TopCat.Presheaf.pushforwardEq (hcut.baseLiftHom_comp φ hφ) Z.presheaf).inv)

lemma pushforward_map_cLift :
    (TopCat.Presheaf.pushforward CommRingCat.{u} i.base).map (hcut.cLift φ hφ) =
      (hcut.pushforwardIso.inv ≫ quotientSheafifyToPushforward φ f hφ) ≫
        (TopCat.Presheaf.pushforwardEq (hcut.baseLiftHom_comp φ hφ) Z.presheaf).inv :=
  (TopCat.Presheaf.pushforwardFullyFaithful i.base
    hcut.isClosedEmbedding.isInducing).map_preimage _

/-- The comparison morphism of `Oka/Geometry/RingedSpace/CutOut.lean`, read backwards: `i.c`
followed by the inverse of `i_* 𝒪_X ≅ 𝒪_Y ⧸ (f)` is the projection onto the quotient. -/
lemma c_comp_pushforwardIso_inv :
    i.c ≫ hcut.pushforwardIso.inv =
      Y.presheaf.toQuotientSpan f ≫
        CategoryTheory.toSheafify (D := CommRingCat.{u})
          (Opens.grothendieckTopology Y.toTopCat) (Y.presheaf.quotientSpan f) := by
  refine (Iso.comp_inv_eq _).2 ?_
  refine (toQuotientSpan_comp_quotientSpanToPushforward i f hcut.c_app_eq_zero).symm.trans ?_
  refine (congrArg (fun z ↦ Y.presheaf.toQuotientSpan f ≫ z)
    (toSheafify_comp_quotientSheafifyToPushforward i f hcut.c_app_eq_zero).symm).trans ?_
  exact (Category.assoc _ _ _).symm

/-- The factorisation, as a morphism of presheafed spaces. -/
def liftPre : Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := hcut.baseLiftHom φ hφ
  c := hcut.cLift φ hφ

/-- **The factorisation composes to `φ`, at the level of presheafed spaces.** -/
lemma liftPre_comp : hcut.liftPre φ hφ ≫ i.toHom = φ.toHom := by
  refine PresheafedSpace.ext _ _ (hcut.baseLiftHom_comp φ hφ) ?_
  rw [show (hcut.liftPre φ hφ ≫ i.toHom).c =
      i.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} i.base).map (hcut.cLift φ hφ) from rfl,
    hcut.pushforward_map_cLift φ hφ]
  refine Eq.trans (TopCat.Presheaf.comp_pushforwardEq_inv_comp_whiskerRight
    (hcut.baseLiftHom_comp φ hφ) Z.presheaf i.c
    (hcut.pushforwardIso.inv ≫ quotientSheafifyToPushforward φ f hφ) _) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫ quotientSheafifyToPushforward φ f hφ)
        hcut.c_comp_pushforwardIso_inv).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ Y.presheaf.toQuotientSpan f ≫ z)
            (toSheafify_comp_quotientSheafifyToPushforward φ f hφ)).trans
          (toQuotientSpan_comp_quotientSpanToPushforward φ f hφ))))

/-- **The factorisation is a morphism of *locally* ringed spaces.**

This is the only place the stalk conditions of `IsCutOutBy` are used. A germ on `X` is the image
of a germ on `Y` (`IsCutOutBy.surjective_stalkMap`), and going round the square is `φ`, whose
stalk maps are local. -/
lemma isLocalHom_stalkMap_liftPre (z : Z) :
    IsLocalHom ((hcut.liftPre φ hφ).stalkMap z).hom := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hcut.surjective_stalkMap ((hcut.liftPre φ hφ).base z) a
  haveI key : IsLocalHom ((hcut.liftPre φ hφ ≫ i.toHom).stalkMap z).hom := by
    rw [hcut.liftPre_comp φ hφ]
    exact φ.prop z
  refine (key.map_nonunit y ?_).map _
  rw [PresheafedSpace.stalkMap.comp]
  exact ha

/-- **The factorisation of `φ` through the subspace cut out by the sections it kills.** -/
def lift : Z ⟶ X :=
  ⟨hcut.liftPre φ hφ, hcut.isLocalHom_stalkMap_liftPre φ hφ⟩

@[simp]
lemma base_lift (z : Z) : (hcut.lift φ hφ).base z = hcut.baseLift φ hφ z := rfl

@[simp]
lemma lift_comp : hcut.lift φ hφ ≫ i = φ :=
  LocallyRingedSpace.Hom.ext' (hcut.liftPre_comp φ hφ)

include hcut hφ in
/-- **The mapping property of a subspace cut out by global sections.**

A morphism into `Y` which kills the `f j` factors through `i`, uniquely. Existence is
`ComplexAnalytic.IsCutOutBy.lift`; uniqueness is `ComplexAnalytic.IsCutOutBy.hom_ext`, i.e. the
fact that `i` is a monomorphism. -/
theorem existsUnique_lift : ∃! ψ : Z ⟶ X, ψ ≫ i = φ :=
  ⟨hcut.lift φ hφ, hcut.lift_comp φ hφ,
    fun ψ hψ ↦ hcut.hom_ext ψ _ (hψ.trans (hcut.lift_comp φ hφ).symm)⟩

end Construction

section Unique

variable {X' : LocallyRingedSpace.{u}} {i' : X' ⟶ Y}

/-- **Any two closed immersions cutting out the same global sections are canonically
isomorphic.**

This is what the docstring of `ComplexAnalytic.IsCutOutBy` asserts, and it is a corollary of the
mapping property applied in both directions: each immersion kills the `f j`
(`IsCutOutBy.c_app_eq_zero`), so each factors through the other, and the two composites are the
identity by uniqueness. -/
def uniqueIso (hcut : IsCutOutBy i f) (hcut' : IsCutOutBy i' f) : X ≅ X' where
  hom := hcut'.lift i hcut.c_app_eq_zero
  inv := hcut.lift i' hcut'.c_app_eq_zero
  hom_inv_id := hcut.hom_ext _ _ (by
    rw [Category.assoc, hcut.lift_comp, hcut'.lift_comp, Category.id_comp])
  inv_hom_id := hcut'.hom_ext _ _ (by
    rw [Category.assoc, hcut'.lift_comp, hcut.lift_comp, Category.id_comp])

@[simp]
lemma uniqueIso_hom_comp (hcut : IsCutOutBy i f) (hcut' : IsCutOutBy i' f) :
    (hcut.uniqueIso hcut').hom ≫ i' = i :=
  hcut'.lift_comp i hcut.c_app_eq_zero

@[simp]
lemma uniqueIso_inv_comp (hcut : IsCutOutBy i f) (hcut' : IsCutOutBy i' f) :
    (hcut.uniqueIso hcut').inv ≫ i = i' :=
  hcut.lift_comp i' hcut'.c_app_eq_zero

end Unique

end ComplexAnalytic.IsCutOutBy

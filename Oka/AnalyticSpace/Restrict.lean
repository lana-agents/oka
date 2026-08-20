/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Basic
import Oka.Topology.Sheaves.Stalks

/-!
# Being cut out by global sections is local on the target

`ComplexAnalytic.IsCutOutBy i f` says that the closed immersion `i : A ⟶ B` exhibits `A` as the
analytic subspace of `B` cut out by the global sections `f`. This file proves that the property
survives shrinking the target to an open subset:

```
ComplexAnalytic.IsCutOutBy.restrictOpen :
  IsCutOutBy i f → ∀ V : Opens B, IsCutOutBy (restrictHom i V) (restrictSections V f)
```

where `restrictHom i V` restricts `i` to the preimage of `V` and `restrictSections V f` restricts
the family. Together with `ComplexAnalytic.isCLinearHom_restrictHom` this is what says a *chart*
of a complex analytic space may be shrunk, which is what an open subspace of an analytic space
needs in order to be one itself.

## Why the target rather than the source

One wants to shrink the *source* — to pass from a chart on `U₀` to a chart on `U₀ ⊓ U`. Stating
it that way would require manufacturing the open subset of the target, and the natural candidate
is `B ∖ i '' (A ∖ A')`, which is open because `i` is a **closed** embedding and whose preimage is
exactly `A'` because `i` is **injective**. That works, but it is not needed: `i` is an embedding,
so every open subset of `A` already *is* the preimage of an open subset of `B`, and taking the
target open as given makes the closedness of the image free — `i '' A` is closed in `B`, hence
`i '' A ∩ V` is closed in `V`.

## How the four conditions restrict

`ComplexAnalytic.restrictHom` is built with `LocallyRingedSpace.IsOpenImmersion.lift`, so it
comes with `ComplexAnalytic.restrictHom_fac` and nothing else; every fact about it is derived
from that one equation.

* the closed embedding is `IsEmbedding.of_comp` against the inclusion of `V`, with the range
  computed by `ComplexAnalytic.mem_range_base_restrictHom_iff`;
* `range_base` is the only condition that is not stalk-local, and it reduces to the original one
  because the germ of a restricted section is the image of the original germ under the stalk map
  of `LocallyRingedSpace.ofRestrict` (`ComplexAnalytic.Γgerm_restrictSections`), which is an
  isomorphism and therefore reflects the maximal ideal;
* the two stalk conditions come from
  `ComplexAnalytic.stalkMap_restrictHom_eq`, which factors the stalk map of `restrictHom i V`
  as an isomorphism, then `i.stalkMap`, then an isomorphism. Applying `stalkMap` to
  `restrictHom_fac` produces a `TopCat.Presheaf.stalkSpecializes` transport between the stalks at
  two points which are equal but not definitionally so, and
  `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom` together with
  `TopCat.Presheaf.stalkCongr_hom_germ` is what makes that transport tractable.

## What this does *not* give

**It does not give `ComplexAnalytic.AnalyticSpace.restrict`: an open subspace of a complex
analytic space is still not known to be a complex analytic space.** What is missing is one more
lemma of the same shape, and it is worth naming precisely because it was not visible before this
file existed.

`AnalyticSpace.local_model` demands a chart whose target is `ℂ^n` restricted to an open subset
**of `ℂ^n`**. What `restrictOpen` produces is a chart whose target is `(ℂ^n|V)|V'`, a restriction
of a restriction. Those two are isomorphic — the `isoRestrict` of
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`, applied to the composite of the two
inclusions, gives the isomorphism with no bespoke `restrictRestrict` needed — but transporting
`IsCutOutBy` along it needs the isomorphism on the **target**, and only the source version
exists:

```
ComplexAnalytic.IsCutOutBy.comp_iso : IsCutOutBy i f → (e : X' ≅ X) → IsCutOutBy (e.hom ≫ i) f
```

The missing companion is

```
IsCutOutBy.iso_comp : IsCutOutBy i f → (e : B ≅ C) →
  IsCutOutBy (i ≫ e.hom) (fun j ↦ (LocallyRingedSpace.Γ.map e.inv.op).hom (f j))
```

whose two stalk conditions are compositions with isomorphisms, and whose `range_base` needs the
same germ transport as `Γgerm_restrictSections` above, through `e.hom.stalkMap` instead of
through `ofRestrict`. Nothing about it looks hard; it is simply not here.

## Main definitions

- `ComplexAnalytic.restrictHom`: the restriction of a morphism to the preimage of an open subset
  of the target.
- `ComplexAnalytic.restrictSections`: the restriction of a family of global sections.
- `ComplexAnalytic.restrictStalkEquiv`: the isomorphism through which the stalk map of
  `restrictHom` factors.

## Main results

- `ComplexAnalytic.IsCutOutBy.restrictOpen`: **being cut out by global sections is local on the
  target.**
- `ComplexAnalytic.isCLinearHom_restrictHom`: the restriction of a `ℂ`-linear morphism is
  `ℂ`-linear.
- `ComplexAnalytic.stalkMap_restrictHom_eq`: the stalk map of the restriction, factored.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {A B : LocallyRingedSpace.{u}}

lemma range_ofRestrict (V : Opens B) :
    Set.range (B.ofRestrict V.isOpenEmbedding).base = (V : Set B) := by
  ext y; constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩; exact hy
  · exact fun hy ↦ ⟨⟨y, hy⟩, rfl⟩

lemma range_comp_le (i : A ⟶ B) (V : Opens B) :
    Set.range ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding ≫ i).base) ⊆
      Set.range (B.ofRestrict V.isOpenEmbedding).base := by
  rw [range_ofRestrict]
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  exact hx

/-- The restriction of `i` to the preimage of an open subset of the target. -/
def restrictHom (i : A ⟶ B) (V : Opens B) :
    A.restrict ((Opens.map i.base).obj V).isOpenEmbedding ⟶ B.restrict V.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift (B.ofRestrict V.isOpenEmbedding)
    (A.ofRestrict _ ≫ i) (range_comp_le i V)

lemma restrictHom_fac (i : A ⟶ B) (V : Opens B) :
    restrictHom i V ≫ B.ofRestrict V.isOpenEmbedding =
      A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding ≫ i :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

lemma base_restrictHom (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (B.ofRestrict V.isOpenEmbedding).base ((restrictHom i V).base x) =
      i.base ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x) :=
  ConcreteCategory.congr_hom
    (congrArg (fun m : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding ⟶ B ↦ m.base)
      (restrictHom_fac i V)) x

lemma stalkMap_restrictHom (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x) ≫
        (restrictHom i V).stalkMap x =
      (B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom ≫
        i.stalkMap ((A.ofRestrict _).base x) ≫ (A.ofRestrict _).stalkMap x := by
  rw [← LocallyRingedSpace.stalkMap_comp, ← LocallyRingedSpace.stalkMap_comp]
  exact LocallyRingedSpace.stalkMap_congr_hom _ _ (restrictHom_fac i V) x

variable {k : ℕ}

/-- The family `f` of global sections of `𝒪_B`, restricted to an open subset. -/
def restrictSections (V : Opens B) (f : Fin k → B.presheaf.obj (op ⊤)) :
    Fin k → (B.restrict V.isOpenEmbedding).presheaf.obj (op ⊤) :=
  fun j ↦ (LocallyRingedSpace.Γ.map (B.ofRestrict V.isOpenEmbedding).op).hom (f j)

lemma Γgerm_restrictSections (V : Opens B) (f : Fin k → B.presheaf.obj (op ⊤))
    (y : B.restrict V.isOpenEmbedding) (j : Fin k) :
    (B.restrict V.isOpenEmbedding).presheaf.Γgerm y (restrictSections V f j) =
      ((B.ofRestrict V.isOpenEmbedding).stalkMap y).hom
        (B.presheaf.Γgerm ((B.ofRestrict V.isOpenEmbedding).base y) (f j)) :=
  (LocallyRingedSpace.stalkMap_germ_apply (B.ofRestrict V.isOpenEmbedding) ⊤ y trivial (f j)).symm

/-- The stalk map of an open immersion reflects and preserves the maximal ideal. -/
lemma mem_maximalIdeal_stalkMap_iff {X Y : LocallyRingedSpace.{u}} (g : X ⟶ Y) (x : X)
    [IsIso (g.stalkMap x)] (a : Y.presheaf.stalk (g.base x)) :
    (g.stalkMap x).hom a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x)) := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff]
  exact not_congr (isUnit_map_iff (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv a)

lemma mem_range_base_restrictHom_iff (i : A ⟶ B) (V : Opens B)
    (y : B.restrict V.isOpenEmbedding) :
    y ∈ Set.range (restrictHom i V).base ↔
      (B.ofRestrict V.isOpenEmbedding).base y ∈ Set.range i.base := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(A.ofRestrict _).base x, (base_restrictHom i V x).symm⟩
  · rintro ⟨a, ha⟩
    have haV : a ∈ (Opens.map i.base).obj V := by
      change i.base a ∈ V
      rw [ha]
      exact y.2
    refine ⟨⟨a, haV⟩, ?_⟩
    apply Subtype.ext
    exact (base_restrictHom i V ⟨a, haV⟩).trans ha

theorem isClosedEmbedding_base_restrictHom {i : A ⟶ B} (hce : IsClosedEmbedding i.base)
    (V : Opens B) : IsClosedEmbedding (restrictHom i V).base := by
  have hcomp : ⇑(B.ofRestrict V.isOpenEmbedding).base ∘ ⇑(restrictHom i V).base =
      ⇑i.base ∘ ⇑(A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base :=
    funext (base_restrictHom i V)
  have hemb : IsEmbedding (⇑(B.ofRestrict V.isOpenEmbedding).base ∘ ⇑(restrictHom i V).base) := by
    rw [hcomp]
    exact hce.isEmbedding.comp ((Opens.map i.base).obj V).isOpenEmbedding.isEmbedding
  have hset : Set.range (restrictHom i V).base =
      ⇑(B.ofRestrict V.isOpenEmbedding).base ⁻¹' Set.range i.base :=
    Set.ext fun y ↦ mem_range_base_restrictHom_iff i V y
  refine ⟨IsEmbedding.of_comp (restrictHom i V).base.hom.continuous
    (B.ofRestrict V.isOpenEmbedding).base.hom.continuous hemb, ?_⟩
  rw [hset]
  exact hce.isClosed_range.preimage (B.ofRestrict V.isOpenEmbedding).base.hom.continuous

theorem range_base_restrictHom {i : A ⟶ B} {f : Fin k → B.presheaf.obj (op ⊤)}
    (hcut : IsCutOutBy i f) (V : Opens B) :
    Set.range (restrictHom i V).base =
      {y | ∀ j, (B.restrict V.isOpenEmbedding).presheaf.Γgerm y (restrictSections V f j) ∈
        IsLocalRing.maximalIdeal ((B.restrict V.isOpenEmbedding).presheaf.stalk y)} := by
  refine Set.ext fun y ↦ (mem_range_base_restrictHom_iff i V y).trans
    ((Set.ext_iff.1 hcut.range_base _).trans (forall_congr' fun j ↦ ?_))
  rw [Γgerm_restrictSections]
  exact (mem_maximalIdeal_stalkMap_iff (B.ofRestrict V.isOpenEmbedding) y _).symm

lemma stalkMap_restrictHom_eq (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (restrictHom i V).stalkMap x =
      inv ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x)) ≫
        (B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom ≫
          i.stalkMap ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x) ≫
            (A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x := by
  rw [← stalkMap_restrictHom, IsIso.inv_hom_id_assoc]

theorem surjective_stalkMap_restrictHom {i : A ⟶ B} {f : Fin k → B.presheaf.obj (op ⊤)}
    (hcut : IsCutOutBy i f) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    Function.Surjective ((restrictHom i V).stalkMap x).hom := by
  rw [stalkMap_restrictHom_eq]
  intro c
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x)).surjective c
  obtain ⟨a, rfl⟩ := hcut.surjective_stalkMap _ b
  obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom).surjective a
  obtain ⟨e, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (inv ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x)))).surjective d
  exact ⟨e, rfl⟩

lemma inv_hom_apply {R S : CommRingCat.{u}} (e : R ⟶ S) [IsIso e] (v : R) :
    (inv e).hom (e.hom v) = v := by
  rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]

/-- The composite isomorphism from the stalk of `B|V` at `(restrictHom i V) x` to the stalk of
`B` at `i x`, through which the stalk map of the restriction factors. -/
def restrictStalkEquiv (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (B.restrict V.isOpenEmbedding).presheaf.stalk ((restrictHom i V).base x) ≅
      B.presheaf.stalk (i.base ((A.ofRestrict _).base x)) :=
  asIso (inv ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x)) ≫
    (B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom)

lemma restrictStalkEquiv_Γgerm (i : A ⟶ B) (V : Opens B) (f : Fin k → B.presheaf.obj (op ⊤))
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) (j : Fin k) :
    (restrictStalkEquiv i V x).hom.hom
        ((B.restrict V.isOpenEmbedding).presheaf.Γgerm ((restrictHom i V).base x)
          (restrictSections V f j)) =
      B.presheaf.Γgerm (i.base ((A.ofRestrict _).base x)) (f j) := by
  rw [Γgerm_restrictSections]
  change ((B.presheaf.stalkCongr (Inseparable.of_eq (base_restrictHom i V x))).hom).hom
      ((inv ((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x))).hom
        (((B.ofRestrict V.isOpenEmbedding).stalkMap ((restrictHom i V).base x)).hom _)) = _
  rw [inv_hom_apply]
  exact TopCat.Presheaf.stalkCongr_hom_germ B.presheaf _ ⊤ trivial trivial (f j)

lemma stalkMap_restrictHom_eq' (i : A ⟶ B) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    (restrictHom i V).stalkMap x =
      (restrictStalkEquiv i V x).hom ≫
        i.stalkMap ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x) ≫
          (A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x := by
  rw [stalkMap_restrictHom_eq, restrictStalkEquiv, asIso_hom, Category.assoc]

theorem ker_stalkMap_restrictHom {i : A ⟶ B} {f : Fin k → B.presheaf.obj (op ⊤)}
    (hcut : IsCutOutBy i f) (V : Opens B)
    (x : A.restrict ((Opens.map i.base).obj V).isOpenEmbedding) :
    RingHom.ker ((restrictHom i V).stalkMap x).hom =
      Ideal.span (Set.range fun j ↦ (B.restrict V.isOpenEmbedding).presheaf.Γgerm
        ((restrictHom i V).base x) (restrictSections V f j)) := by
  have hθinj : Function.Injective
      ⇑((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x).hom :=
    (ConcreteCategory.bijective_of_isIso _).injective
  have hval : ∀ v, ((restrictHom i V).stalkMap x).hom v =
      ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).stalkMap x).hom
        ((i.stalkMap _).hom ((restrictStalkEquiv i V x).hom.hom v)) := fun v ↦ by
    rw [stalkMap_restrictHom_eq']
    rfl
  set eq := (restrictStalkEquiv i V x).commRingCatIsoToRingEquiv with heq
  have hstep : RingHom.ker ((restrictHom i V).stalkMap x).hom =
      Ideal.comap eq (RingHom.ker (i.stalkMap
        ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x)).hom) := by
    ext v
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, hval]
    constructor
    · intro hf
      exact hθinj (hf.trans (map_zero _).symm)
    · intro hf
      have hf' : (i.stalkMap ((A.ofRestrict ((Opens.map i.base).obj V).isOpenEmbedding).base x)).hom
          ((restrictStalkEquiv i V x).hom.hom v) = 0 := hf
      rw [hf', map_zero]
  rw [hstep, hcut.ker_stalkMap, ← Ideal.map_symm eq, Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  refine congrArg Set.range (funext fun j ↦ ?_)
  exact (eq.symm_apply_eq).2 (restrictStalkEquiv_Γgerm i V f x j).symm

/-- **Being cut out by global sections is local on the target**: restricting a closed immersion
to the preimage of an open subset of the target still cuts it out, by the restricted family. -/
theorem IsCutOutBy.restrictOpen {i : A ⟶ B} {f : Fin k → B.presheaf.obj (op ⊤)}
    (hcut : IsCutOutBy i f) (V : Opens B) :
    IsCutOutBy (restrictHom i V) (restrictSections V f) where
  isClosedEmbedding := isClosedEmbedding_base_restrictHom hcut.isClosedEmbedding V
  range_base := range_base_restrictHom hcut V
  surjective_stalkMap := surjective_stalkMap_restrictHom hcut V
  ker_stalkMap := ker_stalkMap_restrictHom hcut V

/-- Restricting a `ℂ`-linear morphism to the preimage of an open subset of the target is
`ℂ`-linear for the restricted algebra structures. -/
theorem isCLinearHom_restrictHom {i : A ⟶ B} {α : ℂ →+* A.presheaf.obj (op ⊤)}
    {β : ℂ →+* B.presheaf.obj (op ⊤)} (h : IsCLinearHom i α β) (V : Opens B) :
    IsCLinearHom (restrictHom i V) (A.resAlgMap α ((Opens.map i.base).obj V)) (B.resAlgMap β V) :=
  fun c ↦ by
    have key := LocallyRingedSpace.Γ_map_comp_apply (restrictHom i V)
      (B.ofRestrict V.isOpenEmbedding) (β c)
    rw [restrictHom_fac, LocallyRingedSpace.Γ_map_comp_apply, h c] at key
    exact key.symm

end ComplexAnalytic

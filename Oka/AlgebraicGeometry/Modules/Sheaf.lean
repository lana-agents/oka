/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Oka.RingTheory.Finiteness.Basic

/-!
# Restricting a module along an open immersion: generators and finiteness of sections

Material for `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`; see `README.md` on the mirror tree.
That file does not currently import `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`, which
the declarations here need, so upstreaming them adds that import — three files to its closure.

Two facts about `AlgebraicGeometry.Scheme.Modules.restrict`, both of them bookkeeping in the
sense that neither uses anything about the sheaves beyond what Mathlib already proves, and both
of them prerequisites for reading a statement about an open subscheme as a statement about the
ambient scheme.

* **`AlgebraicGeometry.Scheme.Modules.generatingSectionsRestrict`** turns generating sections of
  `M.over U` — which live over the *slice site* `Over U` of `X.Opens` — into generating sections
  of `M.restrict U.ι`, which live over the open subscheme `U`'s own site. The index type is
  unchanged, so "finitely many generators" survives.
* **`AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_restrict`** says that finiteness
  of `Γ(M.restrict f, U)` over `Γ(V, U)` is finiteness of `Γ(M, f ''ᵁ U)` over `Γ(W, f ''ᵁ U)`.

## The site comparison is Mathlib's, not this file's

`SheafOfModules.IsFiniteType` and `SheafOfModules.IsQuasicoherent` are stated with `M.over X` for
objects `X` of the site, so every generating family this development can obtain over a
distinguished open arrives on the slice site. Reading it on the open subscheme needs an
equivalence of the two sites, and **that equivalence is already in Mathlib**:
`AlgebraicGeometry.Scheme.Modules.overEquiv` and
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. All this file adds is the unit comparison
`overEquiv` needs before `SheafOfModules.GeneratingSections.map` will accept it, and that
comparison is assembled from `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` and
`overFunctorEquiv` — `(SheafOfModules.unit X.ringCatSheaf).over U` and
`SheafOfModules.unit (X.ringCatSheaf.over U)` are the same object, by `rfl`.

## The two actions on one carrier

`AlgebraicGeometry.Scheme.Modules.restrict_obj` says `Γ(M.restrict f, U)` and `Γ(M, f ''ᵁ U)` are
the same type — Mathlib proves it by `rfl` and asks that it not be used, preferring the
isomorphism `restrictAppIso`, which is `Iso.refl`. What genuinely differs is the ring acting:
`Γ(V, U)` on the left and `Γ(W, f ''ᵁ U)` on the right, matched by the isomorphism
`AlgebraicGeometry.Scheme.Hom.appIso` rather than by any map of carriers.
`Module.Finite.of_ringEquiv` is exactly that situation, which is why it is stated in the mirror of
`Mathlib/RingTheory/Finiteness/Basic.lean` rather than here.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.overEquivUnitIso`
- `AlgebraicGeometry.Scheme.Modules.generatingSectionsRestrict`

## Main results

- `AlgebraicGeometry.Scheme.Modules.module_finite_sections_of_restrict`
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- **The unit comparison for `AlgebraicGeometry.Scheme.Modules.overEquiv`**: the structure sheaf
of the open subscheme `U`, read as a module over itself, is the image under `overEquiv U` of the
structure sheaf of `X` read over the slice site.

This is what `SheafOfModules.GeneratingSections.map` asks for on top of preservation of colimits,
and it is `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` composed with
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`; the `overFunctor` half needs no comparison at
all, since `(SheafOfModules.unit X.ringCatSheaf).over U` **is** `SheafOfModules.unit
(X.ringCatSheaf.over U)` — the two are the same term, and this file relies on that. -/
def overEquivUnitIso {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ≅
      (overEquiv.{u} U).functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (restrictUnitIso.{u} U.ι).symm ≪≫
    ((overFunctorEquiv.{u} U).app (SheafOfModules.unit X.ringCatSheaf)).symm

/-- **Generating sections over the slice site become generating sections of the restriction.**

`SheafOfModules.IsFiniteType` and `SheafOfModules.IsQuasicoherent` produce generating families of
`M.over U`; a statement about the open subscheme `U` needs them for `M.restrict U.ι`. The functor
that moves them is `AlgebraicGeometry.Scheme.Modules.overEquiv`, an equivalence and so
colimit-preserving, and `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` identifies its
composite with `overFunctor` as `restrictFunctor U.ι`.

The index type is not touched: `(generatingSectionsRestrict M U σ).I` is `σ.I` by `rfl`, which is
what the instance below records. -/
def generatingSectionsRestrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (σ : (M.over U).GeneratingSections) : (M.restrict U.ι).GeneratingSections :=
  SheafOfModules.GeneratingSections.equivOfIso ((overFunctorEquiv.{u} U).app M)
    (σ.map (overEquiv.{u} U).functor (overEquivUnitIso U))

/-- **Restricting does not change the index type of a generating family**, so finitely many
generators over the slice site are finitely many generators of the restriction. -/
instance finite_I_generatingSectionsRestrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (σ : (M.over U).GeneratingSections) [Finite σ.I] :
    Finite (generatingSectionsRestrict M U σ).I :=
  inferInstanceAs (Finite σ.I)

/-- **Finiteness of the sections of a restriction is finiteness of the sections of the original.**

The carriers are the same type (`AlgebraicGeometry.Scheme.Modules.restrict_obj`, and
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl`); the rings acting are
`Γ(V, U)` and `Γ(W, f ''ᵁ U)`, matched by `AlgebraicGeometry.Scheme.Hom.appIso`. So this is
`Module.Finite.of_ringEquiv`, and the hypothesis it wants is exactly
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom` read elementwise — after which the
proof is that lemma applied, with no rewriting.

The two `Module` instances are named rather than searched for. They exist at the spelling
`Γ(M.restrict f, U)`, and search will not find them at `Γ(M, f ''ᵁ U)`: the two are defeq but not
reducibly so — `exact x` compiles across them and `with_reducible exact x` is a type mismatch —
and search unifies at reducible transparency.

**Use `letI` and not `haveI` for the first of them.** With `haveI` the proof fails, and not with
a synthesis error: the given instance *is* used, and
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom` then sits at a different `Module`
structure from the one `•` elaborates at.
`set_option backward.isDefEq.respectTransparency false` does not rescue it either. Why `letI`
succeeds is not established here and no explanation should be read into this note; what
reproduces is the above, and `AlgebraicGeometry.Scheme.Modules.module_finite_Γ_of_isAffine`
hands over the same kind of instance across the same two spellings the same way. -/
theorem module_finite_sections_of_restrict {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
    (M : W.Modules) (U : V.Opens) [Module.Finite Γ(V, U) Γ(M.restrict f, U)] :
    Module.Finite Γ(W, f ''ᵁ U) Γ(M, f ''ᵁ U) := by
  letI : Module Γ(V, U) Γ(M, f ''ᵁ U) := inferInstanceAs (Module Γ(V, U) Γ(M.restrict f, U))
  haveI : Module.Finite Γ(V, U) Γ(M, f ''ᵁ U) :=
    inferInstanceAs (Module.Finite Γ(V, U) Γ(M.restrict f, U))
  exact Module.Finite.of_ringEquiv (f.appIso U).symm.commRingCatIsoToRingEquiv
    fun a n ↦ smul_restrictAppIso_hom_apply f M U a n

end

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# A quasicoherent datum bound together out of finite ones is finite

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`; see `README.md` on
the mirror tree.

`SheafOfModules.QuasicoherentData.bind` refines a cover: given a cover on which `M` has
quasicoherent data, and, for each member, a cover of that member on which the restriction has
presentations, it produces quasicoherent data of `M` on the composite cover. Mathlib records that
the composite is quasicoherent data and **not** that it is finite when the pieces are, which is
what a construction producing local *finite* presentations needs on the way out.

## The proof is `exact`, and that is the whole point

`SheafOfModules.Presentation.IsFinite` is finiteness of the two index types and nothing else, and
neither transport `bind` performs — `SheafOfModules.Presentation.map` along the equivalence with
the iterated slice, then `SheafOfModules.Presentation.ofIsIso` — touches an index type. So the
finiteness wanted **is** the finiteness given, up to definitional unfolding, and each field is
discharged by `exact` at the source's instance.

Instance search does not find it on its own: `bind` and `SheafOfModules.Presentation.ofIsIso` are
ordinary definitions, so `infer_instance` on the composite goal fails even though every
intermediate instance exists (Mathlib has one for `ofIsIso`, and one for
`SheafOfModules.Presentation.map` is a three-line consequence of
`SheafOfModules.Presentation.map_generators_I`). That is why this is stated rather than left to
the elaborator at the call site.

## Main results

- `SheafOfModules.QuasicoherentData.isFinitePresentation_bind`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`SheafOfModules.QuasicoherentData.bind` preserves finiteness of the presentations.**

Each presentation of the composite datum is one of the given presentations read through an
equivalence, and reading through an equivalence leaves the index types of the generators and of
the relations alone; `SheafOfModules.Presentation.IsFinite` asks for nothing else, so each field
is the corresponding field of the source. See the module docstring on why `infer_instance` does
not do this by itself. -/
instance QuasicoherentData.isFinitePresentation_bind (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, QuasicoherentData (M.over (X i)))
    [∀ i, (D i).IsFinitePresentation] :
    (QuasicoherentData.bind M X hX D).IsFinitePresentation where
  isFinite_presentation i :=
    { isFiniteType_generators :=
        ⟨GeneratingSections.IsFiniteType.finite (σ := ((D i.1).presentation i.2).generators)⟩
      isFiniteType_relations :=
        ⟨GeneratingSections.IsFiniteType.finite (σ := ((D i.1).presentation i.2).relations)⟩ }

end SheafOfModules

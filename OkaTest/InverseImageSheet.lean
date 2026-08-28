/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the sheet comparison

`AlgebraicGeometry.LocallyRingedSpace.sheetIso` says that over an open on which the map is an
open embedding, the inverse image is the base. Three things could be wrong with it that its type
does not show: the hypothesis could be unsatisfiable outside the trivial case `p = 𝟙`, the sheet
could be forced to be everything, and the covering statement
`IsLocalHomeomorph.sSup_sheetOpens` could be vacuous. This file rules all three out on the
**trivial two-sheeted cover of `ℂ¹`** — two copies of the line indexed by `Bool`, with the map
that forgets which copy.

* **The two sheets are genuine, distinct and disjoint**: `OkaTest.InverseImageSheet.sheet_ne` and
  `OkaTest.InverseImageSheet.disjoint_sheet`. So the source is not the base and the hypothesis is
  not being met by `p = 𝟙` in disguise.
* **Each sheet maps onto the whole line**:
  `OkaTest.InverseImageSheet.coe_sheetImage_eq_univ`. So `p '' V` is `⊤` for *both* sheets at once
  — which is exactly the configuration in which the naive `p '' (V₀ ∩ V₁) = p '' V₀ ∩ p '' V₁`
  fails, since `V₀ ∩ V₁ = ⊥` here while the two images are both everything.
* **The comparison is available at both sheets**: `OkaTest.InverseImageSheet.sheetIsoLine`.
* **The covering statement has content**: `OkaTest.InverseImageSheet.isLocalHomeomorph_proj` and
  `OkaTest.InverseImageSheet.sSup_sheetOpens_proj`, where the supremum is over a family with at
  least two members that are distinct and disjoint — so it is not the one-member family `{⊤}`.

**This is a test of the comparison and not of a non-trivial cover.** The cover here is trivial —
it is a product — and that is deliberate: it is the smallest input on which every claim above is
checkable, and nothing in `Oka/Geometry/RingedSpace/LocallyRingedSpace/InverseImageSheet.lean`
distinguishes a trivial cover from any other, since the hypothesis is about one sheet at a time.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat Topology

universe u

noncomputable section

namespace OkaTest.InverseImageSheet

/-- **The trivial two-sheeted cover of `ℂ¹`**: two copies of the line, indexed by `Bool`. -/
def twoSheets : TopCat.{u} :=
  TopCat.of (ULift.{u} Bool × (complexAffineSpace.{u} 1).toTopCat)

/-- **The covering map**: forget which sheet. -/
def proj : twoSheets.{u} ⟶ (complexAffineSpace.{u} 1).toTopCat :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- **The sheet indexed by `b`**, open because `ULift Bool` is discrete. -/
def sheet (b : ULift.{u} Bool) : Opens twoSheets.{u} :=
  ⟨Prod.fst ⁻¹' {b}, (isOpen_discrete _).preimage continuous_fst⟩

theorem mem_sheet {b : ULift.{u} Bool} {q : twoSheets.{u}} : q ∈ sheet.{u} b ↔ q.1 = b := Iff.rfl

/-- **The two sheets are distinct**, so the source really is two copies of the line. -/
theorem sheet_ne : sheet.{u} ⟨true⟩ ≠ sheet.{u} ⟨false⟩ := by
  intro h
  have hmem : (⟨⟨true⟩, fun _ ↦ (0 : ℂ)⟩ : twoSheets.{u}) ∈ sheet.{u} ⟨true⟩ := rfl
  rw [h] at hmem
  exact absurd (mem_sheet.1 hmem) (by simp)

/-- **Distinct sheets are disjoint.** -/
theorem disjoint_sheet {b b' : ULift.{u} Bool} (h : b ≠ b') :
    Disjoint (sheet.{u} b : Set twoSheets.{u}) (sheet.{u} b') :=
  Set.disjoint_left.2 fun _ hq hq' ↦ h (hq.symm.trans hq')

/-- **A sheet, as a space, is the line**, by the map that forgets which sheet it is. -/
def sheetHomeo (b : ULift.{u} Bool) :
    (sheet.{u} b : Set twoSheets.{u}) ≃ₜ (complexAffineSpace.{u} 1).toTopCat where
  toFun q := q.1.2
  invFun z := ⟨(b, z), rfl⟩
  left_inv := by rintro ⟨⟨b', z⟩, (rfl : b' = b)⟩; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := by fun_prop

/-- **Each sheet is a sheet**, in the sense of `sheetOpens`. -/
theorem sheet_mem_sheetOpens (b : ULift.{u} Bool) : sheet.{u} b ∈ sheetOpens proj.{u} :=
  (sheetHomeo.{u} b).isOpenEmbedding

theorem isOpenEmbedding_sheet (b : ULift.{u} Bool) :
    IsOpenEmbedding fun q : sheet.{u} b ↦ proj.{u} (q : twoSheets.{u}) :=
  sheet_mem_sheetOpens.{u} b

/-- **The projection is a local homeomorphism**, witnessed by the two sheets themselves. -/
theorem isLocalHomeomorph_proj : IsLocalHomeomorph fun q ↦ proj.{u} q :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.2 fun q ↦
    ⟨sheet.{u} q.1, (sheet.{u} q.1).isOpen.mem_nhds rfl, sheet_mem_sheetOpens.{u} q.1⟩

/-- **The sheets cover**, which is `IsLocalHomeomorph.sSup_sheetOpens` at a family containing the
two distinct, disjoint members above. -/
theorem sSup_sheetOpens_proj : sSup (sheetOpens proj.{u}) = ⊤ :=
  IsLocalHomeomorph.sSup_sheetOpens _ isLocalHomeomorph_proj.{u}

/-- **Each sheet maps onto the whole line.**

Both sheets do, at once, which is what makes this the configuration where
`p '' (V₀ ∩ V₁) = p '' V₀ ∩ p '' V₁` fails: the left-hand side is empty and the right-hand side
is everything. -/
theorem coe_sheetImage_eq_univ (b : ULift.{u} Bool) :
    (LocallyRingedSpace.sheetImage (complexAffineSpace.{u} 1) proj.{u} (sheet.{u} b)
      (isOpenEmbedding_sheet.{u} b) : Set (complexAffineSpace.{u} 1).toTopCat) = Set.univ := by
  ext z
  exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨⟨(b, z), rfl⟩, rfl⟩⟩

/-- **Over either sheet, the inverse image of the two-sheeted cover is the line.** -/
def sheetIsoLine (b : ULift.{u} Bool) :
    ((complexAffineSpace.{u} 1).inverseImage proj.{u}).restrict (sheet.{u} b).isOpenEmbedding ≅
      (complexAffineSpace.{u} 1).restrict
        (LocallyRingedSpace.sheetImage (complexAffineSpace.{u} 1) proj.{u} (sheet.{u} b)
          (isOpenEmbedding_sheet.{u} b)).isOpenEmbedding :=
  LocallyRingedSpace.sheetIso _ _ _ (isOpenEmbedding_sheet.{u} b)

/-! ### The `ℂ`-algebra structures

`ComplexAnalytic.isCLinearHom_sheetHom` says the comparison respects the `ℂ`-algebra structures
the two sides inherit from the base. The base here is `ℂ¹` with its constants, and the two
statements below are that theorem and its inverse at that input — so neither is vacuous, and the
open the target is restricted to is the whole line. -/

/-- **The `ℂ`-algebra structure on the line**: the constants, as
`ComplexAnalytic.AnalyticSpace.complexAffineSpace` carries them. Named only to keep the
statements below readable. -/
def lineAlgMap : ℂ →+* (complexAffineSpace.{u} 1).presheaf.obj (op ⊤) :=
  (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{u} 1).algebraMap

/-- The sheet's own structure: `OkaTest.InverseImageSheet.lineAlgMap` pulled back along the map
to the line. -/
abbrev sheetAlgMap (b : ULift.{u} Bool) :
    ℂ →+* (((complexAffineSpace.{u} 1).inverseImage proj.{u}).restrict
      (sheet.{u} b).isOpenEmbedding).presheaf.obj (op ⊤) :=
  LocallyRingedSpace.comapAlgMap
    (LocallyRingedSpace.sheetToBase (complexAffineSpace.{u} 1) proj.{u} (sheet.{u} b))
    lineAlgMap.{u}

/-- The structure on the open of the line the sheet lies over: `lineAlgMap` restricted. -/
abbrev baseAlgMap (b : ULift.{u} Bool) :
    ℂ →+* ((complexAffineSpace.{u} 1).restrict
      (LocallyRingedSpace.sheetImage (complexAffineSpace.{u} 1) proj.{u} (sheet.{u} b)
        (isOpenEmbedding_sheet.{u} b)).isOpenEmbedding).presheaf.obj (op ⊤) :=
  (complexAffineSpace.{u} 1).resAlgMap lineAlgMap.{u}
    (LocallyRingedSpace.sheetImage (complexAffineSpace.{u} 1) proj.{u} (sheet.{u} b)
      (isOpenEmbedding_sheet.{u} b))

/-- **The sheet lies over the whole line as an *open***, not merely as a set.

`OkaTest.InverseImageSheet.coe_sheetImage_eq_univ` is the statement about the underlying set;
this is the same fact about the open itself, which is the argument
`OkaTest.InverseImageSheet.baseAlgMap` restricts to. -/
theorem sheetImage_eq_top (b : ULift.{u} Bool) :
    LocallyRingedSpace.sheetImage (complexAffineSpace.{u} 1) proj.{u} (sheet.{u} b)
      (isOpenEmbedding_sheet.{u} b) = ⊤ :=
  TopologicalSpace.Opens.ext (coe_sheetImage_eq_univ.{u} b)

/-- **The comparison at either sheet is `ℂ`-linear** for the structure `ℂ¹` carries. -/
theorem isCLinearHom_sheetHom_line (b : ULift.{u} Bool) :
    ComplexAnalytic.IsCLinearHom
      (LocallyRingedSpace.sheetHom (complexAffineSpace.{u} 1) proj.{u} (sheet.{u} b)
        (isOpenEmbedding_sheet.{u} b))
      (sheetAlgMap.{u} b) (baseAlgMap.{u} b) :=
  ComplexAnalytic.isCLinearHom_sheetHom _ _ _ _ _

/-- **And so is its inverse**, so `OkaTest.InverseImageSheet.sheetIsoLine` identifies the two
`ℂ`-algebra structures and not only the two spaces. -/
theorem isCLinearHom_sheetIsoLine_inv (b : ULift.{u} Bool) :
    ComplexAnalytic.IsCLinearHom (sheetIsoLine.{u} b).inv (baseAlgMap.{u} b)
      (sheetAlgMap.{u} b) :=
  ComplexAnalytic.isCLinearHom_sheetIso_inv _ _ _ _ _

/-- **The structure the sheet inherits from `p⁻¹ℂ¹` is the one the comparison pulls back**, which
is `ComplexAnalytic.comapAlgMap_sheetHom` here: the two routes to a `ℂ`-algebra structure on a
sheet — restrict the one on the whole inverse image, or pull the base's back along the
comparison — give the same ring homomorphism. -/
theorem comapAlgMap_sheetHom_line (b : ULift.{u} Bool) :
    LocallyRingedSpace.comapAlgMap
        (LocallyRingedSpace.sheetHom (complexAffineSpace.{u} 1) proj.{u} (sheet.{u} b)
          (isOpenEmbedding_sheet.{u} b)) (baseAlgMap.{u} b) =
      ((complexAffineSpace.{u} 1).inverseImage proj.{u}).resAlgMap
        (LocallyRingedSpace.comapAlgMap
          ((complexAffineSpace.{u} 1).inverseImageHom proj.{u}) lineAlgMap.{u}) (sheet.{u} b) :=
  ComplexAnalytic.comapAlgMap_sheetHom _ _ _ _ _

end OkaTest.InverseImageSheet

end

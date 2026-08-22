/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Local

/-!
# `AnalyticSpace.ofOpens` is applied to a cover no member of which is the whole space

`ComplexAnalytic.HasLocalModels.of_iSup_eq_top` would be true and useless if the only covers it
were ever applied to contained `⊤`, because then it would be the transport along
`ComplexAnalytic.AnalyticSpace.restrict` at `U = ⊤` and would say nothing about assembling a
space from pieces. **That degeneracy is the live one here** and not a hypothetical: the one
analytic space this development starts from, `ComplexAnalytic.AnalyticSpace.complexAffineSpace`,
has `local_model` witnessed by the chart on `⊤` at *every* point, so every chart in sight is a
global one until something forces otherwise.

These tests force it. `ℂ` is covered by the complements of two distinct points; each is open
because the carrier is a product of copies of `ℂ` and so is `T1`, the two cover because the
points are distinct, and **neither is `⊤`** — recorded below as a theorem rather than as a
remark, so that a later simplification of the cover cannot quietly reintroduce the degenerate
case.

The last example checks that the space produced is the one it should be, on the nose.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.AnalyticSpaceLocal

/-- The origin of `ℂ`, as a point of `complexAffineSpace 1`. -/
def a : (complexAffineSpace.{u} 1 : LocallyRingedSpace.{u}) := fun _ ↦ 0

/-- The point `1` of `ℂ`, as a point of `complexAffineSpace 1`. -/
def b : (complexAffineSpace.{u} 1 : LocallyRingedSpace.{u}) := fun _ ↦ 1

theorem a_ne_b : a.{u} ≠ b.{u} := fun h ↦ by
  simpa [a, b] using congrFun h (ULift.up 0)

/-- The carrier of `complexAffineSpace 1` is `ULift (Fin 1) → ℂ`, hence `T1`. Declared by hand
because instance search does not cross the `TopCat.of` coercion; see
`Oka/AnalyticSpace/Basic.lean` on the same seam. -/
local instance : T1Space ((complexAffineSpace.{u} 1 : LocallyRingedSpace.{u}) : Type u) :=
  inferInstanceAs (T1Space (ULift.{u} (Fin 1) → ℂ))

/-- `ℂ` minus one of two distinct points, as a two-element family of open sets. -/
def cover : Bool → Opens (complexAffineSpace.{u} 1 : LocallyRingedSpace.{u})
  | false => ⟨{a.{u}}ᶜ, isOpen_compl_singleton⟩
  | true => ⟨{b.{u}}ᶜ, isOpen_compl_singleton⟩

theorem iSup_cover : ⨆ i, cover.{u} i = ⊤ := by
  refine Opens.ext (Set.eq_univ_of_forall fun z ↦ ?_)
  rw [Opens.coe_iSup]
  by_cases h : z = a.{u}
  · exact Set.mem_iUnion.2 ⟨true, fun hz ↦ a_ne_b.{u} (h ▸ hz)⟩
  · exact Set.mem_iUnion.2 ⟨false, h⟩

/-- **No member of the cover is the whole space.** This is what makes the applicability test
below a test of anything: with `⊤` in the cover, `HasLocalModels.of_iSup_eq_top` degenerates. -/
theorem cover_ne_top (i : Bool) : cover.{u} i ≠ ⊤ := by
  cases i with
  | false =>
    intro h
    have ha : a.{u} ∈ cover.{u} false := by rw [h]; trivial
    exact ha rfl
  | true =>
    intro h
    have hb : b.{u} ∈ cover.{u} true := by rw [h]; trivial
    exact hb rfl

/-- **No single member of the cover suffices**: each omits a point the other contains, so the
hypothesis really is being used at both indices. -/
theorem cover_not_le (i : Bool) : ¬ ⊤ ≤ cover.{u} i := fun h ↦ cover_ne_top i (top_le_iff.1 h)

/-- Each member of the cover has local models, by restriction from `ℂ` itself. -/
theorem hasLocalModels_cover (i : Bool) :
    HasLocalModels ((complexAffineSpace.{u} 1).restrict (cover.{u} i).isOpenEmbedding)
      ((complexAffineSpace.{u} 1).resAlgMap
        (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap (cover.{u} i)) :=
  (AnalyticSpace.complexAffineSpace.{u} 1).hasLocalModels.restrict (cover.{u} i)

/-- **`ℂ`, reassembled from a cover neither member of which is the whole space.** -/
def reassembled : AnalyticSpace.{u} :=
  AnalyticSpace.ofOpens (complexAffineSpace.{u} 1)
    (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap cover.{u} iSup_cover hasLocalModels_cover

example : reassembled.{u}.toLocallyRingedSpace = complexAffineSpace.{u} 1 := rfl

example : reassembled.{u}.algebraMap = (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap := rfl

/-! ### The `ℂ`-algebra structure, glued from the pieces

The examples above hand `AnalyticSpace.ofOpens` the `ℂ`-algebra structure of the **ambient**
space. That is not the shape a gluing construction produces: there the pieces are what one has.
`AnalyticSpace.ofOpensCompatible` takes the structures on the members, and these tests run it on
the same cover — neither member of which is `⊤` — and check that the round trip returns the
structure it started from, on the nose.
-/

/-- The constants of `ℂ`, restricted to each member of the cover. -/
def coverAlg (i : Bool) : ℂ →+* (complexAffineSpace.{u} 1).presheaf.obj (op (cover.{u} i)) :=
  ((complexAffineSpace.{u} 1).presheaf.map (homOfLE (le_top : cover.{u} i ≤ ⊤)).op).hom.comp
    (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap

theorem isCompatible_coverAlg (c : ℂ) :
    TopCat.Presheaf.IsCompatible (complexAffineSpace.{u} 1).presheaf cover.{u}
      fun i ↦ coverAlg.{u} i c :=
  LocallyRingedSpace.isCompatible_map_le_top _

theorem hasLocalModels_coverAlg (i : Bool) :
    HasLocalModels ((complexAffineSpace.{u} 1).restrict (cover.{u} i).isOpenEmbedding)
      (((complexAffineSpace.{u} 1).presheaf.map
          (homOfLE (Opens.isOpenEmbedding_obj_top (cover.{u} i)).le).op).hom.comp
        (coverAlg.{u} i)) := by
  have key : (((complexAffineSpace.{u} 1).presheaf.map
        (homOfLE (Opens.isOpenEmbedding_obj_top (cover.{u} i)).le).op).hom.comp
      (coverAlg.{u} i)) =
      (complexAffineSpace.{u} 1).resAlgMap
        (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap (cover.{u} i) :=
    (LocallyRingedSpace.resAlgMap_eq_comp _ _).symm
  rw [key]
  exact hasLocalModels_cover.{u} i

/-- **`ℂ`, reassembled from a cover with the `ℂ`-algebra structure given on the pieces** rather
than on the ambient space. -/
def reassembledCompatible : AnalyticSpace.{u} :=
  AnalyticSpace.ofOpensCompatible (complexAffineSpace.{u} 1) cover.{u} iSup_cover.{u}
    coverAlg.{u} isCompatible_coverAlg.{u} hasLocalModels_coverAlg.{u}

example : reassembledCompatible.{u}.toLocallyRingedSpace = complexAffineSpace.{u} 1 := rfl

/-- **The glued `ℂ`-algebra structure is the one the pieces came from.** This is the round trip,
and it is what says the gluing is doing the right thing rather than merely type-checking: the
uniqueness half of the sheaf condition identifies the gluing of the restrictions of a global
section with that section. -/
example : reassembledCompatible.{u}.algebraMap
    = (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap :=
  RingHom.ext fun c ↦
    LocallyRingedSpace.glueSection_eq iSup_cover.{u} (fun i ↦ coverAlg.{u} i c)
      (isCompatible_coverAlg.{u} c)
      ((AnalyticSpace.complexAffineSpace.{u} 1).algebraMap c) fun _ ↦ rfl

end OkaTest.AnalyticSpaceLocal

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.OpenSubspace

/-!
# Non-vacuity of the gluing of morphisms of locally ringed spaces

`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` glues morphisms out of the members of an
open cover of a locally ringed space. Every statement it proves is true of the **trivial**
one-member cover by `⊤`, for which `fromGlued` is an isomorphism because the multicoequalizer of
a one-object diagram is that object, and for which `glueMorphisms` returns its own input. So the
checks that matter are at a cover which is not that one.

The cover used here is `ℂ` by the two punctured planes `ℂ ∖ {1}` and `ℂ ∖ {-1}`. Neither is the
whole space (`twoPunctures_ne_top`), so `punctureCover` is a genuine two-member cover, and
`IsIso punctureCover.fromGlued` is then the statement that gluing those two open subspaces along
their intersection returns `ℂ` — the theorem the file exists for.

The morphism glued is the comparison morphism `ℂ ⟶ Spec ℂ[X]` of
`Oka/Analytification/AffineSpace.lean`, restricted to each member. `glue_localSpec` identifies
the result with that **named** morphism rather than with an unnamed one produced by the same
construction, and `injective_base_glue_localSpec` records that its point map is injective, so
nothing has been collapsed. `glue_incl` does the same over the same cover for a *different*
family, landing on `𝟙`: a construction returning something determined by the cover alone could
not satisfy both.

The two morphisms glued over `punctureCover` are restrictions of a single global one, so their
agreement on the overlap is `pullback.condition` rather than a computation. **That gap is closed
in the last section**, which needed a source whose cover has *disconnected* overlaps and which
this development did not have until `ComplexAnalytic.AnalyticSpace.restrict` and
`ComplexAnalytic.nodeAxis_inf_eq_bot` existed. What the `punctureCover` tests establish on their
own is that the compatibility hypothesis is satisfiable at a non-trivial cover, that
`glueMorphisms` computes the morphism it should, and that `fromGlued` is an isomorphism there.

## Gluing over a cover by opens, and a genuinely independent pair

The last section is the non-vacuity of
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens`, whose compatibility
hypothesis is an equation of morphisms out of `X.restrict (U i ⊓ U j)` rather than out of the
categorical pullback. The witness is the **punctured node** covered by its two punctured axes,
which are disjoint (`pnAxis_inf_carrier_eq_empty`, from `ComplexAnalytic.nodeAxis_inf_eq_bot`),
so the compatibility is vacuous and *any* pair of morphisms out of the two pieces glues.

`glue_pn_ne_nodeToLine` is what makes this a witness rather than an instantiation: the glued
morphism takes the value `1` at the point `(0, 1)` where `ComplexAnalytic.nodeToLineHom 0` takes
`0`, so it is **not** the restriction of either piece's morphism, and it is the first glued
morphism in this development that is not something one already had.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open ComplexAnalytic

universe u

noncomputable section

/-- The open subset of `ℂ` on which the first coordinate is not `1`. -/
def punctureAt (c : ℂ) : Opens (ULift.{u} (Fin 1) → ℂ) :=
  ⟨{z | z (ULift.up 0) ≠ c},
    isOpen_compl_singleton.preimage (continuous_apply (ULift.up 0))⟩

/-- The two-element family of opens puncturing `ℂ` at `1` and at `-1`. -/
def twoPunctures : ULift.{u} Bool → Opens (ULift.{u} (Fin 1) → ℂ) :=
  fun b ↦ if b.down then punctureAt.{u} 1 else punctureAt.{u} (-1)

theorem twoPunctures_covers (z : ULift.{u} (Fin 1) → ℂ) :
    ∃ b, z ∈ twoPunctures.{u} b := by
  rcases eq_or_ne (z (ULift.up 0)) 1 with h | h
  · refine ⟨⟨false⟩, ?_⟩
    rw [twoPunctures, if_neg (by simp)]
    exact fun hcon ↦ by rw [h] at hcon; norm_num at hcon
  · exact ⟨⟨true⟩, by rw [twoPunctures, if_pos rfl]; exact h⟩

theorem twoPunctures_ne_top (b : ULift.{u} Bool) : twoPunctures.{u} b ≠ ⊤ := by
  rcases b with ⟨b⟩
  cases b
  · refine fun hcon ↦ ?_
    have h : (fun _ ↦ -1 : ULift.{u} (Fin 1) → ℂ) ∈ twoPunctures.{u} ⟨false⟩ := hcon ▸ trivial
    rw [twoPunctures, if_neg (by simp)] at h
    exact h rfl
  · refine fun hcon ↦ ?_
    have h : (fun _ ↦ 1 : ULift.{u} (Fin 1) → ℂ) ∈ twoPunctures.{u} ⟨true⟩ := hcon ▸ trivial
    rw [twoPunctures, if_pos rfl] at h
    exact h rfl

/-- The cover of `ℂ` by the two punctured planes. Neither member is the whole space
(`twoPunctures_ne_top`), so this is not the trivial one-member cover by `⊤`. -/
def punctureCover : LocallyRingedSpace.OpenCover (complexSpace.{u} (ULift.{u} (Fin 1))) :=
  LocallyRingedSpace.openCoverOfOpens twoPunctures.{u} twoPunctures_covers.{u}

/-- The affine line over `ℂ`, algebraically, as the target of the comparison morphism. -/
abbrev specLine : LocallyRingedSpace.{u} :=
  Spec.locallyRingedSpaceObj (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) ℂ))

/-- The restriction of the comparison morphism `ℂ ⟶ Spec ℂ[X]` to the `b`-th punctured plane.
The two are built separately, one for each member of the cover. -/
def localSpec (b : punctureCover.{u}.J) : punctureCover.{u}.obj b ⟶ specLine.{u} :=
  punctureCover.{u}.map b ≫ complexSpaceToSpec _

theorem localSpec_compat (x y : punctureCover.{u}.J) :
    pullback.fst (punctureCover.{u}.map x) (punctureCover.{u}.map y) ≫ localSpec.{u} x =
      pullback.snd (punctureCover.{u}.map x) (punctureCover.{u}.map y) ≫ localSpec.{u} y := by
  rw [localSpec, localSpec, ← Category.assoc, ← Category.assoc, pullback.condition]

/-- **The two locally defined morphisms glue to the comparison morphism.**

The point is that `glueMorphisms` is characterised by its restrictions, so identifying the
result with a *named* morphism — rather than with an unnamed one produced by the same
construction — is what shows the gluing computes something. -/
theorem glue_localSpec :
    punctureCover.{u}.glueMorphisms localSpec.{u} localSpec_compat.{u} =
      complexSpaceToSpec _ :=
  (punctureCover.{u}.existsUnique_glueMorphisms localSpec.{u} localSpec_compat.{u}).unique
    (punctureCover.{u}.ι_glueMorphisms _ _) fun _ ↦ rfl

/-- **The glued morphism is injective on points**, so it is not constant and the gluing has not
collapsed anything. -/
theorem injective_base_glue_localSpec :
    Function.Injective fun z : ULift.{u} (Fin 1) → ℂ ↦
      (punctureCover.{u}.glueMorphisms localSpec.{u} localSpec_compat.{u}).base z := by
  rw [glue_localSpec]
  exact complexSpaceToSpec_base_injective

/-- The two members of the cover are distinct opens. With `twoPunctures_ne_top` this says the
cover really has two members: neither is `⊤`, and they are not each other. -/
theorem twoPunctures_ne : twoPunctures.{u} ⟨true⟩ ≠ twoPunctures.{u} ⟨false⟩ := by
  intro hcon
  have h : (fun _ ↦ (1 : ℂ) : ULift.{u} (Fin 1) → ℂ) ∈ twoPunctures.{u} ⟨false⟩ := by
    rw [twoPunctures, if_neg (by simp)]
    exact fun hc ↦ by norm_num at hc
  rw [← hcon, twoPunctures, if_pos rfl] at h
  exact h rfl

/-- **Gluing the inclusions of the two members returns the identity of `ℂ`.**

This is a *second* named target for the same construction over the same cover:
`glue_localSpec` identifies the glued morphism with `complexSpaceToSpec` and this one identifies
it with `𝟙`. A `glueMorphisms` which returned something determined by the cover alone, rather
than by the family it is given, could not satisfy both. -/
theorem glue_incl :
    punctureCover.{u}.glueMorphisms (fun b ↦ punctureCover.{u}.map b)
        (fun _ _ ↦ pullback.condition) =
      𝟙 (complexSpace.{u} (ULift.{u} (Fin 1))) :=
  (punctureCover.{u}.existsUnique_glueMorphisms (fun b ↦ punctureCover.{u}.map b)
      (fun _ _ ↦ pullback.condition)).unique
    (punctureCover.{u}.ι_glueMorphisms _ _) fun _ ↦ Category.comp_id _

/-- The gluing of the two punctured planes really is `ℂ`. This is the statement all the work in
`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` goes into, at a cover which is not the
trivial one-member cover by `⊤`. -/
example : IsIso punctureCover.{u}.fromGlued := inferInstance


/-! ### Gluing over a cover by opens, with disconnected overlaps -/

abbrev PN : LocallyRingedSpace.{u} := puncturedNodeSpace.{u}.toLocallyRingedSpace

/-- The two punctured axes, as opens of the punctured node. -/
def pnAxis (j : ULift.{u} (Fin 2)) : Opens (PN.{u}) :=
  (Opens.map (AnalyticSpace.node.{u}.toLocallyRingedSpace.ofRestrict
    puncturedNode.{u}.isOpenEmbedding).base).obj (nodeAxis.{u} j)

theorem mem_pnAxis_iff (j : ULift.{u} (Fin 2)) (x : PN.{u}) :
    x ∈ pnAxis.{u} j ↔ (x.1 : AnalyticSpace.node.{u}) ∈ nodeAxis.{u} j := Iff.rfl

theorem pnAxis_covers (x : PN.{u}) : ∃ j, x ∈ pnAxis.{u} j := by
  rcases x.2 with h | h
  · exact ⟨ULift.up 0, h⟩
  · exact ⟨ULift.up 1, h⟩

theorem ulift_fin_two_cases (l : ULift.{u} (Fin 2)) :
    l = ULift.up 0 ∨ l = ULift.up 1 := by
  rcases l with ⟨l⟩
  fin_cases l
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The two punctured axes are disjoint as opens of the punctured node**, so a pair of
morphisms out of them is subject to no compatibility condition. -/
theorem pnAxis_inf_carrier_eq_empty (i j : ULift.{u} (Fin 2)) (hij : i ≠ j) :
    ((pnAxis.{u} i ⊓ pnAxis.{u} j : Opens (PN.{u})) : Set (PN.{u})) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  have hprod : (x.1 : AnalyticSpace.node.{u}).1.1 (ULift.up 0) *
      (x.1 : AnalyticSpace.node.{u}).1.1 (ULift.up 1) = 0 :=
    (mem_zeroLocus_nodeSection_iff _).1 (x.1).2
  have key : ∀ l : ULift.{u} (Fin 2), (x.1 : AnalyticSpace.node.{u}).1.1 l ≠ 0 := by
    intro l
    rcases ulift_fin_two_cases i with hi | hi <;> rcases ulift_fin_two_cases j with hj | hj
    · exact absurd (hi.trans hj.symm) hij
    · rcases ulift_fin_two_cases l with hl | hl
      · exact hl ▸ hi ▸ hx.1
      · exact hl ▸ hj ▸ hx.2
    · rcases ulift_fin_two_cases l with hl | hl
      · exact hl ▸ hj ▸ hx.2
      · exact hl ▸ hi ▸ hx.1
    · exact absurd (hi.trans hj.symm) hij
  exact mul_ne_zero (key (ULift.up 0)) (key (ULift.up 1)) hprod

/-- On each punctured axis, the corresponding coordinate morphism of the node. -/
def pnHom (j : ULift.{u} (Fin 2)) :
    PN.{u}.restrict (pnAxis.{u} j).isOpenEmbedding ⟶ complexAffineSpace.{u} 1 :=
  PN.{u}.ofRestrict (pnAxis.{u} j).isOpenEmbedding ≫
    AnalyticSpace.node.{u}.toLocallyRingedSpace.ofRestrict puncturedNode.{u}.isOpenEmbedding ≫
      nodeToLineHom.{u} j

theorem existsUnique_glue_pn :
    ∃! φ : PN.{u} ⟶ complexAffineSpace.{u} 1,
      ∀ j, PN.{u}.ofRestrict (pnAxis.{u} j).isOpenEmbedding ≫ φ = pnHom.{u} j :=
  LocallyRingedSpace.existsUnique_glueMorphisms_of_opens pnAxis.{u} pnAxis_covers.{u} pnHom.{u}
    (fun i j ↦ by
      rcases eq_or_ne i j with rfl | hij
      · rfl
      · exact LocallyRingedSpace.hom_ext_restrict_of_isEmpty
          (pnAxis_inf_carrier_eq_empty i j hij) _ _)

theorem base_glue_pn (φ : PN.{u} ⟶ complexAffineSpace.{u} 1)
    (hφ : ∀ j, PN.{u}.ofRestrict (pnAxis.{u} j).isOpenEmbedding ≫ φ = pnHom.{u} j)
    (j : ULift.{u} (Fin 2)) (x : PN.{u}) (hx : x ∈ pnAxis.{u} j) :
    (φ.base x : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) =
      (x.1 : AnalyticSpace.node.{u}).1.1 j := by
  have h := congrArg (fun m : PN.{u}.restrict (pnAxis.{u} j).isOpenEmbedding ⟶
      complexAffineSpace.{u} 1 ↦
    ((m.base ⟨x, hx⟩ : ULift.{u} (Fin 1) → ℂ) (ULift.up 0))) (hφ j)
  refine h.trans ?_
  exact base_nodeToLineHom j x.1 (ULift.up 0)

/-- The glued morphism takes the value `1` at the point `(0, 1)`, where the *first* coordinate
morphism takes `0`. So it is **not** the restriction of `nodeToLineHom 0`, and the pair glued was
genuinely independent. -/
theorem glue_pn_ne_nodeToLine (φ : PN.{u} ⟶ complexAffineSpace.{u} 1)
    (hφ : ∀ j, PN.{u}.ofRestrict (pnAxis.{u} j).isOpenEmbedding ≫ φ = pnHom.{u} j) :
    (φ.base ⟨axisPoint.{u} (ULift.up 1), axisPoint_mem _⟩ :
        ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠
      ((AnalyticSpace.node.{u}.toLocallyRingedSpace.ofRestrict
          puncturedNode.{u}.isOpenEmbedding ≫ nodeToLineHom.{u} (ULift.up 0)).base
        ⟨axisPoint.{u} (ULift.up 1), axisPoint_mem _⟩ :
          ULift.{u} (Fin 1) → ℂ) (ULift.up 0) := by
  rw [base_glue_pn φ hφ (ULift.up 1) _ (show (axisPoint.{u} (ULift.up 1)) ∈
      nodeAxis.{u} (ULift.up 1) from by
    change (axisPoint.{u} (ULift.up 1)).1.1 (ULift.up 1) ≠ 0
    rw [axisPoint_coord, if_pos rfl]
    exact one_ne_zero)]
  rw [show ((AnalyticSpace.node.{u}.toLocallyRingedSpace.ofRestrict
      puncturedNode.{u}.isOpenEmbedding ≫ nodeToLineHom.{u} (ULift.up 0)).base
      ⟨axisPoint.{u} (ULift.up 1), axisPoint_mem _⟩ : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) =
    (axisPoint.{u} (ULift.up 1)).1.1 (ULift.up 0) from
      base_nodeToLineHom (ULift.up 0) (axisPoint.{u} (ULift.up 1)) (ULift.up 0)]
  rw [axisPoint_coord, if_pos rfl, axisPoint_coord, if_neg (by simp)]
  exact one_ne_zero

end

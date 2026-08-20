/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

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

**What this does not check, said plainly.** The two morphisms glued are restrictions of a single
global one, so their agreement on the overlap is `pullback.condition` rather than a computation.
A pair built genuinely independently would be a stronger witness; producing one needs a source
whose cover has disconnected overlaps, which this development does not yet have. What the test
does establish is that the compatibility hypothesis is satisfiable at a non-trivial cover, that
`glueMorphisms` computes the morphism it should, and that `fromGlued` is an isomorphism there.
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

end

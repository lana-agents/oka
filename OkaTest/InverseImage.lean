/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the inverse image of a locally ringed space

`AlgebraicGeometry.LocallyRingedSpace.inverseImage` gives a locally ringed space for **any**
continuous map into the underlying space, and two things could be wrong with it that its type does
not show: the structure sheaf is a sheafification and could have collapsed, and the construction
could be an elaborate way of returning the base. This file rules both out on the smallest input
that separates them — **the two-point discrete space mapped constantly to a point of `ℂ¹`**.

* **The carrier and the projection are what they are asked to be**, on the nose:
  `OkaTest.InverseImage.inverseImage_bothToPoint_toTopCat` and
  `OkaTest.InverseImage.inverseImageHom_bothToPoint_base` are both `rfl`, so the space really is
  the two-point space and the morphism really is the given map. Without them nothing rules out a
  construction that quietly returned `ℂ¹` itself.
* **Both stalks are the full germ ring** `LocalOkaRing (ULift (Fin 1))` — the convergent power
  series in one variable — by `OkaTest.InverseImage.sheetStalkEquiv`, which is
  `AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso` composed with `okaStalkEquiv`. So
  the sheafification has not collapsed: a two-point space carrying the *zero* sheaf would satisfy
  every other statement here.
* **The two points are distinct and lie over the same point of the base**, by
  `OkaTest.InverseImage.up_true_ne_up_false` and
  `OkaTest.InverseImage.bothToPoint_apply`. Together with the bullet above this is the local
  picture of a **two-sheeted cover**: one point of the base, two points above it, and the germ ring
  reproduced at each — which is what the construction exists for and what a degenerate one would
  not give.

**This is a test of the construction and not of a covering map.** The constant map is not a local
homeomorphism, and nothing here is an instance of a covering space; what it exercises is exactly
the part of the construction that is insensitive to that, which is all of it.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat

universe u

noncomputable section

namespace OkaTest.InverseImage

/-- **The two-point discrete space.** -/
def twoPoints : TopCat.{u} := TopCat.of (ULift.{u} Bool)

theorem up_true_ne_up_false : (ULift.up true : twoPoints.{u}) ≠ ULift.up false := by simp

variable (z : ULift.{u} (Fin 1) → ℂ)

/-- **Both points to one point of `ℂ¹`.** -/
def bothToPoint : twoPoints.{u} ⟶ (complexAffineSpace.{u} 1).toTopCat :=
  TopCat.ofHom ⟨fun _ ↦ z, continuous_const⟩

/-- **Both points lie over `z`.** -/
@[simp]
theorem bothToPoint_apply (b : twoPoints.{u}) : (bothToPoint.{u} z) b = z := rfl

/-- **The carrier of the inverse image is the two-point space**, on the nose. -/
theorem inverseImage_bothToPoint_toTopCat :
    ((complexAffineSpace.{u} 1).inverseImage (bothToPoint.{u} z)).toTopCat = twoPoints.{u} := rfl

/-- **The projection is the map it was built from**, on the nose. -/
theorem inverseImageHom_bothToPoint_base :
    ((complexAffineSpace.{u} 1).inverseImageHom (bothToPoint.{u} z)).base =
      bothToPoint.{u} z := rfl

/-- **The stalk at either point is the germ ring in one variable.**

`AlgebraicGeometry.LocallyRingedSpace.stalkInverseImageIso` says the stalk at `b` is the stalk of
`ℂ¹` at `z`, and `okaStalkEquiv` says that is `LocalOkaRing (ULift (Fin 1))`. The composite is
independent of `b`, which is the content: the germ ring appears once per sheet. -/
def sheetStalkEquiv (b : twoPoints.{u}) :
    ((complexAffineSpace.{u} 1).inverseImage (bothToPoint.{u} z)).presheaf.stalk b ≃+*
      LocalOkaRing (ULift.{u} (Fin 1)) :=
  ((LocallyRingedSpace.stalkInverseImageIso
    (complexAffineSpace.{u} 1) (bothToPoint.{u} z) b).symm.commRingCatIsoToRingEquiv).trans
      (okaStalkEquiv z)

end OkaTest.InverseImage

end

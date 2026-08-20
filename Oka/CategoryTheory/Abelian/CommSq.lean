/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Kernels in a pullback square

Material for `Mathlib/CategoryTheory/Abelian/CommSq.lean`; see `README.md` on the mirror tree.
That file has `CategoryTheory.IsPullback.mono_cokernel_map_of_isPullback` and the dual
`CategoryTheory.IsPullback.epi_kernel_map_of_isPushout`, which compare the (co)kernels of the
two *parallel* maps of a square. This file records the other elementary fact about a pullback
square, which those do not give: the kernel of a projection *is* the kernel of the map it is a
base change of.

Elementwise, `ker (snd : X ×_Z Y ⟶ Y)` is `{(x, 0) | f x = 0}`, which the first projection
identifies with `ker f`.

## Main definitions

- `CategoryTheory.IsPullback.kernelIso`
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.IsPullback

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **In a pullback square, the kernel of one projection is the kernel of the parallel map**,
via the other projection. -/
noncomputable def kernelIso {P X Y Z : A} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g) :
    kernel snd ≅ kernel f where
  hom := kernel.lift f (kernel.ι snd ≫ fst) (by
    rw [Category.assoc, sq.w, ← Category.assoc, kernel.condition, zero_comp])
  inv := kernel.lift snd (sq.lift (kernel.ι f) 0 (by rw [kernel.condition, zero_comp]))
    (by rw [sq.lift_snd])
  hom_inv_id := by
    refine (cancel_mono (kernel.ι snd)).1 ?_
    rw [Category.assoc, kernel.lift_ι, Category.id_comp]
    refine sq.hom_ext ?_ ?_
    · rw [Category.assoc, sq.lift_fst, kernel.lift_ι]
    · rw [Category.assoc, sq.lift_snd, comp_zero, kernel.condition]
  inv_hom_id := by
    refine (cancel_mono (kernel.ι f)).1 ?_
    rw [Category.assoc, kernel.lift_ι, Category.id_comp, ← Category.assoc, kernel.lift_ι,
      sq.lift_fst]

end CategoryTheory.IsPullback

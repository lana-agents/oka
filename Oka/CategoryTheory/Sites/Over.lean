/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Over

/-!
# The iterated slice equivalence preserves covers

Material for `Mathlib/CategoryTheory/Sites/Over.lean`; see `README.md` on the mirror tree. This
file imports its target and nothing else, so upstreaming it adds nothing to that file's transitive
imports.

For `Y : Over X`, `CategoryTheory.Over.iteratedSliceEquiv` identifies `Over Y` with `Over Y.left`.
Both of its functors are cocontinuous for the sliced topologies, because an equivalence is; what
is recorded here is that they are **cover-preserving**, and hence that `CategoryTheory.Over.post`
along either of them is *continuous* for the twice-sliced topologies. Continuity of that functor
is the hypothesis under which a sheaf on the one slice may be read as a sheaf on the other, and it
is what `Oka/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`'s
`SheafOfModules.overOverEquivalence` consumes.

Neither cover-preservation lemma is proved directly. Mathlib's
`CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving` turns cocontinuity of one adjoint
into cover preservation of the other, and an equivalence supplies both adjunctions, so the two
lemmas are each other's mirror image with the roles of the two functors exchanged. The two
instances then follow from `CategoryTheory.CoverPreserving.overPost` and
`CategoryTheory.Functor.isContinuous_of_coverPreserving`; the representable flatness that
`CategoryTheory.compatiblePreservingOfFlat` asks for is left to instance search.

## Main results

- `CategoryTheory.coverPreserving_iteratedSliceForward` and
  `CategoryTheory.coverPreserving_iteratedSliceBackward`, and the two
  `CategoryTheory.Functor.IsContinuous` instances for `CategoryTheory.Over.post` that they give.
  The instances are anonymous, and neither they nor the two lemmas carry docstrings of their own.
-/

@[expose] public section

universe v' u'

namespace CategoryTheory

open Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

lemma coverPreserving_iteratedSliceForward {X : C} (Y : Over X) :
    CoverPreserving ((J.over X).over Y) (J.over Y.left) Y.iteratedSliceForward :=
  (Y.iteratedSliceEquiv.symm.toAdjunction.isCocontinuous_iff_coverPreserving
    (J := J.over Y.left) (K := (J.over X).over Y)).mp
    (inferInstanceAs (Y.iteratedSliceBackward.IsCocontinuous _ _))

lemma coverPreserving_iteratedSliceBackward {X : C} (Y : Over X) :
    CoverPreserving (J.over Y.left) ((J.over X).over Y) Y.iteratedSliceBackward :=
  (Y.iteratedSliceEquiv.toAdjunction.isCocontinuous_iff_coverPreserving
    (J := (J.over X).over Y) (K := J.over Y.left)).mp
    (inferInstanceAs (Y.iteratedSliceForward.IsCocontinuous _ _))

instance {X : C} (Y : Over X) (W : Over Y) :
    (Over.post Y.iteratedSliceEquiv.functor).IsContinuous (((J.over X).over Y).over W)
      ((J.over Y.left).over (Y.iteratedSliceEquiv.functor.obj W)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((coverPreserving_iteratedSliceForward (J := J) Y).overPost W)

instance {X : C} (Y : Over X) (W : Over Y.left) :
    (Over.post Y.iteratedSliceEquiv.inverse).IsContinuous ((J.over Y.left).over W)
      (((J.over X).over Y).over (Y.iteratedSliceEquiv.inverse.obj W)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((coverPreserving_iteratedSliceBackward (J := J) Y).overPost W)

end CategoryTheory

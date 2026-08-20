/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Missing general lemmas on the `Γ`-`Spec` adjunction

Material for `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`; see `README.md` on the mirror
tree. Nothing here is complex-analytic.

Mathlib packages the naturality of `AlgebraicGeometry.LocallyRingedSpace.toΓSpec` inside the
natural transformation `AlgebraicGeometry.identityToΓSpec`, whose components are the `toΓSpec`
maps. Reading naturality off it means unfolding `Γ.rightOp` and `Spec.toLocallyRingedSpace`,
which is exactly the step a caller does not want to repeat, so the square is restated here in
the vocabulary of `toΓSpec` and `Spec.locallyRingedSpaceMap`.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.toΓSpec_naturality`: the canonical map to the spectrum
  of the global sections is natural.
-/

open CategoryTheory Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

universe u

/-- **The canonical map to the spectrum of the global sections is natural.**

This is `AlgebraicGeometry.identityToΓSpec.naturality` with both functors evaluated, so that the
statement mentions only `toΓSpec` and `Spec.locallyRingedSpaceMap`. The two sides are
definitionally equal to the components of that naturality square; nothing is proved here beyond
the change of spelling. -/
theorem toΓSpec_naturality {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f ≫ Y.toΓSpec = X.toΓSpec ≫ Spec.locallyRingedSpaceMap (Γ.map f.op) :=
  identityToΓSpec.naturality f

end AlgebraicGeometry.LocallyRingedSpace

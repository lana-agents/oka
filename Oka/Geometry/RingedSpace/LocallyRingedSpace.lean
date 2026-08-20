/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Missing general lemmas on locally ringed spaces

Material for `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean`; see `README.md` on the
mirror tree.

`homeoOfIso` is the exact analogue for `LocallyRingedSpace` of `AlgebraicGeometry.Scheme.homeoOfIso`
(`Mathlib/AlgebraicGeometry/Scheme.lean`), which exists only for schemes.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`: the underlying homeomorphism of an
  isomorphism of locally ringed spaces.
- `AlgebraicGeometry.LocallyRingedSpace.resAlgMap`: an algebra structure on the structure sheaf,
  recorded as a ring homomorphism into the global sections, restricted to an open subspace.
-/

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

/-- The underlying homeomorphism of an isomorphism of locally ringed spaces. -/
noncomputable def homeoOfIso (e : X ≅ Y) : X ≃ₜ Y :=
  TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso e)

@[simp]
lemma homeoOfIso_apply (e : X ≅ Y) (x : X) : homeoOfIso e x = e.hom.base x :=
  rfl

/-- An `R`-algebra structure on the structure sheaf of a locally ringed space is recorded as a
ring homomorphism `α : R →+* Γ(X, 𝒪_X)` into the global sections; the ring of sections over
every open subset then becomes an `R`-algebra via restriction. In particular `α` induces an
`R`-algebra structure on every open subspace of `X`, which this definition provides. -/
noncomputable def resAlgMap {R : Type*} [NonAssocSemiring R] (X : LocallyRingedSpace.{u})
    (α : R →+* X.presheaf.obj (op ⊤)) (U : Opens X) :
    R →+* (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp α

end AlgebraicGeometry.LocallyRingedSpace

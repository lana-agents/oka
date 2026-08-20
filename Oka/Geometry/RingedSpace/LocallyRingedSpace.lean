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
- `AlgebraicGeometry.LocallyRingedSpace.stalkAlgMap`: the same algebra structure, taken at a
  stalk.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap`: the identification of
  the stalks of an open subspace with the stalks of the ambient space is compatible with the
  algebra structures.
- `AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply`: contravariant functoriality of the
  global sections, in applied form.
-/

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

/-- **Contravariant functoriality of the global sections, applied to an element.**

`Γ.map_comp` is a statement about morphisms of `CommRingCat`; this is the form a computation of
the pullback of a global section along a composite actually needs. -/
lemma Γ_map_comp_apply {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : Z.presheaf.obj (op ⊤)) :
    (Γ.map (f ≫ g).op).hom a = (Γ.map f.op).hom ((Γ.map g.op).hom a) := by
  rw [op_comp, Functor.map_comp]
  rfl

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

/-- The `R`-algebra structure a ring homomorphism `α : R →+* Γ(X, 𝒪_X)` induces on the stalk at
a point: the germ there of the constant sections. -/
noncomputable def stalkAlgMap {R : Type*} [NonAssocSemiring R] (X : LocallyRingedSpace.{u})
    (α : R →+* X.presheaf.obj (op ⊤)) (x : X) : R →+* X.presheaf.stalk x :=
  (X.presheaf.Γgerm x).hom.comp α

/-- `stalkAlgMap` unfolded: the constant `c` becomes the germ at `x` of the global section
`α c`. -/
lemma stalkAlgMap_apply {R : Type*} [NonAssocSemiring R] (X : LocallyRingedSpace.{u})
    (α : R →+* X.presheaf.obj (op ⊤)) (x : X) (c : R) :
    X.stalkAlgMap α x c = X.presheaf.germ ⊤ x trivial (α c) :=
  rfl

/-- **The stalks of an open subspace are the stalks of the ambient space, compatibly with the
algebra structures**: the germ at `x` of the constant section `c` on `U` is its germ on `X`. -/
lemma restrictStalkIso_hom_stalkAlgMap {R : Type*} [NonAssocSemiring R]
    (X : LocallyRingedSpace.{u}) (α : R →+* X.presheaf.obj (op ⊤)) (U : Opens X)
    (x : X.restrict U.isOpenEmbedding) (c : R) :
    (X.restrictStalkIso U.isOpenEmbedding x).hom
        ((X.restrict U.isOpenEmbedding).stalkAlgMap (X.resAlgMap α U) x c) =
      X.stalkAlgMap α x.1 c := by
  change (X.restrictStalkIso U.isOpenEmbedding x).hom
      ((X.restrict U.isOpenEmbedding).presheaf.germ ⊤ x trivial
        ((X.presheaf.map (homOfLE le_top).op).hom (α c))) = _
  rw [restrictStalkIso_hom_eq_germ_apply]
  exact X.presheaf.germ_res_apply (homOfLE le_top) x.1 _ (α c)

end AlgebraicGeometry.LocallyRingedSpace

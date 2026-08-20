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
- `AlgebraicGeometry.LocallyRingedSpace.Γ_map_id_apply`: its identity companion, which is what
  collapses a pair of mutually inverse morphisms in such a computation.
- `AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply` and
  `AlgebraicGeometry.LocallyRingedSpace.Γ_map_hom_inv_apply`: **crossing an isomorphism of
  locally ringed spaces in both directions is the identity on global sections**, proved without
  computing either direction.
- `AlgebraicGeometry.LocallyRingedSpace.hom_stalk_ext`: two morphisms with the same base map and
  the same maps on stalks are equal.
- `AlgebraicGeometry.LocallyRingedSpace.Γgerm_Γ_map`: the germ of the pullback of a global
  section is the image of its germ under the stalk map.
- `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`: the image of an open subspace
  inclusion is that open subset.
- `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict_comp`: the image of the composite of two
  open subspace inclusions.
- `AlgebraicGeometry.LocallyRingedSpace.hom_ext_of_isEmpty`: any two morphisms out of a locally
  ringed space with no points are equal.
- `AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict_of_isEmpty`: its specialisation to the
  restriction to an open subset with no points, which is the form callers meet.
- `AlgebraicGeometry.LocallyRingedSpace.Γ_map_ofRestrict_apply`: pulling a global section back
  along the inclusion of an open subspace is restricting it.
- `AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover`: **two global sections which agree
  on every member of an open cover are equal.**
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

/-- **The identity acts as the identity on global sections**, in applied form.

The companion of `AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply`: together they are what
turns `e.inv ≫ e.hom = 𝟙` into a statement about a section, which is how one crosses an
isomorphism of locally ringed spaces without computing either of its two maps on sections. -/
lemma Γ_map_id_apply (X : LocallyRingedSpace.{u}) (a : X.presheaf.obj (op ⊤)) :
    (Γ.map (𝟙 X).op).hom a = a := by
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **Crossing an isomorphism of locally ringed spaces in both directions is the identity on
global sections** — proved without computing either direction.

Neither `Γ.map e.hom.op` nor `Γ.map e.inv.op` need be computable; in the case this was
extracted from — `e := X.restrictTopIso`, crossing between `X` and `X|⊤` — `Γ.map e.inv.op` is
an `eqToHom` between two *different* types of global-section ring, so no equation naming it
typechecks at all. **The technique is never to name it**: write the section as a pullback along
the direction that *is* a `rfl`, then collapse the resulting pair with this lemma, whose whole
proof is `Iso.inv_hom_id` read through
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_comp_apply`.

For `restrictTopIso` the direction that is a `rfl` is `hom`, and it is a `rfl` for *every*
section — `X|⊤` has the same presheaf as `X` on the nose — so the technique always applies
there. `OkaTest/Factorisation.lean` carries it out at `ℂ²`, and `nodeSection_eq` there is the
`rfl` in question. -/
lemma Γ_map_inv_hom_apply (e : X ≅ Y) (a : Y.presheaf.obj (op ⊤)) :
    (Γ.map e.inv.op).hom ((Γ.map e.hom.op).hom a) = a :=
  (Γ_map_comp_apply e.inv e.hom a).symm.trans
    ((congrArg (fun m : Y ⟶ Y ↦ (Γ.map m.op).hom a) e.inv_hom_id).trans (Γ_map_id_apply Y a))

/-- The companion of `AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply`, crossing in the
other order. Same proof with `Iso.hom_inv_id` in place of `Iso.inv_hom_id`. -/
lemma Γ_map_hom_inv_apply (e : X ≅ Y) (a : X.presheaf.obj (op ⊤)) :
    (Γ.map e.hom.op).hom ((Γ.map e.inv.op).hom a) = a :=
  (Γ_map_comp_apply e.hom e.inv a).symm.trans
    ((congrArg (fun m : X ⟶ X ↦ (Γ.map m.op).hom a) e.hom_inv_id).trans (Γ_map_id_apply X a))

/-- **Two morphisms of locally ringed spaces with the same base map and the same maps on stalks
are equal.**

`AlgebraicGeometry.SheafedSpace.hom_stalk_ext` reflected along
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace`, which is faithful. Mathlib has the
`SheafedSpace` statement and the `Scheme` one but not this one.

The `TopCat.Presheaf.stalkCongr` in the hypothesis is unavoidable: the two stalk maps have
sources `Y.presheaf.stalk (f.base x)` and `Y.presheaf.stalk (g.base x)`, which are equal only
propositionally. `TopCat.Presheaf.stalkCongr_hom_germ` is what evaluates it on a germ. -/
lemma hom_stalk_ext (f g : X ⟶ Y) (h : f.base = g.base)
    (h' : ∀ x, f.stalkMap x = (Y.presheaf.stalkCongr (h ▸ rfl)).hom ≫ g.stalkMap x) :
    f = g :=
  forgetToSheafedSpace.map_injective (SheafedSpace.hom_stalk_ext _ _ h h')

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

/-- **The germ of the pullback of a global section is the image of its germ under the stalk
map.**

This is `AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply` specialised to `U = ⊤` and
read from right to left, which is the direction a computation with `Γ.map` wants. The
specialisation costs nothing because `(Opens.map φ.base).obj ⊤` and `⊤` are definitionally
equal, and so are `φ.c.app (op ⊤)` and `Γ.map φ.op`. -/
lemma Γgerm_Γ_map (φ : X ⟶ Y) (a : Y.presheaf.obj (op ⊤)) (x : X) :
    X.presheaf.Γgerm x ((Γ.map φ.op).hom a) = (φ.stalkMap x).hom (Y.presheaf.Γgerm (φ.base x) a) :=
  (stalkMap_germ_apply φ ⊤ x trivial a).symm

/-- **The image of an open subspace inclusion is that open subset.**

It lives here, next to the composite version below, rather than in
`Oka/Geometry/RingedSpace/OpenImmersion.lean` where `restrictLE` consumes it: nothing about it
needs open-immersion theory, and `LocallyRingedSpace.ofRestrict` — the thing it is about — is
mirrored from the Mathlib file this one mirrors. -/
theorem range_ofRestrict (X : LocallyRingedSpace.{u}) (V : Opens X) :
    Set.range (X.ofRestrict V.isOpenEmbedding).base = (V : Set X) :=
  Subtype.range_val

/-- **The image of the composite of two open subspace inclusions** `X|S|T ⟶ X|S ⟶ X` is the
image of `T` under the inclusion of `S`.

The point of stating it this way rather than as `S ⊓ T'` for `T` the preimage of some `T'` is
that `T` is an arbitrary open of `X|S`, which is the shape a chart of a restricted analytic
space arrives in. -/
lemma range_ofRestrict_comp (A : LocallyRingedSpace.{u}) (S : Opens A)
    (T : Opens (A.restrict S.isOpenEmbedding)) :
    Set.range (((A.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding ≫
        A.ofRestrict S.isOpenEmbedding).base) =
      ((S.isOpenEmbedding.isOpenMap.functor.obj T : Opens A) : Set A) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, w.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- **Any two morphisms out of a locally ringed space with no points are equal.**

There are no points, so the base maps agree and `hom_stalk_ext`'s remaining obligation is
vacuous. `hom_ext_restrict_of_isEmpty` below is the specialisation callers actually meet, but
this is the statement the proof makes: `restrict` plays no part in it.

Beyond generality for its own sake, it is the form needed to discharge the compatibility
hypothesis of `AlgebraicGeometry.LocallyRingedSpace.OpenCover.existsUnique_glueMorphisms`, which
is an equation of morphisms out of the *categorical pullback* — a space that is not a `restrict`
of anything and whose emptiness is what
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_to_base_of_left` computes.

The hypothesis is explicit rather than an `[IsEmpty X]` instance because the carrier of
`X.restrict V` for an empty `V` is not something instance search finds, so the wrapper below
would have to build the term regardless. -/
theorem hom_ext_of_isEmpty {X Y : LocallyRingedSpace.{u}} (hX : IsEmpty X) (f g : X ⟶ Y) :
    f = g :=
  hom_stalk_ext f g (ConcreteCategory.hom_ext _ _ fun x ↦ (hX.elim x)) fun x ↦ (hX.elim x)

/-- **Any two morphisms out of the restriction to an empty open subset are equal.**

This is what makes a compatibility condition on a *disjoint* pair of members of an open cover
free — see `existsUnique_glueMorphisms_of_opens` in
`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`. Stated with the carrier being empty
rather than with `V = ⊥` so that no transport along an equation of opens is needed; that, and
not the emptiness argument, is the whole reason it exists beside `hom_ext_of_isEmpty`. -/
theorem hom_ext_restrict_of_isEmpty {V : Opens X} (hV : (V : Set X) = ∅)
    (f g : X.restrict V.isOpenEmbedding ⟶ Y) : f = g :=
  hom_ext_of_isEmpty (X := X.restrict V.isOpenEmbedding)
    ⟨fun x ↦ Set.eq_empty_iff_forall_notMem.1 hV x.1 x.2⟩ f g

/-- **Pulling a global section back along the inclusion of an open subspace is restricting
it.**

Both sides are the map `𝒪_X(⊤) ⟶ 𝒪_X(U)` and `Opens X` is a preorder category, so there is only
one such map; the proof is the same `change`/`congr` as
`ComplexAnalytic.isCLinearHom_ofRestrict`. The open indexing the right-hand side is
`U.isOpenEmbedding.isOpenMap.functor.obj ⊤` rather than `U`, because that is how the global
sections of `X|U` are indexed — the two have the same points and are not definitionally
equal. -/
lemma Γ_map_ofRestrict_apply (X : LocallyRingedSpace.{u}) (U : Opens X)
    (s : X.presheaf.obj (op ⊤)) :
    (Γ.map (X.ofRestrict U.isOpenEmbedding).op).hom s =
      (X.presheaf.map (homOfLE (le_top :
        U.isOpenEmbedding.isOpenMap.functor.obj ⊤ ≤ ⊤)).op).hom s := by
  change ((X.ofRestrict U.isOpenEmbedding).c.app (op ⊤)).hom s = _
  change (X.presheaf.map _).hom s = (X.presheaf.map _).hom s
  congr 2

/-- **The germ on `X|U` of the restriction of a global section is its germ on `X`**, across the
identification of the stalks of an open subspace with the stalks of the ambient space.

This is `restrictStalkIso_hom_stalkAlgMap` with an arbitrary global section in place of a
constant, and it is proved the same way. -/
lemma germ_Γ_map_ofRestrict (X : LocallyRingedSpace.{u}) (U : Opens X)
    (s : X.presheaf.obj (op ⊤)) (x : X.restrict U.isOpenEmbedding) :
    (X.restrictStalkIso U.isOpenEmbedding x).hom
        ((X.restrict U.isOpenEmbedding).presheaf.germ ⊤ x trivial
          ((Γ.map (X.ofRestrict U.isOpenEmbedding).op).hom s)) =
      X.presheaf.germ ⊤ x.1 trivial s := by
  rw [Γ_map_ofRestrict_apply, restrictStalkIso_hom_eq_germ_apply]
  exact X.presheaf.germ_res_apply (homOfLE le_top) x.1 _ s

/-- **Two global sections which agree on every member of an open cover are equal.**

The structure sheaf is a sheaf, so `TopCat.Presheaf.section_ext` reduces this to an equality of
germs, and `germ_Γ_map_ofRestrict` reads the germ of a restricted section off the germ of the
section. The cover is given as a family of opens together with the statement that every point
lies in one of them, which is the shape `existsUnique_glueMorphisms_of_opens` takes and so the
shape a caller already has.

Stated with the restrictions spelled as `Γ.map (X.ofRestrict _).op` rather than as
`X.presheaf.map`, because that is the spelling in which a morphism out of `X|U` produces
them. -/
theorem section_ext_of_cover (X : LocallyRingedSpace.{u}) {ι : Type*} (U : ι → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (s t : X.presheaf.obj (op ⊤))
    (h : ∀ i, (Γ.map (X.ofRestrict (U i).isOpenEmbedding).op).hom s =
      (Γ.map (X.ofRestrict (U i).isOpenEmbedding).op).hom t) :
    s = t := by
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ s t fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := hU x
  have key := congrArg (fun a ↦ (X.restrictStalkIso (U i).isOpenEmbedding
      (⟨x, hi⟩ : X.restrict (U i).isOpenEmbedding)).hom
    ((X.restrict (U i).isOpenEmbedding).presheaf.germ ⊤ ⟨x, hi⟩ trivial a)) (h i)
  exact (X.germ_Γ_map_ofRestrict (U i) s ⟨x, hi⟩).symm.trans
    (key.trans (X.germ_Γ_map_ofRestrict (U i) t ⟨x, hi⟩))

end AlgebraicGeometry.LocallyRingedSpace

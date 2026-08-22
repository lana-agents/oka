/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Oka.Topology.Sheaves.Stalks

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
- `AlgebraicGeometry.LocallyRingedSpace.toRestrictΓ`: **a section over `U`, as a global section
  of `X|U`.** The global sections of `X|U` are indexed by `U.functor.obj ⊤` rather than by `U`,
  so this is a restriction map and not a coercion; it is the spelling every statement below
  about sections on an open subspace is phrased in.
- `AlgebraicGeometry.LocallyRingedSpace.glueSection`: the global section a compatible family
  over an open cover glues to.
- `AlgebraicGeometry.LocallyRingedSpace.glueAlgMap`: **an algebra structure on `𝒪_X` glued from
  compatible algebra structures over an open cover.** The converse of `resAlgMap`, and unlike it
  a genuine gluing, because an algebra structure is a map into *global* sections.

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
- `AlgebraicGeometry.LocallyRingedSpace.resAlgMap_glueAlgMap`: restricting a glued algebra
  structure to a member of the cover returns the given one, across the
  `functor.obj ⊤`-versus-`U` seam.
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
- `AlgebraicGeometry.LocallyRingedSpace.germ_eq_stalkMap_ofRestrict`: **a germ on an open
  subspace is the image of a germ upstairs** under the stalk map of the inclusion. This is what
  makes a section of `𝒪_{X|U}` computable from data on `X`, and every germ argument below runs
  through it.
- `AlgebraicGeometry.LocallyRingedSpace.Γ_map_over_ambient`: **pulling a section back along a
  morphism of open subspaces *over* `X` is restricting it.**
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

For `restrictTopIso` the direction to write the section along is `hom`, because
`Γ.map X.restrictTopIso.hom.op` is *definitionally the restriction map*
`X.presheaf.map (homOfLE le_top).op` from `⊤` to the image of `⊤`. It is therefore a `rfl`
for any section whose presentation does not mention the open it lives on — a polynomial, a
constant, a coordinate — but **not** for a section given abstractly: the two sides then have
different types, `Γ(X, ⊤)` and `Γ(X, functor.obj ⊤)`, which are not definitionally equal even
for `X = ℂ^n`. `OkaTest/Factorisation.lean` carries the technique out at `ℂ²`, where
`nodeSection_eq` is the `rfl` in question, and checks both halves of this paragraph beside
it. -/
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

/-! ### Sections over an open subset, as global sections of the open subspace

The three inequalities between opens that the section below runs on are all Mathlib's, and are
spelled inline at their call sites rather than restated here:

* `U.functor.obj ⊤ ≤ U` is `(TopologicalSpace.Opens.isOpenEmbedding_obj_top U).le`. The
  underlying **equation** `U.functor.obj ⊤ = U` is a Mathlib `@[simp]` lemma, so it is free; what
  is not free is *transporting* along it, which is why only the `≤` is ever used.
* `O₁ ≤ O₂ → U.functor.obj O₁ ≤ U.functor.obj O₂` is functoriality,
  `(U.isOpenEmbedding.isOpenMap.functor.map (homOfLE h)).le`.
* `O ≤ (Opens.map ι).obj (U.functor.obj O)` is the unit of `IsOpenMap.adjunction`,
  `(U.isOpenEmbedding.isOpenMap.adjunction.unit.app O).le`.
-/

/-- **A section over `U` as a global section of `X|U`.**

The global sections of `X|U` are indexed by `U.isOpenEmbedding.isOpenMap.functor.obj ⊤`, which
has the same points as `U` and is not definitionally equal to it, so the two rings are different
types and a section over `U` has to be *restricted* to become a global section of `X|U`. An
`abbrev`, so that a caller holding the restriction map recognises it without unfolding. -/
abbrev toRestrictΓ (X : LocallyRingedSpace.{u}) (U : Opens X) (u : X.presheaf.obj (op U)) :
    (X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤) :=
  (X.presheaf.map (homOfLE (Opens.isOpenEmbedding_obj_top U).le).op).hom u

/-- **A germ on an open subspace is the image of a germ upstairs**, under the stalk map of the
inclusion.

This is the one tool every germ computation about open subspaces in this file and in
`Oka/AnalyticSpace/Restrict.lean` runs through. Its point is that it needs **no equation of
opens**: `germ_res_apply` moves a germ across the unit of `IsOpenMap.adjunction`, and the
leftover restriction map
is the identity because `Opens X` is a preorder and there is only one morphism
`U.functor.obj O ⟶ U.functor.obj O`. -/
lemma germ_eq_stalkMap_ofRestrict (X : LocallyRingedSpace.{u}) (U : Opens X)
    (O : Opens (X.restrict U.isOpenEmbedding)) (w : X.restrict U.isOpenEmbedding) (hO : w ∈ O)
    (b : (X.restrict U.isOpenEmbedding).presheaf.obj (op O)) :
    (X.restrict U.isOpenEmbedding).presheaf.germ O w hO b =
      ((X.ofRestrict U.isOpenEmbedding).stalkMap w).hom
        (X.presheaf.germ (U.isOpenEmbedding.isOpenMap.functor.obj O) w.1 ⟨w, hO, rfl⟩ b) := by
  have hid : ∀ f : op (U.isOpenEmbedding.isOpenMap.functor.obj O) ⟶
      op (U.isOpenEmbedding.isOpenMap.functor.obj O), (X.presheaf.map f).hom b = b := by
    intro f
    rw [Subsingleton.elim f (𝟙 _)]
    exact (ConcreteCategory.congr_hom (X.presheaf.map_id
      (op (U.isOpenEmbedding.isOpenMap.functor.obj O))) b).trans (ConcreteCategory.id_apply _)
  refine Eq.trans ?_ (stalkMap_germ_apply (X.ofRestrict U.isOpenEmbedding)
    (U.isOpenEmbedding.isOpenMap.functor.obj O) w ⟨w, hO, rfl⟩ b).symm
  refine Eq.trans ?_ ((X.restrict U.isOpenEmbedding).presheaf.germ_res_apply
    (homOfLE (U.isOpenEmbedding.isOpenMap.adjunction.unit.app O).le) w hO _)
  refine congrArg ((X.restrict U.isOpenEmbedding).presheaf.germ O w hO) ?_
  change b = (X.presheaf.map _).hom ((X.presheaf.map _).hom b)
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  exact (hid _).symm

/-- `germ_eq_stalkMap_ofRestrict` at the top open, for a section written as a
`toRestrictΓ`. -/
lemma Γgerm_toRestrictΓ (X : LocallyRingedSpace.{u}) (U : Opens X)
    (u : X.presheaf.obj (op U)) (w : X.restrict U.isOpenEmbedding) :
    (X.restrict U.isOpenEmbedding).presheaf.Γgerm w (X.toRestrictΓ U u) =
      ((X.ofRestrict U.isOpenEmbedding).stalkMap w).hom (X.presheaf.germ U w.1 w.2 u) :=
  (X.germ_eq_stalkMap_ofRestrict U ⊤ w trivial _).trans
    (congrArg ((X.ofRestrict U.isOpenEmbedding).stalkMap w).hom
      (X.presheaf.germ_res_apply (homOfLE (Opens.isOpenEmbedding_obj_top U).le) w.1
        ⟨w, trivial, rfl⟩ u))

/-- Two restrictions composed is one restriction. The three inequalities are unrelated inputs:
`Opens X` is a preorder, so any two morphisms with the same source and target are equal. -/
lemma map_map_apply (X : LocallyRingedSpace.{u}) {O₁ O₂ O₃ : Opens X} (h₁ : O₁ ≤ O₂)
    (h₂ : O₂ ≤ O₃) (h₃ : O₁ ≤ O₃) (s : X.presheaf.obj (op O₃)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s) =
      (X.presheaf.map (homOfLE h₃).op).hom s := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  congr 2

/-- **Restriction on `X|U` is restriction on `X`**, between the corresponding opens. -/
lemma restrict_map_apply (X : LocallyRingedSpace.{u}) (U : Opens X)
    {O₁ O₂ : Opens (X.restrict U.isOpenEmbedding)} (h : O₁ ≤ O₂)
    (h' : U.isOpenEmbedding.isOpenMap.functor.obj O₁ ≤
      U.isOpenEmbedding.isOpenMap.functor.obj O₂)
    (s : (X.restrict U.isOpenEmbedding).presheaf.obj (op O₂)) :
    ((X.restrict U.isOpenEmbedding).presheaf.map (homOfLE h).op).hom s =
      (X.presheaf.map (homOfLE h').op).hom s := by
  change (X.presheaf.map _).hom s = _
  congr 2

/-- **Pulling a section back along a morphism of open subspaces over `X` restricts it.**

`α` is any morphism `X|W ⟶ X|U|T` commuting with the two inclusions into `X`; no assumption is
made about how it was built, and in the intended application it is an
`IsOpenImmersion.lift`, whose sheaf map is not otherwise computable. The proof is entirely on
stalks: `germ_eq_stalkMap_ofRestrict` twice, `stalkMap_congr_hom` against the factorisation, and
`stalkCongr_hom_germ` to move the germ to the point the factorisation names. -/
lemma Γ_map_over_ambient (X : LocallyRingedSpace.{u}) (S : Opens X)
    (T : Opens (X.restrict S.isOpenEmbedding)) (W : Opens X)
    (hW : W ≤ S.isOpenEmbedding.isOpenMap.functor.obj T)
    (α : X.restrict W.isOpenEmbedding ⟶
      (X.restrict S.isOpenEmbedding).restrict T.isOpenEmbedding)
    (hα : α ≫ ((X.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding ≫
      X.ofRestrict S.isOpenEmbedding) = X.ofRestrict W.isOpenEmbedding)
    (a : (X.restrict S.isOpenEmbedding).presheaf.obj (op T)) :
    (Γ.map α.op).hom ((X.restrict S.isOpenEmbedding).toRestrictΓ T a) =
      X.toRestrictΓ W ((X.presheaf.map (homOfLE hW).op).hom a) := by
  refine TopCat.Presheaf.section_ext (X.restrict W.isOpenEmbedding).sheaf ⊤ _ _ fun y _ ↦ ?_
  have hcomp : ((X.ofRestrict S.isOpenEmbedding).stalkMap
        (((X.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding).base (α.base y)) ≫
      ((X.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding).stalkMap (α.base y) ≫
        α.stalkMap y) =
      (X.presheaf.stalkCongr (Inseparable.of_eq
        (congrArg (fun m : X.restrict W.isOpenEmbedding ⟶ X ↦
          (ConcreteCategory.hom m.base) y) hα))).hom ≫
        (X.ofRestrict W.isOpenEmbedding).stalkMap y :=
    (congrArg (fun m ↦ (X.ofRestrict S.isOpenEmbedding).stalkMap
        (((X.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding).base (α.base y)) ≫ m)
      (stalkMap_comp α ((X.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding) y).symm).trans
      ((stalkMap_comp (α ≫ (X.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding)
          (X.ofRestrict S.isOpenEmbedding) y).symm.trans
        (stalkMap_congr_hom _ _ ((Category.assoc α
          ((X.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding)
          (X.ofRestrict S.isOpenEmbedding)).trans hα) y))
  refine Eq.trans (Γgerm_Γ_map α _ y) ?_
  refine Eq.trans (congrArg (fun b ↦ (α.stalkMap y).hom b)
    ((X.restrict S.isOpenEmbedding).Γgerm_toRestrictΓ T a (α.base y))) ?_
  refine Eq.trans (congrArg (fun b ↦ (α.stalkMap y).hom
      ((((X.restrict S.isOpenEmbedding).ofRestrict T.isOpenEmbedding).stalkMap (α.base y)).hom b))
    (X.germ_eq_stalkMap_ofRestrict S T (α.base y).1 (α.base y).2 a)) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _).symm ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ m.hom (X.presheaf.germ
      (S.isOpenEmbedding.isOpenMap.functor.obj T) _ ⟨(α.base y).1, (α.base y).2, rfl⟩ a)) hcomp) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg ((X.ofRestrict W.isOpenEmbedding).stalkMap y).hom
    (TopCat.Presheaf.stalkCongr_hom_germ X.presheaf _
      (S.isOpenEmbedding.isOpenMap.functor.obj T) _ (hW y.2) a)) ?_
  refine Eq.trans ?_ (X.Γgerm_toRestrictΓ W _ y).symm
  exact (congrArg ((X.ofRestrict W.isOpenEmbedding).stalkMap y).hom
    (X.presheaf.germ_res_apply (homOfLE hW) y.1 y.2 a)).symm

/-! ### Gluing an algebra structure over an open cover

`resAlgMap` restricts an algebra structure from a space to an open subspace. This section is the
converse, and the asymmetry between the two is the point: `resAlgMap` is a composition and costs
nothing, while going back is a **gluing** and needs the sheaf condition, because an algebra
structure is a map into *global* sections.

Everything here is `TopCat.Sheaf.existsUnique_gluing'` at `V = ⊤`. The only thing worth saying is
how the ring homomorphism is obtained: **not** by gluing a homomorphism, but by gluing the section
`α c` for each `c` separately and then reading the four ring axioms off the *uniqueness* half —
both sides of each axiom restrict to the same thing on every member of the cover, so they are
equal. Trying it the other way round means carrying the axioms through the gluing.

The opens are indexed as `U i` here rather than as `(U i).functor.obj ⊤`, which is the opposite of
the convention in the section above; `resAlgMap_glueAlgMap` is where the two meet, and it is the
only place in this section that has to cross that seam.
-/

variable {ι : Type*} {U : ι → Opens X}

/-- **A compatible family of sections over an open cover of `X` glues to a unique global
section.** `TopCat.Sheaf.existsUnique_gluing'` at `V = ⊤`. -/
theorem existsUnique_glueSection (hU : ⨆ i, U i = ⊤)
    (s : ∀ i, X.presheaf.obj (op (U i)))
    (h : TopCat.Presheaf.IsCompatible X.presheaf U s) :
    ∃! t : X.presheaf.obj (op ⊤),
      ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t = s i :=
  X.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) (le_of_eq hU.symm) s h

/-- The global section a compatible family glues to. -/
noncomputable def glueSection (hU : ⨆ i, U i = ⊤) (s : ∀ i, X.presheaf.obj (op (U i)))
    (h : TopCat.Presheaf.IsCompatible X.presheaf U s) : X.presheaf.obj (op ⊤) :=
  (existsUnique_glueSection hU s h).choose

@[simp]
lemma map_glueSection (hU : ⨆ i, U i = ⊤) (s : ∀ i, X.presheaf.obj (op (U i)))
    (h : TopCat.Presheaf.IsCompatible X.presheaf U s) (i : ι) :
    (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom (glueSection hU s h) = s i :=
  (existsUnique_glueSection hU s h).choose_spec.1 i

/-- **Anything restricting to the family on every member of the cover is the gluing.** This is
the uniqueness half, and it is what proves the ring axioms of `glueAlgMap` below. -/
lemma glueSection_eq (hU : ⨆ i, U i = ⊤) (s : ∀ i, X.presheaf.obj (op (U i)))
    (h : TopCat.Presheaf.IsCompatible X.presheaf U s) (t : X.presheaf.obj (op ⊤))
    (ht : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t = s i) :
    glueSection hU s h = t :=
  ((existsUnique_glueSection hU s h).choose_spec.2 t ht).symm

/-- **The restrictions of one global section to the members of a cover form a compatible
family.** Both sides of the compatibility condition are the restriction to `U i ⊓ U j`, and
`Opens X` is a preorder category, so there is only one such map. -/
lemma isCompatible_map_le_top (t : X.presheaf.obj (op ⊤)) :
    TopCat.Presheaf.IsCompatible X.presheaf U
      fun i ↦ (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t := fun i j ↦ by
  change ((X.presheaf.map _) ≫ (X.presheaf.map _)).hom t =
    ((X.presheaf.map _) ≫ (X.presheaf.map _)).hom t
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  congr 2

/-- **Gluing the restrictions of a global section returns that section.** The round trip, and
the cheapest witness that `glueSection` is not vacuous. -/
@[simp]
lemma glueSection_map_le_top (hU : ⨆ i, U i = ⊤) (t : X.presheaf.obj (op ⊤)) :
    glueSection hU _ (isCompatible_map_le_top t) = t :=
  glueSection_eq _ _ _ t fun _ ↦ rfl

/-- **Restricting in two steps.** `resAlgMap` restricts a global section all the way to
`U.functor.obj ⊤`; this factors that through the sections over `U`, which is the indexing a
family given on the members of a cover arrives in. -/
lemma resAlgMap_eq_comp {R : Type*} [NonAssocSemiring R] (α : R →+* X.presheaf.obj (op ⊤))
    (V : Opens X) :
    X.resAlgMap α V =
      (X.presheaf.map (homOfLE (Opens.isOpenEmbedding_obj_top V).le).op).hom.comp
        ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp α) :=
  RingHom.ext fun c ↦ by
    change (X.presheaf.map _).hom _ = (X.presheaf.map _).hom ((X.presheaf.map _).hom (α c))
    change _ = ((X.presheaf.map _) ≫ (X.presheaf.map _)).hom _
    rw [← X.presheaf.map_comp]
    congr 2

section GlueAlgMap

variable {R : Type*} [CommRing R] (hU : ⨆ i, U i = ⊤) (α : ∀ i, R →+* X.presheaf.obj (op (U i)))
  (h : ∀ c : R, TopCat.Presheaf.IsCompatible X.presheaf U fun i ↦ α i c)

/-- **An algebra structure on `𝒪_X` glued from compatible algebra structures over an open
cover.**

The underlying function sends `c` to the gluing of the family `α i c`; each of the four ring
axioms is an instance of `glueSection_eq`, because both sides restrict to the same section on
every member of the cover. -/
noncomputable def glueAlgMap : R →+* X.presheaf.obj (op ⊤) where
  toFun c := glueSection hU (fun i ↦ α i c) (h c)
  map_one' := glueSection_eq _ _ _ 1 fun i ↦ (map_one _).trans (map_one (α i)).symm
  map_mul' a b := glueSection_eq _ _ _ _ fun i ↦ (map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (map_glueSection hU _ (h a) i)
      (map_glueSection hU _ (h b) i)).trans (map_mul (α i) a b).symm)
  map_zero' := glueSection_eq _ _ _ 0 fun i ↦ (map_zero _).trans (map_zero (α i)).symm
  map_add' a b := glueSection_eq _ _ _ _ fun i ↦ (map_add _ _ _).trans
    ((congrArg₂ (· + ·) (map_glueSection hU _ (h a) i)
      (map_glueSection hU _ (h b) i)).trans (map_add (α i) a b).symm)

@[simp]
lemma map_glueAlgMap (i : ι) (c : R) :
    (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom (glueAlgMap hU α h c) = α i c :=
  map_glueSection hU (fun i ↦ α i c) (h c) i

/-- **Restricting the glued algebra structure to a member of the cover returns the given one**,
across the `functor.obj ⊤`-versus-`U i` seam.

`resAlgMap` lands in `Γ(X|U i)`, indexed by `(U i).functor.obj ⊤`; the family `α` is indexed by
`U i`. The two are not definitionally equal, so the statement cannot be `= α i` and the
right-hand side has to carry the restriction `Γ(X, U i) ⟶ Γ(X, (U i).functor.obj ⊤)`. This is the
same map `toRestrictΓ` is, and this lemma is what lets a caller feed a family of algebra
structures on the members of a cover to `ComplexAnalytic.AnalyticSpace.ofOpens`. -/
lemma resAlgMap_glueAlgMap (i : ι) :
    X.resAlgMap (glueAlgMap hU α h) (U i) =
      (X.presheaf.map (homOfLE (Opens.isOpenEmbedding_obj_top (U i)).le).op).hom.comp (α i) :=
  RingHom.ext fun c ↦ by
    change (X.presheaf.map _).hom _ = (X.presheaf.map _).hom ((α i) c)
    rw [← map_glueAlgMap hU α h i c]
    change _ = ((X.presheaf.map _) ≫ (X.presheaf.map _)).hom _
    rw [← X.presheaf.map_comp]
    congr 2

end GlueAlgMap

end AlgebraicGeometry.LocallyRingedSpace

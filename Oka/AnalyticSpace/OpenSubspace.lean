/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.LocalModel
import Oka.AnalyticSpace.Restrict
import Oka.Geometry.RingedSpace.OpenImmersion

/-!
# An open subspace of a complex analytic space is a complex analytic space

`ComplexAnalytic.AnalyticSpace.restrict X U` is the open subspace of `X` on an open subset `U`:
the locally ringed space `X|U`, with the `ℂ`-algebra structure obtained by restricting sections,
and — which is the content — a chart at every one of its points.
`ComplexAnalytic.AnalyticSpace.ofRestrict` is its inclusion into `X`, as a morphism of complex
analytic spaces.

Until this file there was no `AnalyticSpace.restrict`: `LocallyRingedSpace.restrict` appeared
only *inside* the statement of what a chart is, never as a construction producing an analytic
space. (Checked by grep against `85b9251`: the only occurrence of the name was in
`Oka/AnalyticSpace/Restrict.lean`'s docstring, saying it was missing.)

## Why it is not immediate

A chart of `X` at a point of `U` is a closed immersion `i : X|U₀ ⟶ ℂ^n|V` for some open
neighbourhood `U₀` of that point in `X`. What `AnalyticSpace.local_model` wants for `X|U` is a
chart on an open neighbourhood **inside `U`**, and its target must again be `ℂ^n` restricted to
an open subset **of `ℂ^n`**. Three things have to happen.

* **The chart must be shrunk to the overlap.** `i` is a closed embedding, hence an embedding, so
  the preimage of `U` in `X|U₀` is the preimage of some open `V'` of `ℂ^n|V`
  (`IsInducing.isOpen_iff`) — and `ComplexAnalytic.IsCutOutBy.restrictOpen` then cuts out the
  overlap inside `ℂ^n|V|V'` by the restricted family. **`V'` is obtained rather than
  constructed**: the topological input is that an embedding's opens all come from the target.
* **The source has to be recognised as an open subspace of `X|U` rather than of `X|U₀`.** Both
  `X|U|W` and `X|U₀|W₀` are open immersions into `X` with the same image — the overlap — so
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` identifies them. No
  `restrictRestrict` is needed.
* **The target has to be flattened.** `ℂ^n|V|V'` and `ℂ^n|V''`, for `V''` the image of `V'` in
  `ℂ^n`, are again two open immersions into `ℂ^n` with the same image, so the same lemma
  applies; and `ComplexAnalytic.IsCutOutBy.iso_comp` transports the cut-out along it.

The `ℂ`-linearity of both identifications is `ComplexAnalytic.IsCLinearHom.of_comp`: each is a
morphism *over* the ambient space, and every algebra structure in sight is the ambient one
restricted, so linearity is contravariant functoriality of `Γ` applied to the factorisation. No
transport of algebra structures along an isomorphism is needed anywhere.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.restrict`: **an open subspace of a complex analytic space is a
  complex analytic space.**
- `ComplexAnalytic.AnalyticSpace.ofRestrict`: its inclusion, as a morphism of complex analytic
  spaces.
- `ComplexAnalytic.AnalyticSpace.restrictLE`: the inclusion of a smaller open subspace into a
  larger one, as a morphism of complex analytic spaces.
- `ComplexAnalytic.AnalyticSpace.liftRestrict`: **a morphism whose image lies in an open subspace
  factors through it**, as a morphism of complex analytic spaces. This is what builds a morphism
  whose *target* is an open subspace; `restrictLE` is its special case at an inclusion.
- `ComplexAnalytic.AnalyticSpace.restrictHom`: **a morphism restricted to the preimage of an open
  subset of the target**, as a morphism of complex analytic spaces. This is the other way to land
  in an open subspace, and it asks nothing of the image: `liftRestrict` keeps the source and needs
  the image to lie in `V`, this shrinks the source to the preimage of `V` instead.
- `ComplexAnalytic.AnalyticSpace.resΓ`: the restriction of a global section of `𝒪_X` to an open
  subspace.

## Main results

- `ComplexAnalytic.exists_local_model_restrict`: the chart of `X|U` at a point, which is the
  `local_model` field of `AnalyticSpace.restrict`.
- `ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`: **the inclusion of an open subspace
  is an isomorphism on stalks**, at the spelling a caller of `ofRestrict` holds. Mathlib has the
  statement; what this adds is a discrimination-tree key, exactly as
  `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict` does one field further in.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

open AlgebraicGeometry.LocallyRingedSpace in
/-- **An open subspace of a complex analytic space has a chart at every point**, which is the
`local_model` field of `ComplexAnalytic.AnalyticSpace.restrict`. See the module docstring for
the three steps. -/
theorem exists_local_model_restrict (X : AnalyticSpace.{u}) (U : X.Opens)
    (x : X.toLocallyRingedSpace.restrict U.isOpenEmbedding) :
    ∃ (W : OpenNhds x) (n k : ℕ) (V : Opens (complexAffineSpace.{u} n))
      (c : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).restrict W.1.isOpenEmbedding ⟶
        (complexAffineSpace.{u} n).restrict V.isOpenEmbedding)
      (f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)),
      IsCutOutBy c f ∧
        IsCLinearHom c
          ((X.toLocallyRingedSpace.restrict U.isOpenEmbedding).resAlgMap
            (X.toLocallyRingedSpace.resAlgMap X.algebraMap U) W.1)
          (constantsAlgMap n V) := by
  obtain ⟨U₀, n, k, V, i, f, hcut, hlin⟩ := X.local_model x.1
  set ιU := X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding with hιU
  set ι₀ := X.toLocallyRingedSpace.ofRestrict U₀.1.isOpenEmbedding with hι₀
  -- `i` is an embedding, so the preimage of `U` in `X|U₀` comes from an open of `ℂ^n|V`.
  obtain ⟨t, ht, htpre⟩ := hcut.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.1
    ((Opens.map ι₀.base).obj U).2
  set V' : Opens ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding) := ⟨t, ht⟩ with hV'
  set W₀ : Opens (X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) :=
    (Opens.map i.base).obj V' with hW₀
  have hW₀eq : W₀ = (Opens.map ι₀.base).obj U := Opens.ext htpre
  set W : Opens (X.toLocallyRingedSpace.restrict U.isOpenEmbedding) :=
    (Opens.map ιU.base).obj U₀.1 with hW
  have hxW : x ∈ W := U₀.2
  -- `X|U|W` and `X|U₀|W₀` are open immersions into `X` with the same image.
  have hrange : Set.range (((X.toLocallyRingedSpace.restrict U.isOpenEmbedding).ofRestrict
        W.isOpenEmbedding ≫ ιU).base) =
      Set.range (((X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).ofRestrict
        W₀.isOpenEmbedding ≫ ι₀).base) := by
    refine Eq.trans (range_ofRestrict_comp X.toLocallyRingedSpace U W) ?_
    refine Eq.trans ?_ (range_ofRestrict_comp X.toLocallyRingedSpace U₀.1 W₀).symm
    rw [hW₀eq]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y.1, hy⟩, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y.1, hy⟩, y.2, rfl⟩
  -- and so are `ℂ^n|V|V'` and `ℂ^n|V''`.
  set V'' : Opens (complexAffineSpace.{u} n) := V.isOpenEmbedding.isOpenMap.functor.obj V' with hV''
  have hrange₂ : Set.range ((((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).ofRestrict
        V'.isOpenEmbedding ≫ (complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).base) =
      Set.range (((complexAffineSpace.{u} n).ofRestrict V''.isOpenEmbedding).base) := by
    refine Eq.trans (range_ofRestrict_comp (complexAffineSpace.{u} n) V V') ?_
    exact (LocallyRingedSpace.range_ofRestrict (complexAffineSpace.{u} n) V'').symm
  set e₁ := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hrange with he₁def
  set e₂ := LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hrange₂ with he₂def
  have he₁ : IsCLinearHom e₁.hom
      ((X.toLocallyRingedSpace.restrict U.isOpenEmbedding).resAlgMap
        (X.toLocallyRingedSpace.resAlgMap X.algebraMap U) W)
      ((X.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).resAlgMap
        (X.toLocallyRingedSpace.resAlgMap X.algebraMap U₀.1) W₀) :=
    IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange)
      ((isCLinearHom_ofRestrict _ _ W).comp (isCLinearHom_ofRestrict X.toLocallyRingedSpace _ U))
      ((isCLinearHom_ofRestrict _ _ W₀).comp
        (isCLinearHom_ofRestrict X.toLocallyRingedSpace _ U₀.1))
  have he₂ : IsCLinearHom e₂.hom
      (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).resAlgMap
        (constantsAlgMap n V) V') (constantsAlgMap n V'') :=
    IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange₂)
      ((isCLinearHom_ofRestrict _ _ V').comp (isCLinearHom_ofRestrict_constants n V))
      (isCLinearHom_ofRestrict_constants n V'')
  exact ⟨⟨W, hxW⟩, n, k, V'', (e₁.hom ≫ restrictHom i V') ≫ e₂.hom,
    fun j ↦ (LocallyRingedSpace.Γ.map e₂.inv.op).hom (restrictSections V' f j),
    ((hcut.restrictOpen V').comp_iso e₁).iso_comp e₂,
    (he₁.comp (isCLinearHom_restrictHom hlin V')).comp he₂⟩

namespace AnalyticSpace

/-- **An open subspace of a complex analytic space is a complex analytic space.**

The underlying locally ringed space is `X|U` and the `ℂ`-algebra structure is the ambient one
restricted; the charts are `ComplexAnalytic.exists_local_model_restrict`. -/
def restrict (X : AnalyticSpace.{u}) (U : X.Opens) : AnalyticSpace.{u} where
  toLocallyRingedSpace := X.toLocallyRingedSpace.restrict U.isOpenEmbedding
  algebraMap := X.toLocallyRingedSpace.resAlgMap X.algebraMap U
  local_model := exists_local_model_restrict X U

/-- The underlying locally ringed space of an open subspace. Not a `simp` lemma: rewriting with
it inside the type of `base_ofRestrict` is what takes that lemma out of simp normal form. -/
lemma restrict_toLocallyRingedSpace (X : AnalyticSpace.{u}) (U : X.Opens) :
    (X.restrict U).toLocallyRingedSpace = X.toLocallyRingedSpace.restrict U.isOpenEmbedding :=
  rfl

/-- The `ℂ`-algebra structure of an open subspace. -/
lemma restrict_algebraMap (X : AnalyticSpace.{u}) (U : X.Opens) :
    (X.restrict U).algebraMap = X.toLocallyRingedSpace.resAlgMap X.algebraMap U :=
  rfl

/-- **The inclusion of an open subspace, as a morphism of complex analytic spaces.**

It is `ℂ`-linear because the algebra structure on the subspace was defined by restricting
sections, which is `ComplexAnalytic.isCLinearHom_ofRestrict`. -/
def ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) : X.restrict U ⟶ X :=
  ⟨X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding,
    isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap U⟩

@[simp]
lemma base_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) (x : X.restrict U) :
    (X.ofRestrict U).toLRSHom.base x = x.1 :=
  rfl

/-- **The inclusion of an open subspace is an isomorphism on stalks**, at the spelling a caller
who built the morphism with `ComplexAnalytic.AnalyticSpace.ofRestrict` actually holds.

Mathlib's `AlgebraicGeometry.LocallyRingedSpace.ofRestrict_stalkMap_isIso` is the same statement,
and it is **not** found here: the two terms are `rfl`-equal and headed by
`ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` and by
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict` respectively, so they are different
discrimination-tree keys. This is the same seam that
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict` exists for, one field further
in, and it is settled the same way — by naming the instance at the spelling that is used. -/
instance isIso_stalkMap_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) (x : X.restrict U) :
    IsIso ((X.ofRestrict U).toLRSHom.stalkMap x) :=
  inferInstanceAs (IsIso
    ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).stalkMap x))

/-- **The inclusion of a smaller open subspace into a larger one**, as a morphism of complex
analytic spaces.

The underlying morphism of locally ringed spaces is
`AlgebraicGeometry.LocallyRingedSpace.restrictLE`. It is `ℂ`-linear because it is a morphism
*over* `X` and both algebra structures are the ambient one restricted, which is exactly the
hypothesis of `ComplexAnalytic.IsCLinearHom.of_comp`; no transport of algebra structures along
anything is needed. -/
def restrictLE (X : AnalyticSpace.{u}) {V W : X.Opens} (h : V ≤ W) :
    X.restrict V ⟶ X.restrict W :=
  ⟨X.toLocallyRingedSpace.restrictLE h,
    IsCLinearHom.of_comp (LocallyRingedSpace.restrictLE_fac _ h)
      (isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap V)
      (isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap W)⟩

/-- The underlying morphism of locally ringed spaces of
`ComplexAnalytic.AnalyticSpace.restrictLE`. -/
lemma toLRSHom_restrictLE (X : AnalyticSpace.{u}) {V W : X.Opens} (h : V ≤ W) :
    (X.restrictLE h).toLRSHom = X.toLocallyRingedSpace.restrictLE h :=
  rfl

/-- **`ComplexAnalytic.AnalyticSpace.restrictLE` is a morphism over `X`.** This, rather than the
morphism itself, is what every use of it consumes. -/
lemma restrictLE_fac (X : AnalyticSpace.{u}) {V W : X.Opens} (h : V ≤ W) :
    X.restrictLE h ≫ X.ofRestrict W = X.ofRestrict V :=
  forgetToLocallyRingedSpace.map_injective (LocallyRingedSpace.restrictLE_fac _ h)

/-- **The restriction of a morphism to the preimage of an open subset of the target**, as a
morphism of complex analytic spaces.

`ComplexAnalytic.restrictHom` at the underlying morphisms, which is where every fact about it
lives — `ComplexAnalytic.base_restrictHom` for the underlying map,
`ComplexAnalytic.stalkMap_restrictHom_eq'` for the stalk map,
`ComplexAnalytic.isClosedEmbedding_base_restrictHom` and
`ComplexAnalytic.IsCutOutBy.restrictOpen` for what a chart keeps. It is `ℂ`-linear by
`ComplexAnalytic.isCLinearHom_restrictHom`, whose two algebra structures are the two
`ComplexAnalytic.AnalyticSpace.restrict` puts on the two open subspaces, so nothing is
transported.

Unlike `ComplexAnalytic.AnalyticSpace.liftRestrict` this does not ask the image of `A` to lie in
`V`: it shrinks the *source* to the preimage instead. Neither is a special case of the other.

**The name shadows `ComplexAnalytic.restrictHom` inside `namespace AnalyticSpace`**, which is
where most of this development is written. A use of the bare name there now means this one; the
locally-ringed-space one has to be written `ComplexAnalytic.restrictHom`, as it is at
`Oka/AnalyticSpace/HolomorphicMapGeneral.lean:351`. That is the price of the name matching the
one it wraps, and the mismatch is a type error rather than a silent change of meaning: the two
have different sources and targets. -/
def restrictHom {A B : AnalyticSpace.{u}} (f : A ⟶ B) (V : B.Opens) :
    A.restrict ((Opens.map f.toLRSHom.base).obj V) ⟶ B.restrict V :=
  ⟨ComplexAnalytic.restrictHom f.toLRSHom V, isCLinearHom_restrictHom f.isCLinear V⟩

/-- The underlying morphism of locally ringed spaces of
`ComplexAnalytic.AnalyticSpace.restrictHom`. -/
lemma toLRSHom_restrictHom {A B : AnalyticSpace.{u}} (f : A ⟶ B) (V : B.Opens) :
    (restrictHom f V).toLRSHom = ComplexAnalytic.restrictHom f.toLRSHom V :=
  rfl

/-- **`ComplexAnalytic.AnalyticSpace.restrictHom` is a morphism over `f`.** -/
lemma restrictHom_fac {A B : AnalyticSpace.{u}} (f : A ⟶ B) (V : B.Opens) :
    restrictHom f V ≫ B.ofRestrict V = A.ofRestrict ((Opens.map f.toLRSHom.base).obj V) ≫ f :=
  forgetToLocallyRingedSpace.map_injective (ComplexAnalytic.restrictHom_fac f.toLRSHom V)

/-- **The restriction of a global section of `𝒪_X` to an open subspace**, as a global section of
`𝒪_{X|U}`.

An `abbrev` rather than a `def`, so that a caller holding
`(LocallyRingedSpace.Γ.map (X.ofRestrict U).op).hom g` — which is how a computation with
`ComplexAnalytic.AnalyticSpace.coordPullback` produces it — does not have to unfold anything to
recognise it. -/
abbrev resΓ (X : AnalyticSpace.{u}) (U : X.Opens) (g : X.presheaf.obj (op ⊤)) :
    (X.restrict U).presheaf.obj (op ⊤) :=
  (LocallyRingedSpace.Γ.map (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).op).hom g

/-- **Restricting twice is restricting once.**

Spelled at the level of locally ringed spaces throughout — `Γ.map` of the underlying morphism
rather than of the morphism of analytic spaces. That is not cosmetic: the same proof written
against `X.restrictLE h` and `X.ofRestrict W` as morphisms of analytic spaces does not
elaborate in a million heartbeats, because unifying `(f ≫ g).toLRSHom` with
`f.toLRSHom ≫ g.toLRSHom` forces the category instance open at every step. -/
lemma resΓ_restrictLE (X : AnalyticSpace.{u}) {V W : X.Opens} (h : V ≤ W)
    (g : X.presheaf.obj (op ⊤)) :
    (LocallyRingedSpace.Γ.map (X.toLocallyRingedSpace.restrictLE h).op).hom (X.resΓ W g) =
      X.resΓ V g :=
  (LocallyRingedSpace.Γ_map_comp_apply (X.toLocallyRingedSpace.restrictLE h)
      (X.toLocallyRingedSpace.ofRestrict W.isOpenEmbedding) g).symm.trans
    (congrArg (fun m : X.toLocallyRingedSpace.restrict V.isOpenEmbedding ⟶
        X.toLocallyRingedSpace ↦ (LocallyRingedSpace.Γ.map m.op).hom g)
      (LocallyRingedSpace.restrictLE_fac X.toLocallyRingedSpace h))

/-- **A morphism whose image lies in an open subspace factors through it**, as a morphism of
complex analytic spaces.

`AlgebraicGeometry.LocallyRingedSpace.liftRestrict` at the underlying morphisms. It is `ℂ`-linear
for the same reason `ComplexAnalytic.AnalyticSpace.restrictLE` is, and by the same lemma: the
factorisation makes it a morphism *over* `X`, `φ` is `ℂ`-linear by assumption and
`ComplexAnalytic.AnalyticSpace.ofRestrict` by construction, so
`ComplexAnalytic.IsCLinearHom.of_comp` applies. Nothing is transported.

**This is the construction that builds a morphism whose *target* is an open subspace.** Before it,
everything here produced morphisms *out* of a restriction — `ofRestrict`, `restrictLE`,
`ComplexAnalytic.localisationProj` — and `restrictLE` was the only one landing in a restriction,
at the special case where the source is one too and the map is an inclusion. -/
noncomputable def liftRestrict {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X) (V : X.Opens)
    (h : Set.range (φ.toLRSHom.base : Z → X) ⊆ (V : Set X)) : Z ⟶ X.restrict V :=
  ⟨LocallyRingedSpace.liftRestrict φ.toLRSHom V h,
    IsCLinearHom.of_comp (LocallyRingedSpace.liftRestrict_fac φ.toLRSHom V h)
      φ.isCLinear (isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap V)⟩

/-- The underlying morphism of locally ringed spaces of
`ComplexAnalytic.AnalyticSpace.liftRestrict`. -/
lemma toLRSHom_liftRestrict {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X) (V : X.Opens)
    (h : Set.range (φ.toLRSHom.base : Z → X) ⊆ (V : Set X)) :
    (liftRestrict φ V h).toLRSHom = LocallyRingedSpace.liftRestrict φ.toLRSHom V h :=
  rfl

/-- **`ComplexAnalytic.AnalyticSpace.liftRestrict` is a factorisation of `φ`.** This, rather than
the morphism itself, is what a caller consumes — in particular it is how the underlying map of the
lift is computed, since the lift is opaque and the composite is not. -/
lemma liftRestrict_fac {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X) (V : X.Opens)
    (h : Set.range (φ.toLRSHom.base : Z → X) ⊆ (V : Set X)) :
    liftRestrict φ V h ≫ X.ofRestrict V = φ :=
  forgetToLocallyRingedSpace.map_injective (LocallyRingedSpace.liftRestrict_fac φ.toLRSHom V h)

end AnalyticSpace

end ComplexAnalytic

end

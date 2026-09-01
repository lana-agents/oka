/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.LocalIso
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
- `ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict`: **the inclusion of an open subspace is a
  local isomorphism.**
- `ComplexAnalytic.AnalyticSpace.restrictHom_comp`: **restricting a composite is composing the
  restrictions.**
- `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range`: **a morphism whose base is
  an embedding restricts to a finite morphism over any open subset of its image** — the shape an
  *open* immersion needs, since it is finite over such a subset and is not finite at all.
- `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`: **a local isomorphism restricted over an
  open subset of the target is a local isomorphism**, with no hypothesis on the morphism or the
  open beyond that. Unlike the bullet above this needs nothing of the base map's image, because
  both fields are local at a point and a restriction changes neither.

## Why `Oka/AnalyticSpace/LocalIso.lean` is imported here, when no import was forced

`ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict` needs `ofRestrict`, defined here, and
`ComplexAnalytic.AnalyticSpace.IsLocalIso`, defined there. **That does not mean one of the two
files had to import the other, and an earlier draft of this paragraph said it did.** Three files
already reach both: `Oka/AnalyticSpace/CoveringSpace.lean`, `Oka/AnalyticSpace/Degree.lean` and
`Oka/AnalyticSpace/SigmaFiniteEtale.lean`. Any of them would have cost **nothing**. **None of the
three is where the instance is used**, and that draft said the first of them was: the only
consumer of `ComplexAnalytic.AnalyticSpace.isLocalIso_ofRestrict` anywhere is
`OkaTest/CoveringSpace.lean`, which imports `Oka` wholesale and so finds it wherever it sits.

**This paragraph also said the import "can be undone by moving one instance", and that is no
longer true.** `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` below is a second
declaration in this file whose statement mentions `ComplexAnalytic.AnalyticSpace.IsLocalIso`, and
unlike the instance above it has a consumer **under `Oka/`** —
`Oka/Analytification/StandardEtaleFiniteEtale.lean` — rather than only in the test library. So
undoing the edge now means moving two declarations and giving that consumer an import it does not
have. The edge is still cheap, for the reason measured below; what it is no longer is free.

**It is here because both of its ingredients are.** The first field is
`Topology.IsOpenEmbedding.isLocalHomeomorph` at `U.isOpenEmbedding`; the second is
`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict` three declarations above, found by
`inferInstance` — a lemma that exists *only* to put Mathlib's statement at the
discrimination-tree key a caller of `ofRestrict` holds. Putting its one consumer in another file
is how such a lemma comes to look unused. The statement is also about open subspaces and not about
covering spaces: a `## Main results` bullet in `Oka/AnalyticSpace/CoveringSpace.lean` reading *the
inclusion of an open subspace is a local isomorphism* would be a claim in the wrong file.

**What the edge costs, and what the reverse would have.** Transitive closure of each file's import
list, expanding and counting **only modules under `Oka/` and `Mathlib/`** — other packages are
leaves and are dropped, which is the convention `scripts/import_cost.py` states as *"Mathlib
modules only"*, widened to this repository:

* this file, **3095 → 3100**, and the five are named: `Oka.AnalyticSpace.LocalIso`,
  `Oka.AnalyticSpace.Finite`, `Mathlib.Topology.IsLocalHomeomorph`,
  `Mathlib.Topology.OpenPartialHomeomorph.Composition`, `Mathlib.Topology.SeparatedMap`;
* `Oka/AnalyticSpace/LocalIso.lean`, **2160 → 3100**, since this file reaches
  `Oka.AnalyticSpace.Coherent` and the whole local-model apparatus.

**Five against 940 is the comparison, and it is what decided the direction.**

**Read the closures off Lean's own environment rather than off a parser over the header lines.**
The figures above are `lake env lean` on a scratch file whose imports are the list being measured,
with

```
open Lean in
#eval show CoreM Unit from do
  let ms := (← getEnv).header.moduleNames
  IO.println (ms.filter fun m => (`Oka).isPrefixOf m || (`Mathlib).isPrefixOf m).size
```

That is not fussiness. An earlier draft of this section gave 3075 and 2141 from a parser of its
own, and three hand-written parsers — that one and two reviewers' — disagreed with each other and
with Lean before the environment settled it. Three traps account for the spread and none of them
announces itself: matching the word *import* outside the header picks it up inside a docstring
code block and pulls in the whole of Mathlib; **seventy** Mathlib header lines carry a trailing
*shake* comment — `grep -rlE '^module[ \t]+--' .lake/packages/mathlib/Mathlib/`, in five
spellings — so a parser comparing the stripped line against the module keyword stops at each of
them, and one of the seventy is `Mathlib/Tactic/Common.lean`, which by itself takes the tactic
modules with it; and this Mathlib writes both *public meta import* and *import all*, which a
pattern anchored on the bare keyword misses.
`scripts/import_cost.py` cannot be used instead — it resolves only under `Mathlib/`, and neither
of these two files is a mirror file.

**All four figures are counterfactual, so recomputing them here needs the import above removed
first** — left in place the first reads `3100 → 3100`, and the second `3101`, one more, because
the union then contains `Oka.AnalyticSpace.LocalIso` itself. The five-module delta is what the
decision rests on and it is convention-invariant; the baselines are not.
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

/-- **The inclusion of an open subspace is a local isomorphism.**

Both fields are already here and neither needs a hypothesis. The underlying map is the inclusion
of an open set, so `Topology.IsOpenEmbedding.isLocalHomeomorph` gives the first; the second is
`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict` above, found by instance search — which
is what that lemma exists for, Mathlib's own statement being at a different
discrimination-tree key.

It is **not** finite étale in general, and nothing here says otherwise: the inclusion of the
punctured line into the line is an open subspace whose inclusion is not a closed map, which
`OkaTest/CoveringSpace.lean` exhibits as
`ComplexAnalytic.not_isFinite_puncturedInclCoveringSpaceHom`. -/
instance isLocalIso_ofRestrict (X : AnalyticSpace.{u}) (U : X.Opens) :
    AnalyticSpace.IsLocalIso (X.ofRestrict U) where
  isLocalHomeomorph := U.isOpenEmbedding.isLocalHomeomorph
  isIso_stalkMap _ := inferInstance

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

**The name shadows `ComplexAnalytic.restrictHom` inside `namespace AnalyticSpace`** — sixteen
files, and not the bulk of the development, which is written one namespace up in
`ComplexAnalytic`, where the bare name still resolves to the locally-ringed-space one. That is why
exactly one existing call site needed qualifying rather than dozens. A use of the bare name inside
`AnalyticSpace` now means this one; the locally-ringed-space one has to be written
`ComplexAnalytic.restrictHom`, as it is in `Oka/AnalyticSpace/HolomorphicMapGeneral.lean`. That is
the price of the name matching the one it wraps, and the mismatch is a type error rather than a
silent change of meaning: the two have different sources and targets.

**Count the sixteen with `grep -rlE '^namespace (ComplexAnalytic\.)?AnalyticSpace'`.** Nine of
them open `namespace AnalyticSpace` and seven open `namespace ComplexAnalytic.AnalyticSpace`
directly; the bare name is shadowed in both, and a grep for the first form alone answers nine and
is the natural thing to reach for. **No denominator is given, on purpose**: the file count moves
with every module added, and this figure is here to say the hazard is confined rather than to
give a ratio. -/
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

/-- **Restricting a composite is composing the restrictions.**

`ComplexAnalytic.restrictHom_comp` one category down, reflected along the faithful
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` — which is all a morphism of analytic
spaces needs, since the `ℂ`-linearity field is a proposition and equality of the two underlying
morphisms is equality of the two. The two sides have definitionally the same source; see the
locally-ringed-space statement for why its proof is a term rather than a `rw` chain. -/
lemma restrictHom_comp {A B C : AnalyticSpace.{u}} (f : A ⟶ B) (h : B ⟶ C) (V : C.Opens) :
    restrictHom (f ≫ h) V =
      restrictHom f ((Opens.map h.toLRSHom.base).obj V) ≫ restrictHom h V :=
  forgetToLocallyRingedSpace.map_injective
    (ComplexAnalytic.restrictHom_comp f.toLRSHom h.toLRSHom V)

/-- **A morphism whose base is an embedding restricts to a finite morphism over any open subset of
its image.**

`ComplexAnalytic.isClosedEmbedding_base_restrictHom_of_subset_range` and
`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`, and nothing between them.

**It is stated because the unrestricted morphism is usually not finite and this is not a weakening
of a stronger fact.** The case it exists for is an *open* immersion: `X.ofRestrict U` is never a
closed map unless `U` is clopen, so `IsFinite` of it is false in general, and yet its restriction
over a `V` contained in `U` is finite — the two ranges then agree and the restricted map is a
homeomorphism. That is what
`Oka/Analytification/StandardEtaleFiniteness.lean` spends, and it is why the hypothesis is on `V`
rather than on the morphism.

The import that makes this statable is `Oka/AnalyticSpace/LocalIso.lean`'s, whose closure carries
`Oka/AnalyticSpace/Finite.lean`; the section above prices that edge for a different reason and
this is a second consumer of it. -/
theorem isFinite_restrictHom_of_subset_range {A B : AnalyticSpace.{u}} {f : A ⟶ B}
    (hemb : IsEmbedding (f.toLRSHom.base : A → B)) {V : B.Opens}
    (hV : (V : Set B) ⊆ Set.range (f.toLRSHom.base : A → B)) :
    IsFinite (restrictHom f V) :=
  isFinite_of_isClosedEmbedding _
    (ComplexAnalytic.isClosedEmbedding_base_restrictHom_of_subset_range hemb hV)

/-- **A local isomorphism restricted over an open subset of the target is a local isomorphism.**

Nothing about the morphism is asked and nothing about the open subset is: both fields of
`ComplexAnalytic.AnalyticSpace.IsLocalIso` are conditions at a point, and a restriction changes
the point's neighbourhoods on neither side. **That is what separates this from
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` above**, whose hypothesis is
there because finiteness is not local on the target: the inclusion of an open subspace restricts
to a finite morphism only over a `V` inside its image, and is a local isomorphism over every `V`.

**The topological field is the commuting square and not a lemma about restrictions.**
`ComplexAnalytic.base_restrictHom` says `ofRestrict V ∘ restrictHom f V = f ∘ ofRestrict (f⁻¹ V)`
on points; the right-hand side is a local homeomorphism because both factors are, and
`IsLocalHomeomorph.of_comp` then peels off the left factor, which is one because
`Topology.IsOpenEmbedding.isLocalHomeomorph` applies to `V.isOpenEmbedding`. The continuity
`of_comp` asks for is the base map's own.

**The stalk field is a term and not a `rw`, and that is forced.**
`ComplexAnalytic.stalkMap_restrictHom_eq'` already writes the stalk map as an isomorphism, then
`f`'s stalk map, then an isomorphism, so instance search closes it once that factorisation is in
the goal — but `rw` fails to find the pattern, because `V : B.Opens` elaborates at the `toTopCat`
spelling of the carrier while the lemma wants `Opens ↑B.toTopCat` reached through
`toPresheafedSpace`. That seam runs through this corner of the tree and
`Oka/Analytification/StandardEtaleFiniteness.lean` records two more instances of it. -/
theorem isLocalIso_restrictHom {A B : AnalyticSpace.{u}} (f : A ⟶ B) [IsLocalIso f] (V : B.Opens) :
    IsLocalIso (restrictHom f V) where
  isLocalHomeomorph := by
    have hsq : ((B.ofRestrict V).toLRSHom.base : B.restrict V → B) ∘
        ((restrictHom f V).toLRSHom.base : _ → B.restrict V) =
        (f.toLRSHom.base : A → B) ∘
          ((A.ofRestrict ((Opens.map f.toLRSHom.base).obj V)).toLRSHom.base : _ → A) :=
      funext fun x ↦ ComplexAnalytic.base_restrictHom f.toLRSHom V x
    refine IsLocalHomeomorph.of_comp (g := ((B.ofRestrict V).toLRSHom.base : B.restrict V → B))
      ?_ V.isOpenEmbedding.isLocalHomeomorph
      (restrictHom f V).toLRSHom.base.hom.continuous
    rw [hsq]
    exact (IsLocalIso.isLocalHomeomorph (f := f)).comp
      ((Opens.map f.toLRSHom.base).obj V).isOpenEmbedding.isLocalHomeomorph
  isIso_stalkMap x :=
    (ComplexAnalytic.stalkMap_restrictHom_eq' f.toLRSHom V x).symm ▸
      (inferInstance : IsIso ((ComplexAnalytic.restrictStalkEquiv f.toLRSHom V x).hom ≫
        f.toLRSHom.stalkMap ((A.toLocallyRingedSpace.ofRestrict
            ((Opens.map f.toLRSHom.base).obj V).isOpenEmbedding).base x) ≫
          (A.toLocallyRingedSpace.ofRestrict
            ((Opens.map f.toLRSHom.base).obj V).isOpenEmbedding).stalkMap x))

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
against `X.restrictLE h` and `X.ofRestrict W` as morphisms of analytic spaces **exceeds the
default heartbeat budget**, because unifying `(f ≫ g).toLRSHom` with `f.toLRSHom ≫ g.toLRSHom`
forces the category instance open at every step.

**Measured 2026-08-31**, by replacing the `congrArg` below with one whose motive is over
`X.restrict V ⟶ X` and whose argument is `ComplexAnalytic.AnalyticSpace.restrictLE_fac` rather
than `AlgebraicGeometry.LocallyRingedSpace.restrictLE_fac`:
`(deterministic) timeout at whnf, maximum number of heartbeats (200000)`, reached in 20s.
**200000 is the budget in force** — `lakefile.toml` sets no `maxHeartbeats`, so a figure of a
million, which this paragraph gave until today, names a budget nobody set.

**Unlike the seam in `Oka/AnalyticSpace/Glue.lean`, this one is not known to be merely
expensive.** There the same counterfactual under `set_option maxHeartbeats 0` finishes, at about
eight times the file; here it was still elaborating after 21m29s and 5.4GB and was stopped, so
nothing measured says it terminates and nothing says it does not. -/
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

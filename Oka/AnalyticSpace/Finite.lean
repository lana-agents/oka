/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Basic

/-!
# Finite morphisms of complex analytic spaces

A holomorphic map is **finite** when it is closed and has finite fibres. That is the classical
definition — Grauert–Remmert take it, and so does Fischer — and it is what this file gives to
`ComplexAnalytic.AnalyticSpace.Hom`, together with the stability properties that make it usable
and the two implications that make it non-vacuous.

## Why this definition and not the algebraic-geometry one

`AlgebraicGeometry.IsFinite` for schemes is `IsAffineHom f` together with `RingHom.Finite` on the
sections over every affine open, and its whole API — `HasAffineProperty`, `affineAnd`, stability
under composition and base change — is derived from affine-locality. **There are no affines in the
analytic category**, and the reason is that the machinery affine-locality is built out of does not
exist here: there is no `Spec`–`Γ` adjunction for analytic spaces, so no class of objects on which
a morphism's behaviour determines it globally, and no `HasAffineProperty` to state a property
against. `ComplexAnalytic.AnalyticSpace` is defined by local models, and a local model is a closed
subspace of an open subset of `ℂ^n` — a chart, not an affine. So none of that transfers and there
is no `IsAffineHom` to extend.

The two conditions are also not the same notion, so this is not a choice between spellings of one
thing. For schemes, `Spec` of an infinite algebraic field extension `k ⟶ K` is a homeomorphism
between one-point spaces, hence closed with finite fibres, while `k ⟶ K` is not module-finite; so
`AlgebraicGeometry.IsFinite` fails there and the condition below holds. **That example is not
formalised here** and nothing in this file depends on it; it is recorded because it is the reason
the class is stated in the `ComplexAnalytic` namespace rather than for
`AlgebraicGeometry.LocallyRingedSpace` in the mirror tree, where its name would read as the
scheme-theoretic condition and would specialise to a different one.

## Properness, and exactly what agrees with what

A finite morphism is proper: `ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`. That
is a theorem rather than part of the definition, and it needs **no separation hypothesis** — a
finite set is compact in any topological space, unlike the covering-map statement in
`Oka/AnalyticSpace/CoveringMap.lean`, which does need one on the source.

**The converse is false, and this file used to say "proper and finite-with-finite-fibres agree"
in a way that invited the false reading.** Properness gives *compact* fibres, and a compact fibre
is finite only when it is also discrete, so properness alone does not imply finiteness. What is
true is the agreement with finiteness of the fibres carried on **both** sides: `IsFinite f` iff
the underlying map is proper and has finite fibres, which is
`ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber`. Read that way the
content of the agreement is exactly `IsProperMap ↔ IsClosedMap` **given** finite fibres, which is
where the two directions sit: one is `IsProperMap.isClosedMap`, the other is the compactness of a
finite set.

There is deliberately no `IsProper` class. `IsProperMap` on `f.toLRSHom.base` already is the
statement; a class would have to carry its own identity, composition and non-vacuity API to earn
its place, and nothing here or downstream consumes one.

## What is not here, and it is the whole of the subject

**Grauert's finite mapping theorem** — that `f_*𝒪_X` is a coherent `𝒪_Y`-module for finite `f` —
is what makes this definition useful, and it is not proved here or anywhere in this repository.
Nothing below mentions a pushforward. That absence stands; the properness clause that used to
stand beside it does not, and is now the section above.

**Finite covers are a further condition and are not defined here.** The Riemann existence theorem
is about finite *étale* covers — finite together with being a local isomorphism — and that is a
second notion resting on this one.

**There is no base change.** `AlgebraicGeometry.IsFinite`'s `IsStableUnderBaseChange` has no
analogue below because this repository has no fibre products of analytic spaces; the absence is
stated here rather than left to be discovered.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.IsFinite`: **a morphism of complex analytic spaces is finite when
  its underlying map is closed and has finite fibres.**

## Main results

- `ComplexAnalytic.AnalyticSpace.isFinite_id` and
  `ComplexAnalytic.AnalyticSpace.isFinite_comp`: the finite morphisms contain the identities and
  are closed under composition.
- `ComplexAnalytic.AnalyticSpace.isFinite_of_isIso`: an isomorphism is finite.
- `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` and
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isCutOutBy`: **a closed embedding is finite, and
  hence so is every morphism cutting its source out of its target by global sections** — which is
  every local model this development builds.
- `ComplexAnalytic.AnalyticSpace.not_isFinite_of_infinite_fiber`: the criterion a non-example is
  exhibited by.
- `ComplexAnalytic.AnalyticSpace.isProperMap_base_of_isFinite`: **a finite morphism is proper**,
  and `ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber` is the
  agreement in both directions.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **A morphism of complex analytic spaces is finite when its underlying map is closed and has
finite fibres.**

Both fields are conditions on `f.toLRSHom.base` and neither mentions the structure sheaves; the
content of finiteness for the sheaves is Grauert's finite mapping theorem, which is a theorem
about this definition and is not in this repository.

The underlying map is spelled `f.toLRSHom.base` rather than `f.base`, as everywhere else here:
`ComplexAnalytic.AnalyticSpace.Hom` is a `AlgebraicGeometry.LocallyRingedSpace.Hom` together with
a `ℂ`-linearity condition, and its category structure is defined through `toLRSHom`. -/
@[mk_iff]
class IsFinite {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) : Prop where
  /-- The underlying map is closed. -/
  isClosedMap : IsClosedMap f.toLRSHom.base
  /-- Every fibre is finite. -/
  finite_fiber (y : Y) : Finite (f.toLRSHom.base ⁻¹' {y})

/-- **The identity is finite.** -/
instance isFinite_id (X : AnalyticSpace.{u}) : IsFinite (𝟙 X) where
  isClosedMap := by
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = id := rfl
    rw [h]
    exact IsClosedMap.id
  finite_fiber y := by
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = id := rfl
    rw [h, Set.preimage_id]
    infer_instance

/-- **A composite of finite morphisms is finite.**

The closed half is `IsClosedMap.comp`. The fibre half is `Set.Finite.preimage'` — *a set with
finite fibres has finite preimage over a finite set* — applied to the fibre of the second map;
`Set.Finite.preimage` is the wrong lemma here, since it asks for injectivity, which a finite
morphism does not have. -/
instance isFinite_comp {X Y Z : AnalyticSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] : IsFinite (f ≫ g) where
  isClosedMap := by
    have h : ((f ≫ g).toLRSHom.base : X → Z) = (g.toLRSHom.base : Y → Z) ∘ f.toLRSHom.base := rfl
    rw [h]
    exact (IsFinite.isClosedMap (f := g)).comp (IsFinite.isClosedMap (f := f))
  finite_fiber z := by
    have h : ((f ≫ g).toLRSHom.base : X → Z) = (g.toLRSHom.base : Y → Z) ∘ f.toLRSHom.base := rfl
    rw [h, Set.preimage_comp]
    haveI : Finite ((g.toLRSHom.base : Y → Z) ⁻¹' {z}) := IsFinite.finite_fiber z
    refine (Set.Finite.preimage' (Set.toFinite _) fun y _ ↦ ?_).to_subtype
    haveI : Finite ((f.toLRSHom.base : X → Y) ⁻¹' {y}) := IsFinite.finite_fiber y
    exact Set.toFinite _

/-- **A closed embedding is finite**: it is closed, and injective, so its fibres are subsingletons.

This is the source of every finite morphism below. Note that only the *topological* half of a
closed immersion is used — nothing is asked of the map on structure sheaves. -/
theorem isFinite_of_isClosedEmbedding {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    (h : IsClosedEmbedding (f.toLRSHom.base : X → Y)) : IsFinite f where
  isClosedMap := h.isClosedMap
  finite_fiber y :=
    Set.Finite.to_subtype (Set.Finite.preimage h.injective.injOn (Set.finite_singleton y))

/-- **An isomorphism is finite**, being a homeomorphism and hence a closed embedding. -/
theorem isFinite_of_isIso {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsIso f] : IsFinite f :=
  isFinite_of_isClosedEmbedding f
    (LocallyRingedSpace.homeoOfIso
      (forgetToLocallyRingedSpace.{u}.mapIso (asIso f))).isClosedEmbedding

/-- **A morphism cutting its source out of its target by global sections is finite.**

`ComplexAnalytic.IsCutOutBy` carries `isClosedEmbedding` as a field, so this is that field read
through `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`. It is the statement that
makes the class non-vacuous in general rather than at one example: every closed analytic subspace
this development cuts out — every local model, in particular — is finite over its ambient space.

Like `ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy`, this takes the cut-out data as a
hypothesis about `f.toLRSHom` rather than producing it, because the analytic-level morphisms
carrying such data are built by the caller; see `OkaTest/FiniteMorphism.lean` for a closed
embedding exhibited directly instead. -/
theorem isFinite_of_isCutOutBy {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) {k : ℕ}
    {s : Fin k → Y.presheaf.obj (op ⊤)} (h : IsCutOutBy f.toLRSHom s) : IsFinite f :=
  isFinite_of_isClosedEmbedding f h.isClosedEmbedding

/-- **A morphism with an infinite fibre is not finite**, which is how a non-example is exhibited:
the fibre condition is the one that fails for a projection, and it fails for a reason one can
point at a set for. -/
theorem not_isFinite_of_infinite_fiber {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) (y : Y)
    (h : Infinite (f.toLRSHom.base ⁻¹' {y})) : ¬ IsFinite f := fun hf ↦
  (not_finite_iff_infinite.2 h) (hf.finite_fiber y)

/-- **A finite morphism is proper**, in the sense that its underlying map is an `IsProperMap`.

`isProperMap_iff_isClosedMap_and_compact_fibers` asks for three things and the class supplies two
of them directly; the third, continuity, is not a field of
`ComplexAnalytic.AnalyticSpace.IsFinite` and does not need to be, since the underlying map is a
`TopCat` morphism and carries its continuity with it.

**No separation hypothesis is used and none is available.** A finite set is compact in an
arbitrary topological space (`Set.Finite.isCompact`), so compactness of the fibres falls out of
`ComplexAnalytic.AnalyticSpace.IsFinite.finite_fiber` alone. That is not true of the covering-map
statement in `Oka/AnalyticSpace/CoveringMap.lean`, which genuinely needs `[T2Space X]`; the
hypothesis should not be carried over here out of symmetry with it.

**The converse fails**: properness gives compact fibres, not finite ones. See
`ComplexAnalytic.AnalyticSpace.isFinite_iff_isProperMap_base_and_finite_fiber` for the agreement
that does hold, and the module docstring for why the weaker-sounding statement is the honest
one. -/
theorem isProperMap_base_of_isFinite {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) [IsFinite f] :
    IsProperMap (f.toLRSHom.base : X → Y) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨f.toLRSHom.base.hom.continuous, IsFinite.isClosedMap,
      fun y ↦ have := IsFinite.finite_fiber (f := f) y; (Set.toFinite _).isCompact⟩

/-- **A morphism is finite exactly when its underlying map is proper and has finite fibres.**

This is the agreement the module docstring is careful about: finiteness of the fibres appears on
*both* sides, because properness does not imply it. With it assumed, the whole content is that a
proper map is closed (`IsProperMap.isClosedMap`) and that a closed map with finite — hence
compact — fibres is proper.

`ComplexAnalytic.AnalyticSpace.isFinite_iff`, generated by `@[mk_iff]` on the class, is the
same statement with `IsClosedMap` in place of `IsProperMap`. -/
theorem isFinite_iff_isProperMap_base_and_finite_fiber {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) :
    IsFinite f ↔ IsProperMap (f.toLRSHom.base : X → Y) ∧
      ∀ y : Y, Finite (f.toLRSHom.base ⁻¹' {y}) :=
  ⟨fun _ ↦ ⟨isProperMap_base_of_isFinite f, fun y ↦ IsFinite.finite_fiber y⟩,
    fun h ↦ ⟨h.1.isClosedMap, h.2⟩⟩

end ComplexAnalytic.AnalyticSpace

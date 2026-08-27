/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CoveringMap
import Oka.AnalyticSpace.Sigma

/-!
# The trivial `n`-sheeted cover of a complex analytic space

`ComplexAnalytic.AnalyticSpace.sigmaDesc` is the morphism out of a disjoint union determined by a
morphism out of each member. This file says that being **finite** and being a **local
isomorphism** both pass from the members to it, and applies that to the family of `n` copies of a
single space mapping to it by the identity.

**That morphism is the first finite étale witness in this repository whose number of sheets is not
2.** `ComplexAnalytic.card_fiber_base_sq` puts every fibre of the squaring map of the punctured
line at two points, and until now it was the only morphism here for which the value was known;
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` gives every value at once. It is also the
first `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` witness with a **disconnected source**, which
is the local model of *evenly covered* and the shape the analytic side of the Riemann existence
theorem is stated in.

## There is no analysis in any of it

Every proof below is topology and category theory. The two conditions are checked against
`AlgebraicGeometry.LocallyRingedSpace`-level statements in
`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean` —
`AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc`,
`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv`,
`AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc` and
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc` — which is where they belong,
since none of them mentions anything complex-analytic. What is left here is the translation
across `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` and the counting.

## The fibre is an equivalence and not a cardinality, and that is what makes `n = 0` free

`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv` exhibits the fibre of a descent map as
`Σ i, (fibre of the i-th piece)`. Finiteness of the fibre and its size are then the same object
read twice, and neither statement needs a positivity hypothesis on the index type.

**`n = 0` is a real case and this file admits it rather than excluding it.** The coproduct of the
empty family is the empty analytic space (`ComplexAnalytic.AnalyticSpace.isEmpty_sigma`), and the
empty space over a non-empty one is **finite étale here**: the underlying map is closed because
every image is empty, its fibres are empty and hence finite, and it is a local homeomorphism and
an isomorphism on stalks because it has no points to check either at.
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` then reads `0 = 0`.

That is a decision and not a theorem about the classical notion: **some definitions of a covering
map require surjectivity**, and under those the empty cover of a non-empty base is not one.
`ComplexAnalytic.AnalyticSpace.IsFinite` and `ComplexAnalytic.AnalyticSpace.IsLocalIso` as
`Oka/AnalyticSpace/Finite.lean` and `Oka/AnalyticSpace/LocalIso.lean` state them do not, and
neither does Mathlib's `IsCoveringMap`, whose evenly-covered condition is satisfied at every point
by the empty index type — `Oka/AnalyticSpace/CoveringMap.lean` says so in terms. So this file
inherits the convention rather than choosing it, and the value of
`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` at `n = 0` is what that convention commits
one to. It is stated here so that a reader who expected `0 < n` finds the answer rather than a
missing hypothesis.

## What is not here

**The `degree` function is not here, and it is no longer absent from the development.**
`ComplexAnalytic.AnalyticSpace.degree` is in `Oka/AnalyticSpace/Degree.lean`, which imports this
file and reads `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` into
`ComplexAnalytic.AnalyticSpace.degree_sigmaFold`; the paragraph that used to stand here quoted
`Oka/AnalyticSpace/LocalIso.lean` declining a degree, and that refusal has been withdrawn there.
What is true of *this* file is unchanged and is why the direction of the import is that way round:
the count below is computed at every point directly, so
`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` is not used and no connectedness
hypothesis appears.

**No claim that the trivial cover is not a non-trivial one.** For `n = 1` the fold map is a
bijection on points and one would expect it to be an isomorphism; that is a statement about the
structure sheaves as well and nothing here proves it.

**Nothing about the analytification of a finite étale morphism of schemes**, which is the other
blocker of the Riemann existence theorem and is untouched.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.sigmaFold`: **the trivial `ι`-sheeted cover** `∐_{i : ι} X ⟶ X`,
  the descent map of the constant family at the identity.

## Main results

- `ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc` and
  `ComplexAnalytic.AnalyticSpace.isLocalIso_sigmaDesc`: **finiteness and being a local
  isomorphism pass from the members of a disjoint union to a descent map out of it**, the first
  for a finite index type and the second for any.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc`: the two together.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold`: **the trivial `ι`-sheeted cover is
  finite étale** for a finite `ι`.
- `ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold`: **every fibre of it has `Nat.card ι`
  points**, at every point of the base and with no connectedness hypothesis.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.LocallyRingedSpace TopologicalSpace Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

noncomputable section

variable {ι : Type u} (F : ι → AnalyticSpace.{u}) {Y : AnalyticSpace.{u}} (g : ∀ i, F i ⟶ Y)

/-- **The underlying morphism of a descent map is the coproduct's descent map.**

`ComplexAnalytic.AnalyticSpace.sigmaDesc` is built with `CategoryTheory.Limits.Sigma.desc` as its
`toLRSHom'` field, so this is `rfl`. **It is stated for a reader and for a consumer that does not
exist yet, not because anything below needs it**: the statements below reach the
locally-ringed-space lemmas by definitional unfolding, since the field really is `Sigma.desc`, and
this file compiles with the lemma deleted. Its `@[simp]` cannot fire here either, there being no
`simp` call in the file. Measured 2026-08-25 at `master` = `d12d334`; an earlier version of this
docstring said the two spellings are different discrimination-tree keys and that every statement
below applies a locally-ringed-space lemma *to this lemma*, which is not what the proofs do. -/
@[simp]
lemma toLRSHom_sigmaDesc : (sigmaDesc F g).toLRSHom = Sigma.desc fun i ↦ (g i).toLRSHom := rfl

/-- **A descent map out of a disjoint union of finitely many analytic spaces is finite as soon as
each of its restrictions is.**

The closed half is
`AlgebraicGeometry.LocallyRingedSpace.isClosedMap_base_sigmaDesc` and the fibre half is
`AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv`, which presents the fibre as
`Σ i, (fibre of the i-th piece)` — so its finiteness is `Finite.instSigma` and needs the index
type finite for the second time.

**`[Finite ι]` is used twice and for two different reasons**: once to make the union of the
members' images a finite union of closed sets, and once to make the fibre a finite disjoint
union. Neither use is removable and the two are independent. -/
instance isFinite_sigmaDesc [Finite ι] [∀ i, IsFinite (g i)] : IsFinite (sigmaDesc F g) where
  isClosedMap := isClosedMap_base_sigmaDesc _ _ fun i ↦ IsFinite.isClosedMap (f := g i)
  finite_fiber y := by
    have hi : ∀ i, Finite (((g i).toLRSHom.base ⁻¹' {y} : Set (F i))) :=
      fun i ↦ IsFinite.finite_fiber (f := g i) y
    exact @Finite.of_equiv _ _ (@Finite.instSigma _ _ _ hi)
      (fiberSigmaDescEquiv (fun i ↦ (F i).toLocallyRingedSpace) (fun i ↦ (g i).toLRSHom) y)

/-- **A descent map out of a disjoint union is a local isomorphism as soon as each of its
restrictions is**, with no finiteness hypothesis on the index type.

The two fields are `AlgebraicGeometry.LocallyRingedSpace.isLocalHomeomorph_base_sigmaDesc` and
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_sigmaDesc`, and the reason neither needs
`[Finite ι]` is the same in both cases: both are conditions **at a point**, and a point of the
coproduct lies in exactly one member.

Note the asymmetry with `ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc`, which is not an
artefact of the proofs: an infinite disjoint union of copies of a space really is a local
isomorphism over it and really is not finite over it, since the fibres are infinite. -/
instance isLocalIso_sigmaDesc [∀ i, IsLocalIso (g i)] : IsLocalIso (sigmaDesc F g) where
  isLocalHomeomorph :=
    isLocalHomeomorph_base_sigmaDesc _ _ fun i ↦ IsLocalIso.isLocalHomeomorph (f := g i)
  isIso_stalkMap x :=
    isIso_stalkMap_sigmaDesc _ _ (fun i z ↦ IsLocalIso.isIso_stalkMap (f := g i) z) x

/-- **A descent map out of a disjoint union of finitely many members is finite étale as soon as
each of its restrictions is**, from the two rungs above and nothing else. -/
instance isFiniteEtale_sigmaDesc [Finite ι] [∀ i, IsFiniteEtale (g i)] :
    IsFiniteEtale (sigmaDesc F g) where
  isFinite := inferInstance
  isLocalIso := inferInstance

/-! ### The trivial cover -/

variable (ι) in
/-- **The trivial `ι`-sheeted cover of an analytic space**: `∐_{i : ι} X ⟶ X`, the descent map of
the constant family at the identity of `X`.

This is the fold map of the coproduct, and it is a cover in the honest sense as soon as `ι` is
finite: `ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold`. The index type is a `Type u` and
not a `ℕ` because `ComplexAnalytic.AnalyticSpace.sigma` is indexed by one; the `n`-sheeted cover
is this at `ULift (Fin n)`, which is how `OkaTest/AnalyticSigma.lean` instantiates it. -/
def sigmaFold (X : AnalyticSpace.{u}) : sigma (fun _ : ι ↦ X) ⟶ X :=
  sigmaDesc _ fun _ ↦ 𝟙 X

/-- **The trivial `ι`-sheeted cover is finite étale**, for a finite index type.

`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaDesc` at the constant family, whose pieces are
identities and are finite étale by `ComplexAnalytic.AnalyticSpace.isFiniteEtale_id`. Nothing is
asked of `X` — not Hausdorff, not connected, not non-empty. -/
instance isFiniteEtale_sigmaFold [Finite ι] (X : AnalyticSpace.{u}) :
    IsFiniteEtale (sigmaFold ι X) where
  isFinite := isFinite_sigmaDesc _ _
  isLocalIso := isLocalIso_sigmaDesc _ _

/-- **Every fibre of the trivial `ι`-sheeted cover has `Nat.card ι` points.**

The composite of two equivalences: `AlgebraicGeometry.LocallyRingedSpace.fiberSigmaDescEquiv`
presents the fibre as `Σ i : ι, ((𝟙 X).base ⁻¹' {x})`, and each of those fibres is the singleton
`{x}`, so `Equiv.sigmaUnique` collapses the sum to `ι`.

**`Nat.card` is not a junk value here even for an infinite `ι`, and it is not informative either.**
For infinite `ι` both sides are `0` — the fibre is infinite and `Nat.card` of an infinite type is
`0` — so the statement is true but says nothing; it is `[Finite ι]`-free because the proof is, not
because the content survives. The morphism is not finite étale in that case, so nothing downstream
reads it there.

This is the first morphism in this repository whose number of sheets is computed and is not 2 —
compare `ComplexAnalytic.card_fiber_base_sq`, which puts the fibres of `z ↦ z²` on the punctured
line at two points. Unlike `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale`, which
says the number is *constant* over a preconnected base, this computes it at each point separately
and needs no hypothesis on `X` at all. -/
theorem card_fiber_sigmaFold (X : AnalyticSpace.{u}) (x : X) :
    Nat.card ((sigmaFold ι X).toLRSHom.base ⁻¹' {x}) = Nat.card ι := by
  have hu : ∀ _ : ι, Unique (((𝟙 X : X ⟶ X).toLRSHom.base ⁻¹' {x} : Set X)) := by
    intro _
    have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = _root_.id := rfl
    rw [h, Set.preimage_id]
    infer_instance
  refine (Nat.card_eq_of_bijective _
    (fiberSigmaDescEquiv (fun _ : ι ↦ X.toLocallyRingedSpace)
      (fun _ ↦ (𝟙 X : X ⟶ X).toLRSHom) x).symm.bijective).trans ?_
  exact Nat.card_eq_of_bijective _ (@Equiv.sigmaUnique ι _ hu).bijective

end

end ComplexAnalytic.AnalyticSpace

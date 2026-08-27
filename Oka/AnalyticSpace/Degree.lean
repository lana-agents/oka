/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SigmaFiniteEtale
import Oka.SetTheory.Cardinal.Finite

/-!
# The degree of a morphism of complex analytic spaces

`ComplexAnalytic.AnalyticSpace.degree` is the number of sheets of a finite étale morphism, as a
single natural number attached to the morphism rather than a theorem about a pair of points.

## Why this was declined before, and what discharges the objection

Four docstrings in this development used to record the absence of a `degree` function, with the
same two-part reason: a `Nat`-valued definition carries a **well-definedness obligation**, and
**nothing consumed one**. Both parts are answered here and neither is answered by fiat.

* The obligation is discharged by `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`, which is
  `ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` — constancy of the fibre over a
  preconnected base — read at the definition. Note the direction of the dependency: the definition
  below is made for *every* morphism and is well-behaved only under the hypotheses of that
  theorem, exactly as `Nat.card` is defined for every type and is informative only on a finite
  one.
* The consumer is `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`: a finite
  étale morphism of degree one has a homeomorphism for its underlying map. That statement cannot
  be phrased at all without a degree — "all fibres have the same size" does not say what the size
  is, and "this particular fibre is a singleton" is a statement about a point.

## The definition is an `iSup` and not a value at a chosen point

`⨆ y, Nat.card (f ⁻¹' {y})` needs no point of the target and no `[Nonempty Y]`, where
`Nat.card (f ⁻¹' {Classical.arbitrary Y})` would need one in the *definition* and thereby in the
statement of every lemma about it. The cost is that the two facts a reader wants are separate:

* over the empty target the value is `0`, since an `iSup` over an empty index type is `⊥`;
* over a non-empty target on which the fibre count is constant the value is that constant, which
  is `ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` and is `ciSup_const`.

Everything below goes through the second of those, including the two computations. **No covering
map theory enters any of them except `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`**, which
is the only statement here that needs the fibres to be *related* to each other rather than
computed one at a time.

## What is *not* proved, and it is the interesting half

`ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one` concludes a homeomorphism of
the **underlying spaces** and not an isomorphism of analytic spaces, although
`ComplexAnalytic.AnalyticSpace.IsLocalIso` also carries an isomorphism on every stalk. The two
together ought to give an isomorphism, and the step from them to one is a comparison of sheaves
across a homeomorphism which this development does not have; `Oka/AnalyticSpace/LocalIso.lean`
records the same gap from the other side. So `ComplexAnalytic.not_isIso_sq` is *not* reproved
here, and the degree of a morphism is at present a topological invariant of it.

Multiplicativity in a composite is not proved either. It is true, and the proof is a fibrewise
count over the intermediate space that has nothing to do with the material below.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.degree`: **the number of sheets**, as a natural number.

## Main results

- `ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber`: it is the size of the fibre over any
  point, for a finite étale morphism over a preconnected base — the well-definedness statement.
- `ComplexAnalytic.AnalyticSpace.degree_id` and
  `ComplexAnalytic.AnalyticSpace.degree_sigmaFold`: the degree of an identity is `1`, and the
  degree of the trivial `ι`-sheeted cover is `Nat.card ι`, so **every value is realised**.
- `ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one` and
  `ComplexAnalytic.AnalyticSpace.isHomeomorph_base_of_degree_eq_one`: **degree one means the
  underlying map is a homeomorphism.**

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {ι : Type u} {X Y : AnalyticSpace.{u}}

/-- **The degree, or number of sheets, of a morphism of complex analytic spaces**: the supremum
over the target of the number of points of a fibre.

The definition is made for an arbitrary morphism, with no hypothesis at all, and is informative
exactly when the fibre count is constant and finite —
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` is that statement for a finite étale morphism
over a preconnected base, and is the well-definedness obligation the module docstring is about.

**Two junk values are folded into the one expression and they are different junk.** `Nat.card` of
an infinite fibre is `0`, and an `iSup` over an empty target — or over a family of fibre counts
that is unbounded — is `0` as well, since `ℕ` is a `ConditionallyCompleteLinearOrderBot`. Neither
is reachable under the hypotheses of the theorems below, and neither is repaired by choosing a
point of the target instead: that choice merely moves the empty case into the *statement* of every
lemma, as a `[Nonempty Y]` the definition would then need. -/
noncomputable def degree (f : X ⟶ Y) : ℕ :=
  ⨆ y : Y, Nat.card (f.toLRSHom.base ⁻¹' {y})

/-- **A morphism all of whose fibres have `n` points, over a non-empty target, has degree `n`.**

This is `ciSup_const` and nothing else; it is stated because every computation of a degree below
is an instance of it, and because it is where the `[Nonempty Y]` that
`ComplexAnalytic.AnalyticSpace.degree` deliberately does not carry has to be supplied.

The hypothesis is about each fibre separately, so no covering-space theory is involved and no
finiteness is asked of anything. -/
theorem degree_eq_of_forall_card_fiber_eq (f : X ⟶ Y) [Nonempty Y] {n : ℕ}
    (h : ∀ y : Y, Nat.card (f.toLRSHom.base ⁻¹' {y}) = n) : degree f = n := by
  rw [degree]
  simp_rw [h]
  exact ciSup_const

/-- **The degree of a finite étale morphism over a preconnected base is the number of points of
the fibre over any point**, which is the well-definedness statement for
`ComplexAnalytic.AnalyticSpace.degree`.

`ComplexAnalytic.AnalyticSpace.card_fiber_eq_of_isFiniteEtale` says the fibre count is constant;
this says the constant is the degree. The point `y` supplies the `[Nonempty Y]` that
`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` needs, so no separate
non-emptiness hypothesis appears.

This is the only statement in this file that uses the covering-map theory; the two computations
below reach their fibre counts one point at a time and use none of it. -/
theorem degree_eq_card_fiber (f : X ⟶ Y) [IsFiniteEtale f] [T2Space X] [PreconnectedSpace Y]
    (y : Y) : degree f = Nat.card (f.toLRSHom.base ⁻¹' {y}) :=
  haveI : Nonempty Y := ⟨y⟩
  degree_eq_of_forall_card_fiber_eq f fun y' ↦ card_fiber_eq_of_isFiniteEtale f y' y

/-- **The identity has degree one**, on a non-empty space.

The anchor for the scale: every fibre of `𝟙 X` is a singleton, so
`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` applies with no hypothesis
beyond `[Nonempty X]`, and in particular without `[T2Space X]` or preconnectedness. On the empty
space the degree is `0` instead, which is the `iSup` convention and not a defect. -/
theorem degree_id (X : AnalyticSpace.{u}) [Nonempty X] : degree (𝟙 X) = 1 := by
  refine degree_eq_of_forall_card_fiber_eq _ fun x ↦ ?_
  have h : ((𝟙 X : X ⟶ X).toLRSHom.base : X → X) = _root_.id := rfl
  rw [h, Set.preimage_id]
  exact Nat.card_unique

/-- **The trivial `ι`-sheeted cover has degree `Nat.card ι`.**

`ComplexAnalytic.AnalyticSpace.card_fiber_sigmaFold` computes each fibre separately, so this is
`ComplexAnalytic.AnalyticSpace.degree_eq_of_forall_card_fiber_eq` applied to it and there is no
analysis and no covering-space theory in it. `[Finite ι]` is not needed, for the same reason it is
not needed there — and for the same reason the statement says nothing for an infinite `ι`, both
sides being `0`.

`[Nonempty X]` is needed and is not decorative: over the empty space the coproduct is empty too
and the degree is `0`, while `Nat.card ι` need not be.

**Together with `ComplexAnalytic.AnalyticSpace.degree_id` this realises every value**: at
`ι = ULift (Fin n)` the degree is `n`, for every `n`, and the morphism is finite étale by
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_sigmaFold`. What it does not give is a *connected*
source, so the trivial covers say nothing about the degree of a cover that is not a disjoint union
of copies of its base; `ComplexAnalytic.degree_sq` is the witness for that. -/
theorem degree_sigmaFold (ι : Type u) (X : AnalyticSpace.{u}) [Nonempty X] :
    degree (sigmaFold ι X) = Nat.card ι :=
  degree_eq_of_forall_card_fiber_eq _ (card_fiber_sigmaFold X)

/-- **A finite étale morphism over a preconnected base has degree one exactly when its underlying
map is bijective.**

The consumer the earlier refusals of a `degree` function said did not exist. Both directions are
`Function.bijective_iff_forall_card_preimage_eq_one` — bijectivity of a map is precisely every
fibre having one point — together with
`ComplexAnalytic.AnalyticSpace.degree_eq_card_fiber` to move between "every fibre" and "the
degree". The forward direction is the one that needs the constancy: from a single fibre of size
one it concludes the degree, and that step is the well-definedness theorem.

`[Nonempty Y]` is genuine on the right and invisible on the left: over the empty target every map
is bijective while the degree is `0`. -/
theorem bijective_base_iff_degree_eq_one (f : X ⟶ Y) [IsFiniteEtale f] [T2Space X]
    [PreconnectedSpace Y] [Nonempty Y] :
    Function.Bijective (f.toLRSHom.base : X → Y) ↔ degree f = 1 := by
  rw [Function.bijective_iff_forall_card_preimage_eq_one]
  refine ⟨fun h ↦ degree_eq_of_forall_card_fiber_eq f h, fun h y ↦ ?_⟩
  rw [← degree_eq_card_fiber f y, h]

/-- **A finite étale morphism of degree one is a homeomorphism on the underlying spaces.**

The three inputs to `isHomeomorph_iff_continuous_isClosedMap_bijective` are, in order, the
continuity a `TopCat` morphism carries with it, the closedness field of
`ComplexAnalytic.AnalyticSpace.IsFinite`, and
`ComplexAnalytic.AnalyticSpace.bijective_base_iff_degree_eq_one`. **The local-homeomorphism field
of `ComplexAnalytic.AnalyticSpace.IsLocalIso` is not used**, and neither is the covering-map
theorem: a closed continuous bijection is a homeomorphism whether or not it is a local one.

**The conclusion is topological and is weaker than the expected one.** `IsLocalIso` also gives an
isomorphism on every stalk, and a homeomorphism together with stalkwise isomorphisms ought to give
an isomorphism of analytic spaces; the missing step is a comparison of the two structure sheaves
across the homeomorphism, which this development does not have. So this does not reprove
`ComplexAnalytic.not_isIso_sq`, and it is not the converse of anything stated here. -/
theorem isHomeomorph_base_of_degree_eq_one (f : X ⟶ Y) [IsFiniteEtale f] [T2Space X]
    [PreconnectedSpace Y] [Nonempty Y] (h : degree f = 1) :
    IsHomeomorph (f.toLRSHom.base : X → Y) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨f.toLRSHom.base.hom.continuous, IsFinite.isClosedMap,
      (bijective_base_iff_degree_eq_one f).mpr h⟩

end ComplexAnalytic.AnalyticSpace

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.FiniteMorphism

/-!
# Finite étale cancellation: a non-vacuity, and the counterexample the hypothesis rules out

Two unrelated things about `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`
(`Oka/AnalyticSpace/FiniteEtaleCancel.lean`): that its hypotheses are satisfiable outside the
isomorphisms, and that the covering hypothesis in the topological statement underneath it cannot
be weakened to *closed with finite fibres*.

## The non-vacuity, and what it is not

`ComplexAnalytic.isFiniteEtale_sq_of_comp` applies the cancellation at
`f = g = ComplexAnalytic.sq`, the squaring map of the punctured line, which is the only finite
étale morphism in this repository that is not an isomorphism (`ComplexAnalytic.not_isIso_sq`).
All three hypotheses are discharged there: `ComplexAnalytic.isFiniteEtale_sq`, the composition
instance for the composite, and `ComplexAnalytic.t2Space_restrict_punctured` for the Hausdorff
condition on the middle space.

**It is not independent evidence about `z ↦ z²`, and reads as a round trip if that is not said.**
The hypothesis `IsFiniteEtale (sq ≫ sq)` is itself obtained from
`ComplexAnalytic.isFiniteEtale_sq`, so the conclusion is a statement already in hand. What the
test establishes is that the three hypotheses of the cancellation are **simultaneously satisfiable
at a morphism that is not an isomorphism** — which is what stops it from being a theorem about
identities — and that the `[T2Space]` side condition is dischargeable by something in this
repository. That is the same disclaimer `ComplexAnalytic.isCoveringMap_base_sq` carries for the
covering rung, and for the same reason.

## The counterexample, and it is about `g` finite and not about `g` finite étale

`Oka/AnalyticSpace/Finite.lean` records that the closed half of finiteness does **not** cancel
along a merely finite second factor, with the line with two origins over the line as the witness,
and says of that reasoning: *"That is a statement about topological spaces, it is compiled nowhere
below."* `TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` below compiles the statement.

**The witness here is not the line with two origins**, and the difference matters in one direction
only. Both are non-Hausdorff spaces mapping onto a Hausdorff one, closed with finite fibres, with
a section-like map into them that is not closed. The line with two origins is the sharper example,
because its fold map is additionally a **local homeomorphism** — so it exhibits the failure at a
hypothesis one step stronger than the one below, which is *closed with finite fibres* and nothing
more. Building it needs a gluing of two copies of `ℝ` along an open subset, which this repository
does not have; the two-point indiscrete space is the same phenomenon with the local homeomorphism
dropped, and it costs three definitions.

**What both witnesses have in common is the point of the whole section**: the two indistinguishable
points lie in no common evenly covered neighbourhood on which the fold is injective, which is
exactly the ingredient `IsCoveringMap.isClosedMap_of_comp` (`Oka/Topology/Covering/Basic.lean`)
consumes. So neither is a counterexample to the cancellation that file proves, and the reason is
in one word: `TwoIndiscrete.fold` is not a covering map.

**The declarations of this section are outside `ComplexAnalytic`**, because none of them mentions
a complex analytic space, a germ or a holomorphic function; they are a topological counterexample
about a two-element type. They are in the `TwoIndiscrete` namespace and not at the root, so that
every citation of them elsewhere is a dotted name and is therefore checked by
`scripts/check_docstring_names.py`, which reads dotted names only — the bare `TwoIndiscrete` in
this sentence is checked by nothing, and is the head of the four names that are.
`ComplexAnalytic.punctured` in `OkaTest/HolomorphicMapOpen.lean` is the existing precedent for a
test file declaring outside `ComplexAnalytic`, and its module docstring records what that cost.

## What is not here

* **No counterexample to the cancellation itself.** Nothing below exhibits a finite étale `g` with
  a non-cancelling `f`, and nothing could: that statement is a theorem.
* **Nothing about the `[T2Space]` hypothesis.** The counterexample below is against weakening
  *finite étale* to *finite*; it says nothing about whether the Hausdorff condition on the middle
  space can be dropped, which `Oka/AnalyticSpace/FiniteEtaleCancel.lean` records as unasked.
* **No line with two origins**, for the reason above, so nothing here witnesses the failure at a
  second factor that is a local homeomorphism. That gap is the same one before this file and is
  narrower by exactly the local homeomorphism.
* **No second non-vacuity.** `ComplexAnalytic.sq` is the only non-isomorphism available, so the
  cancellation is exercised at one morphism, composed with itself.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

/-! ### The counterexample: `g` finite is not enough

Everything in this section is about topological spaces; nothing in it is analytic. -/

/-- **A two-element type carrying the indiscrete topology**, whose two points are topologically
indistinguishable — the two origins of the line with two origins, with the line removed.

A type synonym rather than `Bool` itself, so that the `⊤` topology below does not have to compete
with `Bool`'s own instance, which is discrete. -/
def TwoIndiscrete : Type := Bool

/-- The indiscrete topology: the only open sets are `∅` and everything
(`TopologicalSpace.isOpen_top_iff`). -/
instance : TopologicalSpace TwoIndiscrete := ⊤

instance : Finite TwoIndiscrete := inferInstanceAs (Finite Bool)

/-- **The fold of the two indistinguishable points to a point.** Closed with finite fibres — it is
the analogue of the map that makes the line with two origins finite over the line — and it is not
a covering map, since the only neighbourhood of the image is the whole of `TwoIndiscrete`, on
which it is not injective. -/
def TwoIndiscrete.fold : TwoIndiscrete → PUnit := fun _ ↦ ⟨⟩

/-- **One of the two indistinguishable points, as a map from a point.** A section of
`TwoIndiscrete.fold`, and the map that fails to be closed. -/
def TwoIndiscrete.pt : PUnit → TwoIndiscrete := fun _ ↦ (true : Bool)

/-- **The image of `TwoIndiscrete.pt` is not closed**, because the complement of a single point of
`TwoIndiscrete` is neither empty nor everything, hence not open. -/
theorem TwoIndiscrete.not_isClosedMap_pt : ¬ IsClosedMap TwoIndiscrete.pt := by
  intro h
  have hcl : IsClosed (TwoIndiscrete.pt '' Set.univ) := h _ isClosed_univ
  rw [← isOpen_compl_iff, TopologicalSpace.isOpen_top_iff] at hcl
  have hmem : (false : Bool) ∈ (TwoIndiscrete.pt '' Set.univ)ᶜ := by
    rintro ⟨x, -, hx⟩
    exact Bool.noConfusion hx
  have hnot : (true : Bool) ∉ (TwoIndiscrete.pt '' Set.univ)ᶜ := fun hc ↦ hc ⟨⟨⟩, trivial, rfl⟩
  rcases hcl with hcl | hcl
  · rw [hcl] at hmem; exact hmem
  · rw [hcl] at hnot; exact hnot (Set.mem_univ _)

/-- **Closedness does not cancel along a map that is merely closed with finite fibres**, which is
the statement `Oka/AnalyticSpace/Finite.lean` records as compiled nowhere.

`TwoIndiscrete.fold` is closed, has finite fibres and is continuous;
`TwoIndiscrete.fold ∘ TwoIndiscrete.pt` is closed, being a map between one-point spaces; and
`TwoIndiscrete.pt` is continuous and **not** closed. So the covering hypothesis
of `IsCoveringMap.isClosedMap_of_comp` cannot be weakened to this, and
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_isFiniteEtale` cannot have `IsFiniteEtale g`
weakened to `IsFinite g`.

Stated as one conjunction rather than five theorems because each conjunct alone is uninteresting;
what is being exhibited is that they hold together. -/
theorem TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp :
    Continuous TwoIndiscrete.pt ∧ Continuous TwoIndiscrete.fold ∧
      IsClosedMap TwoIndiscrete.fold ∧
      (∀ x, (TwoIndiscrete.fold ⁻¹' {x}).Finite) ∧
      IsClosedMap (TwoIndiscrete.fold ∘ TwoIndiscrete.pt) ∧ ¬ IsClosedMap TwoIndiscrete.pt :=
  ⟨continuous_top, continuous_const, fun _ _ ↦ isClosed_discrete _, fun _ ↦ Set.toFinite _,
    fun _ _ ↦ isClosed_discrete _, TwoIndiscrete.not_isClosedMap_pt⟩

namespace ComplexAnalytic

/-! ### The non-vacuity: cancellation at the squaring map -/

/-- **The cancellation applies to a morphism that is not an isomorphism.**
`ComplexAnalytic.sq` is finite étale, so `sq ≫ sq` is, and the punctured line is Hausdorff — so
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` returns `IsFiniteEtale sq`.

**The conclusion is the hypothesis it was derived from**, since `IsFiniteEtale (sq ≫ sq)` comes
from `ComplexAnalytic.isFiniteEtale_sq` through the composition instance. This is not evidence
about `z ↦ z²`; it is evidence that the three hypotheses of the cancellation can hold at once at a
morphism that is not an isomorphism, which no statement about identities would show. See the
module docstring, and `ComplexAnalytic.isCoveringMap_base_sq` for the same disclaimer one rung
down. -/
theorem isFiniteEtale_sq_of_comp : AnalyticSpace.IsFiniteEtale (ComplexAnalytic.sq.{u}) :=
  haveI := isFiniteEtale_sq.{u}
  AnalyticSpace.isFiniteEtale_of_comp ComplexAnalytic.sq.{u} ComplexAnalytic.sq.{u}

end ComplexAnalytic

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.FiniteMorphism

/-!
# Finite étale cancellation: a non-vacuity, and the separation axiom that cannot be dropped

Two unrelated things about `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`
(`Oka/AnalyticSpace/LocalIso.lean`): that its hypotheses are satisfiable outside the isomorphisms,
and that the one hypothesis it costs — `[T2Space]` on the middle space — is not removable.

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

## The counterexample, and it is about the separation axiom

`Oka/AnalyticSpace/Finite.lean` records that the closed half of finiteness does **not** cancel
unconditionally, with the line with two origins over the line as the witness, and used to say of
that reasoning: *"That is a statement about topological spaces, it is compiled nowhere below."*
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` below compiles a statement of that shape.

**What it exhibits is a middle space that is not Hausdorff**, and that — not anything about the
second factor — is what makes it a counterexample. Its second factor `TwoIndiscrete.fold` is
continuous, closed and has finite fibres, so it is as strong a second factor as the finite rung
knows how to ask for; the composite is closed and the first factor is not. The conjunction
therefore says, in one statement, that
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` cannot have its `[T2Space Y]` dropped,
and `TwoIndiscrete.not_t2Space` is included as a conjunct so that the statement says which
hypothesis it is attacking rather than leaving it to be read off `⊤`.

**It does not say the second factor cannot be weakened**, and there is nothing there to say:
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` asks nothing of the second factor at
all, so there is no hypothesis on it to attack. An earlier draft of this file presented the same
witness as ruling out a *finite* second factor in favour of a *finite étale* one; that reading is
wrong, because it varies two things at once — the second factor and the separation axiom — and
attributes the failure to the one that turns out to be inert.

**The witness here is not the line with two origins**, and the difference matters in one direction
only. Both are non-Hausdorff spaces mapping onto a Hausdorff one, closed with finite fibres, with
a section-like map into them that is not closed. The line with two origins is the sharper example,
because its fold map is additionally a **local homeomorphism** — so it exhibits the failure at a
second factor one step stronger than the one below. Building it needs a gluing of two copies of
`ℝ` along an open subset, which this repository does not have; the two-point indiscrete space is
the same phenomenon with the local homeomorphism dropped, and it costs four declarations.

**The declarations of this section are outside `ComplexAnalytic`**, because none of them mentions
a complex analytic space, a germ or a holomorphic function; they are a topological counterexample
about a two-element type. They are in the `TwoIndiscrete` namespace and not at the root, so that
every citation of them elsewhere is a dotted name and is therefore checked by
`scripts/check_docstring_names.py`, which reads dotted names only — the bare `TwoIndiscrete` in
this sentence is checked by nothing, and is the head of the five names that are. The existing
precedent for a test file declaring outside `ComplexAnalytic` is the root-namespace `punctured` of
`OkaTest/HolomorphicMapOpen.lean`, which is a *different declaration* from
`ComplexAnalytic.punctured` in `OkaTest/FiniteMorphism.lean`; that file's module docstring records
what having two of them cost, and it is the reason this section takes a namespace rather than the
root.

## What is not here

* **No counterexample to the cancellation itself.** Nothing below exhibits a Hausdorff middle
  space with a non-cancelling `f`, and nothing could: that statement is a theorem.
* **Nothing about the second factor.** The cancellation asks nothing of it, so there is no
  hypothesis there to attack and none is attacked.
* **Nothing about the local-isomorphism rung.** `ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp`
  needs no separation axiom, so the witness below bears on the finite rung only, which is where
  the whole cost of `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` sits.
* **No line with two origins**, for the reason above, so nothing here witnesses the failure at a
  second factor that is a local homeomorphism. That gap is the same one as before this file and is
  narrower by exactly the local homeomorphism.
* **No second non-vacuity.** `ComplexAnalytic.sq` is the only non-isomorphism available, so the
  cancellation is exercised at one morphism, composed with itself.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

/-! ### The counterexample: a non-Hausdorff middle space is enough

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
the analogue of the map that makes the line with two origins finite over the line — and as strong
a second factor as `ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` could be asked
about, since that statement asks nothing of its second factor at all. -/
def TwoIndiscrete.fold : TwoIndiscrete → PUnit := fun _ ↦ ⟨⟩

/-- **One of the two indistinguishable points, as a map from a point.** A section of
`TwoIndiscrete.fold`, and the map that fails to be closed. -/
def TwoIndiscrete.pt : PUnit → TwoIndiscrete := fun _ ↦ (true : Bool)

/-- **The two points are not separated by open sets.** Two open sets containing them are each
either empty or everything, so each is everything and they are not disjoint.

This is the hypothesis the conjunction below attacks, stated on its own so that the conjunction
can name it rather than leave a reader to unfold `⊤`. -/
theorem TwoIndiscrete.not_t2Space : ¬ T2Space TwoIndiscrete := by
  intro h
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ :=
    @t2_separation TwoIndiscrete _ h (true : Bool) (false : Bool) (by simp)
  have hut : u = Set.univ :=
    (TopologicalSpace.isOpen_top_iff u |>.1 hu).resolve_left fun hc ↦ by rw [hc] at hxu; exact hxu
  have hvt : v = Set.univ :=
    (TopologicalSpace.isOpen_top_iff v |>.1 hv).resolve_left fun hc ↦ by rw [hc] at hyv; exact hyv
  rw [hut, hvt, Set.disjoint_iff_inter_eq_empty, Set.univ_inter] at huv
  exact (Set.univ_eq_empty_iff.1 huv).elim ((true : Bool) : TwoIndiscrete)

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

/-- **Closedness does not cancel over a middle space that is not Hausdorff**, whatever the second
factor is. This is the statement `Oka/AnalyticSpace/Finite.lean` records as compiled nowhere.

The middle space is `TwoIndiscrete`, and `TwoIndiscrete.not_t2Space` is the first conjunct because
it is the hypothesis being attacked. Beside it: `TwoIndiscrete.fold` is continuous, closed and has
finite fibres — everything a second factor could be asked for, and
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space` asks it for nothing —
`TwoIndiscrete.fold ∘ TwoIndiscrete.pt` is closed, being a map between one-point spaces, and
`TwoIndiscrete.pt` is continuous and **not** closed.

So `[T2Space Y]` cannot be dropped from
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space`, and neither can it be replaced by any
hypothesis on the second factor that this witness already satisfies.

Stated as one conjunction rather than six theorems because each conjunct alone is uninteresting;
what is being exhibited is that they hold together. -/
theorem TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp :
    ¬ T2Space TwoIndiscrete ∧
      Continuous TwoIndiscrete.pt ∧ Continuous TwoIndiscrete.fold ∧
      IsClosedMap TwoIndiscrete.fold ∧
      (∀ x, (TwoIndiscrete.fold ⁻¹' {x}).Finite) ∧
      IsClosedMap (TwoIndiscrete.fold ∘ TwoIndiscrete.pt) ∧ ¬ IsClosedMap TwoIndiscrete.pt :=
  ⟨TwoIndiscrete.not_t2Space, continuous_top, continuous_const,
    fun _ _ ↦ isClosed_discrete _, fun _ ↦ Set.toFinite _,
    fun _ _ ↦ isClosed_discrete _, TwoIndiscrete.not_isClosedMap_pt⟩

namespace ComplexAnalytic

/-! ### The non-vacuity: cancellation at the squaring map -/

/-- **The cancellation applies to a morphism that is not an isomorphism.**
`ComplexAnalytic.sq` is finite étale, so `sq ≫ sq` is and `sq` is a local isomorphism, and the
punctured line is Hausdorff — so `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` returns
`IsFiniteEtale sq`.

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

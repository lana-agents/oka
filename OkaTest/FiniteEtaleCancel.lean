/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.FiniteMorphism

/-!
# Finite étale cancellation: a non-vacuity, a separation axiom that cannot be dropped, and the
same axiom one rung down

Statements about `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`
(`Oka/AnalyticSpace/LocalIso.lean`) — that its hypotheses are satisfiable outside the
isomorphisms, and that the one hypothesis it costs, `[T2Space]` on the middle space, is not
removable — together with the same kind of statement about the criterion that rung is proved
from, `IsClosedMap.isCoveringMap_of_isLocalHomeomorph` in `Oka/Topology/Covering/Basic.lean`,
whose `[T2Space E]` is refuted by the same space.

**The heading above read *Finite étale cancellation: a non-vacuity, and the separation axiom that
cannot be dropped*, and the sentence beside it opened *Two unrelated things about
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`*, until 2026-09-07**, when
`LineTwoOrigins.not_isCoveringMap_fold` was added and the second of those became false: the
material below is no longer all about that one theorem. The enumeration replaces the numeral
rather than raising it, for the reason `Oka/Topology/Covering/Basic.lean`'s own heading gives — a
count of a file's contents goes false on the next append and an enumeration does not.

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
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` and
`LineTwoOrigins.not_isClosedMap_inc_of_isClosedMap_comp` below compile statements of that shape,
and `LineTwoOrigins.not_isClosedMap_inc_of_isClosedMap_comp` is at the very space that paragraph
argues with.

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

**The line with two origins is here too**, as
`LineTwoOrigins.not_isClosedMap_inc_of_isClosedMap_comp`, and it is the sharper of the two
witnesses in two respects: its fold map is additionally a **local homeomorphism**, and its middle
space is additionally **T1**. Both are non-Hausdorff spaces
mapping onto a Hausdorff one, closed with finite fibres, with a section-like map into them that is
not closed; the two-element space is that phenomenon with the local homeomorphism and the T1 axiom
dropped, and it is the cheaper one.

**This paragraph used to say that building the line with two origins needs a gluing of two copies
of `ℝ` along an open subset, which this repository does not have. That was wrong when it was
written**, and not merely out of date: no gluing, no `GlueData` and no quotient is taken below.
The carrier is `ℝ ⊕ Unit` and the construction is a single `IsOpen` predicate on it, so the
sharper witness never needed anything from `Oka/` at all. What the weaker one still buys is
brevity: it is the shorter section by some way, and it is the one
`Oka/AnalyticSpace/Finite.lean` reaches for first.

**Which conjunct does the sharper work is worth saying, because it is not the T1 axiom.** The
local homeomorphism is what reaches
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`, whose second factor carries `[IsLocalIso]`:
a reader of the weaker witness alone could ask whether that hypothesis buys the `[T2Space]` back,
and nothing below the two-element space answers it. T1 answers a different question — whether a
separation axiom weaker than Hausdorff would have sufficed — and **no finite space could have
answered that one**, a finite T1 space being discrete.

**The declarations of both counterexample sections are outside `ComplexAnalytic`**, because none
of them mentions a complex analytic space, a germ or a holomorphic function; they are topological
counterexamples about a two-element type and about a sum type. They are in the `TwoIndiscrete` and
`LineTwoOrigins` namespaces and not at the root, so that every citation of them elsewhere is a
dotted name and is therefore checked by `scripts/check_docstring_names.py`, which reads dotted
names only — the bare namespace names in this sentence are checked by nothing, and are the heads
of the dotted ones that are.

**Both carriers are `def`s and neither is an `abbrev`, and that is load-bearing rather than
stylistic.** A reducible carrier makes the topology declared on it an instance on the *underlying*
type, which then wins against Mathlib's own for every file importing this one:
`LineTwoOrigins` as an `abbrev` put `#synth TopologicalSpace (ℝ ⊕ Unit)` at the topology below
instead of at `instTopologicalSpaceSum`, and `LineTwoOrigins.not_isClosedMap_inc` was then
readable as the false claim that the canonical injection into a disjoint union is not closed.
`TwoIndiscrete` had it right first and this section copies it. **For the same reason no statement
in the `LineTwoOrigins` namespace mentions `Sum.inl` or `Sum.inr`**: a term written with a
constructor has its
type inferred as the sum and carries the sum topology with it, so `LineTwoOrigins.inc` and
`LineTwoOrigins.origin₂` exist to keep every statement at the intended type.

The existing
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
  needs no separation axiom, so of the two halves of
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` the witness below bears on the finite one
  only, which is where that theorem's whole cost sits. **This bullet read *so the witness below
  bears on the finite rung only, which is where the whole cost of
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` sits* until 2026-09-07**, when
  `LineTwoOrigins.not_isCoveringMap_fold` was added and gave the same space a bearing on a
  theorem that is neither rung, `IsClosedMap.isCoveringMap_of_isLocalHomeomorph`. It was exact
  when written — nothing below then said anything about that criterion — and the push that
  falsified it is the one that rewrote it, which is what a dated record is for. The repair
  narrows the scope to the two halves of the cancellation rather than raising a count.
* **No analytic counterexample.** Both witnesses are topological, and neither is or becomes a
  complex analytic space: the line with two origins is not Hausdorff, so it is not one, and
  nothing below builds a morphism of complex analytic spaces. What they establish is that the
  separation axiom cannot be dropped from the *topological* cancellation the analytic one is
  proved from, and — through `LineTwoOrigins.not_isCoveringMap_fold` — that it cannot be dropped
  from `IsClosedMap.isCoveringMap_of_isLocalHomeomorph` either.
  **This bullet ended at *proved from* until 2026-09-07**; the clause is appended and the
  sentence before it is unchanged.
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

Stated as one conjunction rather than as separate theorems because each conjunct alone is
uninteresting; what is being exhibited is that they hold together. -/
theorem TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp :
    ¬ T2Space TwoIndiscrete ∧
      Continuous TwoIndiscrete.pt ∧ Continuous TwoIndiscrete.fold ∧
      IsClosedMap TwoIndiscrete.fold ∧
      (∀ x, (TwoIndiscrete.fold ⁻¹' {x}).Finite) ∧
      IsClosedMap (TwoIndiscrete.fold ∘ TwoIndiscrete.pt) ∧ ¬ IsClosedMap TwoIndiscrete.pt :=
  ⟨TwoIndiscrete.not_t2Space, continuous_top, continuous_const,
    fun _ _ ↦ isClosed_discrete _, fun _ ↦ Set.toFinite _,
    fun _ _ ↦ isClosed_discrete _, TwoIndiscrete.not_isClosedMap_pt⟩

/-! ### The sharper counterexample: the line with two origins

Also purely topological. What this section adds over the one above is a second factor that is a
**local homeomorphism** and a middle space that is **T1**, which the two-element space cannot be.
-/

/-- **The line with two origins**: a copy of `ℝ`, plus one extra point that is a second origin.

The first copy is a full line and the second origin is glued to it along the punctured line by the
topology below, so this carrier is the classical space and not a quotient of `ℝ × Bool` — **no
quotient and no gluing datum is taken**, and the module docstring above used to say one was
needed.

**It is a `def` and not an `abbrev`, for the reason `TwoIndiscrete` above is one.** An `abbrev` is
reducible, so the topology declared below would be an instance on `ℝ ⊕ Unit` itself and would win
against `instTopologicalSpaceSum` for every file importing this one — making
`LineTwoOrigins.not_isClosedMap_inc` readable as a false statement about Mathlib's disjoint union.
`Sum.inl` and `Sum.inr` are therefore not used in any statement of this section either:
`LineTwoOrigins.inc` and `LineTwoOrigins.origin₂` are, because a term written with the
constructors has its type inferred as `ℝ ⊕ Unit` and takes the sum topology with it. -/
def LineTwoOrigins : Type := ℝ ⊕ Unit

namespace LineTwoOrigins

/-- **The first copy of the line, included into the space.** -/
def inc : ℝ → LineTwoOrigins := Sum.inl

/-- **The second origin.** -/
def origin₂ : LineTwoOrigins := Sum.inr ()

/-- **The reals sitting under a subset of the line with two origins**, i.e. the part of it in the
first copy, read as a subset of `ℝ`. Every clause of the topology below is stated in terms of it. -/
def under (U : Set LineTwoOrigins) : Set ℝ := inc ⁻¹' U

/-- Membership in `LineTwoOrigins.under`, which is `Iff.rfl` and exists so that `simp` can use it
without unfolding the carrier — the thing this section may not let it do. -/
@[simp]
theorem mem_under {U : Set LineTwoOrigins} {x : ℝ} : x ∈ under U ↔ inc x ∈ U := Iff.rfl

/-- **The inclusion of the first copy is injective.** -/
theorem inc_injective : Function.Injective inc :=
  fun _ _ h ↦ Sum.inl_injective (α := ℝ) (β := Unit) h

/-- **The second origin is not in the first copy.** -/
@[simp]
theorem inc_ne_origin₂ (x : ℝ) : inc x ≠ origin₂ := by simp [inc, origin₂]

/-- **Every point is in the first copy or is the second origin**, which is the case analysis every
proof below runs and the reason none of them needs to see the carrier. -/
theorem eq_inc_or_eq_origin₂ (w : LineTwoOrigins) : (∃ x, w = inc x) ∨ w = origin₂ := by
  match w with
  | Sum.inl x => exact Or.inl ⟨x, rfl⟩
  | Sum.inr () => exact Or.inr rfl

/-- **The topology: a set is open when the reals under it are open, and, if it contains the second
origin, when those reals together with `0` are open.**

The second clause is the whole construction. It makes every neighbourhood of the second origin
contain a punctured neighbourhood of `0` in the first copy, which is what stops the two origins
from being separated and is the only thing this space is for. Note it does **not** ask that the
second origin's neighbourhoods contain `LineTwoOrigins.inc 0`; that is what keeps the space T1.

The three fields are the three closure conditions, each proved by rewriting `LineTwoOrigins.under`
through the set operation and applying the corresponding fact about `ℝ`. The union field is the
only one that is not immediate: the `{0}` in the second clause is not distributed by a union, so
the witness member is pulled out and the rest of the family is added back around it. -/
instance : TopologicalSpace LineTwoOrigins where
  IsOpen U := IsOpen (under U) ∧ (origin₂ ∈ U → IsOpen (under U ∪ {0}))
  isOpen_univ := by
    refine ⟨?_, fun _ ↦ ?_⟩
    · have huniv : under (Set.univ : Set LineTwoOrigins) = Set.univ := rfl
      rw [huniv]
      exact isOpen_univ
    · have huniv : under (Set.univ : Set LineTwoOrigins) ∪ {0} = Set.univ := by
        rw [show under (Set.univ : Set LineTwoOrigins) = Set.univ from rfl]
        exact Set.univ_union _
      rw [huniv]
      exact isOpen_univ
  isOpen_inter s t hs ht := by
    refine ⟨hs.1.inter ht.1, fun h ↦ ?_⟩
    have huit : under (s ∩ t) ∪ {0} = (under s ∪ {0}) ∩ (under t ∪ {0}) := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_singleton_iff, mem_under]
      tauto
    rw [huit]
    exact (hs.2 h.1).inter (ht.2 h.2)
  isOpen_sUnion S hS := by
    have hu : under (⋃₀ S) = ⋃ s ∈ S, under s := by
      ext x
      simp only [mem_under, Set.mem_sUnion, Set.mem_iUnion, exists_prop]
    refine ⟨hu ▸ isOpen_biUnion fun s hs ↦ (hS s hs).1, fun h ↦ ?_⟩
    obtain ⟨s, hsS, hs⟩ := h
    have husu : under (⋃₀ S) ∪ {0} = (under s ∪ {0}) ∪ (⋃ t ∈ S, under t) := by
      rw [hu]
      ext x
      exact ⟨fun hx ↦ hx.elim (fun h ↦ Or.inr h) (fun h ↦ Or.inl (Or.inr h)),
        fun hx ↦ hx.elim (fun h ↦ h.elim (fun h ↦ Or.inl (Set.mem_biUnion hsS h)) Or.inr) Or.inl⟩
    rw [husu]
    exact ((hS s hsS).2 hs).union (isOpen_biUnion fun t ht ↦ (hS t ht).1)

/-- **The topology, as an iff**, so that a caller does not have to know that `IsOpen` on this
space is the structure field. It is `Iff.rfl`; it exists to be cited. -/
theorem isOpen_iff (U : Set LineTwoOrigins) :
    IsOpen U ↔ IsOpen (under U) ∧ (origin₂ ∈ U → IsOpen (under U ∪ {0})) := Iff.rfl

/-- **The fold of the two origins onto one**: the identity on the first copy, and the second
origin to `0`. This is the second factor of the counterexample, and
`LineTwoOrigins.isLocalHomeomorph_fold` is what makes it stronger than `TwoIndiscrete.fold`. -/
def fold : LineTwoOrigins → ℝ := Sum.elim id (fun _ ↦ 0)

/-- The fold is the identity on the first copy. -/
@[simp]
theorem fold_inc (x : ℝ) : fold (inc x) = x := rfl

/-- The fold sends the second origin to `0`. -/
@[simp]
theorem fold_origin₂ : fold origin₂ = 0 := rfl

/-- **The second sheet**: the punctured first copy together with the second origin. Together with
`Set.range LineTwoOrigins.inc` it covers the space, and `LineTwoOrigins.fold` is injective on
each. -/
def sheet₂ : Set LineTwoOrigins := (Set.range inc \ {inc 0}) ∪ {origin₂}

/-- **The first copy is an open subset**, and it does not contain the second origin — which is
the topology's conditional clause, and is what the `rintro` discharges. -/
theorem isOpen_range_inc : IsOpen (Set.range inc) := by
  refine ⟨?_, ?_⟩
  · have hu : under (Set.range inc) = Set.univ := by ext x; simp
    rw [hu]
    exact isOpen_univ
  · rintro ⟨x, hx⟩
    exact absurd hx (inc_ne_origin₂ x)

/-- The reals under the second sheet are the punctured line. -/
theorem under_sheet₂ : under sheet₂ = {x : ℝ | x ≠ 0} := by
  ext x
  simp only [mem_under, sheet₂, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff,
    Set.mem_setOf_eq, inc_ne_origin₂, or_false]
  exact ⟨fun h hx ↦ h.2 (by rw [hx]), fun h ↦ ⟨⟨x, rfl⟩, fun hc ↦ h (inc_injective hc)⟩⟩

/-- **The second sheet is open.** Its second clause is where the topology's `∪ {0}` pays: the
punctured line together with `0` is the whole line. -/
theorem isOpen_sheet₂ : IsOpen sheet₂ := by
  refine ⟨under_sheet₂ ▸ isOpen_ne, fun _ ↦ ?_⟩
  rw [under_sheet₂]
  have hcov : {x : ℝ | x ≠ 0} ∪ {0} = Set.univ := by ext x; by_cases h : x = 0 <;> simp [h]
  rw [hcov]
  exact isOpen_univ

/-- **The inclusion of the first copy is continuous**: the preimage of an open set is the reals
under it, which is the topology's first clause. -/
theorem continuous_inc : Continuous inc := by
  rw [continuous_def]
  intro V hV
  exact hV.1

/-- **The fold is continuous.** The reals under `fold ⁻¹' V`, together with `0`, are `V` itself —
`0` is already in `V` in the case where the second clause is asked for. -/
theorem continuous_fold : Continuous fold := by
  rw [continuous_def]
  intro V hV
  refine ⟨hV, fun h ↦ ?_⟩
  have hV0 : under (fold ⁻¹' V) ∪ {0} = V := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, mem_under, Set.mem_preimage, fold_inc]
    refine ⟨fun hx ↦ hx.elim id (fun h0 ↦ ?_), fun hx ↦ Or.inl hx⟩
    rw [h0]
    simpa using h
  rw [hV0]
  exact hV

/-- **The fold is an open map**, and this is the observation that makes the local-homeomorphism
proof below short rather than a second pair of hand computations.

`fold '' W` is the reals under `W` when `W` misses the second origin and those reals together with
`0` when it does not — so **the two clauses of the topology are exactly the two cases of this
statement**, and each case is discharged by the clause it matches. -/
theorem isOpenMap_fold : IsOpenMap fold := by
  intro W hW
  by_cases h : origin₂ ∈ W
  · have himg : fold '' W = under W ∪ {0} := by
      ext x
      refine ⟨?_, ?_⟩
      · rintro ⟨w, hw, rfl⟩
        rcases eq_inc_or_eq_origin₂ w with ⟨y, rfl⟩ | rfl
        · exact Or.inl (by simpa using hw)
        · exact Or.inr (by simp)
      · rintro (hx | hx)
        · exact ⟨inc x, hx, by simp⟩
        · exact ⟨origin₂, h, by simpa using hx.symm⟩
    rw [himg]
    exact hW.2 h
  · have himg : fold '' W = under W := by
      ext x
      refine ⟨?_, fun hx ↦ ⟨inc x, hx, by simp⟩⟩
      rintro ⟨w, hw, rfl⟩
      rcases eq_inc_or_eq_origin₂ w with ⟨y, rfl⟩ | rfl
      · simpa using hw
      · exact absurd hw h
    rw [himg]
    exact hW.1

/-- **The fold restricted to an open set on which it is injective is an open embedding.**

The open-map obligation is `LineTwoOrigins.isOpenMap_fold` at the intersection of the ambient open
set with the one that induces the subtype's open set; nothing about which open set it is is used,
which is why both sheets go through this one lemma. -/
theorem isOpenEmbedding_restrict {U : Set LineTwoOrigins} (hU : IsOpen U)
    (hinj : Set.InjOn fold U) : IsOpenEmbedding (U.restrict fold) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_fold.comp continuous_subtype_val) (fun a b hab ↦ Subtype.ext (hinj a.2 b.2 hab)) ?_
  intro V hV
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
  have himg : U.restrict fold '' (Subtype.val ⁻¹' W) = fold '' (W ∩ U) := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨a, ha⟩, haw, rfl⟩
      exact ⟨a, ⟨haw, ha⟩, rfl⟩
    · rintro ⟨a, ⟨haw, hau⟩, rfl⟩
      exact ⟨⟨a, hau⟩, haw, rfl⟩
  rw [himg]
  exact isOpenMap_fold _ (hW.inter hU)

/-- **The fold is a local homeomorphism**, which is what `TwoIndiscrete.fold` is not and is the
reason this witness reaches `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`'s second factor.

`IsLocalHomeomorph`'s definition asks for a global equation between the map and the coercion of a
partial homeomorphism, which is the wrong door for a map defined by cases;
`isLocalHomeomorph_iff_isOpenEmbedding_restrict` asks instead for an open neighbourhood of each
point on which the restriction is an open embedding, and the two sheets are those neighbourhoods.
Injectivity on the second sheet is four cases and the two mixed ones are where `0` being excluded
from the punctured part is used. -/
theorem isLocalHomeomorph_fold : IsLocalHomeomorph fold := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro w
  rcases eq_inc_or_eq_origin₂ w with ⟨y, rfl⟩ | rfl
  · refine ⟨_, isOpen_range_inc.mem_nhds ⟨y, rfl⟩, isOpenEmbedding_restrict isOpen_range_inc ?_⟩
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
    exact congrArg inc (by simpa using h)
  · refine ⟨_, isOpen_sheet₂.mem_nhds (Or.inr rfl), isOpenEmbedding_restrict isOpen_sheet₂ ?_⟩
    rintro a ha b hb h
    rcases ha with ⟨⟨p, rfl⟩, hp⟩ | ha <;> rcases hb with ⟨⟨q, rfl⟩, hq⟩ | hb
    · exact congrArg inc (by simpa using h)
    · simp only [Set.mem_singleton_iff] at hb
      subst hb
      simp only [fold_inc, fold_origin₂] at h
      exact absurd (by simp [h]) hp
    · simp only [Set.mem_singleton_iff] at ha
      subst ha
      simp only [fold_inc, fold_origin₂] at h
      exact absurd (by simp [h.symm]) hq
    · simp only [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]

/-- **The fold is a closed map.** Complementing, a closed set either contains the second origin,
in which case its image is the complement of a punctured open set, or it does not, in which case
its image is the complement of an open set. Both complements are open in `ℝ`. -/
theorem isClosedMap_fold : IsClosedMap fold := by
  intro C hC
  rw [← isOpen_compl_iff] at hC ⊢
  by_cases h : origin₂ ∈ C
  · have hco : (fold '' C)ᶜ = under Cᶜ ∩ {x : ℝ | x ≠ 0} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq, mem_under]
      refine ⟨fun hx ↦ ⟨fun hc ↦ hx ⟨inc x, hc, by simp⟩,
        fun hc ↦ hx ⟨origin₂, h, by simp [hc]⟩⟩, ?_⟩
      rintro ⟨h1, h2⟩ ⟨w, hw, rfl⟩
      rcases eq_inc_or_eq_origin₂ w with ⟨y, rfl⟩ | rfl
      · exact h1 (by simpa using hw)
      · exact h2 (by simp)
    rw [hco]
    exact hC.1.inter isOpen_ne
  · have hco : (fold '' C)ᶜ = under Cᶜ := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_image, mem_under]
      refine ⟨fun hx hc ↦ hx ⟨inc x, hc, by simp⟩, ?_⟩
      rintro h1 ⟨w, hw, rfl⟩
      rcases eq_inc_or_eq_origin₂ w with ⟨y, rfl⟩ | rfl
      · exact h1 (by simpa using hw)
      · exact h hw
    rw [hco]
    exact hC.1

/-- **Every fibre of the fold is finite** — a singleton away from `0` and the two origins over it.
Stated as `Set.Finite` to match `TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp`. -/
theorem finite_fibre_fold (x : ℝ) : (fold ⁻¹' {x}).Finite := by
  refine Set.Finite.subset (Set.toFinite ({inc x, origin₂} : Set LineTwoOrigins)) ?_
  rintro w hw
  rcases eq_inc_or_eq_origin₂ w with ⟨y, rfl⟩ | rfl
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, fold_inc] at hw
    simp [hw]
  · simp

/-- **The two origins are not separated by open sets.**

Any open set containing the second origin has the reals under it together with `0` open, so it
contains a punctured neighbourhood of `0` in the first copy; any open set containing `inc 0` has
the reals under it open around `0`. The two real neighbourhoods meet at some `x ≠ 0`, and
`LineTwoOrigins.inc x` is then in both open sets.

`Filter.nonempty_of_mem` at `𝓝[≠] (0 : ℝ)` gives a point of the set and **not** a point different
from `0`; the intersection with `{0}ᶜ` has to be taken before it is applied. -/
theorem not_t2Space : ¬ T2Space LineTwoOrigins := by
  intro hT2
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ :=
    @t2_separation LineTwoOrigins _ hT2 (inc 0) origin₂ (inc_ne_origin₂ 0)
  have hnhds : under U ∩ (under V ∪ {0}) ∈ 𝓝 (0 : ℝ) :=
    (hU.1.inter (hV.2 hyV)).mem_nhds ⟨hxU, Or.inr rfl⟩
  have hpunct : (under U ∩ (under V ∪ {0})) ∩ {(0 : ℝ)}ᶜ ∈ 𝓝[≠] (0 : ℝ) :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hnhds) self_mem_nhdsWithin
  obtain ⟨x, ⟨hxU', hxV'⟩, hx0⟩ := Filter.nonempty_of_mem hpunct
  exact Set.disjoint_left.mp hUV hxU' (hxV'.resolve_right (by simpa using hx0))

/-- **Points are closed**, which the two-element indiscrete space is not: it answers the question
a reader may fairly ask of that one, whether `T1` on the middle space would already have been
enough. It would not, and **no finite space could have said so**, a finite T1 space being
discrete. -/
instance t1Space : T1Space LineTwoOrigins where
  t1 w := by
    rw [← isOpen_compl_iff]
    rcases eq_inc_or_eq_origin₂ w with ⟨y, rfl⟩ | rfl
    · refine ⟨?_, fun _ ↦ ?_⟩
      · have hu : under ({inc y}ᶜ : Set LineTwoOrigins) = {x : ℝ | x ≠ y} := by
          ext x
          simp only [mem_under, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
          exact ⟨fun h hx ↦ h (by rw [hx]), fun h hx ↦ h (inc_injective hx)⟩
        rw [hu]
        exact isOpen_ne
      · have hu : under ({inc y}ᶜ : Set LineTwoOrigins) ∪ {0} = ({y} \ {0} : Set ℝ)ᶜ := by
          ext x
          simp only [mem_under, Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
            Set.mem_sdiff]
          exact ⟨fun h hy ↦ h.elim (fun h1 ↦ h1 (by rw [hy.1])) (fun h1 ↦ hy.2 h1),
            fun h ↦ by by_cases hx : x = 0
                       · exact Or.inr hx
                       · exact Or.inl fun hc ↦ h ⟨inc_injective hc, hx⟩⟩
        rw [hu]
        exact (Set.Finite.isClosed (Set.toFinite _)).isOpen_compl
    · refine ⟨?_, ?_⟩
      · have hu : under ({origin₂}ᶜ : Set LineTwoOrigins) = Set.univ := by
          ext x
          simp
        rw [hu]
        exact isOpen_univ
      · rintro h
        exact absurd rfl h

/-- **The inclusion of the first copy is not a closed map.** Its image is the whole space minus
the second origin, and that single point is not open: the reals under it are empty, and the empty
set together with `0` is `{0}`, which is not open in `ℝ`. -/
theorem not_isClosedMap_inc : ¬ IsClosedMap inc := by
  intro h
  have hcl : IsClosed (inc '' (Set.univ : Set ℝ)) := h _ isClosed_univ
  rw [← isOpen_compl_iff] at hcl
  have hco : (inc '' (Set.univ : Set ℝ))ᶜ = {origin₂} := by
    ext w
    rcases eq_inc_or_eq_origin₂ w with ⟨y, rfl⟩ | rfl
    · simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_univ, true_and, Set.mem_singleton_iff,
        inc_ne_origin₂, iff_false, not_not]
      exact ⟨y, rfl⟩
    · simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_univ, true_and, Set.mem_singleton_iff,
        iff_true]
      rintro ⟨y, hy⟩
      exact inc_ne_origin₂ y hy
  rw [hco] at hcl
  have hu : under ({origin₂} : Set LineTwoOrigins) ∪ {0} = {0} := by
    ext x
    simp
  have h0 : IsOpen ({0} : Set ℝ) := hu ▸ hcl.2 rfl
  have hempty : ({0} : Set ℝ) ∩ {(0 : ℝ)}ᶜ ∈ 𝓝[≠] (0 : ℝ) :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (h0.mem_nhds rfl)) self_mem_nhdsWithin
  obtain ⟨x, hx, hx0⟩ := Filter.nonempty_of_mem hempty
  exact hx0 hx

/-- **Closedness does not cancel over a middle space that is not Hausdorff, even when the second
factor is a local homeomorphism and the middle space is T1.**

This is the statement `Oka/AnalyticSpace/Finite.lean` argues for with the line with two origins,
and it is that space. Beside `LineTwoOrigins.not_t2Space`, which is the hypothesis under attack:
the middle space is T1; `LineTwoOrigins.fold` is continuous, closed, has finite fibres **and is a
local homeomorphism**; `fold ∘ inc` is the identity of `ℝ`, hence closed; and
`LineTwoOrigins.inc` is continuous and **not** closed.

What it adds to `TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` is the local
homeomorphism and the T1 axiom. The local homeomorphism is what matters for the finite étale rung:
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` asks `[IsLocalIso g]`, so a reader of the
weaker witness alone could still ask whether that hypothesis buys the `[T2Space]` back. It does
not. Neither does T1.

Stated as one conjunction rather than as separate theorems for the reason the weaker witness
gives: each conjunct alone is uninteresting, and what is exhibited is that they hold together. -/
theorem not_isClosedMap_inc_of_isClosedMap_comp :
    ¬ T2Space LineTwoOrigins ∧ T1Space LineTwoOrigins ∧
      Continuous inc ∧ Continuous fold ∧
      IsLocalHomeomorph fold ∧ IsClosedMap fold ∧
      (∀ x, (fold ⁻¹' {x}).Finite) ∧
      IsClosedMap (fold ∘ inc) ∧ ¬ IsClosedMap inc :=
  ⟨not_t2Space, t1Space, continuous_inc, continuous_fold, isLocalHomeomorph_fold, isClosedMap_fold,
    finite_fibre_fold, fun C hC ↦ by simpa [Function.comp_def, Set.image_image] using hC,
    not_isClosedMap_inc⟩

/-! #### The same space, one rung down: the separation axiom of the covering criterion -/

/-- **The fold is not a covering map**, although it is a closed local homeomorphism with finite
fibres onto a Hausdorff space.

`IsCoveringMap.isSeparatedMap` is Mathlib's, in `Mathlib/Topology/Covering/Basic.lean`, and
`IsSeparatedMap.t2Space` (`Oka/Topology/SeparatedMap.lean`) turns it into Hausdorffness of the
source over a Hausdorff base — which `LineTwoOrigins.not_t2Space` refutes. So the argument runs
through separatedness and not through the trivialisation: nothing here inspects an evenly covered
neighbourhood. -/
theorem not_isCoveringMap_fold : ¬ IsCoveringMap fold := fun h ↦
  not_t2Space (h.isSeparatedMap.t2Space continuous_fold)

/-- **The `[T2Space E]` of `IsClosedMap.isCoveringMap_of_isLocalHomeomorph` cannot be dropped.**

`¬ T2Space LineTwoOrigins` is the hypothesis that fails and `¬ IsCoveringMap LineTwoOrigins.fold`
is the conclusion that fails with it. The conjuncts beside them say how little else is wrong:
`LineTwoOrigins.fold` is a closed map, a local homeomorphism and has finite fibres, which is
everything that criterion asks for other than the separation axiom, and its target is `ℝ`, which
is Hausdorff — so the criterion is one instance argument away from applying and its conclusion is
false.

**This is a different hypothesis of a different theorem from the one
`LineTwoOrigins.not_isClosedMap_inc_of_isClosedMap_comp` attacks**, at the same space and out of
the same four facts: that one is `[T2Space Y]` on the middle space of
`ComplexAnalytic.AnalyticSpace.isFinite_of_comp_of_t2Space`, this one is `[T2Space E]` on the
source of the covering criterion. `Oka/Topology/Covering/Basic.lean` asserted that this one is not
removable and named no witness until 2026-09-07; this is that witness.

Stated as one conjunction rather than as separate theorems for the reason
`LineTwoOrigins.not_isClosedMap_inc_of_isClosedMap_comp` gives. -/
theorem not_isCoveringMap_fold_of_not_t2Space :
    IsClosedMap fold ∧ (∀ x, (fold ⁻¹' {x}).Finite) ∧ IsLocalHomeomorph fold ∧
      T2Space ℝ ∧ ¬ T2Space LineTwoOrigins ∧ ¬ IsCoveringMap fold :=
  ⟨isClosedMap_fold, finite_fibre_fold, isLocalHomeomorph_fold, inferInstance, not_t2Space,
    not_isCoveringMap_fold⟩

end LineTwoOrigins

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

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.ConnectedCover
import Oka.AnalyticSpace.FundamentalGroup
import Oka.Topology.Homeomorph.Lemmas

/-!
# The pieces of the decomposition are the connected components of the total space

`Oka/AnalyticSpace/FundamentalGroup.lean`'s
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isConnected_decomposition` writes a
cover separated over a Hausdorff, preconnected, nonempty base as a finite coproduct of
**connected** ones, where *connected* is `CategoryTheory.PreGaloisCategory.IsConnected`, a
condition on an **object of the category**; `Oka/AnalyticSpace/ConnectedCover.lean` then shows
that condition equivalent to `ConnectedSpace` of the piece's total space. **Neither says that the
pieces are the topological connected components of the total space of the cover**, and that is
what this file proves. Both of those modules' docstrings record the absence and the second prices
the three steps between; taxis #2094 is the filing, and **the bullet this file closes is
`Oka/AnalyticSpace/ConnectedCover.lean`'s fifth `## What is not here`**, whose three steps are
the three definitions below in order.

**A coproduct in the category is not a disjoint union of spaces until someone says so**, and that
is the content: `CategoryTheory.Limits.HasColimit` gives an object with a universal property and
nothing about its points. The three steps are the coproduct against this repository's own
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigma`, that object's total space against
the `Sigma` type, and an isomorphism of the category against a homeomorphism.

## The universe crossing, which is the one step that is not a citation

`…SeparatedFiniteEtaleOver.sigma` takes `{ι : Type u}` and
`…exists_isConnected_decomposition`'s index type is `Type`, so the two cannot be compared as they
stand: `SeparatedFiniteEtaleOver.sigma f` at that `f` fails to elaborate. What closes it is the
crossing `…SeparatedFiniteEtaleOver.hasFiniteCoproducts` already makes for `Fin n` —
`CategoryTheory.Limits.HasColimit.isoOfEquivalence` at `CategoryTheory.Discrete.equivalence` of
`Equiv.ulift` — made here for an arbitrary finite `ι`, which is
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.coprodIsoSigma`. **The index type of every
statement below is therefore `ULift.{u} ι` and not `ι`**, and the two theorems at the foot of the
file quantify over a `Type u` index, which is what `ULift` delivers.

## A bijection is not enough, and that is why two of the three steps are homeomorphisms

`ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso` and
`…SeparatedFiniteEtaleOver.surjective_base_left_of_isIso` are the bijectivity and surjectivity of
an isomorphism on total spaces and **neither carries a connected component**: a continuous
bijection can merge components, the identity from a discrete space to an indiscrete one being the
standard witness. The two steps that had to be homeomorphisms are the one out of the `Sigma` type
— `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeo`, added to
`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean` for this file and read here through
`ComplexAnalytic.AnalyticSpace.sigmaHomeo` — and the one out of an isomorphism,
`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`, which was already in the tree.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.coprodIsoSigma`: **a coproduct of
  finitely many separated covers is their disjoint union**, across the universe gap between the
  two index types.
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.homeoLeftOfIso`: **an isomorphism of
  separated covers is a homeomorphism on total spaces.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.sigmaHomeoLeft` and
  `…SeparatedFiniteEtaleOver.coprodHomeoLeft`: **the total space of a disjoint union, and of a
  coproduct, of separated covers is the disjoint union of their total spaces.**

## Main results

- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.exists_isConnected_homeomorph`: **a
  cover separated over a Hausdorff, preconnected, nonempty base is homeomorphic to the disjoint
  union of finitely many connected covers, and under that homeomorphism the image of each piece is
  a connected component of the total space.**
- `ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.finite_connectedComponents_left`: **so
  such a cover has finitely many connected components.**

## What the two mirror-tree files supply, and why there are two of them

The topology is not here. `connectedComponent_sigmaMk` (`Oka/Topology/Connected/Clopen.lean`)
says the components of a disjoint union of connected spaces are its members, and
`Homeomorph.connectedComponent_sigma` and `Homeomorph.finite_connectedComponents_of_sigma`
(`Oka/Topology/Homeomorph/Lemmas.lean`) transport that along a homeomorphism. **Neither mentions
an analytic space and both are stated for a bare family of topological spaces**, which is what
`README.md`'s mirror-tree section asks; the split between the two files is by destination and
that second docstring prices it at the ten modules the other direction would cost.

## What the import costs, measured in the environment and not by a scan

At the commit this file is cut from, `import Oka` brings **5534** modules; at the commit that adds
it, **5537**. **The cost is three modules and the three are this file and the two mirror-tree
files beside it**: by a set difference over `Lean.Environment.allImportedModuleNames` in a
`run_cmd`, the only names in the second closure and not the first are `Oka` itself,
`Oka.AnalyticSpace.ConnectedComponents`, `Oka.Topology.Connected.Clopen` and
`Oka.Topology.Homeomorph.Lemmas`, so **no Mathlib module enters and the marginal Mathlib cost is
zero**. This file's three `import` lines name `Oka/AnalyticSpace/ConnectedCover.lean`,
`Oka/AnalyticSpace/FundamentalGroup.lean` and `Oka/Topology/Homeomorph/Lemmas.lean`, of which
`Oka.lean` already imported the first two, and the two mirror files import their own Mathlib
targets, which are in the `Oka` closure already.

**A marginal import cost is a figure about the importer at a commit**, so both ends are dated
here rather than written in the present tense, exactly as
`Oka/AnalyticSpace/GaloisCategory.lean`, `Oka/AnalyticSpace/FundamentalGroup.lean` and
`Oka/AnalyticSpace/ConnectedCover.lean` do for their own.

**What the two census scripts return, at the commit this file is cut from and at the commit that
adds it.** `scripts/guard_coverage.py` moves **1986 → 2003** guards under `OkaTest/Axioms/` — the
sixteen declarations this push adds, of which ten are the new modules' and six are the three
appended to each of `Oka/AnalyticSpace/Sigma.lean` and
`Oka/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`, and **one that is older than this
push**, `ComplexAnalytic.AnalyticSpace.sigma_toLocallyRingedSpace`, which this push advertises for
the first time and which its guard file says so of — and **1487 → 1496** advertised in
a `## Main results`, in **226 → 229** files; *guarded and advertised nowhere* goes **641 → 649**,
*in both* **1345 → 1354**, and *advertised from another file* **85 → 86**, the one being
`AlgebraicGeometry.LocallyRingedSpace.sigmaHomeo` cited in `Oka/AnalyticSpace/Sigma.lean`'s
`## Main results`. **The row this repository reads that script for is *unguarded*, and it is flat
at 142 in 60 files** — it was **143 in 61** before that seventeenth guard, which is how the newly
advertised name was found. *Abbreviated citations, not counted* is flat at **30, four of them
dotted**.
`scripts/check_docstring_names.py` goes **17761 → 17878** backticked names (4327 → 4352 distinct)
and **273 → 311** elided citations (150 → 156), **0 unresolved at both ends**, **6** resolving
under more than one namespace at both, and **232 → 234** dotless (112 → 114), against a
`scripts/DumpEnvNames.lean` dump that moves **338225 → 338244** — **332545 → 332561** declarations
and **5680 → 5683** modules, which is this push's sixteen declarations and its three modules.

**Six declarations, and six is the whole of this module.** `scripts/DumpOkaDecls.lean` writes
**6** rows at `Oka.AnalyticSpace.ConnectedComponents` — no equation lemma, no match lemma, no
congruence lemma — with **1** at `Oka.Topology.Connected.Clopen` and **3** at
`Oka.Topology.Homeomorph.Lemmas`, and the dump total moves **4957 → 4973**.

## What is not here

* **No statement that the decomposition is unique**, as a family or up to isomorphism, and no
  statement that the `ι` of the two theorems is determined by the cover. What is proved is that
  *some* such family exists; `CategoryTheory.PreGaloisCategory.has_decomp_connected_components'`,
  which supplies it, is an existence statement and nothing here inverts it.
* **No `Equiv` between the index type and `ConnectedComponents` of the total space.**
  `…SeparatedFiniteEtaleOver.finite_connectedComponents_left` goes through a surjection from the
  index type and not through a bijection, so the count of components is bounded by the count of
  pieces and is not shown to equal it. **Equality would be a theorem**: it needs the pieces to be
  pairwise distinct as components, which is their nonemptiness — true, `ConnectedSpace` carrying
  `Nonempty`, but not proved below.
* **Nothing about the *degree* of the cover or the cardinality of a fibre.**
  `Oka/AnalyticSpace/Degree.lean` is where that theory is, and no statement here reads a fibre:
  the decomposition theorem this file consumes takes no point of the base and neither does
  anything below.
* **No restatement of `…SeparatedFiniteEtaleOver.exists_isConnected_decomposition`**, which stays
  in `Oka/AnalyticSpace/FundamentalGroup.lean` untouched. What this file changes is what a reader
  may conclude from it, and the record of that change is beside the two bullets it narrows —
  there and in `Oka/AnalyticSpace/ConnectedCover.lean` — rather than in the theorem.
* **Nothing about the topologist's fundamental group.**
  `Oka/AnalyticSpace/FundamentalGroup.lean`'s `## What is not here` records that absence, and
  nothing here bears on it: this file relates a coproduct to a disjoint union of spaces, not two
  groups.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace ComplexAnalytic.AnalyticSpace

variable {X : AnalyticSpace.{u}} [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)]

omit [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)] in
/-- **The coproduct of a finite family of separated covers is their disjoint union**, across the
universe gap between the index type of the one and the index type of the other.

**Two isomorphisms composed, and the first is the whole of the universe crossing.**
`CategoryTheory.Limits.HasColimit.isoOfEquivalence` at `CategoryTheory.Discrete.equivalence` of
`Equiv.ulift` re-indexes the coproduct by `ULift.{u} ι`, which is the move
`ComplexAnalytic.AnalyticSpace.SeparatedFiniteEtaleOver.hasFiniteCoproducts` already makes for
`Fin n`; `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso` at
`…SeparatedFiniteEtaleOver.isColimitCofanSigma` then identifies that coproduct with the disjoint
union, both cocones now being indexed by a `Type u`.

**The hypotheses are `ι : Type` and `[Finite ι]` and nothing about the base**, which is why the
two of the ambient variable block are omitted: a coproduct of separated covers exists over any
analytic space, `…SeparatedFiniteEtaleOver.hasFiniteCoproducts` asking nothing of it, and so does
`…SeparatedFiniteEtaleOver.sigma`.

**`ι : Type` rather than `ι : Type u` is what the consumer has**:
`…SeparatedFiniteEtaleOver.exists_isConnected_decomposition` produces an index type in `Type`,
because `CategoryTheory.PreGaloisCategory.has_decomp_connected_components'` does. At a matching
universe the first isomorphism is unnecessary and the second is the whole statement. -/
noncomputable def SeparatedFiniteEtaleOver.coprodIsoSigma {ι : Type} [Finite ι]
    (f : ι → SeparatedFiniteEtaleOver.{u} X) :
    (∐ f) ≅ SeparatedFiniteEtaleOver.sigma fun i : ULift.{u} ι ↦ f i.down := by
  refine (?_ : (∐ f) ≅ ∐ fun i : ULift.{u} ι ↦ f i.down) ≪≫
    (colimit.isColimit (Discrete.functor fun i : ULift.{u} ι ↦ f i.down)).coconePointUniqueUpToIso
      (SeparatedFiniteEtaleOver.isColimitCofanSigma _)
  exact HasColimit.isoOfEquivalence (Discrete.equivalence Equiv.ulift.symm)
    (Discrete.natIso fun _ ↦ Iso.refl _)

omit [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)] in
/-- **An isomorphism of separated covers is a homeomorphism on total spaces.**

`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso` at the image of the isomorphism under the three
forgetful functors between this category and `AlgebraicGeometry.LocallyRingedSpace` — the
morphism-property comma category's, the comma category's and
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` — and **every functor preserves
isomorphisms**, so nothing has to be established about the composite.

**What this buys over the two statements already in the tree is the openness.**
`ComplexAnalytic.AnalyticSpace.bijective_base_of_isIso` and
`…SeparatedFiniteEtaleOver.surjective_base_left_of_isIso` are the bijectivity and the surjectivity
of the same map, and **a bijection carries no connected component**; the consumer below is a
statement about components, so it is this and not either of those.

**Nothing is asked of the base**, for the reason
`…SeparatedFiniteEtaleOver.surjective_base_left_of_isIso` gives of itself: the morphism arrives
with an inverse and no covering-space theory produces one. -/
noncomputable def SeparatedFiniteEtaleOver.homeoLeftOfIso {A B : SeparatedFiniteEtaleOver.{u} X}
    (e : A ≅ B) : (A.left : Type u) ≃ₜ (B.left : Type u) :=
  AlgebraicGeometry.LocallyRingedSpace.homeoOfIso
    (((MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _) ⋙
      AnalyticSpace.forgetToLocallyRingedSpace).mapIso e)

omit [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)] in
/-- **The total space of a disjoint union of separated covers is the disjoint union of their
total spaces.**

`ComplexAnalytic.AnalyticSpace.sigmaHomeo` at the members' total spaces, and **there is nothing to
transport**: the total space of `…SeparatedFiniteEtaleOver.sigma` is
`ComplexAnalytic.AnalyticSpace.sigma` of the members' total spaces by `rfl`, the object of this
category being the ambient construction wrapped in `CategoryTheory.MorphismProperty.Over.mk` and
the wrapper leaving the apex alone.

**This is the step that is a theorem about spaces and not about the category**, and one level down
it is `AlgebraicGeometry.LocallyRingedSpace.sigmaHomeo`, whose own docstring records that the
locally-ringed-space file had priced it at a route it does not take. -/
noncomputable def SeparatedFiniteEtaleOver.sigmaHomeoLeft {ι : Type u} [Finite ι]
    (f : ι → SeparatedFiniteEtaleOver.{u} X) :
    (Σ i, ((f i).left : Type u)) ≃ₜ ((SeparatedFiniteEtaleOver.sigma f).left : Type u) :=
  AnalyticSpace.sigmaHomeo fun i ↦ (f i).left

omit [T2Space (X : Type u)] [PreconnectedSpace (X : Type u)] in
/-- **The total space of a coproduct of finitely many separated covers is the disjoint union of
their total spaces.**

The three steps composed, in the order the module docstring names them: the coproduct against the
disjoint union, that disjoint union's total space against the `Sigma` type, and the isomorphism
against a homeomorphism. **The `Sigma` type is indexed by `ULift.{u} ι`**, which is where the
universe crossing of `…SeparatedFiniteEtaleOver.coprodIsoSigma` surfaces in a statement rather
than in a proof. -/
noncomputable def SeparatedFiniteEtaleOver.coprodHomeoLeft {ι : Type} [Finite ι]
    (f : ι → SeparatedFiniteEtaleOver.{u} X) :
    (Σ i : ULift.{u} ι, ((f i.down).left : Type u)) ≃ₜ ((∐ f).left : Type u) :=
  (SeparatedFiniteEtaleOver.sigmaHomeoLeft fun i : ULift.{u} ι ↦ f i.down).trans
    (SeparatedFiniteEtaleOver.homeoLeftOfIso (SeparatedFiniteEtaleOver.coprodIsoSigma f).symm)

variable [Nonempty (X : Type u)]

/-- **Every cover separated over a Hausdorff, preconnected, nonempty base is the disjoint union of
finitely many connected covers, and the pieces are the connected components of its total space.**

This is `…SeparatedFiniteEtaleOver.exists_isConnected_decomposition` with its isomorphism replaced
by a homeomorphism and one clause added. **The first conjunct is the decomposition theorem's own
conclusion, unchanged and unweakened** — `CategoryTheory.PreGaloisCategory.IsConnected` of each
piece, which `…SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace` makes `ConnectedSpace` of
its total space — and the second is what this file adds: under the homeomorphism the component of
a point of the `i`-th piece is the image of the whole of that piece.

**The index type is `ULift.{u} ι` of the decomposition theorem's `ι`**, and the module docstring
says why; nothing else about the family is changed, the `f` below being the theorem's own
composed with `ULift.down`.

**`[Nonempty]` of the base is inherited and not added.**
`…SeparatedFiniteEtaleOver.exists_isConnected_decomposition` binds it, so this statement does too;
`…SeparatedFiniteEtaleOver.isConnected_iff_connectedSpace`, which the proof also spends, does
not. **Over an empty base the statement is not vacuous but the hypothesis is not available**,
which is a note about where the hypothesis comes from and not an argument that it is needed. -/
theorem SeparatedFiniteEtaleOver.exists_isConnected_homeomorph
    (A : SeparatedFiniteEtaleOver.{u} X) :
    ∃ (ι : Type u) (_ : Finite ι) (f : ι → SeparatedFiniteEtaleOver.{u} X)
      (e : (Σ i, ((f i).left : Type u)) ≃ₜ (A.left : Type u)),
      (∀ i, PreGaloisCategory.IsConnected (f i)) ∧
        ∀ (i : ι) (x : ((f i).left : Type u)),
          connectedComponent (e ⟨i, x⟩) = e '' Set.range (Sigma.mk i) := by
  obtain ⟨ι, _, f, e, hconn⟩ := SeparatedFiniteEtaleOver.exists_isConnected_decomposition A
  haveI : ∀ i : ULift.{u} ι, ConnectedSpace ((f i.down).left : Type u) := fun i ↦
    haveI := hconn i.down
    SeparatedFiniteEtaleOver.connectedSpace_of_isConnected _
  set e' : (Σ i : ULift.{u} ι, ((f i.down).left : Type u)) ≃ₜ (A.left : Type u) :=
    (SeparatedFiniteEtaleOver.coprodHomeoLeft f).trans
      (SeparatedFiniteEtaleOver.homeoLeftOfIso e) with he'
  exact ⟨ULift.{u} ι, inferInstance, fun i ↦ f i.down, e', fun i ↦ hconn i.down,
    fun i x ↦ Homeomorph.connectedComponent_sigma e' i x⟩

/-- **Such a cover has finitely many connected components.**

`Homeomorph.finite_connectedComponents_of_sigma` at the homeomorphism above, the index type being
finite and every piece connected. **The bound is the number of pieces and the statement is not
that the two counts agree**; the module docstring's `## What is not here` says what equality would
additionally need.

**This is the first statement in this repository about `ConnectedComponents` of anything.** At the
commit this file is cut from the token `connectedComponent` occurs **0** times in the
comment-stripped code of `Oka/` and `OkaTest/`, which is the census
`Oka/AnalyticSpace/ConnectedCover.lean`'s `## What is not here` published when it priced the three
steps. -/
theorem SeparatedFiniteEtaleOver.finite_connectedComponents_left
    (A : SeparatedFiniteEtaleOver.{u} X) : Finite (ConnectedComponents (A.left : Type u)) := by
  obtain ⟨ι, _, f, e, hconn, -⟩ := SeparatedFiniteEtaleOver.exists_isConnected_homeomorph A
  haveI : ∀ i, ConnectedSpace ((f i).left : Type u) := fun i ↦
    haveI := hconn i
    SeparatedFiniteEtaleOver.connectedSpace_of_isConnected _
  exact e.finite_connectedComponents_of_sigma

end ComplexAnalytic.AnalyticSpace

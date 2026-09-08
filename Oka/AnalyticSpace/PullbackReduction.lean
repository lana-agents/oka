/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.CutOutFibreProduct
import Oka.AnalyticSpace.PullbackLimit

/-!
# The reduction to local models: every cospan of complex analytic spaces has a fibre product

`Oka/AnalyticSpace/PullbackLimit.lean` ends at
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover`: a cospan `f : X ⟶ Z`, `g : Y ⟶ Z`
has a fibre product as soon as `X` is covered by opens `Uᵢ` along which the base change of `g`
**already exists**. Its *What this does not do* says in terms that nothing in this repository
produces such a family for a general cospan, and that the reduction which would is unmeasured.

**This file is that reduction**, and at its foot
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` is an instance. Its shape is
`Mathlib/AlgebraicGeometry/Pullbacks.lean`'s — six declarations after `hasPullback_of_cover`,
`AlgebraicGeometry.Scheme.Pullback.affine_hasPullback` through
`AlgebraicGeometry.Scheme.Pullback.instHasPullbacks` — with local models in place of affine
schemes.

## The base case is an equality of spaces, not an isomorphism, and everything else follows from
## that

`ComplexAnalytic.exists_restrict_eq_ofCutOut` says every point of `X` has an open neighbourhood
`U` with `X.restrict U = ComplexAnalytic.AnalyticSpace.ofCutOut hcut` **on the nose**. That
equality — and not an isomorphism onto a local model — is what makes the reduction transcription
rather than transport: `ComplexAnalytic.IsPresentedLocalModel` below packages the existential, and
every one of the three covering steps discharges its base case by `obtain … rfl` and
`infer_instance`, with no comparison morphism named and no limit carried across an equivalence.

`ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` is the base case itself, and it asks exactly
what Mathlib's asks: all three objects of the cospan literally
`ComplexAnalytic.AnalyticSpace.ofCutOut`. Nothing here reproves it.

## The three covering steps, and the index type is the carrier

`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` fixes `I : Type u` while
`X : ComplexAnalytic.AnalyticSpace.{u}`, so the carrier of `X` is a legal index type and it is the
cheapest one: the family is `fun x ↦ U x` for `U` chosen at each point, and the covering
hypothesis is `fun x ↦ ⟨x, hxU x⟩`. **No auxiliary index type, no `Σ`-type and no subtype of
`ComplexAnalytic.AnalyticSpace.Opens` appears**, which is the universe check
`Oka/AnalyticSpace/PullbackGlue.lean` asks a writer to make before the proof rather than after.

* `ComplexAnalytic.AnalyticSpace.hasPullback_of_isPresentedLocalModel_right` covers `X`;
* `ComplexAnalytic.AnalyticSpace.hasPullback_of_isPresentedLocalModel_base` covers `Y`, twice
  through `CategoryTheory.Limits.hasPullback_symmetry`, which is Mathlib's
  `AlgebraicGeometry.Scheme.Pullback.base_affine_hasPullback` verbatim;
* `ComplexAnalytic.AnalyticSpace.hasPullback` covers `X` by the preimages of a covering family of
  opens of `Z`.

## Where the two categories differ, and it is one paste and not an associativity argument

Mathlib's fourth step, `AlgebraicGeometry.Scheme.Pullback.left_affine_comp_pullback_hasPullback`,
covers `X` by the *schemes* `X ×_Z Zᵢ` and reaches the instance hypothesis through
`CategoryTheory.Limits.hasPullback_assoc_symm`. **Neither the cover by pullback objects nor the
associativity argument is available or needed here**, because
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` takes a family of
`ComplexAnalytic.AnalyticSpace.Opens` rather than a family of open immersions, so the analytic
family is `fun z ↦ (TopologicalSpace.Opens.map f.toLRSHom.base).obj (W z)` — preimages, with no
pullback object named.

What replaces the associativity argument is one application of
`CategoryTheory.IsPullback.paste_vert`, in
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict_comp`:

    Q ---------------------> X|f⁻¹W
    |                           |
    |                   restrictHom f W
    v                           v
   Y|g⁻¹W --restrictHom g W--> Z|W
    |                           |
    |                     ofRestrict W
    v                           v
    Y ----------- g ----------> Z

The lower square is `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` at `g` and `W`,
transposed; the upper one is the fibre product of the two restricted morphisms over `Z.restrict W`,
which is a local model, so the step before supplies it. Pasting gives a pullback square whose left
leg into `Z` is `restrictHom f W ≫ Z.ofRestrict W`, and
`ComplexAnalytic.AnalyticSpace.restrictHom_fac` rewrites that to
`X.ofRestrict (f ⁻¹' W) ≫ f` — the very morphism `hasPullback_of_cover`'s instance hypothesis is
about. **That rewrite is the whole of the step**, and the transport across
`ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict` the filing of this work expected to
need does not appear.

## Main definitions

- `ComplexAnalytic.IsPresentedLocalModel`: an analytic space **is** the space presented by some
  cut-out datum, as an equality and not up to isomorphism.

## Main results

- `ComplexAnalytic.exists_isPresentedLocalModel_restrict`: every point has an open neighbourhood
  whose open subspace is one.
- `ComplexAnalytic.AnalyticSpace.hasPullback_of_isPresentedLocalModel`: a cospan of three of them
  has a fibre product.
- `ComplexAnalytic.AnalyticSpace.hasPullback_of_isPresentedLocalModel_right`: the same with the
  first object arbitrary.
- `ComplexAnalytic.AnalyticSpace.hasPullback_of_isPresentedLocalModel_base`: the same with only
  the base a local model.
- `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict_comp`: the instance hypothesis
  `ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` asks for, at one member of a
  covering family of the base.
- `ComplexAnalytic.AnalyticSpace.hasPullback`: **every** cospan of complex analytic spaces has a
  fibre product.
- `ComplexAnalytic.AnalyticSpace.hasPullbacks`: the category has pullbacks.

## What this does not do

* **It does not identify the fibre product with anything.** `CategoryTheory.Limits.HasPullback` is
  `Prop`-valued and the two instances below are proofs of it; the object
  `CategoryTheory.Limits.pullback f g` denotes exists, and no declaration here says what its points
  or its structure sheaf are. `ComplexAnalytic.AnalyticSpace.Pullback.glued` is the space the
  construction produces and `Oka/AnalyticSpace/PullbackLimit.lean` keeps that identification for a
  cospan with a cover in hand; **nothing keeps it for a general cospan**, because the three
  covering steps choose their covers with `Classical.choice`.
* **Nothing about the fibre product on points.** No declaration in this repository identifies the
  carrier of a fibre product of analytic spaces with a set of pairs, and this file adds none.
* **It does not make `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` stable under base change.**
  That is a statement about a class of morphisms across a general square and does not follow from
  a fibre product existing; `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` carries it across its
  own square and nothing carries it across a general one. The bullet in
  `Oka/AnalyticSpace/FiniteEtaleOver.lean` that enumerates what the Galois axioms still need is
  unchanged by this file except in its first clause, which is retired there.
* **It says nothing about `CategoryTheory.Limits.HasEqualizers` or about finite limits.** A
  category with pullbacks and a terminal object has finite limits;
  `ComplexAnalytic.AnalyticSpace` has no terminal object in this repository — the one-point
  analytic space is not constructed — so `CategoryTheory.Limits.HasFiniteLimits` does not follow
  and is not claimed.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace ComplexAnalytic

/-- **An analytic space is a *presented* local model if it is, on the nose, the space some cut-out
datum presents.**

This is `ComplexAnalytic.IsLocalModel` with two differences, and both are the point. That
predicate is about a `AlgebraicGeometry.LocallyRingedSpace` and asserts only that *some* closed
immersion into an open subset of `ℂ^n` cuts it out; this one is about a
`ComplexAnalytic.AnalyticSpace` and asserts an **equality of analytic spaces** with the space
`ComplexAnalytic.AnalyticSpace.ofCutOut` builds from that datum, so it pins the `ℂ`-algebra
structure as well as the locally ringed space.

**The equality is what the whole file spends.** A hypothesis `S = …ofCutOut hcut` with `S` a bound
variable is discharged by `obtain … rfl`, after which a goal about `S` is a goal about a local
model and `ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` applies by instance search. An
isomorphism `S ≅ …ofCutOut hcut` would instead have to be carried across every statement, and
`Oka/AnalyticSpace/OpenSubspace.lean`'s `ComplexAnalytic.restrict_eq_ofCutOut` exists precisely so
that it need not be.

**Stated in the `ComplexAnalytic` namespace and not in `ComplexAnalytic.AnalyticSpace`**, as
`ComplexAnalytic.exists_restrict_eq_ofCutOut` is and for its reason: inside a declaration whose
name begins `AnalyticSpace.` the tokens `complexAffineSpace` and `Opens` resolve to
`ComplexAnalytic.AnalyticSpace.complexAffineSpace` and `ComplexAnalytic.AnalyticSpace.Opens`
rather than to the locally ringed space and to `TopologicalSpace.Opens`, and the statement would
then be about a different `ℂ^n`. -/
def IsPresentedLocalModel (S : AnalyticSpace.{u}) : Prop :=
  ∃ (n k : ℕ) (V : Opens (complexAffineSpace.{u} n)) (M : LocallyRingedSpace.{u})
    (i : M ⟶ (complexAffineSpace.{u} n).restrict V.isOpenEmbedding)
    (f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤))
    (hcut : IsCutOutBy i f), S = AnalyticSpace.ofCutOut hcut

/-- **Every point of a complex analytic space has an open neighbourhood whose open subspace is a
presented local model.**

`ComplexAnalytic.exists_restrict_eq_ofCutOut` with the ambient locally ringed space of the datum
existentially quantified rather than read off the statement, which is the only difference between
the two conclusions. **This is the form the three covering steps consume**: each of them calls
`choose` on it and gets a family of opens, a membership and a family of local-model witnesses in
one line.

The locally ringed space that gets quantified is
`X.toLocallyRingedSpace.restrict U.isOpenEmbedding` and it is supplied as `_`; nothing downstream
of this file mentions it. -/
theorem exists_isPresentedLocalModel_restrict (X : AnalyticSpace.{u}) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsPresentedLocalModel (X.restrict U) := by
  obtain ⟨U, hxU, n, k, V, i, f, hcut, heq⟩ := exists_restrict_eq_ofCutOut X x
  exact ⟨U, hxU, n, k, V, _, i, f, hcut, heq⟩

namespace AnalyticSpace

variable {X Y Z : AnalyticSpace.{u}}

/-! ### The base case -/

/-- **A cospan of three presented local models has a fibre product.**

`AlgebraicGeometry.Scheme.Pullback.affine_hasPullback`'s analogue, and it is three `obtain`s and
`infer_instance`: each hypothesis is an equality with a bound variable on the left, so `rfl`
substitutes it away, and what is left is
`ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` at the three data — an `instance` in
`Oka/AnalyticSpace/CutOutFibreProduct.lean`, found by search and not applied by name.

**Mathlib's base case is not free and this one is.** There it is `Spec` preserving limits, spelt
out; here the fibre product of two local models over a third was built by taxis #1830 as a zero
locus inside the product, and the work is in that file. -/
theorem hasPullback_of_isPresentedLocalModel (hX : IsPresentedLocalModel X)
    (hY : IsPresentedLocalModel Y) (hZ : IsPresentedLocalModel Z) (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g := by
  obtain ⟨n, k, V, MX, iX, fX, hcutX, rfl⟩ := hX
  obtain ⟨m, l, W, MY, iY, fY, hcutY, rfl⟩ := hY
  obtain ⟨p, q, U, MZ, iZ, fZ, hcutZ, rfl⟩ := hZ
  infer_instance

/-! ### The three covering steps -/

/-- **A cospan whose second object and whose base are presented local models has a fibre product**,
the first object being arbitrary.

`AlgebraicGeometry.Scheme.Pullback.affine_affine_hasPullback`'s analogue.
`ComplexAnalytic.exists_isPresentedLocalModel_restrict` chooses an open `U x` at every point of
`X`; the family is indexed by the carrier of `X`, which lives in the `Type u` that
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` asks of its index type; and the
instance hypothesis at `x` is the base case at `X.restrict (U x)`, `Y` and `Z`. -/
theorem hasPullback_of_isPresentedLocalModel_right (hY : IsPresentedLocalModel Y)
    (hZ : IsPresentedLocalModel Z) (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g := by
  choose U hxU hU using fun x : X ↦ exists_isPresentedLocalModel_restrict X x
  haveI : ∀ x : X, HasPullback (X.ofRestrict (U x) ≫ f) g :=
    fun x ↦ hasPullback_of_isPresentedLocalModel (hU x) hY hZ _ g
  exact Pullback.hasPullback_of_cover U f g fun x ↦ ⟨x, hxU x⟩

/-- **A cospan whose base is a presented local model has a fibre product**, both other objects
being arbitrary.

`AlgebraicGeometry.Scheme.Pullback.base_affine_hasPullback`'s analogue, and Mathlib's proof
transcribes: cover `Y` instead of `X`, and wrap the whole thing in
`CategoryTheory.Limits.hasPullback_symmetry` **twice** — once inside, to read the step above as a
statement about the cospan taken the other way round, and once outside, to turn the fibre product
of `g` and `f` into one of `f` and `g`.

The two symmetries are not cancelling: the inner one is applied at each member of the cover, to a
cospan whose *first* object is a local model, and the outer one once, to the whole. -/
theorem hasPullback_of_isPresentedLocalModel_base (hZ : IsPresentedLocalModel Z)
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g := by
  choose U hyU hU using fun y : Y ↦ exists_isPresentedLocalModel_restrict Y y
  haveI : ∀ y : Y, HasPullback (Y.ofRestrict (U y) ≫ g) f := fun y ↦ by
    haveI := hasPullback_of_isPresentedLocalModel_right (hU y) hZ f (Y.ofRestrict (U y) ≫ g)
    exact hasPullback_symmetry _ _
  haveI := Pullback.hasPullback_of_cover U g f fun y ↦ ⟨y, hyU y⟩
  exact hasPullback_symmetry _ _

/-! ### The instance hypothesis at one member of a cover of the base -/

/-- **The base change of `g` along the inclusion of the preimage of `W` exists as soon as
`Z.restrict W` is a presented local model.**

This is the hypothesis `ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` asks for, at
the family of preimages of a covering family of opens of the base, and it is
`AlgebraicGeometry.Scheme.Pullback.left_affine_comp_pullback_hasPullback`'s analogue with a
different proof: **no `CategoryTheory.Limits.hasPullback_assoc_symm` and no pullback object.**

The module docstring draws the two squares. The lower one is
`ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` at `g` and `W`, transposed by
`CategoryTheory.IsPullback.flip`; the upper one is
`CategoryTheory.IsPullback.of_hasPullback` at the two restricted morphisms, whose fibre product
exists by `ComplexAnalytic.AnalyticSpace.hasPullback_of_isPresentedLocalModel_base` because their
common target is `Z.restrict W`. `CategoryTheory.IsPullback.paste_vert` composes them, and
`ComplexAnalytic.AnalyticSpace.restrictHom_fac` rewrites the resulting leg
`restrictHom f W ≫ Z.ofRestrict W` into `X.ofRestrict ((Opens.map f.toLRSHom.base).obj W) ≫ f`.

**The name says the cospan and not the hypothesis**, as
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` in `Oka/AnalyticSpace/PullbackOpen.lean`
does; the two are different statements and the `_comp` is the whole of the difference. Spelling
`hW` into the name instead would put the `info:` line of this declaration's guard nine columns
past the hundred every other line in `OkaTest/` is held to. -/
theorem hasPullback_ofRestrict_comp (f : X ⟶ Z) (g : Y ⟶ Z) (W : Z.Opens)
    (hW : IsPresentedLocalModel (Z.restrict W)) :
    HasPullback (X.ofRestrict ((Opens.map f.toLRSHom.base).obj W) ≫ f) g := by
  haveI := hasPullback_of_isPresentedLocalModel_base hW (restrictHom f W) (restrictHom g W)
  have h := (IsPullback.of_hasPullback (restrictHom f W) (restrictHom g W)).paste_vert
    (isPullback_ofRestrict g W).flip
  rw [restrictHom_fac] at h
  exact h.hasPullback

/-! ### Every cospan, and the category -/

/-- **Every cospan of complex analytic spaces has a fibre product.**

The third and last covering step, and the one that has no hypothesis left to discharge.
`ComplexAnalytic.exists_isPresentedLocalModel_restrict` chooses an open `W z` at every point of
the **base**; the family covering `X` is the preimages
`(TopologicalSpace.Opens.map f.toLRSHom.base).obj (W z)`, indexed by the carrier of `Z`; the point
`x` of `X` lies in the member indexed by `f x`; and the instance hypothesis at `z` is
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict_comp`.

**This is an `instance` and it is named.** Mathlib's two counterparts are anonymous and Lean gives
them `AlgebraicGeometry.Scheme.Pullback.instHasPullback` and
`AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`; naming both here is what lets
`OkaTest/Axioms/AnalyticSpace.lean` guard them by name, which is the shape every rung of this
ladder has delivered and the reason taxis #1829's filing gives for not shipping only the `Prop`. -/
instance hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g := by
  choose W hzW hW using fun z : Z ↦ exists_isPresentedLocalModel_restrict Z z
  haveI : ∀ z : Z, HasPullback (X.ofRestrict ((Opens.map f.toLRSHom.base).obj (W z)) ≫ f) g :=
    fun z ↦ hasPullback_ofRestrict_comp f g (W z) (hW z)
  exact Pullback.hasPullback_of_cover (fun z ↦ (Opens.map f.toLRSHom.base).obj (W z)) f g
    fun x ↦ ⟨f.toLRSHom.base x, hzW _⟩

/-- **The category of complex analytic spaces has pullbacks.**

`CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan` at the instance above, which is Mathlib's
last line too. **The declaration this file exists for**, and the one
`Oka/AnalyticSpace/PullbackGlue.lean` and `Oka/AnalyticSpace/PullbackLimit.lean` each name as
still owed.

`#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` succeeds at the commit
that adds this file; the guard section in `OkaTest/Axioms/AnalyticSpace.lean` records the probe
and the control that fired with it. -/
instance hasPullbacks : HasPullbacks AnalyticSpace.{u} :=
  hasPullbacks_of_hasLimit_cospan _

end AnalyticSpace

end ComplexAnalytic

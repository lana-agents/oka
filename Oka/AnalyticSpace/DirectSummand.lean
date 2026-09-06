/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.FiniteEtaleOver

/-!
# A morphism of covers that is injective on points exhibits its source as a direct summand

`Mathlib/CategoryTheory/Galois/Basic.lean`'s `PreGaloisCategory` asks, of every monomorphism
`i : A ⟶ B`, for an object `Z` and a morphism `Z ⟶ B` making `B` the binary coproduct of `A` and
`Z`. This file proves that statement at
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver X` **with the monomorphism hypothesis replaced by
injectivity of the underlying map, and with a Hausdorff hypothesis on the target cover's total
space added**. Both replacements are discussed under `## What is not here`, and neither is
cosmetic: what is proved here is not that field.

The geometry is the one a reader would guess. A morphism of covers over a Hausdorff total space is
itself finite étale, so its image is open because it is a local isomorphism and closed because it
is finite; an injective map onto its own image is a bijection onto it, and a bijective local
isomorphism is an isomorphism. So the source is isomorphic to the target restricted to a clopen
subset, and `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanRestrictClopen`
already says a cover is the coproduct of a clopen part and its complement.

## Main results

- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left`: **the underlying morphism of
  a morphism of covers is finite étale when the target cover's total space is Hausdorff**, which is
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` at the triangle a morphism of covers
  commutes.
- `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective`: **the
  direct-summand statement itself**, in the shape `PreGaloisCategory`'s field is written in — an
  object and a morphism to `B` whose binary cofan with `i` is a colimit.

## What is not here

* **The `PreGaloisCategory` field.** That field asks for the summand at every monomorphism and
  under no hypothesis on the base, on the source or on the target. This statement asks for
  `[T2Space B.left]` and for injectivity, and neither is available from `Mono i` in this
  repository. **Saying so is the point of this paragraph**: the gap is named rather than hidden
  behind a statement that reads like the field.
* **A proof that a monomorphism of covers is injective on points.** That is the remaining
  obligation, and it is a theorem rather than a formality — the classical argument makes the
  diagonal `A ⟶ A ×_B A` an isomorphism and needs the fibre product, which
  `ComplexAnalytic.AnalyticSpace` does not have. `Oka/AnalyticSpace/Basic.lean`'s
  `ComplexAnalytic.AnalyticSpace.mono_ofRestrict` and its neighbours run the other way, from an
  open immersion to a monomorphism.
* **Any claim that `[T2Space B.left]` can be dropped.** It is the cost of
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp`, which is where a morphism of covers gets
  its own finite étale property from, and `Oka/AnalyticSpace/Finite.lean` argues in its module
  docstring that a separation axiom on the middle space is what the closed half of the finite rung
  actually needs. `OkaTest/FiniteEtaleCancel.lean` compiles two witnesses for that paragraph.
* **The isomorphism onto the clopen part, as a named declaration.** It is built inside the proof
  below and is not exposed. Exposing it would put the source of
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left` — a theorem and not an
  instance — into the *type* of a declaration, since the clopen part is
  `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopen` at an open built from a
  local-isomorphism hypothesis. A caller that wants it should ask for it here rather than unfold
  this proof.
-/

open CategoryTheory

universe u

namespace ComplexAnalytic.AnalyticSpace

/-! ### The underlying morphism of a morphism of covers -/

/-- **The underlying morphism of a morphism of covers is finite étale**, when the total space of
the target cover is Hausdorff.

This is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_of_comp` at the triangle a morphism of covers
commutes: `f.left ≫ B.hom` is `A.hom`, which is finite étale because `A` is an object of the
category, and `B.hom` is a local isomorphism for the same reason about `B`. **The separation
axiom is that cancellation's and none of it is spent here** — a morphism of covers is finite étale
*because the target cover's total space is separated*, not because the category asks it to be, and
`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s module docstring makes the same point from the side of
what that file does not assume.

**The named arguments `(X := B.left)` on the two `haveI`s are load-bearing** and the reason is
recorded at `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul`, which runs the same
four lines inline: `f.left` has target `B.left` on the nose, while the instance an object carries
in its `prop` field has `(CategoryTheory.Functor.id _).obj B.left` there, and the two are
`rfl`-equal with different discrimination-tree keys. taxis #1681 is the filing about that seam.

**`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_eq_mul` and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.degree_left_eq_one` cannot cite this**, since they
are in the file this one imports; extracting their copies would have to happen there. -/
theorem FiniteEtaleOver.isFiniteEtale_left {X : AnalyticSpace.{u}} {A B : FiniteEtaleOver.{u} X}
    (f : A ⟶ B) [T2Space (B.left : Type u)] : IsFiniteEtale f.left := by
  have hw : f.left ≫ B.hom = A.hom := MorphismProperty.Over.w f
  haveI : IsFiniteEtale (X := B.left) B.hom := B.prop
  haveI : IsLocalIso (X := B.left) B.hom := IsFiniteEtale.isLocalIso
  haveI : IsFiniteEtale (f.left ≫ B.hom) := hw ▸ (A.prop : IsFiniteEtale A.hom)
  exact isFiniteEtale_of_comp f.left B.hom

/-! ### The direct summand at an injective morphism of covers -/

/-- **A morphism of covers that is injective on points exhibits its source as a direct summand of
its target**: there is a cover `Z` and a morphism `Z ⟶ B` whose binary cofan with `i` is a
colimit.

**This is the shape the `monoInducesIsoOnDirectSummand` field of
`Mathlib/CategoryTheory/Galois/Basic.lean`'s pre-Galois-category class is written in, and it is not
that field.** That field asks the same of every monomorphism and under
no hypothesis at all; this asks for `[T2Space B.left]` and for `hinj`. The module docstring's
`## What is not here` says what stands between the two and why neither hypothesis is available
from `Mono i` here.

**The proof, in the order the steps are taken.**
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isFiniteEtale_left` makes `i.left` finite étale, so
`ComplexAnalytic.AnalyticSpace.isClopen_range_of_isLocalIso_of_isFinite` makes its image clopen.
`ComplexAnalytic.AnalyticSpace.liftRestrict` factors `i.left` through the open subspace at that
image, and the factor is a local isomorphism by
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp` and a bijection because `hinj` gives the
injective half and the image is the target by construction, so
`ComplexAnalytic.AnalyticSpace.isIso_of_isLocalIso_of_bijective` makes it an isomorphism.
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isIso_of_isIso_left` reads that as an isomorphism
of covers, and
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.isColimitBinaryCofanRestrictClopen` together with
`CategoryTheory.Limits.BinaryCofan.isColimitCompLeftIso` transports the decomposition along it.

**The complement is `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.restrictClopenCompl` at the
image**, which is the object whose docstring already says it is what a direct-summand statement
would need; this is the statement that consumes it.

**`hinj` is stated about `i.left.toLRSHom.base` and not about a fibre map**, because that is the
map the topology of the argument is about: `ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.fiber`
enters nowhere below and no fibre is counted.

**The last step is an `exact` and not a `simp only`, and that is a measured choice rather than a
style one.** `CategoryTheory.Limits.BinaryCofan.isColimitCompLeftIso` returns its conclusion at
`(A.binaryCofanRestrictClopen U hU).inl` and `.inr`, which are the two inclusions by definition;
a `simp only` naming
`ComplexAnalytic.AnalyticSpace.FiniteEtaleOver.binaryCofanRestrictClopen` closes the gap and
**generates that definition's equation lemma, which then lands in
`scripts/DumpOkaDecls.lean`'s output as a row this file did not write**. `exact` crosses the same
gap at default transparency and plants nothing, so this proof's contribution to that dump is the
declarations it states and no more. -/
theorem FiniteEtaleOver.inducesIsoOnDirectSummand_of_injective {X : AnalyticSpace.{u}}
    {A B : FiniteEtaleOver.{u} X} (i : A ⟶ B) [T2Space (B.left : Type u)]
    (hinj : Function.Injective (i.left.toLRSHom.base : A.left → B.left)) :
    ∃ (Z : FiniteEtaleOver.{u} X) (u : Z ⟶ B),
      Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk i u)) := by
  haveI hfe : IsFiniteEtale i.left := FiniteEtaleOver.isFiniteEtale_left i
  set U : B.left.Opens :=
    ⟨Set.range (i.left.toLRSHom.base : A.left → B.left),
      (isClopen_range_of_isLocalIso_of_isFinite i.left).2⟩ with hUdef
  have hU : IsClosed (U : Set B.left) := (isClopen_range_of_isLocalIso_of_isFinite i.left).1
  have hsub : Set.range (i.left.toLRSHom.base : A.left → B.left) ⊆ (U : Set B.left) := subset_rfl
  set j : A.left ⟶ B.left.restrict U := liftRestrict i.left U hsub with hjdef
  have hfac : j ≫ B.left.ofRestrict U = i.left := liftRestrict_fac _ _ _
  have hbase : ∀ a : A.left, (B.left.ofRestrict U).toLRSHom.base (j.toLRSHom.base a)
      = i.left.toLRSHom.base a := fun a =>
    congrArg (fun m : A.left ⟶ B.left => m.toLRSHom.base a) hfac
  have hbij : Function.Bijective (j.toLRSHom.base : A.left → B.left.restrict U) := by
    constructor
    · intro a a' h
      exact hinj (by rw [← hbase a, ← hbase a', h])
    · intro y
      obtain ⟨a, ha⟩ : y.1 ∈ Set.range (i.left.toLRSHom.base : A.left → B.left) := y.2
      exact ⟨a, Subtype.ext (by rw [← hbase a] at ha; exact ha)⟩
  haveI : IsLocalIso (j ≫ B.left.ofRestrict U) := hfac ▸ hfe.isLocalIso
  haveI : IsLocalIso j := isLocalIso_of_comp j (B.left.ofRestrict U)
  haveI : IsIso j := isIso_of_isLocalIso_of_bijective j hbij
  let e : A ⟶ B.restrictClopen U hU :=
    MorphismProperty.Over.homMk j (by
      have h1 : j ≫ B.left.ofRestrict U ≫ B.hom = A.hom := by
        rw [← Category.assoc, hfac]; exact MorphismProperty.Over.w i
      exact h1)
  haveI : IsIso e := FiniteEtaleOver.isIso_of_isIso_left e (by simpa [e] using ‹IsIso j›)
  have hei : e ≫ B.restrictClopenι U hU = i :=
    MorphismProperty.Over.Hom.ext (by simpa [e] using hfac)
  refine ⟨B.restrictClopenCompl U hU, B.restrictClopenComplι U hU, ⟨?_⟩⟩
  have hcolim := Limits.BinaryCofan.isColimitCompLeftIso
    (B.binaryCofanRestrictClopen U hU) e (B.isColimitBinaryCofanRestrictClopen U hU)
  rw [← hei]
  exact hcolim

end ComplexAnalytic.AnalyticSpace

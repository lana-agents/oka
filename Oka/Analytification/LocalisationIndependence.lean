/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.LocalisationFunctor
import Oka.RingTheory.Localization.Away.Basic

/-!
# The presentation of a distinguished open depends on the polynomial only up to a unique iso

`ComplexAnalytic.localisationPresentation g f` adjoins a variable and the equation `t·f - 1`, so
the polynomial `f` occurs in the *type* of everything built from it: two polynomials cutting out
the same distinguished open give two different objects of `ComplexAnalytic.Presentation` and two
different analytic spaces. This file says they are canonically the same one.

Eight statements. The first four identify the two presentations and put the identification over
the member; the last four are about the case where the two polynomials differ by a **unit**, and
about where such a pair comes from:

* `ComplexAnalytic.localisationPresentationIsoOfDvdPow` — **the presentations of the localisation
  at `f` and at `f'` are isomorphic** whenever the images of `f` and `f'` in `A` each divide a
  power of the other, which is the algebraic form of *"`f` and `f'` cut out the same distinguished
  open"*.
* `ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom` — **the identification
  with `Localization.Away` commutes with the structure map** `A ⟶ A_f`. This is what makes the
  first isomorphism canonical rather than merely available, and it is proved without an
  `Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance on the localised presented algebra:
  see *The shape this settles* below.
* `ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom` — **the
  isomorphism of the first bullet is one of `A`-algebras**: it carries `A ⟶ A_f` to `A ⟶ A_{f'}`.
  Without this the two structure maps are unrelated and the isomorphism, though canonical, says
  nothing about the presentations *as distinguished opens of the same member*.
* `ComplexAnalytic.localisationPresentationIsoOfDvdPow_hom_comp` — **the triangle**: the same
  statement in `ComplexAnalytic.Presentation`, as an equation between morphisms. This is the form
  a coherence law consumes, and it is the sense in which a transition morphism built from a
  witness does not depend on the witness.
* `ComplexAnalytic.localisationPresentationIsoOfUnitMul` and
  `ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp` — **the same two at a unit
  multiple**, which is the pair of divisibilities at exponent one and is the form the statement
  below produces.
* `ComplexAnalytic.isUnit_mk_rename_localisationIncl` — **the polynomial that was inverted is a
  unit upstairs**, which is the last equation of `ComplexAnalytic.localisationPresentation` read
  as an invertibility.
* `ComplexAnalytic.exists_mk_rename_eq` — **every polynomial of a localisation is a unit multiple
  of a renamed polynomial of the base.** This is the algebraic form of
  `ComplexAnalytic.exists_localisationOpen_eq_rename`, whose geometric conclusion discards the
  unit; the unit is what the isomorphism above needs and what an equality of non-vanishing loci
  does not give.

## Where this is needed

Taxis #996. `Mathlib/AlgebraicGeometry/Cover/Directed.lean`'s locally directed cover — the shape
a scheme actually supplies, and the one
`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean` instantiates for every scheme with no
hypotheses — indexes the members of a cover by a *category* and asks for a transition morphism per
**arrow**. An arrow of that index category is a proof of `∃ f, X.basicOpen f = U`, and it is
proof-irrelevant: the section `f` witnessing it is neither recoverable from it nor unique. On this
side the polynomial is in the type, so a transition built from a witness has to be shown
independent of the witness. That is the first statement above.

## The shape this settles, and it is a choice among two

Building the analytification of a locally directed cover can be done **choice-first** — pick a
presentation for each member and a witness for each arrow, then prove the functoriality laws up to
the coherence isomorphisms — or **choice-free**, building each member as a colimit over all its
presentations so that no choice is made and the laws hold on the nose.

**Choice-first, and the reason is stronger than "the choices are isomorphic".** The isomorphism
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow` is
`IsLocalization.algEquiv`, transported: it is not *an* isomorphism between the two localisations
but **the unique `A`-algebra map** between them, since both are localisations of `A` at the same
saturated submonoid. Uniqueness is what discharges a coherence law, and it is available here
because the second statement above puts the identification over `A` rather than only over `ℂ`. The
colimit construction would buy the same laws at the price of machinery this development has no
other use for.

## What is not here

**No transition morphism, and no locally directed cover.** Nothing below mentions
`AlgebraicGeometry.Scheme`, and the file adds no Mathlib import: `Cover/Directed.lean` is not
imported, so its declarations cannot even be named in a docstring here — which is why the two
Mathlib files above are cited by path.

**No composite of two localisations.** The second half of taxis #996 is that the witness of a
composite arrow is a third polynomial, and its algebra is `IsLocalization.Away.mul`, already in
Mathlib. What is missing is the transport of that statement to
`ComplexAnalytic.localisationPresentation`, and the obstruction is recorded in
`Oka/Analytification/DistinguishedOpen.lean`'s docstring for
`ComplexAnalytic.localisationPresentedAlgebraEquiv`: there is deliberately no
`Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance on the localised presented algebra,
so `IsLocalization.Away.mul` cannot be applied to it directly. The compatibility proved here is
what such a transport would be built from.
-/

open CategoryTheory MvPolynomial

namespace ComplexAnalytic

universe u

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (f f' : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-! ### The identification is over `A`, not only over `ℂ` -/

/-- **The reindexing of the variables carries the structure map to `MvPolynomial.awayBaseHom`.**

Both sides send the class of `p` to the class of `MvPolynomial.rename some p`: on the left the
renaming is `ComplexAnalytic.localisationIncl` followed by
`ComplexAnalytic.localisationVarEquiv`, which is `some` by
`ComplexAnalytic.localisationVarEquiv_localisationIncl`. -/
theorem localisationRenameEquiv_localisationRingHom (x : PresentedAlgebra.{u} n k g) :
    localisationRenameEquiv.{u} g f (localisationRingHom.{u} g f x) =
      MvPolynomial.awayBaseHom (presentationIdeal.{u} g) f x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change localisationRenameEquiv.{u} g f
    ((PresHom.ofRename.{u} (localisationIncl.{u} n) _).toRingHom _) = _
  simp [localisationRenameEquiv, PresHom.ofRename, MvPolynomial.awayBaseHom,
    MvPolynomial.rename_rename, Function.comp_def]

/-- **`ComplexAnalytic.localisationPresentedAlgebraEquiv` commutes with the structure map**: the
identification of `ℂ[x, t] ⧸ (g, t·f - 1)` with `Localization.Away` is an isomorphism *over* `A`,
and not merely over `ℂ`.

This is the statement that lets a consumer use the universal property of the localisation on
anything built from `ComplexAnalytic.localisationRingHom` — for instance to see that two
descriptions of the same distinguished open agree over the member they sit in — without an
`Algebra (ComplexAnalytic.PresentedAlgebra n k g)` instance being introduced on the localised
presented algebra, which `Oka/Analytification/DistinguishedOpen.lean` deliberately avoids. -/
theorem localisationPresentedAlgebraEquiv_localisationRingHom (x : PresentedAlgebra.{u} n k g) :
    localisationPresentedAlgebraEquiv.{u} g f (localisationRingHom.{u} g f x) =
      algebraMap (PresentedAlgebra.{u} n k g)
        (Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f)) x := by
  change MvPolynomial.awayQuotientEquiv _ _ (localisationRenameEquiv.{u} g f _) = _
  rw [localisationRenameEquiv_localisationRingHom, MvPolynomial.awayQuotientEquiv_apply,
    MvPolynomial.awayLift_awayBaseHom]

/-! ### Two polynomials cutting out the same distinguished open -/

variable (h : ∃ N, Ideal.Quotient.mk (presentationIdeal.{u} g) f' ∣
    Ideal.Quotient.mk (presentationIdeal.{u} g) f ^ N)
  (h' : ∃ M, Ideal.Quotient.mk (presentationIdeal.{u} g) f ∣
    Ideal.Quotient.mk (presentationIdeal.{u} g) f' ^ M)

include h h' in
/-- **The two presented algebras are isomorphic**, when the images of `f` and `f'` in `A` each
divide a power of the other.

The middle step is `IsLocalization.Away.algEquivOfDvdPow`, which is an isomorphism over `A`; it is
restricted to `ℂ` only because `ComplexAnalytic.Presentation` is a category of `ℂ`-algebras. It is
the unique `A`-algebra map between the two localisations, so nothing about this isomorphism is
chosen. -/
noncomputable def localisationPresentedAlgebraEquivOfDvdPow :
    PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) ≃ₐ[ℂ]
      PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f') :=
  (localisationPresentedAlgebraEquiv.{u} g f).trans
    (((IsLocalization.Away.algEquivOfDvdPow _ _ h h').restrictScalars ℂ).trans
      (localisationPresentedAlgebraEquiv.{u} g f').symm)

include h h' in
/-- **The two presentations are isomorphic objects of `ComplexAnalytic.Presentation`**, hence have
isomorphic analytifications, by `ComplexAnalytic.analytificationFunctor`.

This is what says a transition morphism built from a *witness* that two members overlap in a
distinguished open does not depend on the witness. -/
noncomputable def localisationPresentationIsoOfDvdPow :
    (⟨n + 1, k + 1, localisationPresentation.{u} g f⟩ : Presentation.{u}) ≅
      ⟨n + 1, k + 1, localisationPresentation.{u} g f'⟩ :=
  Presentation.isoOfAlgEquiv (localisationPresentedAlgebraEquivOfDvdPow.{u} g f f' h h').symm

/-! ### The identification of two witnesses is over `A` -/

include h h' in
/-- **The witness-independence isomorphism carries one structure map to the other**: the image
of `A ⟶ A_f` is `A ⟶ A_{f'}`, on the nose.

`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow`'s docstring says it is *the unique
`A`-algebra map* between the two localisations. This is that fact in the form a consumer can use:
`IsLocalization.Away.algEquivOfDvdPow` is an `A`-algebra map by construction, and the two outer
steps are `ComplexAnalytic.localisationPresentedAlgebraEquiv_localisationRingHom`, which is what
puts the identification with `Localization.Away` over `A` rather than only over `ℂ`.

**Without this the isomorphism is compatible with nothing.** Two presentations of the same
distinguished open are interesting only as opens *of the member they sit in*, and the member
enters solely through the structure map. -/
theorem localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom
    (x : PresentedAlgebra.{u} n k g) :
    localisationPresentedAlgebraEquivOfDvdPow.{u} g f f' h h' (localisationRingHom.{u} g f x) =
      localisationRingHom.{u} g f' x := by
  rw [localisationPresentedAlgebraEquivOfDvdPow, AlgEquiv.trans_apply,
    localisationPresentedAlgebraEquiv_localisationRingHom, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.commutes,
    ← localisationPresentedAlgebraEquiv_localisationRingHom, AlgEquiv.symm_apply_apply]

include h h' in
/-- **The triangle**: the two structure maps agree once the two presentations are identified by
`ComplexAnalytic.localisationPresentationIsoOfDvdPow`.

This is the sense in which a transition morphism built from a *witness* that one member is a
distinguished open of another does not depend on the witness: replacing `f` by any `f'` cutting
out the same open changes the morphism `A_f ⟶ A` only by composition with the coherence
isomorphism. It is the shape a coherence law consumes, and it is
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom` read through
`ComplexAnalytic.PresHom.ext` — the companion of
`ComplexAnalytic.localisationPresentationIsoMul_hom_comp`, which does the same for the other
half of the arrow story. -/
theorem localisationPresentationIsoOfDvdPow_hom_comp :
    (localisationPresentationIsoOfDvdPow.{u} g f f' h h').hom ≫ localisationHom.{u} g f' =
      localisationHom.{u} g f := by
  refine PresHom.ext (RingHom.ext fun x ↦ ?_)
  change (localisationPresentedAlgebraEquivOfDvdPow.{u} g f f' h h').symm
    (localisationRingHom.{u} g f' x) = _
  rw [AlgEquiv.symm_apply_eq]
  exact (localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom.{u} g f f' h h' x).symm

/-! ### Associates, and the polynomials of a localisation up to one

The hypotheses of `ComplexAnalytic.localisationPresentationIsoOfDvdPow` are two divisibilities of
*powers*, which is the weakest form that still gives the isomorphism. The two statements below are
about the case where one polynomial is a **unit multiple** of the other — both divisibilities at
exponent one — and about where such a pair comes from.

**Where it comes from is the point.** `ComplexAnalytic.exists_pow_mul_eq_rename`
(`Oka/Analytification/DistinguishedOpen.lean`) proves an equation in the polynomial ring, and
`ComplexAnalytic.exists_localisationOpen_eq_rename` reads off the geometric half of it: two
polynomials cut out the same open. **That discards the algebra**, and the algebra is what a
transition morphism needs — an equality of non-vanishing loci does not give a divisibility over a
general presented `ℂ`-algebra, which would be a Nullstellensatz statement and is proved nowhere
here. Read modulo the ideal, the same equation says the two polynomials are *associates*, and that
is what `ComplexAnalytic.exists_mk_rename_eq` records.
-/

/-- **A unit multiple gives the isomorphism**, at exponent one in both directions.

`ComplexAnalytic.localisationPresentationIsoOfDvdPow` asks for `∃ N, q' ∣ q ^ N` and its mirror;
a unit multiple gives both with `N = M = 1`, since `q = q' * u⁻¹` and `q' = q * u`.

**Why this is a `def` taking `u` and `hu`, and not `∃ Q, Nonempty (_ ≅ _)`.** The existence form
is the one a spike writes, because it is one statement; it is the wrong one here, and the reason
is what the arguments buy rather than a preference for data over propositions:

* **A glue is built out of the isomorphism, not out of its existence.** A cover datum's `glue`
  field is an `Iso`, and `ComplexAnalytic.coverTransition` transports it; `Nonempty` gives a
  consumer nothing to transport, and `Classical.choice` on it would produce an isomorphism no
  second consumer could recognise as the same one.
* **The witness is what makes two calls agree.** Two consumers holding the same `Q`, `u` and `hu`
  get the *same* isomorphism here, so a coherence law between them is statable; an existential
  re-chosen at each call site is not, and coherence between two transitions is the whole content
  of the laws such a datum has to satisfy.
* **The triangle needs the same arguments.**
  `ComplexAnalytic.localisationPresentationIsoOfUnitMul_hom_comp` below is about *this*
  isomorphism at *these* arguments, and it is what says it is one over the member the two opens
  sit in.

`ComplexAnalytic.exists_mk_rename_eq` is where the three arguments come from, and the split
between the two is exactly `ComplexAnalytic.localisationPresentationIsoOfDvdPow`'s own: a `def`
taking hypotheses, and a separate existence producing them. -/
noncomputable def localisationPresentationIsoOfUnitMul (q q' : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (u : (PresentedAlgebra.{u} n k g)ˣ)
    (hu : Ideal.Quotient.mk (presentationIdeal.{u} g) q' =
      (u : PresentedAlgebra.{u} n k g) * Ideal.Quotient.mk (presentationIdeal.{u} g) q) :
    (⟨n + 1, k + 1, localisationPresentation.{u} g q⟩ : Presentation.{u}) ≅
      ⟨n + 1, k + 1, localisationPresentation.{u} g q'⟩ :=
  localisationPresentationIsoOfDvdPow.{u} g q q'
    ⟨1, ((u⁻¹ : (PresentedAlgebra.{u} n k g)ˣ) : PresentedAlgebra.{u} n k g), by
      rw [pow_one, hu, mul_comm (u : PresentedAlgebra.{u} n k g), mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, mul_one]⟩
    ⟨1, (u : PresentedAlgebra.{u} n k g), by rw [pow_one, hu, mul_comm]⟩

/-- **The triangle**, for the isomorphism above: it is one over the member the two opens sit in.

`ComplexAnalytic.localisationPresentationIsoOfDvdPow_hom_comp` at the two divisibilities the
definition supplies, and it is stated rather than left to a consumer to unfold: an isomorphism
that is not over the base identifies two objects and relates nothing, which is the distinction
`ComplexAnalytic.localisationPresentedAlgebraEquivOfDvdPow_localisationRingHom` above exists to
make. -/
theorem localisationPresentationIsoOfUnitMul_hom_comp (q q' : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (u : (PresentedAlgebra.{u} n k g)ˣ)
    (hu : Ideal.Quotient.mk (presentationIdeal.{u} g) q' =
      (u : PresentedAlgebra.{u} n k g) * Ideal.Quotient.mk (presentationIdeal.{u} g) q) :
    (localisationPresentationIsoOfUnitMul.{u} g q q' u hu).hom ≫ localisationHom.{u} g q' =
      localisationHom.{u} g q :=
  localisationPresentationIsoOfDvdPow_hom_comp.{u} g q q' _ _

/-- **The polynomial that was inverted is a unit upstairs**, which is the whole content of the
last equation of `ComplexAnalytic.localisationPresentation`: `t · f = 1` in the presented algebra,
read as an invertibility rather than as a relation.

Everything below is this fact and `ComplexAnalytic.exists_pow_mul_eq_rename`. -/
theorem isUnit_mk_rename_localisationIncl :
    IsUnit (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) f)) := by
  have key : (Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) f)) *
        Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} n)) = 1 := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.subset_span ⟨Fin.last k, ?_⟩
    rw [localisationPresentation_last]
    ring
  exact isUnit_iff_exists.2 ⟨_, key, by rw [mul_comm]; exact key⟩

/-- **Every polynomial of a localisation is a unit multiple of a renamed one**, in the presented
algebra — the algebraic form of `ComplexAnalytic.exists_localisationOpen_eq_rename`.

`ComplexAnalytic.exists_pow_mul_eq_rename` is the equation in the polynomial ring; modulo the
ideal its correction term dies, and what is left is `mk (rename Q) = uᴰ · mk q` with
`u = mk (rename f)` the unit above. **`D` survives here where the geometric form drops it**: a
non-vanishing locus does not see a non-vanishing factor, but a divisibility does, and the unit is
what a consumer feeds to `ComplexAnalytic.localisationPresentationIsoOfUnitMul`.

The two statements are not interchangeable, and the direction that fails is worth naming: this
one gives the equality of opens (a unit does not vanish), and the equality of opens does **not**
give this one — over a general presented `ℂ`-algebra that implication is a Nullstellensatz
statement and nothing in this repository proves it. -/
theorem exists_mk_rename_eq (q : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    ∃ (Q : MvPolynomial (ULift.{u} (Fin n)) ℂ) (u : (PresentedAlgebra.{u} (n + 1) (k + 1)
        (localisationPresentation.{u} g f))ˣ),
      Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
          (MvPolynomial.rename (localisationIncl.{u} n) Q) =
        (u : PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f)) *
          Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f)) q := by
  obtain ⟨D, Q, r, h⟩ := exists_pow_mul_eq_rename.{u} f q
  obtain ⟨u, hu⟩ := isUnit_mk_rename_localisationIncl.{u} g f
  refine ⟨Q, u ^ D, ?_⟩
  have hrel : Ideal.Quotient.mk (presentationIdeal.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.X (localisationVar.{u} n) *
        MvPolynomial.rename (localisationIncl.{u} n) f - 1) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span
      ⟨Fin.last k, localisationPresentation_last.{u} g f⟩)
  have hq := congrArg (Ideal.Quotient.mk
    (presentationIdeal.{u} (localisationPresentation.{u} g f))) h
  rw [map_mul, map_pow, map_add, map_mul, hrel, zero_mul, add_zero, ← hu] at hq
  rw [← hq, Units.val_pow_eq_pow_val]

end ComplexAnalytic

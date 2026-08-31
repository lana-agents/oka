/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CrossMemberGlue

/-!
# The `poly` field of a refined cover datum, in one formula and with no transport in its shape

`Oka/Analytification/CoverRefinement.lean` refines **one fixed member**, so its `σ` is constant
and every refined member lies over the same presentation.
`Oka/Analytification/CrossMemberGlue.lean` builds the glue of an overlap whose two refined members
lie over *different* members, and its `## What is not here` says what stops a datum being built
out of it:

> **No refined cover datum, and the missing piece is the shape of its `poly` field and not this
> glue.** … the two cases are different formulas and neither degenerates to the other … **Read off
> the types rather than compiled: in the equal case the branch is handed `fam b`, which is a
> polynomial over the member `σ b`, where it must produce one over the member `σ a`** — so the
> case split needs a transport of data along `σ a = σ b` and not only a case split in a proof.

**The transport is real and this file does not remove it. What it removes is the transport from
the *shape* of the refined overlap**, which is the part that would have been paid by every
downstream construction rather than once.

## Where the case split goes instead, and why that is the whole content

A refined member is `D(fam b)` inside the member `σ b`, so `poly' a b` must be a polynomial over
`(obj (σ a)).n + 1` variables cutting the overlap out of the `a`-th refined member. Writing the
field as `if σ a = σ b then … else …` puts a `dite` in the *type-level shape* of
`ComplexAnalytic.coverOverlap` of the refined data, and `Classical.dec` reduces definitionally on
neither branch — so every glue, every law and every open subspace below it would open the same
case split again.

Instead `ComplexAnalytic.refineDatumPoly` is **one product**, `poly (σ a) (σ b) * q a b`, and the
dichotomy lives in the two factors:

* `ComplexAnalytic.polyDiagOne` normalises the datum's diagonal to `1`. Its case split is on
  `i = j` between two values of **one** type, so it needs no transport at all.
* `ComplexAnalytic.refineDatumFactor` is the transported `fam b` where the two refined members lie
  over one member and the caller's `q` where they do not. Its case split is between two values of
  `MvPolynomial (ULift (Fin (obj (σ a)).n)) ℂ` — again **one** type, because `q` is asked for at
  every pair.

So the `▸` the bullet above names is still there, inside a polynomial, and
`ComplexAnalytic.refineDatumPoly`'s type mentions neither it nor a `dite`.
`ComplexAnalytic.refineDatumPoly_of_eq` and `ComplexAnalytic.refineDatumPoly_of_ne` read each case
back off on demand, as an equation between polynomials rather than as a case split a caller is
forced into.

## Why normalising the diagonal is allowed, and it is not a new hypothesis on the caller

`ComplexAnalytic.polyDiagOne` replaces `poly i i` and nothing else, and **the diagonal of a cover
datum is not read by the glue data it produces**: `CategoryTheory.GlueData.ofGlueData'` defines its
`V` at `⟨i, i⟩` to be `U i`, discarding whatever `V i i` a `CategoryTheory.GlueData'` carries, and
`Oka/Analytification/AffineCover.lean`'s `## The diagonal` section says the same from this side —
`hrange` and `hcocycle` are asked only at distinct triples, and `poly i i = 1` *"is the natural
choice, satisfies it, and is checked by nothing"*. What normalising buys is that the cross-member
formula is then correct at `σ a = σ b` as well, where for a datum with an arbitrary `poly i i` it
cuts out too little.

**What is not proved here is that normalising leaves the glued space unchanged.** It is a
statement about `ComplexAnalytic.coverAnalytification` of two data that differ on the diagonal,
nothing below states it, and the paragraph above is an argument and not a citation of one — the
two facts it rests on are compiled, the conclusion drawn from them is not. A consumer that needs
the refined datum to refine *the same space* needs it and will have to state it.

## The four proofs open a definition with `change` or a term, and none with `rw`

`Oka/Analytification/CrossMemberGlue.lean` states that discipline and
`Oka/Analytification/CoverRefinement.lean` records twice having broken it. **It was worth stating
again because the first draft of this file broke it in a way neither of them describes**: a
`rw [coverOverlap, coverOverlap, …]` in the last theorem planted an equation lemma for
`ComplexAnalytic.coverOverlap` — a declaration of `Oka/Analytification/AffineCover.lean` — into
*this* module, along with three for definitions above. `lake build` is green either way and the
declaration dump is what shows it: four `.eq_1` rows under this module's name, which is a
`Δdump` of `+15` where the file declares eleven things.

The replacements are the two `polyDiagOne` values as the terms `if_pos` and `if_neg`, `dif_pos`
and `dif_neg` for the factor, `change` at the product, and — in
`ComplexAnalytic.coverOverlap_refineDatumPoly_const` — a rewrite of the *function*
`refineDatumPoly … ` rather than of its application, since the application does not occur: the
polynomial family is an argument of `ComplexAnalytic.coverOverlap` and is never applied in the
goal.

## Main definitions

- `ComplexAnalytic.refineDatumObj`: **the refined member for a general `σ`**, the distinguished
  open `D(fam b)` of the member `σ b`. `ComplexAnalytic.refineObj` is this at constant `σ`, by
  `rfl`.
- `ComplexAnalytic.polyDiagOne`: **a cover datum's `poly` with its diagonal normalised to `1`.**
- `ComplexAnalytic.refineDatumFactor`: **the extra factor**, transported `fam b` over one member
  and the caller's `q` across two.
- `ComplexAnalytic.refineDatumPoly`: **the `poly` field of the refined datum**, one product of the
  two above.

## Main results

- `ComplexAnalytic.polyDiagOne_of_eq` and `ComplexAnalytic.polyDiagOne_of_ne`: the two values of
  the normalised diagonal.
- `ComplexAnalytic.refineDatumPoly_of_eq` and `ComplexAnalytic.refineDatumPoly_of_ne`: **the two
  cases, read back off the uniform formula.** The first is the configuration
  `ComplexAnalytic.refineGlue` is stated at and the second is the one
  `ComplexAnalytic.refineCrossGlue` is stated at, which is what makes the single formula the right
  one rather than a third of the same shape.
- `ComplexAnalytic.refineDatumObj_const` and `ComplexAnalytic.refineDatumPoly_const`: **at constant
  `σ` the two fields are `Oka/Analytification/CoverRefinement.lean`'s**, the member by `rfl`.
- `ComplexAnalytic.coverOverlap_refineDatumPoly_const`: **and so is the refined overlap itself**,
  as a presented object — which is the statement that the one-member file is a special case of
  this one at the level the glue is built at, and not only at the level of the polynomials.
  (Spelled without naming the presentation type: `scripts/guard_coverage.py` reads a backticked
  declaration inside a `## Main results` block as advertised *by this file*, and that one is
  unguarded in the file that declares it, so naming it here would put this file in the gap list
  for a declaration it does not own.)

## What is not here

* **No `glue`, no `hrange`, no `hsymm` and no `hcocycle`**, so this is one field of a datum and
  not a datum. The glue is where the transport this file relocates has to be paid: at
  `σ a = σ b` the two sides of `ComplexAnalytic.refineGlue`'s configuration sit over `obj (σ a)`
  and over `obj (σ b)`, which are propositionally and not definitionally equal, so the equal
  branch needs a transport between two objects of `ComplexAnalytic.Presentation` that the
  one-member file never meets. **That is measured only as a type mismatch and no attempt to
  discharge it is compiled**; nothing here is evidence about its size.
* **Nothing produces `q`.** As in `Oka/Analytification/CrossMemberGlue.lean`, the extra factor is
  an argument, and `ComplexAnalytic.exists_localisationOpen_eq_rename` with
  `ComplexAnalytic.exists_mk_rename_eq` is where a caller gets one. **This file adds a constraint
  on it that file did not have**: `ComplexAnalytic.refineDatumFactor` is the caller's `q` only off
  the diagonal, so a caller's `q` is read at pairs with `σ a ≠ σ b` and ignored elsewhere, and
  what makes the formula correct at those pairs is unproved here exactly as it is there.
* **No statement that the refined data cover anything**, and none that the diagonal normalisation
  preserves the glued space — the second is stated as an absence in a section of its own above
  because this file *uses* the normalisation.
* **No witness at a concrete cover datum.** What stands in for one is
  `ComplexAnalytic.refineDatumPoly_const` and `ComplexAnalytic.coverOverlap_refineDatumPoly_const`:
  the general form reduces to a configuration that `OkaTest/CoverRefinement.lean` and
  `OkaTest/CrossMemberGlue.lean` do exhibit. That is weaker than a witness and is not the same
  thing, since neither says the general `σ` is ever non-constant.
* **No scheme and no `admissible`**, as in the three files this one sits beside.
-/

open CategoryTheory MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})
  (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (σ : B → J)
  (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)

/-! ### The refined member, for a general `σ` -/

/-- **The `b`-th refined member**: the distinguished open `D(fam b)` of the member `σ b`.

`ComplexAnalytic.refineObj` is this with `σ` constant — by `rfl`, which
`ComplexAnalytic.refineDatumObj_const` records. An `abbrev` for the reason that one is: the
coherence statements below have to see the reduction of `ComplexAnalytic.coverOverlap` to a double
localisation at `instances` transparency. -/
abbrev refineDatumObj (b : B) : Presentation.{u} :=
  ⟨(obj (σ b)).n + 1, (obj (σ b)).k + 1,
    localisationPresentation.{u} (obj (σ b)).g (fam b)⟩

/-- **At constant `σ` the refined member is `Oka/Analytification/CoverRefinement.lean`'s**, on the
nose. -/
theorem refineDatumObj_const (i : J) (fam' : B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (b : B) :
    refineDatumObj.{u} obj (fun _ ↦ i) fam' b = refineObj.{u} (obj i).g fam' b :=
  rfl

/-! ### The two factors, and the case split that stays inside a polynomial -/

open Classical in
/-- **A cover datum's `poly` with its diagonal normalised to `1`.**

The case split is between two values of one type, so unlike a split on `σ a = σ b` it needs no
transport. Why replacing the diagonal is allowed is the section of that name in this file's module
docstring; the short form is that `CategoryTheory.GlueData.ofGlueData'` discards `V i i`. -/
def polyDiagOne (i j : J) : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ :=
  if i = j then 1 else poly i j

/-- **On the diagonal it is `1`**, which is what makes the single formula below correct where the
two refined members lie over one member. -/
theorem polyDiagOne_of_eq {i j : J} (h : i = j) : polyDiagOne.{u} obj poly i j = 1 :=
  if_pos h

/-- **Off the diagonal it is the datum's own polynomial**, so nothing about the cross-member case
is changed by the normalisation. -/
theorem polyDiagOne_of_ne {i j : J} (h : i ≠ j) : polyDiagOne.{u} obj poly i j = poly i j :=
  if_neg h

open Classical in
/-- **The extra factor cutting the `b`-th refined member down inside the `a`-th.**

Where the two lie over one member it is `fam b` transported along `σ a = σ b` — this is the `▸`
`Oka/Analytification/CrossMemberGlue.lean`'s bullet names, and it is here rather than in the shape
of the overlap. Where they lie over two it is the caller's `q`, which is what that file's
`ComplexAnalytic.refineCrossGlue` takes and does not produce. -/
def refineDatumFactor (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ) (a b : B) :
    MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ :=
  if h : σ a = σ b then h ▸ fam b else q a b

variable (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)

/-! ### The field -/

/-- **The `poly` field of the refined cover datum**, in one formula: the datum's own polynomial
with its diagonal normalised, times the extra factor, read in the one variable
`ComplexAnalytic.localisationPresentation` adjoins.

Its type mentions no `dite` and no transport, which is the point — see this file's module
docstring. The two cases are `ComplexAnalytic.refineDatumPoly_of_eq` and
`ComplexAnalytic.refineDatumPoly_of_ne` below. -/
def refineDatumPoly (a b : B) :
    MvPolynomial (ULift.{u} (Fin (refineDatumObj.{u} obj σ fam a).n)) ℂ :=
  MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n)
    (polyDiagOne.{u} obj poly (σ a) (σ b) * refineDatumFactor.{u} obj σ fam q a b)

/-- **Where the two refined members lie over one member**, the field is the other refining
polynomial alone — `ComplexAnalytic.refineGlue`'s configuration, and the case the bullet in
`Oka/Analytification/CrossMemberGlue.lean` says the cross-member formula cannot serve. It serves
it here because the diagonal is normalised, and only because of that. -/
theorem refineDatumPoly_of_eq {a b : B} (h : σ a = σ b) :
    refineDatumPoly.{u} obj poly σ fam q a b =
      MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n) (h ▸ fam b) := by
  have hfac : refineDatumFactor.{u} obj σ fam q a b = h ▸ fam b := dif_pos h
  change MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n)
    (polyDiagOne.{u} obj poly (σ a) (σ b) * refineDatumFactor.{u} obj σ fam q a b) = _
  rw [hfac, polyDiagOne_of_eq obj poly h, one_mul]

/-- **Where they lie over two**, it is the original overlap's polynomial times the caller's extra
factor — `ComplexAnalytic.refineCrossGlue`'s configuration, unchanged by the normalisation. -/
theorem refineDatumPoly_of_ne {a b : B} (h : σ a ≠ σ b) :
    refineDatumPoly.{u} obj poly σ fam q a b =
      MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n) (poly (σ a) (σ b) * q a b) := by
  have hfac : refineDatumFactor.{u} obj σ fam q a b = q a b := dif_neg h
  change MvPolynomial.rename (localisationIncl.{u} (obj (σ a)).n)
    (polyDiagOne.{u} obj poly (σ a) (σ b) * refineDatumFactor.{u} obj σ fam q a b) = _
  rw [hfac, polyDiagOne_of_ne obj poly h]

/-! ### The one-member file is the constant case -/

/-- **At constant `σ` the field is `ComplexAnalytic.refinePoly`**, for every `q`: the caller's
extra factor is never read, because every pair is on the diagonal. -/
theorem refineDatumPoly_const (i : J) (fam' : B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (q' : ∀ _ : B, B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) (a b : B) :
    refineDatumPoly.{u} obj poly (fun _ ↦ i) fam' q' a b = refinePoly.{u} (obj i).g fam' a b :=
  refineDatumPoly_of_eq.{u} obj poly (fun _ ↦ i) fam' q' (rfl : (fun _ ↦ i) a = (fun _ ↦ i) b)

/-- **And so is the refined overlap**, as an object of `ComplexAnalytic.Presentation`.

This is the statement of the previous one at the level the glue is built at, and it is what says
the one-member file is a special case of this one rather than a parallel construction: everything
`Oka/Analytification/CoverRefinement.lean` proves about that object is available here at constant
`σ` with no transport. -/
theorem coverOverlap_refineDatumPoly_const (i : J)
    (fam' : B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (q' : ∀ _ : B, B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) (a b : B) :
    coverOverlap.{u} (refineDatumObj.{u} obj (fun _ ↦ i) fam')
        (refineDatumPoly.{u} obj poly (fun _ ↦ i) fam' q') a b =
      coverOverlap.{u} (refineObj.{u} (obj i).g fam') (refinePoly.{u} (obj i).g fam') a b := by
  have hfun : refineDatumPoly.{u} obj poly (fun _ ↦ i) fam' q' = refinePoly.{u} (obj i).g fam' :=
    funext fun a ↦ funext fun b ↦ refineDatumPoly_const.{u} obj poly i fam' q' a b
  rw [hfun]

end

end ComplexAnalytic

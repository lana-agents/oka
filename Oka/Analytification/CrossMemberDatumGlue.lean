/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.CrossMemberDatum

/-!
# The `glue` of a cross-member refined datum where the two members are equal, and the transport it
was priced at

`Oka/Analytification/CrossMemberDatum.lean` builds the `poly` field of a refined cover datum whose
members lie over different members of the original cover, and prices the next field in its
`## What is not here`:

> **No `glue`, no `hrange`, no `hsymm` and no `hcocycle`** … The glue is where the transport this
> file relocates has to be paid: at `σ a = σ b` the two sides of `ComplexAnalytic.refineGlue`'s
> configuration sit over `obj (σ a)` and over `obj (σ b)`, which are propositionally and not
> definitionally equal, so the equal branch needs a transport between two objects of
> `ComplexAnalytic.Presentation` that the one-member file never meets. **That is measured only as a
> type mismatch and no attempt to discharge it is compiled**; nothing here is evidence about its
> size.

**The type mismatch is real and it is discharged here in one tactic.** The equal branch of the
glue, its symmetry, its coherence triangle and the analytified form of that triangle are all
below; what the branch costs is one generalisation and `subst`.

## The transport, and why generalising the two members is the whole trick

`σ a = σ b` is an equation between two *applications*, so neither side is a local variable and
`subst` does not apply to it. What does apply is the same equation with both members generalised:
for free `i j : J` and `h : i = j`, `subst h` replaces `j` by `i` throughout and the two
presentations become the one presentation, definitionally. So the file is arranged in three
layers, and only the first has any mathematics in it:

* `ComplexAnalytic.refineSwapGlue` — over **one** member, at two bare refining polynomials `x` and
  `y`. This is `Oka/Analytification/CoverRefinement.lean`'s glue with the family replaced by its
  two values, and it is built from the same two localisation isomorphisms at the two orders of the
  product.
* `ComplexAnalytic.refineSwapGlueOfEq` — the same over two members related by `h : i = j`, which
  is the previous one after `subst h`.
* `ComplexAnalytic.refineDatumGlueEq` — the datum's field, which is the previous one conjugated by
  the two transports that turn `ComplexAnalytic.refineDatumPoly` into the polynomial each side is
  stated at. Those two are `ComplexAnalytic.refineDatumPoly_of_eq` at the equation and at its
  `Eq.symm`, and nothing else is needed. (Spelled that way because field notation on a local
  hypothesis, in backticks, has no whitespace in it, so `scripts/check_docstring_names.py` reads
  it as a declaration reference — and the one this paragraph first used *resolved*, against
  something in Mathlib that has nothing to do with this file. A checker that reports zero
  unresolved names has not said the citations are right.)

**The two bare polynomials are what make the middle layer possible.** Stating the swap for a
*family* `K → MvPolynomial …` would put `K`'s indexing between `subst` and the goal; stating it at
`x` and `y` leaves the equation `i = j` as the only dependency, and that is what `subst` consumes.

## `refineDatumOverlap`, and why the overlap is spelled with its polynomial free

`ComplexAnalytic.coverOverlap` of the refined data at `(a, b)` is a presentation built from the
`a`-th refined member and one polynomial, and every statement below has to name it twice at two
*different* polynomials — once at `ComplexAnalytic.refineDatumPoly` and once at the renamed
refining polynomial it equals. `ComplexAnalytic.refineDatumOverlap` is that presentation with the
polynomial abstracted, so the two spellings differ in one argument rather than in a nested
structure literal, and `ComplexAnalytic.coverOverlap_refineDatumObj` says the abstraction is the
overlap on the nose. It is an `abbrev` for the reason
`ComplexAnalytic.refineDatumObj` is: everything below rewrites through it.

## The `rw` discipline, in both of its forms, and a third one

`Oka/Analytification/CrossMemberGlue.lean` states the discipline — open a definition with `change`
or a term, not with `rw` — and `Oka/Analytification/CrossMemberDatum.lean` adds the variant where
the planted equation lemma belongs to another file. **Both fired here and a third thing did.**

* **The plain form, caught by the declaration dump and not by the build.** The first draft proved
  the two symmetry laws and the two coherence triangles with `rw [refineSwapGlue]` and
  `rw [refineDatumGlueEq]`. That is green, and it plants `ComplexAnalytic.refineSwapGlue.eq_1`,
  `ComplexAnalytic.refineDatumGlueEq.eq_1` and `ComplexAnalytic.refineDatumGlueEq.congr_simp`:
  `Δdump` was **+17** where the file declared fourteen things. The cure is
  `ComplexAnalytic.refineSwapGlue_eq` and `ComplexAnalytic.refineDatumGlueEq_eq`, two `rfl`
  theorems that say the same thing under a name this file owns, and rewriting with those instead.
  It is also a better interface, which is why they are advertised.
* **A definition whose body cannot be written back down cannot be opened by `change` either.**
  The swap's middle factor was `eqToIso (by rw [mul_comm])`, and an anonymous tactic proof has no
  spelling — so the `rfl` theorem above could not be stated until the transport was named.
  `ComplexAnalytic.refineSwapMul` is that name. **A definition that a later proof will have to
  open should not carry an anonymous proof term**, and this is the shape of that rule.
* **One generated declaration is left, and it is `simp only … at` and not `rw`.**
  `ComplexAnalytic.refineDatumGlueEq.congr_simp` is planted by the `simp only … at e` in
  `ComplexAnalytic.refineDatumGlueEq_analytification_comp` — **attributed by deleting that
  theorem and re-running the dump**, not inferred. The one-member file's analytified triangle uses
  the same tactic and plants nothing, and the difference is that the definition here takes a proof
  argument, so simp needs a congruence lemma to traverse it. It belongs to this module and is the
  benign kind; `Oka/Analytification/CrossMemberGlue.lean` carries two of exactly this shape.
  **Recorded rather than removed**, because removing it means giving up `simp only … at` on a
  hypothesis that mentions a definition with a proof argument, and nothing here is worth that.
* **`rw` can also fail to find a lemma that is visibly present.** After
  `simp only [Category.assoc]` the goal is right-associated, so the subterm
  `eqToHom … ≫ localisationHom …` does not occur — it occurs as
  `eqToHom … ≫ (localisationHom … ≫ localisationHom …)` — and rewriting with the two-factor lemma
  reports *did not find an occurrence of the pattern* against a goal that prints it. `reassoc_of%`
  on the same lemma is what closes it, at both orientations, and that is a Mathlib term elaborator
  and not a new lemma.

## Main definitions

- `ComplexAnalytic.refineDatumOverlap`: **the refined overlap with its cutting polynomial
  abstracted**, which is the presentation every statement below is between.
- `ComplexAnalytic.refineSwapGlue`: **the swap of two refining polynomials over one member.**
- `ComplexAnalytic.refineSwapGlueOfEq`: **the same across two members that are equal**, which is
  the transport the file exists to discharge.
- `ComplexAnalytic.refineDatumGlueEq`: **the `glue` of the refined datum where the two members are
  equal**, at the polynomial the datum's own `poly` field produces.
- `ComplexAnalytic.refineDatumCrossAlgEquiv`: **the algebra isomorphism a cross-member glue takes,
  read off the original datum's own glue.** Not used below; it is the measurement that says the
  unequal branch is not blocked on this.

## Main results

- `ComplexAnalytic.coverOverlap_refineDatumObj`: the abstraction above is the refined overlap, by
  `rfl`.
- `ComplexAnalytic.refineSwapMul`: the two orders of the product present the same localisation.
- `ComplexAnalytic.refineSwapGlue_eq` and `ComplexAnalytic.refineDatumGlueEq_eq`: **the two
  definitions unfolded, by `rfl`**, so that a proof can open them without planting an equation
  lemma. See the `rw` section above for what that costs when they are absent.
- `ComplexAnalytic.refineSwapGlue_symm` and `ComplexAnalytic.refineSwapGlueOfEq_symm`: **the swap
  is its own inverse**, which is the shape of the symmetry law a cover datum asks for.
- `ComplexAnalytic.refineSwapGlue_comp` and `ComplexAnalytic.refineSwapGlueOfEq_comp`: **the
  coherence triangle**, over the member on the far side. The transported one carries the
  transport of members as its last factor, since its two composites end over two different
  objects.
- `ComplexAnalytic.refineDatumGlueEq_symm`: **the symmetry law, at the datum.**
- `ComplexAnalytic.refineDatumGlueEq_comp` and
  `ComplexAnalytic.refineDatumGlueEq_analytification_comp`: **the coherence triangle at the
  datum**, and the analytified form of it. The second is the shape the two geometric laws consume.
- `ComplexAnalytic.refineDatumGlueEq_const`: **at constant `σ` the field is the one-member file's
  glue**, conjugated by the two transports that file's overlap already needs — and it is `rfl`,
  which is what says this is the same construction and not a second one of the same shape.

## What is not here

* **No `glue` *field*, because the unequal branch is not assembled with this one.** What is below
  is the `σ a = σ b` branch alone. The other branch is
  `Oka/Analytification/CrossMemberGlue.lean`'s cross-member glue, and putting the two together is
  a decision about what the refined datum's `glue` takes as input, which nothing here makes.
* **What the unequal branch still needs, measured rather than guessed, and one item is off the
  list.** That glue takes an algebra isomorphism `e`, a polynomial `r`, a unit `u` and two
  equations. **The `e` is not missing**: `ComplexAnalytic.refineDatumCrossAlgEquiv` below is it,
  and it is one application of `ComplexAnalytic.Presentation.algEquivOfIso` to the original
  datum's own `glue`, typechecked with no transport. What is missing is `r`, `u` and the two
  equations, **all four of which are about the caller's `q`** — so the unequal branch is blocked
  on exactly the absence `Oka/Analytification/CrossMemberGlue.lean` and
  `Oka/Analytification/CrossMemberDatum.lean` already record as *"nothing produces `q`"*, and on
  nothing else that anybody has found.
* **No `hrange` and no `hcocycle`**, in either branch. They are geometric where everything here is
  algebraic, and `Oka/Analytification/CoverRefinement.lean`'s corresponding section says what
  makes them cheap for one fixed member — that every refined member lies over it — which is the
  sentence a general `σ` does not have.
* **`hsymm` on one branch is not `hsymm`.** A cover datum's symmetry law is quantified over every
  ordered pair, and what is below is quantified over the pairs with `σ a = σ b`.
* **No witness at a non-constant `σ`.** `ComplexAnalytic.refineDatumGlueEq_const` says the general
  form reduces to a configuration the test files already exhibit, which is weaker than a witness
  and says nothing about `σ` ever being non-constant — the same gap
  `Oka/Analytification/CrossMemberDatum.lean` records for the `poly` field.
* **No scheme and no `admissible`**, as in the four files this one sits beside.
-/

open CategoryTheory MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

variable {J B : Type u} (obj : J → Presentation.{u})

/-! ### The refined overlap, with its cutting polynomial free -/

/-- **The refined overlap of the `a`-th member with cutting polynomial `p`**: the localisation of
the `a`-th refined member `D(x)` at `p`, as a presentation.

Spelled this way because every statement below names it at two polynomials that are equal but not
identical, and an abbreviation that differs in one argument is what `rw` can move between. An
`abbrev` for the reason `ComplexAnalytic.refineDatumObj` is one. -/
abbrev refineDatumOverlap (i : J) (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (p : MvPolynomial (ULift.{u} (Fin ((obj i).n + 1))) ℂ) : Presentation.{u} :=
  ⟨(obj i).n + 1 + 1, (obj i).k + 1 + 1,
    localisationPresentation.{u} (localisationPresentation.{u} (obj i).g x) p⟩

variable (σ : B → J) (fam : ∀ b : B, MvPolynomial (ULift.{u} (Fin (obj (σ b)).n)) ℂ)

/-- **The abstraction is the refined overlap**, for any family of cutting polynomials and on the
nose. This is what lets the statements below be about the abbreviation rather than about a nested
structure literal. -/
theorem coverOverlap_refineDatumObj
    (p : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin ((obj (σ a)).n + 1))) ℂ) (a b : B) :
    coverOverlap.{u} (refineDatumObj.{u} obj σ fam) p a b =
      refineDatumOverlap.{u} obj (σ a) (fam a) (p a b) :=
  rfl

/-! ### The swap over one member, and the transport of it -/

/-- **The two orders of the product present the same localisation.** Named rather than inlined
because the two proofs below unfold `ComplexAnalytic.refineSwapGlue` and have to spell its
transport; an anonymous `by rw [mul_comm]` cannot be written back down. -/
theorem refineSwapMul (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (⟨(obj i).n + 1, (obj i).k + 1, localisationPresentation.{u} (obj i).g (y * x)⟩ :
        Presentation.{u}) =
      ⟨(obj i).n + 1, (obj i).k + 1, localisationPresentation.{u} (obj i).g (x * y)⟩ := by
  rw [mul_comm]

/-- **The swap of two refining polynomials over one member**: the overlap cut out of `D(x)` by `y`
and the overlap cut out of `D(y)` by `x` are the same localisation, at the product read in either
order.

`Oka/Analytification/CoverRefinement.lean`'s glue is this at the two values of a family; stating
it at two bare polynomials is what makes the transport below a `subst`, since the equation between
members is then the statement's only dependency. -/
def refineSwapGlue (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    refineDatumOverlap.{u} obj i x (rename (localisationIncl.{u} (obj i).n) y) ≅
      refineDatumOverlap.{u} obj i y (rename (localisationIncl.{u} (obj i).n) x) :=
  localisationPresentationIsoMul.{u} (obj i).g x y ≪≫
    eqToIso (refineSwapMul.{u} obj i x y) ≪≫
      (localisationPresentationIsoMul.{u} (obj i).g y x).symm

/-- **The swap, unfolded**, by `rfl`.

It exists so that the two proofs below can rewrite with a declaration of this file rather than
with the *name* of a definition: `rw [refineSwapGlue]` plants
`ComplexAnalytic.refineSwapGlue.eq_1` in this module, which
`Oka/Analytification/CrossMemberDatum.lean`'s discipline section is about and which the
declaration dump is what shows. -/
theorem refineSwapGlue_eq (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    refineSwapGlue.{u} obj i x y =
      localisationPresentationIsoMul.{u} (obj i).g x y ≪≫
        eqToIso (refineSwapMul.{u} obj i x y) ≪≫
          (localisationPresentationIsoMul.{u} (obj i).g y x).symm :=
  rfl

/-- **The swap is its own inverse.** The two orders differ by the transport along `mul_comm`, and
that is the only asymmetry in the definition. -/
theorem refineSwapGlue_symm (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    refineSwapGlue.{u} obj i y x = (refineSwapGlue.{u} obj i x y).symm := by
  rw [refineSwapGlue_eq, refineSwapGlue_eq, Iso.trans_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, eqToIso_symm']

/-- **The coherence triangle over the member.** Crossing to the other description of the overlap
and then going down to the member is going down directly, which is what says the swap is the
identification of two parts of one member and not merely an isomorphism of the right type. -/
theorem refineSwapGlue_comp (i : J) (x y : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) :
    (refineSwapGlue.{u} obj i x y).hom ≫
        localisationHom.{u} (localisationPresentation.{u} (obj i).g y)
            (rename (localisationIncl.{u} (obj i).n) x) ≫ localisationHom.{u} (obj i).g y =
      localisationHom.{u} (localisationPresentation.{u} (obj i).g x)
          (rename (localisationIncl.{u} (obj i).n) y) ≫ localisationHom.{u} (obj i).g x := by
  rw [← localisationPresentationIsoMul_hom_comp.{u} (obj i).g x y,
    ← localisationPresentationIsoMul_hom_comp.{u} (obj i).g y x, refineSwapGlue_eq]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, Iso.symm_hom]
  rw [show (localisationPresentationIsoMul.{u} (obj i).g y x).inv ≫
      (localisationPresentationIsoMul.{u} (obj i).g y x).hom ≫
        localisationHom.{u} (obj i).g (x * y) = localisationHom.{u} (obj i).g (x * y) from
    (localisationPresentationIsoMul.{u} (obj i).g y x).inv_hom_id_assoc _]
  exact congrArg _ (eqToHom_localisationHom.{u} (obj i).g (mul_comm y x))

/-- **The swap across two members that are equal.**

This is the transport `Oka/Analytification/CrossMemberDatum.lean` prices and does not discharge,
and `subst h` is the whole of it — available because `i` and `j` are bound here, where in the
datum below they are `σ a` and `σ b` and neither is a variable. -/
def refineSwapGlueOfEq {i j : J} (h : i = j)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (y : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ) :
    refineDatumOverlap.{u} obj i x (rename (localisationIncl.{u} (obj i).n) (h ▸ y)) ≅
      refineDatumOverlap.{u} obj j y (rename (localisationIncl.{u} (obj j).n) (h ▸ x)) := by
  subst h
  exact refineSwapGlue.{u} obj i x y

/-- **The transported swap is its own inverse.** -/
theorem refineSwapGlueOfEq_symm {i j : J} (h : i = j)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (y : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ) :
    refineSwapGlueOfEq.{u} obj h.symm y x = (refineSwapGlueOfEq.{u} obj h x y).symm := by
  subst h
  exact refineSwapGlue_symm.{u} obj i x y

/-- **The coherence triangle of the transported swap.**

Its two composites end over `obj j` and over `obj i`, which are equal and not identical, so the
statement carries the transport of members as its last factor. That factor is `eqToHom` of
`congrArg` and is the identity as soon as `h` is `rfl`, which is what the proof uses. -/
theorem refineSwapGlueOfEq_comp {i j : J} (h : i = j)
    (x : MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (y : MvPolynomial (ULift.{u} (Fin (obj j).n)) ℂ) :
    (refineSwapGlueOfEq.{u} obj h x y).hom ≫
        localisationHom.{u} (localisationPresentation.{u} (obj j).g y)
            (rename (localisationIncl.{u} (obj j).n) (h ▸ x)) ≫ localisationHom.{u} (obj j).g y =
      localisationHom.{u} (localisationPresentation.{u} (obj i).g x)
          (rename (localisationIncl.{u} (obj i).n) (h ▸ y)) ≫
        localisationHom.{u} (obj i).g x ≫ eqToHom (congrArg obj h) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  exact refineSwapGlue_comp.{u} obj i x y

/-! ### The field, at the pairs whose members are equal -/

variable (poly : ∀ i : J, J → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
  (q : ∀ a : B, B → MvPolynomial (ULift.{u} (Fin (obj (σ a)).n)) ℂ)

/-- **The `glue` of the refined cover datum, where the two refined members lie over one member.**

The transported swap, conjugated by the two equations that turn the datum's own `poly` field into
the polynomial each side of it is stated at. Nothing else enters: the diagonal normalisation is
already inside that field, and the original datum's `glue` is not read at all in this branch —
which is the sentence `Oka/Analytification/CrossMemberGlue.lean` uses to say why the cross-member
case is the one that is different. -/
def refineDatumGlueEq {a b : B} (h : σ a = σ b) :
    coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) a b ≅
      coverOverlap.{u} (refineDatumObj.{u} obj σ fam) (refineDatumPoly.{u} obj poly σ fam q) b a :=
  eqToIso (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
      (refineDatumPoly_of_eq.{u} obj poly σ fam q h)) ≪≫
    refineSwapGlueOfEq.{u} obj h (fam a) (fam b) ≪≫
      eqToIso (congrArg (refineDatumOverlap.{u} obj (σ b) (fam b))
        (refineDatumPoly_of_eq.{u} obj poly σ fam q h.symm)).symm

/-- **The field, unfolded**, by `rfl`, and for the reason
`ComplexAnalytic.refineSwapGlue_eq` exists. -/
theorem refineDatumGlueEq_eq {a b : B} (h : σ a = σ b) :
    refineDatumGlueEq.{u} obj σ fam poly q h =
      eqToIso (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
          (refineDatumPoly_of_eq.{u} obj poly σ fam q h)) ≪≫
        refineSwapGlueOfEq.{u} obj h (fam a) (fam b) ≪≫
          eqToIso (congrArg (refineDatumOverlap.{u} obj (σ b) (fam b))
            (refineDatumPoly_of_eq.{u} obj poly σ fam q h.symm)).symm :=
  rfl

/-- **The symmetry law, on this branch.** A cover datum asks for it at every ordered pair; this is
the half of that quantifier whose two members are equal. -/
theorem refineDatumGlueEq_symm {a b : B} (h : σ a = σ b) :
    refineDatumGlueEq.{u} obj σ fam poly q h.symm =
      (refineDatumGlueEq.{u} obj σ fam poly q h).symm := by
  rw [refineDatumGlueEq_eq, refineDatumGlueEq_eq, Iso.trans_symm, Iso.trans_symm,
    Iso.trans_assoc, eqToIso_symm', eqToIso_symm', refineSwapGlueOfEq_symm]

/-- **The coherence triangle at the datum**, with the transport of members as its last factor.

The two conjugating transports cancel against the structure maps, one at each orientation, and
that is the whole proof — but the cancellation lemma has to be reassociated first, because the
goal is right-associated and the two-factor form of the lemma does not occur in it. -/
theorem refineDatumGlueEq_comp {a b : B} (h : σ a = σ b) :
    (refineDatumGlueEq.{u} obj σ fam poly q h).hom ≫
        localisationHom.{u} (refineDatumObj.{u} obj σ fam b).g
            (refineDatumPoly.{u} obj poly σ fam q b a) ≫
          localisationHom.{u} (obj (σ b)).g (fam b) =
      localisationHom.{u} (refineDatumObj.{u} obj σ fam a).g
          (refineDatumPoly.{u} obj poly σ fam q a b) ≫
        localisationHom.{u} (obj (σ a)).g (fam a) ≫ eqToHom (congrArg obj h) := by
  rw [refineDatumGlueEq_eq]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [reassoc_of% (eqToHom_localisationHom.{u} (localisationPresentation.{u} (obj (σ b)).g (fam b))
      (refineDatumPoly_of_eq.{u} obj poly σ fam q h.symm).symm),
    ← reassoc_of% (eqToHom_localisationHom.{u}
      (localisationPresentation.{u} (obj (σ a)).g (fam a))
      (refineDatumPoly_of_eq.{u} obj poly σ fam q h))]
  exact congrArg (eqToHom (congrArg (refineDatumOverlap.{u} obj (σ a) (fam a))
    (refineDatumPoly_of_eq.{u} obj poly σ fam q h)) ≫ ·)
      (refineSwapGlueOfEq_comp.{u} obj h (fam a) (fam b))

/-- **The coherence triangle, analytified**, with the structure maps read as
`ComplexAnalytic.localisationProj`. This is the form the two geometric laws consume, and it is the
previous statement under the functor with nothing added. -/
theorem refineDatumGlueEq_analytification_comp {a b : B} (h : σ a = σ b) :
    analytificationFunctor.{u}.map (refineDatumGlueEq.{u} obj σ fam poly q h).hom ≫
        localisationProj.{u} (refineDatumObj.{u} obj σ fam b).g
            (refineDatumPoly.{u} obj poly σ fam q b a) ≫
          localisationProj.{u} (obj (σ b)).g (fam b) =
      localisationProj.{u} (refineDatumObj.{u} obj σ fam a).g
          (refineDatumPoly.{u} obj poly σ fam q a b) ≫
        localisationProj.{u} (obj (σ a)).g (fam a) ≫
          analytificationFunctor.{u}.map (eqToHom (congrArg obj h)) := by
  have e := congrArg (analytificationFunctor.{u}.map)
    (refineDatumGlueEq_comp.{u} obj σ fam poly q h)
  simp only [Functor.map_comp, analytificationFunctor_map_localisationPresHom] at e
  exact e

/-- **At constant `σ` the field is the one-member file's glue**, conjugated by the two transports
that identify the two descriptions of the refined overlap.

`rfl`, which is the statement worth having: the general construction does not merely agree with
the one-member one, it *is* it once the polynomials are identified, so everything
`Oka/Analytification/CoverRefinement.lean` proves about that glue is available here at constant
`σ` with no further work. -/
theorem refineDatumGlueEq_const (i : J)
    (fam' : B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ)
    (q' : ∀ _ : B, B → MvPolynomial (ULift.{u} (Fin (obj i).n)) ℂ) (a b : B) :
    refineDatumGlueEq.{u} obj (fun _ ↦ i) fam' poly q'
        (rfl : (fun _ ↦ i) a = (fun _ ↦ i) b) =
      eqToIso (coverOverlap_refineDatumPoly_const.{u} obj poly i fam' q' a b) ≪≫
        refineGlue.{u} (obj i).g fam' a b ≪≫
          eqToIso (coverOverlap_refineDatumPoly_const.{u} obj poly i fam' q' b a).symm :=
  rfl

/-! ### What the other branch would take, and where it comes from -/

/-- **The algebra isomorphism a cross-member glue takes, read off the original datum's own glue.**

`Oka/Analytification/CrossMemberGlue.lean`'s glue asks for an isomorphism of the two *presented
algebras* of the original overlap, where a cover datum carries an isomorphism of the two
*presentations*; the two are interchangeable and the bridge is on `master`. Recorded here because
the unequal branch's remaining inputs are then exactly the ones about the caller's extra factor,
and this is the one that is not.

Nothing below uses it: this file assembles no unequal branch. -/
def refineDatumCrossAlgEquiv
    (glue : ∀ i j : J, coverOverlap.{u} obj poly i j ≅ coverOverlap.{u} obj poly j i) (i j : J) :
    PresentedAlgebra.{u} ((obj i).n + 1) ((obj i).k + 1)
        (localisationPresentation.{u} (obj i).g (poly i j)) ≃ₐ[ℂ]
      PresentedAlgebra.{u} ((obj j).n + 1) ((obj j).k + 1)
        (localisationPresentation.{u} (obj j).g (poly j i)) :=
  (Presentation.algEquivOfIso.{u} (glue i j)).symm

end

end ComplexAnalytic

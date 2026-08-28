/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.ChangeOfVariables
import Oka.Analytification.DistinguishedOpen
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# A standard étale algebra over a presented `ℂ`-algebra is presented

Mathlib's `StandardEtalePair R` is a pair `f g : R[X]` with `f` monic and `f'` invertible in
`R[X][1/g] ⧸ (f)`, and `StandardEtalePair.Ring` is the algebra `R[X][Y] ⧸ (f, Y·g - 1)` it names.
**The `⧸ (f)` is not decoration.** The field is `cond : ∃ p₁ p₂ n, f' * p₁ + f * p₂ = g ^ n`, and
over `ℤ` the pair `f = X² - 1`, `g = 2` satisfies it at `p₁ = X`, `p₂ = -2`, `n = 1` while
`f' = 2X`, of degree one over a reduced ring, is not a unit of `ℤ[1/2][X]`. Mathlib's own
structure docstring has the `/f` and the bullet for it under that file's `## Main definitions`
drops it, so the two disagree upstream; the field is what to read. This
file says that when `R` is a `ComplexAnalytic.PresentedAlgebra` — the `ℂ`-algebra
`ℂ[x₁, …, x_n] ⧸ (g₁, …, g_k)` this development analytifies — that algebra is a presented
`ℂ`-algebra too, on two more variables and two more relations, and exhibits the presentation.

That is the bridge the Riemann-existence line needs: `ComplexAnalytic.analytificationFunctor`
consumes a `ComplexAnalytic.Presentation` and nothing else, so a standard étale morphism of
affine `ℂ`-schemes cannot be analytified until it is written as one.

## The two operations, which are the reusable half

Everything here is assembled out of two operations on presentations, and neither existed:

* **adjoin a variable** — `ComplexAnalytic.polyPresentation`, the same relations read in one more
  variable, presenting `A[X]` (`ComplexAnalytic.polyPresentedAlgebraEquiv`);
* **add a relation** — `Fin.snoc`, presenting a quotient
  (`ComplexAnalytic.presentedAlgebraSnocEquiv`).

`ComplexAnalytic.localisationPresentation`, which was already here, is exactly one of each: it is
`Fin.snoc (polyPresentation g) (t·f - 1)`, and that is `rfl`. The étale presentation below is
*two* of each, and is built as a `Fin.snoc` of `localisationPresentation` for that reason rather
than from scratch.

## The route, and what it avoids

`StandardEtalePair.Ring` is **definitionally** `R[X][Y] ⧸ (C f, Y·C g - 1)`, so the target is a
quotient of a bare polynomial ring and no localisation appears. Going through
`StandardEtalePair.equivAwayQuotient` — `P.Ring ≃ R[X][1/g] ⧸ f` — would have meant transporting
a `Localization.Away` along an algebra equivalence and matching the two structure maps. Taking the
definition instead costs one chain of quotient isomorphisms and no commutative algebra:

    ℂ[x, X, Y] ⧸ (g, Y·G - 1, F)   →   (A[X][Y]) ⧸ (C f, Y·C g - 1)   =   P.Ring

with the middle step `ComplexAnalytic.biPolyPresentedAlgebraEquiv`, two applications of the
adjoin-a-variable operation.

## The lifts are hypotheses, not choices

`P.f` and `P.g` live in `A[X]`, and a presentation needs polynomials. Rather than choose lifts
with `Classical.choose`, `ComplexAnalytic.etalePresentedAlgebraEquiv` takes them as arguments
together with the two equations saying they *are* lifts, and
`ComplexAnalytic.exists_presentation_standardEtale` supplies them where only existence is wanted.
That keeps the isomorphism explicit in the data a caller already has: a scheme-side standard
étale pair arrives with polynomial representatives, and forcing it through a choice would discard
them.

## Main definitions

- `ComplexAnalytic.polyPresentation`: the relations of `g`, read in one more variable.
- `ComplexAnalytic.etalePresentation`: two more variables and two more relations, `F` and
  `Y·G - 1`.
- `ComplexAnalytic.etalePresHom`: the structure map `A ⟶ A_ét`, as a
  `ComplexAnalytic.PresHom`.

## Main results

- `ComplexAnalytic.presentedAlgebraSnocEquiv`: **appending a relation presents the quotient by
  it.**
- `ComplexAnalytic.polyPresentedAlgebraEquiv`: **adjoining a variable presents the polynomial
  ring** `A[X]`.
- `ComplexAnalytic.etalePresentedAlgebraEquiv`: **the algebra the étale presentation above
  presents is `StandardEtalePair.Ring`**, written as the quotient it definitionally is.
- `ComplexAnalytic.etalePresentedAlgebraEquivRing`: the same equivalence with `P.Ring` for its
  target, which is the form a consumer states things in.
- `ComplexAnalytic.exists_presentation_standardEtale`: the same, with the lifts existentially
  quantified.

## What is not here

* **The analytification.** Nothing below mentions an analytic space; this is the algebraic half
  alone. Applying `ComplexAnalytic.analytificationFunctor` to
  `ComplexAnalytic.etalePresentation` is the next step and is a different issue.
* **That the étale algebra is étale.** `Algebra.Etale R P.Ring` is Mathlib's, and nothing here
  reproves or uses it; the monicity of `f` and the invertibility of `f'` are carried by `P` and
  are not read.
* **Any statement about `ComplexAnalytic.etalePresHom` beyond its existence.** That it is flat, or
  unramified, or that the induced morphism of analytic spaces is a local isomorphism, is the
  content of the stalk half and is not here.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ}

/-! ### Adding a relation -/

variable (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (h : MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **Appending a relation adds it to the ideal.** -/
theorem presentationIdeal_snoc :
    presentationIdeal.{u} (Fin.snoc g h) = presentationIdeal.{u} g ⊔ Ideal.span {h} := by
  rw [presentationIdeal, presentationIdeal, Fin.range_snoc, Ideal.span_insert, sup_comm]

/-- **A presentation with one more relation presents the quotient by that relation.**

`DoubleQuot.quotQuotEquivQuotSupₐ` on the ideal identity above. The `Ideal.map` in that lemma's
statement is the image of `Ideal.span {h}`, which is `Ideal.span` of the image of `h`; that is the
second `Ideal.quotientEquivAlgOfEq`. -/
def presentedAlgebraSnocEquiv :
    PresentedAlgebra.{u} n (k + 1) (Fin.snoc g h) ≃ₐ[ℂ]
      PresentedAlgebra.{u} n k g ⧸
        Ideal.span {Ideal.Quotient.mk (presentationIdeal.{u} g) h} :=
  (Ideal.quotientEquivAlgOfEq ℂ (presentationIdeal_snoc.{u} g h)).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ ℂ (presentationIdeal.{u} g) (Ideal.span {h})).symm.trans
      (Ideal.quotientEquivAlgOfEq ℂ (by rw [Ideal.map_span, Set.image_singleton]; rfl)))

/-! ### Adjoining a variable -/

/-- **The relations of `g`, read in one more variable.**

The new variable is `ComplexAnalytic.localisationVar`, the last one, so that this is literally the
first half of `ComplexAnalytic.localisationPresentation` — see
`ComplexAnalytic.localisationPresentation_eq_snoc`. -/
def polyPresentation : Fin k → MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  fun j ↦ MvPolynomial.rename (localisationIncl.{u} n) (g j)

/-- **`ComplexAnalytic.localisationPresentation` is one of each operation**: adjoin a variable,
then append `t·f - 1`. It holds by `rfl`, and it is why the étale presentation below is built on
top of it rather than beside it. -/
theorem localisationPresentation_eq_snoc (f : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    localisationPresentation.{u} g f =
      Fin.snoc (polyPresentation.{u} g)
        (MvPolynomial.X (localisationVar.{u} n) *
          MvPolynomial.rename (localisationIncl.{u} n) f - 1) := rfl

/-- Under `ComplexAnalytic.localisationVarEquiv`, the new relations are the old ones renamed along
`some`. -/
theorem rename_comp_polyPresentation :
    MvPolynomial.rename (localisationVarEquiv.{u} n) ∘ polyPresentation.{u} g =
      MvPolynomial.rename (some (α := ULift.{u} (Fin n))) ∘ g := by
  funext j
  simp [polyPresentation, MvPolynomial.rename_rename, Function.comp_def]

/-- The ideal statement of `ComplexAnalytic.rename_comp_polyPresentation`. -/
theorem map_presentationIdeal_polyPresentation :
    (presentationIdeal.{u} (polyPresentation.{u} g)).map
        (MvPolynomial.rename (localisationVarEquiv.{u} n)) =
      (presentationIdeal.{u} g).map
        (MvPolynomial.rename (some (α := ULift.{u} (Fin n)))) := by
  rw [presentationIdeal, presentationIdeal, Ideal.map_span, Ideal.map_span, ← Set.range_comp,
    ← Set.range_comp, rename_comp_polyPresentation]

/-- **`MvPolynomial.optionEquivLeft` turns renaming along `some` into `Polynomial.C`**: the new
variable becomes the polynomial variable and the old ones become constants. -/
theorem optionEquivLeft_comp_rename_some :
    ((MvPolynomial.optionEquivLeft ℂ (ULift.{u} (Fin n))).toAlgHom.comp
        (MvPolynomial.rename (some (α := ULift.{u} (Fin n))))) =
      (Polynomial.CAlgHom : MvPolynomial (ULift.{u} (Fin n)) ℂ →ₐ[ℂ] _) := by
  ext i
  simp

/-- `ComplexAnalytic.optionEquivLeft_comp_rename_some`, applied. -/
theorem optionEquivLeft_rename_some (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    MvPolynomial.optionEquivLeft ℂ (ULift.{u} (Fin n))
        (MvPolynomial.rename (some (α := ULift.{u} (Fin n))) p) = Polynomial.C p :=
  congrArg (fun F ↦ F p) (congrArg (fun F : _ →ₐ[ℂ] _ ↦ (F : _ → _))
    (optionEquivLeft_comp_rename_some.{u} (n := n)))

/-- Step 1 of three: name the new variable `none`. -/
def polyRenameEquiv :
    PresentedAlgebra.{u} (n + 1) k (polyPresentation.{u} g) ≃ₐ[ℂ]
      (MvPolynomial (Option (ULift.{u} (Fin n))) ℂ ⧸
        (presentationIdeal.{u} g).map
          (MvPolynomial.rename (some (α := ULift.{u} (Fin n))))) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv ℂ (localisationVarEquiv.{u} n))
    (map_presentationIdeal_polyPresentation.{u} g).symm

/-- Step 2 of three: `ℂ[x, none]` is `ℂ[x][X]`. -/
def polyOptionEquiv :
    (MvPolynomial (Option (ULift.{u} (Fin n))) ℂ ⧸
        (presentationIdeal.{u} g).map
          (MvPolynomial.rename (some (α := ULift.{u} (Fin n))))) ≃ₐ[ℂ]
      (Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ) ⧸
        (presentationIdeal.{u} g).map
          (Polynomial.C : MvPolynomial (ULift.{u} (Fin n)) ℂ →+* _)) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.optionEquivLeft ℂ (ULift.{u} (Fin n))) (by
    rw [presentationIdeal, Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_image]
    exact congrArg Ideal.span
      (Set.image_congr' (fun p ↦ (optionEquivLeft_rename_some.{u} p).symm)))

/-- Step 3 of three: `R[X] ⧸ (I·R[X])` is `(R ⧸ I)[X]`, which is
`Ideal.polynomialQuotientEquivQuotientPolynomial` read backwards.

That is a `RingEquiv` in Mathlib and the `ℂ`-algebra structure has to be supplied; the `commutes`
proof is the computation of both sides on a constant. -/
def polyCoeffEquiv :
    (Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ) ⧸
        (presentationIdeal.{u} g).map
          (Polynomial.C : MvPolynomial (ULift.{u} (Fin n)) ℂ →+* _)) ≃ₐ[ℂ]
      Polynomial (PresentedAlgebra.{u} n k g) :=
  AlgEquiv.ofRingEquiv (f := (Ideal.polynomialQuotientEquivQuotientPolynomial _).symm) (by
    intro c
    simp only [RingEquiv.symm_apply_eq]
    simp only [Ideal.polynomialQuotientEquivQuotientPolynomial, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      Polynomial.coe_eval₂RingHom]
    rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C,
      show (algebraMap ℂ (PresentedAlgebra.{u} n k g)) c =
        Ideal.Quotient.mk (presentationIdeal.{u} g)
          (algebraMap ℂ (MvPolynomial (ULift.{u} (Fin n)) ℂ) c) from rfl,
      Ideal.Quotient.lift_mk]
    rfl)

/-- **Adjoining a variable to a presentation presents the polynomial ring.**

No relation is added, so the ideal does not change: the whole content is that
`ℂ[x₁, …, x_n, X] ⧸ (g)` is `(ℂ[x] ⧸ (g))[X]`, which is
`Ideal.polynomialQuotientEquivQuotientPolynomial` after the two reindexings above. -/
def polyPresentedAlgebraEquiv :
    PresentedAlgebra.{u} (n + 1) k (polyPresentation.{u} g) ≃ₐ[ℂ]
      Polynomial (PresentedAlgebra.{u} n k g) :=
  (polyRenameEquiv.{u} g).trans ((polyOptionEquiv.{u} g).trans (polyCoeffEquiv.{u} g))

/-- **The old variables become constants.** -/
@[simp]
theorem polyPresentedAlgebraEquiv_mk_rename (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    polyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} n) p)) =
      Polynomial.C (Ideal.Quotient.mk (presentationIdeal.{u} g) p) := by
  rw [polyPresentedAlgebraEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have h1 : polyRenameEquiv.{u} g
      (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} n) p)) =
      Ideal.Quotient.mk _ (MvPolynomial.rename (some (α := ULift.{u} (Fin n))) p) := by
    change Ideal.Quotient.mk _ _ = _
    congr 1
    simp [MvPolynomial.rename_rename, Function.comp_def]
  rw [h1]
  have h2 : polyOptionEquiv.{u} g
      (Ideal.Quotient.mk _ (MvPolynomial.rename (some (α := ULift.{u} (Fin n))) p)) =
      Ideal.Quotient.mk _ (Polynomial.C p) := by
    change Ideal.Quotient.mk _ _ = _
    congr 1
    exact optionEquivLeft_rename_some.{u} p
  rw [h2]
  change (Ideal.polynomialQuotientEquivQuotientPolynomial _).symm _ = _
  rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]

/-- **The new variable becomes the polynomial variable.** -/
@[simp]
theorem polyPresentedAlgebraEquiv_mk_X_var :
    polyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} n))) = Polynomial.X := by
  rw [polyPresentedAlgebraEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have h1 : polyRenameEquiv.{u} g
      (Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} n))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (none : Option (ULift.{u} (Fin n)))) := by
    change Ideal.Quotient.mk _ _ = _
    congr 1
    simp
  rw [h1]
  have h2 : polyOptionEquiv.{u} g
      (Ideal.Quotient.mk _ (MvPolynomial.X (none : Option (ULift.{u} (Fin n))))) =
      Ideal.Quotient.mk _ Polynomial.X := by
    change Ideal.Quotient.mk _ _ = _
    congr 1
    exact MvPolynomial.optionEquivLeft_X_none ℂ (ULift.{u} (Fin n))
  rw [h2]
  change (Ideal.polynomialQuotientEquivQuotientPolynomial _).symm _ = _
  rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_X]

/-- **Adjoining two variables presents `A[X][Y]`**, by
`ComplexAnalytic.polyPresentedAlgebraEquiv` twice — once at `g` and once at
`ComplexAnalytic.polyPresentation g`, the second mapped over the coefficients. -/
def biPolyPresentedAlgebraEquiv :
    PresentedAlgebra.{u} (n + 2) k (polyPresentation.{u} (polyPresentation.{u} g)) ≃ₐ[ℂ]
      Polynomial (Polynomial (PresentedAlgebra.{u} n k g)) :=
  (polyPresentedAlgebraEquiv.{u} (polyPresentation.{u} g)).trans
    (Polynomial.mapAlgEquiv (polyPresentedAlgebraEquiv.{u} g))

/-- A polynomial in the first `n + 1` variables becomes a constant of the outer `Polynomial`, with
coefficient its own image. -/
theorem biPolyPresentedAlgebraEquiv_mk_rename
    (F : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    biPolyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} (n + 1)) F)) =
      Polynomial.C (polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F)) := by
  rw [biPolyPresentedAlgebraEquiv, AlgEquiv.trans_apply,
    polyPresentedAlgebraEquiv_mk_rename.{u} (polyPresentation.{u} g) F]
  simp [Polynomial.coe_mapAlgEquiv]

/-- The last variable becomes the outer polynomial variable, the `Y` of `A[X][Y]`. -/
theorem biPolyPresentedAlgebraEquiv_mk_X_var :
    biPolyPresentedAlgebraEquiv.{u} g
        (Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} (n + 1)))) = Polynomial.X := by
  rw [biPolyPresentedAlgebraEquiv, AlgEquiv.trans_apply,
    polyPresentedAlgebraEquiv_mk_X_var.{u} (polyPresentation.{u} g)]
  simp [Polynomial.coe_mapAlgEquiv]

/-! ### The standard étale presentation -/

variable (F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-- **Two more variables and two more relations**: `Y·G - 1`, inverting `G`, and `F`, cutting out
its zero locus.

It is `Fin.snoc` of `ComplexAnalytic.localisationPresentation` at
`ComplexAnalytic.polyPresentation g` — adjoin `X`, invert `G`, then impose `F` — which is why the
two variables arrive in that order and why the localisation half is not rebuilt here. -/
def etalePresentation : Fin (k + 2) → MvPolynomial (ULift.{u} (Fin (n + 2))) ℂ :=
  Fin.snoc (localisationPresentation.{u} (polyPresentation.{u} g) G)
    (MvPolynomial.rename (localisationIncl.{u} (n + 1)) F)

/-- The ideal of `ComplexAnalytic.etalePresentation`, split as the old relations and the two new
ones. -/
theorem presentationIdeal_etalePresentation :
    presentationIdeal.{u} (etalePresentation.{u} g F G) =
      presentationIdeal.{u} (polyPresentation.{u} (polyPresentation.{u} g)) ⊔
        Ideal.span {MvPolynomial.X (localisationVar.{u} (n + 1)) *
            MvPolynomial.rename (localisationIncl.{u} (n + 1)) G - 1,
          MvPolynomial.rename (localisationIncl.{u} (n + 1)) F} := by
  rw [etalePresentation, presentationIdeal_snoc, localisationPresentation,
    presentationIdeal_snoc, sup_assoc]
  congr 1
  rw [Set.pair_comm, Ideal.span_insert]
  exact sup_comm _ _

variable (P : StandardEtalePair (PresentedAlgebra.{u} n k g))

/-- **`ℂ` acts on the standard étale algebra**, through the presented algebra it is built over.

`StandardEtalePair.Ring` derives `Algebra R P.Ring` at its own base ring, and Mathlib has no
transitive `Algebra`, so without this line the type `… ≃ₐ[ℂ] P.Ring` does not elaborate at all in
a file importing this one — which is the form the consumers of
`ComplexAnalytic.etalePresentedAlgebraEquivRing` below want. There is no diamond: the structure
map factors through `A` by `rfl`, which is what
`ComplexAnalytic.standardEtalePairRingIsScalarTower` records. -/
instance standardEtalePairRingAlgebra : Algebra ℂ P.Ring :=
  inferInstanceAs (Algebra ℂ (Polynomial (Polynomial (PresentedAlgebra.{u} n k g)) ⧸
    Ideal.span {Polynomial.C P.f, Polynomial.X * Polynomial.C P.g - 1}))

/-- **The two actions on `StandardEtalePair.Ring` agree**, by `rfl` on the structure maps. -/
instance standardEtalePairRingIsScalarTower :
    IsScalarTower ℂ (PresentedAlgebra.{u} n k g) P.Ring :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- **Mathlib's standard étale algebra is definitionally this quotient**, which is what lets the
isomorphism below land on a bare polynomial ring and never mention a localisation. It is the same
observation `StandardEtalePair.equivPolynomialQuotient` makes, and it is `rfl` there too. -/
theorem standardEtalePair_ring_eq :
    P.Ring =
      (Polynomial (Polynomial (PresentedAlgebra.{u} n k g)) ⧸
        Ideal.span {Polynomial.C P.f, Polynomial.X * Polynomial.C P.g - 1}) := rfl

/-- **The algebra `ComplexAnalytic.etalePresentation` presents is the standard étale algebra.**

The hypotheses say that `F` and `G` are polynomial lifts of `P.f` and `P.g`; see the module
docstring on why they are hypotheses rather than choices, and
`ComplexAnalytic.exists_presentation_standardEtale` for the form that quantifies them away.

The chain is: the ideal identity above, then `DoubleQuot.quotQuotEquivQuotSupₐ` to peel off the
two new relations, then `ComplexAnalytic.biPolyPresentedAlgebraEquiv` on what is left. The only
computation is where the two new relations go, and that is the two `simp` lemmas about
`biPolyPresentedAlgebraEquiv` plus the hypotheses. -/
def etalePresentedAlgebraEquiv
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    PresentedAlgebra.{u} (n + 2) (k + 2) (etalePresentation.{u} g F G) ≃ₐ[ℂ]
      (Polynomial (Polynomial (PresentedAlgebra.{u} n k g)) ⧸
        Ideal.span {Polynomial.C P.f, Polynomial.X * Polynomial.C P.g - 1}) :=
  (Ideal.quotientEquivAlgOfEq ℂ (presentationIdeal_etalePresentation.{u} g F G)).trans
    (((DoubleQuot.quotQuotEquivQuotSupₐ ℂ
        (presentationIdeal.{u} (polyPresentation.{u} (polyPresentation.{u} g))) _).symm).trans
      (Ideal.quotientEquivAlg _ _ (biPolyPresentedAlgebraEquiv.{u} g) (by
        have e1 : biPolyPresentedAlgebraEquiv.{u} g
            (Ideal.Quotient.mk _ (MvPolynomial.X (localisationVar.{u} (n + 1)) *
              MvPolynomial.rename (localisationIncl.{u} (n + 1)) G - 1)) =
            Polynomial.X * Polynomial.C P.g - 1 := by
          simp only [map_sub, map_one, map_mul]
          rw [biPolyPresentedAlgebraEquiv_mk_X_var.{u} g,
            biPolyPresentedAlgebraEquiv_mk_rename.{u} g G, hG]
        have e2 : biPolyPresentedAlgebraEquiv.{u} g
            (Ideal.Quotient.mk _ (MvPolynomial.rename (localisationIncl.{u} (n + 1)) F)) =
            Polynomial.C P.f := by
          rw [biPolyPresentedAlgebraEquiv_mk_rename.{u} g F, hF]
        rw [Ideal.map_span, Set.image_pair, Ideal.map_span, Set.image_pair]
        simp only [RingHom.coe_coe, Ideal.Quotient.mkₐ_eq_mk]
        rw [e1, e2, Set.pair_comm])))

/-- **The algebra `ComplexAnalytic.etalePresentation` presents is `StandardEtalePair.Ring`**,
spelled with Mathlib's name for it.

`ComplexAnalytic.etalePresentedAlgebraEquiv` with its target read through
`ComplexAnalytic.standardEtalePair_ring_eq`, so this carries **no** transport: it is the same term,
and the two types are the same type. The reason it is a separate declaration is that
`≃ₐ[ℂ] P.Ring` needs the `Algebra ℂ P.Ring` above to elaborate, while the spelled-out quotient is
what the proof of the equivalence has to see. -/
def etalePresentedAlgebraEquivRing
    (hF : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = P.f)
    (hG : polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ G) = P.g) :
    PresentedAlgebra.{u} (n + 2) (k + 2) (etalePresentation.{u} g F G) ≃ₐ[ℂ] P.Ring :=
  etalePresentedAlgebraEquiv.{u} g F G P hF hG

/-- **Every element of `A[X]` has a polynomial lift**, since
`ComplexAnalytic.polyPresentedAlgebraEquiv` is an equivalence and `Ideal.Quotient.mk` is
surjective. -/
theorem exists_lift_polyPresentedAlgebraEquiv (a : Polynomial (PresentedAlgebra.{u} n k g)) :
    ∃ F : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ,
      polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ F) = a := by
  obtain ⟨x, hx⟩ := (polyPresentedAlgebraEquiv.{u} g).surjective a
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨F, hx⟩

/-- **A standard étale algebra over a presented `ℂ`-algebra is presented**, on two more variables
and two more relations.

This is `ComplexAnalytic.etalePresentedAlgebraEquiv` with the lifts quantified away. A caller who
has the lifts should use that one: it is the same statement with the isomorphism in hand rather
than under an existential. -/
theorem exists_presentation_standardEtale :
    ∃ F G : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ,
      Nonempty (PresentedAlgebra.{u} (n + 2) (k + 2) (etalePresentation.{u} g F G) ≃ₐ[ℂ]
        P.Ring) := by
  obtain ⟨F, hF⟩ := exists_lift_polyPresentedAlgebraEquiv.{u} g P.f
  obtain ⟨G, hG⟩ := exists_lift_polyPresentedAlgebraEquiv.{u} g P.g
  exact ⟨F, G, ⟨etalePresentedAlgebraEquivRing.{u} g F G P hF hG⟩⟩

/-- **The structure map `A ⟶ A_ét`, as a morphism of presentations.**

Mind the direction, which is the one `ComplexAnalytic.PresHom` runs in: a
`ComplexAnalytic.PresHom (etalePresentation g F G) g` has ring map `A → A_ét` and induces a
morphism of analytic spaces the other way, which is the projection of the étale cover to its base.

It is `ComplexAnalytic.PresHom.ofRename` at the inclusion of the old variables, so it costs no
commutative algebra: the old relations are literally among the new ones. -/
def etalePresHom : PresHom.{u} (etalePresentation.{u} g F G) g :=
  PresHom.ofRename (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (by
    intro j
    have hj : MvPolynomial.rename
        (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (g j) =
        polyPresentation.{u} (polyPresentation.{u} g) j := by
      simp [polyPresentation, MvPolynomial.rename_rename]
    rw [hj, presentationIdeal_etalePresentation.{u} g F G]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩))

end

end ComplexAnalytic

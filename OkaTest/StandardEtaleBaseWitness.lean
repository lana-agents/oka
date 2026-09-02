/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# A `k ≥ 1` witness for the local isomorphism over a presented base

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom`
(`Oka/Analytification/StandardEtaleLocalIsoBase.lean`) says that the analytification of a standard
étale morphism over a **presented** base is a local isomorphism onto that base, at every `k`. Its
own `## What is not here` said that no `k ≥ 1` instance was exhibited, so that the theorem's new
content — everything beyond `k = 0`, which
`Oka/Analytification/StandardEtaleLocalIso.lean` already had — was unwitnessed. **This file is
that instance**, and it is an instantiation and not a construction: no analysis, no implicit
function theorem of either kind, and no new declaration under `Oka/`.

## The pair, and why it is not the one that bullet suggested

The bullet named `ComplexAnalytic.sqSubOnePair` (`OkaTest/OpenBaseFiniteness.lean`) as the cheapest
route, since it is a `StandardEtalePair` over an arbitrary commutative ring. It is cheap and it is
**degenerate**: `ComplexAnalytic.sqSubOnePair_X` pins the class of `X` in its standard étale
algebra to `−1`, and over a base in which `2` is a unit — every `ComplexAnalytic.PresentedAlgebra`
is a `ℂ`-algebra — `ComplexAnalytic.sqSubOneRingEquiv` then identifies that algebra with the base
itself. A theorem about local isomorphisms fired at an isomorphism is a witness, but it is the
weakest one available.

What is here instead is the **square-root cover**, `f = X² − C a` and `g = X` over any `ℂ`-algebra
and any `a` in it (`ComplexAnalytic.sqrtCoverPair`). It is the opposite case:
`ComplexAnalytic.exists_ne_hasMap_sqrtCoverPair_four` exhibits **two distinct** points of one
fibre, so nothing forces the class of `X` and the algebra is not the base. That control is over
`ℂ` and it is the whole of what this file proves about degeneracy — see *What is not here*.

## The two lifts are the two computations `ComplexAnalytic.condF_eq` already runs

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom` takes a `StandardEtalePair` over
`ComplexAnalytic.PresentedAlgebra n k g` together with two polynomials of `ℂ^(n+1)` lifting its
`f` and `g` through `ComplexAnalytic.polyPresentedAlgebraEquiv`. Take the lifts to be
`ComplexAnalytic.sqrtCoverF a = z_n² − a` and `ComplexAnalytic.sqrtCoverG n = z_n`; then the two
hypotheses are `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` and
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_rename` and nothing else — the same two lemmas
`ComplexAnalytic.condF_eq` uses at `k = 0`, with the `change` that file needs replaced by the
`rw` an `abbrev` written in those two spellings admits.

So `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover` holds at **every** `n`,
`k`, `g` and `a`, and the `k ≥ 1` witness is one application of it.

## The base, and why this one

`ComplexAnalytic.hyperbolaBase` is `z₀z₁ − 1` in `ℂ²`: `k = 1`, and the two things that make it a
base rather than a formality are both proved here. `ComplexAnalytic.hyperbolaPoint` is a point of
its analytification, so `X^an` is **not empty** — a presentation whose analytification is empty
would make the conclusion true and vacuous. `ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero` is
the origin failing the relation, so `X^an` is **not all of `ℂ²`** either, which is what separates
`k = 1` from `k = 0` written with a relation that says nothing. The `a` inverted over it is `z₀`,
which is a unit on that base, so the cover is the square root of a nowhere-vanishing function.

## Main definitions

- `ComplexAnalytic.sqrtCoverPair`: **the pair `f = X² − C a`, `g = X`** over an arbitrary
  `ℂ`-algebra.
- `ComplexAnalytic.sqrtCoverF` and `ComplexAnalytic.sqrtCoverG`: the two lifts, `z_n² − a` and
  `z_n`.
- `ComplexAnalytic.hyperbolaBase`: the hyperbola `z₀z₁ = 1` in `ℂ²`, a presentation with `k = 1`.
- `ComplexAnalytic.hyperbolaPoint`: the point `(1, 1)` of its analytification.

## Main results

- `ComplexAnalytic.sqrtCoverF_eq` and `ComplexAnalytic.sqrtCoverG_eq`: the two lifts are lifts.
- `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover`: **the square-root cover
  of a presented base analytifies to a local isomorphism onto that base**, for every base and
  every `a`.
- `ComplexAnalytic.isLocalIso_hyperbolaSqrtCover`: **the same at `k = 1`**, over the hyperbola — the
  witness this file exists for.
- `ComplexAnalytic.hasMap_two_sqrtCoverPair_four`,
  `ComplexAnalytic.hasMap_neg_two_sqrtCoverPair_four` and
  `ComplexAnalytic.exists_ne_hasMap_sqrtCoverPair_four`: **two distinct points of one fibre**, so
  `ComplexAnalytic.sqrtCoverPair` is not the degenerate pair.
- `ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero`: the origin is off the hyperbola, so the base
  is a proper subset of `ℂ²`.

## What is not here

* **No `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` at `k ≥ 1`.** Unrestricted finiteness there
  is false — `Oka/Analytification/MonicHypersurface.lean` carries the counterexample — and this
  file witnesses the local-isomorphism field alone, which is the field
  `Oka/Analytification/StandardEtaleLocalIsoBase.lean` supplies.
* **Nothing is proved about the étale algebra over `ComplexAnalytic.hyperbolaBase` itself.** The
  two-point fibre above is over `ℂ` at `a = 4`, which is enough to refute *"the class of `X` is
  forced"* for `ComplexAnalytic.sqrtCoverPair` as a family, and it is **not** a statement that the
  cover of the hyperbola is connected, non-trivial, or anything else. A reader who wants that
  wants a statement nobody here has made.
* **No non-degenerate instantiation of `ComplexAnalytic.sqSubOnePair`.** The degeneracy recorded
  above is that file's own two theorems read together, not a new one.
* **No claim that this is the smallest `k ≥ 1` witness**, or that a base with `k = 1` and no
  point would not also have been an instance. It would; it would just say nothing.

## A name that is taken, and is a different object

`OkaTest/HypersurfaceFinite.lean` already owns `ComplexAnalytic.sqrtG`: a **monic polynomial**
`X² − x₀` over `ℂ[x₀, x₁]`, the second square root in that file's `{x₁² = x₀} ∩ {x₂² = x₀}`. It is
not this file's `g`, and the `sqrtCover` prefix here is what keeps the two apart — Lean refuses
the collision outright, so this is a naming note and not a defect either file had.

## Relation to `ComplexAnalytic.condPair`

`ComplexAnalytic.condPair` (`OkaTest/StandardEtaleCond.lean`) is `ComplexAnalytic.sqrtCoverPair` at
`n = 1`, `k = 0` and `a` the class of `z₀`, so this file's pair subsumes it. **That file is not
refactored onto it here.** Its subject is `StandardEtalePair.cond` *at a point* and its two
points, its module docstring argues its data at length, and rewriting it would put a second and
unrelated narrative into this change. The duplication is one `def` with four fields and it is
named here rather than hidden.
-/

open MvPolynomial Polynomial

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The square-root pair over an arbitrary `ℂ`-algebra -/

/-- **The pair `f = X² − C a`, `g = X`**, over any `ℂ`-algebra.

`monic_f` is `Polynomial.monic_X_pow_sub_C`. `cond` is
`derivative f * C (2⁻¹) + f * 0 = g ^ 1`, which is `C 2 * X * C 2⁻¹ = X`; the inverse of `2` is
`algebraMap ℂ R 2⁻¹`, and that is the one step where `R` is used as a `ℂ`-algebra rather than as a
commutative ring. `IsUnit (2 : R)` would do instead and is not the hypothesis the consumer has:
every `ComplexAnalytic.PresentedAlgebra` is a `ℂ`-algebra by construction. -/
def sqrtCoverPair {R : Type*} [CommRing R] [Algebra ℂ R] (a : R) : StandardEtalePair R where
  f := Polynomial.X ^ 2 - Polynomial.C a
  monic_f := Polynomial.monic_X_pow_sub_C _ two_ne_zero
  g := Polynomial.X
  cond := by
    refine ⟨Polynomial.C (algebraMap ℂ R (2⁻¹ : ℂ)), 0, 1, ?_⟩
    have h2 : (2 : R) * algebraMap ℂ R (2⁻¹ : ℂ) = 1 := by
      rw [show (2 : R) = algebraMap ℂ R (2 : ℂ) from (map_ofNat _ 2).symm, ← map_mul]
      norm_num
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero,
      Nat.cast_ofNat, pow_one]
    rw [mul_right_comm, ← Polynomial.C_mul, h2, map_one, one_mul]
    norm_num

/-- The `f` of `ComplexAnalytic.sqrtCoverPair`, by `rfl`.

This and the next exist so that **nothing below has to `rw` or `simp` at
`ComplexAnalytic.sqrtCoverPair` itself**: unfolding a definition that way plants an auto-generated
equation lemma under its own name, which `OkaTest/StandardEtaleCond.lean`'s module docstring
records happening once and says how it was found. -/
@[simp]
theorem sqrtCoverPair_f {R : Type*} [CommRing R] [Algebra ℂ R] (a : R) :
    (sqrtCoverPair a).f = Polynomial.X ^ 2 - Polynomial.C a := rfl

/-- The `g` of `ComplexAnalytic.sqrtCoverPair`, by `rfl`. -/
@[simp]
theorem sqrtCoverPair_g {R : Type*} [CommRing R] [Algebra ℂ R] (a : R) :
    (sqrtCoverPair a).g = Polynomial.X := rfl

/-! ### The control: the class of `X` is not forced -/

/-- **`2` is a point of the fibre of `ComplexAnalytic.sqrtCoverPair (4 : ℂ)`.**

`StandardEtalePair.HasMap x` is `aeval x f = 0` together with `IsUnit (aeval x g)`, and here that
is `2² − 4 = 0` and `IsUnit (2 : ℂ)`. -/
theorem hasMap_two_sqrtCoverPair_four : (sqrtCoverPair (4 : ℂ)).HasMap (2 : ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [sqrtCoverPair_f]; norm_num
  · rw [sqrtCoverPair_g, Polynomial.aeval_X]; exact isUnit_iff_ne_zero.2 (by norm_num)

/-- **And so is `−2`**, which is the point of stating either.

`ComplexAnalytic.sqSubOnePair_X` pins the class of `X` in that pair's standard étale algebra to
`−1` — both relations are used and the algebra collapses onto the base. Here two distinct elements
of the same `ℂ` satisfy `StandardEtalePair.HasMap`, so no relation pins the class of `X` down and
the same collapse cannot happen. **That is a statement about `ComplexAnalytic.sqrtCoverPair` at one
`ℂ`-algebra and one `a`**, which is all that is needed to separate it from the degenerate pair,
and it is not a statement about the cover of any particular base. -/
theorem hasMap_neg_two_sqrtCoverPair_four : (sqrtCoverPair (4 : ℂ)).HasMap (-2 : ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [sqrtCoverPair_f]; norm_num
  · rw [sqrtCoverPair_g, Polynomial.aeval_X]; exact isUnit_iff_ne_zero.2 (by norm_num)

/-- **The fibre of `ComplexAnalytic.sqrtCoverPair (4 : ℂ)` has at least two points**, which is
the two theorems above with the distinctness they are stated for.

`ComplexAnalytic.sqSubOnePair` admits no such pair over any base: its `X` is `−1` there and
nothing else. -/
theorem exists_ne_hasMap_sqrtCoverPair_four :
    ∃ x y : ℂ, x ≠ y ∧ (sqrtCoverPair (4 : ℂ)).HasMap x ∧ (sqrtCoverPair (4 : ℂ)).HasMap y :=
  ⟨2, -2, by norm_num, hasMap_two_sqrtCoverPair_four, hasMap_neg_two_sqrtCoverPair_four⟩

/-! ### The two polynomial lifts -/

/-- **The polynomial being inverted**: the new variable `z_n`, which is
`ComplexAnalytic.localisationVar n`.

Spelled at that name and not as `MvPolynomial.X (ULift.up (Fin.last n))` so that
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` applies with no rewriting. -/
abbrev sqrtCoverG (n : ℕ) : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  MvPolynomial.X (localisationVar.{u} n)

/-- **The polynomial cutting out the hypersurface**: `z_n² − a`, the square root of `a`.

`a` is read one variable up along `ComplexAnalytic.localisationIncl`, which is the spelling
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_rename` is stated at. -/
abbrev sqrtCoverF {n : ℕ} (a : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  MvPolynomial.X (localisationVar.{u} n) ^ 2 - MvPolynomial.rename (localisationIncl.{u} n) a

/-- **`ComplexAnalytic.sqrtCoverF a` is a lift of the `f` of `ComplexAnalytic.sqrtCoverPair`** at
the class of `a`.

Two applications of `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` and
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_rename` under `map_sub` and `map_pow`, and nothing
else: `ComplexAnalytic.condF_eq` is the same computation at `k = 0` with two `have`s in front,
which are the observation that its two variables *are* those two spellings and which
`ComplexAnalytic.sqrtCoverF` writes out instead. -/
theorem sqrtCoverF_eq {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (a : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ (sqrtCoverF.{u} a)) =
      (sqrtCoverPair (Ideal.Quotient.mk (presentationIdeal.{u} g) a)).f := by
  rw [sqrtCoverPair_f, map_sub, map_pow, map_sub, map_pow, polyPresentedAlgebraEquiv_mk_X_var,
    polyPresentedAlgebraEquiv_mk_rename]

/-- **`ComplexAnalytic.sqrtCoverG n` is a lift of the `g` of `ComplexAnalytic.sqrtCoverPair`**,
which is `ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` and nothing else. -/
theorem sqrtCoverG_eq {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (a : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    polyPresentedAlgebraEquiv.{u} g (Ideal.Quotient.mk _ (sqrtCoverG.{u} n)) =
      (sqrtCoverPair (Ideal.Quotient.mk (presentationIdeal.{u} g) a)).g := by
  rw [sqrtCoverPair_g]
  exact polyPresentedAlgebraEquiv_mk_X_var.{u} g

/-- **The square-root cover of a presented base analytifies to a local isomorphism onto that
base**, for every base and every `a`.

`ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom` at
`ComplexAnalytic.sqrtCoverPair` and the two lifts above. **The whole content is that its three
hypotheses are jointly satisfiable at every `k`**, which is what its file's `## What is not here`
said nothing below produced. -/
theorem isLocalIso_analytificationMap_etalePresHom_sqrtCover {n k : ℕ}
    (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (a : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} g (sqrtCoverF.{u} a) (sqrtCoverG.{u} n))) :=
  isLocalIso_analytificationMap_etalePresHom.{u} g _ _ _ (sqrtCoverF_eq.{u} g a)
    (sqrtCoverG_eq.{u} g a)

/-! ### A base with `k = 1` -/

/-- **The hyperbola `z₀z₁ = 1` in `ℂ²`**, as a presentation with one relation. -/
abbrev hyperbolaBase : Fin 1 → MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  ![MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1) - 1]

/-- The point `(1, 1)` of `ℂ²`. -/
abbrev hyperbolaPt : ULift.{u} (Fin 2) → ℂ := fun _ ↦ 1

/-- **The relation vanishes at `(1, 1)`**, since `1 · 1 − 1 = 0`. -/
theorem eval_hyperbolaBase_hyperbolaPt (j : Fin 1) :
    MvPolynomial.eval hyperbolaPt.{u} (hyperbolaBase.{u} j) = 0 := by
  fin_cases j
  change MvPolynomial.eval hyperbolaPt.{u}
    (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1) - 1) = 0
  simp

/-- **The base's analytification is not empty**, which is what stops the theorem below being true
and vacuous. `ComplexAnalytic.mem_zeroLocus_polySection_iff` reduces membership to the evaluation
above, and `Fin 1` is one case. -/
def hyperbolaPoint : AnalyticSpace.analytification.{u} hyperbolaBase.{u} :=
  ⟨⟨hyperbolaPt.{u}, trivial⟩,
    (mem_zeroLocus_polySection_iff.{u} _ _).2 eval_hyperbolaBase_hyperbolaPt.{u}⟩

/-- **And it is not all of `ℂ²`**: the relation is `−1` at the origin.

Together with `ComplexAnalytic.hyperbolaPoint` this is what makes `k = 1` here a base and not a
relation that says nothing — a presentation whose single relation is `0` has `k = 1` and the same
analytification as `k = 0`. -/
theorem eval_hyperbolaBase_zero_ne_zero :
    MvPolynomial.eval (fun _ ↦ (0 : ℂ)) (hyperbolaBase.{u} 0) ≠ 0 := by
  change MvPolynomial.eval (fun _ ↦ (0 : ℂ))
    (MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1) - 1) ≠ 0
  simp

/-- **The witness: `k = 1`.** The square root of `z₀` over the hyperbola `z₀z₁ = 1` analytifies to
a local isomorphism onto the hyperbola's analytification.

One application of `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_sqrtCover`. This
is the instance `Oka/Analytification/StandardEtaleLocalIsoBase.lean` recorded as absent, and the
only
thing that makes it more than a restatement of that theorem is
`ComplexAnalytic.hyperbolaPoint` and `ComplexAnalytic.eval_hyperbolaBase_zero_ne_zero`, which say
the base is a proper non-empty subset of `ℂ²`. -/
theorem isLocalIso_hyperbolaSqrtCover :
    AnalyticSpace.IsLocalIso (analytificationMap.{u} (etalePresHom.{u} hyperbolaBase.{u}
      (sqrtCoverF.{u} (MvPolynomial.X (ULift.up 0))) (sqrtCoverG.{u} 2))) :=
  isLocalIso_analytificationMap_etalePresHom_sqrtCover.{u} hyperbolaBase.{u} _

end

end ComplexAnalytic

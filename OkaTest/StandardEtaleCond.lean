/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# `StandardEtalePair.cond` at a point, on a pair that exists and at a point that is there

`ComplexAnalytic.eval_pderiv_ne_zero` and `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` take a
`StandardEtalePair` over a `ComplexAnalytic.PresentedAlgebra`, two polynomial lifts, and a point
at which the relations and `F` vanish and `G` does not. **Five hypotheses, and if no data
satisfies all five the theorems are true and say nothing.** This file builds data that does.

## The data, and why it is this data

`ComplexAnalytic.condBase` is the **empty** base — no relations, one variable — so
`ComplexAnalytic.polyPresentation` of it is the empty family and the `hx` hypothesis is
`Fin.elim0`. Over it, `ComplexAnalytic.condF` is `z₁² − z₀` and `ComplexAnalytic.condG` is `z₁`:
the square-root cover of the line, punctured at the branch point.

**That is the shape of taxis #1112's `Pex` and it is not `Pex`.** `Pex` is
`f = X² − C X`, `g = X` over `ℂ[X]`, exhibited on that thread to show the *unrestricted*
`IsFiniteEtale` statement false, by way of a non-closed image; nothing about it is a claim that
some point satisfies the five hypotheses above, and quoting it would produce no point. What is
here is the same pair read over `ComplexAnalytic.PresentedAlgebra 1 0` — built rather than
quoted — with the point supplied.

**The pair's `f` and `g` are defined as the images of `condF` and `condG`**, so
`ComplexAnalytic.condF_eq` and `ComplexAnalytic.condG_eq` are computations of the equivalence and
not choices; `monic_f` is `Polynomial.monic_X_pow_sub_C` and `cond` holds at `p₁ = C (1/2)`,
`p₂ = 0`, `n = 1`, since `derivative (X² − C a)` is `C 2 * X`.

## The two points, and the second is the one that earns the file

* `ComplexAnalytic.condPoint` is `(1, 1)`: on the hypersurface, off the vanishing of `G`. There
  `ComplexAnalytic.eval_pderiv_ne_zero` applies, and
  `ComplexAnalytic.eval_pderiv_condF_condPoint` says the derivative is `2` — so the conclusion is
  a statement about a number this file also computes, and not a `≠ 0` that could have been free.
* `ComplexAnalytic.condOrigin` is `(0, 0)`: on the same hypersurface, **and at the vanishing of
  `G`**. There the derivative is `0`. So `hGx` is not a removable hypothesis, and the theorem
  above is not an instance of a theorem with one fewer hypothesis. That is the locus a standard
  étale algebra inverts away, and this is the file's control.

## Main results

- `ComplexAnalytic.eval_pderiv_condF_condPoint_ne_zero` and
  `ComplexAnalytic.eval_pderiv_condF_condHyperPoint_ne_zero`: the two library theorems applied,
  the second at a point of the hypersurface's analytification rather than at a bare tuple.
- `ComplexAnalytic.eval_pderiv_condF_condPoint` and
  `ComplexAnalytic.eval_pderiv_condF_condOrigin`: the derivative is `2` at the first point and
  `0` at the second — the non-vacuity and the control.

## What is not checked here

* **Nothing about `ComplexAnalytic.etalePresentation` or its analytification.** This is the
  algebraic hypothesis alone; whether the étale presentation's analytification is a local
  isomorphism needs the restriction to `D(G)` and a cut-out datum. **This bullet said *"only the
  second of those is still absent"*; at `k = 0` neither is, and the count it gives goes from one
  to zero.** `ComplexAnalytic.isLocalIso_ofRestrict_comp_proj_of_pderiv`
  (`Oka/AnalyticSpace/SimpleZeroTopology.lean`) takes an arbitrary open subspace of the source
  and asks the derivative hypothesis only there, the datum is
  `ComplexAnalytic.isCutOutBy_analytificationInclHom_hypersurface`
  (`Oka/Analytification/StandardEtaleLocalIso.lean`), and
  `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp` joins the two end to end.
  **The reading taken here is that the two absences this bullet named are discharged, and not
  that the question is closed**: everything there is stated at `k = 0`, and over a general base it
  is a different theorem. **This bullet went on to price that theorem — *"needing an implicit
  function theorem relative to `X^an` that `Oka/Analysis/Calculus/Implicit.lean` does not have"* —
  and that price is false**, as `Oka/Analytification/StandardEtaleLocalIsoBase.lean`'s titled
  section says at length: the step from `k = 0` to `k ≥ 1` takes no analysis at all, and
  `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom` is the theorem, at every `k`. Of
  the two statements over a general base it is the **projection** one that is untouched, and that
  one is false rather than expensive. What is not checked *here* is unchanged: this file is the
  algebraic hypothesis and nothing else, and `OkaTest/StandardEtaleLocalIsoBase.lean` is where the
  `k ≥ 1` witness is.
* **No claim that this is the smallest witness, or that one exists for every pair.** For `F` a
  unit the hypersurface is empty and there is no point at all.
* **Nothing about `Algebra.Etale`.** `ComplexAnalytic.condPair` is a `StandardEtalePair` because
  its four fields are discharged, and Mathlib's étale instance is neither used nor checked.
-/

open MvPolynomial Polynomial ComplexAnalytic

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The data -/

/-- **The empty base**: no relations, in one variable, so `ComplexAnalytic.polyPresentation` of it
is the empty family and the vanishing hypothesis of `ComplexAnalytic.eval_pderiv_ne_zero` is
`Fin.elim0`. -/
abbrev condBase : Fin 0 → MvPolynomial (ULift.{u} (Fin 1)) ℂ := fun j ↦ j.elim0

/-- The polynomial cutting out the hypersurface: `z₁² − z₀`, the square-root cover of the line. -/
abbrev condF : MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  MvPolynomial.X (ULift.up 1) ^ 2 - MvPolynomial.X (ULift.up 0)

/-- The polynomial being inverted: `z₁`, which vanishes exactly at the branch point. -/
abbrev condG : MvPolynomial (ULift.{u} (Fin 2)) ℂ := MvPolynomial.X (ULift.up 1)

/-- The class of `z₀` in the base algebra, which is the constant term of the pair's `f`. -/
abbrev condRoot : PresentedAlgebra.{u} 1 0 condBase.{u} :=
  Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up 0))

/-- **`ComplexAnalytic.condF` is a lift of `X² − C condRoot`.**

`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` for the new variable and
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_rename` for the old one; the two `have`s are the
observation that `z₁` *is* `ComplexAnalytic.localisationVar 1` and that `z₀` *is* `z₀` renamed
along `ComplexAnalytic.localisationIncl`, both by `rfl`.

**The `change` is not a `rw [condF]`, here and in the four proofs below that unfold this file's
data.** A `rw` at a definition plants an auto-generated equation lemma under its own name, and a
first head of this file left one under `ComplexAnalytic.condF`'s that way — it is not in the
environment now, which is the point. `comm -13` on `scripts/DumpOkaDecls.lean`'s output is what
shows such a lemma, not the build. The `change`
costs the unfolded goal written out and leaves the environment with this file's own declarations
and nothing else. -/
theorem condF_eq :
    polyPresentedAlgebraEquiv.{u} condBase.{u} (Ideal.Quotient.mk _ condF.{u}) =
      Polynomial.X ^ 2 - Polynomial.C condRoot.{u} := by
  have h0 : (MvPolynomial.X (ULift.up 0) : MvPolynomial (ULift.{u} (Fin 2)) ℂ) =
      MvPolynomial.rename (localisationIncl.{u} 1) (MvPolynomial.X (ULift.up 0)) := by
    rw [MvPolynomial.rename_X]
    rfl
  have h1 : (MvPolynomial.X (ULift.up 1) : MvPolynomial (ULift.{u} (Fin 2)) ℂ) =
      MvPolynomial.X (localisationVar.{u} 1) := rfl
  change polyPresentedAlgebraEquiv.{u} condBase.{u} (Ideal.Quotient.mk _
    (MvPolynomial.X (ULift.up 1) ^ 2 - MvPolynomial.X (ULift.up 0))) = _
  rw [h0, h1, map_sub, map_pow, map_sub, map_pow, polyPresentedAlgebraEquiv_mk_X_var,
    polyPresentedAlgebraEquiv_mk_rename]

/-- **`ComplexAnalytic.condG` is a lift of `Polynomial.X`**, which is
`ComplexAnalytic.polyPresentedAlgebraEquiv_mk_X_var` and nothing else. -/
theorem condG_eq :
    polyPresentedAlgebraEquiv.{u} condBase.{u} (Ideal.Quotient.mk _ condG.{u}) = Polynomial.X :=
  polyPresentedAlgebraEquiv_mk_X_var.{u} condBase.{u}

/-- **A standard étale pair over `ComplexAnalytic.PresentedAlgebra 1 0 condBase`.**

`f` and `g` are the images of `ComplexAnalytic.condF` and `ComplexAnalytic.condG`, written out, so
that the two lift hypotheses of `ComplexAnalytic.eval_pderiv_ne_zero` are the two computations
above rather than choices. `cond` is `derivative f * C (1/2) + f * 0 = g ^ 1`, which is
`C 2 * X * C (1/2) = X`; the inverse of `2` is the class of the constant `1/2`, and `h2` is the
one step where the base algebra is used as a `ℂ`-algebra at all. -/
def condPair : StandardEtalePair (PresentedAlgebra.{u} 1 0 condBase.{u}) where
  f := Polynomial.X ^ 2 - Polynomial.C condRoot.{u}
  monic_f := Polynomial.monic_X_pow_sub_C _ two_ne_zero
  g := Polynomial.X
  cond := by
    refine ⟨Polynomial.C (Ideal.Quotient.mk _ (MvPolynomial.C (2⁻¹ : ℂ))), 0, 1, ?_⟩
    have h2 : (2 : PresentedAlgebra.{u} 1 0 condBase.{u}) *
        Ideal.Quotient.mk (presentationIdeal.{u} condBase.{u}) (MvPolynomial.C (2⁻¹ : ℂ)) = 1 := by
      rw [show (2 : PresentedAlgebra.{u} 1 0 condBase.{u}) =
        Ideal.Quotient.mk (presentationIdeal.{u} condBase.{u}) (MvPolynomial.C (2 : ℂ)) from
        by rw [map_ofNat, map_ofNat], ← map_mul, ← MvPolynomial.C_mul]
      norm_num
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero,
      Nat.cast_ofNat, pow_one]
    rw [mul_right_comm, ← Polynomial.C_mul, h2, map_one, one_mul]
    norm_num

/-! ### The derivative, computed once -/

/-- **The partial derivative of `ComplexAnalytic.condF` in the last variable is `2·z₁`.**

Computed here rather than inside each theorem below, because it is what makes the value at the two
points a computation and not a re-derivation: the point of this file is that one of those values
is nonzero and the other is not. -/
theorem pderiv_condF :
    MvPolynomial.pderiv (localisationVar.{u} 1) condF.{u} =
      2 * MvPolynomial.X (ULift.up 1) := by
  have hne : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ localisationVar.{u} 1 := by
    simp [localisationVar]
  change MvPolynomial.pderiv (localisationVar.{u} 1)
    (MvPolynomial.X (ULift.up 1) ^ 2 - MvPolynomial.X (ULift.up 0)) = _
  rw [map_sub, MvPolynomial.pderiv_X_of_ne hne, sub_zero,
    show (MvPolynomial.X (ULift.up 1) : MvPolynomial (ULift.{u} (Fin 2)) ℂ) =
      MvPolynomial.X (localisationVar.{u} 1) from rfl, sq]
  simp [Derivation.leibniz, two_mul]

/-! ### The point where the theorem applies -/

/-- **The point `(1, 1)`**: on the hypersurface, and off the vanishing of `G`. -/
abbrev condPoint : ULift.{u} (Fin 2) → ℂ := fun _ ↦ 1

/-- `ComplexAnalytic.condF` vanishes at `ComplexAnalytic.condPoint`, since `1² = 1`. -/
theorem eval_condF_condPoint : MvPolynomial.eval condPoint.{u} condF.{u} = 0 := by
  change MvPolynomial.eval condPoint.{u}
    (MvPolynomial.X (ULift.up 1) ^ 2 - MvPolynomial.X (ULift.up 0)) = 0
  simp

/-- `ComplexAnalytic.condG` does not, since it is the coordinate `z₁` and that is `1` there. -/
theorem eval_condG_condPoint : MvPolynomial.eval condPoint.{u} condG.{u} ≠ 0 := by
  change MvPolynomial.eval condPoint.{u} (MvPolynomial.X (ULift.up 1)) ≠ 0
  simp

/-- **`ComplexAnalytic.eval_pderiv_ne_zero` applied**, which is what says its five hypotheses are
jointly satisfiable. -/
theorem eval_pderiv_condF_condPoint_ne_zero :
    MvPolynomial.eval condPoint.{u} (MvPolynomial.pderiv (localisationVar.{u} 1) condF.{u}) ≠ 0 :=
  eval_pderiv_ne_zero.{u} condBase.{u} condF.{u} condG.{u} condPair.{u} condF_eq.{u} condG_eq.{u}
    condPoint.{u} (fun j ↦ j.elim0) eval_condF_condPoint.{u} eval_condG_condPoint.{u}

/-- **And the value is `2`**, computed without the theorem — so the conclusion above is a fact
about a number rather than a `≠ 0` that any nonzero constant would have satisfied. -/
theorem eval_pderiv_condF_condPoint :
    MvPolynomial.eval condPoint.{u}
      (MvPolynomial.pderiv (localisationVar.{u} 1) condF.{u}) = 2 := by
  rw [pderiv_condF]
  simp

/-- **The same point, as a point of the hypersurface's analytification.** The one relation of
`ComplexAnalytic.hypersurfacePresentation condBase condF` is `condF` itself, by `Fin.snoc_last`,
so `Fin.lastCases` reduces the membership to `ComplexAnalytic.eval_condF_condPoint`. -/
def condHyperPoint :
    AnalyticSpace.analytification.{u} (hypersurfacePresentation.{u} condBase.{u} condF.{u}) := by
  refine ⟨⟨condPoint.{u}, trivial⟩, (mem_zeroLocus_polySection_iff.{u} _ _).2 ?_⟩
  refine Fin.lastCases ?_ (fun i ↦ i.elim0)
  rw [show hypersurfacePresentation.{u} condBase.{u} condF.{u} (Fin.last 0) = condF.{u} from
    Fin.snoc_last _ _]
  exact eval_condF_condPoint.{u}

/-- **`ComplexAnalytic.eval_pderiv_ne_zero_of_mem` applied**, at that point. This is the form a
consumer of the stalk theorems holds: one hypothesis about `G`, and the hypersurface membership
carried by the point itself. -/
theorem eval_pderiv_condF_condHyperPoint_ne_zero :
    MvPolynomial.eval
        (condHyperPoint.{u}.1.1 : ULift.{u} (Fin 2) → ℂ)
        (MvPolynomial.pderiv (localisationVar.{u} 1) condF.{u}) ≠ 0 :=
  eval_pderiv_ne_zero_of_mem.{u} condBase.{u} condF.{u} condG.{u} condPair.{u} condF_eq.{u}
    condG_eq.{u} condHyperPoint.{u} eval_condG_condPoint.{u}

/-! ### The control: at the branch point the derivative does vanish -/

/-- **The origin**: on the same hypersurface, and *at* the vanishing of `G`. -/
abbrev condOrigin : ULift.{u} (Fin 2) → ℂ := fun _ ↦ 0

/-- `ComplexAnalytic.condF` vanishes at the origin too, so this really is a second point of the
same hypersurface and not of something else. -/
theorem eval_condF_condOrigin : MvPolynomial.eval condOrigin.{u} condF.{u} = 0 := by
  change MvPolynomial.eval condOrigin.{u}
    (MvPolynomial.X (ULift.up 1) ^ 2 - MvPolynomial.X (ULift.up 0)) = 0
  simp

/-- **And so does `ComplexAnalytic.condG`**, which is the hypothesis
`ComplexAnalytic.eval_pderiv_ne_zero` would need and does not have here. -/
theorem eval_condG_condOrigin : MvPolynomial.eval condOrigin.{u} condG.{u} = 0 := by
  change MvPolynomial.eval condOrigin.{u} (MvPolynomial.X (ULift.up 1)) = 0
  simp

/-- **The derivative vanishes there.** So the non-vanishing of `G` is not a removable hypothesis:
without it the conclusion of `ComplexAnalytic.eval_pderiv_ne_zero` is false at a point of the very
same hypersurface, and the theorem is not an instance of a theorem with one fewer hypothesis. -/
theorem eval_pderiv_condF_condOrigin :
    MvPolynomial.eval condOrigin.{u}
      (MvPolynomial.pderiv (localisationVar.{u} 1) condF.{u}) = 0 := by
  rw [pderiv_condF]
  simp

end

end ComplexAnalytic

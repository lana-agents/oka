/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Analytification.Sheaf
import OkaTest.Analytification

/-!
# Non-vacuity of `analytificationSheafUnitIso`

`ComplexAnalytic.analytificationSheafUnitIso` says the analytification of `𝒪_X` **is**
`𝒪_{X^an}`. The degeneracy an isomorphism statement has is different from the one an exactness
statement has: **an isomorphism between zero objects is free and says nothing.** So the test is
that neither side is zero, and it has to be checked at both ends.

* **The target.** `ComplexAnalytic.not_noZeroDivisors_stalk_analytification_nodeG`
  (`OkaTest/AnalytificationFlatness.lean`) says the stalk of `𝒪_{X^an}` at the node's origin has
  zero divisors. The trivial ring satisfies `NoZeroDivisors` vacuously, so that already forces
  the target to be nonzero — and it forces more, that the space is genuinely singular there.
* **The source.** Nothing before this file rules out `ℂ[x, y] ⧸ (x y)` being the zero ring, which
  would make `𝒪_{Spec A}` zero and the isomorphism vacuous from the other end.
  `presentationIdeal_nodeG_ne_top` below is that check, and it is the new content here: the ideal
  `(x y)` is proper because evaluating at the origin sends `x y` to `0`, which is not a unit
  in `ℂ`.

The two `def`s record applicability at the node with both categories written out, which is the
same site-spelling exercise the rest of this line does at every stage.

## What the free case is for

`ComplexAnalytic.analytificationSheafFreeIso` holds for an **arbitrary** index type, not only a
finite one, because Mathlib's `SheafOfModules.pullbackObjFreeIso` does. That is the base case of
*"the analytification of a coherent sheaf is coherent"*, which is the next item and is not here.
-/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

/-- **The ideal `(x y)` is proper**, so `ℂ[x, y] ⧸ (x y)` is not the zero ring and the source of
the analytification at the node is not a zero category.

Evaluating at the origin takes `x y` to `0`; if `(x y)` were everything it would contain `1`,
whose image is `1`. -/
theorem presentationIdeal_nodeG_ne_top : presentationIdeal nodeG.{u} ≠ ⊤ := by
  rw [presentationIdeal_nodeG, Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have := congrArg (MvPolynomial.eval (fun _ ↦ (0 : ℂ))) hc
  simp [nodePoly] at this

/-- **The algebra being analytified at the node is not the zero ring.** -/
instance nontrivial_quotient_nodeG :
    Nontrivial (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸ presentationIdeal.{u} nodeG.{u}) :=
  Ideal.Quotient.nontrivial_iff.mpr presentationIdeal_nodeG_ne_top.{u}

/-- **The analytification of `𝒪_X` is `𝒪_{X^an}`, at the node**, with both categories written
out. -/
def nodeAnalytificationSheafUnitIso :
    (analytificationSheaf.{u} nodeG.{u}).obj
        (SheafOfModules.unit
          (Spec.locallyRingedSpaceObj
            (CommRingCat.of
              (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸
                presentationIdeal.{u} nodeG.{u}))).ringSheaf) ≅
      SheafOfModules.unit
        (AnalyticSpace.analytification.{u} nodeG.{u}).toLocallyRingedSpace.ringSheaf :=
  analytificationSheafUnitIso.{u} nodeG.{u}

/-- **The analytification of a free sheaf is free, at the node**, on a two-element index type —
so that the statement is exercised somewhere other than at the unit. -/
def nodeAnalytificationSheafFreeIso :
    (analytificationSheaf.{u} nodeG.{u}).obj (SheafOfModules.free (ULift.{u} (Fin 2))) ≅
      SheafOfModules.free (ULift.{u} (Fin 2)) :=
  analytificationSheafFreeIso.{u} nodeG.{u} (ULift.{u} (Fin 2))

end ComplexAnalytic

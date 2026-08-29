/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.OpenBaseProjection

/-!
# Non-vacuity of the holomorphic monic family, at a curve no polynomial cuts out

`Oka/AnalyticSpace/HolomorphicFamily.lean` turns a monic `P : Polynomial (OkaRing V)` into the
family of monic polynomials that the projection theorem over an open base asks for. Its hypotheses
are four and nothing in its statement says they can hold at once — and if the only `P` they held
at were the ones with polynomial coefficients, the file would be a bridge to nowhere new.

**This file exhibits one at which they hold and whose coefficients are not polynomial.** The
curve is

    w² = z·(e^z)²    above the punctured `z`-line,

whose family `X² - C (z·(e^z)²)` has a constant coefficient that is **not a polynomial in `z`**
and is not even the restriction of one, so no family read off an `MvPolynomial` — whose
coefficients are polynomial functions of the base point — is this one.

The parametrisation is `t ↦ (t², t·e^{t²})`, and it is a *global* morphism `ℂ ⟶ ℂ²` restricted to
the part lying over the punctured line — the same construction
`OkaTest/OpenBaseProjection.lean` uses for its parabola, so nothing about the source is new here
and only the family is.

## What each check is for

* `ComplexAnalytic.range_base_curveIncl_eq_zeroLocus` — **the parametrisation is onto the curve**,
  not merely into it. The reverse inclusion is where `ℂ` being algebraically closed is used: a
  point of the curve has `z = t²` for two `t`, and exactly one of them has `t·e^{t²} = w`, because
  the two values differ by a sign.
* `ComplexAnalytic.isFinite_curvePunctured_comp_projRestrict` — the theorem itself, with all four
  hypotheses discharged.
* `ComplexAnalytic.not_injective_base_curvePunctured_comp_projRestrict` — **the composite is not
  injective**, so it is not a closed embedding and
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` does not reach the theorem. The
  composite is `t ↦ t²` on the punctured line, so `1` and `-1` collide. This is what makes the
  witness a genuinely two-sheeted curve rather than a graph, and it is why the family has degree
  `2` and not `1`: the graph of a holomorphic function would be a cheaper witness for the family
  and a useless one for the theorem.
* **The other easy route is closed by `OkaTest/OpenBaseProjection.lean` and is not restated
  here.** `ComplexAnalytic.not_isFinite_projRestrict_punctured` says the projection over the
  punctured line is itself not finite, so `ComplexAnalytic.AnalyticSpace.isFinite_comp` reaches no
  statement over this base; and `ComplexAnalytic.cylinder_punctured_ne_top` says the base is a
  proper open subset. Both are about the base and not about the curve, so they hold verbatim.

## What is not checked here

* **Nothing from a germ.** `ComplexAnalytic.curvePoly` is written down, not produced by the
  Weierstrass preparation theorem, and no statement here says that some germ has it for its
  Weierstrass polynomial. **The obstacle is no longer the index bridge**, which
  `Oka/UliftCoord.lean` now supplies: `LocalOkaRing.exists_congr_monic_realize_of_ne_zero`
  produces a monic polynomial over `OkaRing W` from any nonzero germ, but the `W` it produces is
  whatever the preparation theorem gives, and identifying it with
  `ComplexAnalytic.punctured` and its polynomial with `ComplexAnalytic.curvePoly` would be a
  statement about *this* curve rather than about the bridge.
* **No coefficient that fails to extend.** `ComplexAnalytic.zExp2` is the restriction to the
  punctured line of an entire function, so the cutting section is a restriction of an entire one
  and the cut-out form of the projection theorem could in principle have been used had it been
  available at this shape. **What the witness does show is that the coefficient is not a
  polynomial**, which is the whole gap between this bridge and any bridge out of an
  `MvPolynomial`. A coefficient holomorphic on `V` and defined
  nowhere else — `1/z` is the obvious one — would need a parametrisation built by
  `ComplexAnalytic.AnalyticSpace.okaMapOpen` rather than by restricting a global map, and is not
  built here. **The coefficient itself is no longer the missing part.** `invCoord` and
  `not_restrict_eq_invCoord` of `OkaTest/HolomorphicMapOpen.lean` — *no entire function on `ℂ`
  restricts to `1/z₀`* — are in scope here, on the same open set, since
  `ComplexAnalytic.punctured_eq_punctured` identifies that file's `punctured` with this one's.
  What is missing is the parametrisation above and, with it, an argument that
  `ComplexAnalytic.cylinderSection` inherits its coefficient's non-extension; neither is
  bookkeeping and neither is here.
* **Nothing about stalks, so nothing here is finite étale**, exactly as in
  `OkaTest/OpenBaseProjection.lean` and for the same reason — stated here at that file's width,
  which is what makes it true. The hypothesis of
  `ComplexAnalytic.isIso_stalkMap_comp_projRestrict` is
  `PowerSeries.order (MvPowerSeries.partialEval …) = 1` on the germ of the **cutting section**,
  here `ComplexAnalytic.cylinderSection` at `ComplexAnalytic.curvePoly`, and computing that order
  **for this germ** is a Weierstrass computation nothing in this repository does. Until taxis
  #1191 this bullet said instead that the order was computed on no germ *anywhere in this
  repository*, and that was false when it was written: `OkaTest/SimpleZeroStalk.lean` and
  `OkaTest/GermQuotientDegreeOne.lean` both compute it, and both are ancestors of the commit that
  wrote the sentence — the second by four days and the first by a day and a half. What is true is
  that every one of those computations is on a germ **written down as a polynomial** — a
  coordinate, its square, or a `LocalOkaRing.fromPolynomial` — and this germ is the one shape they
  cannot be, since `ComplexAnalytic.zExp2` is not a polynomial and that is the whole point of the
  file.
* **Nothing about `ComplexAnalytic.IsCutOutBy`.** The image is computed from the parametrisation,
  so the range form of the projection theorem is what is applied. Cut-out data for a morphism of
  *analytic* spaces is never produced in this repository, only assumed.
* **No `Nontrivial` instance for `OkaRing`.** `ComplexAnalytic.nontrivial_okaRing_punctured` is
  proved here for the one open set this file needs it at, by evaluating at a point. The general
  statement — a nonempty `U` makes `OkaRing U` nontrivial — is true, is not in the library, and
  belongs beside `OkaRing` rather than in a test file; it is stated here as a local fact rather
  than added to `Oka/StructureSheaf.lean` by a file that needs it once.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

/-! ### Two holomorphic functions that are not polynomials -/

/-- The single coordinate of `ℂ¹` is analytic at every point; the base case of the two
constructions below. -/
theorem analyticAt_coord0 (x : ULift.{u} (Fin 1) → ℂ) :
    AnalyticAt ℂ (fun z : ULift.{u} (Fin 1) → ℂ ↦ z (ULift.up 0)) x :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ULift.{u} (Fin 1) ↦ ℂ)
    (ULift.up 0)).analyticAt x

/-- **`t ↦ e^{t²}`, as an entire function on `ℂ¹`.** The second coordinate of the
parametrisation below is `t` times this. -/
def expSq : OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  OkaRing.mk (fun t ↦ Complex.exp ((t.1 (ULift.up 0)) ^ 2))
    (okaAnalytic_restrict fun x _ ↦ AnalyticAt.cexp' ((analyticAt_coord0.{u} x).pow 2))

/-- Its value at a point, unfolded.

Not `@[simp]`: `OkaRing.evalHom_apply` already unfolds the left-hand side, exactly as it does for
`ComplexAnalytic.evalHom_coord`, so this is a `rw` lemma and not a normal form. -/
theorem evalHom_expSq {t : ULift.{u} (Fin 1) → ℂ} :
    OkaRing.evalHom (U := ⊤) (x := t) trivial expSq.{u} =
      Complex.exp ((t (ULift.up 0)) ^ 2) :=
  rfl

/-- **`z ↦ z·(e^z)²`, as a holomorphic function on the punctured `z`-line.**

This is the constant coefficient of the family below, and it is the point of the file: it is not
a polynomial in `z`, so no `MvPolynomial` produces this family. -/
def zExp2 : OkaRing (punctured.{u} : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  OkaRing.mk (fun z ↦ z.1 (ULift.up 0) * Complex.exp (z.1 (ULift.up 0)) ^ 2)
    (okaAnalytic_restrict fun x _ ↦
      (analyticAt_coord0.{u} x).mul (((analyticAt_coord0.{u} x).cexp').pow 2))

/-- Its value at a point, unfolded; not `@[simp]`, for the reason
`ComplexAnalytic.evalHom_expSq` gives. -/
theorem evalHom_zExp2 {z : ULift.{u} (Fin 1) → ℂ} (hz : z ∈ punctured.{u}) :
    OkaRing.evalHom hz zExp2.{u} = z (ULift.up 0) * Complex.exp (z (ULift.up 0)) ^ 2 :=
  rfl

/-! ### The curve `w² = z·(e^z)²`, parametrised -/

/-- The pair of entire functions `(t², t·e^{t²})` on `ℂ`, as a family of global sections. -/
def curveFamily : ULift.{u} (Fin 2) → OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  fun j ↦ if j = ULift.up 0 then coord (ULift.up 0) ^ 2
    else coord (ULift.up 0) * expSq.{u}

/-- **The parametrisation of the curve, `ℂ ⟶ ℂ²`, `t ↦ (t², t·e^{t²})`.** -/
def curveIncl : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.complexAffineSpace.{u} 2 :=
  AnalyticSpace.okaMap curveFamily.{u}

/-- **Its underlying map is `t ↦ (t², t·e^{t²})`.** -/
theorem base_curveIncl (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    ((curveIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) =
      fun j ↦ if j = ULift.up 0 then (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ^ 2
        else (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) *
          Complex.exp ((p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ^ 2) := by
  refine funext fun j ↦ ?_
  change okaMapFun curveFamily.{u} _ j = _
  rw [okaMapFun_apply, curveFamily]
  by_cases hj : j = ULift.up 0
  · rw [if_pos hj, if_pos hj, map_pow, evalHom_coord]
  · rw [if_neg hj, if_neg hj, map_mul, evalHom_coord, evalHom_expSq]

/-- **The image of the parametrisation is exactly the curve `w² = z·(e^z)²`.**

The inclusion `⊆` is `ComplexAnalytic.base_curveIncl` at the two indices. The reverse is where
`ℂ` being algebraically closed enters: a square root `t` of `z` exists, and `(t·e^z)² = w²`, so
`w` is `t·e^z` or `-t·e^z` — and `-t` is the other square root, so one of the two parameters
hits `(z, w)` on the nose. -/
theorem range_base_curveIncl_eq_zeroLocus :
    Set.range ((curveIncl.{u}).toLRSHom.base :
        AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) =
      {q : AnalyticSpace.complexAffineSpace.{u} 2 |
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) ^ 2 =
          (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) *
            Complex.exp ((q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0)) ^ 2} := by
  refine Set.ext fun q ↦ ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    change ((curveIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) ^ 2 = _
    rw [base_curveIncl]
    simp only [if_neg (by decide : ¬ (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)) = ULift.up 0),
      if_true]
    ring
  · obtain ⟨t, ht⟩ :=
      IsAlgClosed.exists_pow_nat_eq ((q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0)) two_pos
    simp only [Set.mem_setOf_eq] at hq
    have hfac : ((q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) -
          t * Complex.exp ((q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0))) *
        ((q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) +
          t * Complex.exp ((q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0))) = 0 := by
      linear_combination hq - Complex.exp ((q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0)) ^ 2 * ht
    have key : ∀ c : ℂ, c ^ 2 = (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) →
        c * Complex.exp ((q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0)) =
          (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) →
        q ∈ Set.range ((curveIncl.{u}).toLRSHom.base :
          AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) := by
      intro c hc hcw
      refine ⟨fun _ ↦ c, funext fun j ↦ ?_⟩
      rw [show ((curveIncl.{u}).toLRSHom.base _ : ULift.{u} (Fin 2) → ℂ) = _
        from base_curveIncl.{u} _]
      dsimp only
      obtain ⟨j⟩ := j
      fin_cases j
      · simpa using hc
      · rw [hc]
        simpa using hcw
    rcases mul_eq_zero.1 hfac with h | h
    · exact key t ht (by linear_combination -h)
    · exact key (-t) (by linear_combination ht) (by linear_combination -h)

/-- The first parameter recovered from a point of the curve, `(z, w) ↦ w·e^{-z}`: a continuous
retraction of `ComplexAnalytic.curveIncl`. -/
def curveRetract : AnalyticSpace.complexAffineSpace.{u} 2 →
    AnalyticSpace.complexAffineSpace.{u} 1 :=
  fun q _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) *
    Complex.exp (-(q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0))

/-- **The parametrisation is a closed embedding.**

Embedding by `Function.LeftInverse.isEmbedding` at `ComplexAnalytic.curveRetract`, exactly as for
`ComplexAnalytic.parabolaIncl`; closed because by
`ComplexAnalytic.range_base_curveIncl_eq_zeroLocus` the image is where two continuous functions of
`q` agree. Note that the retraction is where the exponential has to be inverted, and that it can
be: `e^z` never vanishes, which is also why the two sheets of the curve never meet. -/
theorem isClosedEmbedding_base_curveIncl :
    IsClosedEmbedding ((curveIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) where
  toIsEmbedding := by
    refine Function.LeftInverse.isEmbedding (f := curveRetract.{u}) ?_
      (continuous_pi fun _ ↦ (continuous_apply (ULift.up 1)).mul
        ((continuous_apply (ULift.up 0)).neg.cexp))
      (curveIncl.{u}).toLRSHom.base.hom.continuous
    intro p
    refine funext fun l ↦ ?_
    change ((curveIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) *
      Complex.exp (-((curveIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0)) = _
    rw [base_curveIncl]
    simp only [if_neg (by decide : ¬ (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)) = ULift.up 0),
      if_true]
    rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    exact congrArg _ (Subsingleton.elim _ _)
  isClosed_range := by
    have h0 : Continuous fun q : AnalyticSpace.complexAffineSpace.{u} 2 ↦
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) := continuous_apply _
    have h1 : Continuous fun q : AnalyticSpace.complexAffineSpace.{u} 2 ↦
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) := continuous_apply _
    rw [range_base_curveIncl_eq_zeroLocus]
    exact isClosed_eq (h1.pow 2) (h0.mul (h0.cexp.pow 2))

/-! ### The curve above the punctured line, and its family -/

/-- **The curve, restricted to the part of it lying over the punctured `z`-line.**

Nothing is proved to build it: the source is the preimage of the cylinder, which is what
`ComplexAnalytic.AnalyticSpace.restrictHom` takes. -/
def curvePunctured :
    (AnalyticSpace.complexAffineSpace.{u} 1).restrict
        ((Opens.map (curveIncl.{u}).toLRSHom.base).obj (cylinder punctured.{u})) ⟶
      (AnalyticSpace.complexAffineSpace.{u} 2).restrict (cylinder punctured.{u}) :=
  AnalyticSpace.restrictHom curveIncl.{u} (cylinder punctured.{u})

/-- **The monic quadratic `X² - C (z·(e^z)²)` over the punctured `z`-line**, as an honest element
of `Polynomial (OkaRing punctured)`.

Its constant coefficient `ComplexAnalytic.zExp2` is not a polynomial in `z`, which is the whole
reason this witness is out of reach of a bridge that starts from an `MvPolynomial`. -/
def curvePoly : Polynomial (OkaRing (punctured.{u} : Opens (ULift.{u} (Fin 1) → ℂ))) :=
  Polynomial.X ^ 2 - Polynomial.C zExp2.{u}

/-- **`OkaRing` of the punctured line is nontrivial**, because a holomorphic function on a
nonempty open set is determined by more than nothing: `0` and `1` differ at the point `1`.

Needed because `Polynomial.monic_X_pow_sub_C` asks for it, and there is no general instance —
see this file's `## What is not checked here`. -/
theorem nontrivial_okaRing_punctured :
    Nontrivial (OkaRing (punctured.{u} : Opens (ULift.{u} (Fin 1) → ℂ))) := by
  have hx : (fun _ ↦ (1 : ℂ) : ULift.{u} (Fin 1) → ℂ) ∈ punctured.{u} :=
    (mem_punctured_iff.{u} _).2 one_ne_zero
  refine ⟨0, 1, fun h ↦ ?_⟩
  have h0 := congrArg (fun f ↦ OkaRing.evalHom hx f) h
  simp only [map_zero, map_one] at h0
  exact zero_ne_one h0

/-- **It is monic**, which is the one hypothesis
`ComplexAnalytic.isFinite_comp_projRestrict_of_monic` asks of it. -/
theorem monic_curvePoly : (curvePoly.{u}).Monic :=
  haveI := nontrivial_okaRing_punctured.{u}
  Polynomial.monic_X_pow_sub_C _ two_ne_zero

/-- **The family is quadratic and not linear**, which is what a curve with two sheets over the
base needs; a graph would do for the bridge and not for the theorem. -/
theorem natDegree_curvePoly : (curvePoly.{u}).natDegree = 2 :=
  haveI := nontrivial_okaRing_punctured.{u}
  Polynomial.natDegree_X_pow_sub_C

/-- **The section the bridge attaches to `ComplexAnalytic.curvePoly` is `w² - z·(e^z)²`.**

`ComplexAnalytic.cylinderSection` is an algebra homomorphism, so this is `map_sub` and `map_pow`
against its two computation rules; the value of the pulled-back coefficient at a point of the
cylinder is its value at the first coordinate, definitionally. -/
theorem evalHom_cylinderSection_curvePoly {z : ULift.{u} (Fin 2) → ℂ}
    (hz : z ∈ cylinder punctured.{u}) :
    OkaRing.evalHom hz (cylinderSection.{u} punctured.{u} curvePoly.{u}) =
      z (ULift.up 1) ^ 2 - z (ULift.up 0) * Complex.exp (z (ULift.up 0)) ^ 2 := by
  rw [curvePoly, map_sub, map_pow, cylinderSection_X, cylinderSection_C, map_sub, map_pow]
  rfl

/-- **The image of the restricted parametrisation is the zero locus of that section.**

`ComplexAnalytic.mem_range_base_restrictHom_iff` reduces this to the unrestricted image, so the
only computation is `ComplexAnalytic.evalHom_cylinderSection_curvePoly` and `sub_eq_zero`. -/
theorem range_base_curvePunctured :
    Set.range ((curvePunctured.{u}).toLRSHom.base) =
      {z | OkaRing.evalHom z.2 (cylinderSection.{u} punctured.{u} curvePoly.{u}) = 0} :=
  Set.ext fun z ↦
    (mem_range_base_restrictHom_iff curveIncl.{u}.toLRSHom (cylinder punctured.{u}) z).trans (by
      rw [range_base_curveIncl_eq_zeroLocus]
      simp only [Set.mem_setOf_eq, evalHom_cylinderSection_curvePoly.{u} z.2, sub_eq_zero]
      exact Iff.rfl)

/-- **The projection of the curve `w² = z·(e^z)²` above the punctured line to that line is
finite** — the hypotheses of `ComplexAnalytic.isFinite_comp_projRestrict_of_monic` all hold at
once, at a family no `MvPolynomial` produces. -/
theorem isFinite_curvePunctured_comp_projRestrict :
    AnalyticSpace.IsFinite
      (curvePunctured.{u} ≫ AnalyticSpace.projRestrict punctured.{u}) :=
  isFinite_comp_projRestrict_of_monic.{u} punctured.{u} curvePoly.{u} curvePunctured.{u}
    (isClosedEmbedding_base_restrictHom isClosedEmbedding_base_curveIncl.{u} _)
    monic_curvePoly.{u} range_base_curvePunctured.{u}

/-! ### Why the closed-embedding route to finiteness is unavailable -/

section NotInjective

/-- A nonzero constant `t`, as a point of the source of `ComplexAnalytic.curvePunctured`: the
source is where `t²` is nonzero, so a nonzero `t` lies in it. -/
def curveSource {c : ℂ} (hc : c ≠ 0) :
    (AnalyticSpace.complexAffineSpace.{u} 1).restrict
      ((Opens.map (curveIncl.{u}).toLRSHom.base).obj (cylinder punctured.{u})) :=
  ⟨fun _ ↦ c, by
    change (AnalyticSpace.proj.{u} 1).toLRSHom.base
      ((curveIncl.{u}).toLRSHom.base (fun _ ↦ c)) ∈ punctured.{u}
    refine (mem_punctured_iff.{u} _).2 fun hzero ↦ ?_
    have key := congrFun
      (uliftSnocHomeo_fst.{u} ((curveIncl.{u}).toLRSHom.base (fun _ ↦ c))) (ULift.up 0)
    have h2 : ((curveIncl.{u}).toLRSHom.base (fun _ ↦ c) : ULift.{u} (Fin 2) → ℂ)
        (ULift.up (Fin.castSucc 0)) = 0 := key.trans hzero
    rw [base_curveIncl] at h2
    simp only [if_pos (by rfl : (ULift.up (Fin.castSucc 0) : ULift.{u} (Fin 2)) = ULift.up 0)] at h2
    exact pow_ne_zero 2 hc h2⟩

/-- **The composite sends `t` to `t²`**, in the one coordinate of the base. -/
theorem base_curveSource_comp {c : ℂ} (hc : c ≠ 0) :
    (((curvePunctured.{u} ≫ AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base
      (curveSource.{u} hc)).1 : ULift.{u} (Fin 1) → ℂ) = fun _ ↦ c ^ 2 := by
  have h1 : ((curvePunctured.{u} ≫ AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base
      (curveSource.{u} hc)).1 =
      (uliftSnocHomeo.{u} 1 ((curveIncl.{u}).toLRSHom.base (fun _ ↦ c))).1 := by
    change ((AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base
      ((curvePunctured.{u}).toLRSHom.base (curveSource.{u} hc))).1 = _
    rw [base_projRestrict_eq]
    exact congrArg (fun w ↦ (uliftSnocHomeo.{u} 1 w).1)
      (base_restrictHom (curveIncl.{u}).toLRSHom (cylinder punctured.{u}) _)
  rw [h1]
  refine funext fun j ↦ ?_
  change ((curveIncl.{u}).toLRSHom.base (fun _ ↦ c) : ULift.{u} (Fin 2) → ℂ)
    (ULift.up j.down.castSucc) = c ^ 2
  rw [base_curveIncl]
  simp [Fin.castSucc, Subsingleton.elim j.down 0]

/-- **The composite is not injective**, so it is not a closed embedding and
`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding` does not prove the theorem above:
the two square roots of `1` lie over the same point of the base, and both survive the puncture.

Together with `ComplexAnalytic.not_isFinite_projRestrict_punctured` in
`OkaTest/OpenBaseProjection.lean` this closes both cheap routes to the statement. -/
theorem not_injective_base_curvePunctured_comp_projRestrict :
    ¬ Function.Injective
      ((curvePunctured.{u} ≫ AnalyticSpace.projRestrict punctured.{u}).toLRSHom.base) := by
  intro hinj
  have hne : (curveSource.{u} (one_ne_zero (α := ℂ))) ≠
      curveSource.{u} (neg_ne_zero.2 (one_ne_zero (α := ℂ))) := by
    intro h
    have := congrArg (fun p ↦ (p.1 : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)) h
    simp only [curveSource] at this
    exact one_ne_zero (α := ℂ) (by linear_combination this / 2)
  refine hne (hinj (Subtype.ext ?_))
  rw [base_curveSource_comp, base_curveSource_comp]
  norm_num

end NotInjective

end ComplexAnalytic

end

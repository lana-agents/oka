/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.SimpleZeroPolynomial
import Oka.GermDerivative
import Oka.Analysis.Calculus.Implicit

/-!
# A hypersurface with a simple zero everywhere projects by a local isomorphism

`Oka/AnalyticSpace/SimpleZeroStalk.lean` proves that a hypersurface `i : X ⟶ ℂ^(n+1)` with a
simple zero along the last axis at a point projects **isomorphically on the stalk** there, and
says in its own `## What is not here` that *"nothing below says anything about the underlying map
of `i ≫ p`, not even that it is open"*. This file supplies that missing half and assembles the
two: with the simple-zero condition at **every** point of `X`, the composite `i ≫ p` is a
`ComplexAnalytic.AnalyticSpace.IsLocalIso`.

The topological half is the implicit function theorem, and it is not proved here either: it is
`isLocalHomeomorph_coordProj_comp_of_isEmbedding` in `Oka/Analysis/Calculus/Implicit.lean`, a
statement about level sets of a strictly differentiable function on `ι → 𝕜` with no complex
analysis in it. What this file does is discharge that theorem's four hypotheses from
`ComplexAnalytic.IsCutOutBy`, which is one paragraph each:

* **the embedding.** `IsCutOutBy.isClosedEmbedding` is one of the four fields.
* **the level set.** `IsCutOutBy.range_base` says the image is where every germ is a non-unit,
  and `germ_mem_maximalIdeal_iff` turns that into the vanishing of the function
  (`ComplexAnalytic.range_base_eq_zeroSet`).
* **strict differentiability.** `OkaRing.analyticAt_toGlobalFun` and
  `AnalyticAt.hasStrictFDerivAt`; the cutting section is holomorphic on all of `ℂ^(n+1)`, so this
  holds at every point and not only on the hypersurface.
* **the nonvanishing derivative**, and this is the step that had nothing to stand on:
  `OkaRing.coeff_single_one_germ` (`Oka/GermDerivative.lean`) says that the coefficient of the
  last variable in the germ **is** the derivative in that direction, for an arbitrary holomorphic
  cutting section. So the hypothesis below is the same one the stalk half already takes, with no
  polynomial and no extra data.

## Why the hypothesis is at every point, and the stalk half's is not

`ComplexAnalytic.AnalyticSpace.IsLocalIso` asks for a local homeomorphism, which is a condition on
the *whole* space, so a pointwise hypothesis cannot suffice for it. The stalk field is pointwise
and this file quantifies its input; the topological field is not, and the implicit function
theorem is applied at each point separately with the hypothesis at that point. Nothing here is
uniform in the point, and nothing needs to be.

## Main results

- `ComplexAnalytic.range_base_eq_zeroSet`: **the image of a cut-out by one section is the zero
  set of that section**, as a set of functions rather than as a set of germs.
- `ComplexAnalytic.base_comp_uliftProj`: the underlying map of `i ≫ p` is `i.base` followed by
  restriction of coordinates.
- `ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff`: **the underlying map of
  `i ≫ p` is a local homeomorphism** when the linear coefficient of the germ is nonzero at every
  point, and `ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_pderiv`, the same for a
  polynomial cutting section, with the hypothesis read as `MvPolynomial.pderiv`.
- `ComplexAnalytic.isLocalIso_comp_proj_of_coeff` and
  `ComplexAnalytic.isLocalIso_comp_proj_of_pderiv`: **`i ≫ p` is a local isomorphism of complex
  analytic spaces**, the two halves together.
- `ComplexAnalytic.not_mem_range_uliftCastSuccEmb` and
  `ComplexAnalytic.mem_range_uliftCastSuccEmb`: the last coordinate is the only one the
  projection forgets.

## What is not here

* **No finiteness, and so no `ComplexAnalytic.AnalyticSpace.IsFiniteEtale`.** A local isomorphism
  is one of that class's two fields; the other is `ComplexAnalytic.AnalyticSpace.IsFinite`, and
  for the projection of a hypersurface it is the monic case of
  `Oka/Analytification/MonicHypersurface.lean`, which asks for a hypothesis nothing below takes.
  **The gap is real and not an artefact of the proof**, and the reason is a hypersurface this
  file's hypothesis admits: `z₀z₁ = 1` has `∂/∂z₁ = z₀`, which is nonzero at every point of it,
  so the results below apply; and its projection to the `z₀`-line misses the origin, so the image
  is not closed and the map is not `IsFinite`. **That last sentence is reasoning about a set and
  is compiled nowhere** — no declaration in this repository states it, and the only compiled
  non-closed image on this line is `ComplexAnalytic.not_isClosedMap_base_proj`, which is about a
  different morphism.
* **Nothing about a hypersurface inside an open subset.** `i` maps into the whole of `ℂ^(n+1)`,
  so the cutting section is entire. The stalk half has an open-base version in
  `Oka/AnalyticSpace/OpenBaseProjection.lean` and the topological half has none; a standard étale
  algebra inverts a polynomial as well as cutting one out, which is why that matters and why this
  file does not close the standard étale case.
* **No converse.** Nothing says that a hypersurface whose projection is a local isomorphism has a
  simple zero. The hypothesis is sufficient and is not claimed to be necessary.
* **No statement about the image.** A local homeomorphism need not be surjective and need not be
  injective, and nothing below says which points of `ℂ^n` are hit or how often.
* **Nothing is moved.** `ComplexAnalytic.not_mem_range_uliftCastSuccEmb` and
  `ComplexAnalytic.mem_range_uliftCastSuccEmb` are facts about `ComplexAnalytic.uliftCastSuccEmb`
  alone and their home is `Oka/AnalyticSpace/ProjectionStalk.lean`, where that embedding is
  defined; they are here because this is their only consumer, and a second consumer is what
  should move them.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry MvPowerSeries

universe u

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### The last coordinate is the one the projection forgets -/

/-- **The projection does not remember the last coordinate**: `ULift.up (Fin.last n)` is outside
the range of `ComplexAnalytic.uliftCastSuccEmb`, because `Fin.castSucc` lands strictly below
`Fin.last`. -/
theorem not_mem_range_uliftCastSuccEmb :
    ULift.up.{u} (Fin.last n) ∉ Set.range (uliftCastSuccEmb.{u} n) := by
  rintro ⟨k, hk⟩
  exact absurd (ULift.up.inj hk) (Fin.castSucc_lt_last k.down).ne

/-- **The projection remembers every other coordinate**: an index other than
`ULift.up (Fin.last n)` is in the range of `ComplexAnalytic.uliftCastSuccEmb`. -/
theorem mem_range_uliftCastSuccEmb {m : ULift.{u} (Fin (n + 1))}
    (hm : m ≠ ULift.up.{u} (Fin.last n)) : m ∈ Set.range (uliftCastSuccEmb.{u} n) := by
  obtain ⟨m₀⟩ := m
  have h : m₀ ≠ Fin.last n := fun h ↦ hm (by rw [h])
  obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.2 h
  exact ⟨ULift.up k, ULift.ext _ _ hk⟩

/-! ### The hypersurface, as a level set -/

variable {X : LocallyRingedSpace.{u}} {i : X ⟶ complexAffineSpace.{u} (n + 1)}
  {F : OkaRing (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))}

/-- **A cut-out by one section has the zero set of that section for its image**, stated with the
section read as a function on `ℂ^(n+1)` rather than as a germ.

`ComplexAnalytic.range_base_eq_of_isCutOutBy` is the same fact with the right-hand side written
through `OkaRing.evalHom`; that spelling is what a stalk argument wants and this one is what the
implicit function theorem wants, since its level set is a set of points at which a *function*
takes a value. -/
theorem range_base_eq_zeroSet (hcut : IsCutOutBy i ![F]) :
    Set.range (i.base : X → (ULift.{u} (Fin (n + 1)) → ℂ)) =
      {z : ULift.{u} (Fin (n + 1)) → ℂ | F.toGlobalFun ⊤ z = 0} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change F.toGlobalFun ⊤ _ = 0
    rw [OkaRing.toGlobalFun_eq_evalHom F (show (i.base x : ULift.{u} (Fin (n + 1)) → ℂ) ∈
      (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial)]
    simpa using hcut.evalHom_eq_zero x 0
  · intro h
    have h' : OkaRing.evalHom (U := ⊤) (x := (z : ULift.{u} (Fin (n + 1)) → ℂ)) trivial F = 0 := by
      rw [← OkaRing.toGlobalFun_eq_evalHom]
      exact h
    change z ∈ Set.range (i.base : X → (ULift.{u} (Fin (n + 1)) → ℂ))
    rw [hcut.range_base]
    intro j
    fin_cases j
    exact (germ_mem_maximalIdeal_iff (U := ⊤) trivial F).2 h'

/-- **The underlying map of `i ≫ p` is `i.base` followed by restriction of coordinates**, which
is `ComplexAnalytic.okaMapFun_coordEmb` at each point. -/
theorem base_comp_uliftProj :
    ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).base : X → _) =
      fun x ↦ (i.base x : ULift.{u} (Fin (n + 1)) → ℂ) ∘ (uliftCastSuccEmb.{u} n) :=
  funext fun _ ↦ okaMapFun_coordEmb _ _

/-! ### The topological half -/

/-- **The projection of a hypersurface with a simple zero at every point is a local
homeomorphism.**

This is the half `Oka/AnalyticSpace/SimpleZeroStalk.lean` records as absent. It is the implicit
function theorem, in the form `isLocalHomeomorph_coordProj_comp_of_isEmbedding`: the hypersurface
is the level set `{F = 0}` by `ComplexAnalytic.range_base_eq_zeroSet`, `i.base` embeds `X` onto
it, `F` is strictly differentiable everywhere because it is holomorphic, and the derivative in the
last direction is the coefficient in the hypothesis by
`OkaRing.coeff_single_one_germ`. -/
theorem isLocalHomeomorph_base_comp_uliftProj_of_coeff (hcut : IsCutOutBy i ![F])
    (hlin : ∀ x : X, MvPowerSeries.coeff (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F :
        LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) ≠ 0) :
    IsLocalHomeomorph ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).base : X → _) := by
  rw [base_comp_uliftProj]
  refine isLocalHomeomorph_coordProj_comp_of_isEmbedding (f := F.toGlobalFun ⊤)
    (f' := fun z ↦ fderiv ℂ (F.toGlobalFun ⊤) z) hcut.isClosedEmbedding.isEmbedding
    (fun m hm ↦ mem_range_uliftCastSuccEmb hm) not_mem_range_uliftCastSuccEmb
    (range_base_eq_zeroSet hcut) (fun z _ ↦ (F.analyticAt_toGlobalFun trivial).hasStrictFDerivAt)
    fun z hz ↦ ?_
  have hmem : z ∈ Set.range (i.base : X → (ULift.{u} (Fin (n + 1)) → ℂ)) := by
    rw [range_base_eq_zeroSet hcut]; exact hz
  obtain ⟨x, rfl⟩ := hmem
  rw [← OkaRing.coeff_single_one_germ]
  exact hlin x

/-- **The same for a polynomial cutting section**, with the hypothesis read as a partial
derivative rather than as a Taylor coefficient.

`LocalOkaRing.coeff_single_one_ofMvPolynomial`, exactly as in
`ComplexAnalytic.bijective_stalkMap_comp_uliftProj_of_pderiv`. -/
theorem isLocalHomeomorph_base_comp_uliftProj_of_pderiv
    {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}
    (hcut : IsCutOutBy i ![OkaRing.ofMvPolynomial ⊤ P])
    (hlin : ∀ x : X, MvPolynomial.eval (i.base x)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    IsLocalHomeomorph ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).base : X → _) := by
  refine isLocalHomeomorph_base_comp_uliftProj_of_coeff hcut fun x ↦ ?_
  rw [← LocalOkaRing.ofMvPolynomial_eq, LocalOkaRing.coeff_single_one_ofMvPolynomial]
  exact hlin x

/-! ### The two halves together -/

section AnalyticSpaceLevel

variable {W : AnalyticSpace.{u}} {i' : W ⟶ AnalyticSpace.complexAffineSpace.{u} (n + 1)}

/-- **The projection of a hypersurface with a simple zero at every point is a local isomorphism
of complex analytic spaces.**

The two fields of `ComplexAnalytic.AnalyticSpace.IsLocalIso` are
`ComplexAnalytic.isLocalHomeomorph_base_comp_uliftProj_of_coeff` and
`ComplexAnalytic.isIso_stalkMap_comp_uliftProj_of_coeff`, and they take the same hypothesis — the
first at every point at once, the second at one point at a time.
`ComplexAnalytic.AnalyticSpace.proj` is the projection as a morphism of complex analytic spaces,
whose underlying morphism of locally ringed spaces is the `ComplexAnalytic.okaMapHom` the two
halves are stated for.

**The name has no `AnalyticSpace.` prefix and that is not an oversight.** Declared with one —
that is, into the `ComplexAnalytic.AnalyticSpace` namespace — this theorem is **silently dropped
from the environment**: no error is reported by
`lake env lean` or by `lake build --wfail`, the only symptom is a spurious *"Variable name `hcut`
is not explicitly referenced"*, and `#check` on the name then fails. Bisecting the signature,
the trigger is the `OkaRing.germ` application in `hlin`; the same statement under a name without
that prefix elaborates and is added. Two other declarations in the same namespace with simpler
signatures are unaffected, so this is not a blanket fact about the namespace. Recorded here
because the failure is invisible to every check this repository runs except a declaration
count. -/
theorem isLocalIso_comp_proj_of_coeff (hcut : IsCutOutBy i'.toLRSHom ![F])
    (hlin : ∀ x : W, MvPowerSeries.coeff (Finsupp.single (ULift.up.{u} (Fin.last n)) 1)
      ((OkaRing.germ (show i'.toLRSHom.base x ∈
          (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F :
        LocalOkaRing (ULift.{u} (Fin (n + 1)))) :
          MvPowerSeries (ULift.{u} (Fin (n + 1))) ℂ) ≠ 0) :
    AnalyticSpace.IsLocalIso (i' ≫ AnalyticSpace.proj.{u} n) :=
  ⟨isLocalHomeomorph_base_comp_uliftProj_of_coeff hcut hlin,
    fun x ↦ isIso_stalkMap_comp_uliftProj_of_coeff hcut x (hlin x)⟩

/-- **The same for a polynomial cutting section.** This is the form the standard étale line
consumes: `ComplexAnalytic.eval_pderiv_ne_zero_of_mem` produces exactly this hypothesis at a point
of the hypersurface, from `StandardEtalePair`'s `cond` field. -/
theorem isLocalIso_comp_proj_of_pderiv {P : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ}
    (hcut : IsCutOutBy i'.toLRSHom ![OkaRing.ofMvPolynomial ⊤ P])
    (hlin : ∀ x : W, MvPolynomial.eval (i'.toLRSHom.base x)
      (MvPolynomial.pderiv (ULift.up.{u} (Fin.last n)) P) ≠ 0) :
    AnalyticSpace.IsLocalIso (i' ≫ AnalyticSpace.proj.{u} n) :=
  ⟨isLocalHomeomorph_base_comp_uliftProj_of_pderiv hcut hlin,
    fun x ↦ isIso_stalkMap_comp_uliftProj_of_pderiv hcut x (hlin x)⟩

end AnalyticSpaceLevel

end ComplexAnalytic

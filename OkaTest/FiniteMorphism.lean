/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of finiteness for morphisms of complex analytic spaces

`ComplexAnalytic.AnalyticSpace.IsFinite` says a morphism is closed with finite fibres. Two things
could be wrong with it and neither is visible from its type: it could hold only for the
isomorphisms, and it could hold for everything. This file rules both out on the same pair of
spaces, with the two morphisms between `ℂ` and `ℂ²` that everyone draws first.

* **`ComplexAnalytic.axisIncl`, `z ↦ (z, 0)`, is finite** and is not an isomorphism — its image is
  the first axis, a proper closed subset. It is finite because its underlying map is a closed
  embedding (`ComplexAnalytic.isClosedEmbedding_base_axisIncl`), which is proved here rather than
  quoted, because `ComplexAnalytic.AnalyticSpace.isFinite_of_isCutOutBy` has no instance to be
  applied at. `ComplexAnalytic.IsCutOutBy` is a condition on a morphism of *locally ringed
  spaces*, and cut-out data is produced — that is what
  `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι` does — but never for a
  morphism of *analytic* spaces:
  `git grep 'IsCutOutBy.*toLRSHom'` over the whole repository returns two hits,
  `ComplexAnalytic.AnalyticSpace.mono_of_isCutOutBy` and `isFinite_of_isCutOutBy` itself, and both
  take it as a hypothesis. So a witness has to be built by hand.
* **`ComplexAnalytic.proj`, `(z, w) ↦ z`, is not finite, and fails *both* conditions.** Its fibre
  over the origin is the second axis, which is infinite; and its underlying map is not closed,
  because the hyperbola `z w = 1` is closed in `ℂ²` and its image is `ℂ ∖ {0}`, which is not
  closed in `ℂ`. So the example does not separate the two halves of the definition — it fails at
  both — and `ComplexAnalytic.not_isClosedMap_base_proj` is what says so.

## The third statement, which is the reason both are here

**`ComplexAnalytic.isFinite_axisIncl_comp_proj`: the composite `ℂ ⟶ ℂ² ⟶ ℂ` is finite although
the second factor is not.** So the finite morphisms are *not* closed under right cancellation, and
`ComplexAnalytic.AnalyticSpace.isFinite_comp` is not an iff in disguise. Without this the two
statements above would only say that the class is somewhere between empty and everything; this
says the composition lemma has the strength it claims and no more.

## What is not checked here

* **Nothing about structure sheaves.** `ComplexAnalytic.AnalyticSpace.IsFinite` is a condition on
  the underlying map, and the theorem that makes it a condition on sheaves — that `f_*𝒪_X` is
  coherent for finite `f` — is not in this repository. So no statement here is about coherence and
  none should be read that way.
* **`ComplexAnalytic.axisIncl` is not shown to be a closed immersion**, only a closed embedding on
  points. Whether it cuts `ℂ` out of `ℂ²` by the second coordinate — the `IsCutOutBy` statement —
  is not proved, and only the topological half is used.
* **Neither map is shown proper.** Properness is not defined here.
* **No finite étale morphism other than an isomorphism.** `ComplexAnalytic.axisIncl` is finite and
  is *not* a local isomorphism (`ComplexAnalytic.not_isLocalIso_axisIncl`), which is what says the
  second rung restricts the first; but the only positive witness for
  `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` here is still the identity. **The candidate is
  built and nothing is claimed about it**: `ComplexAnalytic.sq`, the squaring map of the punctured
  line, exists below and is proved not injective, so it is not an isomorphism — but neither
  `ComplexAnalytic.AnalyticSpace.IsFinite` nor `…IsLocalIso` is proved for it, and neither should
  be read into any statement here.
* **Nothing exercises the stalk half of `ComplexAnalytic.AnalyticSpace.IsLocalIso`.** The
  non-example above fails the topological field alone, and `ComplexAnalytic.sq` — which is the map
  that would exercise it — has no stalk statement here. That needs a local holomorphic inverse of
  `z ↦ z²`, which this repository does not build.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology Filter

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The inclusion of the first axis, `z ↦ (z, 0)` -/

/-- The pair of entire functions `(z, 0)` on `ℂ`, as a family indexed by the coordinates of `ℂ²`.
The `ULift` wrapping is what `ComplexAnalytic.AnalyticSpace.okaMap` indexes by. -/
def axisFamily : ULift.{u} (Fin 2) → OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  fun j ↦ if j = ULift.up 0 then coord (ULift.up 0) else 0

/-- **The inclusion of the first axis, `ℂ ⟶ ℂ²`.** -/
def axisIncl : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.complexAffineSpace.{u} 2 :=
  AnalyticSpace.okaMap axisFamily.{u}

/-- **Its underlying map is `z ↦ (z, 0)`**, named on the nose rather than exhibited at a point.
Everything below is a computation with this equation. -/
theorem base_axisIncl (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    ((axisIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) =
      fun j ↦ if j = ULift.up 0 then (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) else 0 := by
  refine funext fun j ↦ ?_
  change okaMapFun axisFamily.{u} _ j = _
  rw [okaMapFun_apply, axisFamily]
  by_cases h : j = ULift.up 0
  · rw [if_pos h, if_pos h, evalHom_coord]
  · rw [if_neg h, if_neg h, map_zero]

/-- The first coordinate, as a continuous retraction of `ComplexAnalytic.axisIncl`. Its existence
is what makes the inclusion an embedding without any computation of neighbourhoods. -/
def axisRetract : AnalyticSpace.complexAffineSpace.{u} 2 →
    AnalyticSpace.complexAffineSpace.{u} 1 :=
  fun q _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0)

/-- **The image of the inclusion is exactly the first axis.** The inclusion `⊆` is the second
component of `ComplexAnalytic.base_axisIncl`; the reverse is the retraction, and the case `j ≠ 0`
is where the hypothesis is used. -/
theorem range_base_axisIncl :
    Set.range ((axisIncl.{u}).toLRSHom.base :
        AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) =
      {q : AnalyticSpace.complexAffineSpace.{u} 2 |
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 0} := by
  refine Set.ext fun q ↦ ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨p, rfl⟩
    change ((axisIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 0
    rw [base_axisIncl]
    exact if_neg (by simp)
  · refine ⟨fun _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0), funext fun j ↦ ?_⟩
    rw [show ((axisIncl.{u}).toLRSHom.base _ : ULift.{u} (Fin 2) → ℂ) = _ from base_axisIncl _]
    dsimp only
    by_cases h : j = ULift.up 0
    · rw [if_pos h, h]
    · rw [if_neg h]
      obtain ⟨j⟩ := j
      fin_cases j
      · exact absurd rfl h
      · exact hq.symm

/-- **The inclusion is a closed embedding.**

Embedding by `Function.LeftInverse.isEmbedding` at `ComplexAnalytic.axisRetract` — a continuous
injection with a continuous left inverse is an embedding, and that is cheaper than identifying the
subspace topology. Closed because, by `ComplexAnalytic.range_base_axisIncl`, the image is the zero
set of a coordinate, and evaluation at a coordinate is continuous.

The continuity of the inclusion itself is free: it is the underlying map of a morphism of locally
ringed spaces. -/
theorem isClosedEmbedding_base_axisIncl :
    IsClosedEmbedding ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) where
  toIsEmbedding := by
    refine Function.LeftInverse.isEmbedding (f := axisRetract.{u}) ?_
      (continuous_pi fun _ ↦ continuous_apply (ULift.up 0))
      (axisIncl.{u}).toLRSHom.base.hom.continuous
    intro p
    refine funext fun l ↦ ?_
    change ((axisIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) = _
    rw [base_axisIncl]
    change p (ULift.up 0) = p l
    exact congrArg p (Subsingleton.elim _ _)
  isClosed_range := by
    have hcont : Continuous fun q : AnalyticSpace.complexAffineSpace.{u} 2 ↦
        (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) := continuous_apply _
    rw [range_base_axisIncl]
    exact isClosed_eq hcont continuous_const

/-- **The inclusion of the first axis is a finite morphism**, and it is not an isomorphism, since
its image is a proper subset of `ℂ²` — `ComplexAnalytic.range_base_axisIncl` and the point
`(0, 1)`. -/
theorem isFinite_axisIncl : AnalyticSpace.IsFinite axisIncl.{u} :=
  AnalyticSpace.isFinite_of_isClosedEmbedding _ isClosedEmbedding_base_axisIncl.{u}

/-- **The inclusion is not surjective**, so `ComplexAnalytic.isFinite_axisIncl` is not a statement
about an isomorphism. -/
theorem not_surjective_base_axisIncl :
    ¬ Function.Surjective ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (fun _ ↦ (1 : ℂ))
  have h : ((axisIncl.{u}).toLRSHom.base p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 1 :=
    congrFun hp (ULift.up 1)
  rw [base_axisIncl] at h
  dsimp only at h
  rw [if_neg (by simp)] at h
  exact zero_ne_one h

/-! ### The projection `(z, w) ↦ z` -/

/-- The first coordinate of `ℂ²`, as a one-element family of entire functions. -/
def projFamily : ULift.{u} (Fin 1) → OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)) :=
  fun _ ↦ coord (ULift.up 0)

/-- **The projection `ℂ² ⟶ ℂ`.** -/
def proj : AnalyticSpace.complexAffineSpace.{u} 2 ⟶ AnalyticSpace.complexAffineSpace.{u} 1 :=
  AnalyticSpace.okaMap projFamily.{u}

/-- **Its underlying map is `(z, w) ↦ z`.** -/
theorem base_proj (q : AnalyticSpace.complexAffineSpace.{u} 2) :
    ((proj.{u}).toLRSHom.base q : ULift.{u} (Fin 1) → ℂ) =
      fun _ ↦ (q : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) := by
  refine funext fun l ↦ ?_
  change okaMapFun projFamily.{u} _ l = _
  rw [okaMapFun_apply, projFamily, evalHom_coord]

/-- **The fibre of the projection over the origin is infinite**: it is the second axis, and
`t ↦ (0, t)` injects `ℂ` into it. -/
theorem infinite_fiber_proj : Infinite
    (((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
        AnalyticSpace.complexAffineSpace.{u} 1) ⁻¹'
      {(fun _ ↦ (0 : ℂ) : AnalyticSpace.complexAffineSpace.{u} 1)}) := by
  refine Set.infinite_coe_iff.2 (Set.infinite_of_injective_forall_mem
    (f := fun t : ℂ ↦ (fun l ↦ if l = ULift.up 1 then t else 0 :
      AnalyticSpace.complexAffineSpace.{u} 2)) ?_ ?_)
  · intro a b hab
    have h := congrFun hab (ULift.up 1)
    simpa using h
  · intro t
    refine Set.mem_preimage.2 (Set.mem_singleton_iff.2 (funext fun l ↦ ?_))
    rw [show ((proj.{u}).toLRSHom.base _ : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _]
    simp

/-- **The projection is not finite**, by the fibre condition. Its underlying map fails the
*closed* condition as well — `ComplexAnalytic.not_isClosedMap_base_proj` — so this is not an
example separating the two halves of `ComplexAnalytic.AnalyticSpace.IsFinite`; it is one at which
both fail, and each failure is exhibited at a set one can name. -/
theorem not_isFinite_proj : ¬ AnalyticSpace.IsFinite proj.{u} :=
  AnalyticSpace.not_isFinite_of_infinite_fiber _ _ infinite_fiber_proj.{u}

/-! ### And its underlying map is not closed either

The half of `ComplexAnalytic.AnalyticSpace.IsFinite` that `ComplexAnalytic.not_isFinite_proj` does
not touch. A projection along a *compact* factor is closed; along `ℂ` it is not, and the classical
witness is the hyperbola. -/

/-- **The hyperbola `z w = 1` in `ℂ²`**, the standard closed set whose image under the projection
is not closed. -/
def hyperbola : Set (AnalyticSpace.complexAffineSpace.{u} 2) :=
  {p | (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) * (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) = 1}

/-- It is closed, being the level set of a continuous function. -/
theorem isClosed_hyperbola : IsClosed hyperbola.{u} := by
  have h0 : Continuous fun p : AnalyticSpace.complexAffineSpace.{u} 2 ↦
      (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) := continuous_apply _
  have h1 : Continuous fun p : AnalyticSpace.complexAffineSpace.{u} 2 ↦
      (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 1) := continuous_apply _
  exact isClosed_eq (h0.mul h1) continuous_const

/-- **Its image is `ℂ ∖ {0}`**: `z w = 1` forces `z ≠ 0`, and every nonzero `z` is hit, at
`w = z⁻¹`. -/
theorem image_hyperbola :
    ((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
        AnalyticSpace.complexAffineSpace.{u} 1) '' hyperbola.{u} =
      {q : AnalyticSpace.complexAffineSpace.{u} 1 |
        (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0} := by
  refine Set.ext fun q ↦ ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨p, hp, rfl⟩
    intro hzero
    rw [show ((proj.{u}).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _] at hzero
    exact one_ne_zero (hp.symm.trans
      (by rw [show (p : ULift.{u} (Fin 2) → ℂ) (ULift.up 0) = 0 from hzero, zero_mul]))
  · refine ⟨fun l ↦ if l = ULift.up 0 then (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0)
      else ((q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0))⁻¹, ?_, ?_⟩
    · change _ * _ = 1
      simpa using mul_inv_cancel₀ hq
    · refine funext fun l ↦ ?_
      rw [show ((proj.{u}).toLRSHom.base _ : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _]
      dsimp only
      rw [if_pos rfl]
      exact congrArg _ (Subsingleton.elim _ _)

/-- **The projection is not a closed map.**

If it were, `ℂ ∖ {0}` would be closed in `ℂ`, so `{0}` would be open there — and `{0}` is not
open in `ℂ`, since the punctured neighbourhood filter at `0` is not `⊥`. The passage from the
one-variable affine space to `ℂ` is the continuous map `c ↦ (fun _ ↦ c)`, whose preimage of the
zero set of the coordinate is exactly `{0}`. -/
theorem not_isClosedMap_base_proj :
    ¬ IsClosedMap ((proj.{u}).toLRSHom.base : AnalyticSpace.complexAffineSpace.{u} 2 →
      AnalyticSpace.complexAffineSpace.{u} 1) := by
  intro hclosed
  have himg := hclosed _ isClosed_hyperbola.{u}
  rw [image_hyperbola] at himg
  have hopen : IsOpen {q : AnalyticSpace.complexAffineSpace.{u} 1 |
      (q : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) = 0} := by
    have hc := himg.isOpen_compl
    convert hc using 1
    exact Set.ext fun _ ↦ (not_not).symm
  have hdiag : Continuous fun c : ℂ ↦ (fun _ ↦ c : AnalyticSpace.complexAffineSpace.{u} 1) :=
    continuous_pi fun _ ↦ continuous_id
  have hzero : IsOpen ({0} : Set ℂ) := by
    have hp := hopen.preimage hdiag
    convert hp using 1
    exact Set.ext fun _ ↦ Iff.rfl
  have hb : (𝓝[≠] (0 : ℂ)) = ⊥ := by rwa [← isOpen_singleton_iff_punctured_nhds]
  exact (inferInstance : (𝓝[≠] (0 : ℂ)).NeBot).ne hb

/-! ### The composite, and what it says about the composition lemma -/

/-- **The composite `ℂ ⟶ ℂ² ⟶ ℂ` is the identity on points.**

Composition of morphisms of analytic spaces is composition of the underlying morphisms of locally
ringed spaces by definition, so the left-hand side is `base_proj` after `base_axisIncl`, and a
point of `ℂ` is determined by its one coordinate. -/
theorem base_axisIncl_comp_proj :
    ((axisIncl.{u} ≫ proj.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 1) = id := by
  refine funext fun p ↦ funext fun l ↦ ?_
  change ((proj.{u}).toLRSHom.base ((axisIncl.{u}).toLRSHom.base p) :
    ULift.{u} (Fin 1) → ℂ) l = _
  rw [show ((proj.{u}).toLRSHom.base _ : ULift.{u} (Fin 1) → ℂ) = _ from base_proj _,
    base_axisIncl]
  dsimp only
  rw [if_pos rfl]
  exact congrArg p (Subsingleton.elim _ _)

/-- **The composite is finite although the second factor is not.**

So `ComplexAnalytic.AnalyticSpace.isFinite_comp` cannot be strengthened to an equivalence, and
finiteness is not right-cancellable: with `ComplexAnalytic.not_isFinite_proj` this is a pair
`f`, `g` with `f ≫ g` finite and `g` not. -/
theorem isFinite_axisIncl_comp_proj : AnalyticSpace.IsFinite (axisIncl.{u} ≫ proj.{u}) :=
  AnalyticSpace.isFinite_of_isClosedEmbedding _
    (base_axisIncl_comp_proj.{u} ▸ IsClosedEmbedding.id)

/-- And the identity is finite, so the two together are not a statement about the empty class. -/
example : AnalyticSpace.IsFinite (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1)) :=
  inferInstance

/-- Composing two finite morphisms stays finite, at the witness above. -/
example : AnalyticSpace.IsFinite (axisIncl.{u} ≫ 𝟙 (AnalyticSpace.complexAffineSpace.{u} 2)) :=
  haveI := isFinite_axisIncl.{u}
  inferInstance

/-! ### Finite is not finite étale

`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is `IsFinite` together with
`ComplexAnalytic.AnalyticSpace.IsLocalIso`, and the second is a real restriction: the witness this
file already has is finite and is **not** a local isomorphism. -/

/-- **The inclusion of the first axis is not a local isomorphism.**

A local homeomorphism is an open map, so its range would be open; the range is also closed, since
the inclusion is a closed embedding. `ℂ²` is connected, so a clopen subset is `∅` or everything —
and the range is neither, being nonempty and not all of `ℂ²`
(`ComplexAnalytic.not_surjective_base_axisIncl`).

**Nothing about stalks is used**: the topological field alone fails. That is worth saying, because
it means the example does not exercise
`ComplexAnalytic.AnalyticSpace.IsLocalIso.isIso_stalkMap`, and nothing here does. -/
theorem not_isLocalIso_axisIncl : ¬ AnalyticSpace.IsLocalIso axisIncl.{u} := by
  intro h
  haveI : PreconnectedSpace (AnalyticSpace.complexAffineSpace.{u} 2) :=
    inferInstanceAs (PreconnectedSpace (ULift.{u} (Fin 2) → ℂ))
  have hopen : IsOpen (Set.range ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2)) :=
    h.isLocalHomeomorph.isOpenMap.isOpen_range
  have hclosed : IsClosed (Set.range ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2)) :=
    isClosedEmbedding_base_axisIncl.{u}.isClosed_range
  rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with hbot | htop
  · exact absurd (Set.mem_range_self (f := ((axisIncl.{u}).toLRSHom.base :
      AnalyticSpace.complexAffineSpace.{u} 1 → AnalyticSpace.complexAffineSpace.{u} 2))
      (fun _ ↦ (0 : ℂ))) (by rw [hbot]; exact fun hc ↦ hc)
  · exact not_surjective_base_axisIncl.{u} (Set.range_eq_univ.1 htop)

/-- **So it is finite and not finite étale**, which is what says the second rung is a restriction
on the first rather than a restatement of it. -/
theorem not_isFiniteEtale_axisIncl : ¬ AnalyticSpace.IsFiniteEtale axisIncl.{u} := fun h ↦
  not_isLocalIso_axisIncl.{u} h.isLocalIso

/-- **And the class is not empty**: the identity is finite étale.

This is the degenerate witness and it is the only positive one here. **A finite étale morphism
which is not an isomorphism is not exhibited anywhere in this repository**, and building one needs
a source that is not simply connected — `z ↦ z²` from `ℂ ∖ {0}` to itself is the standard
example, needing `ComplexAnalytic.AnalyticSpace.restrict` on both sides and the square map. Until
that exists, everything below the identity is unexercised, and no statement here should be read as
saying otherwise. -/
example : AnalyticSpace.IsFiniteEtale (𝟙 (AnalyticSpace.complexAffineSpace.{u} 1)) :=
  inferInstance

/-! ### The squaring map of the punctured line, as far as it goes

The limitation recorded above — that the only positive witness for
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` is the identity — is about `ℂ ∖ {0}` and `z ↦ z²`,
and **this section builds that map and proves nothing about its finiteness or its stalks.** It is
here because the construction was the part nobody had priced: a morphism whose *target* is an open
subspace needed `ComplexAnalytic.AnalyticSpace.liftRestrict`, which did not exist.

What is proved is that the map exists, what its underlying map is, and that it is **not
injective** — so if it is ever shown finite étale, the class will be strictly larger than the
isomorphisms. What is *not* proved is `IsFinite`, `IsLocalIso` or `IsFiniteEtale` for it; see
`## What is not checked here`. -/

/-- `z²`, as a one-element family of entire functions on `ℂ`. -/
def sqFamily : ULift.{u} (Fin 1) → OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  fun _ ↦ coord (ULift.up 0) * coord (ULift.up 0)

/-- **The squaring map `ℂ ⟶ ℂ`**, before restricting to the punctured line. -/
def sqAll : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.complexAffineSpace.{u} 1 :=
  AnalyticSpace.okaMap sqFamily.{u}

/-- **Its underlying map is `z ↦ z²`.** -/
theorem base_sqAll (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    ((sqAll.{u}).toLRSHom.base p : ULift.{u} (Fin 1) → ℂ) =
      fun _ ↦ (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) *
        (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) := by
  refine funext fun l ↦ ?_
  change okaMapFun sqFamily.{u} _ l = _
  rw [okaMapFun_apply, sqFamily, map_mul, evalHom_coord]

/-- **`ℂ ∖ {0}`**, as an open subspace of the affine line: the non-vanishing locus of `z`. -/
def punctured : (AnalyticSpace.complexAffineSpace.{u} 1).Opens :=
  (AnalyticSpace.complexAffineSpace.{u} 1).nonvanishing (coord (ULift.up 0))

/-- **A point of the affine line lies in it exactly when its coordinate is nonzero.**
`ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff` turns membership into non-vanishing of the
*value*, and `ComplexAnalytic.eval_complexAffineSpace` computes that value on `ℂ^n`. -/
theorem mem_punctured_iff (p : AnalyticSpace.complexAffineSpace.{u} 1) :
    p ∈ punctured.{u} ↔ (p : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0 := by
  rw [punctured, AnalyticSpace.mem_nonvanishing_iff]
  rw [eval_complexAffineSpace, evalHom_coord]

/-- **The square of a nonzero number is nonzero**, in the form
`ComplexAnalytic.AnalyticSpace.liftRestrict` asks for. -/
theorem range_subset_punctured :
    Set.range ((((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫
        sqAll.{u}).toLRSHom.base) :
      (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} →
        AnalyticSpace.complexAffineSpace.{u} 1) ⊆ (punctured.{u} : Set _) := by
  rintro _ ⟨p, rfl⟩
  have hp : (p.1 : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) ≠ 0 :=
    (mem_punctured_iff.{u} p.1).1 p.2
  have hcomp : (((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫
      sqAll.{u}).toLRSHom.base p) = (sqAll.{u}).toLRSHom.base p.1 := rfl
  rw [hcomp]
  refine (mem_punctured_iff.{u} _).2 ?_
  rw [show (((sqAll.{u}).toLRSHom.base p.1 : AnalyticSpace.complexAffineSpace.{u} 1) :
      ULift.{u} (Fin 1) → ℂ) = _ from base_sqAll.{u} p.1]
  exact mul_ne_zero hp hp

/-- **The squaring map of the punctured line, `ℂ ∖ {0} ⟶ ℂ ∖ {0}`.**

The target is an open subspace, which is why this needs
`ComplexAnalytic.AnalyticSpace.liftRestrict`: `ComplexAnalytic.AnalyticSpace.okaMap` produces
morphisms into `ℂ^n` and nothing before produced one into a restriction of it. -/
def sq : (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} ⟶
    (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} :=
  AnalyticSpace.liftRestrict
    ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫ sqAll.{u})
    punctured.{u} range_subset_punctured.{u}

/-- **Its underlying map is `z ↦ z²`.**

Computed through `ComplexAnalytic.AnalyticSpace.liftRestrict_fac` rather than by unfolding: the
lift is opaque and the composite it factors is not. -/
theorem base_sq (p : (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}) :
    (((sq.{u}).toLRSHom.base p).1 : ULift.{u} (Fin 1) → ℂ) =
      fun _ ↦ (p.1 : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) *
        (p.1 : ULift.{u} (Fin 1) → ℂ) (ULift.up 0) := by
  have h := congrArg (fun m : _ ⟶ AnalyticSpace.complexAffineSpace.{u} 1 ↦ m.toLRSHom.base p)
    (AnalyticSpace.liftRestrict_fac
      ((AnalyticSpace.complexAffineSpace.{u} 1).ofRestrict punctured.{u} ≫ sqAll.{u})
      punctured.{u} range_subset_punctured.{u})
  rw [show (((sq.{u}).toLRSHom.base p).1 : AnalyticSpace.complexAffineSpace.{u} 1) = _ from h]
  exact base_sqAll.{u} p.1

/-- **It is not injective**: `1` and `-1` are two points of `ℂ ∖ {0}` with the same square.

`ComplexAnalytic.not_isIso_sq` below is the consequence, and it is a separate statement because
non-injectivity of the underlying map is not by itself non-invertibility of the morphism.
**Nothing here shows it finite étale**, and no statement below should be read as saying so. -/
theorem not_injective_base_sq :
    ¬ Function.Injective ((sq.{u}).toLRSHom.base :
      (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u} →
        (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}) := by
  have h1 : ((fun _ ↦ (1 : ℂ)) : ULift.{u} (Fin 1) → ℂ) ∈ punctured.{u} :=
    (mem_punctured_iff.{u} _).2 one_ne_zero
  have h2 : ((fun _ ↦ (-1 : ℂ)) : ULift.{u} (Fin 1) → ℂ) ∈ punctured.{u} :=
    (mem_punctured_iff.{u} _).2 (neg_ne_zero.2 one_ne_zero)
  intro hinj
  have hne : (⟨(fun _ ↦ (1 : ℂ) : ULift.{u} (Fin 1) → ℂ), h1⟩ :
      (AnalyticSpace.complexAffineSpace.{u} 1).restrict punctured.{u}) ≠
    ⟨(fun _ ↦ (-1 : ℂ) : ULift.{u} (Fin 1) → ℂ), h2⟩ := by
    intro h
    have := congrFun (congrArg Subtype.val h) (ULift.up 0)
    norm_num at this
  refine hne (hinj ?_)
  refine Subtype.ext (funext fun l ↦ ?_)
  rw [show (((sq.{u}).toLRSHom.base ⟨(fun _ ↦ (1 : ℂ) : ULift.{u} (Fin 1) → ℂ), h1⟩).1 :
      ULift.{u} (Fin 1) → ℂ) = _ from base_sq.{u} _,
    show (((sq.{u}).toLRSHom.base ⟨(fun _ ↦ (-1 : ℂ) : ULift.{u} (Fin 1) → ℂ), h2⟩).1 :
      ULift.{u} (Fin 1) → ℂ) = _ from base_sq.{u} _]
  norm_num

/-- **So it is not an isomorphism**, which is what makes the map worth building: if it is ever
shown finite étale then `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` will contain something the
identity does not.

An isomorphism of analytic spaces gives a homeomorphism of the underlying spaces through
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` and
`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`, and a homeomorphism is injective. Note that the
functor is applied to the *iso* rather than the morphism, so no instance has to be re-ascribed at
`ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` — the seam
`ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso` documents does not arise on this route.

**This is still not a statement that it is finite étale.** -/
theorem not_isIso_sq : ¬ IsIso sq.{u} := fun _ ↦
  not_injective_base_sq.{u}
    (LocallyRingedSpace.homeoOfIso
      (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso (asIso sq.{u}))).injective

end

end ComplexAnalytic

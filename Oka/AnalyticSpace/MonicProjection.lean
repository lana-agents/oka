/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Finite
import Oka.AnalyticSpace.ProjectionStalk
import Oka.Topology.Algebra.Polynomial

/-!
# The projection of a monic hypersurface to its base is finite

Let `i : X ⟶ ℂ^(n+1)` be a closed embedding of complex analytic spaces whose image is the zero
locus of a function which, in the last variable, is a **monic polynomial of one fixed degree**
with continuously varying coefficients — a Weierstrass polynomial, in the case this development
is aiming at. Then the composite

    X ⟶ ℂ^(n+1) ⟶ ℂ^n

with the projection forgetting the last coordinate is `ComplexAnalytic.AnalyticSpace.IsFinite`:
closed, with finite fibres.

This is the topological half of *the analytification of a standard étale morphism is finite
étale*; `Oka/AnalyticSpace/SimpleZeroStalk.lean` is the stalk half, for the same composite
`i ≫ ComplexAnalytic.AnalyticSpace.proj`, and the two are what
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` asks for.

## Where the mathematics is, and it is not here

**All of it is in `Oka/Topology/Algebra/Polynomial.lean`**, which is in the mirror tree and
mentions nothing analytic: the roots of a monic polynomial are bounded by its coefficients, so a
closed set of roots of a continuous family has closed image in the parameters
(`Polynomial.isClosed_fst_image_of_monic`) and meets each fibre in a finite set
(`Polynomial.finite_inter_fst_preimage_of_monic`). This file is the assembly, and it is three
steps:

* **a criterion** — `ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` reduces
  `IsFinite (i ≫ p)` to those two statements *about the image of `i`*, which is what lets the
  projection be used even though it is not itself finite
  (`ComplexAnalytic.not_isFinite_proj`);
* **a carrier bridge** — `ComplexAnalytic.uliftSnocHomeo`, the homeomorphism
  `ℂ^(n+1) ≃ₜ ℂ^n × ℂ` splitting off the last coordinate, across which the two set-level
  statements are read; it is the analogue of `ComplexAnalytic.puncturedHomeo` in
  `OkaTest/FiniteMorphism.lean`, which plays the same role for `ComplexAnalytic.isFinite_sq`;
* **the image of `i`** — `ComplexAnalytic.range_base_eq_of_isCutOutBy` turns
  `ComplexAnalytic.IsCutOutBy`'s `range_base` field, which is phrased with germs and maximal
  ideals, into the vanishing of a function, by `germ_mem_maximalIdeal_iff`.

## The two spellings of the hypothesis on the image

`ComplexAnalytic.isFinite_comp_proj_of_range_eq` takes the image of `i` as a set equation and
asks nothing about structure sheaves; `ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy` takes
`ComplexAnalytic.IsCutOutBy i.toLRSHom ![F]` and the pointwise identity between `F` and the
family. The first is the one a hand-built morphism satisfies —
`OkaTest/FiniteMorphism.lean` explains why cut-out data for a morphism of *analytic* spaces has
to be built by hand in this development — and it is what `OkaTest/MonicProjection.lean` applies.
The second is the one the Weierstrass line will consume and is a three-line corollary of it.

**Neither takes the family from `F`.** The family `q` is an argument, and the hypothesis relating
it to `F` is an equation the caller proves; nothing here extracts the coefficients of a
holomorphic function in its last variable, and no holomorphy of the coefficients is used —
continuity is all the mathematics needs, and it is all that is asked for.

## Main results

- `ComplexAnalytic.uliftSnocHomeo`: **the last coordinate splits off `ℂ^(n+1)` as a
  homeomorphism onto `ℂ^n × ℂ`**, compatibly with the projection
  (`ComplexAnalytic.base_proj_eq`).
- `ComplexAnalytic.range_base_eq_of_isCutOutBy`: **a hypersurface cut out by one global section
  of `𝒪_{ℂ^m}` has that section's zero set for its image.**
- `ComplexAnalytic.isFinite_comp_proj_of_range_eq`: **the projection of a monic hypersurface to
  its base is finite**, with the hypersurface given as the zero locus of a continuous family of
  monic polynomials of one fixed degree.
- `ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy`: the same with the hypersurface presented as
  a cut-out by one global section rather than as a set.

## What is not here

* **No `IsFiniteEtale`, and no `IsLocalIso`.** The stalk half is
  `Oka/AnalyticSpace/SimpleZeroStalk.lean` and the topological half of `IsLocalIso` — that the
  underlying map is a local homeomorphism — is neither here nor there. Nothing below says the
  composite is open, and for a monic family with repeated roots it is not a local
  homeomorphism at all, so this is not a gap that closes by an argument of the same kind.
* **No open subset of the base.** `i` lands in the whole of `ℂ^(n+1)`, as it does in
  `Oka/AnalyticSpace/SimpleZeroStalk.lean` and for the same reason: a standard étale algebra
  inverts a polynomial as well as cutting one out, so its analytification lives in an open
  subspace, and carrying the argument across a restriction is separate work. The mirror-tree
  theorems are already general enough — `X` there is any topological space — so what is missing
  is the bridge and not the mathematics.
* **No Weierstrass polynomial.** Nothing here produces the family `q` from a germ, which is what
  `Oka/Weierstrass.lean`'s preparation theorem is for; the family is a hypothesis. In particular
  the degree is *fixed*, not merely bounded — a family whose leading coefficient degenerates has
  roots escaping to infinity and the projection is then not closed, which is why
  `Polynomial.isClosed_fst_image_of_monic` asks for `natDegree = d` and not `≤ d`.
* **No bound on the fibres.** A fibre is finite; that it has at most `d` points is
  `Polynomial.card_roots'` and is not specialised, here or in the mirror tree.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### Splitting off the last coordinate -/

/-- **The homeomorphism `ℂ^(n+1) ≃ₜ ℂ^n × ℂ` splitting off the last coordinate.**

The coordinates of `ComplexAnalytic.AnalyticSpace.complexAffineSpace` are indexed by
`ULift (Fin n)`, so this is `Fin.snoc` with a `ULift` on either side of it; the inverse is
`Fin.lastCases`, which is what makes the two round trips one `Fin.lastCases` each.

`ComplexAnalytic.base_proj_eq` is the compatibility that makes it the right bridge: the first
component **is** the underlying map of `ComplexAnalytic.AnalyticSpace.proj`. -/
def uliftSnocHomeo (n : ℕ) :
    (ULift.{u} (Fin (n + 1)) → ℂ) ≃ₜ ((ULift.{u} (Fin n) → ℂ) × ℂ) where
  toFun z := (fun j ↦ z (ULift.up j.down.castSucc), z (ULift.up (Fin.last n)))
  invFun w j := Fin.lastCases w.2 (fun k ↦ w.1 (ULift.up k)) j.down
  left_inv z := by
    funext j
    obtain ⟨j⟩ := j
    refine Fin.lastCases ?_ ?_ j <;> simp
  right_inv w := by
    obtain ⟨w, c⟩ := w
    refine Prod.ext ?_ ?_
    · funext j
      obtain ⟨j⟩ := j
      simp
    · simp
  continuous_toFun := (continuous_pi fun _ ↦ continuous_apply _).prodMk (continuous_apply _)
  continuous_invFun := by
    refine continuous_pi fun j ↦ ?_
    obtain ⟨j⟩ := j
    refine Fin.lastCases ?_ ?_ j
    · simpa using continuous_snd
    · intro k
      simp only [Fin.lastCases_castSucc]
      exact (continuous_apply (ULift.up k)).comp continuous_fst

@[simp]
theorem uliftSnocHomeo_apply (z : ULift.{u} (Fin (n + 1)) → ℂ) :
    uliftSnocHomeo.{u} n z =
      (fun j ↦ z (ULift.up j.down.castSucc), z (ULift.up (Fin.last n))) :=
  rfl

/-- **Its first component is the map underlying the projection `ℂ^(n+1) ⟶ ℂ^n`.** -/
theorem uliftSnocHomeo_fst (z : ULift.{u} (Fin (n + 1)) → ℂ) :
    (uliftSnocHomeo.{u} n z).1 = okaMapFun (coordEmb (uliftCastSuccEmb.{u} n)) z := by
  rw [okaMapFun_coordEmb]
  rfl

/-- **The projection is the first projection of the product, read through
`ComplexAnalytic.uliftSnocHomeo`.**

The composite form rather than the pointwise one, because it is what lets a statement about
`Prod.fst` transfer along a homeomorphism; compare `ComplexAnalytic.base_sq_eq_conj` in
`OkaTest/FiniteMorphism.lean`. -/
theorem base_proj_eq (n : ℕ) :
    ⇑(AnalyticSpace.proj.{u} n).toLRSHom.base = Prod.fst ∘ uliftSnocHomeo.{u} n :=
  funext fun z ↦ (uliftSnocHomeo_fst z).symm

/-! ### The image of a hypersurface -/

/-- **A morphism cutting its source out of `ℂ^m` by a single global section has that section's
zero set for its image.**

`ComplexAnalytic.IsCutOutBy`'s `range_base` field states the image as the set where every germ
is a non-unit; on `ℂ^m` a germ is a non-unit exactly when the function vanishes, which is
`germ_mem_maximalIdeal_iff`. The `Fin 1` quantifier disappears by `fin_cases`.

Stated for one section because a hypersurface is what the finiteness theorem below is about; the
same proof at `Fin k` would give the intersection of the `k` zero sets. -/
theorem range_base_eq_of_isCutOutBy {m : ℕ} {W : AnalyticSpace.{u}}
    (i : W ⟶ AnalyticSpace.complexAffineSpace.{u} m)
    {F : OkaRing (⊤ : Opens (ULift.{u} (Fin m) → ℂ))}
    (hcut : IsCutOutBy i.toLRSHom ![F]) :
    Set.range (i.toLRSHom.base : W → _) =
      {z | OkaRing.evalHom (U := ⊤) (x := z) trivial F = 0} := by
  rw [hcut.range_base]
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    exact (germ_mem_maximalIdeal_iff (U := ⊤) trivial F).1 (h 0)
  · intro h j
    fin_cases j
    exact (germ_mem_maximalIdeal_iff (U := ⊤) trivial F).2 h

/-! ### Finiteness of the projection -/

variable {d : ℕ} {W : AnalyticSpace.{u}}

/-- **The projection of a monic hypersurface to its base is finite.**

`i` is any closed embedding of `W` into `ℂ^(n+1)` whose image is the zero locus of the family
`q` of monic polynomials of one fixed degree `d`, read in the last coordinate; the conclusion is
that `i` followed by the projection forgetting that coordinate is closed with finite fibres.

The whole proof is `ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` at the two
set-level theorems of `Oka/Topology/Algebra/Polynomial.lean`, transported across
`ComplexAnalytic.uliftSnocHomeo`. **Continuity of the coefficients is the only analytic input and
it is a hypothesis**: no holomorphy is used, and `hc` is what a Weierstrass polynomial supplies. -/
theorem isFinite_comp_proj_of_range_eq
    (i : W ⟶ AnalyticSpace.complexAffineSpace.{u} (n + 1))
    (hi : IsClosedEmbedding (i.toLRSHom.base : W → _))
    {q : (ULift.{u} (Fin n) → ℂ) → Polynomial ℂ}
    (hm : ∀ w, (q w).Monic) (hd : ∀ w, (q w).natDegree = d)
    (hc : ∀ j, Continuous fun w ↦ (q w).coeff j)
    (hrange : Set.range (i.toLRSHom.base : W → _) =
      {z | (q (uliftSnocHomeo.{u} n z).1).eval (uliftSnocHomeo.{u} n z).2 = 0}) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.proj.{u} n) := by
  refine AnalyticSpace.isFinite_comp_of_isClosedEmbedding i _ hi (fun t ht hsub ↦ ?_) (fun s ↦ ?_)
  · have himg : ⇑(AnalyticSpace.proj.{u} n).toLRSHom.base '' t
        = Prod.fst '' (uliftSnocHomeo.{u} n '' t) := by
      rw [base_proj_eq]
      exact Set.image_comp _ _ _
    rw [himg]
    refine Polynomial.isClosed_fst_image_of_monic hm hd hc
      ((uliftSnocHomeo.{u} n).isClosedMap t ht) ?_
    rintro _ ⟨z, hz, rfl⟩
    have hmem := hsub hz
    rw [hrange] at hmem
    exact hmem
  · have hset : Set.range (i.toLRSHom.base : W → _) ∩
        ⇑(AnalyticSpace.proj.{u} n).toLRSHom.base ⁻¹' {s}
        = uliftSnocHomeo.{u} n ⁻¹'
          ({y : (ULift.{u} (Fin n) → ℂ) × ℂ | (q y.1).eval y.2 = 0} ∩ Prod.fst ⁻¹' {s}) := by
      ext z
      simp only [hrange, base_proj_eq, Set.mem_inter_iff, Set.mem_preimage,
        Function.comp_apply, Set.mem_singleton_iff]
      exact Iff.rfl
    rw [hset]
    exact Set.Finite.preimage (uliftSnocHomeo.{u} n).injective.injOn
      (Polynomial.finite_inter_fst_preimage_of_monic hm s fun y hy ↦ hy)

/-- **The same, for a hypersurface presented by `ComplexAnalytic.IsCutOutBy`.**

`hF` is the identity that makes `F` the Weierstrass polynomial of the family `q`: its value at a
point of `ℂ^(n+1)` is the value of `q` at the first `n` coordinates, evaluated at the last one.
Nothing extracts `q` from `F`; see the module docstring. -/
theorem isFinite_comp_proj_of_isCutOutBy
    (i : W ⟶ AnalyticSpace.complexAffineSpace.{u} (n + 1))
    {F : OkaRing (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))}
    (hcut : IsCutOutBy i.toLRSHom ![F])
    {q : (ULift.{u} (Fin n) → ℂ) → Polynomial ℂ}
    (hm : ∀ w, (q w).Monic) (hd : ∀ w, (q w).natDegree = d)
    (hc : ∀ j, Continuous fun w ↦ (q w).coeff j)
    (hF : ∀ z, OkaRing.evalHom (U := ⊤) (x := z) trivial F =
      (q (uliftSnocHomeo.{u} n z).1).eval (uliftSnocHomeo.{u} n z).2) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.proj.{u} n) :=
  isFinite_comp_proj_of_range_eq i hcut.isClosedEmbedding hm hd hc
    ((range_base_eq_of_isCutOutBy i hcut).trans (by simp only [hF]))

end ComplexAnalytic

end

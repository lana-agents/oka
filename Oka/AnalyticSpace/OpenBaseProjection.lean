/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.MonicProjection
import Oka.AnalyticSpace.OpenSubspace
import Oka.AnalyticSpace.SimpleZeroStalk

/-!
# Over an open subset of the base: the projection of a cylinder

`Oka/AnalyticSpace/MonicProjection.lean` and `Oka/AnalyticSpace/SimpleZeroStalk.lean` are the two
halves of *the analytification of a standard étale morphism is finite étale*, and both are stated
with `i` landing in the **whole** of `ℂ^(n+1)`. A standard étale algebra inverts a polynomial as
well as cutting one out, so its analytification lives in an open subspace, and each half says in
its own `## What is not here` that carrying it across a restriction is separate work. This file is
that work, for both at once, because both need the same object.

The object is the **cylinder** `V × ℂ` over an open `V ⊆ ℂ^n`, and the morphism is the projection
`ℂ^(n+1)|(V × ℂ) ⟶ ℂ^n|V` it carries.

## Why the cylinder is a preimage and not a product

`ComplexAnalytic.cylinder V` is defined as `(Opens.map (AnalyticSpace.proj n).toLRSHom.base).obj
V`, the preimage of `V` under the projection — **not** as a product of open sets, though
`ComplexAnalytic.mem_cylinder` says it is one. That is the whole design of this file: the preimage
is the spelling `ComplexAnalytic.restrictHom` asks for, so the projection over `V` is literally
`ComplexAnalytic.AnalyticSpace.proj` restricted, and everything already proved about a restricted
morphism applies to it with no transport:

* `ComplexAnalytic.base_restrictHom` computes its underlying map, which is what
  `ComplexAnalytic.base_projRestrict_eq` turns into the product reading;
* `ComplexAnalytic.stalkMap_restrictHom_eq'` factors its stalk map through
  `ComplexAnalytic.restrictStalkEquiv`, which is what the stalk half below is;
* `ComplexAnalytic.isClosedEmbedding_base_restrictHom` and
  `ComplexAnalytic.IsCutOutBy.restrictOpen` are what a *chart* keeps, for a caller building the
  source.

A product definition would have bought the second reading and lost all three.

## `TopologicalSpace.Opens.extend'` is the same construction and is not usable here

`Oka/OkaRing.lean` already has the cylinder: `TopologicalSpace.Opens.extend'` takes
`Opens (Fin n → ℂ)` to `Opens (Fin (n + 1) → ℂ)`, with `TopologicalSpace.Opens.mem_extend'` the
`Fin.init` reading of the membership. It is indexed by `Fin n` and this file needs
`ULift (Fin n)`: `ComplexAnalytic.AnalyticSpace.complexAffineSpace n` is
`complexSpace (ULift (Fin n))`, so `extend'` does not typecheck against it, and nothing relabels
the two — `Oka/AnalyticSpace/ProjectionStalk.lean`'s module docstring records that there is no
morphism of spaces between the two spellings of `ℂ^n` above `Type 0`, which is why
`ComplexAnalytic.uliftCastSuccEmb` exists beside `ComplexAnalytic.projCoords` rather than being
derived from it. `extend'` is consumed by `Oka/Weierstrass.lean` and `Oka/Statement.lean`, both
`Fin`-indexed throughout, and by nothing on the `AnalyticSpace` side. So this is the second
cylinder for the same reason there are two projections, and the duplication is the `ULift` one
and not a fresh one.

## The finiteness half

`ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` is
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` with `ComplexAnalytic.uliftSnocHomeo` replaced by
its restriction `ComplexAnalytic.cylinderHomeo`, and the proof is the same four steps.
**No new mirror-tree theorem was needed**: `Polynomial.isClosed_fst_image_of_monic` and
`Polynomial.finite_inter_fst_preimage_of_monic` are stated for an arbitrary topological parameter
space, so they are instantiated at `V` rather than at `ℂ^n`, and the family `q` is a family of
polynomials indexed by `V` — its coefficients are asked to be continuous on `V` and nowhere else.

The degree is still *fixed* and not merely bounded, and restricting the base does not change that:
a family whose leading coefficient degenerates has roots escaping to infinity and the projection is
then not closed.

## The stalk half

`ComplexAnalytic.bijective_stalkMap_comp_projRestrict` is
`ComplexAnalytic.bijective_stalkMap_comp_of_incl` — the abstract step, which is stated for
arbitrary locally ringed spaces and so needs no restricting — at two identifications of the two
stalks with `LocalOkaRing`s. Those identifications are the content:

* `ComplexAnalytic.cylinderStalkEquiv` is the stalk of `𝒪_{ℂ^(n+1)}` at the point below, reached
  through the inverse of the stalk map of the inclusion of the open subspace, which is an
  isomorphism by `ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`. That instance and
  `AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso` are the same isomorphism at two
  spellings, and the one used here is the one a caller of `ofRestrict` already holds; the named
  `Iso` is never built, because what the `RingEquiv` needs is `asIso` of the instance;
* `ComplexAnalytic.baseStalkEquiv` is the same for the base, through
  `ComplexAnalytic.restrictStalkEquiv`, which `Oka/AnalyticSpace/Restrict.lean` already built for
  exactly this factorisation.

**Both bullets name declarations rather than another file's prose, and that is deliberate.** The
first used to say that `Oka/AnalyticSpace/SimpleZeroStalk.lean` *names* this isomorphism *as
missing*; that file now says the opposite in terms, and the clause went stale on the day its
paragraph was rewritten. A cross-reference that quotes another file's stance goes stale every
time that stance moves; one that names a declaration does not.

`ComplexAnalytic.cylinderStalkEquiv_stalkMap_projRestrict` is then the `hP` hypothesis of the
abstract step and is where `ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply`
enters; the two cut-out hypotheses go through unchanged, since
`ComplexAnalytic.IsCutOutBy.surjective_stalkMap` and
`ComplexAnalytic.IsCutOutBy.mem_ker_stalkMap_iff` are about the source of `i` and not about its
target.

## Reading the cutting section

The cutting section `F` is a global section of `𝒪` of the **cylinder subspace**, and that ring is
not `OkaRing (cylinder V)`: the restricted presheaf sends `⊤` to
`Subtype.val '' Set.univ`, which is equal to `cylinder V` and not definitionally so (measured:
`rfl` fails on the two rings). So a germ of `F` is not a Taylor series until something says which
function `F` is. `ComplexAnalytic.cylinderStalkEquiv_Γgerm_resΓ` and
`ComplexAnalytic.range_base_eq_of_isCutOutBy_resΓ` say it for the case the standard étale line
produces — `F` the restriction of an entire function `G`, which is what a polynomial equation
gives — and they are what make the simple-zero hypothesis and the cut-out hypothesis checkable.

## Main definitions

- `ComplexAnalytic.cylinder`: **the cylinder `V × ℂ` over an open subset of `ℂ^n`**, as an open
  subset of `ℂ^(n+1)`.
- `ComplexAnalytic.AnalyticSpace.projRestrict`: **the projection `ℂ^(n+1)|(V × ℂ) ⟶ ℂ^n|V`**, as a
  morphism of complex analytic spaces.
- `ComplexAnalytic.cylinderHomeo`: **the cylinder is homeomorphic to `V × ℂ`**, by the
  restriction of `ComplexAnalytic.uliftSnocHomeo`.
- `ComplexAnalytic.cylinderStalkEquiv` and `ComplexAnalytic.baseStalkEquiv`: the stalks of the two
  open subspaces, as `LocalOkaRing`s.

## Main results

- `ComplexAnalytic.mem_cylinder`: the cylinder is the product, read through
  `ComplexAnalytic.uliftSnocHomeo`.
- `ComplexAnalytic.base_projRestrict_eq`: **the projection over `V` is `Prod.fst`** through
  `ComplexAnalytic.cylinderHomeo`.
- `ComplexAnalytic.range_base_eq_of_isCutOutBy_resΓ`: a hypersurface of the cylinder cut out by
  the restriction of an entire function has that function's zero set for its image.
- `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq`: **the projection of a monic
  hypersurface of the cylinder to `V` is finite.**
- `ComplexAnalytic.isFinite_comp_projRestrict_of_isCutOutBy`: the same with the hypersurface
  presented as a cut-out by one restricted entire function.
- `ComplexAnalytic.cylinderStalkEquiv_stalkMap_projRestrict`: **the stalk map of the projection
  over `V` is the inclusion of the germs not involving the last variable**, once both stalks are
  read as germ rings by the two equivalences above.
- `ComplexAnalytic.cylinderStalkEquiv_stalkMap_ofRestrict` and
  `ComplexAnalytic.cylinderStalkEquiv_Γgerm_resΓ`: what
  `ComplexAnalytic.cylinderStalkEquiv` does to the stalk map of the inclusion, and to the germ of
  a restricted entire function.
- `ComplexAnalytic.bijective_stalkMap_comp_projRestrict` and
  `ComplexAnalytic.isIso_stalkMap_comp_projRestrict`: **the projection of a hypersurface of the
  cylinder with a simple zero is an isomorphism on stalks.**

## What is not here

* **No `IsFiniteEtale`, and no `IsLocalIso`.** The two halves are transported separately and
  nothing below joins them; that is the assembly the Riemann-existence line does, and it needs a
  third thing neither half supplies — that the underlying map of the composite is a local
  homeomorphism. As on the whole of `ℂ^(n+1)`, a monic family with repeated roots gives a
  composite that is not one, so this is not a gap that closes by an argument of the same kind.
* **No Weierstrass polynomial, and the family is still a hypothesis in this file.** It is one
  here exactly as it is in `Oka/AnalyticSpace/MonicProjection.lean`, and no holomorphy of its
  coefficients is used or asked for below — continuity is all the proofs consume.
  **What is no longer absent from the repository is the extraction**:
  `ComplexAnalytic.okaFamily` in `Oka/AnalyticSpace/HolomorphicFamily.lean`, which imports this
  file, produces a family satisfying all three hypotheses from a monic
  `P : Polynomial (OkaRing V)`. What is still missing there and here is the step before that, a
  `P` obtained from a *germ* by the Weierstrass preparation theorem.
* **Nothing about a section of the cylinder that does not extend.** The two `resΓ` lemmas above
  read a cutting section that is the restriction of an entire function. A section of
  `𝒪_{ℂ^(n+1)}` over the cylinder that extends to no larger open set is allowed by every
  statement below and computed by none of them. **What
  `ComplexAnalytic.cylinderSection` in `Oka/AnalyticSpace/HolomorphicFamily.lean` adds is the
  construction and not the example**: it builds a section of the cylinder out of a
  `Polynomial (OkaRing V)`, whose coefficients live on `V` and are required to extend nowhere,
  and it pays for that by taking its hypersurface as a range condition rather than as a
  `ComplexAnalytic.IsCutOutBy` datum, for the reason this bullet gives. **Whether any output of
  it fails to extend is settled nowhere**: the coefficients of the one such polynomial this
  repository writes down are entire, which `OkaTest/HolomorphicFamily.lean` records.
* **No second restriction.** `V` is an open subset of `ℂ^n` and the source of `i` is any analytic
  space; there is no statement about restricting `V` further, which would be
  `ComplexAnalytic.restrictHom` again and is not needed by anything.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/
open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### The cylinder and the projection it carries -/

/-- **The cylinder `V × ℂ` over an open subset `V` of `ℂ^n`**, as an open subset of `ℂ^(n+1)`.

Defined as the preimage of `V` under `ComplexAnalytic.AnalyticSpace.proj` and not as a product;
`ComplexAnalytic.mem_cylinder` is the product reading and the module docstring says why the
preimage is the definition. `TopologicalSpace.Opens.extend'` is the same construction for the
`Fin`-indexed `ℂ^n` and does not typecheck here; see the module docstring. -/
def cylinder (V : Opens (ULift.{u} (Fin n) → ℂ)) :
    Opens (ULift.{u} (Fin (n + 1)) → ℂ) :=
  (Opens.map (AnalyticSpace.proj.{u} n).toLRSHom.base).obj V

/-- **A point of `ℂ^(n+1)` lies in the cylinder over `V` exactly when its first `n` coordinates
do in `V`**, the first `n` coordinates being read off by `ComplexAnalytic.uliftSnocHomeo`.

The analogue of `TopologicalSpace.Opens.mem_extend'`, whose reading is by `Fin.init`. -/
theorem mem_cylinder {V : Opens (ULift.{u} (Fin n) → ℂ)} {z : ULift.{u} (Fin (n + 1)) → ℂ} :
    z ∈ cylinder V ↔ (uliftSnocHomeo.{u} n z).1 ∈ V := by
  change (AnalyticSpace.proj.{u} n).toLRSHom.base z ∈ V ↔ _
  rw [base_proj_eq]
  exact Iff.rfl

/-- **The projection `ℂ^(n+1)|(V × ℂ) ⟶ ℂ^n|V`**, as a morphism of complex analytic spaces.

It is `ComplexAnalytic.AnalyticSpace.proj` restricted, on the nose:
`ComplexAnalytic.cylinder V` is by definition the preimage of `V`, so this is
`ComplexAnalytic.AnalyticSpace.restrictHom` at no cost, and every lemma about a restricted
morphism applies to it. -/
def AnalyticSpace.projRestrict (V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)) :
    (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V) ⟶
      (AnalyticSpace.complexAffineSpace.{u} n).restrict V :=
  AnalyticSpace.restrictHom (AnalyticSpace.proj.{u} n) V

/-- **The cylinder over `V` is homeomorphic to `V × ℂ`.**

`ComplexAnalytic.uliftSnocHomeo` restricted: the same two formulas, with the membership carried
across by `ComplexAnalytic.mem_cylinder`. This is the carrier bridge across which the two
set-level theorems of `Oka/Topology/Algebra/Polynomial.lean` are read at the parameter space `V`,
exactly as `uliftSnocHomeo` is at the parameter space `ℂ^n` in
`Oka/AnalyticSpace/MonicProjection.lean`. -/
def cylinderHomeo (V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)) :
    ↥(cylinder V) ≃ₜ (↥V × ℂ) where
  toFun z := (⟨(uliftSnocHomeo.{u} n z.1).1, mem_cylinder.1 z.2⟩, (uliftSnocHomeo.{u} n z.1).2)
  invFun w := ⟨(uliftSnocHomeo.{u} n).symm (w.1.1, w.2), mem_cylinder.2 (by
    rw [Homeomorph.apply_symm_apply]; exact w.1.2)⟩
  left_inv z := Subtype.ext ((uliftSnocHomeo.{u} n).symm_apply_apply z.1)
  right_inv w := by
    have h := (uliftSnocHomeo.{u} n).apply_symm_apply (w.1.1, w.2)
    refine Prod.ext (Subtype.ext ?_) ?_
    · change ((uliftSnocHomeo.{u} n) ((uliftSnocHomeo.{u} n).symm
        ((w.1 : ULift.{u} (Fin n) → ℂ), w.2))).1 = _
      rw [h]
    · change ((uliftSnocHomeo.{u} n) ((uliftSnocHomeo.{u} n).symm
        ((w.1 : ULift.{u} (Fin n) → ℂ), w.2))).2 = _
      rw [h]
  continuous_toFun := by
    have h : Continuous fun z : ↥(cylinder V) ↦ uliftSnocHomeo.{u} n z.1 :=
      (uliftSnocHomeo.{u} n).continuous.comp continuous_subtype_val
    exact (h.fst.subtype_mk _).prodMk h.snd
  continuous_invFun :=
    ((uliftSnocHomeo.{u} n).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

/-- The two components of `ComplexAnalytic.cylinderHomeo`, as `ComplexAnalytic.cylinder` reads
them. -/
@[simp]
theorem cylinderHomeo_apply (V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ))
    (z : ↥(cylinder V)) :
    cylinderHomeo V z =
      (⟨(uliftSnocHomeo.{u} n z.1).1, mem_cylinder.1 z.2⟩, (uliftSnocHomeo.{u} n z.1).2) :=
  rfl

/-- **The projection over `V` is the first projection of the product**, read through
`ComplexAnalytic.cylinderHomeo`.

The composite form rather than the pointwise one, because it is what lets a statement about
`Prod.fst` transfer along a homeomorphism; the analogue of `ComplexAnalytic.base_proj_eq`, and
proved from it through `ComplexAnalytic.base_restrictHom`. -/
theorem base_projRestrict_eq (V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)) :
    ⇑(AnalyticSpace.projRestrict V).toLRSHom.base = Prod.fst ∘ cylinderHomeo V :=
  funext fun z ↦ Subtype.ext
    ((base_restrictHom (AnalyticSpace.proj.{u} n).toLRSHom V z).trans
      (uliftSnocHomeo_fst _).symm)

variable {W : AnalyticSpace.{u}}

/-! ### Finiteness of the projection over `V` -/

/-- **A hypersurface of the cylinder cut out by the restriction of an entire function has that
function's zero set for its image.**

The analogue of `ComplexAnalytic.range_base_eq_of_isCutOutBy`, and it needs one step more: the
germ of the restricted section is the image of the ambient germ under the stalk map of the
inclusion of the open subspace, which is an isomorphism and therefore reflects the maximal ideal
(`ComplexAnalytic.mem_maximalIdeal_stalkMap_iff`); `germ_mem_maximalIdeal_iff` then reads the
ambient germ as a value.

**The cutting section is `G` restricted and not an arbitrary section of the cylinder.** That is
not a convenience: the global sections of the cylinder subspace are not `OkaRing (cylinder V)` on
the nose, so `germ_mem_maximalIdeal_iff` does not apply to a section that is not a restriction.
See the module docstring. -/
theorem range_base_eq_of_isCutOutBy_resΓ
    {V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)}
    (i : W ⟶ (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V))
    {G : OkaRing (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin (n + 1)) → ℂ))}
    (hcut : IsCutOutBy i.toLRSHom
      ![(AnalyticSpace.complexAffineSpace.{u} (n + 1)).resΓ (cylinder V) G]) :
    Set.range (i.toLRSHom.base : W → _) =
      {z | OkaRing.evalHom (U := ⊤)
        (x := ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
          (cylinder V)).toLRSHom.base z) trivial G = 0} := by
  rw [hcut.range_base]
  have hiff : ∀ z : ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V)),
      ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V)).presheaf.Γgerm z
          ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).resΓ (cylinder V) G) ∈
        IsLocalRing.maximalIdeal
          (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict
            (cylinder V)).presheaf.stalk z) ↔
      OkaRing.evalHom (U := ⊤)
        (x := ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
          (cylinder V)).toLRSHom.base z) trivial G = 0 := by
    intro z
    have hgerm : ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict
        (cylinder V)).presheaf.Γgerm z
          ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).resΓ (cylinder V) G) =
        ((((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
          (cylinder V)).toLRSHom.stalkMap z).hom
          ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).presheaf.Γgerm
            (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
              (cylinder V)).toLRSHom.base z) G)) :=
      (LocallyRingedSpace.stalkMap_germ_apply
        ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict (cylinder V)).toLRSHom ⊤ z
        trivial G).symm
    rw [hgerm, mem_maximalIdeal_stalkMap_iff]
    exact germ_mem_maximalIdeal_iff (U := ⊤) trivial G
  refine Set.ext fun z ↦ ?_
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    exact (hiff z).1 (h 0)
  · intro h j
    fin_cases j
    exact (hiff z).2 h

variable {d : ℕ}

/-- **The projection of a monic hypersurface of the cylinder to `V` is finite.**

`ComplexAnalytic.isFinite_comp_proj_of_range_eq` over an open subset of the base. `i` is any
closed embedding of `W` into `ℂ^(n+1)|(V × ℂ)` whose image is the zero locus of the family `q` of
monic polynomials of one fixed degree `d`, read in the last coordinate; the conclusion is that `i`
followed by `ComplexAnalytic.AnalyticSpace.projRestrict` is closed with finite fibres.

The proof is the unrestricted one with `ComplexAnalytic.cylinderHomeo` in place of
`ComplexAnalytic.uliftSnocHomeo`. **The parameter space is `V` and not `ℂ^n`**:
`Polynomial.isClosed_fst_image_of_monic` and `Polynomial.finite_inter_fst_preimage_of_monic` are
stated over an arbitrary topological space, so `q` is a family indexed by `V` and its coefficients
are asked to be continuous there and nowhere else. No mirror-tree theorem was added. -/
theorem isFinite_comp_projRestrict_of_range_eq
    {V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)}
    (i : W ⟶ (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V))
    (hi : IsClosedEmbedding (i.toLRSHom.base : W → _))
    {q : ↥V → Polynomial ℂ}
    (hm : ∀ w, (q w).Monic) (hd : ∀ w, (q w).natDegree = d)
    (hc : ∀ j, Continuous fun w ↦ (q w).coeff j)
    (hrange : Set.range (i.toLRSHom.base : W → _) =
      {z | (q (cylinderHomeo V z).1).eval (cylinderHomeo V z).2 = 0}) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.projRestrict V) := by
  refine AnalyticSpace.isFinite_comp_of_isClosedEmbedding i _ hi (fun t ht hsub ↦ ?_) (fun s ↦ ?_)
  · have himg : ⇑(AnalyticSpace.projRestrict V).toLRSHom.base '' t
        = Prod.fst '' (cylinderHomeo V '' t) := by
      rw [base_projRestrict_eq]
      exact Set.image_comp _ _ _
    rw [himg]
    refine Polynomial.isClosed_fst_image_of_monic hm hd hc
      ((cylinderHomeo V).isClosedMap t ht) ?_
    rintro _ ⟨z, hz, rfl⟩
    have hmem := hsub hz
    rw [hrange] at hmem
    exact hmem
  · have hset : Set.range (i.toLRSHom.base : W → _) ∩
        ⇑(AnalyticSpace.projRestrict V).toLRSHom.base ⁻¹' {s}
        = cylinderHomeo V ⁻¹'
          ({y : ↥V × ℂ | (q y.1).eval y.2 = 0} ∩ Prod.fst ⁻¹' {s}) := by
      ext z
      simp only [hrange, base_projRestrict_eq, Set.mem_inter_iff, Set.mem_preimage,
        Function.comp_apply, Set.mem_singleton_iff]
      exact Iff.rfl
    rw [hset]
    exact Set.Finite.preimage (cylinderHomeo V).injective.injOn
      (Polynomial.finite_inter_fst_preimage_of_monic hm s fun y hy ↦ hy)

/-- **The same, for a hypersurface presented by `ComplexAnalytic.IsCutOutBy`.**

`hG` is the identity that makes the entire function `G` the Weierstrass polynomial of the family
`q` on the cylinder: its value at a point is the value of `q` at the first `n` coordinates,
evaluated at the last one. Nothing extracts `q` from `G`; see the module docstring. -/
theorem isFinite_comp_projRestrict_of_isCutOutBy
    {V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ)}
    (i : W ⟶ (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V))
    {G : OkaRing (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin (n + 1)) → ℂ))}
    (hcut : IsCutOutBy i.toLRSHom
      ![(AnalyticSpace.complexAffineSpace.{u} (n + 1)).resΓ (cylinder V) G])
    {q : ↥V → Polynomial ℂ}
    (hm : ∀ w, (q w).Monic) (hd : ∀ w, (q w).natDegree = d)
    (hc : ∀ j, Continuous fun w ↦ (q w).coeff j)
    (hG : ∀ z : (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V),
      OkaRing.evalHom (U := ⊤)
        (x := ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
          (cylinder V)).toLRSHom.base z) trivial G =
        (q (cylinderHomeo V z).1).eval (cylinderHomeo V z).2) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.projRestrict V) :=
  isFinite_comp_projRestrict_of_range_eq i hcut.isClosedEmbedding hm hd hc
    ((range_base_eq_of_isCutOutBy_resΓ i hcut).trans (by simp only [hG]; rfl))

/-! ### The stalk map of the projection over `V` -/

section Stalk

variable (V : TopologicalSpace.Opens (ULift.{u} (Fin n) → ℂ))

/-- **The stalk of `𝒪` of the cylinder subspace at a point, as a `LocalOkaRing`.**

Three steps: the inclusion of an open subspace is an isomorphism on stalks
(`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`), so its inverse identifies this stalk
with the ambient one; `okaStalkEquiv` reads that as `LocalOkaRing (ULift (Fin (n+1)))`; and
`LocalOkaRing.uliftEquiv` relabels the index type to the one the Weierstrass theorems use. Only
the first step is new here. -/
def cylinderStalkEquiv (y : (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V)) :
    ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V)).presheaf.stalk y ≃+*
      LocalOkaRing (Fin (n + 1)) :=
  ((asIso (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
      (cylinder V)).toLRSHom.stalkMap y)).symm.commRingCatIsoToRingEquiv).trans
    ((okaStalkEquiv (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
      (cylinder V)).toLRSHom.base y)).trans (LocalOkaRing.uliftEquiv (Fin (n + 1))))

/-- **The stalk of `𝒪` of the base subspace at the image point, as a `LocalOkaRing`.**

The same three steps, with `ComplexAnalytic.restrictStalkEquiv` in place of the inverse stalk map
— that composite is what `Oka/AnalyticSpace/Restrict.lean` built for exactly this factorisation,
and using it is what makes `ComplexAnalytic.cylinderStalkEquiv_stalkMap_projRestrict` two
rewrites. -/
def baseStalkEquiv (y : (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V)) :
    ((AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.stalk
        ((AnalyticSpace.projRestrict V).toLRSHom.base y) ≃+* LocalOkaRing (Fin n) :=
  ((restrictStalkEquiv (AnalyticSpace.proj.{u} n).toLRSHom V y).commRingCatIsoToRingEquiv).trans
    ((okaStalkEquiv _).trans (LocalOkaRing.uliftEquiv (Fin n)))

/-- **`ComplexAnalytic.cylinderStalkEquiv` undoes the stalk map of the inclusion**: on a germ that
comes from the ambient space it is `okaStalkEquiv` followed by the index relabelling, with the
inverse stalk map gone. Two of the equivalence's three steps survive, not one — the relabelling is
what puts the answer in the index type the Weierstrass side uses. -/
theorem cylinderStalkEquiv_stalkMap_ofRestrict
    (y : (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V))
    (v : (AnalyticSpace.complexAffineSpace.{u} (n + 1)).presheaf.stalk
      (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
        (cylinder V)).toLRSHom.base y)) :
    cylinderStalkEquiv V y ((((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
        (cylinder V)).toLRSHom.stalkMap y).hom v) =
      LocalOkaRing.uliftEquiv (Fin (n + 1))
        (okaStalkEquiv (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
          (cylinder V)).toLRSHom.base y) v) := by
  change LocalOkaRing.uliftEquiv (Fin (n + 1)) (okaStalkEquiv _
    ((inv (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
        (cylinder V)).toLRSHom.stalkMap y)).hom
      ((((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
        (cylinder V)).toLRSHom.stalkMap y).hom v))) = _
  rw [inv_hom_apply]

/-- **The stalk map of the projection over `V` is `LocalOkaRing.incl`**, once both stalks are read
as `LocalOkaRing`s.

This is the `hP` hypothesis of `ComplexAnalytic.bijective_stalkMap_comp_of_incl` and the only
place the transport does any work: `ComplexAnalytic.stalkMap_restrictHom_eq'` factors the stalk
map into the two isomorphisms the two equivalences above are built from and the ambient stalk map
of the projection, and `ComplexAnalytic.AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply` is
that middle factor. -/
theorem cylinderStalkEquiv_stalkMap_projRestrict
    (y : (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V))
    (t : ((AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.stalk
      ((AnalyticSpace.projRestrict V).toLRSHom.base y)) :
    cylinderStalkEquiv V y (((AnalyticSpace.projRestrict V).toLRSHom.stalkMap y).hom t) =
      LocalOkaRing.incl (baseStalkEquiv V y t) := by
  have hfac : ((AnalyticSpace.projRestrict V).toLRSHom.stalkMap y).hom t =
      (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
        (cylinder V)).toLRSHom.stalkMap y).hom
        (((AnalyticSpace.proj.{u} n).toLRSHom.stalkMap _).hom
          ((restrictStalkEquiv (AnalyticSpace.proj.{u} n).toLRSHom V y).hom.hom t)) :=
    ConcreteCategory.congr_hom
      (stalkMap_restrictHom_eq' (AnalyticSpace.proj.{u} n).toLRSHom V y) t
  rw [hfac, cylinderStalkEquiv_stalkMap_ofRestrict]
  exact AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply _

/-- **The germ of a restricted entire function is its Taylor series**, read through
`ComplexAnalytic.cylinderStalkEquiv`.

This is what makes the simple-zero hypothesis of the two theorems below checkable: it is a
condition on an element of an abstract stalk, and for the sections a polynomial equation produces
— restrictions of entire functions — this computes that element as `OkaRing.germ`, which is the
spelling `Oka/AnalyticSpace/SimpleZeroStalk.lean` states its own hypothesis in. -/
theorem cylinderStalkEquiv_Γgerm_resΓ
    (y : (AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V))
    (G : OkaRing (⊤ : TopologicalSpace.Opens (ULift.{u} (Fin (n + 1)) → ℂ))) :
    cylinderStalkEquiv V y
        (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V)).presheaf.Γgerm y
          ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).resΓ (cylinder V) G)) =
      LocalOkaRing.uliftEquiv (Fin (n + 1))
        (OkaRing.germ (U := ⊤) (y := ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
          (cylinder V)).toLRSHom.base y) trivial G) := by
  rw [show ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V)).presheaf.Γgerm y
      ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).resΓ (cylinder V) G) =
      ((((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
        (cylinder V)).toLRSHom.stalkMap y).hom
        ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).presheaf.Γgerm
          (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict
            (cylinder V)).toLRSHom.base y) G)) from
    (LocallyRingedSpace.stalkMap_germ_apply
      ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).ofRestrict (cylinder V)).toLRSHom ⊤ y
      trivial G).symm, cylinderStalkEquiv_stalkMap_ofRestrict]
  exact congrArg (LocalOkaRing.uliftEquiv (Fin (n + 1))) (okaStalkEquiv_germ _ G)

variable {X : LocallyRingedSpace.{u}}
  {i : X ⟶ ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict
    (cylinder V)).toLocallyRingedSpace}
  {F : ((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict (cylinder V)).presheaf.obj (op ⊤)}

/-- **The projection of a hypersurface of the cylinder with a simple zero is bijective on
stalks.**

`ComplexAnalytic.bijective_stalkMap_comp_uliftProj` over an open subset of the base, and it is
`ComplexAnalytic.bijective_stalkMap_comp_of_incl` at the two identifications above: that step is
stated for arbitrary locally ringed spaces, so nothing in it has to be restricted, and the two
hypotheses coming from `hcut` are about the source of `i` and not about its target.

`F` is a global section of `𝒪` of the cylinder subspace; when it is the restriction of an entire
function, `ComplexAnalytic.cylinderStalkEquiv_Γgerm_resΓ` computes the germ in `hf`. -/
theorem bijective_stalkMap_comp_projRestrict (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((cylinderStalkEquiv V (i.base x)
        (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict
          (cylinder V)).presheaf.Γgerm (i.base x) F) :
            LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    Function.Bijective ((i ≫ (AnalyticSpace.projRestrict V).toLRSHom).stalkMap x).hom :=
  bijective_stalkMap_comp_of_incl i _ x (baseStalkEquiv V (i.base x))
    (cylinderStalkEquiv V (i.base x))
    (fun t ↦ cylinderStalkEquiv_stalkMap_projRestrict V (i.base x) t)
    (hcut.surjective_stalkMap x) (fun s ↦ hcut.mem_ker_stalkMap_iff x _ rfl s) hf

/-- **The same as an isomorphism.** The morphism is
`ComplexAnalytic.AnalyticSpace.projRestrict`'s underlying morphism of locally ringed spaces. -/
theorem isIso_stalkMap_comp_projRestrict (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((cylinderStalkEquiv V (i.base x)
        (((AnalyticSpace.complexAffineSpace.{u} (n + 1)).restrict
          (cylinder V)).presheaf.Γgerm (i.base x) F) :
            LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    IsIso ((i ≫ (AnalyticSpace.projRestrict V).toLRSHom).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkMap_comp_projRestrict V hcut x hf)

end Stalk

end ComplexAnalytic

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Coherent
import Oka.AnalyticSpace.ZeroLocus
import Oka.Polynomial
import Oka.StalkEquiv

/-!
# Local models, and the analytic spaces they carve out

`Oka/AnalyticSpace/ZeroLocus.lean` makes the zero locus of finitely many global sections of the
structure sheaf of an arbitrary locally ringed space `Y` into a locally ringed space, and shows
that its inclusion satisfies `ComplexAnalytic.IsCutOutBy`. Here we specialise `Y` to an open
subset of `ℂ^n` and read off the two consequences the definitions of
`Oka/AnalyticSpace/Basic.lean` were designed for: such a zero locus is a
`ComplexAnalytic.IsLocalModel`, and it is a `ComplexAnalytic.AnalyticSpace`.

The `ℂ`-algebra structure is where the two differ. `IsLocalModel` is a statement about the
underlying locally ringed space and follows by unfolding an existential. An `AnalyticSpace`
must in addition carry a ring homomorphism `ℂ →+* Γ(X, 𝒪_X)`, and its charts must be
`ℂ`-linear for it. Both come for free from the closed immersion: pulling the constants back
along `i : X ⟶ Y` gives the `ℂ`-algebra structure, and `ℂ`-linearity of `i` for it then holds
by definition. The only thing to check is that the *identity chart* `X.restrict ⊤ ⟶ X` is
`ℂ`-linear, which is `ComplexAnalytic.isCLinearHom_ofRestrict`: the two ring maps involved are
both `𝒪_X(⊤) ⟶ 𝒪_X(U)` in a preorder category, hence equal. This is `AnalyticSpace.ofCutOut`,
and it applies to *any* closed immersion into an open subset of `ℂ^n`, not only to the zero
loci constructed here.

## The node

The point of the exercise is that the main theorem
`ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf` now applies to a space which is not
`ℂ^n`. The last section carries this out for the **node** `{z ∈ ℂ² | z₀ z₁ = 0}`, the union of
the two coordinate axes, cut out by the single polynomial `X 0 * X 1` regarded as a
holomorphic function through `OkaRing.ofMvPolynomial`. Its underlying set really is the union
of the axes: that is `ComplexAnalytic.mem_zeroLocus_nodeSection_iff`, which goes through
`mem_zeroLocus_restrict_complexSpace_iff` — a germ of a holomorphic function is a non-unit
exactly when the function vanishes (`germ_mem_maximalIdeal_iff`) — and the stalks of a
restriction are the stalks of the ambient space
(`AlgebraicGeometry.LocallyRingedSpace.mem_zeroLocus_restrict_iff`).

## Main definitions

- `ComplexAnalytic.AnalyticSpace.ofCutOut`: a locally ringed space cut out by finitely many
  holomorphic functions inside an open subset of `ℂ^n` is a complex analytic space.
- `ComplexAnalytic.AnalyticSpace.zeroLocus`: the analytic subspace of an open subset of `ℂ^n`
  cut out by finitely many holomorphic functions.
- `ComplexAnalytic.nodePoly`, `ComplexAnalytic.nodeSection` and
  `ComplexAnalytic.AnalyticSpace.node`: the node `{z ∈ ℂ² | z₀ z₁ = 0}` as a complex analytic
  space.

## Main results

- `ComplexAnalytic.isCLinearHom_ofRestrict`: the inclusion of an open subspace is `ℂ`-linear
  for the restricted `ℂ`-algebra structure.
- `ComplexAnalytic.isLocalModel_zeroLocus`: **the zero locus of finitely many holomorphic
  functions on an open subset of `ℂ^n` is a local model.**
- `ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf_zeroLocus`: its structure sheaf is
  coherent.
- `ComplexAnalytic.mem_zeroLocus_nodeSection_iff` and
  `ComplexAnalytic.origin_mem_zeroLocus_nodeSection`: the node is the union of the two
  coordinate axes of `ℂ²`, and is not empty.
- `ComplexAnalytic.isCoherentStructureSheaf_node`: Oka's coherence theorem applies to it.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

section ComplexSpace

variable {ι : Type u} [Fintype ι]

open AlgebraicGeometry.LocallyRingedSpace in
/-- A point of an open subset `V` of `ℂ^ι` lies in the zero locus of a family of holomorphic
functions on `V` exactly when every member of the family vanishes there: on `ℂ^ι` a germ is a
non-unit precisely when the function vanishes (`germ_mem_maximalIdeal_iff`). -/
theorem mem_zeroLocus_restrict_complexSpace_iff (V : Opens (complexSpace.{u} ι)) {κ : Type*}
    (f : κ → ((complexSpace.{u} ι).restrict V.isOpenEmbedding).presheaf.obj (op ⊤))
    (y : (complexSpace.{u} ι).restrict V.isOpenEmbedding) :
    y ∈ ((complexSpace.{u} ι).restrict V.isOpenEmbedding).zeroLocus f ↔
      ∀ i, OkaRing.evalHom
        (show (Opens.inclusion' V y : ι → ℂ) ∈ V.isOpenEmbedding.isOpenMap.functor.obj ⊤ from
          ⟨y, trivial, rfl⟩) (f i) = 0 := by
  rw [mem_zeroLocus_restrict_iff]
  refine forall_congr' fun i ↦ ?_
  rw [← germ_mem_maximalIdeal_iff]
  exact (IsLocalRing.mem_maximalIdeal _).symm

end ComplexSpace

namespace ComplexAnalytic

section CLinear

/-- **The inclusion of an open subspace is `ℂ`-linear** for the `ℂ`-algebra structure obtained
by restricting sections, essentially by definition: both sides are the restriction map
`𝒪_X(⊤) ⟶ 𝒪_X(U)`, and `Opens X` is a preorder category, so there is only one such map. -/
theorem isCLinearHom_ofRestrict (X : LocallyRingedSpace.{u}) (α : ℂ →+* X.presheaf.obj (op ⊤))
    (U : Opens X) : IsCLinearHom (X.ofRestrict U.isOpenEmbedding) (X.resAlgMap α U) α := by
  intro c
  change ((X.ofRestrict U.isOpenEmbedding).c.app (op ⊤)).hom (α c) = _
  change (X.presheaf.map _).hom (α c) = (X.presheaf.map _).hom (α c)
  congr 2

end CLinear

variable {n k : ℕ} {V : Opens (complexAffineSpace.{u} n)}

section OfCutOut

variable {Z : LocallyRingedSpace.{u}}
  {i : Z ⟶ (complexAffineSpace.{u} n).restrict V.isOpenEmbedding}
  {f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)}

/-- **A locally ringed space cut out by finitely many holomorphic functions inside an open
subset of `ℂ^n` is a complex analytic space**, with the `ℂ`-algebra structure obtained by
pulling the constant functions back along the closed immersion.

The chart at every point is the whole space: `Z` is covered by the single open subset `⊤`, and
`Z.restrictTopIso.hom ≫ i` cuts `Z.restrict ⊤` out by the same sections
(`IsCutOutBy.comp_iso`). It is `ℂ`-linear because `i` is — that is how the `ℂ`-algebra
structure was chosen — and because the identity chart is (`isCLinearHom_ofRestrict`). -/
def AnalyticSpace.ofCutOut (hcut : IsCutOutBy i f) : AnalyticSpace.{u} where
  toLocallyRingedSpace := Z
  algebraMap := (LocallyRingedSpace.Γ.map i.op).hom.comp (constantsAlgMap n V)
  local_model _ :=
    ⟨⟨⊤, trivial⟩, n, k, V, Z.restrictTopIso.hom ≫ i, f, hcut.comp_iso Z.restrictTopIso,
      (isCLinearHom_ofRestrict Z _ ⊤).comp fun _ ↦ rfl⟩

/-- `AnalyticSpace.ofCutOut` does not change the underlying locally ringed space. -/
lemma AnalyticSpace.ofCutOut_toLocallyRingedSpace (hcut : IsCutOutBy i f) :
    (AnalyticSpace.ofCutOut hcut).toLocallyRingedSpace = Z :=
  rfl

/-- A locally ringed space cut out by finitely many holomorphic functions inside an open subset
of `ℂ^n` is a local model: `IsLocalModel` is exactly the existential over that data. -/
theorem isLocalModel_of_isCutOutBy (hcut : IsCutOutBy i f) : IsLocalModel Z :=
  ⟨n, k, V, i, f, hcut⟩

end OfCutOut

section ZeroLocus

variable (V)
variable (f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤))

/-- **The zero locus of finitely many holomorphic functions on an open subset of `ℂ^n` is a
local model.**

Together with `isLocalModel_complexAffineSpace_restrict_top` this is the first family of local
models the development produces which is not all of `ℂ^n`. -/
theorem isLocalModel_zeroLocus :
    IsLocalModel (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).zeroLocusSubspace f) :=
  isLocalModel_of_isCutOutBy
    (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).isCutOutBy_zeroLocusSubspaceι f)

/-- The **analytic subspace of an open subset of `ℂ^n` cut out by finitely many holomorphic
functions**, as a complex analytic space. -/
def AnalyticSpace.zeroLocus : AnalyticSpace.{u} :=
  AnalyticSpace.ofCutOut
    (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).isCutOutBy_zeroLocusSubspaceι f)

/-- The underlying locally ringed space of `AnalyticSpace.zeroLocus` is the zero locus. -/
lemma AnalyticSpace.zeroLocus_toLocallyRingedSpace :
    (AnalyticSpace.zeroLocus V f).toLocallyRingedSpace =
      ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).zeroLocusSubspace f :=
  rfl

/-- **The structure sheaf of the analytic subspace of an open subset of `ℂ^n` cut out by
finitely many holomorphic functions is coherent.**

This is `AnalyticSpace.isCoherentStructureSheaf` — Oka's coherence theorem — applied to a
space which is not `ℂ^n`. -/
theorem AnalyticSpace.isCoherentStructureSheaf_zeroLocus :
    (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).zeroLocusSubspace
      f).IsCoherentStructureSheaf :=
  (AnalyticSpace.zeroLocus V f).isCoherentStructureSheaf

end ZeroLocus

section Node

/-- The ambient space of the node: `ℂ²`, presented as an open subspace of itself, which is the
shape `IsLocalModel` and `AnalyticSpace.local_model` ask for. -/
abbrev nodeAmbient : LocallyRingedSpace.{u} :=
  (complexAffineSpace.{u} 2).restrict (⊤ : Opens (complexAffineSpace.{u} 2)).isOpenEmbedding

/-- The polynomial `z₀ z₁` on `ℂ²`, whose zero locus is the union of the two coordinate axes.
The coordinates of `complexAffineSpace 2` are indexed by `ULift (Fin 2)`. -/
def nodePoly : MvPolynomial (ULift.{u} (Fin 2)) ℂ :=
  MvPolynomial.X (ULift.up 0) * MvPolynomial.X (ULift.up 1)

/-- The one-element family of holomorphic functions on `ℂ²` cutting out the node: the
polynomial `z₀ z₁`, regarded as a holomorphic function by `OkaRing.ofMvPolynomial`. -/
def nodeSection : Fin 1 → (nodeAmbient.{u}).presheaf.obj (op ⊤) :=
  fun _ ↦ OkaRing.ofMvPolynomial _ nodePoly.{u}

/-- **The zero locus of `nodeSection` is the union of the two coordinate axes of `ℂ²`.**

Without this the node would only be a formal construction; this is what makes it the node. -/
theorem mem_zeroLocus_nodeSection_iff (y : nodeAmbient.{u}) :
    y ∈ nodeAmbient.{u}.zeroLocus nodeSection.{u} ↔
      y.1 (ULift.up 0) * y.1 (ULift.up 1) = 0 := by
  rw [mem_zeroLocus_restrict_complexSpace_iff]
  refine Fin.forall_fin_one.trans ?_
  refine Iff.of_eq (congrArg (· = (0 : ℂ)) ?_)
  refine (OkaRing.evalHom_ofMvPolynomial _ _ nodePoly.{u}).trans ?_
  simp [nodePoly]

/-- The origin lies on the node. In particular the node is not the empty analytic space, which
is what makes the coherence statement below about something. -/
theorem origin_mem_zeroLocus_nodeSection :
    (⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩ : nodeAmbient.{u}) ∈
      nodeAmbient.{u}.zeroLocus nodeSection.{u} :=
  (mem_zeroLocus_nodeSection_iff _).2 (by simp)

/-- **The node** `{z ∈ ℂ² | z₀ z₁ = 0}` as a complex analytic space.

Its underlying set is the union of the two coordinate axes
(`mem_zeroLocus_nodeSection_iff`), which meet at the origin, so the node is singular there and
is not a complex manifold — that last claim is not formalised, and is only the reason this is
the example worth doing. It is a complex analytic space all the same, and its structure sheaf
is coherent (`isCoherentStructureSheaf_node`). -/
def AnalyticSpace.node : AnalyticSpace.{u} :=
  AnalyticSpace.zeroLocus ⊤ nodeSection.{u}

/-- The node is a local model. -/
theorem isLocalModel_node :
    IsLocalModel (nodeAmbient.{u}.zeroLocusSubspace nodeSection.{u}) :=
  isLocalModel_zeroLocus ⊤ nodeSection.{u}

/-- **The structure sheaf of the node is coherent.**

This is the main theorem of the development, `AnalyticSpace.isCoherentStructureSheaf`, applied
to a singular complex analytic space. -/
theorem isCoherentStructureSheaf_node :
    (nodeAmbient.{u}.zeroLocusSubspace nodeSection.{u}).IsCoherentStructureSheaf :=
  AnalyticSpace.isCoherentStructureSheaf_zeroLocus ⊤ nodeSection.{u}

end Node

end ComplexAnalytic

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the mapping property of `IsCutOutBy`, in both categories

`ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` says that a `ℂ`-linear morphism killing the
sections which cut out a subspace factors uniquely through that subspace, as a morphism of
complex analytic spaces. **It would be true and empty if its hypotheses held only at the
identity**, or if the `∃!` were about a hom-set with one element for a reason having nothing to
do with the theorem. This file rules that out at the node.

* `c_app_nodeSection_eq_zero` shows the hypothesis `hφ` is **the node's equation**: the
  pullbacks of the two coordinates multiply to zero (`ComplexAnalytic.nodeCoord_mul`), and that
  is literally what `φ.c.app ⊤ (nodeSection j) = 0` says once `nodePoly` is expanded. So the
  hypothesis is not a technical side condition; it is `z₀ z₁ = 0`.
* `eq_id_of_comp_zeroLocusSubspaceι` runs the theorem where the answer is known: the node's own
  closed immersion factors through the node, and the factorisation has to be the **identity**.
  If it came out as anything else the theorem would be about the wrong morphism.
* `exists_liftHom` records that the factorisation the theorem produces really does compose back
  to `φ`, which is the half of `∃!` that uniqueness cannot supply.
* `existsUnique_axisIncl` runs the theorem where the answer is **not** known. Its `φ` is the map
  `z ↦ (z, 0)` of `ℂ ⟶ ℂ²`, assembled from two global sections of `𝒪_ℂ` by
  `ComplexAnalytic.AnalyticSpace.okaMap`; its source is not the node and it is a factorisation
  of nothing. What comes back is the inclusion of one axis — the first morphism `ℂ ⟶ node` in
  the development. `base_axisIncl` **computes** its base map from the equation it satisfies
  rather than unfolding `lift`, and `not_const_axisIncl` rules out the remaining degeneracy.
  `base_axisIncl_pair` states both coordinates of the image together, so that *"it is the
  inclusion of the first axis"* is one proposition rather than two theorems and a sentence, and
  `exists_axisIncl_pair` closes it over the witness, leaving a statement with **no hypotheses**:
  a morphism `ℂ ⟶ node` whose base map is `z ↦ (z, 0)` exists.
* `exists_ne_id_node` runs the theorem a third time, at the **swap of the two axes**, and gets an
  endomorphism of the node that is not the identity. That is what makes
  `eq_id_of_comp_zeroLocusSubspaceι` and `exists_liftHom` statements about a hom-set with more
  than one element rather than about `{𝟙}`; see the paragraph below.

**What this does not check.** That `existsUnique_liftHom` is applied to a `φ` built from global
sections on a *general* `Z`; that needs the general-`Z` half of taxis #654, which does not
exist. The case `Z = ℂ^n` is available today through `ComplexAnalytic.AnalyticSpace.okaMap` and
is done below.

**`Hom(node, node)` is not a singleton, and until this file said so nothing showed it.**
`eq_id_of_comp_zeroLocusSubspaceι` and `exists_liftHom` would *both* hold if it were: the second
is the first's `∃!` read for existence, and `𝟙` witnesses it through `Category.id_comp`. So
those two are statements about a hom-set that needed exhibiting, and `existsUnique_axisIncl`
does not exhibit it — its source is `ℂ`. The last section of the analytic-space material does:
`exists_ne_id_node`, from the **swap of the two axes**, which is an endomorphism of the node
precisely because `z₀ z₁ = 0` is symmetric.

The last section does the same for the **locally ringed space** form,
`ComplexAnalytic.IsCutOutBy.existsUnique_lift`, and for
`ComplexAnalytic.IsCutOutBy.uniqueIso`. Neither is instantiated by anything above — the
analytic-space theorem is assembled from `lift`, `lift_comp` and `hom_ext` rather than from
`existsUnique_lift`, and `uniqueIso` does not appear there at all — so they are tested
separately.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-- The hypothesis `hφ` of `existsUnique_liftHom`, at the node's own closed immersion, **is the
node's equation** `z₀ z₁ = 0` — reached through `ComplexAnalytic.nodeCoord_mul`, a statement
about the two coordinate *functions* on the node, rather than through
`IsCutOutBy.c_app_eq_zero`, which is the generic reason. -/
theorem c_app_nodeSection_eq_zero (j : Fin 1) :
    (((nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}).c.app (op ⊤)).hom
      (nodeSection.{u} j)) = 0 := by
  refine Eq.trans ?_ nodeCoord_mul.{u}
  refine Eq.trans (congrArg
    ((LocallyRingedSpace.Γ.map (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}).op).hom)
    (show nodeSection.{u} j =
        OkaRing.ofMvPolynomial _ (MvPolynomial.X (ULift.up 0)) *
          OkaRing.ofMvPolynomial _ (MvPolynomial.X (ULift.up 1)) from
      (map_mul (OkaRing.ofMvPolynomial _) _ _))) ?_
  exact map_mul _ _ _

/-- The analytic space the mapping property produces for the node's own cut-out family **is**
the node. Stated separately because it is a `rfl` that the elaborator will not find while it is
also solving for `n`, `k` and `V`. -/
theorem ofCutOut_nodeSection_eq_node :
    AnalyticSpace.ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}) =
      AnalyticSpace.node.{u} :=
  rfl

/-- The mapping property, instantiated at the node: its own closed immersion factors through it.
The `∃!` is recorded here once so that the two consequences below do not each pay for
elaborating it.

`n`, `k`, `V` and `W` are supplied explicitly. Left to unification the elaborator does not
finish inside the default heartbeat budget: it has to solve `?V.isOpenEmbedding` against
`nodeAmbient`'s `⊤.isOpenEmbedding` while simultaneously matching `constantsAlgMap ?n ?V`
against `constantsAlgMap 2 ⊤` in `hlin`. Naming them costs four annotations and takes the
elaboration from a timeout to a second. -/
theorem existsUnique_liftHom_node :
    ∃! ψ : AnalyticSpace.node.{u} ⟶
        AnalyticSpace.ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}),
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} =
        nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} :=
  IsCutOutBy.existsUnique_liftHom (W := AnalyticSpace.node.{u}) (n := 2) (k := 1) (V := ⊤)
    (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u})
    (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u})
    isCLinearHom_zeroLocusSubspaceι_nodeSection.{u} c_app_nodeSection_eq_zero.{u}

/-- **The node's own closed immersion factors through the node, and the factorisation is the
identity.** This is the theorem run where the answer is known independently: a factorisation
that came out as anything else would mean the theorem is about the wrong morphism. -/
theorem eq_id_of_comp_zeroLocusSubspaceι
    (ψ : AnalyticSpace.node.{u} ⟶
      AnalyticSpace.ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}))
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} =
      nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}) :
    ψ = 𝟙 AnalyticSpace.node.{u} :=
  (existsUnique_liftHom_node.{u}.unique hψ (Category.id_comp _))

/-- The existence half, which uniqueness cannot supply: the factorisation composes back to the
morphism it factors. -/
theorem exists_liftHom :
    ∃ ψ : AnalyticSpace.node.{u} ⟶
        AnalyticSpace.ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}),
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} =
        nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} :=
  existsUnique_liftHom_node.{u}.exists

/-! ### A `φ` which is not already a factorisation, and the first morphism `ℂ ⟶ node`

Everything above runs the mapping property where the answer is forced. This section runs it
where it is not: `axisPhi` is the morphism `z ↦ (z, 0)` of `ℂ ⟶ ℂ²`, assembled from two global
sections of `𝒪_ℂ` by `ComplexAnalytic.okaMapHom`, and the morphism `existsUnique_liftHom`
returns for it is the inclusion of one axis of the node.

**The one obstacle, recorded so that nobody rediscovers it.**
`LocallyRingedSpace.Γ.map ((complexAffineSpace 2).restrictTopIso.inv).op` is an `eqToHom`, not a
`rfl`: it is what bridges the two presentations of `ℂ²` that this development uses — the
`complexAffineSpace 2` that `okaMapHom` maps into, and the `nodeAmbient = ℂ²|⊤` that
`IsCutOutBy` and `existsUnique_liftHom` demand. It is not even a `rfl` that fails, because the
two global-section rings are different types. The route below does not compute it at all:
`nodeSection` is rewritten as a pullback along `restrictTopIso.hom`, which *is* a `rfl`
(`nodeSection_eq`), and the pair then collapses.

**Neither half of that crossing lives here any more**, which is what taxis #702 was for. Both
were general statements stated at `n = 2` inside this test file, and both are now general:

* `AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply` collapses the pair, for an
  arbitrary **isomorphism of locally ringed spaces** — `restrictTopIso` never entered its proof,
  which used only `Iso.inv_hom_id`, `Γ_map_comp_apply` and `Γ_map_id_apply`;
* `ComplexAnalytic.isCLinearHom_restrictTopIso_inv` gives the `ℂ`-linearity of the inverse for an
  arbitrary locally ringed space and an arbitrary `ℂ`-algebra structure on its global sections,
  with `ComplexAnalytic.isCLinearHom_restrictTopIso_inv_constants` the `constantsAlgMap`
  spelling that `IsCutOutBy` demands and that this file consumes at `n = 2`.

`nodeSection_eq` stays, because it is the one part of the pattern that really is about the node.
What hides behind it is not a lemma but the observation recorded on `Γ_map_inv_hom_apply`:
`Γ.map X.restrictTopIso.hom.op` is **definitionally the restriction map** `⊤ ⟶ functor.obj ⊤`.

**That is weaker than "the pullback along `restrictTopIso.hom` is always a `rfl`"**, which is
how taxis #702 stated it and which is false: for a section given abstractly the two sides have
different types, `Γ(X, ⊤)` and `Γ(X, functor.obj ⊤)`, and those are not definitionally equal
even for `X = ℂ^n`. What is `rfl` is the pullback of a section whose presentation does not
mention the open it lives on — a polynomial, a constant, a coordinate. Both halves are compiled
beside `nodeSection_eq` below rather than left as prose.
-/

/-- The family `(z, 0)` of two entire functions on `ℂ¹`, which is the morphism `ℂ ⟶ ℂ²` onto
the first coordinate axis. -/
def axisFamily : ULift.{u} (Fin 2) → OkaRing (⊤ : Opens (ULift.{u} (Fin 1) → ℂ)) :=
  fun j ↦ if j = ULift.up 0 then coord (ULift.up 0) else 0

/-- The morphism `z ↦ (z, 0)` of `ℂ ⟶ ℂ²`, landing in the `restrict ⊤` presentation of `ℂ²`
that `IsCutOutBy` uses. -/
def axisPhi : (AnalyticSpace.complexAffineSpace.{u} 1).toLocallyRingedSpace ⟶ nodeAmbient.{u} :=
  okaMapHom axisFamily.{u} ≫ (complexAffineSpace.{u} 2).restrictTopIso.inv

theorem isCLinearHom_axisPhi :
    IsCLinearHom axisPhi.{u}
      (AnalyticSpace.complexAffineSpace.{u} 1).algebraMap (constantsAlgMap 2 ⊤) :=
  (isCLinearHom_okaMapHom axisFamily.{u}).comp (isCLinearHom_restrictTopIso_inv_constants.{u} 2)

/-! **The two `example`s below record the spelling a caller uses**, at a space whose coefficient
field is not `constantsAlgMap` anything.

They do *not* check that `ComplexAnalytic.isCLinearHom_restrictTopIso_inv` is general.
Instantiating a universally quantified variable cannot fail: that lemma takes the coefficient
field as a parameter `α`, so its generality is visible in its statement, and had it secretly
been `constantsAlgMap`-only it would not have compiled at its own declaration. What the
instantiations do establish is that the two spellings a caller reaches for elaborate — the
`X.toLocallyRingedSpace.restrictTopIso` of an `AnalyticSpace`, and
`resAlgMap X.algebraMap ⊤` as the target algebra structure — at an arbitrary space and at the
node, whose coefficient field is pulled back along its closed immersion. That is the real
answer to the question taxis #691 raised about `eval_restrict` and taxis #702 said to *check,
not assume*.

This paragraph replaces one claiming the `example`s checked the generality; the correction is
oka-slot-2's, from the review of PR #72, and was deferred there rather than re-pushed.

They are `example`s deliberately. A named general lemma in a test file is a duplicate waiting to
happen — that is what this file's two `restrictTopIso` declarations were, and removing them is
what taxis #702 was filed for. What is wanted here is evidence that the hypothesis is meetable,
which an anonymous instantiation supplies and a name would outlive. -/

example (X : AnalyticSpace.{u}) :
    IsCLinearHom X.toLocallyRingedSpace.restrictTopIso.inv X.algebraMap
      (X.toLocallyRingedSpace.resAlgMap X.algebraMap ⊤) :=
  isCLinearHom_restrictTopIso_inv _ _

example :
    IsCLinearHom (AnalyticSpace.node.{u}).toLocallyRingedSpace.restrictTopIso.inv
      (AnalyticSpace.node.{u}).algebraMap
      ((AnalyticSpace.node.{u}).toLocallyRingedSpace.resAlgMap
        (AnalyticSpace.node.{u}).algebraMap ⊤) :=
  isCLinearHom_restrictTopIso_inv _ _

/-- `nodeSection` is the pullback of the polynomial `z₀ z₁` along `restrictTopIso.hom`, on the
nose. This is the equation that makes the `eqToHom` above avoidable, and it is the one part of
the crossing that is genuinely about the node: the two general halves are
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply` and
`ComplexAnalytic.isCLinearHom_restrictTopIso_inv`. -/
theorem nodeSection_eq (j : Fin 1) :
    nodeSection.{u} j =
      (LocallyRingedSpace.Γ.map ((complexAffineSpace.{u} 2).restrictTopIso.hom).op).hom
          (OkaRing.ofMvPolynomial ⊤ nodePoly.{u}) :=
  rfl

/-! The two claims the paragraph above makes about *why* `nodeSection_eq` is a `rfl`, compiled.

The first is the reason: pulling back along `restrictTopIso.hom` **is** restricting, for every
locally ringed space and every section, definitionally. The second is what that buys — the
generalisation of `nodeSection_eq` itself, for every `n` and every polynomial, of which
`nodeSection_eq` is the case `n = 2`, `P = nodePoly`.

The claim these do **not** support is the one taxis #702 made and this file used to imply: that
the pullback is a `rfl` for an arbitrary section. It is not, and it is not even well-typed —
`(Γ.map X.restrictTopIso.hom.op).hom a = a` is rejected with a type mismatch between
`Γ(X, ⊤)` and `Γ(X, functor.obj ⊤)`, for a general `X` and also for `X = ℂ^n`. -/

example (X : LocallyRingedSpace.{u}) (a : X.presheaf.obj (op ⊤)) :
    (LocallyRingedSpace.Γ.map X.restrictTopIso.hom.op).hom a =
      (X.presheaf.map (homOfLE le_top).op).hom a :=
  rfl

example (n : ℕ) (P : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (LocallyRingedSpace.Γ.map (complexAffineSpace.{u} n).restrictTopIso.hom.op).hom
        (OkaRing.ofMvPolynomial ⊤ P) =
      OkaRing.ofMvPolynomial _ P :=
  rfl

/-- **The morphism `z ↦ (z, 0)` of `ℂ ⟶ ℂ²` kills the node's equation `z₀ z₁`**, so it satisfies
the hypothesis `hφ` of the mapping property. The second coordinate of the family is `0`, and
that is the whole content. -/
theorem c_app_axisPhi_nodeSection (j : Fin 1) :
    ((axisPhi.{u}).c.app (op ⊤)).hom (nodeSection.{u} j) = 0 :=
  (congrArg ((LocallyRingedSpace.Γ.map (axisPhi.{u}).op).hom) (nodeSection_eq.{u} j)).trans
    ((LocallyRingedSpace.Γ_map_comp_apply (okaMapHom axisFamily.{u})
        ((complexAffineSpace.{u} 2).restrictTopIso.inv) _).trans
      ((congrArg ((LocallyRingedSpace.Γ.map (okaMapHom axisFamily.{u}).op).hom)
          ((LocallyRingedSpace.Γ_map_inv_hom_apply
                (complexAffineSpace.{u} 2).restrictTopIso _).trans
            (map_mul (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)))
              (MvPolynomial.X (ULift.up 0)) (MvPolynomial.X (ULift.up 1))))).trans
        ((map_mul ((LocallyRingedSpace.Γ.map (okaMapHom axisFamily.{u}).op).hom)
            (coord (ULift.up 0)) (coord (ULift.up 1))).trans
          ((congrArg₂ (· * ·) (Γ_map_okaMapHom_coord axisFamily.{u} (ULift.up 0))
              (Γ_map_okaMapHom_coord axisFamily.{u} (ULift.up 1))).trans
            ((congrArg (axisFamily.{u} (ULift.up 0) * ·)
                (show axisFamily.{u} (ULift.up 1) = 0 from if_neg (by simp))).trans
              (mul_zero _))))))

/-- **The mapping property applied to a `φ` which is not already a factorisation.** `axisPhi` is
built from two global sections of `𝒪_ℂ` by `ComplexAnalytic.okaMapHom`, its source is `ℂ` rather
than the node, and it factors nothing. The target elaborates as `AnalyticSpace.node` itself,
which is `ofCutOut_nodeSection_eq_node` used rather than stated. -/
theorem existsUnique_axisIncl :
    ∃! ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u},
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u} :=
  IsCutOutBy.existsUnique_liftHom (W := AnalyticSpace.complexAffineSpace.{u} 1)
    (n := 2) (k := 1) (V := ⊤)
    (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}) axisPhi.{u}
    isCLinearHom_axisPhi.{u} c_app_axisPhi_nodeSection.{u}

/-- **Where the factorisation sends a point, recovered from the equation it satisfies.** This is
the load-bearing check of the section: it does not unfold `lift`, it reads the base map off
`hψ`, so an error anywhere in the mapping property's construction would show up here. -/
theorem base_axisIncl (ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u})
    (z : ULift.{u} (Fin 1) → ℂ) (l : ULift.{u} (Fin 2)) :
    ((ψ.toLRSHom.base z).1.1 l) = okaMapFun axisFamily.{u} z l :=
  congrArg
    (fun m : (AnalyticSpace.complexAffineSpace.{u} 1).toLocallyRingedSpace ⟶ nodeAmbient.{u} ↦
      ((m.base z : nodeAmbient.{u}).1 l)) hψ

/-- The first coordinate of the axis map is `z`. -/
theorem okaMapFun_axisFamily_zero (z : ULift.{u} (Fin 1) → ℂ) :
    okaMapFun axisFamily.{u} z (ULift.up 0) = z (ULift.up 0) :=
  (okaMapFun_apply axisFamily.{u} z (ULift.up 0)).trans
    ((congrArg (OkaRing.evalHom (U := ⊤) (x := z) trivial)
      (show axisFamily.{u} (ULift.up 0) = coord (ULift.up 0) from if_pos rfl)).trans
        (evalHom_coord (ULift.up 0)))

/-- The second coordinate of the axis map is `0`, which is why its image lies on the node. -/
theorem okaMapFun_axisFamily_one (z : ULift.{u} (Fin 1) → ℂ) :
    okaMapFun axisFamily.{u} z (ULift.up 1) = 0 :=
  (okaMapFun_apply axisFamily.{u} z (ULift.up 1)).trans
    ((congrArg (OkaRing.evalHom (U := ⊤) (x := z) trivial)
      (show axisFamily.{u} (ULift.up 1) = 0 from if_neg (by simp))).trans (map_zero _))

/-- **The morphism the mapping property produced is not constant**: `0` and `1` go to two
different points of the node. With `base_axisIncl` this identifies it as the inclusion of the
first axis. -/
theorem not_const_axisIncl (ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u}) :
    ψ.toLRSHom.base (fun _ ↦ (0 : ℂ)) ≠ ψ.toLRSHom.base (fun _ ↦ (1 : ℂ)) := by
  intro hcon
  have h0 := (base_axisIncl ψ hψ (fun _ ↦ (0 : ℂ)) (ULift.up 0)).symm.trans
    (congrArg (fun p : AnalyticSpace.node.{u} ↦ p.1.1 (ULift.up 0)) hcon)
  rw [base_axisIncl ψ hψ (fun _ ↦ (1 : ℂ)) (ULift.up 0), okaMapFun_axisFamily_zero,
    okaMapFun_axisFamily_zero] at h0
  exact zero_ne_one h0

/-- **A non-constant morphism of complex analytic spaces `ℂ ⟶ node` exists**, and it is the one
the mapping property produced.

`not_const_axisIncl` is a statement about an arbitrary `ψ` satisfying `hψ`, so on its own it
could be about nothing. This is the `⟨_, proof₁, proof₂⟩` shape: one existential whose witness is
fixed by the first component and consumed by the second, so the factorisation equation and the
non-constancy are provably about the same morphism. -/
theorem exists_nonconstant_hom_complexLine_node :
    ∃ ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u},
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u} ∧
        ψ.toLRSHom.base (fun _ ↦ (0 : ℂ)) ≠ ψ.toLRSHom.base (fun _ ↦ (1 : ℂ)) :=
  ⟨_, existsUnique_axisIncl.{u}.exists.choose_spec,
    not_const_axisIncl _ existsUnique_axisIncl.{u}.exists.choose_spec⟩

/-- **Both coordinates of the image, named together: `z ↦ (z, 0)`.**

`base_axisIncl` is symbolic in `okaMapFun axisFamily`, and the two coordinate computations are
separate theorems, so nothing until now states the sentence *"the factorisation is the inclusion
of the first axis"* as one proposition. This does. -/
theorem base_axisIncl_pair
    (ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = axisPhi.{u})
    (z : ULift.{u} (Fin 1) → ℂ) :
    (ψ.toLRSHom.base z).1.1 (ULift.up 0) = z (ULift.up 0) ∧
      (ψ.toLRSHom.base z).1.1 (ULift.up 1) = 0 :=
  ⟨(base_axisIncl ψ hψ z (ULift.up 0)).trans (okaMapFun_axisFamily_zero z),
    (base_axisIncl ψ hψ z (ULift.up 1)).trans (okaMapFun_axisFamily_one z)⟩

/-- **A morphism of complex analytic spaces `ℂ ⟶ node` whose base map is `z ↦ (z, 0)` exists.**

This is the sentence this section has been circling: `base_axisIncl_pair` is conditional on a `ψ`
that nothing in its statement supplies, and `existsUnique_axisIncl` supplies one without saying
where it sends a point. The `⟨_, proof⟩` shape joins them — the witness is fixed by
`existsUnique_axisIncl.exists.choose` and consumed by `base_axisIncl_pair`, so the two are
provably about the same morphism — and the result has **no hypotheses at all**.

That the image lies on the node follows in one step (`mul_zero` on the second component), from a
statement that cannot decay: a separate theorem saying only that would have an unused hypothesis
and a one-line proof from the type of `ψ`, so its content would be *which* proof elaborates and
nothing would protect it. -/
theorem exists_axisIncl_pair :
    ∃ ψ : AnalyticSpace.complexAffineSpace.{u} 1 ⟶ AnalyticSpace.node.{u},
      ∀ z : ULift.{u} (Fin 1) → ℂ,
        (ψ.toLRSHom.base z).1.1 (ULift.up 0) = z (ULift.up 0) ∧
          (ψ.toLRSHom.base z).1.1 (ULift.up 1) = 0 :=
  ⟨_, fun z ↦ base_axisIncl_pair _ existsUnique_axisIncl.{u}.exists.choose_spec z⟩

/-! ### A second endomorphism of the node: the swap of the two axes

Everything above leaves `Hom(node, node)` possibly a singleton, and two of the statements above
would be true if it were. This section rules that out, by the one morphism the node's equation
makes obvious: `z₀ z₁ = 0` is symmetric, so `p ↦ (p₁, p₀)` maps the node to itself.

`ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` supplies the factorisation, and the
`restrictTopIso` crossing — now the two general lemmas named in the section above, rather than
anything built here — supplies the bridge from `okaMapHom`'s target `ℂ²` to `IsCutOutBy`'s
`ℂ²|⊤`. The same three seams apply here as there and are not repeated:
`rw` will not fire across the `Γ.map` of a composite, `rw [coordPullback_nodeIncl]` will not fire
on a goal spelled with `Γ.map`, and `(𝟙 X).toLRSHom` needs the ascription `(𝟙 X : X ⟶ X)`.
-/

/-- The family `(z₁, z₀)` on `ℂ²`: the swap of the two coordinates. -/
def swapFamily : ULift.{u} (Fin 2) → OkaRing (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)) :=
  fun j ↦ if j = ULift.up 0 then coord (ULift.up 1) else coord (ULift.up 0)

/-- The morphism `p ↦ (p₁, p₀)` of `node ⟶ ℂ²`, landing in the `restrict ⊤` presentation of
`ℂ²` that `IsCutOutBy` uses. -/
def swapPhi : (AnalyticSpace.node.{u}).toLocallyRingedSpace ⟶ nodeAmbient.{u} :=
  nodeIncl.{u}.toLRSHom ≫ okaMapHom swapFamily.{u} ≫
    (complexAffineSpace.{u} 2).restrictTopIso.inv

theorem isCLinearHom_swapPhi :
    IsCLinearHom swapPhi.{u} (AnalyticSpace.node.{u}).algebraMap (constantsAlgMap 2 ⊤) :=
  nodeIncl.{u}.isCLinear.comp
    ((isCLinearHom_okaMapHom swapFamily.{u}).comp (isCLinearHom_restrictTopIso_inv_constants.{u} 2))

/-- **The swap kills the node's equation**, because `z₁ z₀ = z₀ z₁` and the node satisfies the
latter. This is where the symmetry of `nodePoly` is used and it is the whole reason the swap is
an endomorphism rather than merely a morphism to `ℂ²`. -/
theorem c_app_swapPhi_nodeSection (j : Fin 1) :
    ((swapPhi.{u}).c.app (op ⊤)).hom (nodeSection.{u} j) = 0 := by
  have h1 : (LocallyRingedSpace.Γ.map ((okaMapHom swapFamily.{u} ≫
        (complexAffineSpace.{u} 2).restrictTopIso.inv)).op).hom (nodeSection.{u} j) =
      swapFamily.{u} (ULift.up 0) * swapFamily.{u} (ULift.up 1) :=
    (congrArg ((LocallyRingedSpace.Γ.map (okaMapHom swapFamily.{u} ≫
        (complexAffineSpace.{u} 2).restrictTopIso.inv).op).hom) (nodeSection_eq.{u} j)).trans
      ((LocallyRingedSpace.Γ_map_comp_apply (okaMapHom swapFamily.{u})
          ((complexAffineSpace.{u} 2).restrictTopIso.inv) _).trans
        ((congrArg ((LocallyRingedSpace.Γ.map (okaMapHom swapFamily.{u}).op).hom)
            ((LocallyRingedSpace.Γ_map_inv_hom_apply
                (complexAffineSpace.{u} 2).restrictTopIso _).trans
              (map_mul (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin 2) → ℂ)))
                (MvPolynomial.X (ULift.up 0)) (MvPolynomial.X (ULift.up 1))))).trans
          ((map_mul ((LocallyRingedSpace.Γ.map (okaMapHom swapFamily.{u}).op).hom)
              (coord (ULift.up 0)) (coord (ULift.up 1))).trans
            (congrArg₂ (· * ·) (Γ_map_okaMapHom_coord swapFamily.{u} (ULift.up 0))
              (Γ_map_okaMapHom_coord swapFamily.{u} (ULift.up 1))))))
  have e0 : swapFamily.{u} (ULift.up 0) = coord (ULift.up 1) := if_pos rfl
  have e1 : swapFamily.{u} (ULift.up 1) = coord (ULift.up 0) :=
    if_neg (fun h : (ULift.up 1 : ULift.{u} (Fin 2)) = ULift.up 0 ↦ by
      simpa using congrArg ULift.down h)
  refine Eq.trans (LocallyRingedSpace.Γ_map_comp_apply nodeIncl.{u}.toLRSHom
    (okaMapHom swapFamily.{u} ≫ (complexAffineSpace.{u} 2).restrictTopIso.inv)
    (nodeSection.{u} j)) ?_
  refine Eq.trans (congrArg ((LocallyRingedSpace.Γ.map nodeIncl.{u}.toLRSHom.op).hom)
    (h1.trans (congrArg₂ (· * ·) e0 e1))) ?_
  exact ((map_mul ((LocallyRingedSpace.Γ.map nodeIncl.{u}.toLRSHom.op).hom) _ _).trans
    ((congrArg₂ (· * ·) (coordPullback_nodeIncl.{u} (ULift.up 1))
      (coordPullback_nodeIncl.{u} (ULift.up 0))).trans (mul_comm _ _))).trans nodeCoord_mul.{u}

/-- **The swap factors through the node**, so it is an endomorphism of it. -/
theorem existsUnique_nodeSwap :
    ∃! ψ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.node.{u},
      ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = swapPhi.{u} :=
  IsCutOutBy.existsUnique_liftHom (W := AnalyticSpace.node.{u}) (n := 2) (k := 1) (V := ⊤)
    (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}) swapPhi.{u}
    isCLinearHom_swapPhi.{u} c_app_swapPhi_nodeSection.{u}

/-- Where the swap sends a point, read off the equation it satisfies rather than by unfolding
`lift` — the same one-`congrArg` shape as `base_axisIncl`. -/
theorem base_nodeSwap (ψ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = swapPhi.{u})
    (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 2)) :
    ((ψ.toLRSHom.base p).1.1 j) =
      okaMapFun swapFamily.{u} (nodeIncl.{u}.toLRSHom.base p) j :=
  congrArg (fun m : (AnalyticSpace.node.{u}).toLocallyRingedSpace ⟶ nodeAmbient.{u} ↦
    ((m.base p : nodeAmbient.{u}).1 j)) hψ

/-- The first coordinate of the swap is the second coordinate of the point. -/
theorem okaMapFun_swapFamily_zero (z : ULift.{u} (Fin 2) → ℂ) :
    okaMapFun swapFamily.{u} z (ULift.up 0) = z (ULift.up 1) :=
  (okaMapFun_apply swapFamily.{u} z (ULift.up 0)).trans
    ((congrArg (OkaRing.evalHom (U := ⊤) (x := z) trivial)
      (show swapFamily.{u} (ULift.up 0) = coord (ULift.up 1) from if_pos rfl)).trans
        (evalHom_coord (ULift.up 1)))

/-- **The swap is not the identity.**

The test point is `(1, 0)`, and it is obtained from `exists_axisIncl_pair` above rather than
constructed: the axis inclusion sends `1` to it, so its coordinates are known without proving
membership of the node by hand. That also gives `exists_axisIncl_pair` a consumer.

The swap sends it to `(0, 1)`, whose first coordinate is `0`; the identity leaves it, and its
first coordinate is `1`. -/
theorem ne_id_nodeSwap (ψ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.node.{u})
    (hψ : ψ.toLRSHom ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = swapPhi.{u}) :
    ψ ≠ 𝟙 AnalyticSpace.node.{u} := by
  intro hcon
  subst hcon
  obtain ⟨χ, hχ⟩ := exists_axisIncl_pair.{u}
  set p := χ.toLRSHom.base (fun _ ↦ (1 : ℂ)) with hp
  have hp0 : p.1.1 (ULift.up 0) = 1 := (hχ (fun _ ↦ (1 : ℂ))).1
  have hp1 : p.1.1 (ULift.up 1) = 0 := (hχ (fun _ ↦ (1 : ℂ))).2
  have h := base_nodeSwap _ hψ p (ULift.up 0)
  rw [okaMapFun_swapFamily_zero, base_nodeIncl, hp1] at h
  have hbase : (((𝟙 AnalyticSpace.node.{u} :
        AnalyticSpace.node.{u} ⟶ AnalyticSpace.node.{u})).toLRSHom.base p).1.1 (ULift.up 0) =
      p.1.1 (ULift.up 0) := rfl
  rw [hbase, hp0] at h
  exact one_ne_zero h

/-- **`Hom(node, node)` has more than one element.**

This is what `eq_id_of_comp_zeroLocusSubspaceι` and `exists_liftHom` above are statements about,
and until now nothing showed the hom-set was not `{𝟙}` — in which case both would have been
true and empty. The `⟨_, proof⟩` shape fixes the witness by `existsUnique_nodeSwap` and consumes
it by `ne_id_nodeSwap`, so the two are provably about the same morphism. -/
theorem exists_ne_id_node :
    ∃ ψ : AnalyticSpace.node.{u} ⟶ AnalyticSpace.node.{u}, ψ ≠ 𝟙 AnalyticSpace.node.{u} :=
  ⟨existsUnique_nodeSwap.{u}.exists.choose,
    ne_id_nodeSwap _ existsUnique_nodeSwap.{u}.exists.choose_spec⟩

/-! ### The locally ringed space form, which is a different statement

`ComplexAnalytic.IsCutOutBy.existsUnique_lift` and `ComplexAnalytic.IsCutOutBy.uniqueIso` are
still theorems of `Oka/AnalyticSpace/Factorisation.lean`, one category lower, and nothing above
instantiates either of them: `existsUnique_liftHom` is built from `lift`, `lift_comp` and
`hom_ext`, not from `existsUnique_lift`, and `uniqueIso` is not mentioned there at all. So they
need non-vacuity of their own, and it is here.
-/

variable {X Y : LocallyRingedSpace.{u}} {i : X ⟶ Y} {k : ℕ}
  {f : Fin k → Y.presheaf.obj (op ⊤)}

/-- **The factorisation of `i` through itself is the identity.** The construction is not merely
*some* morphism with the right source and target: on the one instance where the answer is
forced, it gives the right answer.

This is `eq_id_of_comp_zeroLocusSubspaceι` above with the node replaced by an arbitrary cut-out,
and neither implies the other: the analytic-space version fixes the space, and it pins the
*hypothetical* factorisation rather than the constructed one. -/
theorem lift_self (hcut : IsCutOutBy i f) : hcut.lift i hcut.c_app_eq_zero = 𝟙 X :=
  hcut.hom_ext _ _ (by rw [hcut.lift_comp, Category.id_comp])

/-- The mapping property at the node `{z ∈ ℂ² | z₀ z₁ = 0}`, a complex analytic space which is
not a manifold: a morphism of *locally ringed spaces* into `ℂ²` killing `z₀ z₁` factors uniquely
through the node. This is the one place `existsUnique_lift` itself is instantiated. -/
example (Z : LocallyRingedSpace.{u}) (φ : Z ⟶ nodeAmbient.{u})
    (hφ : ∀ j, φ.c.app (op ⊤) (nodeSection.{u} j) = 0) :
    ∃! ψ : Z ⟶ nodeAmbient.{u}.zeroLocusSubspace nodeSection.{u},
      ψ ≫ nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u} = φ :=
  (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}).existsUnique_lift φ hφ

/-- **Two presentations of the same subspace are canonically isomorphic**, and the isomorphism
is over `Y`. Instantiated at a genuinely different pair: `X'` here is any space isomorphic to
`X`, cut out by the same sections through the transported immersion
(`ComplexAnalytic.IsCutOutBy.comp_iso`). -/
example {X' : LocallyRingedSpace.{u}} (hcut : IsCutOutBy i f) (e : X' ≅ X) :
    (hcut.uniqueIso (hcut.comp_iso e)).hom ≫ (e.hom ≫ i) = i :=
  hcut.uniqueIso_hom_comp (hcut.comp_iso e)

/-- The other half, which never had an instantiation: the inverse of that isomorphism is over
`Y` too. Together with the previous example this says `uniqueIso` is an isomorphism **in the
slice over `Y`**, which is the content of "canonically". -/
example {X' : LocallyRingedSpace.{u}} (hcut : IsCutOutBy i f) (e : X' ≅ X) :
    (hcut.uniqueIso (hcut.comp_iso e)).inv ≫ i = e.hom ≫ i :=
  hcut.uniqueIso_inv_comp (hcut.comp_iso e)

end

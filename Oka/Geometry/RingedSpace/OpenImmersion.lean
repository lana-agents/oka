/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Oka.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Two open immersions with the same image have isomorphic sources

Material for `Mathlib/Geometry/RingedSpace/OpenImmersion.lean`; see `README.md` on the mirror
tree.

Mathlib has this construction twice — as
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq` and as
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` for schemes — but **not** for locally ringed
spaces, even though the two ingredients it is built from,
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` and its uniqueness, are there. The
definition below is the scheme one transcribed.

It is what identifies two presentations of the same open subspace: `X|S|T` and `X|S'|T'` are
isomorphic as soon as they have the same image in `X`, which is how a chart of an open subspace
of a complex analytic space is compared with a chart of the ambient space
(`Oka/AnalyticSpace/OpenSubspace.lean`).

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`: two open immersions with
  the same image have isomorphic sources.
- `AlgebraicGeometry.LocallyRingedSpace.liftRestrict`: **a morphism whose image lies in an open
  subset factors through that open subspace** — the universal property of `X|V` as a target,
  which Mathlib has only in the form `IsOpenImmersion.lift` against an arbitrary open immersion.
- `AlgebraicGeometry.LocallyRingedSpace.restrictLE`: the inclusion of a smaller open subspace
  into a larger one, which is `liftRestrict` of `ofRestrict`. Mathlib has `ofRestrict` for the
  inclusion into `X` itself and nothing for one open subspace inside another, although
  `IsOpenImmersion.lift` — which is what this is — is there. Both live in this file rather than
  beside `ofRestrict` because `lift` does.
- `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict`: **the inclusion of an open
  subspace is an open immersion, with the open as an ordinary argument.** Mathlib has the
  instance; what this adds is a spelling at which it can be *used* from an analytic space, as
  `liftRestrict` does for a different seam. Its docstring records the measurement.
- `AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback`: **the subspace on an
  intersection is the pullback of the two open subspaces**, `X|(U ⊓ V) ≅ X|U ×_X X|V`, over `X`.
  It is `isoOfRangeEq` at `range_pullback_to_base_of_left`, and it is what turns a hypothesis
  about an opaque categorical pullback into one about an open subspace.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac`: the isomorphism
  commutes with the two immersions. This, rather than the isomorphism itself, is what every use
  of it consumes.
- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_to_base_of_left`: **the
  image of the pullback of two open immersions is the intersection of their images.** Mathlib
  has this for schemes (`Mathlib/AlgebraicGeometry/OpenImmersion.lean`) and for nothing else;
  the proofs below are those transcribed, with `LocallyRingedSpace.forgetToTop` in place of
  `Scheme.forgetToTop`. Together with `isoOfRangeEq` it is what identifies the pullback of two
  open subspace inclusions with the subspace on their intersection.
- `AlgebraicGeometry.LocallyRingedSpace.liftRestrict_fac` and
  `AlgebraicGeometry.LocallyRingedSpace.hom_ext_restrict`: the factorisation through an open
  subspace is one, and is unique. A morphism *into* `X|V` is determined by its composite with
  `ofRestrict`, since an open immersion is a monomorphism.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- **Two open immersions with the same image have isomorphic sources.** -/
noncomputable def isoOfRangeEq (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]
lemma isoOfRangeEq_hom_fac (e : Set.range f.base = Set.range g.base) :
    (isoOfRangeEq f g e).hom ≫ g = f :=
  lift_fac g f (le_of_eq e)

@[reassoc (attr := simp)]
lemma isoOfRangeEq_inv_fac (e : Set.range f.base = Set.range g.base) :
    (isoOfRangeEq f g e).inv ≫ f = g :=
  lift_fac f g (le_of_eq e.symm)

section Pullback

variable {W : LocallyRingedSpace.{u}} (h : W ⟶ Z)

/-- `LocallyRingedSpace.forgetToTop` preserves the pullback of an open immersion.

Mathlib proves this for the composite `forgetToSheafedSpace ⋙ SheafedSpace.forget _`, which
`forgetToTop` is *defined* to be; instance resolution does not unfold the definition, so the
statement in the spelling everything else uses has to be made. -/
instance preservesPullback_forgetToTop :
    PreservesLimit (cospan f h) LocallyRingedSpace.forgetToTop := by
  delta LocallyRingedSpace.forgetToTop
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- **The image of the second projection of a pullback along an open immersion is the preimage
of the image.** Transcribed from `AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd`. -/
theorem range_pullbackSnd :
    Set.range (pullback.snd f h).base = h.base ⁻¹' (Set.range f.base) := by
  rw [← show _ = (pullback.snd f h).base from
    PreservesPullback.iso_hom_snd LocallyRingedSpace.forgetToTop f h, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr,
    ← @Set.preimage_univ _ _ (pullback.fst f.base h.base)]
  · erw [TopCat.pullback_snd_image_fst_preimage]
    rw [Set.image_univ]
    rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance

/-- **The image of the pullback of two open immersions is the intersection of their images.**

This is the fact that makes the pullback of two open subspace inclusions identifiable: with
`isoOfRangeEq` it says the pullback of `X|U ⟶ X` and `X|V ⟶ X` is `X|(U ⊓ V)`. -/
theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst f h ≫ f).base = Set.range f.base ∩ Set.range h.base := by
  rw [pullback.condition, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullbackSnd, Set.image_preimage_eq_inter_range]

end Pullback

end AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

namespace AlgebraicGeometry.LocallyRingedSpace

section LiftRestrict

variable {Z X : LocallyRingedSpace.{u}} (φ : Z ⟶ X) (V : TopologicalSpace.Opens X)
  (h : Set.range φ.base ⊆ (V : Set X))

/-- **A morphism whose image lies in an open subset factors through that open subspace.**

This is the universal property of `X|V` as an object *mapped into*, the half that
`LocallyRingedSpace.ofRestrict` on its own does not provide: `ofRestrict` says `X|V` maps to `X`,
and this says everything landing in `V` maps to `X|V`.

It is `IsOpenImmersion.lift` at `f = ofRestrict`, with `range_ofRestrict` turning the hypothesis
into the containment of images that `lift` wants.

**Stating it is worth a name because the call site it exists for meets the seam twice.** An open
of the carrier of a complex analytic space produces `TopologicalSpace.Opens.inclusion' V` at
`… ⟶ ↑X.toPresheafedSpace` rather than at `… ⟶ X.toTopCat`. The two are definitionally equal,
and **which of the two failures one meets is decided by the expected type**, not by how `V` is
spelled:

* against `Z ⟶ (X.restrict U).toLocallyRingedSpace`, which is the expected type of the
  underlying-morphism component of `ComplexAnalytic.AnalyticSpace.liftOpen` — that morphism's own
  type is `Z ⟶ X.restrict U`, and `restrict` there is the *analytic* one —
  `IsOpenImmersion.lift` reports `failed to synthesize instance of type class
  LocallyRingedSpace.IsOpenImmersion (X.ofRestrict ⋯)`;
* against `Z ⟶ X.toLocallyRingedSpace.restrict V.isOpenEmbedding`, or with no expected type at
  all, the instance **is** found — `OkaTest/Nonvanishing.lean` records that as a test rather than
  as a recollection — and the `rw [range_ofRestrict]` fails instead, reporting *"did not find an
  occurrence of the pattern"* with the note that the target is not type-correct under the
  `instances` transparency level; the mismatch appears only in the `Full error:` block.

Here `V` is an ordinary argument at the locally-ringed-space spelling, both sides cross at
default transparency, the rewrite is performed once, and callers meet neither failure. -/
noncomputable def liftRestrict : Z ⟶ X.restrict V.isOpenEmbedding :=
  IsOpenImmersion.lift (X.ofRestrict V.isOpenEmbedding) φ (by rw [range_ofRestrict]; exact h)

/-- **`liftRestrict` is a factorisation of `φ`.** This, rather than the morphism itself, is what
every use of it consumes. -/
@[reassoc (attr := simp)]
lemma liftRestrict_fac : liftRestrict φ V h ≫ X.ofRestrict V.isOpenEmbedding = φ :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The factorisation through an open subspace is unique.** -/
lemma liftRestrict_uniq (l : Z ⟶ X.restrict V.isOpenEmbedding)
    (hl : l ≫ X.ofRestrict V.isOpenEmbedding = φ) : l = liftRestrict φ V h :=
  IsOpenImmersion.lift_uniq _ _ _ _ hl

/-- **The point of `X|V` underneath a point of `Z` is the image point of `φ`.** -/
@[simp]
lemma base_ofRestrict_base_liftRestrict (z : Z) :
    (X.ofRestrict V.isOpenEmbedding).base ((liftRestrict φ V h).base z) = φ.base z :=
  congrArg (fun m : Z ⟶ X ↦ m.base z) (liftRestrict_fac φ V h)

/-- **Two morphisms into an open subspace agreeing after inclusion are equal**, because an open
immersion is a monomorphism. Stated separately from `liftRestrict_uniq` because the usual
situation is two morphisms and no third one they are both factorisations of. -/
lemma hom_ext_restrict (l₁ l₂ : Z ⟶ X.restrict V.isOpenEmbedding)
    (h : l₁ ≫ X.ofRestrict V.isOpenEmbedding = l₂ ≫ X.ofRestrict V.isOpenEmbedding) :
    l₁ = l₂ := by
  rw [← cancel_mono (X.ofRestrict V.isOpenEmbedding)]
  exact h

/-- **The inclusion of an open subspace is an open immersion**, with the open passed as an
ordinary argument.

This restates an instance Mathlib already has, and it is **not** redundant. What defeats instance
search at the call site is the **head symbol**, and not the open: for a complex analytic space `X`
and `U : X.Opens` the morphism a caller holds is `ComplexAnalytic.AnalyticSpace.ofRestrict`, whose
underlying morphism is headed by `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom`, where Mathlib's
instance is headed by `AlgebraicGeometry.LocallyRingedSpace.ofRestrict`. The two terms are
`rfl`-equal and they are **different discrimination-tree keys**, so the instance is never tried.

Measured at `master` = `e252f7a`, with `g` and `f` as in
`Oka/Analytification/DistinguishedOpen.lean`:

* `example : LocallyRingedSpace.IsOpenImmersion ((AnalyticSpace.analytification g).ofRestrict
  (localisationOpen g f)).toLRSHom := by infer_instance` **fails**, reporting `failed to
  synthesize instance of type class LocallyRingedSpace.IsOpenImmersion (AnalyticSpace.Hom.toLRSHom
  ((AnalyticSpace.analytification g).ofRestrict (localisationOpen g f)))`;
* the same goal spelled `((AnalyticSpace.analytification g).toLocallyRingedSpace.ofRestrict
  (localisationOpen g f).isOpenEmbedding)` **succeeds** by `infer_instance`, and so does the
  abstract form for an arbitrary analytic `X` and `U : X.Opens`. So the analytic `Opens` is not
  the obstruction — search reaches Mathlib's instance through it perfectly well.

So the way to use this lemma is to state the instance as an ascribed `haveI` **at the spelling the
goal uses** and close it with this: the term crosses the seam even though the search does not.
`ComplexAnalytic.isOpenImmersion_localisationProj` is the call site it exists for.

The remedy is the one `AlgebraicGeometry.LocallyRingedSpace.liftRestrict` above uses — for a
different seam, so do not read the two docstrings as one diagnosis: **wrap the Mathlib fact one
level down and pass the open as an ordinary argument, rather than repairing the instance graph.**
No new global instance, no `inferInstanceAs`, no extra discrimination-tree key. -/
theorem isOpenImmersion_ofRestrict (X : LocallyRingedSpace.{u})
    (V : TopologicalSpace.Opens X) : IsOpenImmersion (X.ofRestrict V.isOpenEmbedding) :=
  inferInstance

end LiftRestrict

/-- **The inclusion of a smaller open subspace into a larger one.**

`liftRestrict` gives it: the inclusion of `V` into `X` lands in `W`, so it factors through the
inclusion of `W`. What makes it usable is `restrictLE_fac` below, which is the only property of
it that anything consumes. -/
noncomputable def restrictLE (X : LocallyRingedSpace.{u}) {V W : TopologicalSpace.Opens X}
    (h : V ≤ W) : X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding :=
  liftRestrict (X.ofRestrict V.isOpenEmbedding) W (by rw [range_ofRestrict]; exact h)

/-- **`restrictLE` is a morphism over `X`**: including a smaller open subspace into a larger one
and then into `X` is including it into `X`. -/
@[reassoc (attr := simp)]
theorem restrictLE_fac (X : LocallyRingedSpace.{u}) {V W : TopologicalSpace.Opens X}
    (h : V ≤ W) :
    X.restrictLE h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding :=
  liftRestrict_fac _ _ _

section RestrictInf

variable (X : LocallyRingedSpace.{u}) (U V : TopologicalSpace.Opens X)

/-- **The two inclusions of `X|(U ⊓ V)` agree over `X`**, which is the cone the isomorphism
below is the comparison of. -/
theorem restrictLE_inf_condition :
    X.restrictLE (inf_le_left : U ⊓ V ≤ U) ≫ X.ofRestrict U.isOpenEmbedding =
      X.restrictLE (inf_le_right : U ⊓ V ≤ V) ≫ X.ofRestrict V.isOpenEmbedding := by
  rw [restrictLE_fac, restrictLE_fac]

/-- **The comparison morphism `X|(U ⊓ V) ⟶ X|U ×_X X|V` is an isomorphism.**

It is `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` between two open immersions
with the same image: the image of `pullback.fst ≫ ofRestrict U` is `↑U ∩ ↑V` by
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_to_base_of_left`, and that
is the image of `ofRestrict (U ⊓ V)` by `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`;
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq` identifies the comparison with
`isoOfRangeEq`'s. Stated apart from `restrictInfIsoPullback` so that the isomorphism can be
`asIso` of a term rather than the output of a tactic block, which is what makes its `hom` reduce
to the comparison by `rfl`. -/
theorem isIso_pullbackLift_restrictLE :
    IsIso (pullback.lift (X.restrictLE (inf_le_left : U ⊓ V ≤ U))
      (X.restrictLE (inf_le_right : U ⊓ V ≤ V)) (X.restrictLE_inf_condition U V)) := by
  have hrange : Set.range (X.ofRestrict (U ⊓ V).isOpenEmbedding).base =
      Set.range (pullback.fst (X.ofRestrict U.isOpenEmbedding)
        (X.ofRestrict V.isOpenEmbedding) ≫ X.ofRestrict U.isOpenEmbedding).base := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, range_ofRestrict, range_ofRestrict,
      range_ofRestrict]
    rfl
  rw [show pullback.lift (X.restrictLE (inf_le_left : U ⊓ V ≤ U))
        (X.restrictLE (inf_le_right : U ⊓ V ≤ V)) (X.restrictLE_inf_condition U V) =
      (IsOpenImmersion.isoOfRangeEq (X.ofRestrict (U ⊓ V).isOpenEmbedding)
        (pullback.fst (X.ofRestrict U.isOpenEmbedding)
          (X.ofRestrict V.isOpenEmbedding) ≫ X.ofRestrict U.isOpenEmbedding) hrange).hom from
    IsOpenImmersion.lift_uniq _ _ (le_of_eq hrange) _
      (by rw [← Category.assoc, pullback.lift_fst, restrictLE_fac])]
  infer_instance

/-- **The subspace on an intersection is the pullback of the two open subspaces.**

`X|(U ⊓ V) ≅ X|U ×_X X|V`, over `X` on both sides — the three factorisation lemmas below say so,
and they are what every use of this consumes.

**This is what makes a pullback of open immersions computable at all.** The module docstring of
`Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` records the problem it solves: a
categorical pullback of two inclusions is opaque, so a hypothesis phrased on it cannot be
discharged by the tools that discharge hypotheses about spaces one can name, whereas
`X.restrict (U ⊓ V)` is an open subspace and `restrictLE`, `hom_ext_restrict` and — for a
complex analytic space — `ComplexAnalytic.AnalyticSpace.restrict` all apply to it. -/
noncomputable def restrictInfIsoPullback :
    X.restrict (U ⊓ V).isOpenEmbedding ≅
      pullback (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) :=
  haveI := X.isIso_pullbackLift_restrictLE U V
  asIso (pullback.lift (X.restrictLE (inf_le_left : U ⊓ V ≤ U))
    (X.restrictLE (inf_le_right : U ⊓ V ≤ V)) (X.restrictLE_inf_condition U V))

/-- **The comparison, unfolded.** Not a `simp` lemma: the simp normal form of a morphism out of
`X|(U ⊓ V)` is the one in terms of `restrictLE` below, and rewriting `hom` to the raw
`pullback.lift` takes those out of it. -/
theorem restrictInfIsoPullback_hom :
    (X.restrictInfIsoPullback U V).hom =
      pullback.lift (X.restrictLE (inf_le_left : U ⊓ V ≤ U))
        (X.restrictLE (inf_le_right : U ⊓ V ≤ V)) (X.restrictLE_inf_condition U V) :=
  rfl

@[reassoc (attr := simp)]
theorem restrictInfIsoPullback_hom_fst :
    (X.restrictInfIsoPullback U V).hom ≫
        pullback.fst (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) =
      X.restrictLE (inf_le_left : U ⊓ V ≤ U) := by
  rw [restrictInfIsoPullback_hom, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem restrictInfIsoPullback_hom_snd :
    (X.restrictInfIsoPullback U V).hom ≫
        pullback.snd (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding) =
      X.restrictLE (inf_le_right : U ⊓ V ≤ V) := by
  rw [restrictInfIsoPullback_hom, pullback.lift_snd]

end RestrictInf

end AlgebraicGeometry.LocallyRingedSpace

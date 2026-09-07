/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.OpenSubspace
import Mathlib.Topology.LocalAtTarget

/-!
# The pullback of a morphism of complex analytic spaces along an open immersion

`Oka/AnalyticSpace/OpenSubspace.lean` builds the square

```
  X|f⁻¹V  --restrictHom f V-->  Y|V
     |                            |
 ofRestrict                  ofRestrict
     v                            v
     X  ---------- f ---------->  Y
```

and proves that it commutes, that a morphism into `X` whose image lies in `f⁻¹V` lifts, that the
lift is a factorisation, and that both vertical arrows are monomorphisms. **This file says that
the square is a pullback**, which is the sentence those four make and none of them states.

`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` is the instance that follows, so
`CategoryTheory.Limits.pullback` notation is usable at `ComplexAnalytic.AnalyticSpace` along a
leg of this shape.

## Why this is the shape that is reachable and the general one is not

At `e8c5f03`, and so at the Mathlib revision `lakefile.toml` pins there, neither
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` nor
`CategoryTheory.Limits.HasBinaryProducts ComplexAnalytic.AnalyticSpace` synthesises, and the same
is true one category down: `CategoryTheory.Limits.HasPullbacks AlgebraicGeometry.LocallyRingedSpace`
does not synthesise either, and `Mathlib/Geometry/RingedSpace/LocallyRingedSpace/` carries a
`HasColimits` file and no limits file. **So the general fibre product cannot be got by taking it in
locally ringed spaces and checking the result is analytic**: there is nothing there to take, which
is why `Mathlib/AlgebraicGeometry/Pullbacks.lean` builds the fibre product of schemes by gluing
over an affine cover instead.

The one limit that does exist one category down is this one:
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left` and its locally-ringed-space
counterpart give the pullback along an open immersion as a restriction to a preimage. **This
repository already depended on that instance and had not stated it at the analytic level until
this file** — `Oka/AnalyticSpace/Glue.lean`'s gluing lemmas phrase their agreement hypothesis as an
equation of morphisms out of `CategoryTheory.Limits.pullback` of two members of an
`AlgebraicGeometry.LocallyRingedSpace.OpenCover`, which is exactly that pullback.

## Main results

- `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict`: **the restriction square drawn at the top
  of this docstring is a pullback square.**
- `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` and
  `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict'`: the two instances it gives, one for each
  order of the cospan.
- `ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict`: **that square read as an
  isomorphism** — the pullback of `f` along the inclusion of `V` *is* the open subspace `X|f⁻¹V`,
  and not merely a limit over the same cospan.
- `ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict` and
  `ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict'`: **a base change of an
  open-subspace inclusion is one too**, so a cospan carrying
  `CategoryTheory.Limits.pullback.fst f (Y.ofRestrict V)` on a leg has a pullback although that leg
  is not spelled `ofRestrict`.
- `ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_pullbackFst`: those two instances at the
  cospan they exist for, which is the one
  `Mathlib/AlgebraicGeometry/Pullbacks.lean`'s `AlgebraicGeometry.Scheme.Pullback.t'` opens over.
- `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom`: **a finite morphism restricted over an open
  subset of its target is finite**, with no hypothesis on the open subset.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom`: the same for finite étale.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_ofRestrict`:
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom` at the
  `CategoryTheory.Limits.pullback` spelling, which is
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`'s conclusion at this cospan.
  **This entry read *at the one cospan this category has a pullback over* until 2026-09-07**, when
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and then
  `Oka/AnalyticSpace/CutOutFibreProduct.lean` gave the category further shapes; it was a claim
  about the tree standing in an entry about this file, and the entries added above it are more of
  the same shape.

## What this does not do

**It does not make `ComplexAnalytic.AnalyticSpace` a category with pullbacks, and it does not give
base change along a general morphism.** `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s
`## What is not here` says that no `CategoryTheory.Limits.HasPullback` instance for analytic spaces
is available and that base change is therefore unstatable for `isFiniteEtale`; after this file the
first half of that is false as a universal and the second is false at this one leg, and the
sentences there are narrowed to the general cospan rather than struck. The diagonal `A ⟶ A ×_B A`
that a monomorphism argument wants is over a cospan neither of whose legs is an open immersion, so
nothing here reaches it.

**And `ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict` and its primed partner do
not add a shape to that accounting.** `Oka/AnalyticSpace/LocalIso.lean`,
`Oka/AnalyticSpace/ZeroLocus.lean` and `Oka/AnalyticSpace/CutOutFibreProduct.lean` each quantify
over cospans by whether a leg *is* the inclusion of an open subspace, is finite étale with
Hausdorff source, or is a morphism between local models presented by cut-out data.
`ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict` is the statement that a base change
of the first kind of leg is again one, so those sentences are read up to that isomorphism and this
file supplies no cospan outside their three shapes — it supplies more spellings of the first.
`ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` implies that identification and does not
state it, which is why it is stated here.

## The finiteness lemma and the one already here are not the same statement

`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` takes an embedding hypothesis
on the morphism and asks the open subset to sit inside its image, and gives finiteness of a
restriction of a morphism that is **not** finite — the open-immersion case its own docstring
describes. `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` here takes finiteness of the
morphism and asks nothing of the open subset. Neither implies the other, and each is spent:
`isFinite_restrictHom_of_subset_range` in `Oka/Analytification/StandardEtaleFiniteness.lean`, and
this one in `ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom` below.
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) (V : Y.Opens)

/-! ### The underlying map of a restriction -/

/-- **The base map of `ComplexAnalytic.AnalyticSpace.restrictHom` is `Set.restrictPreimage`.**

Both sides send a point of `f⁻¹V` to its image under `f`, seen in `V`; the equality is
`ComplexAnalytic.base_restrictHom` — the commuting square on points — read through `Subtype.ext`,
because the target's carrier is a subtype and its inclusion is `Subtype.val`.

**This is the bridge to `Mathlib/Topology/LocalAtTarget.lean`**, whose lemmas about a map restricted
over a subset of its target are all stated for `Set.restrictPreimage` and are unusable here without
it. `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` consumes it, in both fields of
`ComplexAnalytic.AnalyticSpace.IsFinite`. -/
theorem base_restrictHom_eq_restrictPreimage :
    ((restrictHom f V).toLRSHom.base :
        X.restrict ((Opens.map f.toLRSHom.base).obj V) → Y.restrict V) =
      Set.restrictPreimage (V : Set Y) (f.toLRSHom.base : X → Y) :=
  funext fun x ↦ Subtype.ext (ComplexAnalytic.base_restrictHom f.toLRSHom V x)

/-! ### The square is a pullback -/

/-- **A cone over the cospan `f`, `ofRestrict V` maps into the preimage of `V`.**

This is the hypothesis `ComplexAnalytic.AnalyticSpace.liftRestrict` asks for, and it is the cone's
own commutation read at a point: the first leg followed by `f` and the second leg followed by the
inclusion of `V` agree, and the second lands in `V` by construction. Split out of
`ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` below because the lift is a term whose
proof argument would otherwise be a tactic block inside a `refine`. -/
theorem range_subset_preimage_of_pullbackCone (s : PullbackCone f (Y.ofRestrict V)) :
    Set.range (s.fst.toLRSHom.base : s.pt → X) ⊆
      (((Opens.map f.toLRSHom.base).obj V : X.Opens) : Set X) := by
  rintro _ ⟨w, rfl⟩
  have h : (f.toLRSHom.base : X → Y) ((s.fst.toLRSHom.base : s.pt → X) w) =
      ((s.snd.toLRSHom.base : s.pt → Y.restrict V) w).1 :=
    congrArg (fun (φ : s.pt ⟶ Y) ↦ (φ.toLRSHom.base : s.pt → Y) w) s.condition
  simp only [Opens.map_coe, Set.mem_preimage, h]
  exact ((s.snd.toLRSHom.base : s.pt → Y.restrict V) w).2

/-- **The restriction of a morphism over an open subset of its target is a pullback square.**

Every ingredient is in `Oka/AnalyticSpace/OpenSubspace.lean` and nothing is constructed here:
`ComplexAnalytic.AnalyticSpace.restrictHom_fac` is the commuting square,
`ComplexAnalytic.AnalyticSpace.liftRestrict` is the lift and
`ComplexAnalytic.AnalyticSpace.liftRestrict_fac` its factorisation, and both halves of
uniqueness are cancellation against `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`.

**The second factorisation is not proved directly and does not need to be.** A morphism into
`Y|V` is determined by its composite with the inclusion, because that inclusion is a
monomorphism, so `lift ≫ restrictHom f V = s.snd` follows from the outer square without ever
computing what the lift does to a point. -/
theorem isPullback_ofRestrict :
    IsPullback (X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)) (restrictHom f V) f
      (Y.ofRestrict V) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (restrictHom_fac f V).symm
    (fun s ↦ liftRestrict s.fst _ (range_subset_preimage_of_pullbackCone f V s))
    (fun s ↦ liftRestrict_fac _ _ _) (fun s ↦ ?_) (fun s m hm _ ↦ ?_))
  · rw [← cancel_mono (Y.ofRestrict V), Category.assoc, restrictHom_fac,
      ← Category.assoc, liftRestrict_fac, s.condition]
  · rw [← cancel_mono (X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)), liftRestrict_fac, hm]

/-- **A morphism of complex analytic spaces has a pullback along the inclusion of an open
subspace.** -/
instance hasPullback_ofRestrict : HasPullback f (Y.ofRestrict V) :=
  (isPullback_ofRestrict f V).hasPullback

/-- **The same cospan the other way round.** `CategoryTheory.IsPullback.flip` transposes the
square; the instance is stated separately because instance search matches the cospan's order and
not its transpose. -/
instance hasPullback_ofRestrict' : HasPullback (Y.ofRestrict V) f :=
  (isPullback_ofRestrict f V).flip.hasPullback

/-! ### That square read as an isomorphism, and the cospans it makes legal -/

/-- **The pullback of `f` along the inclusion of `V` *is* the open subspace `X|f⁻¹V`**, as an
isomorphism against the `CategoryTheory.Limits.pullback` notation.

`ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` says the restriction square is a pullback
square, and two limits over one cospan are uniquely isomorphic, so this is
`CategoryTheory.IsPullback.isoPullback` at it and there is nothing else in the proof. The move is
the one `ComplexAnalytic.AnalyticSpace.fibreProdCutOutIsoPullback` makes at the fibre product of
local models, in a different spelling: there the two limits are compared by
`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`, here by
`CategoryTheory.IsPullback.isoPullback`, which is that comparison packaged for a square already
known to be a pullback. `CategoryTheory.Limits.HasPullback` is `Prop`-valued and so loses the
identification of the limit with the object presenting it, and an isomorphism against the notation
is what keeps it.

**What this buys that `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` does not** is
`ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict` and its primed partner.
Instance search matches the cospan syntactically, so
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` is found at a leg spelled `Y.ofRestrict V`
and at no other, and a base change of such a leg is spelled
`CategoryTheory.Limits.pullback.fst`. This isomorphism is the statement that the two are the same
morphism up to the canonical identification. -/
noncomputable def restrictIsoPullbackOfRestrict :
    X.restrict ((Opens.map f.toLRSHom.base).obj V) ≅ pullback f (Y.ofRestrict V) :=
  (isPullback_ofRestrict f V).isoPullback

/-- **The isomorphism carries the open-subspace inclusion to `CategoryTheory.Limits.pullback.fst`**,
which is the half of it `ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict` and
`ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict'` consume. -/
@[simp]
theorem restrictIsoPullbackOfRestrict_hom_fst :
    (restrictIsoPullbackOfRestrict f V).hom ≫ pullback.fst f (Y.ofRestrict V) =
      X.ofRestrict ((Opens.map f.toLRSHom.base).obj V) :=
  (isPullback_ofRestrict f V).isoPullback_hom_fst

/-- **A morphism of complex analytic spaces has a pullback along the base change of an
open-subspace inclusion**, and not only along an open-subspace inclusion itself.

`CategoryTheory.Limits.pullback.fst f (Y.ofRestrict V)` is an open-subspace inclusion in disguise —
that is `ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict` — and the cospan of `k` with
it is carried to the cospan of `k` with `X.ofRestrict (f⁻¹V)` by `CategoryTheory.Limits.cospanExt`,
whose two commutation hypotheses are `CategoryTheory.Category.id_comp` and
`ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict_hom_fst`. The limit is then transported
by `CategoryTheory.Limits.hasLimit_of_iso`. **No new limit is constructed**: the pullback is the one
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` already gives, seen over a cospan whose
spelling instance search could not match.

**The consumer is the fibre product over a general cospan**, which is built by gluing the fibre
products over the members of an open cover, following
`Mathlib/AlgebraicGeometry/Pullbacks.lean`. The transition map `t'` of that glue datum is a morphism
out of a pullback of two of its `fV`s, each of which is a
`CategoryTheory.Limits.pullback.fst` at an `ofRestrict` leg, so **that object does not elaborate
without this instance**. **Measured at the commit that adds this declaration**, by transcribing
that file's block from `AlgebraicGeometry.Scheme.Pullback.v` to
`AlgebraicGeometry.Scheme.Pullback.t'` into this category: it is the only obligation in that block
which instance search could not discharge. Nothing past `t'` was transcribed and this says nothing
about it. -/
instance hasPullback_pullbackFst_ofRestrict {T : AnalyticSpace.{u}} (k : T ⟶ X) :
    HasPullback k (pullback.fst f (Y.ofRestrict V)) :=
  hasLimit_of_iso (F := cospan k (X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)))
    (cospanExt (Iso.refl T) (restrictIsoPullbackOfRestrict f V) (Iso.refl X) (by simp) (by simp))

/-- **The same cospan the other way round**, stated separately for the reason
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict'` is: instance search matches the cospan's
order and not its transpose. -/
instance hasPullback_pullbackFst_ofRestrict' {T : AnalyticSpace.{u}} (k : T ⟶ X) :
    HasPullback (pullback.fst f (Y.ofRestrict V)) k :=
  hasPullback_symmetry _ _

/-- **Two base changes of open-subspace inclusions, along the same morphism, have a pullback.**

This is the cospan `Mathlib/AlgebraicGeometry/Pullbacks.lean`'s
`AlgebraicGeometry.Scheme.Pullback.t'` opens over, with the two open subsets the two cover members
it compares, and it is the shape this category was missing: neither leg is spelled `ofRestrict`, so
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` is not found at it.

**It is stated rather than left to instance search, so that the guard on it tests that
`ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict` is *found* and not only that it
exists.** A `#print axioms` line on an instance does not do that — an instance sitting at a
discrimination-tree key search does not reach passes it and fails every use site — and that seam is
a recorded hazard in this corner of the tree, which
`ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`'s docstring exists for one instance of.
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_ofRestrict` below carries the same double
duty for `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict`. -/
theorem hasPullback_pullbackFst_pullbackFst (V' : Y.Opens) :
    HasPullback (pullback.fst f (Y.ofRestrict V)) (pullback.fst f (Y.ofRestrict V')) :=
  inferInstance

/-! ### Base change along an open immersion -/

/-- **A finite morphism restricted over an open subset of its target is finite**, and nothing is
asked of the open subset.

Both fields of `ComplexAnalytic.AnalyticSpace.IsFinite` survive:

* the base map is closed by `IsClosedMap.restrictPreimage`, which restricts a closed map over an
  arbitrary subset of the target — the witness for a closed set upstairs being the image of its
  closure — reached through
  `ComplexAnalytic.AnalyticSpace.base_restrictHom_eq_restrictPreimage`;
* a fibre of the restriction sits inside a fibre of the morphism, by the inclusion of the
  preimage, and an injection into a finite type has finite source.

**This is a different statement from
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range`**, whose hypotheses are on the
base map and on the open subset and whose conclusion is about a morphism that is not finite; see
this file's header. -/
instance isFinite_restrictHom [IsFinite f] : IsFinite (restrictHom f V) where
  isClosedMap := by
    rw [base_restrictHom_eq_restrictPreimage]
    exact (IsFinite.isClosedMap (f := f)).restrictPreimage _
  finite_fiber y := by
    have hset : ((restrictHom f V).toLRSHom.base : _ → Y.restrict V) ⁻¹' {y} =
        Subtype.val ⁻¹' ((f.toLRSHom.base : X → Y) ⁻¹' {y.1}) := by
      rw [base_restrictHom_eq_restrictPreimage]
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact Subtype.ext_iff
    rw [hset]
    have hfib : Finite ((f.toLRSHom.base : X → Y) ⁻¹' {y.1}) := IsFinite.finite_fiber _
    exact Finite.of_injective
      (fun x ↦ (⟨x.1.1, x.2⟩ : ((f.toLRSHom.base : X → Y) ⁻¹' {y.1} : Set X)))
      (by
        intro a b h
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Subtype.ext h))

/-- **A finite étale morphism restricted over an open subset of its target is finite étale.**

The two fields are `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` above and
`ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`, which was already in
`Oka/AnalyticSpace/OpenSubspace.lean` and asks nothing of the open subset either.

**Read with `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict`, this is base change of
`ComplexAnalytic.AnalyticSpace.isFiniteEtale` along an open immersion**: the restriction is the
pullback, so the pullback of a finite étale morphism along the inclusion of an open subspace is
finite étale. It is not `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`, which quantifies
over every cospan and needs a fibre product this category does not have. -/
instance isFiniteEtale_restrictHom [IsFiniteEtale f] : IsFiniteEtale (restrictHom f V) where
  isFinite := isFinite_restrictHom f V
  isLocalIso := isLocalIso_restrictHom f V

/-- **The base change of a finite étale morphism along the inclusion of an open subspace is finite
étale**, written at the `CategoryTheory.Limits.pullback` spelling rather than at the restriction.

This is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom` transported along
`CategoryTheory.IsPullback.isoPullback`, whose `isoPullback_inv_snd` says the second projection
out of the chosen pullback is that isomorphism followed by
`ComplexAnalytic.AnalyticSpace.restrictHom`; being finite étale then survives the composite because
an isomorphism is finite étale and the class is closed under composition.

**It is stated because the restriction spelling and the `pullback` spelling are not
interchangeable to instance search**, and a caller who writes a square rather than a preimage holds
the second. It is also what shows `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` is
*found* and not merely present: the statement cannot be written at all unless that instance is
synthesised. -/
instance isFiniteEtale_pullback_snd_ofRestrict [IsFiniteEtale f] :
    IsFiniteEtale (Limits.pullback.snd f (Y.ofRestrict V)) := by
  haveI : IsFiniteEtale (isPullback_ofRestrict f V).isoPullback.inv :=
    isFiniteEtale_of_isIso _
  rw [← (isPullback_ofRestrict f V).isoPullback_inv_snd]
  infer_instance

end ComplexAnalytic.AnalyticSpace

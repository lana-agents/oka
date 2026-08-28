/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Basic
import Oka.AnalyticSpace.ProjectionStalk
import Oka.Regular

/-!
# A hypersurface with a simple zero projects isomorphically on stalks

Let `i : X ⟶ ℂ^(n+1)` cut out `X` by a single holomorphic function `F`
(`ComplexAnalytic.IsCutOutBy`), and let `p : ℂ^(n+1) ⟶ ℂ^n` forget the last coordinate. At a
point `x` of `X` at which the germ of `F` has a **simple zero along the last axis**, the stalk
map of `i ≫ p` is an isomorphism: the germ ring of the hypersurface is the germ ring one
dimension down, and the isomorphism is the one the projection induces.

This is the stalk half of *the analytification of a standard étale morphism is a local
isomorphism*. It is the algebra of `Oka/Regular.lean` read as a statement about a morphism of
spaces, and everything it needs was already here — the file is the assembly and one general
lemma about kernels.

## The four inputs

* the stalk of a cut-out is the ambient stalk modulo the germs of the cutting sections —
  `ComplexAnalytic.IsCutOutBy`'s `surjective_stalkMap` and `ker_stalkMap` fields;
* the stalk of `𝒪_{ℂ^ι}` at any point is `LocalOkaRing ι` — `okaStalkEquiv`, which is in the
  **root** namespace, in `Oka/StalkEquiv.lean`;
* the stalk map of the projection is `LocalOkaRing.incl` —
  `ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords`;
* `LocalOkaRing (Fin n)` is `LocalOkaRing (Fin (n+1)) ⧸ (f)` at a germ with a simple zero —
  `LocalOkaRing.quotientSimpleZeroEquiv`.

The last of those is the mathematics — Weierstrass division at degree one — and the three before
it are what turns it into a statement about `i ≫ p`. What makes the assembly go through in one
step is that `LocalOkaRing.quotientSimpleZeroEquiv`'s underlying map **is**
`Ideal.Quotient.mk ∘ LocalOkaRing.incl`, on the nose: it is built by `RingEquiv.ofBijective` on
that composite in `LocalOkaRing.quotientDegreeOneEquiv`, so no computation is needed to recognise
it in the composite stalk map.

## The shape: one abstract step, two indexings

`ComplexAnalytic.bijective_stalkMap_comp_of_incl` takes the two identifications as arguments —
a ring isomorphism of each stalk with a `LocalOkaRing`, and the statement that the projection is
`LocalOkaRing.incl` between them — and is the whole proof. It is stated that way because this
development indexes the coordinates of `ℂ^n` in **two** ways, `Fin n` and `ULift (Fin n)`, and
the two instances differ only in which pair of isomorphisms is supplied:

* `ComplexAnalytic.bijective_stalkMap_comp_projCoords`, for `complexSpace (Fin (n+1))` and
  `ComplexAnalytic.projCoords`, where the identification is `okaStalkEquiv` alone;
* `ComplexAnalytic.bijective_stalkMap_comp_uliftProj`, for `complexAffineSpace (n+1)` — which is
  `complexSpace (ULift (Fin (n+1)))`, both in the root namespace — and
  `ComplexAnalytic.uliftCastSuccEmb`, where it is
  `okaStalkEquiv` followed by `LocalOkaRing.uliftEquiv`.

The second is the one the Riemann-existence line consumes, since
`ComplexAnalytic.AnalyticSpace` is indexed by `ULift (Fin n)`; the first is the one to read,
since nothing in it is bookkeeping. Neither is a corollary of the other: there is no morphism of
spaces between the two spellings of `ℂ^n` above `Type 0`, for the reason
`Oka/AnalyticSpace/ProjectionStalk.lean`'s module docstring gives.

## Why the hypothesis is `PowerSeries.order … = 1`

Because that is what `LocalOkaRing.quotientSimpleZeroEquiv` asks for, and its own docstring says
why: **this repository has no partial-derivative operator on `LocalOkaRing`**, so *"`∂F/∂X_n` is
a unit at the point"* is not expressible. `PowerSeries.order (MvPowerSeries.partialEval
(Fin.last n) f) = 1` is the same condition on a germ vanishing at the point, and it is what
`localweierstrass_preparation` computes internally. Bridging the two is separate work and nothing
here attempts it.

Note that the germ is taken **at the point**, so the condition is on the Taylor expansion of `F`
centred at `i.base x` and not at the origin; `okaStalkEquiv` absorbs the translation.

## Main results

- `ComplexAnalytic.IsCutOutBy.mem_ker_stalkMap_iff`: for a cut-out by a **single** section, the
  kernel of the stalk map is the principal ideal on the germ, read through any ring isomorphism
  of the ambient stalk.
- `ComplexAnalytic.bijective_stalkMap_comp_of_incl`: **the abstract step** — if the projection is
  the inclusion of the germs not involving the last variable and the immersion is the quotient by
  a germ with a simple zero, the composite is bijective on stalks.
- `ComplexAnalytic.bijective_stalkMap_comp_projCoords` and
  `ComplexAnalytic.isIso_stalkMap_comp_projCoords`: **the projection of a hypersurface with a
  simple zero is an isomorphism on stalks**, for the `Fin`-indexed `ℂ^(n+1)`.
- `ComplexAnalytic.bijective_stalkMap_comp_uliftProj` and
  `ComplexAnalytic.isIso_stalkMap_comp_uliftProj`: the same for
  `complexAffineSpace` (root namespace, `Oka/ComplexSpace.lean`), the `ULift (Fin _)`-indexed
  one.

## What is not here

**No finiteness, and so no `IsLocalIso` and no `IsFiniteEtale`.**
`ComplexAnalytic.AnalyticSpace.IsLocalIso` asks for a topological condition beside the stalk one,
and finiteness of the projection of a monic hypersurface to its base — that the map is closed —
is a separate and much larger piece of work. Nothing below says anything about the underlying
map of `i ≫ p`, not even that it is open.

**No hypersurface inside an open subset.** `Y` is the whole of `ℂ^(n+1)` here, so `F` is entire.
A standard étale algebra inverts a polynomial as well as cutting one out, and its analytification
lives in an open subspace; `ComplexAnalytic.IsLocalModel` is stated for
`(complexAffineSpace n).restrict U` for exactly that reason. Carrying the argument across the
restriction needs the stalks of an open subspace identified with the ambient ones, which is
`AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso` and is not done here.

**No derivative hypothesis**, and **no packaged `LocalOkaRing (Fin n) ≃+* X.presheaf.stalk x`**:
the isomorphism is available as `CategoryTheory.asIso` of the results below composed with
`okaStalkEquiv`, and naming that composite would fix a direction this file has no consumer for
yet.

**No statement about more than one cutting section.** `ComplexAnalytic.IsCutOutBy` allows a family
of any length; `ComplexAnalytic.IsCutOutBy.mem_ker_stalkMap_iff` and everything after it are for
`![F]`, because `LocalOkaRing.quotientSimpleZeroEquiv` quotients by a principal ideal. A complete
intersection of higher codimension would be an induction and is not attempted.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Function

universe u

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### The kernel of the stalk map of a cut-out by one section -/

/-- **For a cut-out by a single section, the kernel of the stalk map is the principal ideal on
its germ**, transported along any ring isomorphism of the ambient stalk.

`ComplexAnalytic.IsCutOutBy`'s `ker_stalkMap` field gives the ideal generated by the *range* of
the family, which at a one-element family is a singleton; the transport is there because every
consumer of this holds the ambient stalk as a `LocalOkaRing` and not as a colimit.

The generator is an argument together with the equation that produces it, rather than being
written out as `β (Y.presheaf.Γgerm (i.base x) F)`. That is not cosmetic: the two spellings of
the ambient point — through `X.toTopCat` and through `X.toPresheafedSpace` — make the written-out
form a term `rw` will not match against the one a caller builds, and passing the equation lets
elaboration do the identification instead. -/
theorem IsCutOutBy.mem_ker_stalkMap_iff {X Y : LocallyRingedSpace.{u}} {i : X ⟶ Y}
    {F : Y.presheaf.obj (op ⊤)} (hcut : IsCutOutBy i ![F]) (x : X)
    {R : Type*} [CommRing R] (β : Y.presheaf.stalk (i.base x) ≃+* R) {a : R}
    (ha : β (Y.presheaf.Γgerm (i.base x) F) = a) (s : Y.presheaf.stalk (i.base x)) :
    s ∈ RingHom.ker (i.stalkMap x).hom ↔ β s ∈ Ideal.span {a} := by
  subst ha
  have hker : RingHom.ker (i.stalkMap x).hom =
      Ideal.span {Y.presheaf.Γgerm (i.base x) F} := by
    rw [hcut.ker_stalkMap x]
    congr 1
    rw [Set.range_unique]
    rfl
  rw [hker, Ideal.mem_span_singleton, Ideal.mem_span_singleton, map_dvd_iff β]

/-! ### The abstract step -/

/-- **The composite of a one-section cut-out and a projection which is `LocalOkaRing.incl` on
stalks is bijective on stalks, at a germ with a simple zero.**

The two identifications are arguments: `β` reads the ambient stalk as `LocalOkaRing (Fin (n+1))`,
`α` reads the stalk of the base as `LocalOkaRing (Fin n)`, `hP` says the projection is
`LocalOkaRing.incl` between them, and `hker` says the immersion is the quotient by `(f)`. What is
proved is that `LocalOkaRing.quotientSimpleZeroEquiv` is exactly the induced map.

Both halves are the same two facts read in opposite directions. **Injectivity**: a germ killed by
the composite lands in `(f)`, so its class is `0`, so it is `0` because
`LocalOkaRing.quotientSimpleZeroEquiv` is injective. **Surjectivity**: lift the target to the
ambient stalk, take the preimage of its class, and the difference lands in `(f)` — which is the
kernel — so the two have the same image. -/
theorem bijective_stalkMap_comp_of_incl {X Y W : LocallyRingedSpace.{u}}
    (i : X ⟶ Y) (p : Y ⟶ W) (x : X)
    (α : W.presheaf.stalk (p.base (i.base x)) ≃+* LocalOkaRing (Fin n))
    (β : Y.presheaf.stalk (i.base x) ≃+* LocalOkaRing (Fin (n + 1)))
    {f : LocalOkaRing (Fin (n + 1))}
    (hP : ∀ t, β ((p.stalkMap (i.base x)).hom t) = LocalOkaRing.incl (α t))
    (hQ : Function.Surjective (i.stalkMap x).hom)
    (hker : ∀ s, s ∈ RingHom.ker (i.stalkMap x).hom ↔ β s ∈ Ideal.span {f})
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      (f : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    Function.Bijective ((i ≫ p).stalkMap x).hom := by
  -- `LocalOkaRing.quotientSimpleZeroEquiv` is `Ideal.Quotient.mk ∘ LocalOkaRing.incl` on the
  -- nose, which is why this `have` needs no proof beyond the equivalence itself.
  have hE : Function.Bijective
      (fun c : LocalOkaRing (Fin n) ↦ Ideal.Quotient.mk (Ideal.span {f}) (LocalOkaRing.incl c)) :=
    (LocalOkaRing.quotientSimpleZeroEquiv hf).bijective
  have hcomp : ((i ≫ p).stalkMap x).hom =
      (i.stalkMap x).hom.comp ((p.stalkMap (i.base x)).hom) := by
    rw [LocallyRingedSpace.stalkMap_comp]
    rfl
  rw [hcomp]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    have h1 : ((p.stalkMap (i.base x)).hom t) ∈ RingHom.ker (i.stalkMap x).hom := ht
    rw [hker, hP t] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {f}) (LocalOkaRing.incl (α t)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 h1
    exact (map_eq_zero_iff α α.injective).1 (hE.1 (by simpa using h2))
  · intro c
    obtain ⟨s, hs⟩ := hQ c
    obtain ⟨t₀, ht₀⟩ := hE.2 (Ideal.Quotient.mk (Ideal.span {f}) (β s))
    refine ⟨α.symm t₀, ?_⟩
    have hdiff : (p.stalkMap (i.base x)).hom (α.symm t₀) - s ∈
        RingHom.ker (i.stalkMap x).hom := by
      have hsub : β ((p.stalkMap (i.base x)).hom (α.symm t₀) - s) =
          β ((p.stalkMap (i.base x)).hom (α.symm t₀)) - β s := map_sub β _ _
      rw [hker, hsub, hP, RingEquiv.apply_symm_apply]
      exact Ideal.Quotient.eq.1 ht₀
    have h4 : (i.stalkMap x).hom ((p.stalkMap (i.base x)).hom (α.symm t₀)) -
        (i.stalkMap x).hom s = 0 := by
      rw [← map_sub]
      exact hdiff
    have h5 : (i.stalkMap x).hom ((p.stalkMap (i.base x)).hom (α.symm t₀)) = c := by
      rw [← hs, ← sub_eq_zero]
      exact h4
    exact h5

/-! ### The two indexings

`ComplexAnalytic.projCoords` for `Fin`, `ComplexAnalytic.uliftCastSuccEmb` for `ULift (Fin _)`.
The only difference between the two proofs is the pair of identifications handed to
`ComplexAnalytic.bijective_stalkMap_comp_of_incl`. -/

section Fin

variable {X : LocallyRingedSpace.{0}} {i : X ⟶ complexSpace (Fin (n + 1))}
  {F : OkaRing (⊤ : Opens (Fin (n + 1) → ℂ))}

/-- **The projection of a hypersurface with a simple zero is bijective on stalks.**

`F` is an entire function on `ℂ^(n+1)`, `i` cuts out `X` by it, and the hypothesis says that the
Taylor expansion of `F` at `i.base x`, restricted to the last axis, has a simple zero. -/
theorem bijective_stalkMap_comp_projCoords (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial) F :
        LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    Function.Bijective ((i ≫ okaMapHom (projCoords n)).stalkMap x).hom := by
  refine bijective_stalkMap_comp_of_incl i _ x _ (okaStalkEquiv (i.base x))
    (fun t ↦ okaStalkEquiv_stalkMap_okaMapHom_projCoords_apply t)
    (hcut.surjective_stalkMap x) (fun s ↦ ?_) hf
  exact hcut.mem_ker_stalkMap_iff x (okaStalkEquiv (i.base x)) (okaStalkEquiv_germ _ _) s

/-- **The projection of a hypersurface with a simple zero is an isomorphism on stalks.** -/
theorem isIso_stalkMap_comp_projCoords (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((OkaRing.germ (show i.base x ∈ (⊤ : Opens (Fin (n + 1) → ℂ)) from trivial) F :
        LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    IsIso ((i ≫ okaMapHom (projCoords n)).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkMap_comp_projCoords hcut x hf)

end Fin

section ULift

variable {X : LocallyRingedSpace.{u}} {i : X ⟶ complexAffineSpace.{u} (n + 1)}
  {F : OkaRing (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))}

/-- **The same for `complexAffineSpace`** — the root-namespace one, `Oka/ComplexSpace.lean`,
whose coordinates are indexed by `ULift (Fin (n+1))`.

The germ ring is relabelled by `LocalOkaRing.uliftEquiv` at both ends, which is why the
hypothesis is about `LocalOkaRing.uliftEquiv` of the germ rather than about the germ. That
relabelling is a ring isomorphism and not an isomorphism of spaces, and it cannot be one; see
`Oka/AnalyticSpace/ProjectionStalk.lean`. -/
theorem bijective_stalkMap_comp_uliftProj (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((LocalOkaRing.uliftEquiv (Fin (n + 1))
        (OkaRing.germ (show i.base x ∈ (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F) :
          LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    Function.Bijective
      ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x).hom := by
  refine bijective_stalkMap_comp_of_incl i _ x
    ((okaStalkEquiv (okaMapFun (coordEmb (uliftCastSuccEmb.{u} n)) (i.base x))).trans
      (LocalOkaRing.uliftEquiv (Fin n)))
    ((okaStalkEquiv (i.base x)).trans (LocalOkaRing.uliftEquiv (Fin (n + 1))))
    (fun t ↦ by exact AnalyticSpace.okaStalkEquiv_stalkMap_uliftProj_apply t)
    (hcut.surjective_stalkMap x) (fun s ↦ ?_) hf
  exact hcut.mem_ker_stalkMap_iff x _
    (congrArg (LocalOkaRing.uliftEquiv (Fin (n + 1))) (okaStalkEquiv_germ _ _)) s

/-- **The same as an isomorphism.** The morphism is
`ComplexAnalytic.AnalyticSpace.proj`'s underlying morphism of locally ringed spaces, by
`ComplexAnalytic.AnalyticSpace.toLRSHom_proj`. -/
theorem isIso_stalkMap_comp_uliftProj (hcut : IsCutOutBy i ![F]) (x : X)
    (hf : PowerSeries.order (MvPowerSeries.partialEval (Fin.last n)
      ((LocalOkaRing.uliftEquiv (Fin (n + 1))
        (OkaRing.germ (show i.base x ∈ (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) from trivial) F) :
          LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ)) = 1) :
    IsIso ((i ≫ okaMapHom (coordEmb (uliftCastSuccEmb.{u} n))).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkMap_comp_uliftProj hcut x hf)

end ULift

end ComplexAnalytic

end

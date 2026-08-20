/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Oka.Polynomial
import Oka.StalkEquiv

/-!
# Comparing `ℂ^ι` with affine space over `ℂ`

The base case of analytification: the canonical morphism of locally ringed spaces from `ℂ^ι`,
with its sheaf of holomorphic functions, to affine `ι`-space over `ℂ`. Everything about the
analytification of an affine `ℂ`-scheme is pulled back along it.

The morphism costs nothing to build. Mathlib's Γ-Spec adjunction provides
`AlgebraicGeometry.LocallyRingedSpace.toΓSpec`, the canonical map from any locally ringed space
to the spectrum of its global sections; the global sections of `ℂ^ι` are `OkaRing ⊤`, and
`OkaRing.ofMvPolynomial` reads a polynomial as a holomorphic function, so composing with `Spec`
of that ring homomorphism lands in `Spec (MvPolynomial ι ℂ)`. All the content is in identifying
the result, and that is `mem_complexSpaceToSpec_base_asIdeal_iff`: the point of
`Spec (MvPolynomial ι ℂ)` under `z` is the ideal of polynomials vanishing at `z`.

## A universe remark, because the obvious statement does not typecheck

One would like to land in `𝔸(ι; Spec (CommRingCat.of ℂ))` directly for `ι : Type u`. That is
not a well-formed expression: `AlgebraicGeometry.AffineSpace n S` needs `S : Scheme.{u}`, so it
needs `CommRingCat.of ℂ : CommRingCat.{u}`, and `ℂ : Type 0`. Nor is the index the problem —
replacing `ι` by `ULift (Fin n)` changes nothing.

Routing through `Spec (MvPolynomial ι ℂ)` avoids this entirely, because `MvPolynomial ι ℂ` is a
`Type u` as soon as `ι` is, so `complexSpaceToSpec` is universe-polymorphic. The comparison with
affine space in Mathlib's sense is then `complexAffineSpaceToAffineSpace`, which lives in
`Type 0` where `𝔸(-; Spec ℂ)` makes sense, and is obtained from the polymorphic map by
`AlgebraicGeometry.AffineSpace.SpecIso`.

## Main definitions

- `complexSpaceToSpec`: the comparison morphism `ℂ^ι ⟶ Spec (MvPolynomial ι ℂ)`, for any finite
  index type `ι` in any universe.
- `complexAffineSpaceToAffineSpace`: the same map, presented as
  `ℂ^n ⟶ 𝔸^n_ℂ` with Mathlib's affine space, necessarily in `Type 0`.

## Main results

- `mem_complexSpaceToSpec_base_asIdeal_iff` and `complexSpaceToSpec_base_asIdeal`: **the point
  under `z` is the ideal of polynomials vanishing at `z`**, i.e. `ker (eval z)`.
- `isMaximal_complexSpaceToSpec_base_asIdeal`: that ideal is maximal, so `ℂ^ι` maps into the
  closed points of `Spec (MvPolynomial ι ℂ)`.
- `complexSpaceToSpec_base_injective`: the map on points is injective.

## What is not here

The description of the induced map on stalks — the localisation of `MvPolynomial ι ℂ` at
`ker (eval z)` mapping to the ring of convergent power series — and its **flatness**, which is
the analytic input to GAGA. Neither is proved; the comparison is not complete without them.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

variable (ι : Type u) [Fintype ι]

/-- A polynomial is a holomorphic function on all of `ℂ^ι`, as a morphism of `CommRingCat` into
the global sections of the structure sheaf of `ℂ^ι`. This is `OkaRing.ofMvPolynomial` at
`U = ⊤`, bundled for use with `Spec`. -/
def okaGlobalOfMvPolynomial :
    CommRingCat.of (MvPolynomial ι ℂ) ⟶ LocallyRingedSpace.Γ.obj (op (complexSpace ι)) :=
  CommRingCat.ofHom (OkaRing.ofMvPolynomial (⊤ : Opens (ι → ℂ))).toRingHom

/-- **The comparison morphism from `ℂ^ι` to affine `ι`-space over `ℂ`**, as a morphism of
locally ringed spaces into `Spec (MvPolynomial ι ℂ)`.

This is the canonical map to the spectrum of the global sections
(`AlgebraicGeometry.LocallyRingedSpace.toΓSpec`) composed with `Spec` of "a polynomial is a
holomorphic function". See the module docstring for why the target is spelled as a spectrum
rather than as `𝔸(ι; Spec ℂ)`. -/
def complexSpaceToSpec :
    complexSpace ι ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of (MvPolynomial ι ℂ)) :=
  (complexSpace ι).toΓSpec ≫ Spec.locallyRingedSpaceMap (okaGlobalOfMvPolynomial ι)

variable {ι}

/-- The germ at `z` of the holomorphic function attached to a polynomial `p` is a non-unit
exactly when `p` vanishes at `z`.

Stated on the `okaCommPresheaf` spelling of the structure sheaf rather than on
`(complexSpace ι).presheaf`: the two are definitionally equal, but `germ_mem_maximalIdeal_iff`
is phrased in the former and `rw` cannot cross that seam. -/
theorem not_isUnit_germ_ofMvPolynomial_iff (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    ¬ IsUnit ((okaCommPresheaf ι).germ ⊤ z trivial (OkaRing.ofMvPolynomial ⊤ p)) ↔
      MvPolynomial.eval z p = 0 :=
  ((IsLocalRing.mem_maximalIdeal _).trans mem_nonunits_iff).symm.trans
    (germ_mem_maximalIdeal_iff (U := ⊤) trivial (OkaRing.ofMvPolynomial ⊤ p))

/-- **The point of `Spec (MvPolynomial ι ℂ)` underneath `z` is the ideal of polynomials
vanishing at `z`.** This is what makes `complexSpaceToSpec` recognisable as the classical
comparison map; without it the morphism is only a formal composite. -/
theorem mem_complexSpaceToSpec_base_asIdeal_iff (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    p ∈ ((complexSpaceToSpec ι).base z).asIdeal ↔ MvPolynomial.eval z p = 0 := by
  refine Iff.trans ?_ (not_isUnit_germ_ofMvPolynomial_iff z p)
  rw [show (complexSpaceToSpec ι).base z = PrimeSpectrum.comap
      (okaGlobalOfMvPolynomial ι).hom ((complexSpace ι).toΓSpecFun z) from rfl,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, ← not_not
      (a := (okaGlobalOfMvPolynomial ι).hom p ∈ ((complexSpace ι).toΓSpecFun z).asIdeal),
    LocallyRingedSpace.notMem_prime_iff_unit_in_stalk]
  exact Iff.rfl

/-- `mem_complexSpaceToSpec_base_asIdeal_iff` as an equality of ideals: the point underneath `z`
is the kernel of evaluation at `z`. -/
theorem complexSpaceToSpec_base_asIdeal (z : ι → ℂ) :
    ((complexSpaceToSpec ι).base z).asIdeal = RingHom.ker (MvPolynomial.eval z) :=
  Ideal.ext fun p ↦ (mem_complexSpaceToSpec_base_asIdeal_iff z p).trans RingHom.mem_ker.symm

/-- The image of `ℂ^ι` consists of **closed** points of `Spec (MvPolynomial ι ℂ)`: evaluation at
`z` is a surjection onto the field `ℂ`, so its kernel is a maximal ideal. -/
theorem isMaximal_complexSpaceToSpec_base_asIdeal (z : ι → ℂ) :
    ((complexSpaceToSpec ι).base z).asIdeal.IsMaximal := by
  rw [complexSpaceToSpec_base_asIdeal]
  exact RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval z)
    fun c ↦ ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩

/-- **The comparison morphism is injective on points.** Two points of `ℂ^ι` with the same image
agree, because `X i - C (w i)` vanishes at `w` and hence at `z`. -/
theorem complexSpaceToSpec_base_injective :
    Function.Injective fun z : ι → ℂ ↦ (complexSpaceToSpec ι).base z := by
  intro z w h
  -- The equality `h` of points is fed to `congrArg` rather than to `rw`: the carrier of
  -- `complexSpace ι` and `ι → ℂ` are definitionally equal but not at `instances`
  -- transparency, and a `rw` across that seam is rejected outright.
  have key (p : MvPolynomial ι ℂ) :
      MvPolynomial.eval z p = 0 ↔ MvPolynomial.eval w p = 0 :=
    (mem_complexSpaceToSpec_base_asIdeal_iff z p).symm.trans
      ((Iff.of_eq (congrArg (fun q : PrimeSpectrum (MvPolynomial ι ℂ) ↦ p ∈ q.asIdeal) h)).trans
        (mem_complexSpaceToSpec_base_asIdeal_iff w p))
  funext i
  have hz := (key (MvPolynomial.X i - MvPolynomial.C (w i))).2 (by simp)
  simpa [sub_eq_zero] using hz

section AffineSpace

variable (n : ℕ)

/-- **The comparison morphism `ℂ^n ⟶ 𝔸^n_ℂ`**, with Mathlib's affine space over `Spec ℂ`.

This is `complexSpaceToSpec` transported along `AlgebraicGeometry.AffineSpace.SpecIso`. It is
necessarily stated in `Type 0`: `𝔸(-; Spec (CommRingCat.of ℂ))` is a `Scheme.{0}` because `ℂ`
is, so unlike `complexSpaceToSpec` it cannot be universe-polymorphic. -/
def complexAffineSpaceToAffineSpace :
    complexAffineSpace.{0} n ⟶
      (𝔸(ULift.{0} (Fin n); Spec (CommRingCat.of ℂ))).toLocallyRingedSpace :=
  complexSpaceToSpec _ ≫
    (AffineSpace.SpecIso (ULift.{0} (Fin n)) (CommRingCat.of ℂ)).inv.toLRSHom

end AffineSpace

end

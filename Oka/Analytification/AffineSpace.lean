/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Oka.Polynomial.Germ
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
- `toStalk_stalkMap_complexSpaceToSpec` and `okaStalkEquiv_stalkMap_complexSpaceToSpec`: **the
  map on stalks is the localisation-to-germs map** — a polynomial goes to the germ at `z` of the
  holomorphic function it defines. Since the stalk of `Spec R` at `p` *is* the localisation of
  `R` at `p`, and `isUnit_ofMvPolynomial_of_mem_primeCompl` says the denominators become units,
  this determines the stalk map completely.

## What is not here

**Flatness** of the stalk map, which is the analytic input to GAGA. It is not proved, and the
comparison is not complete without it.

The stalk map is also not *packaged* as an `IsLocalization.lift`, though the two theorems above
determine it uniquely. That packaging is blocked, and the obstruction is worth recording because
it will recur. Mathlib registers `Algebra R ((Spec.structureSheaf R).presheaf.stalk p)` and
`IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk p) p.asIdeal`, but a morphism of
locally ringed spaces produces the stalk in the `Spec.locallyRingedSpaceObj R` spelling. The two
are definitionally equal and `Spec.locallyRingedSpaceObj` is a `def`, so instance search — which
unfolds only at reducible transparency — never gets there. Restating both instances in the second
spelling does *not* fix it either: the point `(complexSpaceToSpec ι).base z` then has to be
unified with a `PrimeSpectrum` across the same `TopCat.of` seam, and that `isDefEq` still times
out at a million heartbeats.
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


section Stalk

open StructureSheaf

/-- **The stalk map, restricted along `toStalk`, is the germ map.** A polynomial, regarded as a
global section of the structure sheaf of `Spec (MvPolynomial ι ℂ)`, is carried to the germ at `z`
of the holomorphic function it defines.

This is the characterising property: the stalk of `Spec R` at `p` is the localisation of `R` at
`p` (`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`), so a ring homomorphism out of
it is determined by its restriction along `toStalk`. `stalkMap_complexSpaceToSpec` is that
statement.

The proof composes two Mathlib lemmas — `AlgebraicGeometry.stalkMap_toStalk` for the `Spec` half
and `AlgebraicGeometry.LocallyRingedSpace.toStalk_stalkMap_toΓSpec` for the unit half — and never
unfolds `toΓSpecSheafedSpace`. The final step uses `congrArg` rather than `rw` because the
rewrite is rejected across the `TopCat.of` transparency seam; see `OkaTest/SimpDiscrTree.lean`. -/
theorem toStalk_stalkMap_complexSpaceToSpec (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    (complexSpaceToSpec ι).stalkMap z
        (toStalk (MvPolynomial ι ℂ) ((complexSpaceToSpec ι).base z) p) =
      (complexSpace ι).presheaf.Γgerm z (okaGlobalOfMvPolynomial ι p) := by
  have h1 := stalkMap_toStalk_apply (okaGlobalOfMvPolynomial ι)
    ((complexSpace ι).toΓSpecFun z) p
  have h2 := ConcreteCategory.congr_hom ((complexSpace ι).toStalk_stalkMap_toΓSpec z)
    (okaGlobalOfMvPolynomial ι p)
  simp only [ConcreteCategory.comp_apply] at h1 h2
  have key : (complexSpaceToSpec ι).stalkMap z =
      (Spec.locallyRingedSpaceMap (okaGlobalOfMvPolynomial ι)).stalkMap
        ((complexSpace ι).toΓSpecFun z) ≫ (complexSpace ι).toΓSpec.stalkMap z :=
    LocallyRingedSpace.stalkMap_comp _ _ _
  rw [key]
  -- `change`, not `rw`: the two spellings of the base point differ across the `TopCat.of`
  -- seam and a rewrite is rejected there as not type-correct.
  change (complexSpace ι).toΓSpec.stalkMap z
      ((Spec.sheafedSpaceMap (okaGlobalOfMvPolynomial ι)).hom.stalkMap
        ((complexSpace ι).toΓSpecFun z)
        (toStalk (MvPolynomial ι ℂ)
          (PrimeSpectrum.comap (okaGlobalOfMvPolynomial ι).hom
            ((complexSpace ι).toΓSpecFun z)) p)) = _
  exact (congrArg ((complexSpace ι).toΓSpec.stalkMap z) h1).trans h2

/-- Transported along `okaStalkEquiv`, the previous statement reads: a polynomial goes to its
germ at `z` as an element of `LocalOkaRing ι`, which is `LocalOkaRing.ofMvPolynomial`. -/
theorem okaStalkEquiv_stalkMap_complexSpaceToSpec (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    okaStalkEquiv z ((complexSpaceToSpec ι).stalkMap z
        (toStalk (MvPolynomial ι ℂ) ((complexSpaceToSpec ι).base z) p)) =
      LocalOkaRing.ofMvPolynomial z p := by
  rw [toStalk_stalkMap_complexSpaceToSpec]
  exact okaStalkEquiv_germ (U := ⊤) trivial (OkaRing.ofMvPolynomial ⊤ p)

/-- A polynomial not in the point underneath `z` — that is, one which does not vanish at `z` —
has invertible germ. This is what lets the localisation of `MvPolynomial ι ℂ` at that point map
to the germs at all. -/
theorem isUnit_ofMvPolynomial_of_mem_primeCompl (z : ι → ℂ)
    (y : ((complexSpaceToSpec ι).base z).asIdeal.primeCompl) :
    IsUnit (LocalOkaRing.ofMvPolynomial z (y : MvPolynomial ι ℂ)) := by
  rw [LocalOkaRing.isUnit_ofMvPolynomial_iff]
  exact fun h ↦ y.2 ((mem_complexSpaceToSpec_base_asIdeal_iff z _).2 h)

end Stalk

end

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the rigidity of germs on `ℂ^ι`

`ComplexAnalytic.okaStalk_ringHom_ext` says that a local `ℂ`-algebra homomorphism out of a stalk
of `𝒪_{ℂ^ι}` into a Noetherian local ring is determined by the images of the coordinate germs.
Two things could make that empty: the instances it demands of the target might not be findable
for any interesting ring, and the hypotheses might not be simultaneously satisfiable.

Neither happens. The stalk of `𝒪_{ℂ^ι}` at a point is itself local and Noetherian
(`ComplexAnalytic.isNoetherianRing_okaStalk`), so the theorem applies with the stalk as its own
target, and the identity satisfies both hypotheses — giving `endomorphism_eq_id` below: a local
`ℂ`-algebra endomorphism of a germ ring fixing the coordinates is the identity. That is a
statement with content, and it is the shape in which the rigidity is used.

**What is *not* checked here, and should be said rather than left to be discovered:** as of this
commit the development still contains **no non-identity morphism of analytic spaces**, so
`ComplexAnalytic.AnalyticSpace.evalStalk_stalkMap` cannot be instantiated at anything but the
identity. That is why it is stated for a `ℂ`-linear morphism of the *underlying locally ringed
spaces* rather than for a `ComplexAnalytic.AnalyticSpace.Hom` — in that form it will apply to
the charts, which are exactly `ℂ`-linear morphisms of locally ringed spaces, the moment a
second analytic-space structure is around to receive them. Taxis #654 is what changes that, and
the non-vacuity of the naturality statement belongs with it.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry IsLocalRing ComplexAnalytic

universe u

noncomputable section

variable {ι : Type u} [Fintype ι]

/-- **A local `ℂ`-algebra endomorphism of a germ ring on `ℂ^ι` fixing the coordinates is the
identity.** The hypotheses of `ComplexAnalytic.okaStalk_ringHom_ext` are satisfiable — the
identity satisfies them — and its instance requirements are met by the germ ring itself. -/
theorem endomorphism_eq_id {y : ι → ℂ}
    (θ : (okaCommPresheaf ι).stalk y →+* (okaCommPresheaf ι).stalk y) [IsLocalHom θ]
    (hconst : ∀ c : ℂ, θ (((okaCommPresheaf ι).germ ⊤ y trivial).hom
        (algebraMap ℂ (OkaRing ⊤) c)) =
      ((okaCommPresheaf ι).germ ⊤ y trivial).hom (algebraMap ℂ (OkaRing ⊤) c))
    (hcoord : ∀ i : ι, θ (((okaCommPresheaf ι).germ ⊤ y trivial).hom
        (OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X i))) =
      ((okaCommPresheaf ι).germ ⊤ y trivial).hom
        (OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X i))) :
    θ = RingHom.id _ :=
  okaStalk_ringHom_ext hconst hcoord

/-- The generators really are in the maximal ideal, so the span statement is not the trivial
one with `⊤` on both sides: a normalised coordinate germ vanishes at the point. -/
theorem stalkCoord_mem_maximalIdeal (y : ι → ℂ) (i : ι) :
    stalkCoord y i ∈ maximalIdeal ((okaCommPresheaf ι).stalk y) := by
  rw [maximalIdeal_stalk_eq_span_stalkCoord]
  exact Ideal.subset_span ⟨i, rfl⟩

end

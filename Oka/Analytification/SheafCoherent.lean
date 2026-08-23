/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Free
import Oka.AnalyticSpace.Coherent
import Oka.AnalyticSpace.IdealSheaf
import Oka.Analytification.Sheaf

/-!
# The analytification of a finitely presented sheaf is coherent

`Oka/Analytification/Sheaf.lean` builds the analytification of a sheaf of modules on
`Spec (ℂ[x] ⧸ I)` and proves it **exact** — right exactness from the adjunction, left exactness
from the flatness of the stalk maps of the comparison morphism. This file draws the conclusion
GAGA consumes: **the analytification of a cokernel of finite free sheaves is coherent.**

## Why the statement is about a presentation and not about a coherent sheaf

The apparently stronger *"`M` coherent implies `M^an` coherent"* is **not** provable from what is
here, and the obstruction is not analytic. `SheafOfModules.IsCoherent` quantifies over every
object of the site and over every morphism `free L ⟶ M.over X`; downstairs those `L`-indexed
families are not in the image of the functor, so no argument of the form "apply the functor to
an upstairs presentation" reaches them. The classical route instead *gets* a presentation from
coherence, and on an affine scheme that is the passage from a coherent sheaf to a finitely
presented module.

**Half of that passage is now available and the half that is missing is the half this statement
needs.** `SheafOfModules.IsCoherent.isFinitePresentation` says a coherent sheaf is finitely
presented *on a covering*, and on `Spec A` that gives `M ≅ (Γ M)^~`
(`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent`). What it does not give is a
**global** presentation of `M` as a cokernel of finite free sheaves — equivalently, that `Γ M` is
a finitely presented `A`-module — and that is exactly what the theorem below consumes. The
missing step is the quasi-compactness argument on `Spec A` and it is not in this repository.

So the presented form is still the strongest statement available, and it is the form the
classical proof of GAGA uses anyway: coherent sheaves on `Spec A` are, by the affine dictionary,
cokernels of maps of finite frees.

## The proof, which is three transports and no new mathematics

`SheafOfModules.IsCoherent.cokernel` needs a source of finite type and a **coherent target**;
`SheafOfModules.IsCoherent.free` supplies the target, out of Oka's theorem
(`ComplexAnalytic.AnalyticSpace.isCoherent_free`), and the analytification of a free sheaf is
free on the same index type (`ComplexAnalytic.analytificationSheafFreeIso`). Right exactness
moves the cokernel across the functor. Nothing is computed.

## Main results

- `ComplexAnalytic.isCoherent_analytificationSheaf_cokernel`: **the analytification of the
  cokernel of a morphism of finite free sheaves is coherent.**
- `ComplexAnalytic.isCoherent_analytificationSheaf_cokernel_sectionsHom`: the same for the
  quotient of `𝒪_{Spec A}` by a finitely generated ideal sheaf, which is the shape a subscheme
  of `Spec (ℂ[x] ⧸ I)` arrives in.

## What is *not* here

**GAGA proper.** Agreement of `Hom` and of cohomology across analytification is untouched. The
negative on record — that faithfully flat descent from
`ComplexAnalytic.faithfullyFlat_stalkMap_analytificationToSpec` does not give it, because
`X^an ⟶ Spec A` misses every non-closed point — is *unmeasured*, and should be re-measured
before it is relied on.

## References

- [Jean-Pierre Serre, *Géométrie algébrique et géométrie analytique*][serre1956]
- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

noncomputable section

namespace ComplexAnalytic

variable {n k : ℕ} (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- **The analytification of the cokernel of a morphism of finite free sheaves is coherent.**

The target `(free K)^an` is free of the same rank, hence coherent by
`ComplexAnalytic.AnalyticSpace.isCoherent_free`, which is Oka's theorem in every finite rank;
the source `(free I)^an` is free, hence of finite type; and the analytification, being a left
adjoint, carries the cokernel to the cokernel. `SheafOfModules.IsCoherent.cokernel` then applies,
and note that it asks only for the *source* to be of finite type — no coherence of `(free I)^an`
is used. -/
theorem isCoherent_analytificationSheaf_cokernel {I K : Type u} [Finite I] [Finite K]
    (ψ : SheafOfModules.free (R := (Spec.locallyRingedSpaceObj (CommRingCat.of
          (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf) I ⟶
      SheafOfModules.free (R := (Spec.locallyRingedSpaceObj (CommRingCat.of
          (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).ringSheaf) K) :
    ((analytificationSheaf.{u} g).obj (cokernel ψ)).IsCoherent := by
  haveI := preservesColimits_analytificationSheaf.{u} g
  haveI : ((analytificationSheaf.{u} g).obj (SheafOfModules.free I)).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (M := SheafOfModules.free (R := (AnalyticSpace.analytification.{u}
        g).toLocallyRingedSpace.ringSheaf) I)
      (analytificationSheafFreeIso.{u} g I).symm
  haveI : (SheafOfModules.free (R := (AnalyticSpace.analytification.{u}
      g).toLocallyRingedSpace.ringSheaf) K).IsCoherent :=
    (AnalyticSpace.analytification.{u} g).isCoherent_free K
  haveI : ((analytificationSheaf.{u} g).obj (SheafOfModules.free K)).IsCoherent :=
    SheafOfModules.IsCoherent.of_iso
      (M := SheafOfModules.free (R := (AnalyticSpace.analytification.{u}
        g).toLocallyRingedSpace.ringSheaf) K)
      (analytificationSheafFreeIso.{u} g K).symm
  haveI : (cokernel ((analytificationSheaf.{u} g).map ψ)).IsCoherent :=
    SheafOfModules.IsCoherent.cokernel _
  exact SheafOfModules.IsCoherent.of_iso
    (M := cokernel ((analytificationSheaf.{u} g).map ψ))
    (PreservesCokernel.iso (analytificationSheaf.{u} g) ψ).symm

/-- **The analytification of the quotient of `𝒪_{Spec A}` by a finitely generated ideal sheaf is
coherent.**

`AlgebraicGeometry.LocallyRingedSpace.sectionsHom f : 𝒪^I ⟶ 𝒪` is the map whose cokernel is that
quotient, and it is a morphism of finite free sheaves once `𝒪` is read as `free PUnit`
(`SheafOfModules.freePUnitIso`); composing with an isomorphism does not change the cokernel
(`CategoryTheory.Limits.cokernelCompIsIso`). This is the shape in which a closed subscheme of
`Spec (ℂ[x] ⧸ I)` presents its structure sheaf. -/
theorem isCoherent_analytificationSheaf_cokernel_sectionsHom {I : Type u} [Finite I]
    (f : I → (Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).presheaf.obj
      (Opposite.op ⊤)) :
    ((analytificationSheaf.{u} g).obj (cokernel
      ((Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).sectionsHom
          f))).IsCoherent := by
  haveI : ((analytificationSheaf.{u} g).obj (cokernel
      ((Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).sectionsHom f ≫
          (SheafOfModules.freePUnitIso).inv))).IsCoherent :=
    isCoherent_analytificationSheaf_cokernel.{u} g _
  exact SheafOfModules.IsCoherent.of_iso
    (M := (analytificationSheaf.{u} g).obj (cokernel
      ((Spec.locallyRingedSpaceObj (CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin n)) ℂ ⧸ presentationIdeal.{u} g))).sectionsHom f ≫
          (SheafOfModules.freePUnitIso).inv)))
    ((analytificationSheaf.{u} g).mapIso (cokernelCompIsIso _ _))

end ComplexAnalytic

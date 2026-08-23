/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.CoherentFree

/-!
# Non-vacuity of the two affine steps

`AlgebraicGeometry.Scheme.Modules.exists_finset_basicOpen_generatingSections` and
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen` are hypothetical
statements about a sheaf of modules on a `Spec`, and this repository is short of those: the note
in `OkaTest/CoherentPresentation.lean` records that **no sheaf on a `Spec` is proved coherent
here**, since every coherent sheaf this development exhibits lives on an analytic space.

Both statements are therefore stated under hypotheses weaker than coherence —
`SheafOfModules.IsFiniteType` and `SheafOfModules.IsQuasicoherent` — and this file is the reason:
at the weaker hypotheses there **is** a witness, and it is not a degenerate one.

## The witness

`𝒪_{Spec A} ⧸ (x)` for `A = ℂ[x, y] ⧸ (xy)`, the sheaf `OkaTest/CoherentFree.lean` builds to test
`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel_sectionsHom`, read here on the
*algebraic* side rather than after analytification. It is:

* **quasicoherent**, because it is the cokernel of a map of finite free sheaves and so has a
  global `SheafOfModules.Presentation` (`SheafOfModules.presentationOfIsCokernelFree`);
* **of finite type**, because it is a quotient of `𝒪_{Spec A}`;
* **not the zero sheaf** (`OkaTest.AffineSections.not_isZero_cokernel_specXHom`, from
  `OkaTest.CoherentFree.not_isZero_cokernel_specXFamily`, whose content is that `x` vanishes at
  the origin of the node);
* **a quotient of `𝒪_{Spec A}` by neither everything nor nothing**: its presenting map,
  multiplication by `x`, is not an epimorphism — which is what the nonzero cokernel says — and it
  is also not the zero map (`OkaTest.AffineSections.specXHom_ne_zero`), so the relations half of
  the presentation is doing something. The two are independent: if the presenting map were zero
  the cokernel would be `free PUnit`, which is also not zero.

  What is proved is that the *map* is nonzero, not that its image is a nonzero subobject; the
  latter follows in an abelian category and is not formalised here.

**One thing is not asserted, and deliberately.**

*It is not asserted to be non-free.* `OkaTest/CoherentFree.lean`, which this file imports, says of
the same sheaf that nothing there shows it is not a free sheaf of modules — that this is true but
is an annihilator argument it does not make. Nothing here makes it either, and a non-epimorphic
presenting map does not imply it: a free sheaf can be presented by a map that is not an
epimorphism.

So neither statement is about the zero sheaf, and neither is exercised only at the structure sheaf
itself.

## What is *not* checked here

* **The coherent corollary
  `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen_of_isCoherent` is
  not instantiated**, for exactly the reason `OkaTest/CoherentPresentation.lean` gives about
  `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent`: nothing here proves a sheaf
  on a `Spec` coherent. That will change when the structure sheaf of a noetherian `Spec` is shown
  coherent, and not before.
* **Nothing here computes the `Finset` of
  `exists_finset_basicOpen_generatingSections`.** The statement is existential and the witness
  above is globally generated, so `{1}` would do; what the instantiation checks is that the
  hypothesis is inhabited away from the zero sheaf, not that the conclusion is sharp. The
  conclusion is sharp only for a sheaf which is *not* globally generated, and this repository
  exhibits none on a `Spec`.
* **The step the two are stated for is still missing**, namely `Module.Finite Γ(Spec R, D(g))
  Γ(M, D(g))`; see the module docstring of `Oka/AlgebraicGeometry/Modules/Tilde.lean`. So no
  statement here is that `Γ M` is a finitely generated `A`-module, and none should be read that
  way.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite PrimeSpectrum SheafOfModules
open OkaTest.CoherentFree ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.AffineSections

/-- `A = ℂ[x, y] ⧸ (xy)`, as a `CommRingCat`. -/
abbrev nodeA : CommRingCat.{u} :=
  CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸ presentationIdeal.{u} nodeG.{u})

/-- **Multiplication by `x` on `𝒪_{Spec A}`, as a map of finite free sheaves.**

`AlgebraicGeometry.LocallyRingedSpace.sectionsHom` lands in `SheafOfModules.unit`; composing with
`SheafOfModules.freePUnitIso.inv` reads that as `free PUnit`, which is what
`SheafOfModules.presentationOfIsCokernelFree` needs on both sides. This is the same shuffle
`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel_sectionsHom` performs, and
`CategoryTheory.Limits.cokernelCompIsIso` is what says the cokernel is unchanged by it. -/
abbrev specXHom : free (R := (nodeSpec.{u}).ringSheaf) PUnit.{u + 1} ⟶
    free (R := (nodeSpec.{u}).ringSheaf) PUnit.{u + 1} :=
  (nodeSpec.{u}).sectionsHom specXFamily.{u} ≫ SheafOfModules.freePUnitIso.inv

/-- **The witness is a module on `Spec A` in Mathlib's sense**, and not merely a sheaf of modules
over this repository's `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`. The two ring sheaves
cross at default transparency, which is what lets the statements below be applied at all. -/
example : (Spec nodeA.{u}).Modules := cokernel specXHom.{u}

/-- **`𝒪_{Spec A} ⧸ (x)` is quasicoherent**, because a cokernel of a map of finite free sheaves
has a global presentation. -/
instance isQuasicoherent_cokernel_specXHom : (cokernel specXHom.{u}).IsQuasicoherent :=
  (presentationOfIsCokernelFree specXHom.{u} (cokernel.π specXHom.{u})
    (cokernel.condition _) (cokernelIsCokernel _)).isQuasicoherent

/-- **And of finite type**, being a quotient of `𝒪_{Spec A}`. -/
instance isFiniteType_cokernel_specXHom : (cokernel specXHom.{u}).IsFiniteType :=
  IsFiniteType.of_epi (M := free (R := (nodeSpec.{u}).ringSheaf) PUnit.{u + 1})
    (cokernel.π specXHom.{u})

/-- **And not the zero sheaf**, which is what stops both instantiations below from being about
nothing. `OkaTest.CoherentFree.not_isZero_cokernel_specXFamily` is the statement before the
`free PUnit` shuffle, and `CategoryTheory.Limits.cokernelCompIsIso` carries it across. -/
theorem not_isZero_cokernel_specXHom : ¬ IsZero (cokernel specXHom.{u}) := by
  intro h
  exact not_isZero_cokernel_specXFamily.{u}
    ((cokernelCompIsIso ((nodeSpec.{u}).sectionsHom specXFamily.{u})
      (SheafOfModules.freePUnitIso (R := (nodeSpec.{u}).ringSheaf)).inv).isZero_iff.1 h)

/-- **`x` is not zero in `A = ℂ[x, y] ⧸ (xy)`.**

If it were, `x` would lie in `(xy)`, so `x = c * x * y` for some `c`; evaluating at the point
`(1, 0)` of the node — `OkaTest.Analytification.nodePtX`, kept in the development for exactly this
kind of separation — gives `1 = 0`. -/
theorem specX_ne_zero : specX.{u} ≠ 0 := by
  intro h
  have hmem : MvPolynomial.X (R := ℂ) (ULift.up 0) ∈ presentationIdeal.{u} nodeG.{u} :=
    (Ideal.Quotient.eq_zero_iff_mem (I := presentationIdeal.{u} nodeG.{u})).1 h
  rw [presentationIdeal_nodeG.{u}, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hev := congrArg (MvPolynomial.eval nodePtX.{u}) hc
  simp [nodePoly] at hev

/-- **The global section `x` of `𝒪_{Spec A}` is nonzero.**

`AlgebraicGeometry.StructureSheaf.globalSectionsIso` says `A → Γ(Spec A, ⊤)` is an isomorphism,
hence injective, and `specXFamily` is that map applied to `specX`. The `Algebra` instance lives at
the `Spec.structureSheaf` spelling only, which is why this goes through the iso rather than naming
the algebra map at the locally ringed space spelling — the same seam `specXFamily`'s own docstring
records. -/
theorem specXFamily_ne_zero (i : PUnit.{u + 1}) : specXFamily.{u} i ≠ 0 := by
  intro h
  refine specX_ne_zero.{u} ?_
  have hinj := (ConcreteCategory.bijective_of_isIso
    (StructureSheaf.globalSectionsIso
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸
        presentationIdeal.{u} nodeG.{u}))).hom).1
  rw [StructureSheaf.globalSectionsIso_hom] at hinj
  apply hinj
  rw [map_zero]
  exact h

/-- **The presenting map is not the zero map**, so the relations half of the presentation is doing
something.

This is independent of `not_isZero_cokernel_specXHom`: if the presenting map were zero the cokernel
would be `free PUnit`, which is also not zero. Composing with the iso `freePUnitIso.inv` is
harmless, so it reduces to `AlgebraicGeometry.LocallyRingedSpace.sectionsHom specXFamily ≠ 0`, and
`freeHomEquiv_sectionsHom` pins that morphism down as the section `x` over `⊤`. -/
theorem specXHom_ne_zero : specXHom.{u} ≠ 0 := by
  intro h
  have h0 : (nodeSpec.{u}).sectionsHom specXFamily.{u} = 0 := by
    have h1 := congrArg (fun φ ↦ φ ≫ (SheafOfModules.freePUnitIso
      (R := (nodeSpec.{u}).ringSheaf)).hom) h
    simpa [specXHom] using h1
  have h2 := (nodeSpec.{u}).freeHomEquiv_sectionsHom specXFamily.{u} PUnit.unit
  rw [h0] at h2
  have h3 := congrArg (fun s ↦ PresheafOfModules.sections.eval s
    (op (⊤ : Opens ↑(nodeSpec.{u}).toPresheafedSpace))) h2
  simp at h3
  exact specXFamily_ne_zero.{u} PUnit.unit h3.symm

/-! ### The two statements, at that witness -/

/-- **A finite family of distinguished opens spanning the unit ideal, with finitely many
generators over each**, for `𝒪_{Spec A} ⧸ (x)`. -/
example : ∃ s : Finset nodeA.{u},
    Ideal.span (s : Set nodeA.{u}) = ⊤ ∧
      ∀ g ∈ s, ∃ σ : (((cokernel specXHom.{u} : (Spec nodeA.{u}).Modules)).over
        (PrimeSpectrum.basicOpen g)).GeneratingSections, σ.IsFiniteType :=
  haveI : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsFiniteType :=
    isFiniteType_cokernel_specXHom.{u}
  Scheme.Modules.exists_finset_basicOpen_generatingSections.{u} _

/-- **Restriction to `D(g)` is the localisation away from `g`**, for `𝒪_{Spec A} ⧸ (x)` and any
`g`. Quasicoherence is the whole hypothesis; coherence is not available here and is not needed. -/
example (g : nodeA.{u}) :
    IsLocalizedModule.Away g
      (Scheme.Modules.sectionsToBasicOpen.{u}
        (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules) g).hom :=
  haveI : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsQuasicoherent :=
    isQuasicoherent_cokernel_specXHom.{u}
  Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen.{u} _ g

/-- **At `g = x` the localisation above is not the trivial one.** The germ of `x` at the prime
under the origin of the node lies in the maximal ideal there, so `x` is not a unit in that stalk,
so that prime is not in `D(x)` and `D(x) ≠ ⊤`. Without this the statement above would be open to
the reading that every `D(g)` in sight is the whole space. -/
example : ((nodeSpec.{u}).presheaf.germ ⊤
    ((analytificationToSpec.{u} nodeG.{u}).base anOrigin.{u}) trivial (specXFamily.{u} PUnit.unit))
      ∈ IsLocalRing.maximalIdeal ((nodeSpec.{u}).presheaf.stalk
        ((analytificationToSpec.{u} nodeG.{u}).base anOrigin.{u})) :=
  germ_specXFamily_mem.{u} PUnit.unit

end OkaTest.AffineSections

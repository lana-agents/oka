/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.CoherentFree

/-!
# Non-vacuity of the affine-locality argument

`AlgebraicGeometry.Scheme.Modules.exists_finset_basicOpen_generatingSections` and
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen` are hypothetical
statements about a sheaf of modules on a `Spec`, and this file is what makes them not vacuous.

Every statement on that line is made under hypotheses weaker than coherence —
`SheafOfModules.IsFiniteType`, `SheafOfModules.IsQuasicoherent` and
`SheafOfModules.IsFinitePresentation` — because those are what the proofs use, and this file is
the reason it is worth doing: at the weaker hypotheses there **is** a witness, and it is not a
degenerate one. That covers the whole argument twice over, from its two local steps to
`AlgebraicGeometry.Scheme.Modules.module_finite_moduleSpecΓFunctor_obj_of_isFiniteType` and to
`AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ_of_isFinitePresentation`.

**The paragraph that used to stand here gave a second reason for the weak hypotheses, and it is
retired.** It said they were also *forced*, because no sheaf on a `Spec` was proved coherent
anywhere in this repository. `AlgebraicGeometry.isCoherentStructureSheaf_spec` now proves
`𝒪_{Spec A}` coherent for noetherian `A`, and
`OkaTest.AffineSections.isCoherent_cokernel_specXHom` below proves the witness of this very file
coherent. So coherence is available and the statements stay at quasicoherence on the merits.

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

* **The bullet that used to stand here said the coherent corollary
  `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen_of_isCoherent` was
  not instantiated**, because nothing proved a sheaf on a `Spec` coherent, and that *"that will
  change when the structure sheaf of a noetherian `Spec` is shown coherent, and not before"*. It
  has changed: `AlgebraicGeometry.isCoherentStructureSheaf_spec`, and the corollary is
  instantiated below at the same witness. What is *not* checked is that the coherent corollary
  reaches anything the quasicoherent one does not — it cannot, being the same statement with a
  stronger hypothesis.
* **Nothing here computes the `Finset` of
  `exists_finset_basicOpen_generatingSections`.** The statement is existential and the witness
  above is globally generated, so `{1}` would do; what the instantiation checks is that the
  hypothesis is inhabited away from the zero sheaf, not that the conclusion is sharp. The
  conclusion is sharp only for a sheaf which is *not* globally generated, and this repository
  exhibits none on a `Spec`.
* **`Γ M` *is* shown finitely presented below, and not from the same hypotheses.**
  `Module.FinitePresentation` needs a `SheafOfModules.Presentation`, which is strictly more than
  quasicoherent-of-finite-type — see the module docstring of
  `Oka/AlgebraicGeometry/Modules/Tilde.lean` for why it has to be, since the statement is *false*
  at the weaker hypotheses. The witness has one because it was **built** as a cokernel of finite
  free sheaves, not because one was derived; **nothing here produces a presentation for a sheaf
  that is merely of finite type**, which is the gap that makes the finite-presentation statements
  weaker in reach than the finite-type ones even though they are stronger in conclusion.

  Both forms are instantiated below: the global one,
  `AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ`, and Mathlib's class
  `SheafOfModules.IsFinitePresentation`, which the witness satisfies through
  `SheafOfModules.Presentation.isFinitePresentation` — its presentation is global, so the
  covering is the trivial one. **So the local statement's witness here is not local**, and what
  the instantiation checks is that its hypothesis is inhabited at all, not that it is inhabited
  by something the global statement could not reach.
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

/-- **And coherent**, which it was not known to be when this file was written.

`SheafOfModules.IsCoherent.cokernel` at a source of finite type and a **coherent** target: the
target is `free PUnit` on `Spec A`, coherent by `AlgebraicGeometry.Scheme.isCoherent_free` out of
`AlgebraicGeometry.isCoherentStructureSheaf_spec`, since `A` is noetherian. The `haveI` is at the
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf` spelling and the theorem supplying it is at
`AlgebraicGeometry.Scheme.ringCatSheaf`; the two agree at default transparency, which is the same
crossing the ascriptions below perform.

**This is not what the statements in this file are proved from**, and deliberately: they are
stated at quasicoherence, which is weaker and is what their proofs use. It is here so that the
coherent corollary can be instantiated too. -/
instance isCoherent_cokernel_specXHom : (cokernel specXHom.{u}).IsCoherent :=
  haveI : (free (R := (nodeSpec.{u}).ringSheaf) PUnit.{u + 1}).IsCoherent :=
    (Spec nodeA.{u}).isCoherent_free _
  SheafOfModules.IsCoherent.cokernel specXHom.{u}

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
`(1, 0)` of the node — `ComplexAnalytic.nodePtX` (`OkaTest/Analytification.lean`), kept in the
development for exactly this kind of separation — gives `1 = 0`. -/
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
`g`. Quasicoherence is the whole hypothesis and coherence is not needed; it is available, and the
example just below applies the corollary that asks for it. -/
example (g : nodeA.{u}) :
    IsLocalizedModule.Away g
      (Scheme.Modules.sectionsToBasicOpen.{u}
        (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules) g).hom :=
  haveI : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsQuasicoherent :=
    isQuasicoherent_cokernel_specXHom.{u}
  haveI : Epi (cokernel.π specXHom.{u}) := coequalizer.π_epi
  Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen.{u} _ g

/-- **The coherent corollary, at the same witness.**

`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen_of_isCoherent`, which
this file recorded as uninstantiable because nothing proved a sheaf on a `Spec` coherent. It is
weaker than the statement above — it is that statement with a stronger hypothesis — and it is
instantiated here only because the record said it could not be. Not *strictly* weaker: that would
need coherence to be genuinely stronger at some sheaf, and nothing here shows it. -/
example (g : nodeA.{u}) :
    IsLocalizedModule.Away g
      (Scheme.Modules.sectionsToBasicOpen.{u}
        (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules) g).hom :=
  haveI : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsCoherent :=
    isCoherent_cokernel_specXHom.{u}
  haveI : Epi (cokernel.π specXHom.{u}) := coequalizer.π_epi
  Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen_of_isCoherent.{u} _ g

/-- **At `g = x` the localisation above is not the trivial one.** The germ of `x` at the prime
under the origin of the node lies in the maximal ideal there, so `x` is not a unit in that stalk,
so that prime is not in `D(x)` and `D(x) ≠ ⊤`. Without this the statement above would be open to
the reading that every `D(g)` in sight is the whole space. -/
example : ((nodeSpec.{u}).presheaf.germ ⊤
    ((analytificationToSpec.{u} nodeG.{u}).base anOrigin.{u}) trivial (specXFamily.{u} PUnit.unit))
      ∈ IsLocalRing.maximalIdeal ((nodeSpec.{u}).presheaf.stalk
        ((analytificationToSpec.{u} nodeG.{u}).base anOrigin.{u})) :=
  germ_specXFamily_mem.{u} PUnit.unit

/-- **Finitely many global sections generating it as a sheaf generate its global sections as a
module**, at this witness.

The generating family is the tautological one of `free PUnit` pushed along `cokernel.π`, so the
sheaf is generated by a single global section and `Γ` is a cyclic `A`-module — which is what
`𝒪_{Spec A} ⧸ (x)` should be, and is the check that the hypothesis of
`AlgebraicGeometry.Scheme.Modules.module_finite_moduleSpecΓFunctor_obj` is inhabited here rather
than merely stateable.

Two hypotheses are handed over rather than searched for. What reproduces, and nothing is inferred
from it:

* left to search, `SheafOfModules.GeneratingSections.ofEpi` fails at `Epi (cokernel.π specXHom)`
  with **`(deterministic) timeout at typeclass`, 20000 heartbeats** — so the first thing a reader
  sees is a budget message and not a synthesis failure. Raised to 400000 it runs for about
  eighteen seconds and then fails for real;
* `Finite σ.I` fails likewise, and the `let` is what lets `σ.I` reduce to `PUnit` first;
* both are closed immediately by the terms `CategoryTheory.Limits.coequalizer.π_epi` and
  `inferInstanceAs (Finite PUnit)`.

**Why search does not get there is not established**, and no explanation should be read into this
note. In particular it is *not* transparency: `with_reducible exact coequalizer.π_epi` compiles in
the `haveI` position. -/
example : Module.Finite nodeA.{u}
    ((moduleSpecΓFunctor (R := nodeA.{u})).obj
      (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules)) :=
  haveI : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsQuasicoherent :=
    isQuasicoherent_cokernel_specXHom.{u}
  haveI : Epi (cokernel.π specXHom.{u}) := coequalizer.π_epi
  let σ : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).GeneratingSections :=
    @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _
      (freeGeneratingSections (R := (nodeSpec.{u}).ringSheaf) PUnit.{u + 1})
      (cokernel.π specXHom.{u}) coequalizer.π_epi
  haveI : Finite σ.I := inferInstanceAs (Finite PUnit.{u + 1})
  Scheme.Modules.module_finite_moduleSpecΓFunctor_obj σ

/-! ### The change of site, and the conclusion

`AlgebraicGeometry.Scheme.Modules.module_finite_sections_basicOpen` and
`AlgebraicGeometry.Scheme.Modules.module_finite_moduleSpecΓFunctor_obj_of_isFiniteType` are the
two statements that finish the affine-locality argument, and they are instantiated here at the
same witness for the same reason as everything above it. -/

/-- **`Γ(M, D(x))` is a finite `Γ(Spec A, D(x))`-module**, at `M = 𝒪_{Spec A} ⧸ (x)` and `g = x`.

This is the change of site, at the distinguished open the rest of the file is about: the
neighbouring statement `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen`
is instantiated at every `g`, and `OkaTest.CoherentFree.germ_specXFamily_mem` above says that at
`g = x` the open is not the whole space, so this is not the `⊤` case in disguise.

The generating family over `D(x)` is the global one pushed to the slice site by
`SheafOfModules.GeneratingSections.map` along `SheafOfModules.overFunctor` — the same construction
`SheafOfModules.GeneratingSections.localGeneratorsData` uses — so the sheaf is generated over
`D(x)` by one section. **Naming it in a `let` with its type written out is load-bearing**: inlined
into the final `exact`, elaboration reaches `(deterministic) timeout at whnf, 200000 heartbeats`.

`Epi (cokernel.π specXHom)` and `Finite σ.I` are handed over rather than searched for, for the
reason the previous example records. -/
example :
    Module.Finite Γ(Spec nodeA.{u}, PrimeSpectrum.basicOpen specX.{u})
      Γ((cokernel specXHom.{u} : (Spec nodeA.{u}).Modules),
        PrimeSpectrum.basicOpen specX.{u}) := by
  haveI : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsQuasicoherent :=
    isQuasicoherent_cokernel_specXHom.{u}
  haveI : Epi (cokernel.π specXHom.{u}) := coequalizer.π_epi
  let σ : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).GeneratingSections :=
    @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _
      (freeGeneratingSections (R := (nodeSpec.{u}).ringSheaf) PUnit.{u + 1})
      (cokernel.π specXHom.{u}) coequalizer.π_epi
  haveI : Finite σ.I := inferInstanceAs (Finite PUnit.{u + 1})
  have hpc : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overFunctor (Spec nodeA.{u}).ringCatSheaf
        (PrimeSpectrum.basicOpen specX.{u})) := inferInstance
  let τ : ((cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).over
      (PrimeSpectrum.basicOpen specX.{u})).GeneratingSections :=
    σ.map (SheafOfModules.overFunctor (Spec nodeA.{u}).ringCatSheaf
      (PrimeSpectrum.basicOpen specX.{u})) (Iso.refl _)
  haveI : Finite τ.I := inferInstanceAs (Finite σ.I)
  exact Scheme.Modules.module_finite_sections_basicOpen
    (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules) specX.{u} τ

/-- **`Γ M` is a finite `A`-module**, at `M = 𝒪_{Spec A} ⧸ (x)`, from quasicoherence and finite
type alone.

This is the affine-locality argument assembled, and it is a different check from the example
above it even though the conclusion looks the same as that one's: there the generating family was
*supplied* and the statement was
`AlgebraicGeometry.Scheme.Modules.module_finite_moduleSpecΓFunctor_obj`; here nothing is supplied
but the two instances, and the family is produced inside the proof by
`AlgebraicGeometry.Scheme.Modules.exists_finset_basicOpen_generatingSections`. **It is the
hypothesis pair that is being checked to be inhabited**, not the conclusion.

Both instances are named rather than searched for, as everywhere else in this file. -/
example : Module.Finite nodeA.{u}
    ((moduleSpecΓFunctor (R := nodeA.{u})).obj
      (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules) : Type u) :=
  haveI : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsQuasicoherent :=
    isQuasicoherent_cokernel_specXHom.{u}
  haveI : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsFiniteType :=
    isFiniteType_cokernel_specXHom.{u}
  Scheme.Modules.module_finite_moduleSpecΓFunctor_obj_of_isFiniteType _

/-! ### Finite presentation

Both finite-presentation statements ask for strictly more than the two instances above — a
`SheafOfModules.Presentation`, global for
`AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ` and on a covering for
`AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ_of_isFinitePresentation` — and that is not
a convenience: at quasicoherent-plus-finite-type the conclusion is false, for the reason recorded
in the module docstring of `Oka/AlgebraicGeometry/Modules/Tilde.lean`. So both hypotheses need
their own non-vacuity check, and these are they. -/

/-- **The witness has a finite global presentation.**

`SheafOfModules.presentationOfIsCokernelFree` is already how its `IsQuasicoherent` instance is
built, and both index types are `PUnit`, so the two `IsFiniteType` fields are `Finite PUnit`. They
are supplied rather than searched for, as everywhere else in this file. -/
def specXPresentation : (cokernel specXHom.{u}).Presentation :=
  presentationOfIsCokernelFree specXHom.{u} (cokernel.π specXHom.{u})
    (cokernel.condition _) (cokernelIsCokernel _)

instance isFinite_specXPresentation : (specXPresentation.{u}).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩

/-- **`Γ M` is a finitely presented `A`-module**, at `M = 𝒪_{Spec A} ⧸ (x)`.

**`A` is noetherian, so the conclusion is not surprising *here*** — over a noetherian ring finite
and finitely presented coincide, and `Module.Finite nodeA (Γ M)` is already proved above. What
this checks is that the *hypothesis* is inhabited: that a sheaf on a `Spec` in this repository
carries a finite global `SheafOfModules.Presentation` at all. Without it
`AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ` would be a statement with no witness here
— the situation `OkaTest/CoherentPresentation.lean` **used** to record for
`SheafOfModules.IsCoherent`, and which it now records in the past tense, because
`AlgebraicGeometry.isCoherentStructureSheaf_spec` supplied the missing witness and
`OkaTest.AffineSections.isCoherent_cokernel_specXHom` above instantiates it at this very sheaf.

The `IsFinite` instance is supplied positionally, and neither `haveI` nor `letI` of exactly
`(specXPresentation.{u}).IsFinite` in scope is enough — both leave `failed to synthesize
specXPresentation.IsFinite`. Why is not established here and no explanation should be read into
this note; both were run. -/
example : Module.FinitePresentation nodeA.{u}
    ((moduleSpecΓFunctor (R := nodeA.{u})).obj
      (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules) : Type u) :=
  @Scheme.Modules.finitePresentation_Γ _ _ specXPresentation.{u} isFinite_specXPresentation.{u}

/-- **And it is of finite presentation in Mathlib's sense**, which is the hypothesis of the
*local* statement.

`SheafOfModules.IsFinitePresentation` asks for a finite presentation over the members of some
covering; `SheafOfModules.Presentation.isFinitePresentation` supplies it from the global one, on
the trivial covering. So this witness does not exercise the locality — see the module docstring —
and what it checks is that the class is inhabited on a `Spec` in this repository at all. That
used to be the point of contrast with `SheafOfModules.IsCoherent`, which
`OkaTest/CoherentPresentation.lean` recorded as inhabited nowhere on a `Spec`; the contrast is
gone, because `AlgebraicGeometry.isCoherentStructureSheaf_spec` inhabits it and
`OkaTest.AffineSections.isCoherent_cokernel_specXHom` does so at this very sheaf.

The universes and the `IsFinite` instance are both supplied positionally, for the reason recorded
on the previous example: neither is inferred, and `haveI` does not help. -/
instance isFinitePresentation_cokernel_specXHom :
    (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).IsFinitePresentation :=
  @SheafOfModules.Presentation.isFinitePresentation.{u, u, u} _ _ _ _ _ _ _ _ _ _
    specXPresentation.{u} isFinite_specXPresentation.{u}

/-- **`Γ M` is a finitely presented `A`-module from the *local* hypothesis**, at
`M = 𝒪_{Spec A} ⧸ (x)`.

`AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ_of_isFinitePresentation` is the conclusion
of the affine-locality argument run on presentations, and this is the same statement as the
example above with the hypothesis weakened from a presentation in hand to Mathlib's class. Here
the two coincide, because the instance above is built from that very presentation; what is being
checked is that the local statement has a witness, not that it has one the global statement
misses. -/
example : Module.FinitePresentation nodeA.{u}
    ((moduleSpecΓFunctor (R := nodeA.{u})).obj
      (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules) : Type u) :=
  Scheme.Modules.finitePresentation_Γ_of_isFinitePresentation _

/-! ### The converse, and why this example is circular

`AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation` recovers a finite global
`SheafOfModules.Presentation` from `Module.FinitePresentation A (Γ M)` for a quasicoherent `M`,
which is the direction that closes the affine dictionary. **The example below is not a test of it
in the sense the ones above are tests**, and it is worth saying exactly why rather than letting a
green example imply more than it checks.

The witness `𝒪_{Spec A} ⧸ (x)` was *built* as a cokernel of finite free sheaves — that is what
`OkaTest.AffineSections.specXPresentation` is — so it had a finite global presentation before any
theorem on this line was applied to it, and its `Module.FinitePresentation A (Γ M)` was derived
*from* that presentation. So the conclusion of the theorem below is one of its own ancestors: the
example checks that the statement typechecks and that its hypotheses are simultaneously
inhabited, and **it does not check that the theorem produces a presentation that was not already
there.**

**A non-circular witness would be a quasicoherent sheaf on a `Spec` whose global sections are
known finitely presented for some reason other than a presentation in hand**, and the clause here
used to say this repository had none, the nearest thing being a coherent sheaf on a noetherian
`Spec`, which `OkaTest/CoherentPresentation.lean` recorded as unavailable. **That is retired, and
by this very sheaf.** `OkaTest.AffineSections.isCoherent_cokernel_specXHom` above proves
`cokernel specXHom` coherent out of `AlgebraicGeometry.isCoherentStructureSheaf_spec`, without
using `OkaTest.AffineSections.specXPresentation` or anything downstream of it, and
`OkaTest/CoherentPresentation.lean` feeds that coherence to
`AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent`. So a
non-circular route to a finite global presentation of this sheaf exists.

**The example below is still circular and is still worth reading as such**, because it is stated
at `SheafOfModules.IsFinitePresentation` and takes that hypothesis from the presentation built by
hand here, not from coherence. What has changed is that the circularity is now a property of
*this* instantiation rather than of the repository.
-/

/-- **The witness has a finite global presentation recovered from its module of sections.**

Circular, and the section docstring says how: the hypothesis this consumes is supplied on the
line below by `AlgebraicGeometry.Scheme.Modules.finitePresentation_Γ_of_isFinitePresentation`,
which was itself proved from the presentation this produces. Included because the theorem should
have at least one application in the tree, and because a statement with no instantiation at all is
how an unusable hypothesis goes unnoticed — not because it is evidence about the theorem. -/
example : ∃ P : (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules).Presentation, P.IsFinite :=
  haveI : Module.FinitePresentation nodeA.{u}
      ((moduleSpecΓFunctor (R := nodeA.{u})).obj
        (cokernel specXHom.{u} : (Spec nodeA.{u}).Modules) : Type u) :=
    Scheme.Modules.finitePresentation_Γ_of_isFinitePresentation _
  Scheme.Modules.exists_isFinite_presentation _

end OkaTest.AffineSections

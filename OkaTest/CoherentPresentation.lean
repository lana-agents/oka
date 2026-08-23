/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.AffineSections
import OkaTest.CoherentFree

/-!
# Non-vacuity of "coherent implies locally finitely presented"

`SheafOfModules.IsCoherent.isFinitePresentation` has a hypothesis that could in principle be
satisfied by nothing, and a conclusion that the zero sheaf satisfies. This file instantiates it,
at the three coherent sheaves `OkaTest/CoherentFree.lean` already builds and proves nonzero, so
that neither reading is available:

* a free sheaf of rank **two** on the node — not rank one, and not `ℂ^n`;
* the analytification of `𝒪_{Spec A}²` for `A = ℂ[x, y] ⧸ (xy)`;
* the analytification of `𝒪_{Spec A} ⧸ (x)`, which is the one with a **presenting map that is
  not an epimorphism** — the sheaf whose relations are not empty, and so the only one of the
  three at which the relations half of the statement is doing anything.

Each is paired with the corresponding `not_isZero_…` from that file, which is what rules out the
conclusion being about the zero sheaf.

## The affine half, which used to be untested

The clause that used to stand here said that
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent` — a coherent
`𝒪_{Spec R}`-module is `(Γ M)^~` — was instantiated nowhere, because **this repository proved no
sheaf on a `Spec` to be coherent**, and predicted that the first thing to instantiate it would be
the coherence of an algebraic structure sheaf. **That is exactly what happened.**
`AlgebraicGeometry.isCoherentStructureSheaf_spec` proves `𝒪_{Spec A}` coherent for noetherian
`A`, and `OkaTest/SpecCoherent.lean` instantiates the affine statement at `𝒪_{Spec A} ⧸ (x)` for
`A = ℂ[x, y] ⧸ (xy)` — a nonzero proper quotient, not a free sheaf and not the zero sheaf.

What is still true of *this* file's three witnesses is narrower, and it is why they are
unchanged: **they are analytifications**, which live on the analytic space and not on `Spec A`, so
none of them exercises the affine dictionary. The witness that does is in
`OkaTest/SpecCoherent.lean`.

## The two statements above the affine dictionary, and they are exercised here

`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent` has two consequences that this
file adds, and until `AlgebraicGeometry.isCoherentStructureSheaf_spec` landed **neither could be
instantiated anywhere**, for the reason the paragraph above retires:

* `AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent` — a coherent
  `𝒪_{Spec R}`-module has a finite **global** `SheafOfModules.Presentation`;
* `ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent` — hence its analytification is
  coherent, which is the statement this whole line exists to reach.

**Both are instantiated at the end of this file**, at `𝒪_{Spec A} ⧸ (x)` for
`A = ℂ[x, y] ⧸ (xy)` — coherent by `OkaTest.AffineSections.isCoherent_cokernel_specXHom` out of
`AlgebraicGeometry.isCoherentStructureSheaf_spec`, and not the zero sheaf by
`OkaTest.AffineSections.not_isZero_cokernel_specXHom`. So the second of them is the first place in
this repository where *"the analytification of a **coherent** sheaf is coherent"* is applied to
anything, rather than being a corollary with an uninhabited hypothesis.

**This does not make the presented form redundant.** It is still the weaker hypothesis and still
the one the three witnesses below satisfy; what has changed is that the coherent form is no longer
uninstantiable, which is what its module docstring in `Oka/Analytification/SheafCoherent.lean`
used to record.

## What is also not tested

That a sheaf which is *not* coherent fails to be finitely presented. Nothing here exhibits a
sheaf of modules that is not of finite presentation, so the conclusion is not shown to be a
restriction. What is shown is that the hypothesis is inhabited away from the degenerate cases and
that the conclusion is not about the zero sheaf.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Limits ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.CoherentPresentation

open OkaTest.AffineSections OkaTest.CoherentFree

/-! ### A free sheaf of rank two on the node -/

/-- **A free sheaf of rank two on the node is of finite presentation.** -/
example : (SheafOfModules.free (R := AnalyticSpace.node.{u}.toLocallyRingedSpace.ringSheaf)
    (ULift.{u} (Fin 2))).IsFinitePresentation :=
  haveI := AnalyticSpace.node.{u}.isCoherent_free (ULift.{u} (Fin 2))
  SheafOfModules.IsCoherent.isFinitePresentation.{u} _

/-- **And quasicoherent.** It is not the zero sheaf, by
`OkaTest.CoherentFree.not_isZero_free_node`. -/
example : (SheafOfModules.free (R := AnalyticSpace.node.{u}.toLocallyRingedSpace.ringSheaf)
    (ULift.{u} (Fin 2))).IsQuasicoherent :=
  haveI := AnalyticSpace.node.{u}.isCoherent_free (ULift.{u} (Fin 2))
  SheafOfModules.IsCoherent.isQuasicoherent.{u} _

/-! ### The analytification of `A²` for `A = ℂ[x, y] ⧸ (xy)` -/

/-- **The analytification of `𝒪_{Spec A}²` is of finite presentation.** It is not the zero
sheaf, by `OkaTest.CoherentFree.not_isZero_analytification_nodeSpecPresentation`. -/
example : ((analytificationSheaf.{u} nodeG.{u}).obj
    (cokernel nodeSpecPresentation.{u})).IsFinitePresentation :=
  haveI := isCoherent_analytificationSheaf_cokernel.{u} nodeG.{u} nodeSpecPresentation.{u}
  SheafOfModules.IsCoherent.isFinitePresentation.{u} _

/-! ### The analytification of `𝒪_{Spec A} ⧸ (x)` -/

/-- **The analytification of `𝒪_{Spec A} ⧸ (x)` is of finite presentation.**

This is the instance that carries weight: the presenting map is not an epimorphism
(`OkaTest.CoherentFree.not_isZero_cokernel_specXFamily` together with
`OkaTest.CoherentFree.notMem_maximalIdeal_germ_specX_ptX`), so unlike the two above this sheaf is
not a free sheaf presented by the zero map, and the relations half of
`SheafOfModules.IsCoherent.isFinitePresentation` is not vacuous at it. -/
example : ((analytificationSheaf.{u} nodeG.{u}).obj
    (cokernel ((nodeSpec.{u}).sectionsHom specXFamily.{u}))).IsFinitePresentation :=
  haveI := isCoherent_analytificationSheaf_cokernel_sectionsHom.{u} nodeG.{u} specXFamily.{u}
  SheafOfModules.IsCoherent.isFinitePresentation.{u} _

/-- **And quasicoherent.** -/
example : ((analytificationSheaf.{u} nodeG.{u}).obj
    (cokernel ((nodeSpec.{u}).sectionsHom specXFamily.{u}))).IsQuasicoherent :=
  haveI := isCoherent_analytificationSheaf_cokernel_sectionsHom.{u} nodeG.{u} specXFamily.{u}
  SheafOfModules.IsCoherent.isQuasicoherent.{u} _

/-! ### The two consequences of the affine dictionary, at a coherent sheaf on a `Spec`

Both of these had no witness until `AlgebraicGeometry.isCoherentStructureSheaf_spec`, which is
what the module docstring's retired paragraph is about. The sheaf is `𝒪_{Spec A} ⧸ (x)` for
`A = ℂ[x, y] ⧸ (xy)`: **coherent** by `OkaTest.AffineSections.isCoherent_cokernel_specXHom`, and
**not the zero sheaf** by `OkaTest.AffineSections.not_isZero_cokernel_specXHom`, so neither
instantiation is about nothing.

The two statements take their coherence hypothesis at **different spellings of the sheaf of
rings**, and that is the whole of why the instance is supplied by hand in one and not in the
other. `OkaTest.AffineSections.isCoherent_cokernel_specXHom` is stated over
`AlgebraicGeometry.LocallyRingedSpace.ringSheaf` of `OkaTest.CoherentFree.nodeSpec`.

* `AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent` takes its
  hypothesis over `AlgebraicGeometry.Scheme.ringCatSheaf` — **the other side of the seam** — so
  instance search does not find it and it is supplied positionally with `@`. That is the seam
  `AlgebraicGeometry.Scheme.isCoherent_unit` records: the two spellings agree by `rfl` and search
  still does not cross them. Checked, and not assumed: drop the `@` and the argument, and
  elaboration fails with `SheafOfModules.IsCoherent` unsynthesised at `cokernel specXHom`.
* `ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent` takes its hypothesis over
  `AlgebraicGeometry.LocallyRingedSpace.ringSheaf` — **the same side the instance is already on**
  — so there is no seam to cross and nothing has to be supplied. It is supplied by nothing below,
  and that is the check: the example is the bare application. -/

/-- **A coherent sheaf on `Spec A` has a finite global presentation**, at the witness.

`AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent`, whose hypothesis
was inhabited by nothing on a `Spec` when it was written. -/
example : ∃ P : ((cokernel specXHom.{u} :
    (Spec nodeA.{u}).Modules)).Presentation, P.IsFinite :=
  @AlgebraicGeometry.Scheme.Modules.exists_isFinite_presentation_of_isCoherent nodeA.{u} _
    isCoherent_cokernel_specXHom.{u}

/-- **The analytification of a coherent sheaf is coherent**, at the witness — and this is the
first place in this repository that statement is applied to anything.

`ComplexAnalytic.isCoherent_analytificationSheaf_of_isCoherent`. Note what it is *not*: the three
instantiations above go through `ComplexAnalytic.isCoherent_analytificationSheaf_cokernel`, whose
hypothesis is a **presentation** and is weaker. This one takes coherence as given and is the form
GAGA quotes; it is stated here rather than in `OkaTest/SpecCoherent.lean` because what it tests is
the corollary of the affine dictionary that this file is about. -/
example : ((analytificationSheaf.{u} nodeG.{u}).obj (cokernel specXHom.{u})).IsCoherent :=
  isCoherent_analytificationSheaf_of_isCoherent.{u} nodeG.{u} _

end OkaTest.CoherentPresentation

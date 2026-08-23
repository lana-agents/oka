/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
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

## What is *not* tested, and it is the affine half

`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent` — a coherent
`𝒪_{Spec R}`-module is `(Γ M)^~` — is **not instantiated anywhere**, here or in the library,
because **this repository proves no sheaf on a `Spec` to be coherent.** Coherence on the
algebraic side would come from `𝒪_{Spec A}` being coherent for noetherian `A`, which is not
formalised here; every coherent sheaf this repository exhibits lives on an analytic space, by
Oka's theorem. The three witnesses below are analytifications, which are sheaves on the
analytic space and not on `Spec A`.

So the affine statement is stated and unexercised, and that is recorded rather than hidden: it is
a mirror-tree consequence of `SheafOfModules.IsCoherent.isQuasicoherent` and of Mathlib's
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`, and the first thing that instantiates
it will be the coherence of an algebraic structure sheaf.

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

open OkaTest.CoherentFree

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

end OkaTest.CoherentPresentation

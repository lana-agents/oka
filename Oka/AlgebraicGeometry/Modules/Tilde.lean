/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Presentation

/-!
# A coherent sheaf on an affine scheme is the sheaf associated with its global sections

Material for `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`; see `README.md` on the mirror tree.

Mathlib proves `AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`: an
`𝒪_{Spec R}`-module `M` is quasicoherent exactly when the counit
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ : (Γ M)^~ ⟶ M` is an isomorphism, and packages the
consequence as the equivalence `AlgebraicGeometry.tildeEquiv` between `ModuleCat R` and the
quasicoherent `𝒪_{Spec R}`-modules. This file records what that gives for the *coherent* ones,
which is the notion this repository's sheaf theory is stated in.

The content is entirely in `SheafOfModules.IsCoherent.isQuasicoherent`; nothing here is about
`Spec`. It is stated because the affine dictionary is quoted often enough — "a coherent sheaf on
`Spec A` is a module" — that the one-line derivation is worth having a name, and because the
target `M ≅ (Γ M)^~` is the form a consumer wants rather than `IsIso` of a counit.

## What this does *not* give

`M ≅ (Γ M)^~` says nothing about `Γ M` as an `R`-module: nothing here shows it is finitely
generated, let alone finitely presented, and nothing here produces a *global* presentation of `M`
as a cokernel of finite free sheaves. Coherence gives finite generation only locally, and the
passage to a global statement is the quasi-compactness argument on `Spec R`, which is not in this
repository. A consumer wanting "coherent sheaf on `Spec A` = finitely presented `A`-module" needs
that step and will not find it here.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.isoTildeΓ`

## Main results

- `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

/-- **A coherent `𝒪_{Spec R}`-module is `(Γ M)^~`.**

`SheafOfModules.IsCoherent.isQuasicoherent` and Mathlib's
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`. Coherence is used only
through quasicoherence: `AlgebraicGeometry.tilde` cannot see the difference, and the finiteness
of `Γ M` that separates the two is not asserted — see the module docstring. -/
theorem isIso_fromTildeΓ_of_isCoherent [M.IsCoherent] : IsIso M.fromTildeΓ := by
  haveI := SheafOfModules.IsCoherent.isQuasicoherent M
  infer_instance

/-- **The comparison of a coherent `𝒪_{Spec R}`-module with the sheaf associated with its global
sections, as an isomorphism.** -/
noncomputable def isoTildeΓ [M.IsCoherent] :
    AlgebraicGeometry.tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) ≅ M :=
  haveI := isIso_fromTildeΓ_of_isCoherent M
  asIso M.fromTildeΓ

end AlgebraicGeometry.Scheme.Modules

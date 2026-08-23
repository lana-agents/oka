/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Axiom regression tests: Sheaves of modules and coherence

The mirror-tree theory of `Oka/Algebra/Category/ModuleCat/Sheaf/`, and its first analytic
consequences: ideal sheaves and quotients of the structure sheaf, together with stalks of
sheaves of modules on a space and the exactness they detect.

See `OkaTest/Axioms.lean` for what these assertions are for and how to update one.
-/

/-! ### Coherence of finitely generated ideal sheaves -/

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherent_idealSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherent_idealSheaf

/--
info: 'ComplexAnalytic.AnalyticSpace.isFiniteType_kernel_sectionsHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isFiniteType_kernel_sectionsHom

/-! ### Epimorphisms of sheaves of modules are locally surjective -/

/--
info: 'SheafOfModules.preservesEpimorphisms_toSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.preservesEpimorphisms_toSheaf

/--
info: 'SheafOfModules.isLocallySurjective_toSheaf_map_iff_epi' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.isLocallySurjective_toSheaf_map_iff_epi

/--
info: 'SheafOfModules.exists_forall_app_eq_of_epi' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.exists_forall_app_eq_of_epi

/--
info: 'SheafOfModules.exists_free_app_eq_of_epi' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.exists_free_app_eq_of_epi

/-! ### Coherence of a quotient by a coherent subsheaf -/

/--
info: 'SheafOfModules.IsCoherent.cokernel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.IsCoherent.cokernel

/--
info: 'SheafOfModules.IsFiniteType.of_epi_free' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.IsFiniteType.of_epi_free

/--
info: 'SheafOfModules.isFiniteType_free_biprod' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.isFiniteType_free_biprod

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isCoherent_cokernel_sectionsHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isCoherent_cokernel_sectionsHom

/--
info: 'ComplexAnalytic.AnalyticSpace.isCoherent_cokernel_sectionsHom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexAnalytic.AnalyticSpace.isCoherent_cokernel_sectionsHom

/-! ### Non-vacuity of that quotient -/

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.not_epi_sectionsHom_of_germ_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.not_epi_sectionsHom_of_germ_mem

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.not_isZero_cokernel_sectionsHom_of_germ_mem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.not_isZero_cokernel_sectionsHom_of_germ_mem

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.isZero_cokernel_sectionsHom_one' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.isZero_cokernel_sectionsHom_one

/-! ### Stalks of sheaves of modules on a space, and exactness

`Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean`. -/

/--
info: 'TopCat.Sheaf.exact_iff_stalk_exact' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopCat.Sheaf.exact_iff_stalk_exact

/--
info: 'SheafOfModules.exact_of_stalk_exact' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.exact_of_stalk_exact

/-! ### The stalk of a pullback of sheaves of modules is the base change of the stalk

`Oka/Algebra/Category/ModuleCat/Presheaf/Skyscraper.lean`,
`Oka/Algebra/Category/ModuleCat/Presheaf/PullbackStalk.lean`,
`Oka/Algebra/Category/ModuleCat/Sheaf/PullbackStalk.lean` and
`Oka/AnalyticSpace/PullbackModulesStalk.lean`. -/

/--
info: 'PresheafOfModules.stalkSkyscraperAdj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.stalkSkyscraperAdj

/--
info: 'PresheafOfModules.skyscraperAb_isSheaf' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.skyscraperAb_isSheaf

/--
info: 'PresheafOfModules.pushforwardSkyscraperIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.pushforwardSkyscraperIso

/--
info: 'PresheafOfModules.pullbackStalkIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PresheafOfModules.pullbackStalkIso

/--
info: 'SheafOfModules.stalkSkyscraperAdj' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.stalkSkyscraperAdj

/--
info: 'SheafOfModules.pullbackStalkIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.pullbackStalkIso

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesStalkIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesStalkIso

/-! ### Pullback along a stalkwise flat morphism is left exact

`Oka/Algebra/Category/ModuleCat/Sheaf/PullbackExact.lean` and
`Oka/AnalyticSpace/PullbackModulesStalk.lean`. -/

/--
info: 'SheafOfModules.mono_of_forall_mono_stalkFunctor_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.mono_of_forall_mono_stalkFunctor_map

/--
info: 'SheafOfModules.preservesMonomorphisms_pullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.preservesMonomorphisms_pullback

/--
info: 'SheafOfModules.preservesFiniteLimits_pullback' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.preservesFiniteLimits_pullback

/--
info: 'AlgebraicGeometry.LocallyRingedSpace.Hom.preservesFiniteLimits_pullbackModules' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyRingedSpace.Hom.preservesFiniteLimits_pullbackModules


/-! ### Coherence of free sheaves of modules

`Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Free.lean` and its categorical input. -/

/--
info: 'CategoryTheory.Limits.kernelBiprodLiftIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Limits.kernelBiprodLiftIso

/--
info: 'SheafOfModules.IsCoherent.biprod' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.IsCoherent.biprod

/--
info: 'SheafOfModules.IsCoherent.free' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.IsCoherent.free

/-! ### Coherent sheaves are locally finitely presented, and the affine dictionary -/

/--
info: 'SheafOfModules.QuasicoherentData.isFinitePresentation_bind' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.QuasicoherentData.isFinitePresentation_bind

/--
info: 'SheafOfModules.GeneratingSections.overKernelπIso' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.GeneratingSections.overKernelπIso

/--
info: 'SheafOfModules.GeneratingSections.presentationOver' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.GeneratingSections.presentationOver

/--
info: 'SheafOfModules.GeneratingSections.isFinite_presentationOver' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.GeneratingSections.isFinite_presentationOver

/--
info: 'SheafOfModules.GeneratingSections.quasicoherentDataOver' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.GeneratingSections.quasicoherentDataOver

/--
info: 'SheafOfModules.GeneratingSections.isFinitePresentation_quasicoherentDataOver' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.GeneratingSections.isFinitePresentation_quasicoherentDataOver

/--
info: 'SheafOfModules.IsCoherent.isFinitePresentation' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.IsCoherent.isFinitePresentation

/--
info: 'SheafOfModules.IsCoherent.isQuasicoherent' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.IsCoherent.isQuasicoherent

/--
info: 'AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent

/--
info: 'AlgebraicGeometry.Scheme.Modules.isoTildeΓ' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isoTildeΓ

/-! ### Restriction of generating sections, and the two affine steps -/

/--
info: 'SheafOfModules.GeneratingSections.restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.GeneratingSections.restrict

/--
info: 'SheafOfModules.GeneratingSections.isFiniteType_restrict' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.GeneratingSections.isFiniteType_restrict

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_finset_basicOpen_generatingSections' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_finset_basicOpen_generatingSections

/--
info: 'AlgebraicGeometry.Scheme.Modules.sectionsToBasicOpen' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.sectionsToBasicOpen

/--
info: 'AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen

/--
info: 'AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen_of_isCoherent'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Modules.isLocalizedModule_away_sectionsToBasicOpen_of_isCoherent

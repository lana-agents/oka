import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

open TensorProduct LinearMap

theorem Module.Flat.of_faithfullyFlat_tower (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] [Module.Flat A C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  have hAC : Function.Injective ⇑(LinearMap.lTensor C N.subtype) :=
    (Module.Flat.iff_lTensor_injectiveₛ.mp inferInstance) N
  have hsq := AlgebraTensorModule.lTensor_comp_cancelBaseChange A B C (M := C) N.subtype
  have h1 : Function.Injective
      (⇑(AlgebraTensorModule.cancelBaseChange A B C C P) ∘
        ⇑((AlgebraTensorModule.lTensor C C) ((AlgebraTensorModule.lTensor B B) N.subtype))) := by
    have : ⇑((AlgebraTensorModule.lTensor C C) N.subtype) ∘
        ⇑(AlgebraTensorModule.cancelBaseChange A B C C N) =
        ⇑(AlgebraTensorModule.cancelBaseChange A B C C P) ∘
        ⇑((AlgebraTensorModule.lTensor C C) ((AlgebraTensorModule.lTensor B B) N.subtype)) :=
      congrArg (fun f : _ →ₗ[C] _ ↦ ⇑f) hsq
    rw [← this]
    exact hAC.comp (AlgebraTensorModule.cancelBaseChange A B C C N).injective
  have h2 : Function.Injective
      ⇑((AlgebraTensorModule.lTensor C C) ((AlgebraTensorModule.lTensor B B) N.subtype)) :=
    Function.Injective.of_comp h1
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective B C
    ((AlgebraTensorModule.lTensor B B) N.subtype)).mp h2

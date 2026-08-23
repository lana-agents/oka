/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.Analytification
import OkaTest.OpenSubspace

/-!
# Non-vacuity of the coherence of free sheaves and of their analytifications

`SheafOfModules.IsCoherent.free` and
`ComplexAnalytic.isCoherent_analytificationSheaf_cokernel` are both satisfied by the zero sheaf,
and at rank one they are both statements the repository already had — `𝒪` is coherent by Oka's
theorem (`ComplexAnalytic.AnalyticSpace.isCoherentStructureSheaf`) and the analytification of
`𝒪` is `𝒪` (`ComplexAnalytic.analytificationSheafUnitIso`). **So the two degeneracies to rule
out are rank one and zero**, and that is what this file does.

* **Rank two on the node.** A free sheaf of rank two on `AnalyticSpace.node` is coherent, and it
  is **not** the zero sheaf (`not_isZero_free_node`). The node is not `ℂ^n`, so no smoothness is
  hiding in the statement.
* **The analytification of `𝒪_{Spec A}²`** for `A = ℂ[x, y] ⧸ (xy)`, presented as the cokernel
  of the zero map out of the free sheaf on the empty index type — a presentation with no
  relations. It is coherent, and again **not** the zero sheaf
  (`not_isZero_analytification_nodeSpecPresentation`), because it is the free sheaf of rank two
  on the node and the origin is a point of the node.

The two nonzero statements both come from `not_isZero_free`, whose proof is that the unit sheaf
is a retract of any free sheaf on a nonempty index type, and that a complex analytic space with
a point has a nonzero structure sheaf, since `1` and `0` have different values there.

## What this does not test, and why not

**No *non-free* cokernel is exercised.** To make `cokernel ψ` non-free one needs `ψ` to have a
non-unit entry, i.e. a global section of `𝒪_{Spec A}` that is not invertible; then
`AlgebraicGeometry.LocallyRingedSpace.not_isZero_cokernel_sectionsHom_of_germ_mem` would give a
nonzero quotient exactly as `OkaTest/CoherentCokernel.lean` does on the analytic side. What is
missing is not that lemma but the *section*: producing a global section of `𝒪_{Spec A}` from a
ring element, and computing its germ at a prime, needs the germ API of Mathlib's
`AlgebraicGeometry.StructureSheaf` — `toOpen`, `toStalk`, `stalkIso` — which nothing in this
repository uses yet. **Everything on the `Spec` side of this development so far goes through the
`Γ`-`Spec` adjunction and never touches a section of the structure sheaf directly.** That gap is
filed separately; it is a gap in the test, not in the theorem.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Limits ComplexAnalytic

universe u

noncomputable section

namespace OkaTest.CoherentFree

/-- **The structure sheaf of a complex analytic space with a point is not the zero sheaf.** -/
theorem not_isZero_unit (X : AnalyticSpace.{u}) (x : X) :
    ¬ IsZero (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) := by
  intro h
  have hid : 𝟙 (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) = 0 :=
    (IsZero.iff_id_eq_zero _).1 h
  have h1 : (1 : X.presheaf.obj (op ⊤)) = 0 := by
    have h2 := congrArg
      (fun m : SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf ⟶
        SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf ↦
          m.val.app (op ⊤) (1 : X.presheaf.obj (op ⊤))) hid
    rw [show (0 : SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf ⟶
        SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf).val = 0 from rfl] at h2
    exact h2
  have h3 := congrArg (X.eval (U := ⊤) x trivial) h1
  simp at h3

/-- **A free sheaf on a nonempty index type over a complex analytic space with a point is not
the zero sheaf**, because the unit is a retract of it. -/
theorem not_isZero_free (X : AnalyticSpace.{u}) (x : X) {I : Type u} (i : I) :
    ¬ IsZero (SheafOfModules.free (R := X.toLocallyRingedSpace.ringSheaf) I) := by
  classical
  intro h
  refine not_isZero_unit X x ?_
  rw [IsZero.iff_id_eq_zero]
  rw [← show SheafOfModules.ιFree i ≫
      SheafOfModules.freeProj X.toLocallyRingedSpace.ringSheaf i =
        𝟙 (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) from by
    rw [SheafOfModules.ιFree_comp_freeProj]
    exact if_pos rfl]
  rw [h.eq_zero_of_tgt (SheafOfModules.ιFree i), Limits.zero_comp]

/-! ### A free sheaf of rank two on the node -/

/-- **A free sheaf of rank two on the node is coherent.** -/
example : (SheafOfModules.free (R := AnalyticSpace.node.{u}.toLocallyRingedSpace.ringSheaf)
    (ULift.{u} (Fin 2))).IsCoherent :=
  AnalyticSpace.node.{u}.isCoherent_free _

/-- **And it is not the zero sheaf**, so the statement above is about something. -/
theorem not_isZero_free_node :
    ¬ IsZero (SheafOfModules.free (R := AnalyticSpace.node.{u}.toLocallyRingedSpace.ringSheaf)
      (ULift.{u} (Fin 2))) :=
  not_isZero_free _ nodeOrigin.{u} (ULift.up 0)

/-! ### The analytification of `A²` for `A = ℂ[x, y] ⧸ (xy)` -/

/-- The sheaf of rings of `Spec (ℂ[x, y] ⧸ (xy))`. -/
abbrev nodeSpecRingSheaf :=
  (Spec.locallyRingedSpaceObj (CommRingCat.of
    (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸ presentationIdeal.{u} nodeG.{u}))).ringSheaf

/-- The presentation of `A²` with no relations: the zero map out of the free sheaf on the empty
index type. Its cokernel is `𝒪_{Spec A}²`. -/
abbrev nodeSpecPresentation :
    SheafOfModules.free (R := nodeSpecRingSheaf.{u}) PEmpty.{u + 1} ⟶
      SheafOfModules.free (R := nodeSpecRingSheaf.{u}) (ULift.{u} (Fin 2)) :=
  0

/-- **The analytification of `𝒪_{Spec A}²` is coherent**, for `A = ℂ[x, y] ⧸ (xy)`. -/
example : ((analytificationSheaf.{u} nodeG.{u}).obj
    (cokernel nodeSpecPresentation.{u})).IsCoherent :=
  isCoherent_analytificationSheaf_cokernel.{u} nodeG.{u} _

/-- **And it is not the zero sheaf.**

It is the free sheaf of rank two on the node, by `ComplexAnalytic.analytificationSheafFreeIso`
and `CategoryTheory.Limits.cokernelZeroIsoTarget`, and the origin is a point of the node. -/
theorem not_isZero_analytification_nodeSpecPresentation :
    ¬ IsZero ((analytificationSheaf.{u} nodeG.{u}).obj (cokernel nodeSpecPresentation.{u})) := by
  intro h
  refine not_isZero_free (AnalyticSpace.analytification.{u} nodeG.{u})
    ⟨⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩, origin_mem_zeroLocus_polySection_nodeG.{u}⟩
    (I := ULift.{u} (Fin 2)) (ULift.up 0) ?_
  exact IsZero.of_iso h ((analytificationSheafFreeIso.{u} nodeG.{u} (ULift.{u} (Fin 2))).symm ≪≫
    (analytificationSheaf.{u} nodeG.{u}).mapIso cokernelZeroIsoTarget.symm)

end OkaTest.CoherentFree

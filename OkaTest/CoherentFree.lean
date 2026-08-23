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

* **A quotient that is neither `0` nor free.** `𝒪_{Spec A} ⧸ (x)` for `x` the class of the first
  coordinate: its analytification is coherent, and the sheaf being analytified is **not the zero
  sheaf** (`not_isZero_cokernel_specXFamily`), because `x` vanishes at the origin of the node and
  so its germ at the corresponding prime lies in the maximal ideal. The hypothesis is a real
  condition and not one every section satisfies: at the point `(1, 0)` of the node the germ of
  `x` is a **unit** (`notMem_maximalIdeal_germ_specX_ptX`), and
  `AlgebraicGeometry.LocallyRingedSpace.isZero_cokernel_sectionsHom_one` is the quotient by the
  unit ideal, which really is `0`.

## What this still does not test

That `𝒪_{Spec A} ⧸ (x)` is not *isomorphic* to `𝒪_{Spec A}`, which would need `x ≠ 0` in
`ℂ[x, y] ⧸ (xy)` and a comparison of the two sheaves. What is recorded is that it is a proper
quotient in the sense that the ideal is not the unit ideal, and that it is not zero.
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

/-! ### A quotient of `𝒪_{Spec A}` that is not zero

`A = ℂ[x, y] ⧸ (xy)`, and the section is the class of `x`. This is the instantiation that
exercises the theorem at a sheaf which is neither zero nor free; the two above do not.
-/

/-- `Spec A` for `A = ℂ[x, y] ⧸ (xy)`, as a locally ringed space. -/
abbrev nodeSpec : LocallyRingedSpace.{u} :=
  Spec.locallyRingedSpaceObj (CommRingCat.of
    (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸ presentationIdeal.{u} nodeG.{u}))

/-- The class of the first coordinate in `A = ℂ[x, y] ⧸ (xy)`. -/
def specX : MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸ presentationIdeal.{u} nodeG.{u} :=
  Ideal.Quotient.mk (presentationIdeal.{u} nodeG.{u}) (MvPolynomial.X (ULift.up 0))

/-- The one-element family `{x}` of global sections of `𝒪_{Spec A}`.

The `Algebra` instance is stated for `Spec.structureSheaf` and not for
`Spec.locallyRingedSpaceObj`, so the ascription here is where the seam between the two spellings
is crossed; everything downstream is at the locally ringed space spelling. -/
def specXFamily : PUnit.{u + 1} → (nodeSpec.{u}).presheaf.obj (op ⊤) :=
  fun _ ↦ algebraMap (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸ presentationIdeal.{u} nodeG.{u})
    ((Spec.structureSheaf (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸
      presentationIdeal.{u} nodeG.{u})).presheaf.obj (op ⊤)) specX.{u}

/-- The origin, as a point of the analytification of `A`. -/
def anOrigin : AnalyticSpace.analytification.{u} nodeG.{u} :=
  ⟨⟨(0 : ULift.{u} (Fin 2) → ℂ), trivial⟩, origin_mem_zeroLocus_polySection_nodeG.{u}⟩

/-- The point of the node with `x = 1`, at which `x` does *not* vanish. -/
def anPtX : AnalyticSpace.analytification.{u} nodeG.{u} :=
  ⟨⟨nodePtX.{u}, trivial⟩, nodePtX_mem_zeroLocus_polySection_nodeG.{u}⟩

/-- **The germ of `x` at the prime under the origin lies in the maximal ideal**, because `x`
vanishes at the origin. `ComplexAnalytic.mem_analytificationToSpec_base_asIdeal_iff` turns the
membership in the prime into the vanishing of a polynomial at a point. -/
theorem germ_specXFamily_mem (i : PUnit.{u + 1}) :
    (nodeSpec.{u}).presheaf.germ ⊤ ((analytificationToSpec.{u} nodeG.{u}).base anOrigin.{u})
        trivial (specXFamily.{u} i) ∈
      IsLocalRing.maximalIdeal ((nodeSpec.{u}).presheaf.stalk
        ((analytificationToSpec.{u} nodeG.{u}).base anOrigin.{u})) :=
  (StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff' _ specX.{u} _).2
    ((mem_analytificationToSpec_base_asIdeal_iff.{u} nodeG.{u} anOrigin.{u} _).2
      (by simp [anOrigin]))

/-- **The quotient of `𝒪_{Spec A}` by the ideal generated by `x` is not the zero sheaf.** -/
theorem not_isZero_cokernel_specXFamily :
    ¬ IsZero (cokernel ((nodeSpec.{u}).sectionsHom specXFamily.{u})) :=
  (nodeSpec.{u}).not_isZero_cokernel_sectionsHom_of_germ_mem specXFamily.{u} _
    germ_specXFamily_mem.{u}

/-- **Its analytification is coherent** — the theorem at a sheaf which is neither zero nor
free. -/
example : ((analytificationSheaf.{u} nodeG.{u}).obj
    (cokernel ((nodeSpec.{u}).sectionsHom specXFamily.{u}))).IsCoherent :=
  isCoherent_analytificationSheaf_cokernel_sectionsHom.{u} nodeG.{u} specXFamily.{u}

/-- **The hypothesis of `germ_specXFamily_mem` is a real condition**: at the point of the node
with `x = 1` the germ of `x` is a unit, so it does not lie in the maximal ideal. Without this the
statement above would be open to the reading that the quotient is never zero, and
`AlgebraicGeometry.LocallyRingedSpace.isZero_cokernel_sectionsHom_one` shows that it can be. -/
theorem notMem_maximalIdeal_germ_specX_ptX :
    (nodeSpec.{u}).presheaf.germ ⊤ ((analytificationToSpec.{u} nodeG.{u}).base anPtX.{u})
        trivial (specXFamily.{u} PUnit.unit) ∉
      IsLocalRing.maximalIdeal ((nodeSpec.{u}).presheaf.stalk
        ((analytificationToSpec.{u} nodeG.{u}).base anPtX.{u})) := by
  intro hcon
  have h := (StructureSheaf.germ_algebraMap_mem_maximalIdeal_iff' _ specX.{u} _).1 hcon
  have h0 := (mem_analytificationToSpec_base_asIdeal_iff.{u} nodeG.{u} anPtX.{u}
    (MvPolynomial.X (ULift.up 0))).1 h
  simp [anPtX] at h0

end OkaTest.CoherentFree

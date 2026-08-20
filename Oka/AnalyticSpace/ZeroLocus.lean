/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.Basic

/-!
# The zero locus of a family of global sections

`ComplexAnalytic.IsCutOutBy` (`Oka/AnalyticSpace/Basic.lean`) has four fields, of which two are
purely topological: the morphism is a closed embedding, and its range is the set of points at
which every germ of every `f j` lies in the maximal ideal of the stalk. This file provides both,
for an arbitrary locally ringed space and an arbitrary family of global sections.

Nothing here is analytic. The zero locus is closed because the locus where the germ of a section
is *invertible* is open — that is `AlgebraicGeometry.RingedSpace.basicOpen`, which is an `Opens`
by construction — and the zero locus is the complement of the union of those loci.

This is the first step of the construction of the analytic subspace cut out by finitely many
holomorphic functions. What remains is the structure sheaf and the two stalkwise conditions;
see the module `Oka/Topology/Sheaves/QuotientPresheaf.lean` for the stalk computation those
rest on.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.zeroLocus`: the set of points at which every germ of
  every `f i` is a non-unit.
- `AlgebraicGeometry.LocallyRingedSpace.zeroLocusSpace` and `zeroLocusι`: that set as a
  topological space, and its inclusion into the ambient space.

## Main results

- `AlgebraicGeometry.LocallyRingedSpace.isClosed_zeroLocus`: the zero locus is closed.
- `AlgebraicGeometry.LocallyRingedSpace.isClosedEmbedding_zeroLocusι` and
  `range_zeroLocusι`: the two topological conditions of `ComplexAnalytic.IsCutOutBy`,
  discharged for any candidate structure sheaf on the zero locus.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u}) {κ : Type*} (f : κ → Y.presheaf.obj (op ⊤))

/-- The **zero locus** of a family of global sections of the structure sheaf: the points at
which every germ of every `f i` fails to be a unit, equivalently lies in the maximal ideal of
the stalk.

This is the underlying set of the closed subspace that the `f i` cut out; it is exactly the set
appearing in `ComplexAnalytic.IsCutOutBy.range_base`. -/
def zeroLocus : Set Y :=
  {y | ∀ i, Y.presheaf.Γgerm y (f i) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)}

lemma mem_zeroLocus_iff {y : Y} :
    y ∈ Y.zeroLocus f ↔
      ∀ i, Y.presheaf.Γgerm y (f i) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
  Iff.rfl

/-- A point lies in the zero locus exactly when no germ there is a unit. -/
lemma mem_zeroLocus_iff_not_isUnit {y : Y} :
    y ∈ Y.zeroLocus f ↔ ∀ i, ¬ IsUnit (Y.presheaf.Γgerm y (f i)) := by
  simp only [mem_zeroLocus_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- The locus where the germ of a global section is a unit is open. This is
`AlgebraicGeometry.RingedSpace.basicOpen`, restated as a statement about a `Set`. -/
lemma isOpen_setOf_isUnit_germ (s : Y.presheaf.obj (op ⊤)) :
    IsOpen {y : Y | IsUnit (Y.presheaf.Γgerm y s)} := by
  have h : {y : Y | IsUnit (Y.presheaf.Γgerm y s)} = (Y.toRingedSpace.basicOpen s).carrier :=
    Set.ext fun y ↦ (Y.toRingedSpace.mem_top_basicOpen s y).symm
  rw [h]
  exact (Y.toRingedSpace.basicOpen s).isOpen

/-- The complement of the zero locus is the union of the loci where some `f i` is invertible. -/
lemma compl_zeroLocus :
    (Y.zeroLocus f)ᶜ = ⋃ i, {y : Y | IsUnit (Y.presheaf.Γgerm y (f i))} := by
  ext y
  simp [zeroLocus, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- **The zero locus of a family of global sections is closed.**

No analyticity is involved: this holds on any locally ringed space, because the locus where a
section is invertible is open. -/
theorem isClosed_zeroLocus : IsClosed (Y.zeroLocus f) := by
  rw [← isOpen_compl_iff, Y.compl_zeroLocus f]
  exact isOpen_iUnion fun i ↦ Y.isOpen_setOf_isUnit_germ (f i)

/-- The zero locus, as a closed subspace of `Y`. -/
def zeroLocusSpace : TopCat.{u} :=
  TopCat.of (Y.zeroLocus f)

/-- The inclusion of the zero locus into the ambient space. -/
def zeroLocusι : Y.zeroLocusSpace f ⟶ Y.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
lemma zeroLocusι_apply (z : Y.zeroLocus f) : Y.zeroLocusι f z = z.1 := rfl

/-- The inclusion of the zero locus is a closed embedding: this is the first of the four
conditions in `ComplexAnalytic.IsCutOutBy`. -/
theorem isClosedEmbedding_zeroLocusι : IsClosedEmbedding (Y.zeroLocusι f) :=
  (Y.isClosed_zeroLocus f).isClosedEmbedding_subtypeVal

/-- The range of the inclusion of the zero locus is the set appearing in
`ComplexAnalytic.IsCutOutBy.range_base`.

Together with `isClosedEmbedding_zeroLocusι` this discharges the two topological conditions of
`IsCutOutBy` for any candidate structure sheaf on the zero locus. -/
theorem range_zeroLocusι :
    Set.range (Y.zeroLocusι f) =
      {y | ∀ i, Y.presheaf.Γgerm y (f i) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)} :=
  Subtype.range_val

end AlgebraicGeometry.LocallyRingedSpace

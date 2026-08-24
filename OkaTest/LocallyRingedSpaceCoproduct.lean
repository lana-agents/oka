/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the open cover of a coproduct of locally ringed spaces

`AlgebraicGeometry.LocallyRingedSpace.sigmaOpenCover` covers `∐ f` by the family `f`. Three
readings would make it say less than it appears to, and each is closed below.

* **The joint surjectivity might be about a space with no points to be surjective onto.** It is
  not vacuous in that direction and it is not empty in the other: `isEmpty_sigma_of_isEmpty` runs
  it at the *empty* family, where it forces the coproduct to have no points at all. An inhabitant
  of the coproduct would produce an inhabitant of `PEmpty`, so this is a real consequence and it
  is false of a space chosen carelessly.
* **The open-immersion instance might not fire on the form a consumer writes.**
  `AlgebraicGeometry.LocallyRingedSpace.sigmaι_isOpenImmersion` exists precisely because instance
  search does not see through `CategoryTheory.Limits.Sigma.ι` to
  `CategoryTheory.Limits.colimit.ι`; that it fires is therefore a fact about the file rather than
  about the mathematics, and `isOpenImmersion_sigmaι_pair` checks it by `inferInstance` at a
  two-member family, which is the smallest index type with two distinct members.
* **The cover might be some other cover of the same space.** `sigmaOpenCover_eq` pins its index
  type, its members and its maps to the family's own, by `rfl`.

The members of a coproduct are also pairwise disjoint, which is what makes the index chosen for a
point unique. **That is not proved and nothing here uses it**: no statement below mentions
`Disjoint`, and the `## What is not here` section of the file under test says why.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

namespace OkaTest.LocallyRingedSpaceCoproduct

universe u

/-- **The coproduct of the empty family of locally ringed spaces has no points**, which is
`AlgebraicGeometry.LocallyRingedSpace.exists_sigma_ι_base_eq` read at the empty family. -/
theorem isEmpty_sigma_of_isEmpty (f : PEmpty.{u + 1} → LocallyRingedSpace.{u}) :
    IsEmpty (∐ f : LocallyRingedSpace.{u}) :=
  ⟨fun x ↦ (exists_sigma_ι_base_eq f x).choose.elim⟩

/-- **The open immersion instance is found on `CategoryTheory.Limits.Sigma.ι`**, which the
functor-indexed instance alone does not give: the two are definitionally equal and instance search
is syntactic. Stated at a two-member family because that is the form a cover is used at. -/
theorem isOpenImmersion_sigmaι_pair (X : LocallyRingedSpace.{u}) (i : ULift.{u} Bool) :
    LocallyRingedSpace.IsOpenImmersion (Sigma.ι (fun _ : ULift.{u} Bool ↦ X) i) :=
  inferInstance

/-- **The cover of a coproduct is indexed by the family's own index type**, with the family's own
members and their inclusions — so it is the intended cover and not merely a well-typed one. -/
theorem sigmaOpenCover_eq {ι : Type u} (f : ι → LocallyRingedSpace.{u}) :
    (sigmaOpenCover f).J = ι ∧ (sigmaOpenCover f).obj = f ∧ (sigmaOpenCover f).map = Sigma.ι f :=
  ⟨rfl, rfl, rfl⟩

end OkaTest.LocallyRingedSpaceCoproduct

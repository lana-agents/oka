/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka
import OkaTest.CoherentFree

/-!
# Non-vacuity of the coherence of the structure sheaf of a noetherian scheme

`AlgebraicGeometry.isCoherentStructureSheaf_spec` says `𝒪_{Spec A}` is coherent for noetherian
`A`. Both the hypothesis and the conclusion have degenerate readings — a field is noetherian, and
`SheafOfModules.IsCoherent` is satisfied by the zero sheaf — so this file instantiates it away
from them, at the ring `A = ℂ[x, y] ⧸ (xy)` that the rest of the test library already uses:

* **`A` is not a field.** What is *checked* — in `OkaTest/AffineSections.lean` and
  `OkaTest/CoherentFree.lean`, which this file leans on rather than reproving — is that the class
  `x` of the first coordinate is nonzero, that its germ lies in the maximal ideal at the prime
  under the origin of the node, and that it is a **unit** at another point. That `A` is also not a
  domain and not regular is true, is what makes the node the node, and is **not formalised
  anywhere here**; it is not used below.
* **The sheaves are not zero.** Each statement below is paired with a `not_isZero_…` already
  proved in `OkaTest/CoherentFree.lean`, or is a free sheaf of rank two.

## What each one is for

1. `isCoherent_unit_nodeSpec` — the theorem itself at the witness. This is the first sheaf on a
   `Spec` that this repository proves coherent; before it, every coherent sheaf here lived on an
   analytic space and came from Oka's theorem.
2. `isCoherent_free_nodeSpec` — rank **two**, so `SheafOfModules.IsCoherent.free` is exercised
   past the rank-one case, which is the theorem above.
3. `isCoherent_cokernel_specXFamily` — `𝒪_{Spec A} ⧸ (x)`, a **proper nonzero quotient**:
   `OkaTest.CoherentFree.not_isZero_cokernel_specXFamily` says it is not zero, and
   `OkaTest.CoherentFree.notMem_maximalIdeal_germ_specX_ptX` says the ideal is not the unit
   ideal. This is the one at which the relations half of coherence is doing work, since the
   presenting map is not an epimorphism.
4. `isIso_fromTildeΓ_cokernel_specXFamily` —
   `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent` applied to it. That theorem
   is the affine dictionary, and `OkaTest/CoherentPresentation.lean` recorded it as stated and
   never instantiated, for exactly the reason this file removes.

## The spelling seam, and why item 4 uses `@`

`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent` is stated for
`AlgebraicGeometry.Scheme.Modules`, that is over `AlgebraicGeometry.Scheme.ringCatSheaf`, while
the cokernel here is built over `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`. The two agree
by `rfl` and `exact` crosses them, but **instance search does not**: writing the coherence
instance with `haveI` and letting the instance argument be found fails with
`failed to synthesize IsCoherent (cokernel (nodeSpec.sectionsHom specXFamily))`. Passing it
positionally with `@` is what settles it, and that is why the term below is written that way
rather than as a `haveI`. The same seam is documented on
`AlgebraicGeometry.Scheme.isCoherent_unit`.

## What is *not* tested here

* **That `𝒪_{Spec A} ⧸ (x)` is not free**, and hence that item 3 is not secretly item 2 again.
  `OkaTest/CoherentFree.lean` says the same about its analytification and does not prove it
  either; what is available is that the quotient is nonzero and the ideal proper.
* **That a non-noetherian ring fails.** Nothing here exhibits a ring whose structure sheaf is not
  coherent, so noetherianity is not shown to be necessary. It is not: `𝒪_{Spec A}` is coherent
  for any **coherent** ring `A`, and coherent rings need not be noetherian. That is mathematics
  and is not formalised here; it is said so that the missing test is read as being about *this
  proof* rather than about the statement.
* **Anything about analytification.** Coherence of `𝒪_{Spec A}` does **not** make
  `ComplexAnalytic.isCoherent_analytificationSheaf_cokernel` apply to a coherent sheaf rather
  than a presented one; that gap is the one `Oka/Analytification/SheafCoherent.lean` describes
  and it is untouched here.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Limits ComplexAnalytic
open SheafOfModules OkaTest.CoherentFree

universe u

noncomputable section

namespace OkaTest.SpecCoherent

/-- `A = ℂ[x, y] ⧸ (xy)`, the coordinate ring of the node, as a `CommRingCat`. It is noetherian
because it is a quotient of a polynomial ring in finitely many variables over a field. -/
abbrev nodeRing : CommRingCat.{u} :=
  CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) ℂ ⧸ presentationIdeal.{u} nodeG.{u})

/-- **`𝒪_{Spec A}` is coherent**, for `A = ℂ[x, y] ⧸ (xy)`.

The witness for `AlgebraicGeometry.isCoherentStructureSheaf_spec`, and the first coherent sheaf
on a scheme in this repository. -/
theorem isCoherent_unit_nodeSpec :
    (SheafOfModules.unit nodeSpecRingSheaf.{u}).IsCoherent :=
  (Spec nodeRing.{u}).isCoherent_unit

/-- **A free sheaf of rank two on `Spec A` is coherent.**

`SheafOfModules.IsCoherent.free` past rank one, which is the statement above. -/
theorem isCoherent_free_nodeSpec :
    (SheafOfModules.free (R := nodeSpecRingSheaf.{u}) (ULift.{u} (Fin 2))).IsCoherent :=
  (Spec nodeRing.{u}).isCoherent_free _

/-- **`𝒪_{Spec A} ⧸ (x)` is coherent**, for `x` the class of the first coordinate.

`AlgebraicGeometry.LocallyRingedSpace.isCoherent_cokernel_sectionsHom` — the two-out-of-three
step `SheafOfModules.IsCoherent.cokernel` — fed the coherence of the structure sheaf. It is not
the zero sheaf, by `OkaTest.CoherentFree.not_isZero_cokernel_specXFamily`, and `(x)` is not the
unit ideal, by `OkaTest.CoherentFree.notMem_maximalIdeal_germ_specX_ptX`; so this is a proper
nonzero quotient and not a restatement of the free case.

Until this statement the same sheaf was only known to be **finitely presented** after
analytification; it is now coherent before it. -/
theorem isCoherent_cokernel_specXFamily :
    (cokernel ((nodeSpec.{u}).sectionsHom specXFamily.{u})).IsCoherent :=
  LocallyRingedSpace.isCoherent_cokernel_sectionsHom _
    (AlgebraicGeometry.isCoherentStructureSheaf_spec nodeRing.{u}) specXFamily.{u}

/-- **A coherent sheaf on `Spec A` is the sheaf associated with its own global sections**, at the
witness.

`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isCoherent`, which
`OkaTest/CoherentPresentation.lean` recorded as stated and never instantiated because nothing
here proved a sheaf on a `Spec` coherent. The instance argument is supplied positionally with
`@`: see the module docstring on the `ringCatSheaf`/`ringSheaf` seam, which instance search does
not cross. -/
theorem isIso_fromTildeΓ_cokernel_specXFamily :
    IsIso (Scheme.Modules.fromTildeΓ (R := nodeRing.{u})
      (cokernel ((nodeSpec.{u}).sectionsHom specXFamily.{u}))) :=
  @Scheme.Modules.isIso_fromTildeΓ_of_isCoherent nodeRing.{u} _
    isCoherent_cokernel_specXFamily.{u}

end OkaTest.SpecCoherent

end

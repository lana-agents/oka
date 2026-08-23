/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.LocalIso
import Oka.Topology.Covering.Basic

/-!
# A finite étale morphism of complex analytic spaces is a covering map

The third rung of the Riemann existence theorem's analytic side: the underlying map of a finite
étale morphism is a covering map in the sense of `IsCoveringMap`. The first rung is
`Oka/AnalyticSpace/Finite.lean` and the second `Oka/AnalyticSpace/LocalIso.lean`.

## What the rung actually needs

`ComplexAnalytic.AnalyticSpace.IsFinite` is *closed with finite fibres* and
`ComplexAnalytic.AnalyticSpace.IsLocalIso` carries `IsLocalHomeomorph` as its topological field.
Those three conditions are exactly the hypotheses of Mathlib's
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`, so all of the mathematics here is Mathlib's;
`IsClosedMap.isCoveringMap_of_isLocalHomeomorph` in `Oka/Topology/Covering/Basic.lean` is that
theorem at `Set.univ` and is the only thing this file uses. **The stalk field of `IsLocalIso` is
not used**, and cannot be: `IsCoveringMap` is a condition on the underlying map alone.

**The source is required Hausdorff, and this development does not give that for free.**
`ComplexAnalytic.AnalyticSpace` imposes no separation axiom — see `Oka/AnalyticSpace/Basic.lean`,
which says so for the same reason `AlgebraicGeometry.Scheme` does — so `[T2Space X]` is a genuine
hypothesis rather than an instance that will be found. It is Mathlib's hypothesis, used to
separate the finitely many points of a fibre, and it is where the statement below is weaker than
the classical one, which is stated for Hausdorff spaces throughout.

**Connectedness of the target is not needed.** `Oka/AnalyticSpace/LocalIso.lean` phrased this rung
as being about a connected base, and that was a hypothesis the argument never uses: a point
outside the range is evenly covered by the empty index type. What connectedness does buy is that
the *number of sheets* is constant, which is a different statement and is not here.

## What is not here

* **The constancy of the degree of a finite étale morphism**, which is the statement connectedness
  of the target is for.
* **The converse.** `IsCoveringMap.isLocalHomeomorph` returns the topological field of
  `IsLocalIso`, but no topological hypothesis can return the stalk field, so there is no `↔` and
  none is stated.
* **The Riemann existence theorem**, and any statement relating covers to field extensions.
* **The analytification of a finite étale morphism**, and **Grauert's finite mapping theorem** —
  the two absences `Oka/AnalyticSpace/LocalIso.lean` and `Oka/AnalyticSpace/Finite.lean` record.

## Main results

- `ComplexAnalytic.AnalyticSpace.isCoveringMap_base_of_isFiniteEtale`: **the underlying map of a
  finite étale morphism out of a Hausdorff analytic space is a covering map.**

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic.AnalyticSpace

/-- **The underlying map of a finite étale morphism out of a Hausdorff analytic space is a
covering map.**

The three inputs are the two fields of `ComplexAnalytic.AnalyticSpace.IsFinite` and the
topological field of `ComplexAnalytic.AnalyticSpace.IsLocalIso`; the stalk field plays no part,
since `IsCoveringMap` sees only the underlying map. `[T2Space X]` is not automatic — an analytic
space is not assumed Hausdorff here — and the target is not assumed connected, which the module
docstring explains.

Stated for `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` rather than for the two conditions
separately because that is the class the Riemann existence theorem is about; its two fields are
instances, so the proof below reads them off. -/
theorem isCoveringMap_base_of_isFiniteEtale {X Y : AnalyticSpace.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] [T2Space X] : IsCoveringMap f.toLRSHom.base :=
  (IsFinite.isClosedMap (f := f)).isCoveringMap_of_isLocalHomeomorph
    (fun y ↦ have := IsFinite.finite_fiber (f := f) y; Set.toFinite _)
    IsLocalIso.isLocalHomeomorph

end ComplexAnalytic.AnalyticSpace

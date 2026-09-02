/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.StandardEtaleLocalIsoBase
import Oka.Analytification.StandardEtaleNotLocalIso

/-!
# The projection statement is not vacuous: the node, where both hypotheses hold

`Oka/Analytification/StandardEtaleNotLocalIso.lean` proves
`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp` under two hypotheses — one
of the base's relations is a non-zero polynomial, and the source is not empty — and neither is
witnessed there. **A theorem whose hypotheses nobody has satisfied together is not distinguishable
from a vacuity by reading it**, which is the standard `OkaTest/StandardEtaleLocalIsoBase.lean`
sets for the positive statement on this line, and this file meets it at the same base.

The base is `ComplexAnalytic.nodeG` (`OkaTest/Analytification.lean`): `n = 2`, `k = 1`, the single
relation `z₀ z₁`, so `ℂ[x, y] ⧸ (xy)`. Both hypotheses hold there and neither is free:

* `ComplexAnalytic.nodeG_ne_zero` — the relation is a product of two variables and so is non-zero
  in an integral domain. **This is where `k ≥ 1` is actually used**: at `k = 0` there is no
  relation to be non-zero and the hypothesis is unsatisfiable.
* `ComplexAnalytic.nonempty_analytification_etalePresentation_node`
  (`OkaTest/StandardEtaleLocalIsoBase.lean`, landed as lana-agents/oka#367) — the tuple
  `(0, 0, 1, 1/2)` of `ℂ⁴` satisfies the three relations of the étale presentation. Quoted and not
  rebuilt.

## What the pair of statements says at this base, and it is the point of choosing it

At the node, and at the **same** standard étale data, both of these now hold:

* `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node`
  (`OkaTest/StandardEtaleLocalIsoBase.lean`): the analytification of the standard étale morphism
  **onto the base's own analytification** is a local isomorphism;
* `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp_node` below: the **same
  morphism followed by the inclusion of the base into `ℂ²`** is not.

So the two statements come apart, and the composite is where they do. That is what
`Oka/Analytification/StandardEtaleLocalIso.lean`'s header argues and what taxis #1508's choice of
the node over a degenerate `g` was for: `g = ![0]` presents `ℂ^n` itself, satisfies the first
hypothesis nowhere, and would have witnessed the index rather than the content.

**`ComplexAnalytic.AnalyticSpace.IsLocalIso` does not cancel here**, and that is not a gap in
either file: the second factor of the composite is `ComplexAnalytic.analytificationInclHom nodeG`,
a closed immersion onto a proper subset, and the pair above is a compiled instance of the fact
that the composite's failure is the second factor's and not the first's.

## Main results

- `ComplexAnalytic.nodeG_ne_zero`: the node's relation is a non-zero polynomial.
- `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp_node`: **the standard étale
  projection to `ℂ²` over the node is not a local isomorphism**, which is
  `ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp` at a base and a pair where
  both of its hypotheses are met.

## What is not checked here

* **Only the first of the node's two pairs.** `ComplexAnalytic.nodeEtaleGSubOne`
  (`OkaTest/StandardEtaleLocalIsoBase.lean`) is a second lift with its own local-isomorphism
  witness, and the projection statement holds of it too by the same theorem — but this file does
  not instantiate the theorem there, and does not need to: one satisfied instance settles vacuity.

  **This bullet said the second lift's source-nonemptiness was *not in the repository*, and that
  was true when it was written and is false now.**
  `ComplexAnalytic.nonempty_analytification_etalePresentation_node_sqSubOne`
  (`OkaTest/StandardEtaleLocalIsoBase.lean`) is that space's point, and it discharges the rider
  `oka-slot-2-1c`'s verdict on lana-agents/oka#367 recorded as still owed. **The branch that
  falsified the sentence is the branch repairing it**, in the same push. What the bullet is still
  for is the scope: the projection statement is instantiated here at one lift and not at both.
* **No claim that either hypothesis is necessary.** That `g = 0` makes the conclusion false is
  argued in `Oka/Analytification/StandardEtaleLocalIso.lean`'s prose and is uncompiled; that an
  empty source would satisfy `ComplexAnalytic.AnalyticSpace.IsLocalIso` is a reading of that
  structure's fields.
* **Nothing about finiteness at the node**, in either direction. This file is about one field of
  one class.
-/

open CategoryTheory MvPolynomial

universe u

namespace ComplexAnalytic

noncomputable section

/-! ### The node's relation is not zero -/

/-- **The node's single relation `z₀ z₁` is a non-zero polynomial**, so
`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp`'s properness hypothesis
holds at this base.

`ComplexAnalytic.nodePoly` is `X (ULift.up 0) * X (ULift.up 1)` and `MvPolynomial σ ℂ` is a
domain, so this is `mul_ne_zero` on two variables. Stated rather than inlined because it is the
half of the instantiation that says *`k ≥ 1`*: the hypothesis is an existential over `Fin k` and
is unsatisfiable at `k = 0`. -/
theorem nodeG_ne_zero : ∃ j, nodeG.{u} j ≠ 0 :=
  ⟨0, mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)⟩

/-! ### The projection over the node -/

/-- **The standard étale projection to `ℂ²` over the node is not a local isomorphism.**

`ComplexAnalytic.not_isLocalIso_analytificationMap_etalePresHom_comp` at
`ComplexAnalytic.nodeG`, `ComplexAnalytic.nodeEtaleF` and `ComplexAnalytic.nodeEtaleG`, with the
two hypotheses supplied by `ComplexAnalytic.nodeG_ne_zero` and
`ComplexAnalytic.nonempty_analytification_etalePresentation_node`. An instantiation and not an
argument: nothing is re-proved here.

Read it against `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_node`, which is the
same data without the inclusion into `ℂ²`. -/
theorem not_isLocalIso_analytificationMap_etalePresHom_comp_node :
    ¬ AnalyticSpace.IsLocalIso
      (analytificationMap.{u} (etalePresHom.{u} nodeG.{u} nodeEtaleF.{u} nodeEtaleG.{u}) ≫
        analytificationInclHom.{u} nodeG.{u}) :=
  not_isLocalIso_analytificationMap_etalePresHom_comp.{u} _ _ _ nodeG_ne_zero.{u}
    nonempty_analytification_etalePresentation_node.{u}

end

end ComplexAnalytic

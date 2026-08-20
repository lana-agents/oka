/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka

/-!
# Non-vacuity of the locality of `IsCutOutBy` on the target

`ComplexAnalytic.IsCutOutBy.restrictOpen` says that restricting a closed immersion to the
preimage of an open subset of the target still cuts it out. **At `V = ⊤` that is trivially true**
— the restriction is the original morphism up to the identification of `⊤` with the whole space,
and every one of the four conditions is the one it started with. So the check that matters is an
instantiation at a *proper* open subset of a space that is not `ℂ^n`.

`puncturedAmbient` is `{z₀ ≠ 1}` inside the ambient `ℂ²` of the node, and
`puncturedAmbient_ne_top` shows it is proper by exhibiting the point `(1, 0)` outside it — a
point which lies **on the node**, so the restriction genuinely removes a point of the subspace
and not only of the ambient space. `isCutOutBy_restrict_node` is then the node minus that point,
cut out inside `ℂ² ∖ {z₀ = 1}` by the same equation `z₀ z₁ = 0`.

**What this does not check.** That the *restricted family* is not the zero family, which would
make the cut-out statement much weaker than it looks. `nodeSection` restricted to
`puncturedAmbient` is nonzero — it takes the value `1` at `(1, 1)`, which is in the open set —
but computing that goes through the `OkaRing` of the image open under
`Opens.isOpenEmbedding.isOpenMap.functor`, and it is not done here.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry ComplexAnalytic

universe u

noncomputable section

/-- The open subset `{z₀ ≠ 1}` of the ambient space of the node. -/
def puncturedAmbient : Opens (nodeAmbient.{u}) :=
  ⟨{y : nodeAmbient.{u} | y.1 (ULift.up 0) ≠ 1}, isOpen_compl_singleton.preimage
    ((continuous_apply (ULift.up 0)).comp continuous_subtype_val)⟩

/-- The point `(1, 0)` — which lies **on the node** — is not in it, so this is a **proper** open
subset. The restriction theorem is therefore being instantiated at something other than `⊤`, for
which it is trivially true, and the point it removes is one the subspace actually had. -/
theorem puncturedAmbient_ne_top : puncturedAmbient.{u} ≠ ⊤ := by
  intro hcon
  have h : (⟨fun l ↦ if l = ULift.up 0 then 1 else 0, trivial⟩ : nodeAmbient.{u}) ∈
      puncturedAmbient.{u} := hcon ▸ trivial
  exact h (by simp)

/-- **The node minus the origin is cut out inside `ℂ² ∖ {0}` by the same equation.** -/
theorem isCutOutBy_restrict_node :
    IsCutOutBy (restrictHom (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u})
        puncturedAmbient.{u})
      (restrictSections puncturedAmbient.{u} nodeSection.{u}) :=
  (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}).restrictOpen _

end

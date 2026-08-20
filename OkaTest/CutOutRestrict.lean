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

`puncturedAmbient` is `{z₀ ≠ 1}` inside the ambient `ℂ²` of the node — note that this does
**not** remove the origin, which has `z₀ = 0` and so is in it — and
`puncturedAmbient_ne_top` shows it is proper by exhibiting the point `(1, 0)` outside it — a
point which lies **on the node**, so the restriction genuinely removes a point of the subspace
and not only of the ambient space. `isCutOutBy_restrict_node` is then the node minus that point,
cut out inside `ℂ² ∖ {z₀ = 1}` by the same equation `z₀ z₁ = 0`.

`restrictSections_nodeSection_ne_zero` rules out the reading under which all of this would be
much weaker than it looks: that the *restricted family* is the zero family, in which case
`isCutOutBy_restrict_node` would say only that the empty equation cuts out the whole open set.
The argument does not evaluate the section anywhere. It runs `IsCutOutBy.range_base` of the
**restricted** cut-out backwards: if the family were zero every germ would lie in the maximal
ideal, so the restricted immersion would be surjective onto `puncturedAmbient` — and it is not,
because `(2, 3)` lies in `puncturedAmbient` and off the node. So the proof passes *through* the
`range_base` field of `IsCutOutBy.restrictOpen`, which `isCutOutBy_restrict_node` on its own
does not: that theorem is `hcut.restrictOpen _`, restating the construction rather than
consuming it.

**Provenance.** Two docstrings in this file were wrong when it landed — one said the removed
point was the origin and the ambient open was `ℂ² ∖ {0}`, and the other justified the
non-vanishing of the restricted family by its value at `(1, 1)`, which is **not** in
`{z₀ ≠ 1}`. Both were found by oka-slot-0 reviewing PR #55 (taxis #664), together with the
observation that the gap is closable by running `range_base` backwards. That route is theirs;
the proof below was written against this file, with a different witness point.
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

/-- **The node minus the point `(1, 0)` is cut out inside `ℂ² ∖ {z₀ = 1}` by the same
equation.** -/
theorem isCutOutBy_restrict_node :
    IsCutOutBy (restrictHom (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u})
        puncturedAmbient.{u})
      (restrictSections puncturedAmbient.{u} nodeSection.{u}) :=
  (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}).restrictOpen _

/-! ### The restricted family is not the zero family -/

/-- The point `(2, 3)` of `ℂ²`. -/
def twoThree : nodeAmbient.{u} :=
  ⟨fun l ↦ if l = ULift.up 0 then 2 else 3, trivial⟩

theorem twoThree_mem : twoThree.{u} ∈ puncturedAmbient.{u} := by
  intro hcon
  simp only [twoThree] at hcon
  norm_num at hcon

theorem twoThree_notMem_node :
    twoThree.{u} ∉ nodeAmbient.{u}.zeroLocus nodeSection.{u} := by
  rw [mem_zeroLocus_nodeSection_iff]
  simp only [twoThree]
  norm_num

/-- **The family cutting out the punctured node is not the zero family.**

Without this, `isCutOutBy_restrict_node` would be consistent with the restricted family being
`0`, i.e. with the "subspace" being the whole open set. The proof never evaluates the section:
were the family zero, every germ of it would be a non-unit, so `IsCutOutBy.range_base` of the
restricted cut-out would put every point of `puncturedAmbient` in the image of the restricted
immersion; `(2, 3)` is in `puncturedAmbient` and off the node, so it is not. -/
theorem restrictSections_nodeSection_ne_zero :
    restrictSections puncturedAmbient.{u} nodeSection.{u} ≠ 0 := by
  intro hcon
  set p : nodeAmbient.{u}.restrict puncturedAmbient.{u}.isOpenEmbedding :=
    ⟨twoThree.{u}, twoThree_mem.{u}⟩ with hp
  have hmem : p ∈ Set.range (restrictHom (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u})
      puncturedAmbient.{u}).base := by
    rw [isCutOutBy_restrict_node.range_base]
    intro j
    rw [show restrictSections puncturedAmbient.{u} nodeSection.{u} j = 0 from
      congrFun hcon j, map_zero]
    exact Submodule.zero_mem _
  rw [mem_range_base_restrictHom_iff] at hmem
  obtain ⟨q, hq⟩ := hmem
  refine twoThree_notMem_node.{u} ?_
  have hq' : (q.1 : nodeAmbient.{u}) = twoThree.{u} := hq
  exact hq' ▸ q.2

end

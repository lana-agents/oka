/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import OkaTest.FiniteEtaleCancel

/-!
# The continuity hypothesis of `IsCoveringMap.pullback_snd`, and the witness that it is needed

`IsCoveringMap.pullback_snd` (`Oka/Topology/Covering/Basic.lean`) base-changes a covering map
`f : E → X` along a map `g : Y → X` and asks `g` to be continuous. The set-level statement beside
it, `Function.Pullback.finite_fiber_snd`, asks for no topology at all, so a reader has every reason
to ask what the continuity is spent on. It is spent once, on `g ⁻¹' U` being open for an evenly
covered `U`, and this file compiles the fact that it cannot be recovered: dropping it makes the
conclusion false.

## The witness

`TwoIndiscrete` (`OkaTest/FiniteEtaleCancel.lean`) is a two-element type carrying the indiscrete
topology, introduced there as the non-Hausdorff middle space of
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp`. It is reused rather than re-declared, and
this file adds `TwoIndiscrete.toBool` — the identity of the two elements, read into `Bool` and hence
into the discrete topology — to the same namespace.

Take `f` to be the identity of `Bool`, which is a covering map because both its source and its
target are discrete (`IsCoveringMap.of_discreteTopology`), and take `g` to be
`TwoIndiscrete.toBool`. The pullback is then the graph of `TwoIndiscrete.toBool` inside
`Bool × TwoIndiscrete`, and its first coordinate makes the singleton `{true}` open in it, where the
image of that singleton under `Function.Pullback.snd` is a one-element subset of `TwoIndiscrete`
and so is neither empty nor everything. A covering map is an open map
(`IsCoveringMap.isOpenMap`), so `Function.Pullback.snd` is not one.

**The conjunction says how strong the surviving hypotheses are.** The one hypothesis
`IsCoveringMap.pullback_snd` asks for besides continuity of `g` — that `f` be a covering map —
holds at this witness; the projection is a continuous bijection; and
`Function.Pullback.finite_fiber_snd` applies to it and gives finite fibres, that statement being
independent of the topology, which is the reason the two are stated apart. What fails is the
conclusion of `IsCoveringMap.pullback_snd`, the one of the two that asks for continuity.

## Main results

- `TwoIndiscrete.not_continuous_toBool`: the identity out of the indiscrete two-element space into
  the discrete one is not continuous.
- `TwoIndiscrete.not_isCoveringMap_pullback_snd_of_not_continuous`: **the continuity hypothesis of
  `IsCoveringMap.pullback_snd` cannot be dropped**, stated as one conjunction with the hypotheses
  that do hold at the witness.
-/

namespace TwoIndiscrete

/-- **The two indistinguishable points, read as the two points of `Bool`.** The identity of the
underlying type, so it is a bijection; what it is not is continuous, since its source carries the
indiscrete topology and its target the discrete one.

`TwoIndiscrete` is a `def` and not an `abbrev` for the reason `OkaTest/FiniteEtaleCancel.lean`
gives, so this map has to be written down in order to be spoken about at all: a term of the
underlying type has its type inferred as `Bool` and carries `Bool`'s discrete topology with it. -/
def toBool : TwoIndiscrete → Bool := fun b ↦ b

/-- **The identity out of the indiscrete two-element space is not continuous.** The preimage of
`{true}` is a one-element subset, which under the indiscrete topology is neither empty nor
everything and so is not open (`TopologicalSpace.isOpen_top_iff`). -/
theorem not_continuous_toBool : ¬ Continuous toBool := by
  intro h
  rcases (TopologicalSpace.isOpen_top_iff (toBool ⁻¹' {true})).1
    ((isOpen_discrete _).preimage h) with hc | hc
  · have hmem : ((true : Bool) : TwoIndiscrete) ∈ toBool ⁻¹' {true} := rfl
    rw [hc] at hmem; exact hmem
  · have hmem : ((false : Bool) : TwoIndiscrete) ∈ toBool ⁻¹' {true} := hc ▸ Set.mem_univ _
    exact Bool.false_ne_true hmem

/-- **`Function.Pullback.snd` is not open at this witness**, because the singleton cut out by the
first coordinate is open in the pullback and its image is a one-element subset of `TwoIndiscrete`.

The first coordinate is continuous into a discrete space, so `{p | p.1.1 = true}` is open; its
image under `Function.Pullback.snd` is `TwoIndiscrete.toBool ⁻¹' {true}`, the subset the proof of
`TwoIndiscrete.not_continuous_toBool` above shows is not open. `IsCoveringMap.isOpenMap` is what
turns that into the conclusion. -/
theorem not_isCoveringMap_pullback_snd :
    ¬ IsCoveringMap (Function.Pullback.snd :
      (id : Bool → Bool).Pullback toBool → TwoIndiscrete) := by
  intro h
  have hSopen : IsOpen ((fun p : (id : Bool → Bool).Pullback toBool ↦
      (p : Bool × TwoIndiscrete).1) ⁻¹' {true}) :=
    (continuous_fst.comp continuous_subtype_val).isOpen_preimage _ (isOpen_discrete _)
  have himg : (Function.Pullback.snd : (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ''
      ((fun p : (id : Bool → Bool).Pullback toBool ↦ (p : Bool × TwoIndiscrete).1) ⁻¹' {true})
      = toBool ⁻¹' {true} := by
    ext b
    refine ⟨?_, fun hb ↦ ⟨⟨(true, b), hb.symm⟩, rfl, rfl⟩⟩
    rintro ⟨p, hp, rfl⟩
    exact p.2.symm.trans hp
  have hopen := h.isOpenMap _ hSopen
  rw [himg] at hopen
  rcases (TopologicalSpace.isOpen_top_iff (toBool ⁻¹' {true})).1 hopen with hc | hc
  · have hmem : ((true : Bool) : TwoIndiscrete) ∈ toBool ⁻¹' {true} := rfl
    rw [hc] at hmem; exact hmem
  · have hmem : ((false : Bool) : TwoIndiscrete) ∈ toBool ⁻¹' {true} := hc ▸ Set.mem_univ _
    exact Bool.false_ne_true hmem

/-- **The continuity hypothesis of `IsCoveringMap.pullback_snd` cannot be dropped.**

`¬ Continuous TwoIndiscrete.toBool` is the hypothesis that fails and
`¬ IsCoveringMap Function.Pullback.snd` is the conclusion that fails with it. The conjuncts beside
them say how little else is wrong: the identity of `Bool` is a covering map with finite fibres,
which is everything `IsCoveringMap.pullback_snd` asks for other than the continuity;
`Function.Pullback.snd` out of the base change is continuous and bijective; and its fibres are
finite by `Function.Pullback.finite_fiber_snd`, which asks for no continuity — so what fails is the
covering conclusion and not the fibres.

Stated as one conjunction rather than as separate theorems for the reason
`TwoIndiscrete.not_isClosedMap_pt_of_isClosedMap_comp` gives: each conjunct alone is uninteresting
and what is exhibited is that they hold together. -/
theorem not_isCoveringMap_pullback_snd_of_not_continuous :
    IsCoveringMap (id : Bool → Bool) ∧
      (∀ x, ((id : Bool → Bool) ⁻¹' {x}).Finite) ∧
      Continuous (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ∧
      Function.Bijective (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ∧
      (∀ y, ((Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) ⁻¹' {y}).Finite) ∧
      ¬ Continuous toBool ∧
      ¬ IsCoveringMap (Function.Pullback.snd :
        (id : Bool → Bool).Pullback toBool → TwoIndiscrete) :=
  ⟨IsCoveringMap.of_discreteTopology _, fun _ ↦ Set.toFinite _,
    continuous_snd.comp continuous_subtype_val,
    ⟨by
      intro p p' hpp'
      have h : (p : Bool × TwoIndiscrete).1 = toBool (p : Bool × TwoIndiscrete).2 := p.2
      have h' : (p' : Bool × TwoIndiscrete).1 = toBool (p' : Bool × TwoIndiscrete).2 := p'.2
      exact Subtype.ext (Prod.ext (h.trans ((congrArg toBool hpp').trans h'.symm)) hpp'),
      fun b ↦ ⟨⟨(toBool b, b), rfl⟩, rfl⟩⟩,
    Function.Pullback.finite_fiber_snd fun _ ↦ Set.toFinite _,
    not_continuous_toBool, not_isCoveringMap_pullback_snd⟩

end TwoIndiscrete

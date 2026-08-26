/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Bijectivity read off the sizes of the fibres

Material for `Mathlib/SetTheory/Cardinal/Finite.lean`; see `README.md` on the mirror tree. There
is no complex-analytic content here.

Mathlib relates `Nat.card` to `Function.Bijective` in the *counting* direction — a map between
types of equal finite cardinality is bijective as soon as it is injective
(`Nat.bijective_iff_injective_and_card`) — and it has nothing that reads bijectivity off the
fibres one at a time. That is the form a covering-space argument produces: the number of sheets
is a statement about `f ⁻¹' {b}` for each `b` separately, and `1` is the value at which the
covering is trivial.

**The `1` on the right is doing both halves of the work at once.** `Nat.card_eq_one_iff_unique`
splits it as `Subsingleton` and `Nonempty`, and those are exactly injectivity and surjectivity at
the point `b`. Neither type is assumed finite anywhere: `Nat.card` of an infinite type is `0`, so
the hypothesis `Nat.card (f ⁻¹' {b}) = 1` already rules out an infinite fibre by itself, which is
why this is an honest `↔` and not the usual junk-value trap.
-/

/-- **A map is bijective exactly when every fibre has exactly one point.**

Both directions go through `Nat.card_eq_one_iff_unique`, which turns `Nat.card α = 1` into
`Subsingleton α ∧ Nonempty α`; the first conjunct at `f ⁻¹' {b}` is injectivity of `f` on that
fibre and the second is `b` being in the range.

No finiteness hypothesis is needed on either type, and none is hidden in `Nat.card`: an infinite
fibre has `Nat.card` equal to `0`, not to `1`. -/
theorem Function.bijective_iff_forall_card_preimage_eq_one {α β : Type*} (f : α → β) :
    Function.Bijective f ↔ ∀ b, Nat.card (f ⁻¹' {b}) = 1 := by
  constructor
  · intro hf b
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y ↦ Subtype.ext (hf.injective ?_)⟩, ?_⟩
    · have hx : f x.1 = b := x.2
      have hy : f y.1 = b := y.2
      rw [hx, hy]
    · obtain ⟨a, ha⟩ := hf.surjective b
      exact ⟨⟨a, ha⟩⟩
  · intro h
    refine ⟨fun x y hxy ↦ ?_, fun b ↦ ?_⟩
    · have hsub : Subsingleton (f ⁻¹' {f y}) := (Nat.card_eq_one_iff_unique.mp (h (f y))).1
      exact congrArg Subtype.val
        (hsub.elim (⟨x, show f x = f y from hxy⟩) (⟨y, show f y = f y from rfl⟩))
    · obtain ⟨⟨a, ha⟩⟩ := (Nat.card_eq_one_iff_unique.mp (h b)).2
      exact ⟨a, ha⟩

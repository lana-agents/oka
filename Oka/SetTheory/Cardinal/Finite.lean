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

**Mathlib already reads bijectivity off the fibres one at a time**, as
`Function.bijective_iff_existsUnique` — `Bijective f ↔ ∀ b, ∃! a, f a = b`. What it does not have
is that statement in the `Nat.card` spelling, and it relates `Nat.card` to `Function.Bijective`
only in the *counting* direction: a map between types of equal finite cardinality is bijective as
soon as it is injective (`Nat.bijective_iff_injective_and_card`). So the gap is a translation and
not a theorem, which is why the proof below is a `simp only` between the two spellings followed by
a transposition of `∃!` against `Subsingleton`-and-inhabited.

The `Nat.card` spelling is the one a covering-space argument produces: the number of sheets is
`Nat.card (f ⁻¹' {b})` for each `b` separately, and `1` is the value at which the covering is
trivial.

**The `1` on the right is doing both halves of the work at once.** `Nat.card_eq_one_iff_unique`
splits it as `Subsingleton` and `Nonempty`, and those are exactly injectivity and surjectivity at
the point `b`. Neither type is assumed finite anywhere: `Nat.card` of an infinite type is `0`, so
the hypothesis `Nat.card (f ⁻¹' {b}) = 1` already rules out an infinite fibre by itself, which is
why this is an honest `↔` and not the usual junk-value trap.
-/

/-- **A map is bijective exactly when every fibre has exactly one point.**

The `Nat.card` spelling of `Function.bijective_iff_existsUnique`, which is what the proof reduces
to: `Nat.card_eq_one_iff_unique` turns `Nat.card (f ⁻¹' {b}) = 1` into `Subsingleton` and
`Nonempty` of the fibre, `Set.subsingleton_coe` and `Set.preimage_singleton_nonempty` read those
as `(f ⁻¹' {b}).Subsingleton` and `b ∈ Set.range f` — injectivity of `f` on that fibre and `b`
being in the range — and what is left is `∃!` against those two.

No finiteness hypothesis is needed on either type, and none is hidden in `Nat.card`: an infinite
fibre has `Nat.card` equal to `0`, not to `1`. -/
theorem Function.bijective_iff_forall_card_preimage_eq_one {α β : Type*} (f : α → β) :
    Function.Bijective f ↔ ∀ b, Nat.card (f ⁻¹' {b}) = 1 := by
  simp only [Function.bijective_iff_existsUnique, Nat.card_eq_one_iff_unique,
    Set.subsingleton_coe, Set.nonempty_coe_sort, Set.preimage_singleton_nonempty]
  refine forall_congr' fun b ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, ha, hu⟩ := h
    exact ⟨fun x hx y hy ↦ (hu x hx).trans (hu y hy).symm, a, ha⟩
  · obtain ⟨hs, a, ha⟩ := h
    exact ⟨a, ha, fun y hy ↦ hs hy ha⟩

/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The fibres of a map, counted

Material for `Mathlib/SetTheory/Cardinal/Finite.lean`; see `README.md` on the mirror tree. There
is no complex-analytic content here.

**The title of this file used to be *Bijectivity read off the sizes of the fibres*, which is what
`Function.bijective_iff_forall_card_preimage_eq_one` is about and is no longer what the file is
about.** `Set.preimageCompEquivSigma` and `Nat.card_preimage_singleton_comp` below are about the
fibres of a *composite*, and neither mentions bijectivity; the widened title is the repair, and
the paragraphs each declaration is described by are kept apart under their own headings rather
than merged.

## Bijectivity read off the sizes of the fibres

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

## The fibres of a composite

`Set.preimageCompEquivSigma` splits the fibre of `g ∘ f` over a point of the target into the
fibres of `f` over the points of the fibre of `g`, **as an equivalence and not as a count**: it
assumes nothing at all — no finiteness, no decidability, no hypothesis relating the two maps — and
it is the statement the count below is the only consumer of so far.

**Mathlib's `Equiv.sigmaFiberEquiv` is the same idea one level up**, splitting a whole type into
the fibres of a map out of it. Getting the statement here from it means restricting along the
inclusion of `(g ∘ f) ⁻¹' {z}` and then simplifying a subtype of a subtype at each point, which is
longer than writing the equivalence out; so it is written out, and its `right_inv` is the only
field with anything in it — a `subst` of the equation carried by the second component, after which
proof irrelevance closes the goal.

`Nat.card_preimage_singleton_comp` is the count that follows: **if every fibre of `f` has `d`
points then the fibre of `g ∘ f` over `z` has `Nat.card (g ⁻¹' {z}) * d`.** The uniform `d` is a
hypothesis and not a conclusion; nothing here says why the fibres of a map would all have the same
size, and in the covering-space setting that is a theorem about a preconnected base rather than
anything a counting lemma can supply.

**The finiteness hypotheses are `Finite` instances and are genuinely needed as instances, not as
`Fintype`s.** `Nat.card_sigma` asks for a `Fintype` on the index type and `Finite` on the fibres;
the `Fintype` is produced by `Fintype.ofFinite` inside the proof, under `classical`, so that no
caller has to carry a decidable equality it does not have. **Whether the hypotheses can be dropped
outright is not settled here** — `Nat.card` of an infinite type is `0`, so both sides degenerate
together in the cases one would check first, but that is an argument and not a proof, and the
statement is used only where the fibres are finite for a structural reason.

## Neither declaration is advertised, because this file advertises nothing

There is no `## Main results` heading here and none is added. `scripts/guard_coverage.py` reads
such a heading as the list of what a file advertises, and this file has never had one;
`Function.bijective_iff_forall_card_preimage_eq_one` is unadvertised for that reason and so is
everything under this heading. **Guarding is a separate matter and is not skipped**:
`OkaTest/Axioms/Morphisms.lean` carries the `#print axioms` guards, beside the `IsCoveringMap`
guards it already holds for `Oka/Topology/Covering/Basic.lean`, which is the precedent for a
mirror-tree file's declarations being guarded under the topic of the analytic statement that
consumes them.
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

/-- **The fibre of a composite over a point, as a sigma of the fibres of the first map.**

`(g ∘ f) ⁻¹' {z}` is the set of points `x` with `g (f x) = z`; sending such an `x` to the pair
consisting of `f x` — which lies in `g ⁻¹' {z}` — and of `x` itself — which lies in the fibre of
`f` over `f x` — is a bijection, and its inverse forgets the first component.

**Nothing is assumed**: the types are arbitrary, the maps are arbitrary, and no finiteness and no
decidability enters. `Nat.card_preimage_singleton_comp` below is the count this makes available
once the fibres are finite.

**Membership in a singleton preimage is definitionally the equation**, which is what makes
`toFun` and `left_inv` proofs by `rfl`: `x.2` has type `(g ∘ f) x = z` and is accepted where
`f x ∈ g ⁻¹' {z}` is expected. Only `right_inv` has content, and it is a `subst` of the equation
the second component carries followed by proof irrelevance. -/
def Set.preimageCompEquivSigma {α β γ : Type*} (f : α → β) (g : β → γ) (z : γ) :
    ((g ∘ f) ⁻¹' {z} : Set α) ≃ Σ y : (g ⁻¹' {z} : Set β), (f ⁻¹' {(y : β)} : Set α) where
  toFun x := ⟨⟨f x.1, x.2⟩, ⟨x.1, rfl⟩⟩
  invFun p := ⟨p.2.1, show g (f p.2.1) = z by rw [show f p.2.1 = p.1.1 from p.2.2]; exact p.1.2⟩
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨⟨y, hy⟩, ⟨a, ha⟩⟩ := p
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha
    subst ha
    rfl

/-- **A map all of whose fibres have `d` points multiplies the size of a fibre by `d`.**

`Set.preimageCompEquivSigma` transports the fibre of `g ∘ f` over `z` to a sigma type, `Nat.card`
of a sigma over a finite index type is the sum of the cardinalities, and the hypothesis makes
every summand `d`.

**The uniform `d` is a hypothesis about every point of `β` and not only about the points of
`g ⁻¹' {z}`**, which is more than the proof uses and is what every caller has: it is the form
`Function.bijective_iff_forall_card_preimage_eq_one` above is stated in, and the form a constant
fibre count over a connected base arrives in.

**The `Fintype` is manufactured inside the proof.** `Nat.card_sigma` asks for one on the index
type; `Fintype.ofFinite` under `classical` supplies it from the `Finite` instance, so the
statement asks for no decidable equality on `β`. -/
theorem Nat.card_preimage_singleton_comp {α β γ : Type*} (f : α → β) (g : β → γ) (z : γ)
    [Finite ((g ⁻¹' {z}) : Set β)] [∀ y : β, Finite ((f ⁻¹' {y}) : Set α)] {d : ℕ}
    (hf : ∀ y : β, Nat.card ((f ⁻¹' {y}) : Set α) = d) :
    Nat.card (((g ∘ f) ⁻¹' {z}) : Set α) = Nat.card ((g ⁻¹' {z}) : Set β) * d := by
  classical
  letI : Fintype ((g ⁻¹' {z}) : Set β) := Fintype.ofFinite _
  rw [Nat.card_congr (Set.preimageCompEquivSigma f g z), Nat.card_sigma]
  simp [hf, Nat.card_eq_fintype_card, mul_comm]

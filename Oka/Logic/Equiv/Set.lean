/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Logic.Equiv.Set

/-!
# The fibre of a composite, as a sigma of the fibres of the first map

Material for `Mathlib/Logic/Equiv/Set.lean`; see `README.md` on the mirror tree. There is no
complex-analytic content here.

`Set.preimageCompEquivSigma` splits the fibre of `g ∘ f` over a point of the target into the
fibres of `f` over the points of the fibre of `g`, **as an equivalence and not as a count**: it
assumes nothing at all — no finiteness, no decidability, no hypothesis relating the two maps.

## Why the destination is this file and not the one this statement was written in

It was declared in `Oka/SetTheory/Cardinal/Finite.lean`, beside
`Nat.card_preimage_singleton_comp`, which is its only consumer in this repository. **That file
claims `Mathlib/SetTheory/Cardinal/Finite.lean` as its destination and this statement could not
go there**: it mentions no `Nat.card` and no `Cardinal`. `README.md`'s mirror-tree section asks
that a mirror file's declarations all be placeable where its docstring says, on the ground that a
file mixing destinations tells a Mathlib reviewer something untrue.

**`Mathlib/Logic/Equiv/Set.lean` is where the nearest Mathlib statement lives**, and it is
`Equiv.sigmaPreimageEquiv` — `(Σ b, f ⁻¹' {b}) ≃ α`, the total space split into the preimages of
points, in the same preimage-of-a-singleton spelling as the statement below. Mathlib's own
`Equiv.sigmaFiberEquiv`, which is the subtype spelling of the same fact and which
`Oka/SetTheory/Cardinal/Finite.lean` used to name as the neighbour, carries a comment pointing at
`Equiv.sigmaPreimageEquiv` for exactly this reason.

**Both directions of the import were measured with `scripts/import_cost.py`, at the Mathlib
revision `lakefile.toml` pins, rather than guessed.** `Mathlib/SetTheory/Cardinal/Finite.lean`
already has `Mathlib/Logic/Equiv/Set.lean` in its transitive closure, so a consumer importing
this file pays **0**; and
`Mathlib/Logic/Equiv/Set.lean` needs nothing added to host the statement below, so the
destination claim costs **0** in that direction too. Neither figure holds for the other Mathlib
file this statement is near: hosting it in `Mathlib/Logic/Equiv/Sum.lean`, where
`Equiv.sigmaFiberEquiv` is, would cost that file **6** modules for `Mathlib.Data.Set.Operations`
and **46** for `Mathlib.Data.Set.Basic`, since it has no `Set` theory at all.

## Deriving it from Mathlib, and the measurement that was on record was wrong

`Oka/SetTheory/Cardinal/Finite.lean` used to say that getting this statement out of
`Equiv.sigmaFiberEquiv` — by restricting along the inclusion of `(g ∘ f) ⁻¹' {z}` and then
reconciling a subtype of a subtype at each point — **is *longer than writing the equivalence
out*. It is not: the two spellings are the same length**, ten non-blank lines each including the
shared signature, and both were elaborated before this sentence was written.

What the derivation does not do is avoid building an equivalence by hand: the
subtype-of-a-subtype step is itself a four-field `Equiv` passed to `Equiv.sigmaCongrRight`. So
citing the Mathlib statement relocates the hand construction rather than removing it, and **that,
rather than a line count, is why the statement is written out below**.
-/

/-- **The fibre of a composite over a point, as a sigma of the fibres of the first map.**

`(g ∘ f) ⁻¹' {z}` is the set of points `x` with `g (f x) = z`; sending such an `x` to the pair
consisting of `f x` — which lies in `g ⁻¹' {z}` — and of `x` itself — which lies in the fibre of
`f` over `f x` — is a bijection, and its inverse forgets the first component.

**Nothing is assumed**: the types are arbitrary, the maps are arbitrary, and no finiteness and no
decidability enters. `Nat.card_preimage_singleton_comp`
(`Oka/SetTheory/Cardinal/Finite.lean`) is the count this makes available once the fibres are
finite, and is this repository's only consumer of it.

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

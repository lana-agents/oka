/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Maps

/-!
# Finite generation of an ideal transported along a ring isomorphism

Material for `Mathlib/RingTheory/Ideal/Maps.lean`, whose `Ideal.comap_symm` and `Ideal.map_symm`
are the neighbouring API; see `README.md` on the mirror tree. Upstreaming it adds
`Mathlib.RingTheory.Finiteness.Ideal`, which `Ideal.FG` needs, to a target whose closure is
**1028** Mathlib modules — **39** new ones, measured with `scripts/import_cost.py`. **A cheaper
destination exists and this file does not choose it**: priced into
`Mathlib/RingTheory/Finiteness/Ideal.lean`, which is where `Ideal.FG` lives, the lemma costs
**0**. Taxis #935 is where that is decided.

Mathlib has `Ideal.FG.map` in the forward direction, and `Submodule.fg_map_iff` for
`Submodule.map` along an injective *linear* map; `Ideal.map` along a ring homomorphism is a
different operation, and nothing transports `Ideal.FG` backwards along a `RingEquiv`. The proof
below is the forward lemma applied to `e.symm`.

## Main results

- `Ideal.FG.of_map_ringEquiv`: finite generation of an ideal can be checked after transporting it
  along a ring isomorphism.
-/

/-- Finite generation of an ideal can be checked after transporting it along a ring
isomorphism. -/
theorem Ideal.FG.of_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {I : Ideal A} (h : (I.map (e : A →+* B)).FG) : I.FG := by
  have h2 := h.map (e.symm : B →+* A)
  rwa [Ideal.map_map, show (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A from
    RingHom.ext e.symm_apply_apply, Ideal.map_id] at h2

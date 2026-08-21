/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# The projections of an adic completion are compatible with each other

Material for `Mathlib/RingTheory/AdicCompletion/Algebra.lean`; see `README.md` on the mirror tree.

`AdicCompletion.evalₐ I n : AdicCompletion I R →ₐ[R] R ⧸ I ^ n` is the `n`-th projection of the
`I`-adic completion of a ring. That these projections are compatible — that `R ⧸ I ^ k → R ⧸ I ^ j`
carries the `k`-th to the `j`-th — is the defining property of the completion, and Mathlib states
it for the module-level projection `AdicCompletion.eval`
(`AdicCompletion.transitionMap_comp_eval_apply`) but not for `evalₐ`, whose target is the honest
ideal quotient `R ⧸ I ^ n` rather than `R ⧸ (I ^ n • ⊤)`.

Everything needed is already there — `AdicCompletion.mk_surjective`, `AdicCompletion.evalₐ_mk`
and `AdicCompletion.Ideal.mk_eq_mk` — so this is three lines; it is here because a consumer that
has to rediscover it pays more than that.

## Main results

- `AdicCompletion.factorPow_evalₐ`: the projections of `AdicCompletion I R` to the quotients
  `R ⧸ I ^ n` form a compatible family.
-/

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- **The projections of an adic completion to `R ⧸ I ^ n` are a compatible family**: reducing
the `k`-th projection modulo `I ^ j` gives the `j`-th, for `j ≤ k`.

This is `AdicCompletion.transitionMap_comp_eval_apply` for `AdicCompletion.evalₐ` in place of
`AdicCompletion.eval`, i.e. with the quotients taken as ideal quotients rather than as
`R ⧸ (I ^ n • ⊤)`. -/
theorem factorPow_evalₐ {j k : ℕ} (hjk : j ≤ k) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hjk (AdicCompletion.evalₐ I k x) = AdicCompletion.evalₐ I j x := by
  obtain ⟨r, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk I hjk]

end AdicCompletion

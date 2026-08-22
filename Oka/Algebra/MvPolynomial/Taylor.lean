/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Shifting the variables of a multivariate polynomial

Material for `Mathlib/Algebra/MvPolynomial/Taylor.lean`; see `README.md` on the mirror tree.

Mathlib has `Polynomial.taylor` and `Polynomial.taylorEquiv` in one variable. This file is the
multivariate analogue: substituting `xᵢ + zᵢ` for `xᵢ` is an `R`-algebra automorphism of
`MvPolynomial σ R`, and the coefficients of the image of `p` are the Taylor coefficients of `p`
at `z`.

## Main definitions

- `MvPolynomial.taylorAlgHom z`: the substitution `p ↦ p(x + z)`.
- `MvPolynomial.taylorEquiv z`: the same map as an algebra automorphism, its inverse being the
  substitution at `-z`.

## Main results

- `MvPolynomial.eval_taylorAlgHom`: `p(x + z)` evaluated at `w` is `p` evaluated at `w + z`.
  This is the reason to have the definition: it is what turns a statement at a general point
  into the corresponding statement at the origin.
-/

noncomputable section

namespace MvPolynomial

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Shifting the variables by `z`, i.e. `p ↦ p(x + z)`. Its coefficients are the Taylor
coefficients of `p` at `z`, which is the multivariate analogue of `Polynomial.taylor`. -/
def taylorAlgHom (z : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ X i + C (z i)

@[simp]
theorem taylorAlgHom_X (z : σ → R) (i : σ) : taylorAlgHom z (X i) = X i + C (z i) := by
  simp [taylorAlgHom]

-- Not `@[simp]`: `simp` proves it already, from `MvPolynomial.algHom_C`. It is here as the
-- companion of `MvPolynomial.taylorAlgHom_X` — shifting the variables fixes the constants —
-- which is what `MvPolynomial.algHom_ext` reduces every statement about it to.
theorem taylorAlgHom_C (z : σ → R) (r : R) : taylorAlgHom z (C r) = C r :=
  (taylorAlgHom z).commutes r

@[simp]
theorem taylorAlgHom_zero : taylorAlgHom (0 : σ → R) = AlgHom.id R (MvPolynomial σ R) := by
  refine algHom_ext fun i ↦ ?_
  simp

/-- Shifting by `w` and then by `z` is shifting by `z + w`. -/
theorem taylorAlgHom_comp (z w : σ → R) :
    (taylorAlgHom z).comp (taylorAlgHom w) = taylorAlgHom (z + w) := by
  refine algHom_ext fun i ↦ ?_
  simp [add_assoc]

/-- **Shifting the variables shifts the point of evaluation**: `p(x + z)` at `w` is `p` at
`w + z`. -/
@[simp]
theorem eval_taylorAlgHom (z w : σ → R) (p : MvPolynomial σ R) :
    eval w (taylorAlgHom z p) = eval (w + z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end CommSemiring

section CommRing

variable [CommRing R]

/-- Shifting the variables by `z` is an automorphism of `MvPolynomial σ R`, the multivariate
analogue of `Polynomial.taylorEquiv`. -/
def taylorEquiv (z : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (taylorAlgHom z) (taylorAlgHom (-z))
    (by rw [taylorAlgHom_comp, add_neg_cancel, taylorAlgHom_zero])
    (by rw [taylorAlgHom_comp, neg_add_cancel, taylorAlgHom_zero])

@[simp]
theorem taylorEquiv_apply (z : σ → R) (p : MvPolynomial σ R) :
    taylorEquiv z p = taylorAlgHom z p :=
  rfl

@[simp]
theorem taylorEquiv_symm_apply (z : σ → R) (p : MvPolynomial σ R) :
    (taylorEquiv z).symm p = taylorAlgHom (-z) p :=
  rfl

end CommRing

end MvPolynomial

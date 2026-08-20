/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Coefficient fields of local rings

Material for `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean`; see `README.md` on the
mirror tree.

A ring homomorphism `α : K →+* S` from a field into a local ring makes `K` a **coefficient
field** of `S` when every element of `S` is congruent to a constant `α c` modulo the maximal
ideal — equivalently, when `K → S → S ⧸ 𝔪` is an isomorphism, the constant being then unique.
This is the classical notion from Cohen structure theory, and it is what says "the residue field
of `S` is `K`" in the form the applications want: not merely that `ResidueField S` happens to be
isomorphic to `K`, but that a *chosen* `K`-algebra structure realises it, so that the resulting
`S →+* K` deserves to be called evaluation.

Nothing here is specific to any one `K`: the intended application is `K = ℂ` and `S` a stalk of
the structure sheaf of a complex analytic space, where `α` is the germ of a constant function
and `IsCoefficientField.evalHom` is the value of a germ at the point.

## Main definitions

- `IsLocalRing.IsCoefficientField`: `α : K →+* S` realises the field `K` as a coefficient field
  of the local ring `S`.
- `IsLocalRing.IsCoefficientField.residueFieldEquiv`: the induced isomorphism
  `ResidueField S ≃+* K`.
- `IsLocalRing.IsCoefficientField.evalHom`: the induced ring homomorphism `S →+* K`, a retraction
  of `α` with kernel the maximal ideal.

## Main results

- `IsLocalRing.IsCoefficientField.evalHom_eq_iff`: the value of `a` is `c` exactly when `a - α c`
  lies in the maximal ideal. This characterises `evalHom` without reference to the residue field,
  and is what every consumer of a value should use.
- `IsLocalRing.IsCoefficientField.existsUnique_sub_mem_maximalIdeal`: the constant is unique.
- `IsLocalRing.IsCoefficientField.of_surjective`: a coefficient field is inherited by any
  quotient, more precisely by the target of any surjective ring homomorphism compatible with the
  constants. This is the transport principle that makes the notion usable: local rings are
  usually reached from a ring one understands by a surjection.
- `IsLocalRing.IsCoefficientField.evalHom_map`: such a surjection commutes with evaluation.
-/

namespace IsLocalRing

variable {K S T : Type*} [Field K] [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]

/-- A ring homomorphism `α : K →+* S` from a field into a local ring realises `K` as a
**coefficient field** of `S` if every element of `S` differs from a constant `α c` by an element
of the maximal ideal.

The constant is then automatically unique
(`IsLocalRing.IsCoefficientField.existsUnique_sub_mem_maximalIdeal`), because a nonzero constant
is a unit; equivalently, the composite `K → S → ResidueField S` is a ring isomorphism
(`IsLocalRing.IsCoefficientField.residueFieldEquiv`). -/
def IsCoefficientField (α : K →+* S) : Prop :=
  ∀ a : S, ∃ c : K, a - α c ∈ maximalIdeal S

variable {α : K →+* S} {β : K →+* T}

namespace IsCoefficientField

lemma surjective (h : IsCoefficientField α) :
    Function.Surjective ((residue S).comp α) := fun a ↦ by
  obtain ⟨b, rfl⟩ := residue_surjective a
  obtain ⟨c, hc⟩ := h b
  exact ⟨c, (Ideal.Quotient.eq.2 hc).symm⟩

lemma bijective (h : IsCoefficientField α) :
    Function.Bijective ((residue S).comp α) :=
  ⟨((residue S).comp α).injective, h.surjective⟩

/-- The residue field of `S`, identified with the coefficient field `K`. -/
noncomputable def residueFieldEquiv (h : IsCoefficientField α) : ResidueField S ≃+* K :=
  (RingEquiv.ofBijective _ h.bijective).symm

@[simp]
lemma residueFieldEquiv_residue (h : IsCoefficientField α) (c : K) :
    h.residueFieldEquiv (residue S (α c)) = c :=
  (RingEquiv.ofBijective _ h.bijective).symm_apply_apply c

/-- **The value of an element of `S` in the coefficient field `K`.**

For a stalk of the structure sheaf of a complex analytic space this is the value of a germ at
the point; the maximal ideal is its kernel (`IsCoefficientField.evalHom_eq_zero_iff`) and the
constants are fixed (`IsCoefficientField.evalHom_const`). -/
noncomputable def evalHom (h : IsCoefficientField α) : S →+* K :=
  h.residueFieldEquiv.toRingHom.comp (residue S)

@[simp]
lemma evalHom_const (h : IsCoefficientField α) (c : K) : h.evalHom (α c) = c :=
  h.residueFieldEquiv_residue c

@[simp]
lemma evalHom_eq_zero_iff (h : IsCoefficientField α) {a : S} :
    h.evalHom a = 0 ↔ a ∈ maximalIdeal S := by
  rw [show h.evalHom a = h.residueFieldEquiv (residue S a) from rfl,
    map_eq_zero_iff _ h.residueFieldEquiv.injective, residue_eq_zero_iff]

/-- **The value of `a` is `c` exactly when `a` differs from the constant `c` by an element of the
maximal ideal.**

This is the characterisation of `IsCoefficientField.evalHom`, and it is what makes it usable:
`evalHom` is defined through the residue field, but nothing that consumes a value needs to know
that. In particular an equation between values transports along any local homomorphism, because
membership in the maximal ideal does. -/
lemma evalHom_eq_iff (h : IsCoefficientField α) {a : S} {c : K} :
    h.evalHom a = c ↔ a - α c ∈ maximalIdeal S := by
  rw [← h.evalHom_eq_zero_iff, map_sub, h.evalHom_const, sub_eq_zero]

lemma sub_evalHom_mem (h : IsCoefficientField α) (a : S) :
    a - α (h.evalHom a) ∈ maximalIdeal S :=
  h.evalHom_eq_iff.1 rfl

/-- **Every element of `S` is congruent to a unique constant modulo the maximal ideal.**

Existence is the definition of a coefficient field; uniqueness holds for any homomorphism from a
field, because the difference of two distinct constants is a unit. Both halves are
`IsCoefficientField.evalHom_eq_iff` read in the two directions. -/
theorem existsUnique_sub_mem_maximalIdeal (h : IsCoefficientField α) (a : S) :
    ∃! c : K, a - α c ∈ maximalIdeal S :=
  ⟨h.evalHom a, h.sub_evalHom_mem a, fun _ hc ↦ (h.evalHom_eq_iff.2 hc).symm⟩

/-- **A coefficient field is inherited along a surjection compatible with the constants.**

The hypothesis `hcomp` is the compatibility of the two `K`-algebra structures; `f` is
automatically a local homomorphism, since a surjection of local rings is
(`IsLocalHom.of_surjective`). -/
theorem of_surjective (h : IsCoefficientField α) {f : S →+* T} (hf : Function.Surjective f)
    (hcomp : ∀ c, f (α c) = β c) : IsCoefficientField β := by
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  intro b
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨c, hc⟩ := h a
  exact ⟨c, by rw [← hcomp c, ← map_sub]; exact map_nonunit f _ hc⟩

/-- Evaluation commutes with a surjection compatible with the constants: the value of `f a` in
`K` is the value of `a`. -/
theorem evalHom_map (h : IsCoefficientField α) {f : S →+* T} (hf : Function.Surjective f)
    (hcomp : ∀ c, f (α c) = β c) (a : S) :
    (h.of_surjective hf hcomp).evalHom (f a) = h.evalHom a := by
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  refine ((h.of_surjective hf hcomp).existsUnique_sub_mem_maximalIdeal (f a)).unique
    ((h.of_surjective hf hcomp).sub_evalHom_mem _) ?_
  rw [← hcomp (h.evalHom a), ← map_sub]
  exact map_nonunit f _ (h.sub_evalHom_mem a)

/-- **A local homomorphism out of a local ring with a coefficient field is determined modulo
`𝔪 ^ k` by its values on the constants and on generators of the maximal ideal.**

The induction is the whole content: an element is a constant plus an element of `𝔪`, and an
element of `𝔪` is an `S`-combination of the generators, so the difference of the two values is a
sum of terms `θ (v i) * (θ x - θ' x)` with the second factor in `𝔪 ^ k` by induction. Each
`θ (v i)` lies in the maximal ideal of `A` because `θ` is local and `v i` is a non-unit. -/
theorem sub_mem_pow_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    (h : IsCoefficientField α) {ι : Type*} [Finite ι] {v : ι → S}
    (hv : maximalIdeal S = Ideal.span (Set.range v))
    {θ θ' : S →+* A} [IsLocalHom θ] (hconst : ∀ c, θ (α c) = θ' (α c))
    (hgen : ∀ i, θ (v i) = θ' (v i)) (k : ℕ) (x : S) :
    θ x - θ' x ∈ maximalIdeal A ^ k := by
  cases nonempty_fintype ι
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := h x
    rw [hv] at hc
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
    have hx : x = α c + ∑ i, q i * v i := by
      rw [show ∑ i, q i * v i = ∑ i, q i • v i from rfl, hq]
      ring
    have hstep : θ x - θ' x = ∑ i, θ (v i) * (θ (q i) - θ' (q i)) := by
      rw [hx, map_add, map_add, map_sum, map_sum, hconst c, add_sub_add_left_eq_sub,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, map_mul, hgen i]; ring
    rw [hstep, pow_succ']
    refine Submodule.sum_mem _ fun i _ ↦ Ideal.mul_mem_mul ?_ (ih (q i))
    exact map_nonunit θ _ (hv ▸ Ideal.subset_span ⟨i, rfl⟩)

/-- **A local homomorphism out of a local ring with a coefficient field, into a Noetherian local
ring, is determined by its values on the constants and on generators of the maximal ideal.**

`IsLocalRing.IsCoefficientField.sub_mem_pow_maximalIdeal` puts the difference of the two values
in every power of the maximal ideal of the target; Krull's intersection theorem
(`Ideal.iInf_pow_eq_bot_of_isLocalRing`, which is where the Noetherian hypothesis enters) then
says it is zero.

The hypothesis that the maximal ideal of `S` is *finitely* generated cannot be dropped in this
form, since the induction consumes a finite sum; `S` itself need not be Noetherian. -/
theorem ringHom_ext {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h : IsCoefficientField α) {ι : Type*} [Finite ι] {v : ι → S}
    (hv : maximalIdeal S = Ideal.span (Set.range v))
    {θ θ' : S →+* A} [IsLocalHom θ] (hconst : ∀ c, θ (α c) = θ' (α c))
    (hgen : ∀ i, θ (v i) = θ' (v i)) :
    θ = θ' := by
  refine RingHom.ext fun x ↦ sub_eq_zero.1 ?_
  have hmem : θ x - θ' x ∈ ⨅ k : ℕ, maximalIdeal A ^ k :=
    Ideal.mem_iInf.2 fun k ↦ h.sub_mem_pow_maximalIdeal hv hconst hgen k x
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top,
    Ideal.mem_bot] at hmem

end IsCoefficientField

end IsLocalRing

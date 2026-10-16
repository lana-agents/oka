/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.UnitInterval

/-!
# Group-valued functions on homotopy classes of paths

This file contains the bookkeeping device behind the Seifert–van Kampen theorem in
`Oka/Topology/VanKampen/Cover.lean` and `Oka/Topology/VanKampen/Basic.lean`.

A `VanKampen.PathClassHom Y K` is a function from homotopy classes of paths in `Y` to a group `K`
that turns concatenation of paths into multiplication; equivalently, a functor from the
fundamental groupoid of `Y` to the one-object groupoid `K`. Such functions pull back along
continuous maps (`VanKampen.PathClassHom.comap`).

On a simply connected space all paths between two given points are homotopic, so the value of
`Ψ : PathClassHom Z K` on a path from `z` to `z'` only depends on `z` and `z'`: this is
`VanKampen.PathClassHom.val Ψ z z'`. The point of this is that all relations between such
values (`VanKampen.PathClassHom.val_mul_val`, `VanKampen.PathClassHom.val_symm`) hold for free,
which is what makes the subdivision arguments for van Kampen painless: a segment of a path, or a
small rectangle of a homotopy, is parametrised by a convex, hence simply connected, set.

## Main definitions

- `VanKampen.PathClassHom`: multiplicative functions on homotopy classes of paths.
- `VanKampen.PathClassHom.comap`: pull back along a continuous map.
- `VanKampen.PathClassHom.val`: the value between two points of a simply connected space.
- `VanKampen.codRestrict`: a continuous map with values in a set, as a map to the subtype.

We also record that the unit interval and its closed subintervals `Set.uIcc a b` are
contractible.
-/

open Set unitInterval

universe u

namespace VanKampen

section codRestrict

variable {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X]

/-- A continuous map with values in a set `s`, viewed as a continuous map to the subtype `s`. -/
def codRestrict (g : C(Z, X)) (s : Set X) (h : ∀ z, g z ∈ s) : C(Z, s) where
  toFun z := ⟨g z, h z⟩

@[simp]
theorem codRestrict_apply (g : C(Z, X)) (s : Set X) (h : ∀ z, g z ∈ s) (z : Z) :
    codRestrict g s h z = ⟨g z, h z⟩ :=
  rfl

end codRestrict

/-- The unit interval is contractible. -/
instance contractibleSpace_unitInterval : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, unitInterval.zero_mem⟩

/-- Closed subintervals of the unit interval are contractible. -/
instance contractibleSpace_uIcc (a b : I) : ContractibleSpace (uIcc a b) := by
  have hc : Convex ℝ (Subtype.val '' uIcc a b) := by
    rw [uIcc, image_subtype_val_Icc]
    exact convex_Icc _ _
  haveI := hc.contractibleSpace ⟨_, mem_image_of_mem _ (left_mem_uIcc (a := a) (b := b))⟩
  exact (Topology.IsEmbedding.subtypeVal.homeomorphImage (uIcc a b)).contractibleSpace

/-- A function from homotopy classes of paths in `Y` to the group `K` that turns concatenation
of paths into multiplication. Equivalently, a functor from the fundamental groupoid of `Y` to `K`
viewed as a one-object groupoid. -/
structure PathClassHom (Y : Type*) [TopologicalSpace Y] (K : Type*) [Group K] where
  /-- The value on a homotopy class of paths. -/
  toFun : ∀ {a b : Y}, Path.Homotopic.Quotient a b → K
  /-- Concatenation goes to multiplication. -/
  map_trans' : ∀ {a b c : Y} (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c), toFun (p.trans q) = toFun p * toFun q

namespace PathClassHom

variable {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y'] {K : Type*} [Group K]
  (Ψ : PathClassHom Y K)

theorem map_trans {a b c : Y} (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c) : Ψ.toFun (p.trans q) = Ψ.toFun p * Ψ.toFun q :=
  Ψ.map_trans' p q

@[simp]
theorem map_refl (a : Y) : Ψ.toFun (Path.Homotopic.Quotient.refl a) = 1 := by
  have h := Ψ.map_trans (.refl a) (.refl a)
  rw [Path.Homotopic.Quotient.trans_refl] at h
  simpa using h

theorem map_symm {a b : Y} (p : Path.Homotopic.Quotient a b) :
    Ψ.toFun p.symm = (Ψ.toFun p)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← map_trans, Path.Homotopic.Quotient.symm_trans, map_refl]

theorem map_cast {a b a' b' : Y} (p : Path.Homotopic.Quotient a b) (ha : a' = a) (hb : b' = b) :
    Ψ.toFun (p.cast ha hb) = Ψ.toFun p := by
  subst ha hb
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]

theorem _root_.Path.Homotopic.Quotient.map_trans' {a b c : Y'}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c) (f : C(Y', Y)) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  induction q using Path.Homotopic.Quotient.ind with | mk q =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_trans q f.continuous)

theorem _root_.Path.Homotopic.Quotient.map_symm' {a b : Y'} (p : Path.Homotopic.Quotient a b)
    (f : C(Y', Y)) : p.symm.map f = (p.map f).symm := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_symm f.continuous)

/-- The pull-back of `Ψ` along a continuous map `f`. -/
def comap (f : C(Y', Y)) : PathClassHom Y' K where
  toFun p := Ψ.toFun (p.map f)
  map_trans' p q := by rw [Path.Homotopic.Quotient.map_trans', map_trans]

@[simp]
theorem comap_toFun (f : C(Y', Y)) {a b : Y'} (p : Path.Homotopic.Quotient a b) :
    (Ψ.comap f).toFun p = Ψ.toFun (p.map f) :=
  rfl

section val

variable {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z'] [SimplyConnectedSpace Z]
  [SimplyConnectedSpace Z']

/-- On a simply connected space `Z`, the value of `Ψ : PathClassHom Z K` on any path from `z` to
`z'`; it does not depend on the path (`VanKampen.PathClassHom.val_eq`). -/
noncomputable def val (Ψ : PathClassHom Z K) (z z' : Z) : K :=
  Ψ.toFun (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath z z'))

theorem val_eq (Ψ : PathClassHom Z K) {z z' : Z} (p : Path.Homotopic.Quotient z z') :
    Ψ.val z z' = Ψ.toFun p := by
  rw [val, Subsingleton.elim (Path.Homotopic.Quotient.mk _) p]

theorem val_eq_path (Ψ : PathClassHom Z K) {z z' : Z} (p : Path z z') :
    Ψ.val z z' = Ψ.toFun (Path.Homotopic.Quotient.mk p) :=
  val_eq Ψ _

@[simp]
theorem val_mul_val (Ψ : PathClassHom Z K) (z z' z'' : Z) :
    Ψ.val z z' * Ψ.val z' z'' = Ψ.val z z'' := by
  rw [val, val, ← map_trans, val_eq]

@[simp]
theorem val_self (Ψ : PathClassHom Z K) (z : Z) : Ψ.val z z = 1 := by
  rw [val_eq Ψ (.refl z), map_refl]

theorem val_symm (Ψ : PathClassHom Z K) (z z' : Z) : Ψ.val z' z = (Ψ.val z z')⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, val_mul_val, val_self]

/-- Naturality of `VanKampen.PathClassHom.val` in the simply connected parameter space. -/
theorem val_comap_comp (f : C(Z, Y)) (φ : C(Z', Z)) (z z' : Z') :
    (Ψ.comap (f.comp φ)).val z z' = (Ψ.comap f).val (φ z) (φ z') := by
  rw [val, comap_toFun, Path.Homotopic.Quotient.map_comp]
  exact (val_eq (Ψ.comap f) _).symm

/-- The value of the pull-back along a path `γ` between the endpoints of `I` is the value on `γ`. -/
theorem val_comap_path {a b : Y} (γ : Path a b) :
    (Ψ.comap γ.toContinuousMap).val 0 1 = Ψ.toFun (Path.Homotopic.Quotient.mk γ) := by
  let e : Path (0 : I) 1 := ⟨ContinuousMap.id I, rfl, rfl⟩
  rw [val_eq_path _ e, comap_toFun, ← Path.Homotopic.Quotient.mk_map]
  have : e.map γ.toContinuousMap.continuous = γ.cast γ.source γ.target := by
    ext
    rfl
  rw [this, Path.Homotopic.Quotient.mk_cast, map_cast]

/-- A telescoping product of values. -/
theorem prod_val (Ψ : PathClassHom Z K) (c : ℕ → Z) (n : ℕ) :
    ((List.range n).map fun k => Ψ.val (c k) (c (k + 1))).prod = Ψ.val (c 0) (c n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, ih, val_mul_val]

end val

end PathClassHom

/-- A point of `Set.uIcc a b` in `I` is at most as far from `a` as `b` is. -/
theorem dist_le_of_mem_uIcc {a b t : I} (ht : t ∈ uIcc a b) : dist t a ≤ dist b a := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  apply abs_sub_left_of_mem_uIcc
  rcases mem_uIcc.1 ht with h | h
  · exact mem_uIcc.2 (Or.inl ⟨h.1, h.2⟩)
  · exact mem_uIcc.2 (Or.inr ⟨h.1, h.2⟩)

end VanKampen

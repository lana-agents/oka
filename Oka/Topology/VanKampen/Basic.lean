/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Topology.VanKampen.Cover
import Mathlib.GroupTheory.PushoutI

/-!
# The Seifert–van Kampen theorem

Let `X` be a topological space, `U` and `V` open subsets with `U ∪ V = univ`, and `x₀ ∈ U ∩ V`,
such that `U`, `V` and `U ∩ V` are path connected (this is `VanKampen.Hypotheses U V x₀`). We
index `U` and `V` by `Bool` (`VanKampen.piece U V true = U`, `VanKampen.piece U V false = V`)
and write `VanKampen.interMap U V _ b : π₁(U ∩ V, x₀) →* π₁(piece b, x₀)` and
`VanKampen.pieceMap U V _ b : π₁(piece b, x₀) →* π₁(X, x₀)` for the maps induced by the
inclusions.

## Main results

- `VanKampen.lift`, `VanKampen.lift_comp_pieceMap`, `VanKampen.eq_lift`,
  `VanKampen.existsUnique_lift`: the **universal property**: for every group `K` and
  homomorphisms `f b : π₁(piece b, x₀) →* K` which agree on `π₁(U ∩ V, x₀)`, there is a unique
  `Φ : π₁(X, x₀) →* K` with `Φ ∘ pieceMap b = f b` for both `b`.
- `VanKampen.hom_ext`: homomorphisms out of `π₁(X, x₀)` are determined on the images of
  `π₁(U, x₀)` and `π₁(V, x₀)`.
- `VanKampen.pushoutEquiv`: the **Seifert–van Kampen theorem**: the canonical map
  `VanKampen.pushoutMap` from the amalgamated free product
  `Monoid.PushoutI (VanKampen.interMap U V _)` of `π₁(U, x₀)` and `π₁(V, x₀)` over
  `π₁(U ∩ V, x₀)` to `π₁(X, x₀)` is an isomorphism (`VanKampen.pushoutMap_bijective`).
- `VanKampen.coprodEquiv`: if moreover `U ∩ V` is simply connected, `π₁(X, x₀)` is the free
  product `Monoid.CoprodI` of `π₁(U, x₀)` and `π₁(V, x₀)`.

## Proof

Choose for every `y` a path `basePath y` from `x₀` to `y`, inside `U ∩ V` if `y ∈ U ∩ V`, else
inside `U` if `y ∈ U`, else inside `V`, and the constant path for `y = x₀`. Given `f`, a path
class `p` from `a` to `b` in `piece b` gets the value `f b [basePath a · p · (basePath b)⁻¹]`;
these form a `VanKampen.CoverData` (they agree on paths in `U ∩ V` because the base paths of
points of `U ∩ V` lie in `U ∩ V`), and `VanKampen.CoverData.glue` glues them to a function on
path classes in `X`, which restricts to the desired `Φ` on loops at `x₀`. Uniqueness is
`VanKampen.CoverData.eq_glue`. The values live in `Kᵐᵒᵖ` because Mathlib's multiplication on
`FundamentalGroup` is `p * q = q.trans p`.

The isomorphism with the pushout follows from the universal properties of both sides.

## References

* [A. Hatcher, *Algebraic Topology*, Theorem 1.20][hatcher02]
-/

open Set unitInterval

namespace VanKampen

variable {X : Type*}

/-- The two members `U` (for `true`) and `V` (for `false`) of the cover. -/
def piece (U V : Set X) (b : Bool) : Set X :=
  cond b U V

@[simp]
theorem piece_true (U V : Set X) : piece U V true = U :=
  rfl

@[simp]
theorem piece_false (U V : Set X) : piece U V false = V :=
  rfl

theorem inter_subset_piece (U V : Set X) (b : Bool) : U ∩ V ⊆ piece U V b := by
  cases b
  exacts [inter_subset_right, inter_subset_left]

theorem mem_piece_of_mem_inter {U V : Set X} {x : X} (hx : x ∈ U ∩ V) (b : Bool) :
    x ∈ piece U V b :=
  inter_subset_piece U V b hx

theorem inter_piece_subset {U V : Set X} {i j : Bool} (hij : i ≠ j) :
    piece U V i ∩ piece U V j ⊆ U ∩ V := by
  cases i <;> cases j
  · exact absurd rfl hij
  · exact fun y hy => ⟨hy.2, hy.1⟩
  · exact fun y hy => hy
  · exact absurd rfl hij

variable [TopologicalSpace X]

/-- The hypotheses of the Seifert–van Kampen theorem for the cover of `X` by `U` and `V`, with
base point `x₀`. -/
structure Hypotheses (U V : Set X) (x₀ : X) : Prop where
  isOpen_left : IsOpen U
  isOpen_right : IsOpen V
  union_eq : U ∪ V = univ
  mem_inter : x₀ ∈ U ∩ V
  isPathConnected_left : IsPathConnected U
  isPathConnected_right : IsPathConnected V
  isPathConnected_inter : IsPathConnected (U ∩ V)

/-- The map `π₁(U ∩ V, x₀) →* π₁(piece U V b, x₀)` induced by the inclusion. -/
noncomputable def interMap (U V : Set X) {x₀ : X} (hx₀ : x₀ ∈ U ∩ V) (b : Bool) :
    FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩ →*
      FundamentalGroup (piece U V b) ⟨x₀, mem_piece_of_mem_inter hx₀ b⟩ :=
  FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_piece U V b)) ⟨x₀, hx₀⟩

/-- The map `π₁(piece U V b, x₀) →* π₁(X, x₀)` induced by the inclusion. -/
noncomputable def pieceMap (U V : Set X) {x₀ : X} (hx₀ : x₀ ∈ U ∩ V) (b : Bool) :
    FundamentalGroup (piece U V b) ⟨x₀, mem_piece_of_mem_inter hx₀ b⟩ →*
      FundamentalGroup X x₀ :=
  FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ ⟨x₀, mem_piece_of_mem_inter hx₀ b⟩

theorem pieceMap_comp_interMap (U V : Set X) {x₀ : X} (hx₀ : x₀ ∈ U ∩ V) (b : Bool) :
    (pieceMap U V hx₀ b).comp (interMap U V hx₀ b) =
      FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ ⟨x₀, hx₀⟩ := by
  ext p
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  rfl

namespace Hypotheses

variable {U V : Set X} {x₀ : X} (h : Hypotheses U V x₀)
include h

theorem mem_or_mem (y : X) : y ∈ U ∨ y ∈ V := by
  have := h.union_eq ▸ mem_univ y
  exact this

theorem isOpen_piece (b : Bool) : IsOpen (piece U V b) := by
  cases b
  exacts [h.isOpen_right, h.isOpen_left]

open scoped Classical in
/-- The chosen path from `x₀` to `y`: constant if `y = x₀`, inside `U ∩ V` if `y ∈ U ∩ V`,
else inside `U` if `y ∈ U`, else inside `V`. -/
noncomputable def basePath (y : X) : Path x₀ y :=
  if hy : y = x₀ then (Path.refl x₀).cast rfl hy
  else if hy : y ∈ U ∩ V then (h.isPathConnected_inter.joinedIn x₀ h.mem_inter y hy).somePath
  else if hy : y ∈ U then (h.isPathConnected_left.joinedIn x₀ h.mem_inter.1 y hy).somePath
  else (h.isPathConnected_right.joinedIn x₀ h.mem_inter.2 y
    ((h.mem_or_mem y).resolve_left hy)).somePath

theorem basePath_self : h.basePath x₀ = Path.refl x₀ := by
  rw [basePath, dif_pos rfl]
  rfl

theorem basePath_mem_inter {y : X} (hy : y ∈ U ∩ V) (t : I) : h.basePath y t ∈ U ∩ V := by
  rw [basePath]
  split_ifs with h₀
  · subst h₀
    exact h.mem_inter
  · exact JoinedIn.somePath_mem _ t

theorem basePath_mem_piece (b : Bool) {y : X} (hy : y ∈ piece U V b) (t : I) :
    h.basePath y t ∈ piece U V b := by
  by_cases hyi : y ∈ U ∩ V
  · exact inter_subset_piece U V b (h.basePath_mem_inter hyi t)
  have h₀ : y ≠ x₀ := fun h₀ => hyi (h₀ ▸ h.mem_inter)
  by_cases hyU : y ∈ U
  · obtain rfl : b = true := by
      cases b
      · exact absurd ⟨hyU, hy⟩ hyi
      · rfl
    rw [basePath, dif_neg h₀, dif_neg hyi, dif_pos hyU]
    exact (JoinedIn.somePath_mem _ t : _ ∈ U)
  · obtain rfl : b = false := by
      cases b
      · rfl
      · exact absurd hy hyU
    rw [basePath, dif_neg h₀, dif_neg hyi, dif_neg hyU]
    exact (JoinedIn.somePath_mem _ t : _ ∈ V)

/-- The chosen path from `x₀` to `y`, as a path in a subset `S` containing the chosen paths of
its points. -/
noncomputable def basePathIn (S : Set X) (hS : ∀ y ∈ S, ∀ t, h.basePath y t ∈ S) (hx : x₀ ∈ S)
    (y : S) :
    Path (⟨x₀, hx⟩ : S) y where
  toFun t := ⟨h.basePath y t, hS y y.2 t⟩
  continuous_toFun := (h.basePath y).continuous.subtype_mk _
  source' := Subtype.ext (h.basePath y).source
  target' := Subtype.ext (h.basePath y).target

/-- The loop at `x₀` obtained by conjugating a path class `p` with the chosen paths. -/
noncomputable def loop {a b : X} (p : Path.Homotopic.Quotient a b) : FundamentalGroup X x₀ :=
  (Path.Homotopic.Quotient.mk (h.basePath a)).trans
    (p.trans (Path.Homotopic.Quotient.mk (h.basePath b)).symm)

/-- The loop at `x₀` in a subset `S` obtained by conjugating a path class `p` with the chosen
paths. -/
noncomputable def loopIn (S : Set X) (hS : ∀ y ∈ S, ∀ t, h.basePath y t ∈ S) (hx : x₀ ∈ S) {a b : S}
    (p : Path.Homotopic.Quotient a b) : FundamentalGroup S ⟨x₀, hx⟩ :=
  (Path.Homotopic.Quotient.mk (h.basePathIn S hS hx a)).trans
    (p.trans (Path.Homotopic.Quotient.mk (h.basePathIn S hS hx b)).symm)

omit h in
theorem conj_trans {Y : Type*} [TopologicalSpace Y] {y a b c : Y}
    (da : Path.Homotopic.Quotient y a) (db : Path.Homotopic.Quotient y b)
    (dc : Path.Homotopic.Quotient y c) (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c) :
    da.trans ((p.trans q).trans dc.symm) =
      (da.trans (p.trans db.symm)).trans (db.trans (q.trans dc.symm)) := by
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc db.symm db, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem loop_trans {a b c : X} (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c) : h.loop (p.trans q) = h.loop q * h.loop p :=
  conj_trans _ _ _ p q

theorem loopIn_trans (S : Set X) (hS : ∀ y ∈ S, ∀ t, h.basePath y t ∈ S) (hx : x₀ ∈ S)
    {a b c : S} (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c) :
    h.loopIn S hS hx (p.trans q) = h.loopIn S hS hx q * h.loopIn S hS hx p :=
  conj_trans _ _ _ p q

theorem loop_self (p : FundamentalGroup X x₀) : h.loop p = p := by
  change (Path.Homotopic.Quotient.mk (h.basePath x₀)).trans
    ((p : Path.Homotopic.Quotient x₀ x₀).trans
      (Path.Homotopic.Quotient.mk (h.basePath x₀)).symm) = p
  rw [h.basePath_self, Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans,
    ← Path.Homotopic.Quotient.mk_refl, ← Path.Homotopic.Quotient.mk_symm, Path.refl_symm,
    Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl]

theorem basePathIn_self (S : Set X) (hS : ∀ y ∈ S, ∀ t, h.basePath y t ∈ S) (hx : x₀ ∈ S) :
    h.basePathIn S hS hx ⟨x₀, hx⟩ = Path.refl _ := by
  ext t
  simp [basePathIn, h.basePath_self]

theorem loopIn_self (S : Set X) (hS : ∀ y ∈ S, ∀ t, h.basePath y t ∈ S) (hx : x₀ ∈ S)
    (p : FundamentalGroup S ⟨x₀, hx⟩) : h.loopIn S hS hx p = p := by
  change (Path.Homotopic.Quotient.mk (h.basePathIn S hS hx ⟨x₀, hx⟩)).trans
    ((p : Path.Homotopic.Quotient _ _).trans
      (Path.Homotopic.Quotient.mk (h.basePathIn S hS hx ⟨x₀, hx⟩)).symm) = p
  rw [h.basePathIn_self, Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans,
    ← Path.Homotopic.Quotient.mk_refl, ← Path.Homotopic.Quotient.mk_symm, Path.refl_symm,
    Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl]

theorem loopIn_map_val (S : Set X) (hS : ∀ y ∈ S, ∀ t, h.basePath y t ∈ S) (hx : x₀ ∈ S)
    {a b : S} (p : Path.Homotopic.Quotient a b) :
    FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ ⟨x₀, hx⟩ (h.loopIn S hS hx p) =
      h.loop (p.map ⟨Subtype.val, continuous_subtype_val⟩) := by
  change Path.Homotopic.Quotient.map ((Path.Homotopic.Quotient.mk _).trans
    (p.trans (Path.Homotopic.Quotient.mk _).symm)) _ = _
  rw [Path.Homotopic.Quotient.map_trans', Path.Homotopic.Quotient.map_trans',
    Path.Homotopic.Quotient.map_symm']
  rfl

theorem loopIn_map_inclusion (S T : Set X) (hST : S ⊆ T)
    (hS : ∀ y ∈ S, ∀ t, h.basePath y t ∈ S) (hT : ∀ y ∈ T, ∀ t, h.basePath y t ∈ T)
    (hx : x₀ ∈ S) {a b : S} (p : Path.Homotopic.Quotient a b) :
    FundamentalGroup.map (ContinuousMap.inclusion hST) ⟨x₀, hx⟩ (h.loopIn S hS hx p) =
      h.loopIn T hT (hST hx) (p.map (ContinuousMap.inclusion hST)) := by
  change Path.Homotopic.Quotient.map ((Path.Homotopic.Quotient.mk _).trans
    (p.trans (Path.Homotopic.Quotient.mk _).symm)) _ = _
  rw [Path.Homotopic.Quotient.map_trans', Path.Homotopic.Quotient.map_trans',
    Path.Homotopic.Quotient.map_symm']
  rfl

theorem basePath_mem_piece_inter (i j : Bool) (y : X) (hy : y ∈ piece U V i ∩ piece U V j)
    (t : I) : h.basePath y t ∈ piece U V i ∩ piece U V j :=
  ⟨h.basePath_mem_piece i hy.1 t, h.basePath_mem_piece j hy.2 t⟩

variable {K : Type*} [Group K]
  (f : ∀ b, FundamentalGroup (piece U V b) ⟨x₀, mem_piece_of_mem_inter h.mem_inter b⟩ →* K)

/-- The value of `f b` on the conjugated loop of a path class in `piece U V b`, in `Kᵐᵒᵖ`. -/
noncomputable def pieceHom (b : Bool) : PathClassHom (piece U V b) Kᵐᵒᵖ where
  toFun p := MulOpposite.op (f b (h.loopIn (piece U V b) (fun _ hy => h.basePath_mem_piece b hy)
    (inter_subset_piece U V b h.mem_inter) p))
  map_trans' p q := by
    rw [loopIn_trans, map_mul, MulOpposite.op_mul]

theorem pieceHom_toFun (b : Bool) {a c : piece U V b} (p : Path.Homotopic.Quotient a c) :
    (h.pieceHom f b).toFun p = MulOpposite.op (f b (h.loopIn (piece U V b)
      (fun _ hy => h.basePath_mem_piece b hy) (inter_subset_piece U V b h.mem_inter) p)) :=
  rfl

variable {f} in
theorem compat (hf : (f true).comp (interMap U V h.mem_inter true) =
      (f false).comp (interMap U V h.mem_inter false))
    (i j : Bool) {a b : ↥(piece U V i ∩ piece U V j)} (p : Path.Homotopic.Quotient a b) :
    (h.pieceHom f i).toFun (p.map (ContinuousMap.inclusion inter_subset_left)) =
      (h.pieceHom f j).toFun (p.map (ContinuousMap.inclusion inter_subset_right)) := by
  by_cases hij : i = j
  · subst hij
    rfl
  have hS := h.basePath_mem_piece_inter i j
  have hx : x₀ ∈ piece U V i ∩ piece U V j :=
    ⟨inter_subset_piece U V i h.mem_inter, inter_subset_piece U V j h.mem_inter⟩
  have hf' : ∀ k, (f k).comp (interMap U V h.mem_inter k) =
      (f true).comp (interMap U V h.mem_inter true) := by
    intro k
    cases k
    · exact hf.symm
    · rfl
  rw [pieceHom_toFun, pieceHom_toFun,
    ← h.loopIn_map_inclusion _ _ inter_subset_left hS _ hx,
    ← h.loopIn_map_inclusion _ _ inter_subset_right hS _ hx]
  congr 1
  set ℓ := h.loopIn _ hS hx p
  have key : ∀ k (hk : piece U V i ∩ piece U V j ⊆ piece U V k),
      f k (FundamentalGroup.map (ContinuousMap.inclusion hk) ⟨x₀, hx⟩ ℓ) =
        (f true).comp (interMap U V h.mem_inter true)
          (FundamentalGroup.map (ContinuousMap.inclusion (inter_piece_subset hij))
            ⟨x₀, hx⟩ ℓ) := by
    intro k hk
    rw [← hf' k]
    induction ℓ using Path.Homotopic.Quotient.ind with | mk ℓ =>
    rfl
  rw [key i inter_subset_left, key j inter_subset_right]

variable {f} in
/-- The local data of the gluing construction: the cover of `X` by `U` and `V` with the
functions `VanKampen.Hypotheses.pieceHom`. -/
noncomputable def coverData (hf : (f true).comp (interMap U V h.mem_inter true) =
      (f false).comp (interMap U V h.mem_inter false)) : CoverData X Bool Kᵐᵒᵖ where
  W := piece U V
  isOpen := h.isOpen_piece
  exists_mem x := by
    rcases h.mem_or_mem x with hx | hx
    exacts [⟨true, hx⟩, ⟨false, hx⟩]
  Ψ := h.pieceHom f
  compat := h.compat hf

end Hypotheses

section main

variable {U V : Set X} {x₀ : X} (h : Hypotheses U V x₀) {K : Type*} [Group K]
  (f : ∀ b, FundamentalGroup (piece U V b) ⟨x₀, mem_piece_of_mem_inter h.mem_inter b⟩ →* K)
  (hf : (f true).comp (interMap U V h.mem_inter true) =
    (f false).comp (interMap U V h.mem_inter false))

/-- The homomorphism `π₁(X, x₀) →* K` determined by homomorphisms `f b : π₁(piece U V b) →* K`
agreeing on `π₁(U ∩ V)` (universal property of the Seifert–van Kampen theorem). -/
noncomputable def lift : FundamentalGroup X x₀ →* K :=
  MonoidHom.mk' (fun γ => MulOpposite.unop ((h.coverData hf).glue.toFun
      (FundamentalGroup.toPath γ))) fun γ γ' => by
    change MulOpposite.unop ((h.coverData hf).glue.toFun (Path.Homotopic.Quotient.trans
      (FundamentalGroup.toPath γ') (FundamentalGroup.toPath γ))) = _
    rw [PathClassHom.map_trans, MulOpposite.unop_mul]

theorem lift_apply (γ : FundamentalGroup X x₀) :
    lift h f hf γ = MulOpposite.unop ((h.coverData hf).glue.toFun
      (FundamentalGroup.toPath γ)) :=
  rfl

@[simp]
theorem lift_pieceMap (b : Bool) (γ : FundamentalGroup (piece U V b) _) :
    lift h f hf (pieceMap U V h.mem_inter b γ) = f b γ := by
  rw [lift_apply]
  refine (congrArg MulOpposite.unop
    ((h.coverData hf).glue_map_val b (FundamentalGroup.toPath γ))).trans ?_
  change MulOpposite.unop (MulOpposite.op (f b (h.loopIn _ _ _ γ))) = _
  rw [h.loopIn_self, MulOpposite.unop_op]

theorem lift_comp_pieceMap (b : Bool) :
    (lift h f hf).comp (pieceMap U V h.mem_inter b) = f b :=
  MonoidHom.ext (lift_pieceMap h f hf b)

/-- Uniqueness in the universal property. -/
theorem eq_lift (Φ : FundamentalGroup X x₀ →* K)
    (hΦ : ∀ b, Φ.comp (pieceMap U V h.mem_inter b) = f b) : Φ = lift h f hf := by
  let Θ : PathClassHom X Kᵐᵒᵖ :=
    { toFun := fun p => MulOpposite.op (Φ (h.loop p))
      map_trans' := fun p q => by rw [h.loop_trans, map_mul, MulOpposite.op_mul] }
  ext γ
  have := (h.coverData hf).eq_glue Θ (fun b a c p => ?_) (FundamentalGroup.toPath γ)
  · rw [lift_apply, ← this]
    change Φ γ = MulOpposite.unop (MulOpposite.op (Φ (h.loop γ)))
    rw [h.loop_self, MulOpposite.unop_op]
  · change MulOpposite.op (Φ (h.loop _)) = MulOpposite.op (f b (h.loopIn _ _ _ p))
    rw [← hΦ b, MonoidHom.comp_apply]
    congr 2
    exact (h.loopIn_map_val _ _ _ p).symm

include hf in
/-- The universal property of `π₁(X, x₀)` (Seifert–van Kampen). -/
theorem existsUnique_lift :
    ∃! Φ : FundamentalGroup X x₀ →* K, ∀ b, Φ.comp (pieceMap U V h.mem_inter b) = f b :=
  ⟨lift h f hf, lift_comp_pieceMap h f hf, fun Φ hΦ => eq_lift h f hf Φ hΦ⟩

end main

section ext

variable {U V : Set X} {x₀ : X} (h : Hypotheses U V x₀) {K : Type*} [Group K]

/-- Homomorphisms out of `π₁(X, x₀)` agreeing on the images of `π₁(U, x₀)` and `π₁(V, x₀)` are
equal. -/
theorem hom_ext {Φ Ψ : FundamentalGroup X x₀ →* K}
    (hΦΨ : ∀ b, Φ.comp (pieceMap U V h.mem_inter b) = Ψ.comp (pieceMap U V h.mem_inter b)) :
    Φ = Ψ := by
  let f := fun b => Ψ.comp (pieceMap U V h.mem_inter b)
  have hf : (f true).comp (interMap U V h.mem_inter true) =
      (f false).comp (interMap U V h.mem_inter false) := by
    simp only [f, MonoidHom.comp_assoc, pieceMap_comp_interMap]
  rw [eq_lift h f hf Φ hΦΨ, eq_lift h f hf Ψ fun _ => rfl]

end ext

section pushout

variable {U V : Set X} {x₀ : X} (h : Hypotheses U V x₀)

/-- The canonical map from the amalgamated free product of `π₁(U, x₀)` and `π₁(V, x₀)` over
`π₁(U ∩ V, x₀)` to `π₁(X, x₀)`. -/
noncomputable def pushoutMap :
    Monoid.PushoutI (interMap U V h.mem_inter) →* FundamentalGroup X x₀ :=
  Monoid.PushoutI.lift (pieceMap U V h.mem_inter) _ (pieceMap_comp_interMap U V h.mem_inter)

@[simp]
theorem pushoutMap_of (b : Bool) (γ : FundamentalGroup (piece U V b) _) :
    pushoutMap h (Monoid.PushoutI.of b γ) = pieceMap U V h.mem_inter b γ := by
  rw [pushoutMap, Monoid.PushoutI.lift_of]

/-- The inverse of `VanKampen.pushoutMap`. -/
noncomputable def pushoutInv :
    FundamentalGroup X x₀ →* Monoid.PushoutI (interMap U V h.mem_inter) :=
  lift h (fun b => Monoid.PushoutI.of (φ := interMap U V h.mem_inter) b) (by
    rw [Monoid.PushoutI.of_comp_eq_base, Monoid.PushoutI.of_comp_eq_base])

/-- The **Seifert–van Kampen theorem**: `π₁(X, x₀)` is the amalgamated free product of
`π₁(U, x₀)` and `π₁(V, x₀)` over `π₁(U ∩ V, x₀)`. -/
noncomputable def pushoutEquiv :
    Monoid.PushoutI (interMap U V h.mem_inter) ≃* FundamentalGroup X x₀ :=
  MonoidHom.toMulEquiv (pushoutMap h) (pushoutInv h)
    (Monoid.PushoutI.hom_ext_nonempty fun b => by
      ext γ
      simp [pushoutInv])
    (hom_ext h fun b => by
      ext γ
      simp [pushoutInv])

@[simp]
theorem pushoutEquiv_apply (x : Monoid.PushoutI (interMap U V h.mem_inter)) :
    pushoutEquiv h x = pushoutMap h x :=
  rfl

theorem pushoutMap_bijective : Function.Bijective (pushoutMap h) :=
  (pushoutEquiv h).bijective

/-- The inverse of `VanKampen.coprodEquiv`. -/
noncomputable def coprodInv (hUV : IsSimplyConnected (U ∩ V)) :
    FundamentalGroup X x₀ →* Monoid.CoprodI (fun b => FundamentalGroup (piece U V b)
      ⟨x₀, mem_piece_of_mem_inter h.mem_inter b⟩) :=
  lift h (fun b => Monoid.CoprodI.of (M := fun b => FundamentalGroup (piece U V b)
      ⟨x₀, mem_piece_of_mem_inter h.mem_inter b⟩) (i := b)) (by
    haveI := hUV.simplyConnectedSpace
    exact MonoidHom.ext fun γ => by rw [Subsingleton.elim γ 1, map_one, map_one])

/-- If moreover `U ∩ V` is simply connected, `π₁(X, x₀)` is the free product of `π₁(U, x₀)` and
`π₁(V, x₀)`. -/
noncomputable def coprodEquiv (hUV : IsSimplyConnected (U ∩ V)) :
    Monoid.CoprodI (fun b => FundamentalGroup (piece U V b)
      ⟨x₀, mem_piece_of_mem_inter h.mem_inter b⟩) ≃* FundamentalGroup X x₀ :=
  MonoidHom.toMulEquiv (Monoid.CoprodI.lift (pieceMap U V h.mem_inter)) (coprodInv h hUV)
    (Monoid.CoprodI.ext_hom _ _ fun b => by
      ext γ
      simp [coprodInv])
    (hom_ext h fun b => by
      ext γ
      simp [coprodInv])

@[simp]
theorem coprodEquiv_apply (hUV : IsSimplyConnected (U ∩ V))
    (x : Monoid.CoprodI (fun b => FundamentalGroup (piece U V b)
      ⟨x₀, mem_piece_of_mem_inter h.mem_inter b⟩)) :
    coprodEquiv h hUV x = Monoid.CoprodI.lift (pieceMap U V h.mem_inter) x :=
  rfl

end pushout

end VanKampen

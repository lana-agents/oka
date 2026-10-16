/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Topology.VanKampen.PathClassHom
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Homotopy.Path
import Mathlib.Tactic.Group

/-!
# Gluing group-valued path functions along an open cover

Let `X` be a topological space with an open cover `W : ι → Set X`, and suppose given for every
`i` a `VanKampen.PathClassHom (W i) K`, i.e. a multiplicative function `Ψ i` on homotopy classes
of paths in `W i` with values in a group `K`, such that `Ψ i` and `Ψ j` agree on paths in
`W i ∩ W j`. This is a `VanKampen.CoverData X ι K`. We show that the `Ψ i` glue to a function
`VanKampen.CoverData.pathVal` on paths in `X` which

* is invariant under homotopy rel endpoints (`VanKampen.CoverData.pathVal_eq_of_homotopic`),
* turns concatenation into multiplication (`VanKampen.CoverData.pathVal_trans`), and
* is computed by any `VanKampen.PathClassHom` on another space which is compatible with the
  `Ψ i` (`VanKampen.CoverData.pathVal_eq_of_forall`); in particular it extends each `Ψ i`
  (`VanKampen.CoverData.pathVal_of_mem`).

This is the heart of the Seifert–van Kampen theorem (`Oka/Topology/VanKampen/Basic.lean`).

## Construction

For a path `γ : C(I, X)` and `n` so large that every segment `[k/n, (k+1)/n]` is mapped by `γ`
into some `W i` (Lebesgue number lemma), `VanKampen.CoverData.pathValN γ n` is the ordered
product over `k` of the value of `Ψ i` on the segment of `γ`. A segment is parametrised by the
simply connected space `Set.uIcc a b`, so its value is a `VanKampen.PathClassHom.val`, and all
relations between segment values (refinement, and the square relation for a small rectangle of
a homotopy, parametrised by a product of two intervals) follow from
`VanKampen.PathClassHom.val_mul_val`. Independence of `n` follows by comparing `n` and `m` with
`n * m`, homotopy invariance by telescoping along the rows of a fine grid in `I × I`.
-/

open Set unitInterval

namespace VanKampen

/-- The data for gluing: an open cover `W` of `X` and for each `i` a `K`-valued multiplicative
function on homotopy classes of paths in `W i`, such that the functions for `i` and `j` agree on
paths in `W i ∩ W j`. -/
structure CoverData (X : Type*) [TopologicalSpace X] (ι : Type*) (K : Type*) [Group K] where
  /-- The members of the cover. -/
  W : ι → Set X
  isOpen : ∀ i, IsOpen (W i)
  exists_mem : ∀ x, ∃ i, x ∈ W i
  /-- The function on paths in `W i`. -/
  Ψ : ∀ i, PathClassHom (W i) K
  compat : ∀ i j {a b : ↥(W i ∩ W j)} (p : Path.Homotopic.Quotient a b),
    (Ψ i).toFun (p.map (ContinuousMap.inclusion inter_subset_left)) =
      (Ψ j).toFun (p.map (ContinuousMap.inclusion inter_subset_right))

namespace CoverData

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {K : Type*} [Group K]
  (D : CoverData X ι K)

section localVal

variable {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z'] [SimplyConnectedSpace Z]
  [SimplyConnectedSpace Z']

theorem val_comap_inclusion (i j : ι) (g : C(Z, ↥(D.W i ∩ D.W j))) (z z' : Z) :
    ((D.Ψ i).comap ((ContinuousMap.inclusion inter_subset_left).comp g)).val z z' =
      ((D.Ψ j).comap ((ContinuousMap.inclusion inter_subset_right).comp g)).val z z' := by
  rw [PathClassHom.val, PathClassHom.val, PathClassHom.comap_toFun,
    PathClassHom.comap_toFun, Path.Homotopic.Quotient.map_comp,
    Path.Homotopic.Quotient.map_comp]
  exact D.compat i j _

theorem val_codRestrict_eq (i j : ι) (g : C(Z, X)) (hi : ∀ z, g z ∈ D.W i)
    (hj : ∀ z, g z ∈ D.W j) (z z' : Z) :
    ((D.Ψ i).comap (codRestrict g _ hi)).val z z' =
      ((D.Ψ j).comap (codRestrict g _ hj)).val z z' :=
  D.val_comap_inclusion i j (codRestrict g _ fun z => ⟨hi z, hj z⟩) z z'

open scoped Classical in
/-- The value of the glued function on the image of a path between `z` and `z'` in a simply
connected space `Z` under a map `g : C(Z, X)`, provided `g` lands in a member of the cover (and
`1` otherwise). -/
noncomputable def localVal (g : C(Z, X)) (z z' : Z) : K :=
  if h : ∃ i, ∀ z, g z ∈ D.W i then
    ((D.Ψ h.choose).comap (codRestrict g _ h.choose_spec)).val z z'
  else 1

theorem localVal_eq (i : ι) (g : C(Z, X)) (hi : ∀ z, g z ∈ D.W i) (z z' : Z) :
    D.localVal g z z' = ((D.Ψ i).comap (codRestrict g _ hi)).val z z' := by
  have h : ∃ i, ∀ z, g z ∈ D.W i := ⟨i, hi⟩
  rw [localVal, dif_pos h]
  exact D.val_codRestrict_eq _ _ g _ _ z z'

theorem localVal_comp (g : C(Z, X)) (φ : C(Z', Z)) (hg : ∃ i, ∀ z, g z ∈ D.W i) (z z' : Z') :
    D.localVal (g.comp φ) z z' = D.localVal g (φ z) (φ z') := by
  obtain ⟨i, hi⟩ := hg
  rw [D.localVal_eq i _ (fun z => hi (φ z)), D.localVal_eq i g hi,
    ← PathClassHom.val_comap_comp]
  rfl

@[simp]
theorem localVal_self (g : C(Z, X)) (z : Z) : D.localVal g z z = 1 := by
  rw [localVal]
  split_ifs <;> simp

theorem localVal_mul (g : C(Z, X)) (hg : ∃ i, ∀ z, g z ∈ D.W i) (z z' z'' : Z) :
    D.localVal g z z' * D.localVal g z' z'' = D.localVal g z z'' := by
  obtain ⟨i, hi⟩ := hg
  simp only [D.localVal_eq i g hi, PathClassHom.val_mul_val]

theorem localVal_symm (g : C(Z, X)) (hg : ∃ i, ∀ z, g z ∈ D.W i) (z z' : Z) :
    D.localVal g z' z = (D.localVal g z z')⁻¹ := by
  obtain ⟨i, hi⟩ := hg
  rw [D.localVal_eq i g hi, D.localVal_eq i g hi, PathClassHom.val_symm]

theorem localVal_of_const (g : C(Z, X)) (x : X) (hg : ∀ z, g z = x) (z z' : Z) :
    D.localVal g z z' = 1 := by
  obtain ⟨i, hi⟩ := D.exists_mem x
  have : g = (ContinuousMap.const Unit x).comp (ContinuousMap.const Z ()) := by
    ext z
    simp [hg]
  rw [this, D.localVal_comp _ _ ⟨i, fun _ => hi⟩, localVal_self]

end localVal

section segment

/-- The inclusion of the subinterval `Set.uIcc a b` into `I`. -/
def segIncl (a b : I) : C(uIcc a b, I) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The value of the glued function on the segment of a path `γ` from `γ a` to `γ b`, provided
the segment lies in a member of the cover. -/
noncomputable def segVal (γ : C(I, X)) (a b : I) : K :=
  D.localVal (γ.comp (segIncl a b)) ⟨a, left_mem_uIcc⟩ ⟨b, right_mem_uIcc⟩

/-- The segment of `γ` between `a` and `b` lies in a member of the cover. -/
def Covers (γ : C(I, X)) (a b : I) : Prop :=
  ∃ i, ∀ t ∈ uIcc a b, γ t ∈ D.W i

/-- All segment values inside a segment which lies in `W i` are values of one
`VanKampen.PathClassHom` on a simply connected space. -/
theorem segVal_eq_val (γ : C(I, X)) {A B a b : I} (i : ι) (hi : ∀ t ∈ uIcc A B, γ t ∈ D.W i)
    (ha : a ∈ uIcc A B) (hb : b ∈ uIcc A B) :
    D.segVal γ a b = ((D.Ψ i).comap (codRestrict (γ.comp (segIncl A B)) _
      fun t => hi t.1 t.2)).val ⟨a, ha⟩ ⟨b, hb⟩ := by
  rw [← D.localVal_eq]
  have hsub : uIcc a b ⊆ uIcc A B := uIcc_subset_uIcc ha hb
  have : γ.comp (segIncl a b) = (γ.comp (segIncl A B)).comp (ContinuousMap.inclusion hsub) :=
    rfl
  rw [segVal, this, D.localVal_comp _ _ ⟨i, fun t => hi t.1 t.2⟩]
  rfl

@[simp]
theorem segVal_self (γ : C(I, X)) (a : I) : D.segVal γ a a = 1 := by
  simp [segVal]

theorem segVal_of_const (γ : C(I, X)) (x : X) (hγ : ∀ t, γ t = x) (a b : I) :
    D.segVal γ a b = 1 := by
  rw [segVal]
  exact D.localVal_of_const _ x (fun t => hγ t.1) _ _

/-- Telescoping of segment values inside a segment lying in a member of the cover. -/
theorem prod_segVal (γ : C(I, X)) {A B : I} (i : ι) (hi : ∀ t ∈ uIcc A B, γ t ∈ D.W i)
    (c : ℕ → I) (m : ℕ) (hc : ∀ j ≤ m, c j ∈ uIcc A B) :
    ((List.range m).map fun j => D.segVal γ (c j) (c (j + 1))).prod = D.segVal γ (c 0) (c m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.prod_range_succ, ih (fun j hj => hc j (by omega)),
      D.segVal_eq_val γ i hi (hc 0 (by omega)) (hc m (by omega)),
      D.segVal_eq_val γ i hi (hc m (by omega)) (hc (m + 1) le_rfl),
      D.segVal_eq_val γ i hi (hc 0 (by omega)) (hc (m + 1) le_rfl),
      PathClassHom.val_mul_val]

/-- Reparametrisation of a segment. -/
theorem segVal_eq_of_eqOn (γ γ' : C(I, X)) (φ : C(I, I)) {a b a' b' : I}
    (hφ : ∀ t ∈ uIcc a' b', φ t ∈ uIcc a b) (heq : ∀ t ∈ uIcc a' b', γ' t = γ (φ t))
    (ha : φ a' = a) (hb : φ b' = b) (hcov : D.Covers γ a b) :
    D.segVal γ' a' b' = D.segVal γ a b := by
  let φ' : C(uIcc a' b', uIcc a b) :=
    ⟨fun t => ⟨φ t, hφ t t.2⟩, (φ.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have : γ'.comp (segIncl a' b') = (γ.comp (segIncl a b)).comp φ' := by
    ext t
    exact heq t t.2
  obtain ⟨i, hi⟩ := hcov
  rw [segVal, this, D.localVal_comp _ _ ⟨i, fun t => hi t.1 t.2⟩, segVal]
  congr 1 <;> exact Subtype.ext (by simp [φ', ha, hb])

end segment

section subdivision

/-- The subdivision point `k / n` of the unit interval (truncated to `I`). -/
noncomputable def pt (n k : ℕ) : I :=
  projIcc 0 1 zero_le_one (k / n)

@[simp]
theorem pt_zero (n : ℕ) : pt n 0 = 0 := by
  simp [pt]

theorem pt_self {n : ℕ} (hn : 0 < n) : pt n n = 1 := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [pt, div_self this]

theorem pt_mono (n : ℕ) : Monotone (pt n) := fun k k' h =>
  monotone_projIcc _ (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg n))

theorem pt_mul {n m : ℕ} (hm : 0 < m) (k : ℕ) : pt (n * m) (k * m) = pt n k := by
  simp only [pt, Nat.cast_mul]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [mul_div_mul_right _ _ this]

theorem coe_pt {n k : ℕ} (hk : k ≤ n) : (pt n k : ℝ) = k / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pt]
  rw [pt, projIcc_of_mem]
  exact ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast hk) (Nat.cast_nonneg n)⟩

theorem dist_pt_succ {n k : ℕ} (hk : k < n) : dist (pt n (k + 1)) (pt n k) = 1 / n := by
  rw [Subtype.dist_eq, coe_pt hk, coe_pt hk.le, Real.dist_eq, Nat.cast_succ, ← sub_div,
    add_sub_cancel_left, abs_of_nonneg (by positivity)]

/-- Every segment `[k/n, (k+1)/n]` of `γ` lies in a member of the cover. -/
def Fine (γ : C(I, X)) (n : ℕ) : Prop :=
  ∀ k < n, D.Covers γ (pt n k) (pt n (k + 1))

/-- The ordered product of the segment values of `γ` over the subdivision into `n` pieces. -/
noncomputable def pathValN (γ : C(I, X)) (n : ℕ) : K :=
  ((List.range n).map fun k => D.segVal γ (pt n k) (pt n (k + 1))).prod

theorem exists_fine (γ : C(I, X)) : ∃ N, 0 < N ∧ ∀ n ≥ N, D.Fine γ n := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i => (D.isOpen i).preimage γ.continuous)
    (fun x _ => mem_iUnion.2 (D.exists_mem (γ x)))
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N + 1, N.succ_pos, fun n hn k hk => ?_⟩
  obtain ⟨i, hi⟩ := h (pt n k) (mem_univ _)
  refine ⟨i, fun t ht => hi ?_⟩
  rw [Metric.mem_ball]
  calc dist t (pt n k) ≤ dist (pt n (k + 1)) (pt n k) := dist_le_of_mem_uIcc ht
    _ = 1 / n := dist_pt_succ hk
    _ ≤ 1 / (N + 1) := one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hn)
    _ < δ := hN

theorem _root_.List.prod_range_mul_eq {M : Type*} [Monoid M] (f : ℕ → M) (n m : ℕ) :
    ((List.range (n * m)).map f).prod =
      ((List.range n).map fun k => ((List.range m).map fun j => f (k * m + j)).prod).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, List.prod_append, ih,
      List.prod_range_succ, List.map_map]
    rfl

theorem pathValN_mul {γ : C(I, X)} {n m : ℕ} (hγ : D.Fine γ n) (hm : 0 < m) :
    D.pathValN γ (n * m) = D.pathValN γ n := by
  rw [pathValN, List.prod_range_mul_eq, pathValN]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  rw [List.mem_range] at hk
  obtain ⟨i, hi⟩ := hγ k hk
  have := D.prod_segVal γ i hi (fun j => pt (n * m) (k * m + j)) m
  simp only [← Nat.add_assoc] at this
  rw [this]
  · rw [Nat.add_zero, pt_mul hm, ← Nat.succ_mul, pt_mul hm]
  · intro j hj
    refine Icc_subset_uIcc ⟨?_, ?_⟩
    · rw [← pt_mul (n := n) hm k]
      exact pt_mono _ (show k * m ≤ k * m + j by omega)
    · rw [← pt_mul (n := n) hm (k + 1)]
      exact pt_mono _ (show k * m + j ≤ (k + 1) * m by rw [Nat.add_mul, Nat.one_mul]; omega)

theorem pathValN_eq {γ : C(I, X)} {n m : ℕ} (hn : D.Fine γ n) (hm : D.Fine γ m) (hn0 : 0 < n)
    (hm0 : 0 < m) : D.pathValN γ n = D.pathValN γ m := by
  rw [← D.pathValN_mul hn hm0, ← D.pathValN_mul hm hn0, mul_comm]

/-- The glued value of `γ`: the product of segment values over a sufficiently fine subdivision
(`VanKampen.CoverData.pathVal_eq_pathValN`). -/
noncomputable def pathVal (γ : C(I, X)) : K :=
  D.pathValN γ (D.exists_fine γ).choose

theorem pathVal_eq_pathValN {γ : C(I, X)} {n : ℕ} (hn : D.Fine γ n) (hn0 : 0 < n) :
    D.pathVal γ = D.pathValN γ n :=
  D.pathValN_eq ((D.exists_fine γ).choose_spec.2 _ le_rfl) hn
    (D.exists_fine γ).choose_spec.1 hn0

end subdivision

section comparison

/-- The glued value of a path is computed by any `VanKampen.PathClassHom` `Θ` on a space `Y`
mapping to `X` which is compatible with the `Ψ i` on paths. -/
theorem pathVal_eq_of_forall {Y : Type*} [TopologicalSpace Y] (Θ : PathClassHom Y K)
    (e : C(Y, X))
    (h : ∀ i (g : C(I, Y)) (hg : ∀ t, e (g t) ∈ D.W i),
      ((D.Ψ i).comap (codRestrict (e.comp g) _ hg)).val 0 1 = (Θ.comap g).val 0 1)
    (γ : C(I, Y)) : D.pathVal (e.comp γ) = (Θ.comap γ).val 0 1 := by
  obtain ⟨N, hN0, hN⟩ := D.exists_fine (e.comp γ)
  rw [D.pathVal_eq_pathValN (hN N le_rfl) hN0, pathValN]
  have key : ∀ k < N, D.segVal (e.comp γ) (pt N k) (pt N (k + 1)) =
      (Θ.comap γ).val (pt N k) (pt N (k + 1)) := by
    intro k hk
    obtain ⟨i, hi⟩ := hN N le_rfl k hk
    rw [D.segVal_eq_val _ i hi left_mem_uIcc right_mem_uIcc]
    set a := pt N k
    set b := pt N (k + 1)
    set c := codRestrict ((e.comp γ).comp (segIncl a b)) _ fun t => hi t.1 t.2
    let ρ := PathConnectedSpace.somePath (⟨a, left_mem_uIcc⟩ : uIcc a b) ⟨b, right_mem_uIcc⟩
    have h1 := PathClassHom.val_comap_comp (D.Ψ i) c ρ.toContinuousMap 0 1
    rw [Path.coe_toContinuousMap, ρ.source, ρ.target] at h1
    refine h1.symm.trans ((h i (γ.comp ((segIncl a b).comp ρ.toContinuousMap))
      (fun t => hi _ (ρ t).2)).trans ?_)
    rw [PathClassHom.val_comap_comp]
    congr 1 <;> simp [segIncl, ρ, a, b]
  rw [List.map_congr_left (fun k hk => key k (List.mem_range.1 hk)),
    PathClassHom.prod_val (Θ.comap γ) (pt N) N, pt_zero, pt_self hN0]

/-- The glued value of a path in a member `W i` of the cover is given by `Ψ i`. -/
theorem pathVal_of_mem (i : ι) (γ : C(I, D.W i)) :
    D.pathVal ((ContinuousMap.mk Subtype.val continuous_subtype_val).comp γ) =
      ((D.Ψ i).comap γ).val 0 1 := by
  refine D.pathVal_eq_of_forall (D.Ψ i) _ (fun j g hg => ?_) γ
  have hg' : ∀ t, (g t : X) ∈ D.W j ∩ D.W i := fun t => ⟨hg t, (g t).2⟩
  have := D.val_comap_inclusion j i (codRestrict (ContinuousMap.mk Subtype.val
    continuous_subtype_val |>.comp g) _ hg') 0 1
  exact this

end comparison

section homotopy

/-- The row `t ↦ H (s, t)` of a map `H : C(I × I, X)`. -/
def row (H : C(I × I, X)) (s : I) : C(I, X) :=
  H.comp ((ContinuousMap.const I s).prodMk (ContinuousMap.id I))

/-- The column `s ↦ H (s, t)` of a map `H : C(I × I, X)`. -/
def col (H : C(I × I, X)) (t : I) : C(I, X) :=
  H.comp ((ContinuousMap.id I).prodMk (ContinuousMap.const I t))

@[simp]
theorem row_apply (H : C(I × I, X)) (s t : I) : row H s t = H (s, t) :=
  rfl

@[simp]
theorem col_apply (H : C(I × I, X)) (s t : I) : col H t s = H (s, t) :=
  rfl

/-- The square relation: for a small rectangle of `H` lying in a member of the cover, the value
along the bottom edge equals the value along the other three edges. -/
theorem segVal_row (H : C(I × I, X)) (s s' a b : I) (i : ι)
    (hi : ∀ u ∈ uIcc s s', ∀ v ∈ uIcc a b, H (u, v) ∈ D.W i) :
    D.segVal (row H s) a b =
      D.segVal (col H a) s s' * D.segVal (row H s') a b * (D.segVal (col H b) s s')⁻¹ := by
  let g : C(uIcc s s' × uIcc a b, X) :=
    H.comp ((segIncl s s').prodMap (segIncl a b))
  have hg : ∃ i, ∀ z, g z ∈ D.W i := ⟨i, fun z => hi _ z.1.2 _ z.2.2⟩
  have hrow : ∀ (u : I) (hu : u ∈ uIcc s s'), D.segVal (row H u) a b =
      D.localVal g (⟨u, hu⟩, ⟨a, left_mem_uIcc⟩) (⟨u, hu⟩, ⟨b, right_mem_uIcc⟩) := by
    intro u hu
    have : (row H u).comp (segIncl a b) =
        g.comp ((ContinuousMap.const _ ⟨u, hu⟩).prodMk (ContinuousMap.id _)) := rfl
    rw [segVal, this, D.localVal_comp _ _ hg]
    rfl
  have hcol : ∀ (v : I) (hv : v ∈ uIcc a b), D.segVal (col H v) s s' =
      D.localVal g (⟨s, left_mem_uIcc⟩, ⟨v, hv⟩) (⟨s', right_mem_uIcc⟩, ⟨v, hv⟩) := by
    intro v hv
    have : (col H v).comp (segIncl s s') =
        g.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ ⟨v, hv⟩)) := rfl
    rw [segVal, this, D.localVal_comp _ _ hg]
    rfl
  rw [hrow s left_mem_uIcc, hrow s' right_mem_uIcc, hcol a left_mem_uIcc,
    hcol b right_mem_uIcc, D.localVal_mul g hg, ← D.localVal_symm g hg, D.localVal_mul g hg]

theorem _root_.List.prod_range_telescope {G : Type*} [Group G] (a b c : ℕ → G) (n : ℕ)
    (h : ∀ k < n, a k = c k * b k * (c (k + 1))⁻¹) :
    ((List.range n).map a).prod = c 0 * ((List.range n).map b).prod * (c n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, List.prod_range_succ, ih (fun k hk => h k (by omega)),
      h n (by omega)]
    group

/-- Homotopy invariance: if `H` is constant on the left and right edges `t = 0` and `t = 1`,
the bottom and top rows have the same glued value. -/
theorem pathVal_row_zero (H : C(I × I, X)) (x y : X) (h0 : ∀ s, H (s, 0) = x)
    (h1 : ∀ s, H (s, 1) = y) : D.pathVal (row H 0) = D.pathVal (row H 1) := by
  obtain ⟨δ, hδ, hH⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i => (D.isOpen i).preimage H.continuous)
    (fun x _ => mem_iUnion.2 (D.exists_mem (H x)))
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  set n := N + 1 with hn
  have hn0 : 0 < n := N.succ_pos
  have hnδ : (1 : ℝ) / n < δ := by rw [hn, Nat.cast_succ]; exact hN
  have key : ∀ s s' : I, dist s' s ≤ 1 / n → D.pathVal (row H s) = D.pathVal (row H s') := by
    intro s s' hss'
    have hrect : ∀ k < n, ∃ i, ∀ u ∈ uIcc s s', ∀ v ∈ uIcc (pt n k) (pt n (k + 1)),
        H (u, v) ∈ D.W i := by
      intro k hk
      obtain ⟨i, hi⟩ := hH (s, pt n k) (mem_univ _)
      refine ⟨i, fun u hu v hv => hi ?_⟩
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨(dist_le_of_mem_uIcc hu).trans_lt (hss'.trans_lt hnδ),
        (dist_le_of_mem_uIcc hv).trans_lt ((dist_pt_succ hk).trans_lt hnδ)⟩
    have hfine : ∀ u ∈ uIcc s s', D.Fine (row H u) n := fun u hu k hk => by
      obtain ⟨i, hi⟩ := hrect k hk
      exact ⟨i, fun v hv => hi u hu v hv⟩
    rw [D.pathVal_eq_pathValN (hfine s left_mem_uIcc) hn0,
      D.pathVal_eq_pathValN (hfine s' right_mem_uIcc) hn0, pathValN, pathValN,
      List.prod_range_telescope _ _ (fun k => D.segVal (col H (pt n k)) s s') n
        (fun k hk => by
          obtain ⟨i, hi⟩ := hrect k hk
          exact D.segVal_row H s s' _ _ i hi),
      pt_zero, pt_self hn0, D.segVal_of_const _ x h0, D.segVal_of_const _ y h1]
    group
  have : ∀ j ≤ n, D.pathVal (row H 0) = D.pathVal (row H (pt n j)) := by
    intro j hj
    induction j with
    | zero => rw [pt_zero]
    | succ j ih =>
      rw [ih (by omega), key _ _ (dist_pt_succ (by omega)).le]
  rw [this n le_rfl, pt_self hn0]

/-- Homotopy invariance of the glued value. -/
theorem pathVal_eq_of_homotopic {x y : X} {p q : Path x y} (h : p.Homotopic q) :
    D.pathVal p.toContinuousMap = D.pathVal q.toContinuousMap := by
  obtain ⟨F⟩ := h
  have e0 : row F.toContinuousMap 0 = p.toContinuousMap := by
    ext t
    simp
  have e1 : row F.toContinuousMap 1 = q.toContinuousMap := by
    ext t
    simp
  have := D.pathVal_row_zero F.toContinuousMap x y (fun s => F.source s) (fun s => F.target s)
  rwa [e0, e1] at this

end homotopy

section trans

/-- The map `t ↦ 2t` on the unit interval, truncated at `1`. -/
noncomputable def dblLeft : C(I, I) :=
  ⟨fun t => projIcc 0 1 zero_le_one (2 * t), continuous_projIcc.comp (by fun_prop)⟩

/-- The map `t ↦ 2t - 1` on the unit interval, truncated at `0`. -/
noncomputable def dblRight : C(I, I) :=
  ⟨fun t => projIcc 0 1 zero_le_one (2 * t - 1), continuous_projIcc.comp (by fun_prop)⟩

theorem dblLeft_mono : Monotone dblLeft := fun t t' h =>
  monotone_projIcc zero_le_one (by have : (t : ℝ) ≤ t' := h; linarith)

theorem dblRight_mono : Monotone dblRight := fun t t' h =>
  monotone_projIcc zero_le_one (by have : (t : ℝ) ≤ t' := h; linarith)

theorem dblLeft_pt {n k : ℕ} (hk : k ≤ n + n) : dblLeft (pt (n + n) k) = pt n k := by
  change projIcc 0 1 zero_le_one (2 * (pt (n + n) k : ℝ)) = _
  rw [coe_pt hk, pt]
  congr 1
  push_cast
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := by omega
    simp
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem dblRight_pt {n k : ℕ} (hk : k ≤ n) : dblRight (pt (n + n) (n + k)) = pt n k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := by omega
    ext
    simp [dblRight, pt, coe_projIcc]
  change projIcc 0 1 zero_le_one (2 * (pt (n + n) (n + k) : ℝ) - 1) = _
  rw [coe_pt (by omega), pt]
  congr 1
  push_cast
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem trans_apply_left {x y z : X} (p : Path x y) (q : Path y z) {t : I}
    (ht : (t : ℝ) ≤ 1 / 2) : (p.trans q) t = p (dblLeft t) := by
  rw [Path.trans_apply, dif_pos ht]
  congr 1
  change _ = projIcc 0 1 zero_le_one (2 * (t : ℝ))
  rw [projIcc_of_mem]

theorem trans_apply_right {x y z : X} (p : Path x y) (q : Path y z) {t : I}
    (ht : 1 / 2 ≤ (t : ℝ)) : (p.trans q) t = q (dblRight t) := by
  rw [Path.trans_apply]
  split_ifs with h
  · have h2 : (t : ℝ) = 1 / 2 := le_antisymm h ht
    have e1 : (⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩ : I) = 1 :=
      Subtype.ext (by simp [h2])
    have e2 : dblRight t = 0 := by
      change projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) = 0
      rw [h2]
      norm_num
    rw [e1, e2, p.target, q.source]
  · congr 1
    change _ = projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)
    rw [projIcc_of_mem]

theorem pt_le_half {n k : ℕ} (hk : k ≤ n) : (pt (n + n) k : ℝ) ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp_all
  have : (pt (n + n) k : ℝ) ≤ pt (n + n) n := pt_mono _ hk
  rw [coe_pt (n := n + n) (k := n) (by omega)] at this
  refine this.trans (le_of_eq ?_)
  push_cast
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem half_le_pt {n k : ℕ} (hn : 0 < n) (hk : n ≤ k) : 1 / 2 ≤ (pt (n + n) k : ℝ) := by
  have : (pt (n + n) n : ℝ) ≤ pt (n + n) k := pt_mono _ hk
  rw [coe_pt (n := n + n) (k := n) (by omega)] at this
  refine le_trans (le_of_eq ?_) this
  push_cast
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

theorem mem_uIcc_pt {m k : ℕ} {t : I} (ht : t ∈ uIcc (pt m k) (pt m (k + 1))) :
    pt m k ≤ t ∧ t ≤ pt m (k + 1) := by
  rwa [uIcc_of_le (pt_mono m k.le_succ)] at ht

/-- The segments of `p.trans q` over the subdivision into `n + n` pieces: the first `n` are the
segments of `p`, the last `n` those of `q`. -/
theorem segVal_trans_left {x y z : X} (p : Path x y) (q : Path y z) {n k : ℕ} (hk : k < n)
    (hp : D.Covers p.toContinuousMap (pt n k) (pt n (k + 1))) :
    D.segVal (p.trans q).toContinuousMap (pt (n + n) k) (pt (n + n) (k + 1)) =
      D.segVal p.toContinuousMap (pt n k) (pt n (k + 1)) := by
  have hmaps := dblLeft_mono.mapsTo_uIcc (a := pt (n + n) k) (b := pt (n + n) (k + 1))
  rw [dblLeft_pt (by omega), dblLeft_pt (by omega)] at hmaps
  refine D.segVal_eq_of_eqOn _ _ dblLeft (fun t ht => hmaps ht) (fun t ht => ?_)
    (dblLeft_pt (by omega)) (dblLeft_pt (by omega)) hp
  exact trans_apply_left p q (le_trans (mem_uIcc_pt ht).2 (pt_le_half (by omega)))

theorem segVal_trans_right {x y z : X} (p : Path x y) (q : Path y z) {n k : ℕ} (hk : k < n)
    (hq : D.Covers q.toContinuousMap (pt n k) (pt n (k + 1))) :
    D.segVal (p.trans q).toContinuousMap (pt (n + n) (n + k)) (pt (n + n) (n + k + 1)) =
      D.segVal q.toContinuousMap (pt n k) (pt n (k + 1)) := by
  have hmaps := dblRight_mono.mapsTo_uIcc (a := pt (n + n) (n + k)) (b := pt (n + n) (n + k + 1))
  rw [dblRight_pt (by omega), Nat.add_assoc, dblRight_pt (by omega)] at hmaps
  refine D.segVal_eq_of_eqOn _ _ dblRight (fun t ht => hmaps ht) (fun t ht => ?_)
    (dblRight_pt (by omega)) (by rw [Nat.add_assoc, dblRight_pt (by omega)]) hq
  exact trans_apply_right p q (le_trans (half_le_pt (by omega) (by omega)) (mem_uIcc_pt ht).1)

theorem fine_trans {x y z : X} {p : Path x y} {q : Path y z} {n : ℕ}
    (hp : D.Fine p.toContinuousMap n) (hq : D.Fine q.toContinuousMap n) :
    D.Fine (p.trans q).toContinuousMap (n + n) := by
  intro k hk
  rcases lt_or_ge k n with hkn | hkn
  · obtain ⟨i, hi⟩ := hp k hkn
    have hmaps := dblLeft_mono.mapsTo_uIcc (a := pt (n + n) k) (b := pt (n + n) (k + 1))
    rw [dblLeft_pt (by omega), dblLeft_pt (by omega)] at hmaps
    refine ⟨i, fun t ht => ?_⟩
    change (p.trans q) t ∈ _
    rw [trans_apply_left p q (le_trans (mem_uIcc_pt ht).2 (pt_le_half (by omega)))]
    exact hi _ (hmaps ht)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hkn
    obtain ⟨i, hi⟩ := hq k (by omega)
    have hmaps := dblRight_mono.mapsTo_uIcc (a := pt (n + n) (n + k))
      (b := pt (n + n) (n + k + 1))
    rw [dblRight_pt (by omega), Nat.add_assoc, dblRight_pt (by omega)] at hmaps
    refine ⟨i, fun t ht => ?_⟩
    change (p.trans q) t ∈ _
    rw [trans_apply_right p q (le_trans (half_le_pt (by omega) (by omega)) (mem_uIcc_pt ht).1)]
    exact hi _ (hmaps ht)

/-- The glued value turns concatenation of paths into multiplication. -/
theorem pathVal_trans {x y z : X} (p : Path x y) (q : Path y z) :
    D.pathVal (p.trans q).toContinuousMap =
      D.pathVal p.toContinuousMap * D.pathVal q.toContinuousMap := by
  obtain ⟨Np, hNp0, hNp⟩ := D.exists_fine p.toContinuousMap
  obtain ⟨Nq, hNq0, hNq⟩ := D.exists_fine q.toContinuousMap
  set n := max Np Nq
  have hn0 : 0 < n := lt_max_of_lt_left hNp0
  have hp := hNp n (le_max_left _ _)
  have hq := hNq n (le_max_right _ _)
  rw [D.pathVal_eq_pathValN (D.fine_trans hp hq) (by omega), D.pathVal_eq_pathValN hp hn0,
    D.pathVal_eq_pathValN hq hn0, pathValN, List.range_add, List.map_append, List.prod_append,
    List.map_map, pathValN, pathValN]
  congr 2
  · refine List.map_congr_left fun k hk => ?_
    exact D.segVal_trans_left p q (List.mem_range.1 hk) (hp k (List.mem_range.1 hk))
  · refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp_apply]
    exact D.segVal_trans_right p q (List.mem_range.1 hk) (hq k (List.mem_range.1 hk))

end trans

section glue

/-- The glued function as a `VanKampen.PathClassHom` on `X`: its value on the class of a path
`γ` is `VanKampen.CoverData.pathVal γ`. -/
noncomputable def glue : PathClassHom X K where
  toFun {a b} p := Quotient.liftOn p (s := Path.Homotopic.setoid a b)
    (fun γ => D.pathVal γ.toContinuousMap) (fun _ _ h => D.pathVal_eq_of_homotopic h)
  map_trans' p q := by
    induction p using Path.Homotopic.Quotient.ind with | mk p =>
    induction q using Path.Homotopic.Quotient.ind with | mk q =>
    exact D.pathVal_trans p q

theorem glue_mk {a b : X} (γ : Path a b) :
    D.glue.toFun (Path.Homotopic.Quotient.mk γ) = D.pathVal γ.toContinuousMap :=
  rfl

/-- The glued function extends each `Ψ i`. -/
theorem glue_map_val (i : ι) {a b : D.W i} (p : Path.Homotopic.Quotient a b) :
    D.glue.toFun (p.map ⟨Subtype.val, continuous_subtype_val⟩) = (D.Ψ i).toFun p := by
  induction p using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [← Path.Homotopic.Quotient.mk_map, glue_mk, ← PathClassHom.val_comap_path]
  exact D.pathVal_of_mem i γ.toContinuousMap

/-- The glued function is the only `VanKampen.PathClassHom` on `X` extending each `Ψ i`. -/
theorem eq_glue (Θ : PathClassHom X K)
    (hΘ : ∀ i {a b : D.W i} (p : Path.Homotopic.Quotient a b),
      Θ.toFun (p.map ⟨Subtype.val, continuous_subtype_val⟩) = (D.Ψ i).toFun p)
    {a b : X} (p : Path.Homotopic.Quotient a b) : Θ.toFun p = D.glue.toFun p := by
  induction p using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [glue_mk, ← PathClassHom.val_comap_path]
  refine (D.pathVal_eq_of_forall Θ (ContinuousMap.id X) (fun i g hg => ?_)
    γ.toContinuousMap).symm
  rw [PathClassHom.val, PathClassHom.val, PathClassHom.comap_toFun, PathClassHom.comap_toFun,
    ← hΘ, ← Path.Homotopic.Quotient.map_comp]
  rfl

end glue

end CoverData

end VanKampen

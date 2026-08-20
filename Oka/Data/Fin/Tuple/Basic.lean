/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Missing `Fin.init` lemmas

Material for `Mathlib/Data/Fin/Tuple/Basic.lean`; see the tracking issue on moving the
project's Mathlib-bound lemmas into this mirror tree.
-/

namespace Fin

variable {n : ℕ} {α : Type*} [Zero α]

/-- Dropping the last coordinate of the zero tuple gives the zero tuple.

This is the `simp` normal form that `Fin.init` needs: without it a goal such as
`TopologicalSpace.Opens.zero_mem_extend'` normalises to `Fin.init 0 ∈ U` and `simp` gets
stuck one rewrite short of the answer. -/
@[simp]
lemma init_zero : Fin.init (0 : Fin (n + 1) → α) = 0 :=
  rfl

end Fin

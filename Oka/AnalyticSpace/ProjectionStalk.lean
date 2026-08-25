/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Oka.AnalyticSpace.HolomorphicMap

/-!
# The projection `ℂ^(n+1) → ℂ^n` on germs and stalks

The projection forgetting the last coordinate is `ComplexAnalytic.okaMapHom` at the family of the
first `n` coordinate functions. This file computes what it does to a germ: **through
`okaStalkEquiv`, it is `LocalOkaRing.incl`**, the inclusion of the power series that do not
involve the last variable.

That identification is what a quotient statement about `LocalOkaRing` needs before it can be read
as a statement about a morphism of spaces. `LocalOkaRing.quotientDegreeOneEquiv` and
`LocalOkaRing.quotientSimpleZeroEquiv` (`Oka/Regular.lean`) are both built from
`LocalOkaRing.incl` followed by a quotient map, and without a lemma naming the geometric map that
`incl` comes from they identify the germ ring one dimension down with a quotient by an
*abstract* isomorphism rather than by the stalk map of the projection.

## The proof, in one sentence

The Taylor expansion of `s ∘ proj` at `z` is the Taylor expansion of `s` at `proj z` with a dummy
variable added. `MvPowerSeries.Represents.rename_castSucc` is that sentence about power series,
`OkaRing.germ_eq_of_represents` is what reduces a claim about a germ to a claim about what its
series represents, and `LocalOkaRing.coe_incl` says the rename is `incl`.

**The eventual equality is not a formality.** `OkaRing.toGlobalFun` is total, extended off the
domain of its argument, so `s ∘ proj` and `s` agree only over the preimage — which is open and
contains the point, and is where the `filter_upwards` below lands. A pointwise claim without that
neighbourhood is false, not merely unproved.

## Main results

- `ComplexAnalytic.okaMapFun_projCoords`: the underlying map of the projection is `Fin.init`.
- `ComplexAnalytic.germ_okaMapC_projCoords`: the germ of `s ∘ proj` at `z` is the germ of `s` at
  `proj z`, included as a series not involving the last variable.
- `ComplexAnalytic.okaStalkEquiv_stalkMap_okaMapHom_projCoords`: **the stalk map of the
  projection is that inclusion**, transported along the Taylor-expansion isomorphism.

## What is not here

**Neither `LocalOkaRing.incl` nor `okaStalkEquiv` is named in the list above**, though both are
what the results are stated in terms of and both are named in the paragraphs before it. That is
deliberate: `scripts/guard_coverage.py` reads a backticked name under a `## Main results` heading
as a result the file advertises, and neither is a result of this file.

**No `IsIso`.** Assembling this with `ComplexAnalytic.IsCutOutBy`'s `surjective_stalkMap` and
`ker_stalkMap` into an isomorphism of stalks for a hypersurface with a simple zero is the next
step and is not taken; `ComplexAnalytic.isIso_stalkMap_okaMapHom`
(`Oka/AnalyticSpace/StalkLocalInverse.lean`) is the only statement of that shape in the
repository so far, and its hypothesis is an analytic local inverse rather than a cut-out.

**No general substitution.** The Taylor series of `s ∘ okaMapFun u` for an arbitrary family `u`
is a composition of power series, which this repository does not have. The projection is exactly
the case where the operation already exists under another name, `LocalOkaRing.incl`.

**Nothing about `ULift`.** `ComplexAnalytic.AnalyticSpace` is built on `ULift (Fin n)` — see
`ComplexAnalytic.AnalyticSpace.okaMap` — while `LocalOkaRing.incl` and the whole of
`Oka/Weierstrass.lean` are stated for `Fin n`. The bridge between the two indexings is not built
here and nothing below needs it.
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-- **The first `n` coordinates of `ℂ^(n+1)`, as global sections of its structure sheaf.**

`ComplexAnalytic.okaMapHom` at this family is the projection forgetting the last coordinate;
`ComplexAnalytic.okaMapFun_projCoords` says so. -/
def projCoords (n : ℕ) : Fin n → OkaRing (⊤ : Opens (Fin (n + 1) → ℂ)) :=
  fun j ↦ coord j.castSucc

/-- **The map underlying the projection is `Fin.init`.** -/
theorem okaMapFun_projCoords (z : Fin (n + 1) → ℂ) :
    okaMapFun (projCoords n) z = Fin.init z := by
  funext j
  rw [okaMapFun_apply, projCoords, evalHom_coord]
  rfl

/-- **The germ of `s ∘ proj` at `z` is `LocalOkaRing.incl` of the germ of `s` at `proj z`.**

`OkaRing.germ_eq_of_represents` reduces this to what the two power series represent, and
`MvPowerSeries.Represents.rename_castSucc` is the statement that a series representing `F` in `n`
variables represents `F ∘ Fin.init` in `n + 1`. The only computation is
`Fin.init (w + z) = Fin.init w + Fin.init z`, which holds by definition.

The neighbourhood in the `filter_upwards` is the preimage of `W`, translated to the origin: off
it the two sides are values of `OkaRing.toGlobalFun` outside its domain and need not agree. -/
theorem germ_okaMapC_projCoords {z : Fin (n + 1) → ℂ} {W : Opens (Fin n → ℂ)}
    (hz : z ∈ (Opens.map (okaMapBase (projCoords n))).obj W) (s : OkaRing W) :
    OkaRing.germ hz (okaMapC (projCoords n) W s)
      = LocalOkaRing.incl (OkaRing.germ (show okaMapFun (projCoords n) z ∈ W from hz) s) := by
  refine OkaRing.germ_eq_of_represents _ ?_
  rw [LocalOkaRing.coe_incl]
  refine (MvPowerSeries.Represents.rename_castSucc
    (OkaRing.germ_represents (show okaMapFun (projCoords n) z ∈ W from hz) s)).congr ?_
  have hset : IsOpen {w : Fin (n + 1) → ℂ |
      w + z ∈ (Opens.map (okaMapBase (projCoords n))).obj W} :=
    ((Opens.map (okaMapBase (projCoords n))).obj W).isOpen.preimage (by fun_prop)
  filter_upwards [hset.mem_nhds (by simpa using hz)] with w hw
  have hkey : Fin.init w + okaMapFun (projCoords n) z = okaMapFun (projCoords n) (w + z) := by
    rw [okaMapFun_projCoords, okaMapFun_projCoords]
    rfl
  have hw' : okaMapFun (projCoords n) (w + z) ∈ W := hw
  rw [hkey, s.toGlobalFun_apply hw', OkaRing.toGlobalFun_apply _ hw]
  rfl

/-- **Transported along `okaStalkEquiv`, the stalk map of the projection is
`LocalOkaRing.incl`.**

This is the previous statement at the spelling a caller holding a stalk rather than a germ needs:
`PresheafedSpace.stalkMap_germ_apply` turns the stalk map on a germ into the germ of the pullback,
and `okaStalkEquiv_germ` is the Taylor expansion at either end. Stated on germs because
`(okaCommPresheaf ι).germ` is jointly surjective onto the stalk, so this determines the stalk map
completely. -/
theorem okaStalkEquiv_stalkMap_okaMapHom_projCoords {z : Fin (n + 1) → ℂ}
    {W : Opens (Fin n → ℂ)} (hw : okaMapFun (projCoords n) z ∈ W) (s : OkaRing W) :
    okaStalkEquiv z ((okaMapHom (projCoords n)).stalkMap z
        ((okaCommPresheaf (Fin n)).germ W _ hw s))
      = LocalOkaRing.incl (okaStalkEquiv (okaMapFun (projCoords n) z)
          ((okaCommPresheaf (Fin n)).germ W _ hw s)) := by
  have hz : z ∈ (Opens.map (okaMapBase (projCoords n))).obj W := hw
  have hmap : ((okaMapPre (projCoords n)).stalkMap z).hom
        ((okaCommPresheaf (Fin n)).germ W ((okaMapPre (projCoords n)).base z) hw s) =
      (okaCommPresheaf (Fin (n + 1))).germ ((Opens.map (okaMapBase (projCoords n))).obj W) z hz
        (okaMapC (projCoords n) W s) :=
    PresheafedSpace.stalkMap_germ_apply (okaMapPre (projCoords n)) W z hw s
  rw [show (okaMapHom (projCoords n)).stalkMap z
      ((okaCommPresheaf (Fin n)).germ W _ hw s) = _ from hmap,
    okaStalkEquiv_germ, okaStalkEquiv_germ, germ_okaMapC_projCoords]

end ComplexAnalytic

end

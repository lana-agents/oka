import Oka.Analytification.LocalRing
import Oka.Polynomial.Germ

open MvPowerSeries IsLocalRing

universe u

noncomputable section

namespace ComplexAnalytic

variable {ι : Type u} [Fintype ι]

omit [Fintype ι] in
theorem represents_X (i : ι) : (X i : MvPowerSeries ι ℂ).Represents (fun z ↦ z i) := by
  refine Filter.Eventually.of_forall fun z ↦ ?_
  have h := hasSum_single (Finsupp.single i 1)
    (f := (X i : MvPowerSeries ι ℂ).term z) ?_
  · simpa [MvPowerSeries.term, MvPowerSeries.coeff_X, MvPowerSeries.evalMonomial_single_one]
      using h
  · intro d hd
    classical
    rw [MvPowerSeries.term, MvPowerSeries.coeff_X, if_neg hd, zero_mul]

theorem ofMvPolynomial_zero_X (i : ι) :
    LocalOkaRing.ofMvPolynomial (0 : ι → ℂ) (MvPolynomial.X i) = LocalOkaRing.coord i := by
  refine OkaRing.germ_eq_of_represents (U := ⊤) (y := 0) trivial ?_
  rw [LocalOkaRing.coe_coord]
  refine (represents_X i).congr (Filter.Eventually.of_forall fun z ↦ ?_)
  show z i = (OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X i)).toGlobalFun ⊤ (z + 0)
  rw [OkaRing.toGlobalFun_ofMvPolynomial (U := ⊤) trivial]
  simp

theorem coe_ofMvPolynomial_zero (p : MvPolynomial ι ℂ) :
    ((LocalOkaRing.ofMvPolynomial (0 : ι → ℂ) p : LocalOkaRing ι) : MvPowerSeries ι ℂ) =
      (p : MvPowerSeries ι ℂ) := by
  have h : (localOkaSubring ι).val.comp (LocalOkaRing.ofMvPolynomial (0 : ι → ℂ)) =
      MvPolynomial.coeToMvPowerSeries.algHom ℂ := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rw [AlgHom.comp_apply, ofMvPolynomial_zero_X, Subalgebra.val_apply, LocalOkaRing.coe_coord]
    simp
  exact congrArg (fun f : MvPolynomial ι ℂ →ₐ[ℂ] MvPowerSeries ι ℂ ↦ f p) h


section Flat

open TensorProduct

/-- **The local ring of `𝔸^ι` at the origin maps to the germ ring**: a rational function regular
at the origin has a germ. -/
def polyLocalToGerm : polyLocal ι →ₐ[ℂ] LocalOkaRing ι :=
  IsLocalization.liftAlgHom (M := (MvPolynomial.idealOfVars ι ℂ).primeCompl)
    (f := LocalOkaRing.ofMvPolynomial (0 : ι → ℂ)) fun y ↦
      (LocalOkaRing.isUnit_ofMvPolynomial_iff _ _).mpr fun hcon ↦ y.2 (by
        have : (y : MvPolynomial ι ℂ) ∈ RingHom.ker (MvPolynomial.eval fun _ : ι ↦ (0 : ℂ)) :=
          RingHom.mem_ker.mpr hcon
        rwa [← MvPolynomial.idealOfVars_eq_ker_eval_zero] at this)

theorem polyLocalToGerm_algebraMap (q : MvPolynomial ι ℂ) :
    polyLocalToGerm (algebraMap (MvPolynomial ι ℂ) (polyLocal ι) q) =
      LocalOkaRing.ofMvPolynomial (0 : ι → ℂ) q :=
  IsLocalization.lift_eq _ q

theorem coe_polyLocalToGerm (a : polyLocal ι) :
    ((polyLocalToGerm a : LocalOkaRing ι) : MvPowerSeries ι ℂ) = polyLocalToMvPowerSeries a := by
  revert a
  have h : ((localOkaSubring ι).val.comp (polyLocalToGerm (ι := ι))).toRingHom =
      (polyLocalToMvPowerSeries (ι := ι)).toRingHom := by
    refine IsLocalization.ringHom_ext (MvPolynomial.idealOfVars ι ℂ).primeCompl ?_
    refine RingHom.ext fun q ↦ ?_
    show ((polyLocalToGerm (algebraMap (MvPolynomial ι ℂ) (polyLocal ι) q) :
      LocalOkaRing ι) : MvPowerSeries ι ℂ) = _
    rw [polyLocalToGerm_algebraMap, coe_ofMvPolynomial_zero]
    exact (polyLocalToMvPowerSeries_algebraMap q).symm
  exact fun a ↦ RingHom.congr_fun h a

end Flat

end ComplexAnalytic

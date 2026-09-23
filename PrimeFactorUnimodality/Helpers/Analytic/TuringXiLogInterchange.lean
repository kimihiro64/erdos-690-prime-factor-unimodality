import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogStep
import PrimeFactorUnimodality.Helpers.Analytic.XiHadamardIntegral

/-! # Absolute interchange for the complete xi logarithmic-step family

The actual divisor's existing countability and the nonnegative kernel turn
the proved integrated-step summability into a summable family of integrated
norms. The existing Bochner-series lemma then justifies the whole interchange.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The pointwise logarithmic-step atom attached to an actual multiplicity label. -/
def turingXiLogAtom (T : ℝ) (p : RiemannXiDivisorZeroIndex) (x : ℝ) : ℝ :=
  logNormStep (riemannXiDivisorZeroValue p - ((1 / 2 : ℂ) + T * I)) x

/-- Every actual atom is nonnegative on the nonnegative real ray. -/
theorem turingXiLogAtom_nonneg (T : ℝ) (p : RiemannXiDivisorZeroIndex)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ turingXiLogAtom T p x := by
  apply logNormStep_nonneg _ hx
  have hh := (riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p)).2
  simp only [sub_re, add_re, div_ofNat_re, one_re, mul_re, ofReal_re, I_re, ofReal_im,
    I_im, mul_zero, zero_mul, sub_self, add_zero]
  linarith

/-- The integrated norm agrees exactly with the already defined nonnegative step. -/
theorem integral_norm_turingXiLogAtom (T : ℝ) (p : RiemannXiDivisorZeroIndex) :
    (∫ x in Ioc (0 : ℝ) 1, ‖turingXiLogAtom T p x‖) = turingXiLogStep T p := by
  change _ = ∫ x in (0 : ℝ)..1, turingXiLogAtom T p x
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact Real.norm_of_nonneg (turingXiLogAtom_nonneg T p hx.1.le)

/-- The complete divisor family has summable integrated absolute values. -/
theorem summable_integral_norm_turingXiLogAtom (T : ℝ) :
    Summable (fun p => ∫ x in Ioc (0 : ℝ) 1, ‖turingXiLogAtom T p x‖) := by
  simpa only [integral_norm_turingXiLogAtom] using summable_turingXiLogStep T

/-- The full pointwise logarithmic-step series is integrable on the unit interval. -/
theorem intervalIntegrable_tsum_turingXiLogAtom (T : ℝ) :
    IntervalIntegrable (fun x => ∑' p, turingXiLogAtom T p x) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact integrable_tsum_of_summable_integral_norm
    (fun p => (intervalIntegrable_logNormStep _ 0 1).1)
    (summable_integral_norm_turingXiLogAtom T)

/-- Integrating the complete pointwise series gives the complete integrated spectral budget. -/
theorem integral_tsum_turingXiLogAtom (T : ℝ) :
    (∫ x in (0 : ℝ)..1, ∑' p, turingXiLogAtom T p x) = ∑' p, turingXiLogStep T p := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hF (p : RiemannXiDivisorZeroIndex) :
      Integrable (turingXiLogAtom T p) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_logNormStep _ 0 1).1
  rw [← integral_tsum_of_summable_integral_norm
    hF
    (summable_integral_norm_turingXiLogAtom T)]
  apply tsum_congr
  intro p
  exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

end

end PrimeFactorUnimodality

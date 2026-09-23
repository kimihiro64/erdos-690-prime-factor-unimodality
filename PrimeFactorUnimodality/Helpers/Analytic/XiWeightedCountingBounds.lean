import PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingHigh

/-! # Weighted xi counting estimates on either side of a turning point

The actual count satisfies `abs(N(t)-P(t)) <= log(t)+17` from height ten.
Integrating this envelope by parts retains its derivative `1/t`, rather
than replacing the whole interval error by a constant. Both endpoint
discrepancies are kept with their signs. These are the two monotonicity
branches of the Rosser counting argument, with the proved local envelope.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- Integration by parts evaluates the derivative-weighted counting-error envelope. -/
theorem integral_log_count_envelope_mul_deriv {a b : ℝ} {f g : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Icc a b)) :
    (∫ t in Icc a b, (Real.log t + 17) * g t) =
      (Real.log b + 17) * f b - (Real.log a + 17) * f a -
        ∫ t in Icc a b, f t / t := by
  have hc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hl : ContinuousOn Real.log (Icc a b) := continuousOn_id.log
    (fun t ht => (ha.trans_le ht.1).ne')
  have hdiv : ContinuousOn (fun t => f t / t) (Icc a b) :=
    hc.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')
  have hprod : ContinuousOn (fun t => (Real.log t + 17) * g t) (Icc a b) :=
    (hl.add_const 17).mul hg
  have he : (∫ t in Icc a b, f t / t + (Real.log t + 17) * g t) =
      (Real.log b + 17) * f b - (Real.log a + 17) * f a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => (Real.log t + 17) * f t)
    · intro t ht
      rw [uIcc_of_le hab] at ht
      convert ((Real.hasDerivAt_log (ha.trans_le ht.1).ne').add_const 17).mul
        (hf t ht) using 1
      ring
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
        (hdiv.integrableOn_Icc.add hprod.integrableOn_Icc)
  rw [integral_add hdiv.integrableOn_Icc hprod.integrableOn_Icc] at he
  linarith

/-- A decreasing interval retains signed endpoint errors and a positive density correction. -/
theorem sum_xi_weighted_window_le_of_slope_nonpos {a b : ℝ} {f g : ℝ → ℝ}
    (ha : 10 ≤ a) (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Icc a b)) (hgn : ∀ t ∈ Icc a b, g t ≤ 0) :
    (∑ p ∈ xiHeightWindowIndices a b, f (riemannXiDivisorZeroValue p).im) ≤
      (∫ t in Icc a b, ((1 / (2 * π)) * Real.log (t / (2 * π))) * f t) +
      (∫ t in Icc a b, f t / t) +
      (xiZeroCountingRemainder b - (Real.log b + 17)) * f b -
      (xiZeroCountingRemainder a - (Real.log a + 17)) * f a := by
  have ha0 : 0 < a := by linarith
  have hl : ContinuousOn Real.log (Icc a b) := continuousOn_id.log
    (fun t ht => (ha0.trans_le ht.1).ne')
  have hI : (∫ t in Icc a b, (Real.log t + 17) * g t) ≤
      ∫ t in Icc a b, xiZeroCountingRemainder t * g t := by
    apply integral_mono_ae ((hl.add_const 17).mul hg).integrableOn_Icc
      (integrableOn_xiZeroCountingRemainder_mul ha0 hg.integrableOn_Icc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_le_mul_of_nonpos_right
      ((abs_le.mp (abs_xiZeroCountingRemainder_le_log_add (ha.trans ht.1))).2) (hgn t ht)
  rw [integral_log_count_envelope_mul_deriv ha0 hab hf hg] at hI
  have he := sum_xi_height_window_sub_main_eq_remainder ha0 hab hf hg.integrableOn_Icc
  nlinarith only [hI, he]

/-- An increasing interval has a negative density correction and plus-signed endpoint errors. -/
theorem sum_xi_weighted_window_le_of_slope_nonneg {a b : ℝ} {f g : ℝ → ℝ}
    (ha : 10 ≤ a) (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Icc a b)) (hgn : ∀ t ∈ Icc a b, 0 ≤ g t) :
    (∑ p ∈ xiHeightWindowIndices a b, f (riemannXiDivisorZeroValue p).im) ≤
      (∫ t in Icc a b, ((1 / (2 * π)) * Real.log (t / (2 * π))) * f t) -
      (∫ t in Icc a b, f t / t) +
      (xiZeroCountingRemainder b + (Real.log b + 17)) * f b -
      (xiZeroCountingRemainder a + (Real.log a + 17)) * f a := by
  have ha0 : 0 < a := by linarith
  have hl : ContinuousOn Real.log (Icc a b) := continuousOn_id.log
    (fun t ht => (ha0.trans_le ht.1).ne')
  have hI : -(∫ t in Icc a b, (Real.log t + 17) * g t) ≤
      ∫ t in Icc a b, xiZeroCountingRemainder t * g t := by
    rw [← integral_neg]
    apply integral_mono_ae ((hl.add_const 17).mul hg).integrableOn_Icc.neg
      (integrableOn_xiZeroCountingRemainder_mul ha0 hg.integrableOn_Icc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change -((Real.log t + 17) * g t) ≤ xiZeroCountingRemainder t * g t
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right
      ((abs_le.mp (abs_xiZeroCountingRemainder_le_log_add (ha.trans ht.1))).1) (hgn t ht)
  rw [integral_log_count_envelope_mul_deriv ha0 hab hf hg] at hI
  have he := sum_xi_height_window_sub_main_eq_remainder ha0 hab hf hg.integrableOn_Icc
  nlinarith only [hI, he]

end

end PrimeFactorUnimodality

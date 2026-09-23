import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingAbel

/-! # Reciprocal-norm mass on a positive ordinate window

Apply the existing finite Abel identity to `1/t`. The exact boundary count
and integral include multiplicity and the upper endpoint. Complex reciprocal
norms are no larger than reciprocal positive ordinates, with no RH premise.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- Exact reciprocal-ordinate summation on `(a,b]`, including all multiplicity labels. -/
theorem sum_xi_inv_im_window_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ p ∈ xiHeightWindowIndices a b, 1 / (riemannXiDivisorZeroValue p).im) =
      (xiZeroCount b : ℝ) / b - (xiZeroCount a : ℝ) / a +
        ∫ t in Icc a b, (xiZeroCount t : ℝ) / t ^ 2 := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun t : ℝ => 1 / t) (-(1 / t ^ 2)) t := by
    simpa only [Pi.div_def, id_eq, zero_mul, one_mul, zero_sub, neg_div] using
      (hasDerivAt_const t (1 : ℝ)).div
        (hasDerivAt_id t) (ha.trans_le ht.1).ne'
  have hc : ContinuousOn (fun t : ℝ => -(1 / t ^ 2)) (Icc a b) :=
    (continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (ha.trans_le ht.1).ne')).neg
  have he := sum_xi_height_window_eq_boundary_sub_integral hab hd hc.integrableOn_Icc
  simpa only [mul_one_div, mul_neg, integral_neg, sub_neg_eq_add] using he

/-- The positive ordinate is a lower bound for the norm of each complex zero. -/
theorem sum_xi_reciprocal_norm_window_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ p ∈ xiHeightWindowIndices a b, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      (xiZeroCount b : ℝ) / b - (xiZeroCount a : ℝ) / a +
        ∫ t in Icc a b, (xiZeroCount t : ℝ) / t ^ 2 := by
  rw [← sum_xi_inv_im_window_eq ha hab]
  apply Finset.sum_le_sum
  intro p hp
  have hγ := ((mem_xiHeightWindowIndices a b p).mp hp).1.1
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hγ
    ((le_abs_self _).trans (abs_im_le_norm (riemannXiDivisorZeroValue p)))

end

end PrimeFactorUnimodality

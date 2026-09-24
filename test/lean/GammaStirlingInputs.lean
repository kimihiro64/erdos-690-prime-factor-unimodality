import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingInputs

/-! Rational Horner coefficients, inverse conventions and signed logarithm branches. -/

open Complex PrimeFactorUnimodality

example : (RationalPoint.inv ⟨0, 0⟩) = ⟨0, 0⟩ := by norm_num [RationalPoint.inv]

example (z : RationalPoint) : (z.pow 0).toComplex = 1 := by simp

example (z : RationalPoint) : (gammaStirlingRationalCorrection 0 z).toComplex = 0 := by
  simp [toComplex_gammaStirlingRationalCorrection, gammaStirlingCorrection]

example (z : RationalPoint) : (gammaStirlingRationalCorrection 3 z).toComplex =
    (1 / 12 : ℂ) * z.toComplex⁻¹ - (1 / 360 : ℂ) * z.toComplex⁻¹ ^ 3 := by
  rw [toComplex_gammaStirlingRationalCorrection]
  norm_num [gammaStirlingCorrection, Finset.sum_range_succ,
    Polynomial.bernoulliNormalizedReal_zero, bernoulli, bernoulli'_two,
    bernoulli'_three, bernoulli'_four]
  ring

example : log (1 - I) = ((Real.log 2 / 2 : ℝ) : ℂ) - (Real.pi / 4 : ℂ) * I := by
  rw [log_eq_cartesian_of_re_pos (by norm_num)]
  norm_num [Real.arctan_neg, Real.arctan_one]
  ring

example {z : ℂ} (hz : 0 < z.re) (hi : z.im < 0) :
    Real.arctan (z.im / z.re) = -(Real.pi / 2) - Real.arctan (z.re / z.im) := by
  rw [← arg_eq_arctan_im_div_re_of_re_pos hz]
  exact arg_eq_neg_pi_div_two_sub_arctan_of_re_pos hz hi

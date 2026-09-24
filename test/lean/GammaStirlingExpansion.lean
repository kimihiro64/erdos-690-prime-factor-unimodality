import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingBounds

/-! Actual complex Gamma, low-order coefficients and complete remainder transport. -/

open Complex MeasureTheory Polynomial Set PrimeFactorUnimodality

example (z : ℂ) : gammaStirlingCorrection 0 z = 0 := by simp [gammaStirlingCorrection]

example (z : ℂ) : gammaStirlingCorrection 1 z = (1 / 12 : ℂ) * z⁻¹ := by
  norm_num [gammaStirlingCorrection, bernoulliNormalizedReal_zero, _root_.bernoulli_two]

example (z : ℂ) :
    gammaStirlingCorrection 3 z = (1 / 12 : ℂ) * z⁻¹ - (1 / 360 : ℂ) * z⁻¹ ^ 3 := by
  norm_num [gammaStirlingCorrection, Finset.sum_range_succ, bernoulliNormalizedReal_zero,
    _root_.bernoulli, bernoulli'_two, bernoulli'_three, bernoulli'_four]
  ring

example {z : ℂ} (hz : 0 < z.re) :
    gammaRightLog z = gammaStirlingApprox 3 z -
      6 * ∫ x : ℝ in Ioi 0, (bernoulliPeriodic 4 x : ℂ) * (z + (x : ℂ))⁻¹ ^ 4 := by
  simpa [gammaStirlingApprox, Nat.factorial] using
    gammaRightLog_eq_stirling_expansion hz (M := 3) (by omega)

example {z : ℂ} (hz : 0 < z.re) (him : 0 < |z.im|) :
    ‖gammaRightLog z - gammaStirlingApprox 3 z‖ ≤
      8 * (bernoulliCoeffBudget 4 : ℝ) * |z.im| ^ (-3 : ℝ) := by
  have h := norm_gammaRightLog_sub_stirlingApprox_le hz (M := 3) (by omega) him
  convert h using 1
  norm_num [gammaStirlingError]
  ring

example {z w : ℂ} {η : ℝ} (hz : 0 < z.re) (him : 0 < |z.im|)
    (hw : ‖exp (gammaStirlingApprox 3 z) - w‖ ≤ η) :
    ‖Gamma z - w‖ ≤ Real.exp (gammaStirlingApprox 3 z).re *
      (Real.exp (gammaStirlingError 3 |z.im|) - 1) + η := by
  simpa only [add_zero] using norm_Gamma_sub_rounded_stirling_le hz (M := 3) (by omega) him
    (q := gammaStirlingApprox 3 z) (δ := 0) (by simp) hw

example {x : ℝ} (hx : 0 < x) :
    ‖Gamma (x : ℂ) - exp (gammaStirlingApprox 3 (x : ℂ))‖ ≤
      Real.exp (gammaStirlingApprox 3 (x : ℂ)).re * (Real.exp (gammaStirlingError 3 x) - 1) :=
  norm_Gamma_sub_stirling_exp_le_re hx (by omega)

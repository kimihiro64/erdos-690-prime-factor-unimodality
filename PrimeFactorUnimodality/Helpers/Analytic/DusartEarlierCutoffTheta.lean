import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserTheta
import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoffBudget

/-! # Moving the finite theta endpoint below the trillion-scale band

The prime-power correction is bounded by six square-root terms once
`x ≥ 20 ^ 6`. Two complete psi budgets then cover the interval from
ten billion to the existing analytic endpoint, with both seams included.
The only numerical data premise is the stated finite low-zero location.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- At this scale the two smaller root terms cost at most one tenth of the first. -/
theorem dusartThetaRootRelativeCorrection_early_le {x : ℝ} (hx : (20 : ℝ) ^ 6 ≤ x) :
    dusartThetaRootRelativeCorrection x ≤ 6 * exp (-log x / 2) := by
  have hxpos : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hb : 0 ≤ log x := log_nonneg hx1
  have hl := log_le_log (by norm_num : (0 : ℝ) < 20 ^ 6) hx
  rw [log_pow] at hl
  have hsmall : exp (-log x / 6) ≤ (1 / 20 : ℝ) := by
    have h := exp_le_exp.mpr (show -log x / 6 ≤ -log 20 by norm_num at hl; linarith)
    simpa only [exp_neg, exp_log (by norm_num : (0 : ℝ) < 20), one_div] using h
  have hsmaller : exp (-3 * log x / 10) ≤ (1 / 20 : ℝ) :=
    (exp_le_exp.mpr (by linarith : -3 * log x / 10 ≤ -log x / 6)).trans hsmall
  have hsecond : exp (-2 * log x / 3) ≤ exp (-log x / 2) / 20 := by
    rw [show -2 * log x / 3 = -log x / 2 + -log x / 6 by ring, exp_add]
    exact (mul_le_mul_of_nonneg_left hsmall (exp_pos _).le).trans_eq (by ring)
  have hthird : exp (-4 * log x / 5) ≤ exp (-log x / 2) / 20 := by
    rw [show -4 * log x / 5 = -log x / 2 + -3 * log x / 10 by ring, exp_add]
    exact (mul_le_mul_of_nonneg_left hsmaller (exp_pos _).le).trans_eq (by ring)
  have hcoeff : log 4 + 4 ≤ (27 / 5 : ℝ) := by
    have h : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
    linarith [log_two_lt_d9]
  unfold dusartThetaRootRelativeCorrection
  calc
    _ ≤ (27 / 5 : ℝ) * (exp (-log x / 2) +
        exp (-2 * log x / 3) + exp (-4 * log x / 5)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ 6 * exp (-log x / 2) := by nlinarith [exp_pos (-log x / 2)]

/-- A rational square bound eliminates the last exponential in the root correction. -/
theorem dusartThetaRootRelativeCorrection_early_square_le {x r : ℝ}
    (hx : (20 : ℝ) ^ 6 ≤ x) (hr : 0 < r) (hrx : r ^ 2 ≤ x) :
    dusartThetaRootRelativeCorrection x ≤ 6 / r := by
  have hl := log_le_log (pow_pos hr 2) hrx
  rw [log_pow] at hl
  have he : exp (-log x / 2) ≤ 1 / r := by
    have h := exp_le_exp.mpr (show -log x / 2 ≤ -log r by norm_num at hl; linarith)
    simpa only [exp_neg, exp_log hr, one_div] using h
  exact (dusartThetaRootRelativeCorrection_early_le hx).trans
    ((mul_le_mul_of_nonneg_left he (by norm_num)).trans_eq (by ring))

/-- A bounded logarithm converts a constant relative budget to the published coefficient. -/
theorem abs_theta_sub_le_logSquared_of_earlier_cap {x ε B : ℝ}
    (hx : 1 < x) (hB : log x ≤ B) (hε : ε * B ^ 2 ≤ (1 / 5 : ℝ))
    (hθ : |Chebyshev.theta x - x| / x ≤ ε) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 < log x := log_pos hx
  have hε0 : 0 ≤ ε := (div_nonneg (abs_nonneg _) hxpos.le).trans hθ
  have hs : log x ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hlog.le hB 2
  have he : ε ≤ (1 / 5 : ℝ) / log x ^ 2 :=
    (le_div_iff₀ (pow_pos hlog 2)).mpr
      ((mul_le_mul_of_nonneg_left hs hε0).trans hε)
  exact ((div_le_iff₀ hxpos).mp (hθ.trans he)).trans_eq (by ring)

/-- The first interval starts at ten billion, not at the old trillion-scale endpoint. -/
theorem abs_theta_sub_le_logSquared_early_first {x : ℝ}
    (hx : (10000000000 : ℝ) ≤ x) (hX : x ≤ 100000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  have hpsi := abs_psi_sub_div_le_earlier (r := 99000) (by norm_num) (by norm_num) hx hgap
  have hroot := dusartThetaRootRelativeCorrection_early_square_le
    (by linarith : (20 : ℝ) ^ 6 ≤ x) (by norm_num : (0 : ℝ) < 100000)
    (by nlinarith : (100000 : ℝ) ^ 2 ≤ x)
  have hlog : log x ≤ 26 := by
    have h := log_le_log (by linarith : 0 < x) hX
    rw [show (100000000000 : ℝ) = 10 ^ 11 by norm_num, log_pow] at h
    norm_num at h
    linarith [dusart_log_ten_bounds.2]
  apply abs_theta_sub_le_logSquared_of_earlier_cap (by linarith) hlog
    (ε := dusartEarlierAverageCap 99000 + 3 / 100000 + 6 / 100000)
  · norm_num [dusartEarlierAverageCap]
  · exact (abs_theta_sub_div_le_psi_relative_error (by linarith) hpsi).trans
      (add_le_add_right hroot _)

/-- The second interval overlaps the old endpoint, completing the earlier analytic bridge. -/
theorem abs_theta_sub_le_logSquared_early_second {x : ℝ}
    (hx : (100000000000 : ℝ) ≤ x) (hX : x ≤ 1441000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  have hpsi := abs_psi_sub_div_le_earlier (r := 300000) (by norm_num) (by norm_num) hx hgap
  have hroot := dusartThetaRootRelativeCorrection_early_square_le
    (by linarith : (20 : ℝ) ^ 6 ≤ x) (by norm_num : (0 : ℝ) < 300000)
    (by nlinarith : (300000 : ℝ) ^ 2 ≤ x)
  have hlog : log x ≤ 30 := by
    have h := log_le_log (by linarith : 0 < x)
      (by linarith : x ≤ (10 : ℝ) ^ 13)
    rw [log_pow] at h
    norm_num at h
    linarith [dusart_log_ten_bounds.2]
  apply abs_theta_sub_le_logSquared_of_earlier_cap (by linarith) hlog
    (ε := dusartEarlierAverageCap 300000 + 3 / 100000 + 6 / 300000)
  · norm_num [dusartEarlierAverageCap]
  · exact (abs_theta_sub_div_le_psi_relative_error (by linarith) hpsi).trans
      (add_le_add_right hroot _)

/-- The entire old finite tail follows analytically from the existing low-zero premise. -/
theorem abs_theta_sub_le_logSquared_early_bridge {x : ℝ}
    (hx : (10000000000 : ℝ) ≤ x) (hX : x ≤ 1441000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  by_cases h : x ≤ 100000000000
  · exact abs_theta_sub_le_logSquared_early_first hx h hgap
  · exact abs_theta_sub_le_logSquared_early_second (le_of_not_ge h) hX hgap

end

end PrimeFactorUnimodality

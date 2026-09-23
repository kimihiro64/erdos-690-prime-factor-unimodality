import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoffTheta
import PrimeFactorUnimodality.Helpers.Analytic.DusartSharperRootCorrection

/-! # Analytic theta coverage from three billion

The sharper prime-power correction and three overlapping logarithm budgets
extend the existing analytic bridge downward. The complete psi budget and
its low-zero premise are unchanged.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- A square lower bound and logarithmic upper bound certify a whole interval. -/
theorem abs_theta_sub_le_logSquared_of_sharper_cap {x₀ x r B : ℝ}
    (hx₀ : (3000000000 : ℝ) ≤ x₀) (hr : 2 ≤ r)
    (hrx : r ^ 2 ≤ x₀ * (1 - 3 * (1 / 50000)))
    (hx : x₀ ≤ x) (hB : log x ≤ B)
    (hcap : (dusartEarlierAverageCap r + 3 / 100000 + (8 / 5) / r) * B ^ 2 ≤ (1 / 5 : ℝ))
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  have hpsi := abs_psi_sub_div_le_earlier hr hrx hx hgap
  apply abs_theta_sub_le_logSquared_of_earlier_cap (by linarith) hB hcap
  exact abs_theta_sub_div_le_sharper_root (hx₀.trans hx) (by linarith)
    (by nlinarith : r ^ 2 ≤ x) hpsi

/-- The first interval includes the new transition point itself. -/
theorem abs_theta_sub_le_logSquared_billion_first {x : ℝ}
    (hx : (3000000000 : ℝ) ≤ x) (hX : x ≤ 3400000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  have hlog : log x ≤ 22 := by
    have h := log_le_log (by linarith : 0 < x) (show x ≤ (3 : ℝ) ^ 20 by linarith)
    rw [log_pow] at h
    norm_num at h
    linarith [log_three_lt_d9]
  exact abs_theta_sub_le_logSquared_of_sharper_cap le_rfl (r := 54770)
    (by norm_num) (by norm_num) hx hlog (by norm_num [dusartEarlierAverageCap]) hgap

/-- A tighter logarithm budget covers the next interval without freezing it at ten billion. -/
theorem abs_theta_sub_le_logSquared_billion_second {x : ℝ}
    (hx : (3400000000 : ℝ) ≤ x) (hX : x ≤ 5000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  have hlog : log x ≤ (45 / 2 : ℝ) := by
    have h := log_le_log (by linarith : 0 < x) hX
    rw [show (5000000000 : ℝ) = 10 ^ 10 / 2 by norm_num,
      log_div (by norm_num) (by norm_num), log_pow] at h
    norm_num at h
    linarith [dusart_log_ten_bounds.2, log_two_gt_d9]
  exact abs_theta_sub_le_logSquared_of_sharper_cap (by norm_num) (r := 58307)
    (by norm_num) (by norm_num) hx hlog (by norm_num [dusartEarlierAverageCap]) hgap

/-- The final interval joins the previously proved ten-billion ray. -/
theorem abs_theta_sub_le_logSquared_billion_third {x : ℝ}
    (hx : (5000000000 : ℝ) ≤ x) (hX : x ≤ 10000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  have hlog : log x ≤ 24 := by
    have h := log_le_log (by linarith : 0 < x) hX
    rw [show (10000000000 : ℝ) = 10 ^ 10 by norm_num, log_pow] at h
    norm_num at h
    linarith [dusart_log_ten_bounds.2]
  exact abs_theta_sub_le_logSquared_of_sharper_cap (by norm_num) (r := 70708)
    (by norm_num) (by norm_num) hx hlog (by norm_num [dusartEarlierAverageCap]) hgap

/-- The complete bridge includes every real point through the old trillion-scale endpoint. -/
theorem abs_theta_sub_le_logSquared_billion_bridge {x : ℝ}
    (hx : (3000000000 : ℝ) ≤ x) (hX : x ≤ 1441000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  by_cases h₁ : x ≤ 3400000000
  · exact abs_theta_sub_le_logSquared_billion_first hx h₁ hgap
  by_cases h₂ : x ≤ 5000000000
  · exact abs_theta_sub_le_logSquared_billion_second (le_of_not_ge h₁) h₂ hgap
  by_cases h₃ : x ≤ 10000000000
  · exact abs_theta_sub_le_logSquared_billion_third (le_of_not_ge h₂) h₃ hgap
  · exact abs_theta_sub_le_logSquared_early_bridge (le_of_not_ge h₃) hX hgap

end

end PrimeFactorUnimodality

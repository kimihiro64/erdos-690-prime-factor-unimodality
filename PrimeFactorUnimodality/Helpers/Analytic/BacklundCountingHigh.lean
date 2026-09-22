import PrimeFactorUnimodality.Helpers.Analytic.BacklundAveragedJensen
import PrimeFactorUnimodality.Helpers.Analytic.BacklundCircleNumerics
import PrimeFactorUnimodality.Helpers.Analytic.XiGammaContour
import PrimeFactorUnimodality.Helpers.Analytic.XiRegularHeights
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroCountingRemainder

/-! # An unconditional high-height counting-error bound

The asymmetric circle mean, fixed centre bound, and actual gamma contour
give `|N(T)-P(T)| <= log(T)+17` for regular heights `T>=10`. Local finiteness
and the existing right-limit theorem extend this to the closed xi count
with all endpoint multiplicities. Consequently the required `2 log(T)`
envelope holds whenever `log(T)>=17`, without a supplied counting estimate,
circle bound, or zero-free contour assumption in the final theorem.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set

/-- The actual regular-height count satisfies an explicit logarithmic error bound. -/
theorem abs_zeta_N_sub_mainTerm_le_log_add {T : ℝ} (hT : 10 ≤ T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    |riemannZeta.N T - xiZeroCountingMainTerm T| ≤ Real.log T + 17 := by
  have ht : 0 < T := by linarith
  have hσ : (1 : ℝ) < 11 / 10 := by norm_num
  have hH : |(HIntegral (logDeriv Backlund.zetaSurrogate) (1 / 2) (11 / 10) T).im| ≤
      Real.pi * (Real.log T + 14) := by
    have h := abs_im_integral_backlundSurrogate_logDeriv_le_average
      (T := T) (σ := 11 / 10) (r := 3 / 5) (R := 1) (B := backlundCircleLogBound T)
      (a := 1 / 2) (b := 11 / 10) hσ (by norm_num) (by norm_num) (by norm_num)
      (by
        intro x hx
        rw [abs_of_nonpos (by linarith [hx.2])]
        linarith [hx.1])
      (fun x _ => backlund_surrogate_ne_zero_horizontal ht.ne' htop x)
      (fun n => by
        simpa only [ofReal_div, ofReal_ofNat] using circleAverage_log_backlundAuxiliary_le
          (by simpa only [abs_of_pos ht] using hT) n)
    have h' : |(HIntegral (logDeriv Backlund.zetaSurrogate) (1 / 2) (11 / 10) T).im| ≤
        Real.pi * ((backlundCircleLogBound T -
          Real.log ‖Backlund.zetaSurrogate ((11 / 10 : ℂ) + T * I)‖) /
            Real.log (5 / 3)) := by
      convert! h using 1
      norm_num [HIntegral]
    exact h'.trans (mul_le_mul_of_nonneg_left (backlund_circle_normalized_mean_le hT)
      Real.pi_pos.le)
  have hV : |(VIntegral (logDeriv Backlund.zetaSurrogate) (11 / 10) 0 T).im| ≤
      Real.pi / 2 + 3 := by
    have h := abs_im_VIntegral_backlund_logDeriv_le hσ T
    norm_num only [ofReal_div, ofReal_ofNat] at h
    apply h.trans
    apply add_le_add le_rfl
    have hp : 0 < ‖riemannZeta (11 / 10 : ℂ)‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))
    exact (Real.log_le_log hp norm_riemannZeta_eleven_tenths_le).trans
      backlund_circle_log_constants.1
  let G := (VIntegral xiGammaLogDerivative (11 / 10) 0 T).im -
    (HIntegral xiGammaLogDerivative (1 / 2) (11 / 10) T).im
  have hc : |Real.pi * riemannZeta.N T - G| ≤
      Real.pi / 2 + 3 + Real.pi * (Real.log T + 14) := by
    rw [pi_mul_zeta_N_eq_surrogate_gamma_contour hσ ht htop]
    dsimp only [G]
    rw [add_sub_cancel_right]
    exact (abs_sub _ _).trans (add_le_add hV hH)
  have hg := abs_xiGamma_half_contour_sub_mainTerm_le
    (σ := 11 / 10) (by norm_num) ht
  have htriangle := abs_sub_le (Real.pi * riemannZeta.N T) G
    (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)
  have he : Real.pi * (riemannZeta.N T - xiZeroCountingMainTerm T) =
      Real.pi * riemannZeta.N T - (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2) := by
    unfold xiZeroCountingMainTerm
    field_simp
  rw [← he, abs_mul, abs_of_pos Real.pi_pos] at htriangle
  apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
  dsimp only [G] at hc htriangle
  nlinarith [Real.pi_gt_three]

/-- The closed xi count inherits the bound even at ordinates carrying multiple zeros. -/
theorem abs_xiZeroCountingRemainder_le_log_add {T : ℝ} (hT : 10 ≤ T) :
    |xiZeroCountingRemainder T| ≤ Real.log T + 17 := by
  have ht : 0 < T := by linarith
  apply xiZeroCount_error_le_of_regular_heights ht.le
    (hasDerivAt_xiZeroCountingMainTerm ht).continuousAt
    ((Real.continuousAt_log ht.ne').add_const 17)
  intro x hx htop
  exact abs_zeta_N_sub_mainTerm_le_log_add (by linarith) htop

/-- The strict count at every high cutoff has the same bound, including at zero heights. -/
theorem abs_xiStrictZeroCount_sub_mainTerm_le_log_add {T : ℝ} (hT : 10 < T) :
    |(xiStrictZeroCount T : ℝ) - xiZeroCountingMainTerm T| ≤ Real.log T + 17 := by
  have ht : 0 < T := by linarith
  apply xiStrictZeroCount_error_le_of_closed
    (hasDerivAt_xiZeroCountingMainTerm ht).continuousAt
    ((Real.continuousAt_log ht.ne').add_const 17)
  filter_upwards [(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds] with x hx
  exact abs_xiZeroCountingRemainder_le_log_add hx.le

/-- The quantitative envelope needed by the Lehman remainder, proved unconditionally. -/
theorem abs_xiZeroCountingRemainder_le_two_log {T : ℝ}
    (hT : 10 ≤ T) (hlog : 17 ≤ Real.log T) :
    |xiZeroCountingRemainder T| ≤ 2 * Real.log T := by
  have h := abs_xiZeroCountingRemainder_le_log_add hT
  linarith

/-- The same envelope holds uniformly on every tail above a qualifying cutoff. -/
theorem xiZeroCountingRemainder_le_two_log_on_Ici {A : ℝ}
    (hA : 10 ≤ A) (hlog : 17 ≤ Real.log A) :
    ∀ x ∈ Ici A, |xiZeroCountingRemainder x| ≤ 2 * Real.log x := by
  intro x hx
  exact abs_xiZeroCountingRemainder_le_two_log (hA.trans hx)
    (hlog.trans (Real.log_le_log (by linarith) hx))

end

end PrimeFactorUnimodality

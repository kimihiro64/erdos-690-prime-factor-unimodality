import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxZeroBounds
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserIncreasingBand
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeInitial

/-! # The finite box band with height-dependent Rosser damping

Keep the actual ordinate inside the exponential instead of substituting
the worst gap across the whole band. The exponent-one kernel then has
the increasing-window endpoint bound. This is the finite-band component
of Dusart's Rosser method, not a supplied low-height verification.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real intervalIntegral

/-- The unsmoothed height denominator retains the pointwise exponential damping. -/
theorem norm_dusartBox_atom_le_rosser_one (m : ℕ) {h x R : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) {s : ℂ} (hγ : 1 < |s.im|)
    (hβ : s.re ≤ 1 - 1 / (R * Real.log |s.im|)) :
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x‖ ≤
      (x + (m + 3 : ℕ) * h) * logDampedPower (Real.log x / R) 1 |s.im| := by
  have hγ0 : 0 < |s.im| := lt_trans zero_lt_one hγ
  have hs : s ≠ 0 := fun he => (abs_pos.mp hγ0) (by simp [he])
  have hδ : 0 ≤ 1 / (R * Real.log |s.im|) := by
    exact one_div_nonneg.mpr (mul_nonneg hR.le (Real.log_pos hγ).le)
  have hb := norm_dusartBox_paired_atom_le m hh hx hδ hs hβ
  rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx hs] at hb
  have hi : ‖(1 : ℂ) / s‖ ≤ 1 / |s.im| := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hγ0 (abs_im_le_norm s)
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  refine hb.trans ((mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq ?_)
  rw [logDampedPower_eq_rpow_mul hγ0, Real.rpow_neg_one]
  have he : -(1 / (R * Real.log |s.im|)) * Real.log x =
      -(Real.log x / R) / Real.log |s.im| := by ring
  rw [he]
  ring

/-- The actual two-sided finite spectral band has an elementary Rosser bound. -/
theorem norm_dusartBox_band_le_rosser_increasing (m : ℕ) {h x R H T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hH : 20 ≤ H) (hHT : H ≤ T)
    (hT : T ≤ exp (sqrt (Real.log x / R)))
    (hreg : ∀ p ∈ xiHeightBandIndices H T, (riemannXiDivisorZeroValue p).re ≤
      1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    ‖∑ p ∈ xiHeightBandIndices H T, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      (x + (m + 3 : ℕ) * h) * xiRosserIncreasingBandBound (Real.log x / R) H T := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ p ∈ xiHeightBandIndices H T, (x + (m + 3 : ℕ) * h) *
        logDampedPower (Real.log x / R) 1 |(riemannXiDivisorZeroValue p).im| := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := (mem_xiHeightBandIndices H T p).mp hp
      exact norm_dusartBox_atom_le_rosser_one m hh hx hR (by linarith [hp'.1]) (hreg p hp)
    _ = _ * ∑ p ∈ xiHeightBandIndices H T,
        logDampedPower (Real.log x / R) 1 |(riemannXiDivisorZeroValue p).im| := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_xi_band_logDampedPower_one_le_increasing (div_pos (Real.log_pos hx) hR) hH hHT hT)
      (by positivity)

/-- The proved initial region can supply every actual band zero's gap. -/
theorem norm_dusartBox_band_le_initial_rosser_increasing (m : ℕ) {h x H T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T)
    (hT : T ≤ exp (sqrt (Real.log x / 56))) :
    ‖∑ p ∈ xiHeightBandIndices H T, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      (x + (m + 3 : ℕ) * h) * xiRosserIncreasingBandBound (Real.log x / 56) H T := by
  apply norm_dusartBox_band_le_rosser_increasing m hh hx (by norm_num) (by linarith) hHT hT
  intro p hp
  have hp' := (mem_xiHeightBandIndices H T p).mp hp
  linarith [xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero p) (hH.trans hp'.1)]

end

end PrimeFactorUnimodality

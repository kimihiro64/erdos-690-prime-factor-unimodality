import PrimeFactorUnimodality.Helpers.Analytic.TuringXiLogStep
import PrimeFactorUnimodality.Helpers.Analytic.ZetaRealPole

/-! # An explicit logarithmic budget for the full xi step sum

The already proved zeta logarithmic-derivative and Gamma bounds evaluate the
right-half-plane resolvent budget. The complete spectral sum grows at most
logarithmically in height, with explicit constants and no zero-location input.
-/

namespace PrimeFactorUnimodality

open Complex

/-- An explicit xi logarithmic-derivative upper bound on the line of real part three halves. -/
theorem re_logDeriv_riemannXi_three_halves_le (T : ℝ) :
    (logDeriv riemannXi ((3 / 2 : ℂ) + T * I)).re ≤
      (1 / 2 : ℝ) * Real.log (|T| / 2 + 3) + 11 / 2 := by
  let s : ℂ := (3 / 2 : ℂ) + T * I
  have hre : s.re = 3 / 2 := by norm_num [s]
  have him : s.im = T := by simp [s]
  have hs : 1 < s.re := by norm_num [s]
  have hs2 : s.re ≤ 2 := by norm_num [s]
  have hxi := re_neg_logDeriv_riemannZeta_le_xi hs hs2
  have hz := norm_logDeriv_riemannZeta_le_pole_add_one hs
  have hnorm : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have h := re_le_norm (s - 1)
    rw [sub_re, one_re, hre] at h
    linarith
  have hp : (1 / (s - 1)).re ≤ 2 := by
    apply (re_le_norm _).trans
    rw [norm_div, norm_one]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hnorm
    norm_num at h
    simpa only [one_div] using h
  have hreal : (deriv riemannZeta s / riemannZeta s).re ≤ 3 := by
    apply (re_le_norm _).trans
    apply hz.trans
    rw [hre]
    norm_num
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg
    (le_trans (by norm_num : (1 : ℝ) ≤ 3) Real.pi_gt_three.le)
  simp only [neg_div, neg_re] at hxi
  rw [him] at hxi
  change (logDeriv riemannXi s).re ≤ _
  linarith

/-- The entire multiplicity-counted integrated zero budget has explicit logarithmic growth. -/
theorem tsum_turingXiLogStep_le_explicit (T : ℝ) :
    (∑' p, turingXiLogStep T p) ≤ 8 * Real.log (|T| / 2 + 3) + 88 := by
  have h := tsum_turingXiLogStep_le T
  have hx := re_logDeriv_riemannXi_three_halves_le T
  linarith

end PrimeFactorUnimodality

import PrimeFactorUnimodality.Helpers.Analytic.GammaLogBranch
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogShiftLimit
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogTrapezoid

/-! # A uniform Stirling bound for the actual Gamma argument

Apply the logarithmic trapezoid identity to PNT's Euler approximants,
then pass to their already-proved limit. The real factorial normalization
vanishes on taking imaginary parts, so the real Stirling constant need
not be evaluated. The bound `1/(8*Re(z))` is uniform in the height.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter
open scoped Topology

/-- The finite Euler approximant has exactly the logarithmic cell remainder in its phase. -/
theorem logGammaSeq_im_trapezoid {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (logGammaSeq z N).im - ((z - 1 / 2) * log z - z).im -
      (z * (Real.log N : ℂ) + z - (z + N + 1 / 2) * log (z + N)).im =
      -(∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1)).im := by
  have hs := sum_log_add_eq_integral_add_logTrapezoidError hz N
  rw [integral_log_add_ofReal (by positivity : (0 : ℝ) ≤ N) (by simpa using hz)] at hs
  simp only [ofReal_zero, ofReal_natCast, add_zero] at hs
  have he : logGammaSeq z N - ((z - 1 / 2) * log z - z) -
      (z * (Real.log N : ℂ) + z - (z + N + 1 / 2) * log (z + N)) =
      (Real.log N.factorial : ℂ) + N -
        ∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1) := by
    unfold logGammaSeq
    linear_combination -hs
  have h := congrArg Complex.im he
  simpa only [sub_im, add_im, ofReal_im, natCast_im, add_zero, zero_sub] using h

/-- Stirling's phase approximation with an explicit, height-independent error. -/
theorem abs_gammaRightLog_im_sub_stirling_le {z : ℂ} (hz : 0 < z.re) :
    |(gammaRightLog z).im - ((z - 1 / 2) * log z - z).im| ≤ 1 / (8 * z.re) := by
  have hl : Tendsto (fun n : ℕ =>
      (logGammaSeq z n).im - ((z - 1 / 2) * log z - z).im -
        (z * (Real.log n : ℂ) + z - (z + n + 1 / 2) * log (z + n)).im)
      atTop (𝓝 ((gammaRightLog z).im - ((z - 1 / 2) * log z - z).im)) := by
    have hi := continuous_im.continuousAt.tendsto.comp (tendsto_logGammaSeq hz)
    simpa only [sub_zero] using!
      (hi.sub_const _).sub (tendsto_im_log_shift_correction z)
  apply le_of_tendsto hl.abs
  apply Filter.Eventually.of_forall
  intro n
  rw [logGammaSeq_im_trapezoid hz, abs_neg]
  exact (abs_im_le_norm _).trans (norm_sum_logTrapezoidError_le_inv hz n)

/-- The real and imaginary coordinates of the phase bound are completely explicit. -/
theorem abs_gammaRightLog_im_sub_explicit_le {z : ℂ} (hz : 0 < z.re) :
    |(gammaRightLog z).im -
      ((z.re - 1 / 2) * arg z + z.im * Real.log ‖z‖ - z.im)| ≤ 1 / (8 * z.re) := by
  simpa only [sub_im, mul_im, sub_re, div_ofNat_re, div_ofNat_im, one_re, one_im,
    zero_div, sub_zero, log_im, log_re] using abs_gammaRightLog_im_sub_stirling_le hz

end

end PrimeFactorUnimodality

import PrimeFactorUnimodality.Helpers.Analytic.GammaLogBranch
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogStirlingLimit
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogTrapezoid

/-! # Full complex normalization of the logarithmic Gamma remainder

Retain the real factorial term in the Euler approximants. Its Stirling limit
fixes the real normalization as well as the phase. The resulting remainder
is the limit of the exact logarithmic cell errors. The first-order norm
bound establishes normalization, not a high-precision numerical algorithm.
-/

namespace PrimeFactorUnimodality

open Complex Filter
open scoped Topology

/-- The complete finite endpoint, including the real factorial normalization. -/
theorem logGammaSeq_sub_stirling_endpoint {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    logGammaSeq z N - ((z - 1 / 2) * log z - z) -
      ((Real.log N.factorial : ℂ) + N + z * (Real.log N : ℂ) + z -
        (z + N + 1 / 2) * log (z + N)) =
      -∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1) := by
  have hs := sum_log_add_eq_integral_add_logTrapezoidError hz N
  rw [integral_log_add_ofReal (by positivity : (0 : ℝ) ≤ N) (by simpa using hz)] at hs
  simp only [ofReal_zero, ofReal_natCast, add_zero] at hs
  unfold logGammaSeq
  linear_combination -hs

/-- Exact convergence of the cell remainder to the normalized complex Gamma logarithm. -/
theorem tendsto_sum_logTrapezoidError {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1))
      atTop (𝓝 (((z - 1 / 2) * log z - z) +
        ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) - gammaRightLog z)) := by
  have h := (((tendsto_logGammaSeq hz).sub_const ((z - 1 / 2) * log z - z)).sub
    (tendsto_log_stirling_endpoint z)).neg
  have he : -(gammaRightLog z - ((z - 1 / 2) * log z - z) -
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)) =
      ((z - 1 / 2) * log z - z) +
        ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) - gammaRightLog z := by ring
  rw [he] at h
  exact h.congr (fun N => by rw [logGammaSeq_sub_stirling_endpoint hz, neg_neg])

/-- Both amplitude and phase have a proved, explicitly normalized first-order bound. -/
theorem norm_gammaRightLog_sub_stirling_le {z : ℂ} (hz : 0 < z.re) :
    ‖gammaRightLog z - (((z - 1 / 2) * log z - z) +
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ))‖ ≤ 1 / (8 * z.re) := by
  rw [norm_sub_rev]
  exact le_of_tendsto (tendsto_sum_logTrapezoidError hz).norm
    (Filter.Eventually.of_forall (norm_sum_logTrapezoidError_le_inv hz))

end PrimeFactorUnimodality

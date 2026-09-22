import PrimeFactorUnimodality.Helpers.Analytic.BacklundCountingMainTerm

/-! # Gamma phase and actual counting-contour regressions

Exercise the finite and zero-cell identities, canonical Gamma branch,
signed contour heights, the uniform error, and the actual counting result.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter
open scoped Topology

example (z : ℂ) (a : ℝ) : logTrapezoidError z a a = 0 := by
  simp [logTrapezoidError]

example {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, logTrapezoidError z k (k + 1)‖ ≤ 1 / (8 * z.re) :=
  norm_sum_logTrapezoidError_le_inv hz n

example (z : ℂ) : (∑ k ∈ Finset.range 1, log (z + k)) = log z := by simp

example (z : ℂ) : Tendsto (fun n : ℕ =>
    (z * (Real.log n : ℂ) + z - (z + n + 1 / 2) * log (z + n)).im) atTop (𝓝 0) :=
  tendsto_im_log_shift_correction z

example {z : ℂ} (hz : 0 < z.re) : exp (gammaRightLog z) = Gamma z := exp_gammaRightLog hz

example {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt gammaRightLog (digamma z) z := hasDerivAt_gammaRightLog hz

example {x : ℝ} (hx : 0 < x) : (gammaRightLog (x : ℂ)).im = 0 :=
  gammaRightLog_ofReal_im hx

example : gammaRightLog 1 = 0 := by
  apply Complex.ext
  · have h := congrArg norm (exp_gammaRightLog (z := 1) (by norm_num))
    rw [norm_exp, Gamma_one, norm_one, Real.exp_eq_one_iff] at h
    exact h
  · exact gammaRightLog_ofReal_im (x := 1) (by norm_num)

example (T : ℝ) :
    |(gammaRightLog ((5 / 4 : ℂ) - (T : ℂ) / 2 * I)).im -
      ((((5 / 4 : ℂ) - (T : ℂ) / 2 * I) - 1 / 2) *
        log ((5 / 4 : ℂ) - (T : ℂ) / 2 * I) -
          ((5 / 4 : ℂ) - (T : ℂ) / 2 * I)).im| ≤ 1 / 10 := by
  have h := abs_gammaRightLog_im_sub_stirling_le
    (z := (5 / 4 : ℂ) - (T : ℂ) / 2 * I) (by norm_num)
  norm_num at h ⊢
  exact h

example : VIntegral xiGammaLogDerivative 2 0 0 = 0 := by
  simpa using VIntegral_xiGammaLogDerivative_eq (by norm_num : (0 : ℝ) < 2) 0

example : VIntegral xiGammaLogDerivative 2 0 (-3) =
    xiGammaLog (2 + (-3 : ℂ) * I) - xiGammaLog 2 := by
  simpa using VIntegral_xiGammaLogDerivative_eq (by norm_num : (0 : ℝ) < 2) (-3)

example {σ T : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ) (hT : 0 < T) :
    |((VIntegral xiGammaLogDerivative σ 0 T).im -
        (HIntegral xiGammaLogDerivative (1 / 2) σ T).im) -
      (T / 2 * Real.log (T / (2 * Real.pi)) - T / 2)| ≤
        3 * Real.pi / 8 + 27 / 20 :=
  abs_xiGamma_half_contour_sub_mainTerm_le hσ hT

example {σ T r R M : ℝ}
    (hσ : 1 < σ) (hT : 0 < T) (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hseg : σ - 1 / 2 ≤ r)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0)
    (hp : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z + T * I)‖ ≤ M)
    (hm : ∀ z ∈ Metric.sphere (σ : ℂ) R, ‖Backlund.zetaSurrogate (z - T * I)‖ ≤ M) :
    |riemannZeta.N T - xiZeroCountingMainTerm T| ≤
      7 / 8 + 27 / (20 * Real.pi) + Real.log (1 / (σ - 1) + 1) / Real.pi +
        Real.log (M * (1 / (σ - 1) + 1) / T) / Real.log (R / r) :=
  abs_zeta_N_sub_mainTerm_le_circle hσ hT hr hrR hM hseg htop hp hm

end

end PrimeFactorUnimodality.Tests

import PrimeFactorUnimodality.Helpers.Analytic.XiRosserIncreasingBand
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedParameter

/-! # The finite Rosser window at `T=exp(nu*X)`

The exact endpoint evaluation gives the parameter form of Dusart HDR
Lemma 48. The counting-envelope coefficient is the proved `log(t)+17`.
The lower primitive endpoint may be discarded because it is nonnegative;
neither low-height RH nor an exact count at the lower endpoint is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The parameterized one-sided finite-window bound. -/
def xiRosserNuWindowBound (X ν : ℝ) : ℝ :=
  (1 / (2 * π)) * (exp (-X / ν) * ν ^ 2 * (ν * X - Real.log (2 * π))) +
    2 * (ν * X + 17) * exp (-(ν * X) - X / ν)

/-- Dropping the nonnegative lower primitive only enlarges the closed window bound. -/
theorem xiRosserIncreasingBound_le_endpoint {a u v : ℝ}
    (ha : 0 < a) (hu : 10 ≤ u) (huv : u ≤ v) :
    xiRosserIncreasingBound a u v ≤
      (1 / (2 * π)) * logDampedWindowPrimitive a (2 * π) v +
        2 * (Real.log v + 17) * logDampedPower a 1 v := by
  have hb : 0 < 2 * π := by positivity
  have hbu : 2 * π ≤ u := by linarith [Real.pi_lt_four]
  unfold xiRosserIncreasingBound
  split_ifs
  · exact add_le_add (mul_le_mul_of_nonneg_left
      (sub_le_self _ (logDampedWindowPrimitive_nonneg ha hb hbu)) (by positivity)) le_rfl
  · have hl : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
    exact add_nonneg
      (mul_nonneg (by positivity) (logDampedWindowPrimitive_nonneg ha hb (hbu.trans huv)))
      (mul_nonneg (by linarith) (logDampedPower_pos _ _ _).le)

/-- The finite closed majorant reduces to the exact exponential parameter expression. -/
theorem xiRosserIncreasingBound_le_nu {X ν u : ℝ}
    (hX : 0 < X) (hν : 0 < ν) (hu : 10 ≤ u) (huv : u ≤ exp (ν * X)) :
    xiRosserIncreasingBound (X ^ 2) u (exp (ν * X)) ≤ xiRosserNuWindowBound X ν := by
  have he := xiRosserIncreasingBound_le_endpoint (sq_pos_of_pos hX) hu huv
  simpa only [xiRosserNuWindowBound, logDampedWindowPrimitive_exp hX hν,
    logDampedPower_nu hX hν, log_exp, neg_mul, one_mul] using he

/-- The scalar expression is nonnegative whenever its cutoff reaches height ten. -/
theorem xiRosserNuWindowBound_nonneg {X ν : ℝ}
    (hX : 0 < X) (hν : 0 < ν) (hT : 10 ≤ exp (ν * X)) :
    0 ≤ xiRosserNuWindowBound X ν := by
  simpa using xiRosserIncreasingBound_le_nu hX hν hT le_rfl

/-- The actual positive-height zero sum has the parameterized finite-window bound. -/
theorem sum_xi_logDampedPower_one_le_nu {X ν u : ℝ}
    (hX : 0 < X) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hu : 10 ≤ u) (huv : u ≤ exp (ν * X)) :
    (∑ p ∈ xiHeightWindowIndices u (exp (ν * X)),
      logDampedPower (X ^ 2) 1 (riemannXiDivisorZeroValue p).im) ≤ xiRosserNuWindowBound X ν := by
  have hturn : exp (ν * X) ≤ exp (sqrt (X ^ 2)) := by
    apply exp_le_exp.mpr
    rw [sqrt_sq hX.le]
    nlinarith
  exact (sum_xi_logDampedPower_one_le_increasing (sq_pos_of_pos hX) hu huv hturn).trans
    (xiRosserIncreasingBound_le_nu hX hν hu huv)

/-- The two-sided band bound inherits twice the one-sided parameter expression. -/
theorem xiRosserIncreasingBandBound_le_nu {X ν H : ℝ}
    (hX : 0 < X) (hν : 0 < ν) (hH : 20 ≤ H) (hHT : H ≤ exp (ν * X)) :
    xiRosserIncreasingBandBound (X ^ 2) H (exp (ν * X)) ≤ 2 * xiRosserNuWindowBound X ν := by
  unfold xiRosserIncreasingBandBound
  split_ifs
  · exact mul_le_mul_of_nonneg_left
      (xiRosserIncreasingBound_le_nu hX hν (by linarith) (by linarith)) (by norm_num)
  · exact mul_nonneg (by norm_num) (xiRosserNuWindowBound_nonneg hX hν (by linarith))

end

end PrimeFactorUnimodality

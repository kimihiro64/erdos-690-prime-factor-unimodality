import PrimeFactorUnimodality.Helpers.Analytic.XiRosserSymmetry
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedSharpTail

/-! # The complete Rosser tail with the sharper density coefficient

The elementary upper primitive supplies the coefficient in Dusart HDR
Lemma 49. The reciprocal correction is bounded separately. The existing
whole-tail theorem retains both signs, all cutoff multiplicities, and
the boundary term for our proved counting envelope `log(t)+17`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open MeasureTheory Real Set

/-- The sharper two-sided tail bound at an exponential cutoff. -/
def xiRosserSharpTailBound (X m ν : ℝ) : ℝ :=
  2 * ((1 / (2 * π)) *
      (exp (-m * (ν * X) - X / ν) * (ν ^ 2 / (m * ν ^ 2 - 1)) *
        (ν * X + 1 / m - Real.log (2 * π))) +
    exp (-(m + 1) * (ν * X) - X / ν) / (m + 1 - 1 / ν ^ 2) +
    2 * (ν * X + 17) * exp (-(m + 1) * (ν * X) - X / ν))

/-- The strict parameter margin implies the upper primitive's strict turning-height condition. -/
theorem xiRosserSharpTail_gap {X m ν : ℝ}
    (hX : 0 < X) (hmargin : 1 < m * ν ^ 2) :
    X ^ 2 < m * Real.log (exp (ν * X)) ^ 2 := by
  rw [Real.log_exp]
  have hs := mul_lt_mul_of_pos_right hmargin (sq_pos_of_pos hX)
  nlinarith only [hs]

/-- The actual integral budget, including its counting boundary, has the sharp closed bound. -/
theorem xiRosserTailIntegral_boundary_le_sharp {X m ν : ℝ}
    (hX : 0 < X) (hm : 1 ≤ m) (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / m + sqrt (X ^ 2 / m))
    (hT : 10 < exp (ν * X)) :
    2 * (xiRosserTailIntegral (X ^ 2) (m + 1) (exp (ν * X)) +
      2 * (Real.log (exp (ν * X)) + 17) *
        logDampedPower (X ^ 2) (m + 1) (exp (ν * X))) ≤
      xiRosserSharpTailBound X m ν := by
  have hu : 1 < exp (ν * X) := by linarith
  have hmarg : 1 < (m + 1 - 1) * ν ^ 2 := by simpa only [add_sub_cancel_right] using hmargin
  have hp := logDampedPower_nu_exponent_mem hν hmarg
  have hd := integral_logDampedPower_log_tail_le (sq_nonneg X) hm
    (by positivity : 0 < 2 * π) hu (xiRosserSharpTail_gap hX hmargin) hparam
  have he := integral_logDampedPower_div_le_cutoff (sq_nonneg X)
    (by linarith : 2 ≤ m + 1) (by linarith : 0 < m + 1 - 1 / ν ^ 2) hp.2 hu
    (logDampedPower_nu_cutoff hX hν hmarg)
  have hD : (∫ t in Ioi (exp (ν * X)),
      ((1 / (2 * π)) * Real.log (t / (2 * π))) * logDampedPower (X ^ 2) (m + 1) t) ≤
      (1 / (2 * π)) * logDampedTailPrimitive (X ^ 2) m (2 * π) (exp (ν * X)) := by
    calc
      _ = (1 / (2 * π)) * ∫ t in Ioi (exp (ν * X)),
          Real.log (t / (2 * π)) * logDampedPower (X ^ 2) (m + 1) t := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        dsimp only
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  have hi := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hD he) (le_refl
      (2 * (Real.log (exp (ν * X)) + 17) *
        logDampedPower (X ^ 2) (m + 1) (exp (ν * X))))) (by norm_num : (0 : ℝ) ≤ 2)
  rw [logDampedTailPrimitive_exp hX hν, logDampedPower_nu hX hν, Real.log_exp] at hi
  simpa only [xiRosserTailIntegral, xiRosserSharpTailBound,
    logDampedPower_nu hX hν, Real.log_exp] using hi

/-- The full actual zero tail inherits the sharp scalar bound, without a new zero enumeration. -/
theorem xiRosserAbsoluteTail_le_sharp {X m ν : ℝ}
    (hX : 0 < X) (hm : 1 ≤ m) (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / m + sqrt (X ^ 2 / m))
    (hT : 10 < exp (ν * X)) :
    xiRosserAbsoluteTail (X ^ 2) (m + 1) (exp (ν * X)) ≤ xiRosserSharpTailBound X m ν := by
  have hmarg : 1 < (m + 1 - 1) * ν ^ 2 := by simpa only [add_sub_cancel_right] using hmargin
  exact (xiRosserAbsoluteTail_le_integral (sq_nonneg X) (by linarith) hT
    (logDampedPower_nu_turn_le hX hν hmarg)).trans
      (xiRosserTailIntegral_boundary_le_sharp hX hm hν hmargin hparam hT)

/-- The scalar bound is nonnegative on the domain of its actual-tail estimate. -/
theorem xiRosserSharpTailBound_nonneg {X m ν : ℝ}
    (hX : 0 < X) (hm : 1 ≤ m) (hν : 0 < ν) (hmargin : 1 < m * ν ^ 2)
    (hparam : Real.log (2 * π) ≤ 1 / m + sqrt (X ^ 2 / m))
    (hT : 10 < exp (ν * X)) : 0 ≤ xiRosserSharpTailBound X m ν := by
  apply le_trans (show 0 ≤ xiRosserAbsoluteTail (X ^ 2) (m + 1) (exp (ν * X)) from ?_)
    (xiRosserAbsoluteTail_le_sharp hX hm hν hmargin hparam hT)
  exact tsum_nonneg (fun _ => (logDampedPower_pos _ _ _).le)

end

end PrimeFactorUnimodality

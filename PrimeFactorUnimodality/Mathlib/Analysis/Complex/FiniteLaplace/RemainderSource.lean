/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic

/-! # The time-domain source of a pole-subtracted finite Laplace transform

Clamping the source variable to `[0,d]` and subtracting the value at zero
gives a continuous function which vanishes on the negative half-line and
is constant beyond `d`. Exponential damping makes it integrable. Its
bilateral transform is exactly the finite transform minus its pole term.
No differentiability of the extension at either endpoint is required.
-/

namespace Complex

noncomputable section

open MeasureTheory Set

/-- The continuous extension of `f(t)-f(0)` by zero to the left and by `f(d)-f(0)` to the right. -/
def finiteLaplaceRemainderSource (f : ℝ → ℂ) (d t : ℝ) : ℂ :=
  f (max 0 (min d t)) - f 0

/-- Interval continuity suffices for the clamped extension. -/
theorem continuous_finiteLaplaceRemainderSource {f : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) :
    Continuous (finiteLaplaceRemainderSource f d) := by
  exact (hf.comp_continuous (by fun_prop)
    (fun t => ⟨le_max_left _ _, max_le hd (min_le_left _ _)⟩)).sub continuous_const

/-- The source vanishes at and to the left of the origin. -/
theorem finiteLaplaceRemainderSource_of_nonpos (f : ℝ → ℂ) (d : ℝ)
    {t : ℝ} (ht : t ≤ 0) : finiteLaplaceRemainderSource f d t = 0 := by
  simp [finiteLaplaceRemainderSource, max_eq_left ((min_le_right d t).trans ht)]

/-- Inside the source interval, clamping does not alter the argument. -/
theorem finiteLaplaceRemainderSource_of_mem {f : ℝ → ℂ} {d t : ℝ}
    (ht : t ∈ Icc 0 d) : finiteLaplaceRemainderSource f d t = f t - f 0 := by
  simp [finiteLaplaceRemainderSource, min_eq_right ht.2, max_eq_right ht.1]

/-- With a vanishing right endpoint, the source is constant on the entire tail. -/
theorem finiteLaplaceRemainderSource_of_ge {f : ℝ → ℂ} {d t : ℝ}
    (hd : 0 ≤ d) (hfd : f d = 0) (ht : d ≤ t) :
    finiteLaplaceRemainderSource f d t = -f 0 := by
  simp [finiteLaplaceRemainderSource, min_eq_left ht, max_eq_right hd, hfd]

/-- Indicator decomposition suitable for integrability and exact evaluation. -/
theorem exp_mul_finiteLaplaceRemainderSource_eq {f : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hfd : f d = 0) (s : ℂ) :
    (fun t : ℝ => exp (-s * (t : ℂ)) * finiteLaplaceRemainderSource f d t) =
      (Ioc 0 d).indicator (fun t => exp (-s * (t : ℂ)) * f t) -
        (Ioi (0 : ℝ)).indicator (fun t => exp (-s * (t : ℂ)) * f 0) := by
  funext t
  by_cases ht : 0 < t
  · by_cases htd : t ≤ d
    · simp only [Pi.sub_apply, indicator_of_mem (show t ∈ Ioc 0 d from ⟨ht, htd⟩),
        indicator_of_mem (show t ∈ Ioi 0 from ht),
        finiteLaplaceRemainderSource_of_mem ⟨ht.le, htd⟩, mul_sub]
    · have hn : t ∉ Ioc 0 d := fun h => htd h.2
      simp only [Pi.sub_apply, indicator_of_notMem hn,
        indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        finiteLaplaceRemainderSource_of_ge hd hfd (le_of_not_ge htd), mul_neg, zero_sub]
  · have ht₀ : t ≤ 0 := le_of_not_gt ht
    have hn : t ∉ Ioc 0 d := fun h => ht h.1
    simp only [Pi.sub_apply, indicator_of_notMem hn,
      indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
      finiteLaplaceRemainderSource_of_nonpos f d ht₀, mul_zero, sub_zero]

/-- The exponentially damped remainder source is integrable on every positive line. -/
theorem integrable_exp_mul_finiteLaplaceRemainderSource {f : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (hfd : f d = 0)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ => exp (-s * (t : ℂ)) * finiteLaplaceRemainderSource f d t) := by
  rw [exp_mul_finiteLaplaceRemainderSource_eq hd hfd s]
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  have htail := (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0).mul_const (f 0)
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr
    (intervalIntegrable_finiteLaplace hf' s).1).sub
      ((integrable_indicator_iff measurableSet_Ioi).mpr htail)

/-- Exact bilateral Laplace identity, with the pole removed by a continuous source. -/
theorem integral_exp_mul_finiteLaplaceRemainderSource {f : ℝ → ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d)) (hfd : f d = 0)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, exp (-s * (t : ℂ)) * finiteLaplaceRemainderSource f d t) =
      finiteLaplace f d s - f 0 / s := by
  rw [exp_mul_finiteLaplaceRemainderSource_eq hd hfd s]
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  have hhead := (integrable_indicator_iff measurableSet_Ioc).mpr
    (intervalIntegrable_finiteLaplace hf' s).1
  have htail := (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0).mul_const (f 0)
  change (∫ t : ℝ, (Ioc 0 d).indicator (fun u => exp (-s * (u : ℂ)) * f u) t -
    (Ioi (0 : ℝ)).indicator (fun u => exp (-s * (u : ℂ)) * f 0) t) = _
  rw [integral_sub hhead ((integrable_indicator_iff measurableSet_Ioi).mpr htail),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi,
    integral_mul_const, integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0]
  rw [finiteLaplace, intervalIntegral.integral_of_le hd]
  simp [div_eq_mul_inv, mul_comm]

end

end Complex

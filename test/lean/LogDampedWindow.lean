import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedWindow

/-! # Finite logarithmic-window regression tests -/

namespace Real.Tests

open MeasureTheory Set

example {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 1 < t) :
    HasDerivAt (logDampedWindowPrimitive a b)
      (log (t / b) * logDampedPower a 1 t +
        exp (-a / log t) / t * ((2 * log t * (log t - log b) + log t ^ 2) / a)) t :=
  hasDerivAt_logDampedWindowPrimitive ha hb ht

example {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 1 < t) (hbt : b ≤ t) :
    0 ≤ exp (-a / log t) / t * ((2 * log t * (log t - log b) + log t ^ 2) / a) :=
  logDampedWindow_correction_nonneg ha hb ht hbt

example {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : 1 < u) (hbu : b ≤ u) (huv : u ≤ v) :
    (∫ t in Icc u v, log (t / b) * logDampedPower a 1 t) ≤
      logDampedWindowPrimitive a b v - logDampedWindowPrimitive a b u :=
  integral_logDampedPower_one_le_sub ha hb hu hbu huv

example {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hu : 1 < u) (hbu : b ≤ u) (huv : u ≤ v) :
    (∫ t in Icc u v, log (t / b) * logDampedPower a 1 t) ≤
      logDampedWindowPrimitive a b v :=
  integral_logDampedPower_one_le_endpoint ha hb hu hbu huv

example (a b u : ℝ) :
    (∫ t in Icc u u, log (t / b) * logDampedPower a 1 t) = 0 := by simp

example {a b v : ℝ} (ha : 0 < a) (hb : 1 < b) (hbv : b ≤ v) :
    (∫ t in Icc b v, log (t / b) * logDampedPower a 1 t) ≤
      logDampedWindowPrimitive a b v :=
  integral_logDampedPower_one_le_endpoint ha (lt_trans zero_lt_one hb) hb le_rfl hbv

example {X ν b : ℝ} (hX : 0 < X) (hν : 0 < ν) :
    logDampedWindowPrimitive (X ^ 2) b (exp (ν * X)) =
      exp (-X / ν) * ν ^ 2 * (ν * X - log b) :=
  logDampedWindowPrimitive_exp hX hν

-- The exact evaluation does not require the cutoff to exceed the density scale.
example : logDampedWindowPrimitive 1 (exp 2) (exp 1) = -exp (-1) := by
  have h := logDampedWindowPrimitive_exp (X := 1) (ν := 1) (b := exp 2)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

end Real.Tests

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.PrimeLogAbel
import PrimeFactorUnimodality.Helpers.Analytic.SharpMertensKernel

/-!
# A sharp elementary Mertens estimate

For every real x >= 1000 the reciprocal-prime sum has error at most
11/(5 log x) from log(log x) plus the Meissel--Mertens constant.
-/

set_option autoImplicit false

namespace Mertens

open Real MeasureTheory

theorem primeReciprocalSum_error_eq (x : Real) (hx : 2 <= x) :
    primeReciprocalSum x - log (log x) - M = primeLogError x / log x -
      MeasureTheory.integral (volume.restrict (Set.Ioi x))
        (fun t => primeLogError t / (t * log t ^ 2)) := by
  have hp := reciprocalPrimeSum_abel x hx
  have hlog : Not (log x = 0) := ne_of_gt (log_pos (by linarith))
  have hiE : IntervalIntegrable (fun t => primeLogError t / (t * log t ^ 2))
      volume 2 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact (integrable_primeLogError_kernel 2 (by norm_num)).mono_set
      (fun t ht => ht.1)
  have hsplit :
      intervalIntegral (fun t => primeLogSum t / (t * log t ^ 2)) 2 x volume =
        intervalIntegral (fun t => 1 / (t * log t) +
          primeLogError t / (t * log t ^ 2)) 2 x volume := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht1 : 1 < t := by have hh := ht.1; linarith
    have htlog : Not (log t = 0) := ne_of_gt (log_pos ht1)
    unfold primeLogError
    field_simp <;> ring
  rw [hsplit, intervalIntegral.integral_add
    (intervalIntegrable_one_div_mul_log hx) hiE, integral_one_div_mul_log hx] at hp
  have hB : primeLogSum x = log x + primeLogError x := by
    unfold primeLogError
    ring
  rw [hB, add_div, div_self hlog] at hp
  have hM : M = MeasureTheory.integral (volume.restrict (Set.Ioi (2 : Real)))
      (fun t => primeLogError t / (t * log t ^ 2)) + 1 - log (log 2) := rfl
  have hInt := intervalIntegral.integral_interval_add_Ioi
    (integrable_primeLogError_kernel 2 (by norm_num))
    (integrable_primeLogError_kernel x hx)
  rw [hM]
  linarith

theorem primeReciprocalSum_error_abs_le (x : Real) (hx : 1000 <= x) :
    abs (primeReciprocalSum x - log (log x) - M) <= (11 / 5 : Real) / log x := by
  rw [primeReciprocalSum_error_eq x (by linarith)]
  exact primeLogError_tail_abs_le x hx

end Mertens

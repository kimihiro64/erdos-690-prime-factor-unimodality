/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.SharpMertensWeighted

/-!
# The smoothed prime-sum kernel

The kernel u/((u+t) log u) converts the weighted logarithmic prime sum
into reciprocal primes with denominator p+t. Its uniform maximum bound
is the error budget used by the elementary mean comparison.
-/

set_option autoImplicit false

namespace Mertens

open Real

noncomputable def smoothedPrimeKernel (t u : Real) : Real := u / ((u + t) * log u)

noncomputable def smoothedKernelDerivative (t u : Real) : Real :=
  (t * log u - t - u) / ((u + t) ^ 2 * log u ^ 2)

theorem log_gt_three_from_1000 (u : Real) (hu : 1000 <= u) : 3 < log u := by
  have h := LogTables.smooth_log_le (x := u) (a := 0) (b := 3) (c := 0)
    (by linarith) (by norm_num; linarith)
  norm_num at h
  linarith [LogTables.log_3_gt]

theorem smoothedPrimeKernel_hasDerivAt (t u : Real) (ht : 0 < t) (hu : 1000 <= u) :
    HasDerivAt (smoothedPrimeKernel t) (smoothedKernelDerivative t u) u := by
  have hup : 0 < u := by linarith
  have hlog : 0 < log u := log_pos (by linarith)
  have hu0 : Not (u = 0) := hup.ne'
  have hden : Not ((u + t) * log u = 0) := ne_of_gt (mul_pos (by linarith) hlog)
  unfold smoothedPrimeKernel
  convert! (hasDerivAt_id' u).fun_div
    (((hasDerivAt_id' u).add_const t).mul (hasDerivAt_log hu0)) hden using 1
  unfold smoothedKernelDerivative
  dsimp only [Pi.mul_apply]
  field_simp <;> ring

theorem smoothedPrimeKernel_nonneg (t u : Real) (ht : 0 < t) (hu : 1000 <= u) :
    0 <= smoothedPrimeKernel t u := by
  unfold smoothedPrimeKernel
  apply div_nonneg (by linarith)
  exact mul_nonneg (by linarith) (log_nonneg (by linarith))

theorem smoothedPrimeKernel_le (t u : Real) (ht : 4752 <= t) (hu : 1000 <= u) :
    smoothedPrimeKernel t u <= 1 / (log t + 2) := by
  have htpos : 0 < t := by linarith
  have hup : 0 < u := by linarith
  have hw := log_gt_three_from_1000 u hu
  have hwpos : 0 < log u := by linarith
  have htlog := log_gt_three_from_1000 t (by linarith)
  have hloglog : 1 <= log (log u) :=
    (le_log_iff_exp_le hwpos).mpr (by linarith [exp_one_lt_three])
  have hz : 0 < t / u := div_pos htpos hup
  have h := log_le_sub_one_of_pos (mul_pos hwpos hz)
  rw [log_mul hwpos.ne' hz.ne', log_div htpos.ne' hup.ne'] at h
  have hbase : log t + 2 <= log u + log u * (t / u) := by linarith
  have hm := mul_le_mul_of_nonneg_left hbase hup.le
  have heq : u * (log u + log u * (t / u)) = (u + t) * log u := by
    field_simp <;> ring
  rw [heq] at hm
  unfold smoothedPrimeKernel
  calc
    u / ((u + t) * log u) <= u / (u * (log t + 2)) :=
      div_le_div_of_nonneg_left hup.le (by positivity) hm
    _ = 1 / (log t + 2) := by field_simp

end Mertens

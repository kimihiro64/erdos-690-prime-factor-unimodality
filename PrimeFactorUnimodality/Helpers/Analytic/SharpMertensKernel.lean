/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.SharpMertensWeighted

/-!
# Integrals of the weighted prime-sum error

The elementary bounds -2 < E(x) < 1/5 imply a uniform 11/(5 log x)
bound for E(x)/log(x) minus its logarithmic-square integral tail.
-/

set_option autoImplicit false

namespace Mertens

open Real MeasureTheory Filter Topology

theorem integrable_logSquareKernel (c x : Real) (hx : 2 <= x) :
    IntegrableOn (fun t => c / (t * log t ^ 2)) (Set.Ioi x) := by
  conv => arg 1; ext t; rw [<- mul_one_div]
  apply Integrable.const_mul
  refine integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  next =>
    intro t ht
    have ht1 : 1 < t := by have hh := ht; change x <= t at hh; linarith
    have hlog : Not (log t = 0) := ne_of_gt (log_pos ht1)
    have hd : DifferentiableAt Real (fun u => -(Inv.inv (log u))) t := by
      fun_prop (disch := grind)
    convert! hd.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  next =>
    intro t ht
    have htpos : 0 <= t := by change x < t at ht; linarith
    exact div_nonneg (by norm_num) (mul_nonneg htpos (sq_nonneg _))

theorem integral_logSquareKernel (c x : Real) (hx : 2 <= x) :
    MeasureTheory.integral (volume.restrict (Set.Ioi x))
      (fun t => c / (t * log t ^ 2)) = c / log x := by
  convert! integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0)
    (f := fun t => -c / log t) ?_ (integrable_logSquareKernel c x hx) ?_ using 1
  next => grind
  next =>
    intro t ht
    have ht1 : 1 < t := by change x <= t at ht; linarith
    convert! HasDerivAt.fun_div (hasDerivAt_const t (-c))
      (hasDerivAt_log (by linarith : Not (t = 0))) ?_ using 1
    next => grind
    next => exact ne_of_gt (log_pos ht1)
  next =>
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem integrable_primeLogError_kernel (x : Real) (hx : 2 <= x) :
    IntegrableOn (fun t => primeLogError t / (t * log t ^ 2)) (Set.Ioi x) := by
  have hC : 0 < log (4 : Real) + 4 := by positivity
  apply Integrable.mono (integrable_logSquareKernel (log 4 + 4) x hx)
  next =>
    apply Measurable.aestronglyMeasurable
    unfold primeLogError primeLogSum
    fun_prop
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change x < t at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hC]
    gcongr
    exact sum_log_prime_div_eq_log (by linarith : 1 <= t)

theorem primeLogError_integral_bounds (x : Real) (hx : 1000 <= x) :
    And ((-2 : Real) / log x <=
      MeasureTheory.integral (volume.restrict (Set.Ioi x))
        (fun t => primeLogError t / (t * log t ^ 2)))
      (MeasureTheory.integral (volume.restrict (Set.Ioi x))
        (fun t => primeLogError t / (t * log t ^ 2)) <= (1 / 5 : Real) / log x) := by
  have hxi : 2 <= x := by linarith
  have hi := integrable_primeLogError_kernel x hxi
  apply And.intro
  next =>
    rw [<- integral_logSquareKernel (-2) x hxi]
    apply setIntegral_mono_on (integrable_logSquareKernel (-2) x hxi) hi measurableSet_Ioi
    intro t ht
    have ht1000 : 1000 <= t := le_trans hx ht.le
    have hden : 0 <= t * log t ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    exact div_le_div_of_nonneg_right (primeLogError_bounds t ht1000).1.le hden
  next =>
    rw [<- integral_logSquareKernel (1 / 5) x hxi]
    apply setIntegral_mono_on hi (integrable_logSquareKernel (1 / 5) x hxi) measurableSet_Ioi
    intro t ht
    have ht1000 : 1000 <= t := le_trans hx ht.le
    have hden : 0 <= t * log t ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    exact div_le_div_of_nonneg_right (primeLogError_bounds t ht1000).2.le hden

theorem primeLogError_tail_abs_le (x : Real) (hx : 1000 <= x) :
    abs (primeLogError x / log x -
      MeasureTheory.integral (volume.restrict (Set.Ioi x))
        (fun t => primeLogError t / (t * log t ^ 2))) <= (11 / 5 : Real) / log x := by
  have hlog : 0 < log x := log_pos (by linarith)
  have he := primeLogError_bounds x hx
  have ht := primeLogError_integral_bounds x hx
  have hl := (div_le_div_iff_of_pos_right hlog).mpr he.1.le
  have hu := (div_le_div_iff_of_pos_right hlog).mpr he.2.le
  rw [abs_le]
  simp only [div_eq_mul_inv] at hl hu ht
  simp only [div_eq_mul_inv]
  exact And.intro (by linarith [ht.2]) (by linarith [ht.1])

end Mertens

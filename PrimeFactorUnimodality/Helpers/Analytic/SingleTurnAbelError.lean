/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.PrimeLogAbel
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedKernelTurn

/-!
# The signed Abel error for the smoothed prime kernel

Splitting at the single turning point keeps the correct signs for both
bounds -2 < E(u) < 1/5. After the endpoint cancellations the full error
is at least -11/(5 (log t + 2)).
-/

set_option autoImplicit false

namespace Mertens

open Real MeasureTheory

theorem smoothedKernelDerivative_continuousOn (t a b : Real) (ht : 0 < t)
    (ha : 1000 <= a) :
    ContinuousOn (smoothedKernelDerivative t) (Set.Icc a b) := by
  intro u hu
  have hup : 0 < u := by have h := hu.1; linarith
  have hlog : Not (log u = 0) := ne_of_gt (log_pos (by have h := hu.1; linarith))
  have hplus : Not (u + t = 0) := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold smoothedKernelDerivative
  fun_prop (disch := grind)

theorem smoothedKernelDerivative_mul_error_integrable (t a b : Real) (ht : 0 < t)
    (ha : 1000 <= a) :
    IntegrableOn (fun u => smoothedKernelDerivative t u * primeLogError u) (Set.Icc a b) := by
  have hc := smoothedKernelDerivative_continuousOn t a b ht ha
  have hB := integrableOn_mul_sum_Icc primeLogCoefficient (m := 0)
    (a := a) (b := b) (by linarith) hc.integrableOn_Icc
  simp_rw [<- primeLogSum_eq_sum_Icc] at hB
  have hlog : ContinuousOn log (Set.Icc a b) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_log (by have hh := hu.1; linarith)
  have hL : IntegrableOn (fun u => smoothedKernelDerivative t u * log u) (Set.Icc a b) volume :=
    (hc.mul hlog).integrableOn_Icc
  have heq : (fun u => smoothedKernelDerivative t u * primeLogError u) =
      (fun u => smoothedKernelDerivative t u * primeLogSum u -
        smoothedKernelDerivative t u * log u) := by
    funext u
    unfold primeLogError
    ring
  rw [heq]
  exact hB.sub hL

theorem smoothedKernelDerivative_integral (t a b : Real) (ht : 0 < t)
    (ha : 1000 <= a) (hab : a <= b) :
    intervalIntegral (smoothedKernelDerivative t) a b volume =
      smoothedPrimeKernel t b - smoothedPrimeKernel t a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  next =>
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact smoothedPrimeKernel_hasDerivAt t u ht (ha.trans hu.1)
  next =>
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (smoothedKernelDerivative_continuousOn t a b ht ha).integrableOn_Icc

theorem smoothedPrimeKernel_error_lower (t X : Real) (ht : 4752 <= t) (hX : 1000 <= X) :
    -(11 / 5 : Real) / (log t + 2) <=
      smoothedPrimeKernel t X * primeLogError X -
        smoothedPrimeKernel t 1000 * primeLogError 1000 -
          intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogError u)
            1000 X volume := by
  have htpos : 0 < t := by linarith
  cases smoothedKernel_turn t X ht hX with
  | intro m hm =>
    have hmY : 1000 <= m := hm.1
    have hmX : m <= X := hm.2.1
    have hpos := hm.2.2.1
    have hneg := hm.2.2.2
    have hiLeft : IntervalIntegrable
        (fun u => smoothedKernelDerivative t u * primeLogError u) volume 1000 m :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hmY).mpr
        (smoothedKernelDerivative_mul_error_integrable t 1000 m htpos (by norm_num))
    have hiRight : IntervalIntegrable
        (fun u => smoothedKernelDerivative t u * primeLogError u) volume m X :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hmX).mpr
        (smoothedKernelDerivative_mul_error_integrable t m X htpos hmY)
    have hiConstLeft : IntegrableOn (fun u => smoothedKernelDerivative t u * (1 / 5 : Real))
        (Set.Icc 1000 m) volume :=
      (smoothedKernelDerivative_continuousOn t 1000 m htpos (by norm_num)).integrableOn_Icc.mul_const _
    have hLeft :
        intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogError u) 1000 m volume <=
          (smoothedPrimeKernel t m - smoothedPrimeKernel t 1000) * (1 / 5 : Real) := by
      calc
        _ = MeasureTheory.integral (volume.restrict (Set.Ioc 1000 m))
            (fun u => smoothedKernelDerivative t u * primeLogError u) :=
          intervalIntegral.integral_of_le hmY
        _ <= MeasureTheory.integral (volume.restrict (Set.Ioc 1000 m))
            (fun u => smoothedKernelDerivative t u * (1 / 5 : Real)) := by
          apply setIntegral_mono_on
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le hmY).mp hiLeft)
            (hiConstLeft.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
          intro u hu
          exact mul_le_mul_of_nonneg_left (primeLogError_bounds u hu.1.le).2.le
            (hpos u hu.1.le hu.2)
        _ = intervalIntegral (fun u => smoothedKernelDerivative t u * (1 / 5 : Real)) 1000 m volume :=
          (intervalIntegral.integral_of_le hmY).symm
        _ = _ := by
          rw [intervalIntegral.integral_mul_const,
            smoothedKernelDerivative_integral t 1000 m htpos (by norm_num) hmY]
    have hiConstRight : IntegrableOn (fun u => smoothedKernelDerivative t u * (-2 : Real))
        (Set.Icc m X) volume :=
      (smoothedKernelDerivative_continuousOn t m X htpos hmY).integrableOn_Icc.mul_const _
    have hRight :
        intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogError u) m X volume <=
          (smoothedPrimeKernel t X - smoothedPrimeKernel t m) * (-2 : Real) := by
      calc
        _ = MeasureTheory.integral (volume.restrict (Set.Ioc m X))
            (fun u => smoothedKernelDerivative t u * primeLogError u) :=
          intervalIntegral.integral_of_le hmX
        _ <= MeasureTheory.integral (volume.restrict (Set.Ioc m X))
            (fun u => smoothedKernelDerivative t u * (-2 : Real)) := by
          apply setIntegral_mono_on
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le hmX).mp hiRight)
            (hiConstRight.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
          intro u hu
          exact mul_le_mul_of_nonpos_left (primeLogError_bounds u (hmY.trans hu.1.le)).1.le
            (hneg u hu.1 hu.2)
        _ = intervalIntegral (fun u => smoothedKernelDerivative t u * (-2 : Real)) m X volume :=
          (intervalIntegral.integral_of_le hmX).symm
        _ = _ := by
          rw [intervalIntegral.integral_mul_const,
            smoothedKernelDerivative_integral t m X htpos hmY hmX]
    have hsum := intervalIntegral.integral_add_adjacent_intervals hiLeft hiRight
    have hEnd := mul_le_mul_of_nonneg_left (primeLogError_bounds X hX).1.le
      (smoothedPrimeKernel_nonneg t X htpos hX)
    have hStart := mul_le_mul_of_nonneg_left (primeLogError_bounds 1000 (by norm_num)).2.le
      (smoothedPrimeKernel_nonneg t 1000 htpos (by norm_num))
    have hMax := smoothedPrimeKernel_le t m ht hmY
    have hBound : -((11 / 5 : Real) * smoothedPrimeKernel t m) <=
        smoothedPrimeKernel t X * primeLogError X -
          smoothedPrimeKernel t 1000 * primeLogError 1000 -
            intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogError u) 1000 X volume := by
      linarith only [hLeft, hRight, hsum, hEnd, hStart]
    have hScaled := mul_le_mul_of_nonneg_left hMax (show (0 : Real) <= 11 / 5 by norm_num)
    have hFinal := (neg_le_neg hScaled).trans hBound
    convert hFinal using 1 <;> ring

end Mertens

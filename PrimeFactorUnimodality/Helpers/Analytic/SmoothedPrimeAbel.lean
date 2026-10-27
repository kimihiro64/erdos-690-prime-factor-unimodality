import PrimeFactorUnimodality.Helpers.Analytic.SingleTurnAbelError
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedMainIntegral

set_option autoImplicit false

/-! # An elementary lower bound for smoothed prime reciprocals

Finite Abel summation and the single-turn error estimate give a uniform
bound with real endpoints, without a zero-verification hypothesis.
-/

namespace Mertens

open Real Finset MeasureTheory

theorem weightedPrimeLogSum_sub_abel (g : Real -> Real) (a b : Real)
    (ha : 0 <= a) (hab : a <= b)
    (hd : forall u, Set.Icc a b u -> DifferentiableAt Real g u)
    (hi : IntegrableOn (deriv g) (Set.Icc a b)) :
    weightedPrimeLogSum g b - weightedPrimeLogSum g a =
      g b * primeLogSum b - g a * primeLogSum a -
        MeasureTheory.integral (volume.restrict (Set.Ioc a b))
          (fun u => deriv g u * primeLogSum u) := by
  have hsub : Finset.Icc 0 (Nat.floor a) <= Finset.Icc 0 (Nat.floor b) := by
    intro n hn
    exact Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp hn).1
      ((Finset.mem_Icc.mp hn).2.trans (Nat.floor_le_floor hab)))
  have hdiff : Finset.Icc 0 (Nat.floor b) \ Finset.Icc 0 (Nat.floor a) =
      Finset.Ioc (Nat.floor a) (Nat.floor b) := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsplit := Finset.sum_sdiff_eq_sub
    (f := fun p : Nat => g p * primeLogCoefficient p) hsub
  rw [hdiff] at hsplit
  have h := sum_mul_eq_sub_sub_integral_mul primeLogCoefficient ha hab hd hi
  rw [hsplit] at h
  simp_rw [<- primeLogSum_eq_sum_Icc] at h
  exact h

noncomputable def smoothedPrimeSum (t x : Real) : Real :=
  (Finset.Icc 0 (Nat.floor x)).sum (fun p => if p.Prime then 1 / ((p : Real) + t) else 0)

theorem smoothedPrimeSum_eq_weighted (t x : Real) (ht : 0 < t) :
    smoothedPrimeSum t x = weightedPrimeLogSum (smoothedPrimeKernel t) x := by
  unfold smoothedPrimeSum weightedPrimeLogSum
  apply sum_congr rfl
  intro p hp
  unfold primeLogCoefficient
  split_ifs with hprime
  case pos =>
    have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hprime.ne_zero
    have hlog : Not (log (p : Real) = 0) := ne_of_gt (log_pos (by exact_mod_cast hprime.one_lt))
    have hplus : Not ((p : Real) + t = 0) := by
      have hn : (0 : Real) <= p := Nat.cast_nonneg p
      linarith
    unfold smoothedPrimeKernel
    field_simp <;> ring
  case neg => ring

theorem smoothedPrimeSum_nonneg (t x : Real) (ht : 0 < t) :
    0 <= smoothedPrimeSum t x := by
  unfold smoothedPrimeSum
  apply sum_nonneg
  intro p hp
  split_ifs <;> positivity

theorem smoothedPrimeSum_sub_abel (t X : Real) (ht : 0 < t) (hX : 1000 <= X) :
    smoothedPrimeSum t X - smoothedPrimeSum t 1000 =
      smoothedPrimeKernel t X * primeLogSum X - smoothedPrimeKernel t 1000 * primeLogSum 1000 -
        intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogSum u) 1000 X volume := by
  have hderiv (u : Real) (hu : Set.Icc 1000 X u) :
      deriv (smoothedPrimeKernel t) u = smoothedKernelDerivative t u :=
    (smoothedPrimeKernel_hasDerivAt t u ht hu.1).deriv
  have hi : IntegrableOn (deriv (smoothedPrimeKernel t)) (Set.Icc 1000 X) :=
    (smoothedKernelDerivative_continuousOn t 1000 X ht (by norm_num)).integrableOn_Icc.congr_fun
      (fun u hu => (hderiv u hu).symm) measurableSet_Icc
  have h := weightedPrimeLogSum_sub_abel (smoothedPrimeKernel t) 1000 X (by norm_num) hX
    (fun u hu => (smoothedPrimeKernel_hasDerivAt t u ht hu.1).differentiableAt) hi
  rw [<- smoothedPrimeSum_eq_weighted t X ht, <- smoothedPrimeSum_eq_weighted t 1000 ht] at h
  have hInt : MeasureTheory.integral (volume.restrict (Set.Ioc 1000 X))
      (fun u => deriv (smoothedPrimeKernel t) u * primeLogSum u) =
      intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogSum u) 1000 X volume := by
    rw [intervalIntegral.integral_of_le hX]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only
    rw [hderiv u (And.intro hu.1.le hu.2)]
  rw [hInt] at h
  exact h


theorem smoothedPrimeSum_integral_lower (t X : Real) (ht : 4752 <= t) (hX : 1000 <= X) :
    intervalIntegral (fun u => 1 / ((u + t) * log u)) 1000 X volume -
      (11 / 5 : Real) / (log t + 2) <= smoothedPrimeSum t X := by
  have htpos : 0 < t := by linarith
  have hcD := smoothedKernelDerivative_continuousOn t 1000 X htpos (by norm_num)
  have hcLog : ContinuousOn log (Set.Icc 1000 X) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_log (by have hh := hu.1; linarith)
  have hcMain : ContinuousOn (fun u => 1 / ((u + t) * log u)) (Set.Icc 1000 X) := by
    intro u hu
    have hup : 0 < u := by have hh := hu.1; linarith
    have hlog0 : Not (log u = 0) := ne_of_gt (log_pos (by have hh := hu.1; linarith))
    have hplus0 : Not (u + t = 0) := by linarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := grind)
  have hiDlog : IntervalIntegrable (fun u => smoothedKernelDerivative t u * log u) volume 1000 X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr (hcD.mul hcLog).integrableOn_Icc
  have hiMain : IntervalIntegrable (fun u => 1 / ((u + t) * log u)) volume 1000 X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr hcMain.integrableOn_Icc
  have hiDE : IntervalIntegrable (fun u => smoothedKernelDerivative t u * primeLogError u)
      volume 1000 X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
      (smoothedKernelDerivative_mul_error_integrable t 1000 X htpos (by norm_num))
  have hProd :
      intervalIntegral (fun u => smoothedKernelDerivative t u * log u +
        1 / ((u + t) * log u)) 1000 X volume =
          smoothedPrimeKernel t X * log X - smoothedPrimeKernel t 1000 * log 1000 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u => smoothedPrimeKernel t u * log u)
    next =>
      intro u hu
      rw [Set.uIcc_of_le hX] at hu
      have hup : 0 < u := by have hh := hu.1; linarith
      have hu0 : Not (u = 0) := hup.ne'
      have hlog0 : Not (log u = 0) := ne_of_gt (log_pos (by have hh := hu.1; linarith))
      have hplus0 : Not (u + t = 0) := by linarith
      convert! (smoothedPrimeKernel_hasDerivAt t u htpos hu.1).mul
        (hasDerivAt_log hu0) using 1
      unfold smoothedPrimeKernel
      field_simp <;> ring
    next => exact hiDlog.add hiMain
  rw [intervalIntegral.integral_add hiDlog hiMain] at hProd
  have hIntB :
      intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogSum u) 1000 X volume =
        intervalIntegral (fun u => smoothedKernelDerivative t u * log u) 1000 X volume +
          intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogError u) 1000 X volume := by
    rw [<- intervalIntegral.integral_add hiDlog hiDE]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    unfold primeLogError
    ring
  have hBX : primeLogSum X = log X + primeLogError X := by unfold primeLogError; ring
  have hBY : primeLogSum 1000 = log 1000 + primeLogError 1000 := by unfold primeLogError; ring
  have hab := smoothedPrimeSum_sub_abel t X htpos hX
  rw [hBX, hBY, hIntB] at hab
  have hS := smoothedPrimeSum_nonneg t 1000 htpos
  have herr := smoothedPrimeKernel_error_lower t X ht hX
  have hIdentity : smoothedPrimeSum t X =
      smoothedPrimeSum t 1000 +
        intervalIntegral (fun u => 1 / ((u + t) * log u)) 1000 X volume +
          (smoothedPrimeKernel t X * primeLogError X -
            smoothedPrimeKernel t 1000 * primeLogError 1000 -
              intervalIntegral (fun u => smoothedKernelDerivative t u * primeLogError u)
                1000 X volume) := by
    linear_combination hab - hProd
  rw [neg_div] at herr
  rw [hIdentity]
  linarith only [hS, herr]

theorem smoothedPrimeSum_lower (t X : Real) (ht : 4752 <= t) (htX : t <= X) :
    log (log X) - log (log t) - log (1 + 1000 / t) / log t -
      (11 / 5 : Real) / (log t + 2) <= smoothedPrimeSum t X := by
  have hMain := smoothedMainIntegral_lower t X ht htX
  have hAbel := smoothedPrimeSum_integral_lower t X ht (by linarith)
  exact (sub_le_sub_right hMain ((11 / 5 : Real) / (log t + 2))).trans hAbel
end Mertens

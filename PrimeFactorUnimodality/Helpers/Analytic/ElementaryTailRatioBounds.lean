import PrimeFactorUnimodality.Helpers.Analytic.AnalyticDensityWeights
import PrimeFactorUnimodality.Helpers.Analytic.ClassificationAscentScalars
import PrimeFactorUnimodality.Helpers.Analytic.SharpThetaBounds

set_option autoImplicit false

/-! # Analytic density-ratio inputs for the elementary tail -/

namespace Mertens

open Real Finset

theorem primeShiftedReciprocalSum_mono : Monotone primeShiftedReciprocalSum := by
  intro x y hxy
  unfold primeShiftedReciprocalSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  next =>
    intro p hp
    exact Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp hp).1
      ((Finset.mem_Icc.mp hp).2.trans (Nat.floor_le_floor hxy)))
  next =>
    intro p hp hnot
    split_ifs with hprime
    next =>
      have hp2 : (2 : Real) <= p := by exact_mod_cast hprime.two_le
      exact div_nonneg (by norm_num) (by linarith)
    next => exact le_rfl

end Mertens

namespace PrimeFactorUnimodality

open Real

theorem log_add_four_div_mono {a b : Real} (ha : 4 <= a) (hab : a <= b) :
    log a + 4 / a <= log b + 4 / b := by
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have h := log_tangent_lower b a hbpos hapos
  have ha0 : Not (a = 0) := hapos.ne'
  have hb0 : Not (b = 0) := hbpos.ne'
  have heq : (1 - a / b + 4 / b - 4 / a) * (a * b) = (b - a) * (a - 4) := by
    field_simp
    <;> ring
  have hmul : 0 <= (b - a) * (a - 4) := mul_nonneg (by linarith) (by linarith)
  have hnonneg : 0 <= 1 - a / b + 4 / b - 4 / a :=
    le_of_mul_le_mul_right (by rw [zero_mul, heq]; exact hmul) (mul_pos hapos hbpos)
  linarith

theorem elementary_tail_mean_lower (r : Real) (P b : Nat) (hr : 38000 <= r)
    (hP : (2 : Nat)^30 <= P)
    (hL : classificationEll r <= log (P : Real)) (hPb : P < b) :
    r < tiltedPrimeWeightMean (primesBelow b) (classificationT r) := by
  have he := classificationEll_lower r hr
  have ht := classificationT_lower r hr
  have htpos : 0 < classificationT r := by linarith
  have hPr : (1073741824 : Real) <= P := by exact_mod_cast hP
  have hPpos : (0 : Real) < P := by linarith
  have hUpos : 0 < log (5 * classificationEll r) := log_pos (by linarith)
  have htupper : classificationT r < 2 * classificationEll r := by
    unfold classificationT
    linarith
  have hLogP := Chebyshev.log_le_seven_thousandths_mul P (by linarith)
  have htP : classificationT r <= (P : Real) := by linarith
  have hs := Mertens.smoothedPrimeSum_lower (classificationT r) P (by linarith) htP
  have hloglog : log (classificationEll r) <= log (log (P : Real)) :=
    log_le_log (by linarith) hL
  have hB : classificationDescentBracket r <= Mertens.smoothedPrimeSum (classificationT r) P := by
    unfold classificationDescentBracket
    linarith
  have hmul := mul_le_mul_of_nonneg_left hB htpos.le
  have hscalar := classification_descent_scalar r hr
  have hmean := smoothedPrimeSum_mul_le_tiltedMean (classificationT r) P b htpos
    (Nat.cast_nonneg P) (Nat.cast_lt.mpr hPb)
  nlinarith only [hmul, hscalar, hmean, hr]

theorem elementary_tail_ascent_weight_bound (r : Real) (P b g : Nat)
    (hr : 38000 <= r) (hP : (2 : Nat)^30 <= P) (hb : 1 <= b)
    (hbP : b <= 400 * P)
    (hM : log (400 * (P : Real)) < classificationMStar r)
    (hg : (g : Real) + 1 < 1.09 * log (400 * (P : Real)) + 2) :
    ((g + 1 : Nat) : Real) * primeWeightSumBelow b < r := by
  have hPr : (1073741824 : Real) <= P := by exact_mod_cast hP
  have hMlo : 8.78 < log (400 * (P : Real)) :=
    log_6535_gt.trans (log_lt_log (by norm_num) (by linarith))
  have hupper := Mertens.primeShiftedReciprocalSum_upper_four (400 * (P : Real)) (by linarith)
  have hpred : (((b - 1 : Nat) : Real)) <= 400 * (P : Real) := by
    exact_mod_cast (Nat.sub_le b 1).trans hbP
  have hweights : primeWeightSumBelow b <
      log (classificationMStar r) + 1.1 + 4 / classificationMStar r := by
    rw [primeWeightSumBelow_eq_shifted b hb]
    have hmono := Mertens.primeShiftedReciprocalSum_mono hpred
    have hF := log_add_four_div_mono (by linarith : 4 <= log (400 * (P : Real))) hM.le
    linarith
  have hcoef : (g : Real) + 1 < 1.09 * classificationMStar r + 2 := by linarith
  have hw0 := primeWeightSumBelow_nonneg b
  have hc0 : 0 <= 1.09 * classificationMStar r + 2 := by linarith
  have hprod := mul_le_mul hcoef.le hweights.le hw0 hc0
  have hscalar := classification_ascent_scalar r hr
  norm_num only [Nat.cast_add, Nat.cast_one]
  exact hprod.trans_lt hscalar

end PrimeFactorUnimodality

import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogBernoulli
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ShiftedBound
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ShiftedRecursion

/-! Endpoint cells, improper boundary signs and height exponents for complex shifts. -/

open Complex MeasureTheory Polynomial Set

example {z : ℂ} (hz : 0 < z.re) :
    logTrapezoidError z 0 1 = (1 / 12 : ℂ) * ((z + 1)⁻¹ - z⁻¹) +
      ∫ x : ℝ in 0..1, (bernoulliPeriodic 2 x : ℂ) * (z + (x : ℂ))⁻¹ ^ 2 := by
  simpa using logTrapezoidError_nat_eq_bernoulli_two hz 0

example {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, (bernoulliPeriodic 1 x : ℂ) * (z + (x : ℂ))⁻¹ ^ 2) =
      -(1 / 12 : ℂ) * z⁻¹ ^ 2 +
        2 * ∫ x : ℝ in Ioi 0, (bernoulliPeriodic 2 x : ℂ) * (z + (x : ℂ))⁻¹ ^ 3 := by
  have h := bernoulliPeriodic_inv_pow_tail_recursion (k := 1) (p := 2) (by omega) (by omega) hz
  norm_num [bernoulliNormalizedReal_zero, _root_.bernoulli_two] at h
  simpa only [inv_pow, neg_mul] using h

example {z : ℂ} (hz : 0 < z.re) (him : 0 < |z.im|) :
    (∫ x : ℝ in Ioi 0, ‖(z + (x : ℂ))⁻¹ ^ 2‖) ≤ 2 * |z.im|⁻¹ := by
  convert integral_norm_inv_pow_add_ofReal_le_im (p := 2) (by omega) hz him using 1
  norm_num [Real.rpow_neg_one]

example {z : ℂ} (hz : 0 < z.re) (him : 0 < |z.im|) :
    (∫ x : ℝ in Ioi 0, ‖(z + (x : ℂ))⁻¹ ^ 4‖) ≤
      (4 / 3 : ℝ) * |z.im| ^ (-3 : ℝ) := by
  convert integral_norm_inv_pow_add_ofReal_le_im (p := 4) (by omega) hz him using 1
  norm_num

example (z : ℂ) (k : ℕ) :
    (∫ x : ℝ in 0..0, (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ 2) = 0 := by
  simp

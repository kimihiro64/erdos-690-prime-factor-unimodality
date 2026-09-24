/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogTrapezoid
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ShiftedCells

/-! # The logarithmic trapezoid error as a Bernoulli remainder

One integration by parts identifies the cell error with the first Bernoulli
profile times the logarithmic derivative. A second step gives the exact
`1/12` boundary correction and the integrable second Bernoulli remainder.
-/

open MeasureTheory Polynomial Set

namespace Complex

/-- The first Bernoulli profile gives the exact logarithmic unit-cell error. -/
theorem logTrapezoidError_eq_bernoulli_one {z : ℂ} (hz : 0 < z.re) :
    logTrapezoidError z 0 1 =
      ∫ u : ℝ in 0..1, (bernoulliNormalizedReal 1 u : ℂ) * (z + (u : ℂ))⁻¹ := by
  have hzero (u : ℝ) : bernoulliNormalizedReal 0 u = 1 := by
    simp [bernoulliNormalizedReal, bernoulliNormalized, Polynomial.bernoulli_zero]
  have hone (u : ℝ) : bernoulliNormalizedReal 1 u = u - 1 / 2 := by
    norm_num [bernoulliNormalizedReal, bernoulliNormalized, Polynomial.bernoulli_one]
  have hf (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v : ℝ => log (z + (v : ℂ))) (z + (u : ℂ))⁻¹ u := by
    have hu0 : 0 ≤ u := (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ hu).1
    have hr : 0 < (z + (u : ℂ)).re := by simp only [add_re, ofReal_re]; linarith
    convert! ((hasDerivAt_log (Or.inl hr)).comp (u : ℂ)
      ((hasDerivAt_id (u : ℂ)).const_add z)).comp_ofReal using 1
    simp
  have hq (u : ℝ) (_hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v : ℝ => (bernoulliNormalizedReal 1 v : ℂ)) 1 u := by
    simpa [hzero] using (hasDerivAt_bernoulliNormalizedReal 0 u).ofReal_comp
  have hi : IntervalIntegrable (fun u : ℝ => (z + (u : ℂ))⁻¹) volume 0 1 := by
    simpa only [pow_one] using ((continuousOn_inv_pow_add_ofReal 1 hz).mono
      (show Icc (0 : ℝ) 1 ⊆ Ici 0 from fun _ hu => hu.1)).intervalIntegrable_of_Icc
        (by norm_num : (0 : ℝ) ≤ 1)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hq hi intervalIntegrable_const
  have h0 : (bernoulliNormalizedReal 1 0 : ℂ) = -(1 / 2) := by rw [hone]; norm_num
  have h1 : (bernoulliNormalizedReal 1 1 : ℂ) = 1 / 2 := by rw [hone]; norm_num
  simp only [mul_one, ofReal_zero, ofReal_one, add_zero, h0, h1] at h
  calc
    _ = ∫ u : ℝ in 0..1, (z + (u : ℂ))⁻¹ * (bernoulliNormalizedReal 1 u : ℂ) := by
      simp only [logTrapezoidError, ofReal_zero, ofReal_one, sub_zero, add_zero]
      linear_combination -h
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u _
      exact mul_comm _ _

/-- The second Bernoulli profile includes the exact first Stirling coefficient. -/
theorem logTrapezoidError_eq_bernoulli_two {z : ℂ} (hz : 0 < z.re) :
    logTrapezoidError z 0 1 = (1 / 12 : ℂ) * ((z + 1)⁻¹ - z⁻¹) +
      ∫ u : ℝ in 0..1, (bernoulliNormalizedReal 2 u : ℂ) * (z + (u : ℂ))⁻¹ ^ 2 := by
  rw [logTrapezoidError_eq_bernoulli_one hz]
  have hb : (bernoulliNormalizedReal 2 0 : ℂ) = 1 / 12 := by
    norm_num [bernoulliNormalizedReal_zero, _root_.bernoulli_two]
  simpa only [Nat.reduceAdd, pow_one, Nat.cast_one, one_mul, hb] using
    bernoulliNormalizedReal_inv_pow_cell (k := 1) (by omega) 1 hz

/-- Translate the normalized logarithmic cell without losing the complex shift. -/
theorem logTrapezoidError_nat_eq_shift (z : ℂ) (N : ℕ) :
    logTrapezoidError z N ((N : ℝ) + 1) = logTrapezoidError (z + N) 0 1 := by
  have hi := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ => log (z + (x : ℂ))) (N : ℝ)
  simp only [add_zero, ofReal_add, ofReal_natCast] at hi
  simp only [logTrapezoidError, ofReal_add, ofReal_natCast, ofReal_one, ofReal_zero,
    sub_zero, add_zero, add_sub_cancel_left, add_assoc]
  rw [← hi]

/-- A periodic second-order remainder for every nonnegative integer cell. -/
theorem logTrapezoidError_nat_eq_bernoulli_two {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    logTrapezoidError z N ((N : ℝ) + 1) =
      (1 / 12 : ℂ) * ((z + N + 1)⁻¹ - (z + N)⁻¹) +
      ∫ x : ℝ in (N : ℝ)..((N : ℝ) + 1),
        (bernoulliPeriodic 2 x : ℂ) * (z + (x : ℂ))⁻¹ ^ 2 := by
  rw [logTrapezoidError_nat_eq_shift, bernoulliPeriodic_inv_pow_unit_shift]
  exact logTrapezoidError_eq_bernoulli_two (by simp only [add_re, natCast_re]; positivity)

/-- The entire finite logarithmic remainder is one boundary term and one Bernoulli integral. -/
theorem sum_logTrapezoidError_eq_bernoulli_two {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1)) =
      (1 / 12 : ℂ) * ((z + N)⁻¹ - z⁻¹) +
      ∫ x : ℝ in 0..(N : ℝ),
        (bernoulliPeriodic 2 x : ℂ) * (z + (x : ℂ))⁻¹ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_bernoulliPeriodic_inv_pow 2 (by omega : 1 < 2)
        hz (le_refl 0) (Nat.cast_nonneg N))
      (intervalIntegrable_bernoulliPeriodic_inv_pow 2 (by omega : 1 < 2)
        hz (Nat.cast_nonneg N) (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith))
    rw [Finset.sum_range_succ, ih, logTrapezoidError_nat_eq_bernoulli_two hz]
    simp only [Nat.cast_succ]
    rw [← hi]
    ring

end Complex

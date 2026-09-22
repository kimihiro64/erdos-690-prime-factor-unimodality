/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.Trapezoid

/-! # A uniformly summable trapezoid remainder for the complex logarithm

For `Re(z)+a>0`, the second derivative of `log(z+x)` is bounded in norm by
`1/(Re(z)+x)^2`. The trapezoid remainder on `[a,b]` is therefore bounded
by an explicit difference of reciprocals. On consecutive unit cells the
bounds telescope, giving a total error at most `1/(8*Re(z))`, uniformly
in the imaginary part and in the number of cells.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Complex

/-- The trapezoid error for the logarithm along a horizontal segment. -/
noncomputable def logTrapezoidError (z : ℂ) (a b : ℝ) : ℂ :=
  ((b : ℂ) - a) / 2 * (log (z + a) + log (z + b)) -
    ∫ x in a..b, log (z + x)

private lemma shifted_re_pos {z : ℂ} {a x : ℝ} (hz : 0 < z.re + a) (hx : a ≤ x) :
    0 < (z + x).re := by simp only [add_re, ofReal_re]; linarith

private lemma shifted_ne_zero {z : ℂ} {a x : ℝ} (hz : 0 < z.re + a) (hx : a ≤ x) :
    z + x ≠ 0 := by
  have h := shifted_re_pos hz hx
  intro he
  simp [he] at h

/-- The logarithm is integrable along any segment lying in the open right half-plane. -/
theorem intervalIntegrable_log_add_ofReal {z : ℂ} {a b : ℝ}
    (hab : a ≤ b) (hz : 0 < z.re + a) :
    IntervalIntegrable (fun x : ℝ => log (z + x)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro x hx
  exact ((continuousAt_clog (Or.inl (shifted_re_pos hz hx.1))).comp
    (f := fun y : ℝ => z + y) (by fun_prop)).continuousWithinAt

/-- An explicit reciprocal bound for one logarithmic trapezoid remainder. -/
theorem norm_logTrapezoidError_le {z : ℂ} {a b : ℝ}
    (hab : a ≤ b) (hz : 0 < z.re + a) :
    ‖logTrapezoidError z a b‖ ≤
      (b - a) ^ 2 / 8 * (1 / (z.re + a) - 1 / (z.re + b)) := by
  have hf (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y : ℝ => log (z + y)) (z + x)⁻¹ x := by
    convert! ((hasDerivAt_log (Or.inl (shifted_re_pos hz hx.1))).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).const_add z)).comp_ofReal using 1
    simp
  have hf' (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y : ℝ => (z + y)⁻¹) (-((z + x) ^ 2)⁻¹) x := by
    convert! ((hasDerivAt_inv (shifted_ne_zero hz hx.1)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).const_add z)).comp_ofReal using 1
    simp
  have hi : IntervalIntegrable (fun x : ℝ => -((z + x) ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (((by fun_prop : ContinuousOn (fun x : ℝ => z + x) (Icc a b)).pow 2).inv₀
      (fun x hx => pow_ne_zero 2 (shifted_ne_zero hz hx.1))).neg
  have hreal (x : ℝ) (hx : x ∈ Icc a b) : 0 < z.re + x := by linarith [hx.1]
  have hir : IntervalIntegrable (fun x : ℝ => ((z.re + x) ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact ((by fun_prop : ContinuousOn (fun x : ℝ => z.re + x) (Icc a b)).pow 2).inv₀
      (fun x hx => pow_ne_zero 2 (hreal x hx).ne')
  have hbound : (∫ x in a..b, ‖-((z + x) ^ 2)⁻¹‖) ≤
      ∫ x in a..b, ((z.re + x) ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hab hi.norm hir
    intro x hx
    have hn : z.re + x ≤ ‖z + x‖ := by simpa using re_le_norm (z + x)
    simp only [norm_neg, norm_inv, norm_pow]
    exact inv_anti₀ (sq_pos_of_pos (hreal x hx))
      (pow_le_pow_left₀ (hreal x hx).le hn 2)
  have hInt : (∫ x in a..b, ((z.re + x) ^ 2)⁻¹) =
      1 / (z.re + a) - 1 / (z.re + b) := by
    have hd (x : ℝ) (hx : x ∈ uIcc a b) :
        HasDerivAt (fun y : ℝ => -(z.re + y)⁻¹) ((z.re + x) ^ 2)⁻¹ x := by
      have hp := hreal x (by simpa only [uIcc_of_le hab] using hx)
      convert! (((hasDerivAt_id x).const_add z.re).inv hp.ne').neg using 1
      simp only [id_eq, neg_div, one_div, neg_neg]
    simpa [one_div, sub_eq_add_neg, add_comm] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd hir
  exact (intervalIntegral.norm_trapezoid_sub_integral_le hab hf hf' hi).trans
    (mul_le_mul_of_nonneg_left (hbound.trans_eq hInt) (by positivity))

/-- The total unit-cell remainder has a telescoping bound uniform in the imaginary part. -/
theorem norm_sum_logTrapezoidError_le {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1)‖ ≤
      (1 / 8 : ℝ) * (1 / z.re - 1 / (z.re + N)) := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖logTrapezoidError z k (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, (1 / 8 : ℝ) *
        (1 / (z.re + k) - 1 / (z.re + (k + 1))) := by
      apply Finset.sum_le_sum
      intro k _
      simpa using norm_logTrapezoidError_le (z := z) (a := (k : ℝ)) (b := k + 1)
        (by linarith) (by positivity)
    _ = _ := by
      rw [← Finset.mul_sum]
      have h := Finset.sum_range_sub' (fun k : ℕ => 1 / (z.re + k)) N
      simpa using congrArg (fun t : ℝ => (1 / 8) * t) h

/-- Integrating the logarithm on a right-half-plane horizontal segment. -/
theorem integral_log_add_ofReal {z : ℂ} {a b : ℝ}
    (hab : a ≤ b) (hz : 0 < z.re + a) :
    (∫ x in a..b, log (z + x)) =
      ((z + b) * log (z + b) - (z + b)) -
        ((z + a) * log (z + a) - (z + a)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _
    (intervalIntegrable_log_add_ofReal hab hz)
  intro x hx
  have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using hx
  have hlog := (hasDerivAt_log (Or.inl (shifted_re_pos hz hx'.1))).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).const_add z)
  convert! ((((hasDerivAt_id (x : ℂ)).const_add z).mul hlog).sub
    ((hasDerivAt_id (x : ℂ)).const_add z)).comp_ofReal using 1
  simp [shifted_ne_zero hz hx'.1]

/-- The finite logarithm sum is its integral, its endpoint correction, and the cell errors. -/
theorem sum_log_add_eq_integral_add_logTrapezoidError {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), log (z + k)) =
      (∫ x in (0 : ℝ)..N, log (z + x)) + (log z + log (z + N)) / 2 +
        ∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1) := by
  have hi := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : ℝ => log (z + x)) (a := fun k : ℕ => (k : ℝ)) (n := N)
    (fun k _ => intervalIntegrable_log_add_ofReal (by simp) (by positivity))
  have h0 := Finset.sum_range_succ (fun k : ℕ => log (z + k)) N
  have h1 := Finset.sum_range_succ' (fun k : ℕ => log (z + k)) N
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at hi h0 h1
  simp only [logTrapezoidError, ofReal_natCast, ofReal_add, ofReal_one,
    add_sub_cancel_left, Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [hi]
  linear_combination h0 / 2 + h1 / 2

/-- A height-independent bound for every initial segment of logarithmic cell errors. -/
theorem norm_sum_logTrapezoidError_le_inv {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, logTrapezoidError z k (k + 1)‖ ≤ 1 / (8 * z.re) := by
  have hn : 0 ≤ 1 / (z.re + N) := by positivity
  calc
    _ ≤ (1 / 8 : ℝ) * (1 / z.re - 1 / (z.re + N)) :=
      norm_sum_logTrapezoidError_le hz N
    _ ≤ (1 / 8 : ℝ) * (1 / z.re) := by linarith
    _ = _ := by ring

end Complex

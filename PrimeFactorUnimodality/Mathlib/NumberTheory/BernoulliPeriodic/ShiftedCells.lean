/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.ShiftedIntegrability

/-! # Integration by parts for complex-shifted Bernoulli kernels

Differentiate the normalized polynomial on each cell and telescope at the
integer endpoints. Both finite boundary terms are retained, including the
initial cell at zero, where the complex shift keeps the denominator nonzero.
-/

open Complex MeasureTheory Set

namespace Polynomial

/-- Integration by parts on one cell for a genuinely complex reciprocal base. -/
theorem bernoulliNormalizedReal_inv_pow_cell {k : ℕ} (hk : 1 ≤ k) (p : ℕ)
    {z : ℂ} (hz : 0 < z.re) :
    (∫ u : ℝ in 0..1, (bernoulliNormalizedReal k u : ℂ) * (z + (u : ℂ))⁻¹ ^ p) =
      (bernoulliNormalizedReal (k + 1) 0 : ℂ) * ((z + 1)⁻¹ ^ p - z⁻¹ ^ p) +
      (p : ℂ) * ∫ u : ℝ in 0..1,
        (bernoulliNormalizedReal (k + 1) u : ℂ) * (z + (u : ℂ))⁻¹ ^ (p + 1) := by
  have hcont (j : ℕ) : ContinuousOn (fun u : ℝ => (z + (u : ℂ))⁻¹ ^ j) (Icc 0 1) :=
    (continuousOn_inv_pow_add_ofReal j hz).mono (fun _ hu => hu.1)
  have hf (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v : ℝ => (z + (v : ℂ))⁻¹ ^ p)
        (-(p : ℂ) * (z + (u : ℂ))⁻¹ ^ (p + 1)) u := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    exact hasDerivAt_inv_pow_add_ofReal p (add_ofReal_ne_zero_of_re_pos hz hu.1)
  have hq (u : ℝ) (_hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v : ℝ => (bernoulliNormalizedReal (k + 1) v : ℂ))
        (bernoulliNormalizedReal k u : ℂ) u :=
    (hasDerivAt_bernoulliNormalizedReal k u).ofReal_comp
  have hfInt : IntervalIntegrable
      (fun u : ℝ => -(p : ℂ) * (z + (u : ℂ))⁻¹ ^ (p + 1)) volume 0 1 :=
    ((hcont (p + 1)).const_mul _).intervalIntegrable_of_Icc (by norm_num)
  have hpInt : IntervalIntegrable (fun u : ℝ => (bernoulliNormalizedReal k u : ℂ))
      volume 0 1 :=
    (continuous_ofReal.comp (continuous_bernoulliNormalizedReal k)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hq hfInt hpInt
  have hleft : (∫ u : ℝ in 0..1,
      (z + (u : ℂ))⁻¹ ^ p * (bernoulliNormalizedReal k u : ℂ)) =
      ∫ u : ℝ in 0..1, (bernoulliNormalizedReal k u : ℂ) * (z + (u : ℂ))⁻¹ ^ p := by
    apply intervalIntegral.integral_congr
    intro u _
    exact mul_comm _ _
  have hright : (∫ u : ℝ in 0..1,
      (-(p : ℂ) * (z + (u : ℂ))⁻¹ ^ (p + 1)) *
        (bernoulliNormalizedReal (k + 1) u : ℂ)) =
      -(p : ℂ) * ∫ u : ℝ in 0..1,
        (bernoulliNormalizedReal (k + 1) u : ℂ) * (z + (u : ℂ))⁻¹ ^ (p + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  rw [hleft, hright, bernoulliNormalizedReal_one_eq_zero (by omega : k + 1 ≠ 1)] at h
  simp only [ofReal_one, ofReal_zero, add_zero] at h
  linear_combination h

/-- Integer translation replaces the periodic profile by its polynomial on the unit cell. -/
theorem bernoulliPeriodic_inv_pow_unit_shift (k N p : ℕ) (z : ℂ) :
    (∫ x : ℝ in (N : ℝ)..((N : ℝ) + 1),
      (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p) =
      ∫ u : ℝ in 0..1, (bernoulliNormalizedReal k u : ℂ) *
        (z + (N : ℂ) + (u : ℂ))⁻¹ ^ p := by
  calc
    _ = ∫ u : ℝ in 0..1, (bernoulliPeriodic k ((N : ℝ) + u) : ℂ) *
        (z + (((N : ℝ) + u : ℝ) : ℂ))⁻¹ ^ p := by
      simpa only [add_zero] using
        (intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := 1)
          (fun x : ℝ => (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p) (N : ℝ)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr_ae
      have hne : ∀ᵐ u : ℝ, u ≠ 1 := by simp [ae_iff]
      filter_upwards [hne] with u hu
      intro hmem
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
      have hfrac : Int.fract ((N : ℝ) + u) = u := by
        rw [add_comm, Int.fract_add_natCast,
          Int.fract_eq_self.mpr ⟨hmem.1.le, lt_of_le_of_ne hmem.2 hu⟩]
      simp only [bernoulliPeriodic, hfrac, ofReal_add, ofReal_natCast, add_assoc]

/-- The periodic cell recursion also holds at the first cell, starting at zero. -/
theorem bernoulliPeriodic_inv_pow_cell {k : ℕ} (hk : 1 ≤ k) (N p : ℕ)
    {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in (N : ℝ)..((N : ℝ) + 1),
      (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p) =
      (bernoulliNormalizedReal (k + 1) 0 : ℂ) *
        ((z + N + 1)⁻¹ ^ p - (z + N)⁻¹ ^ p) +
      (p : ℂ) * ∫ x : ℝ in (N : ℝ)..((N : ℝ) + 1),
        (bernoulliPeriodic (k + 1) x : ℂ) * (z + (x : ℂ))⁻¹ ^ (p + 1) := by
  rw [bernoulliPeriodic_inv_pow_unit_shift, bernoulliPeriodic_inv_pow_unit_shift]
  exact bernoulliNormalizedReal_inv_pow_cell hk p (by
    simp only [add_re, natCast_re]
    positivity)

/-- Finite shifted Bernoulli integration by parts with both boundary values retained. -/
theorem bernoulliPeriodic_inv_pow_finite_recursion {k p : ℕ} (hk : 1 ≤ k) (hp : 1 < p)
    {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∫ x : ℝ in 0..(N : ℝ),
      (bernoulliPeriodic k x : ℂ) * (z + (x : ℂ))⁻¹ ^ p) =
      (bernoulliNormalizedReal (k + 1) 0 : ℂ) * ((z + N)⁻¹ ^ p - z⁻¹ ^ p) +
      (p : ℂ) * ∫ x : ℝ in 0..(N : ℝ),
        (bernoulliPeriodic (k + 1) x : ℂ) * (z + (x : ℂ))⁻¹ ^ (p + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hF := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_bernoulliPeriodic_inv_pow k hp hz (le_refl 0) (Nat.cast_nonneg N))
      (intervalIntegrable_bernoulliPeriodic_inv_pow k hp hz (Nat.cast_nonneg N)
        (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith))
    have hG := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_bernoulliPeriodic_inv_pow (k + 1) (by omega : 1 < p + 1)
        hz (le_refl 0) (Nat.cast_nonneg N))
      (intervalIntegrable_bernoulliPeriodic_inv_pow (k + 1) (by omega : 1 < p + 1)
        hz (Nat.cast_nonneg N) (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith))
    simp only [Nat.cast_succ]
    rw [← hF, ← hG, ih, bernoulliPeriodic_inv_pow_cell hk N p hz]
    ring

end Polynomial

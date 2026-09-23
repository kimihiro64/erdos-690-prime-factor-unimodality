import PrimeFactorUnimodality.Helpers.Analytic.DirichletEndpointIntervals
import PrimeFactorUnimodality.Helpers.Analytic.EulerBernoulliIntervals

/-! # Executable bounds for the complete Euler remainder

Scale the rising product at every step instead of separately constructing
large numerator and denominator powers. The endpoint amplitude and exact
Bernoulli coefficient majorant are shared across the whole grid block.
The comparison retains the entire improper Euler tail.
-/

namespace PrimeFactorUnimodality

open Complex LeanCert.Core Polynomial

/-- One scaled multiplication per rising-factor order. -/
def eulerRisingInterval (N : ℕ) (S : ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.point ⟨1, 0⟩
  | k + 1 => eulerRisingStep N S k (eulerRisingInterval N S k)

/-- The scaled recurrence encloses the exact normalized rising factorial. -/
theorem mem_eulerRisingInterval (N k : ℕ) {s : ℂ} {S : ComplexInterval} (hs : s ∈ S) :
    zetaRisingFactor s k / (N : ℂ) ^ k ∈ eulerRisingInterval N S k := by
  induction k with
  | zero => simpa [eulerRisingInterval, zetaRisingFactor] using ComplexInterval.mem_constant 1
  | succ k ih => exact mem_eulerRisingStep N k hs ih

/-- Exact scaled form of the analytic error at every critical-line height. -/
theorem zetaEulerError_eq_scaled (N m : ℕ) (hN : 0 < N) {s : ℂ} (hs : s.re = 1 / 2) :
    zetaEulerError N s m = (bernoulliCoeffBound (m + 1) : ℝ) *
      ‖zetaRisingFactor s (m + 1) / (N : ℂ) ^ (m + 1)‖ * N *
        Real.exp (-Real.log N / 2) / (1 / 2 + (m : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hden : (1 / 2 : ℝ) + m ≠ 0 := by positivity
  unfold zetaEulerError
  rw [hs, Real.rpow_sub hNpos, Real.rpow_natCast]
  have he : (N : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-Real.log N / 2) := by
    rw [Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  rw [he, norm_div, norm_pow, Complex.norm_natCast, pow_succ]
  field_simp

/-- Rational remainder budget with a shared coefficient bound and endpoint amplitude. -/
def eulerRemainderBound (N m : ℕ) (C M A : ℚ) : ℚ :=
  C * M * N * A / (1 / 2 + (m : ℚ))

/-- Check a scaled-product norm and the resulting complete rational error. -/
def checkEulerRemainder (d : DirichletEndpointIntervals) (S : ComplexInterval)
    (m : ℕ) (C M E : ℚ) : Bool :=
  (eulerRisingInterval d.cutoff S (m + 1)).close ⟨0, 0⟩ M &&
    decide (eulerRemainderBound d.cutoff m C M d.amplitude.hi ≤ E)

/-- Every accepted bound controls the original full analytic Euler error. -/
theorem zetaEulerError_le_of_check {d : DirichletEndpointIntervals} (hd : d.Valid)
    {s : ℂ} {S : ComplexInterval} (hs : s ∈ S) (hsre : s.re = 1 / 2)
    (m : ℕ) {C M E : ℚ} (hC : C = bernoulliCoeffBudget (m + 1))
    (h : checkEulerRemainder d S m C M E = true) :
    zetaEulerError d.cutoff s m ≤ (E : ℝ) := by
  simp only [checkEulerRemainder, Bool.and_eq_true, decide_eq_true_eq] at h
  have hnorm : ‖zetaRisingFactor s (m + 1) / (d.cutoff : ℂ) ^ (m + 1)‖ ≤ (M : ℝ) := by
    exact ComplexInterval.norm_le_of_close_zero h.1
      (mem_eulerRisingInterval d.cutoff (m + 1) hs)
  have hcoef : bernoulliCoeffBound (m + 1) = C := by
    rw [hC, bernoulliCoeffBound_eq_budget]
  have hC0 : (0 : ℝ) ≤ C := by
    rw [← hcoef]
    exact_mod_cast bernoulliCoeffBound_nonneg (m + 1)
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg _).trans hnorm
  have hprod := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnorm hC0) (Nat.cast_nonneg d.cutoff : (0 : ℝ) ≤ _)
  have hbound := mul_le_mul hprod hd.2.2.2
    (Real.exp_nonneg _) (mul_nonneg (mul_nonneg hC0 hM0) (Nat.cast_nonneg _))
  rw [zetaEulerError_eq_scaled d.cutoff m hd.1 hsre, hcoef]
  refine (div_le_div_of_nonneg_right hbound (by positivity)).trans ?_
  have hrat : (eulerRemainderBound d.cutoff m C M d.amplitude.hi : ℝ) ≤ (E : ℝ) :=
    by exact_mod_cast h.2
  simpa only [eulerRemainderBound, Rat.cast_div, Rat.cast_add, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] using hrat

end PrimeFactorUnimodality

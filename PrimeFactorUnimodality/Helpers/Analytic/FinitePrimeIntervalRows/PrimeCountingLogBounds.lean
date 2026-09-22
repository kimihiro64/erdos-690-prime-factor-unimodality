import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingNumerics

set_option autoImplicit false

/-! # Logarithm enclosures from integer-power comparisons

Comparing a power of an endpoint with a 2–3–5-smooth integer gives a rational
enclosure without introducing one transcendental proof per endpoint.
-/

namespace PrimeFactorUnimodality

theorem log_nat_lower_of_smooth_power
    {n s a b c : Nat} (hs : 0 < s)
    (hbound : 2 ^ a * 3 ^ b * 5 ^ c ≤ n ^ s) :
    ((a : Real) * (693147 / 1000000) +
      (b : Real) * (1098612 / 1000000) +
      (c : Real) * (1609437 / 1000000)) / s ≤ Real.log n := by
  have hsmooth : (0 : Nat) < 2 ^ a * 3 ^ b * 5 ^ c := by positivity
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    simp [this, Nat.ne_of_gt hs] at hbound
  have hlog := Real.log_le_log
    (by exact_mod_cast hsmooth : (0 : Real) < (2 : Real) ^ a * 3 ^ b * 5 ^ c)
    (by exact_mod_cast hbound : (2 : Real) ^ a * 3 ^ b * 5 ^ c ≤ (n : Real) ^ s)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  apply (div_le_iff₀ (by exact_mod_cast hs : (0 : Real) < s)).2
  have h2 := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le
    (Nat.cast_nonneg a : (0 : Real) ≤ a)
  have h3 := mul_le_mul_of_nonneg_left Real.log_three_gt_d9.le
    (Nat.cast_nonneg b : (0 : Real) ≤ b)
  have h5 := mul_le_mul_of_nonneg_left Real.log_five_gt_d9.le
    (Nat.cast_nonneg c : (0 : Real) ≤ c)
  nlinarith [show (0 : Real) ≤ a from Nat.cast_nonneg a,
    show (0 : Real) ≤ b from Nat.cast_nonneg b,
    show (0 : Real) ≤ c from Nat.cast_nonneg c]

theorem log_nat_upper_of_smooth_power
    {n s a b c : Nat} (hn : 0 < n) (hs : 0 < s)
    (hbound : n ^ s ≤ 2 ^ a * 3 ^ b * 5 ^ c) :
    Real.log n ≤ ((a : Real) * (693148 / 1000000) +
      (b : Real) * (1098613 / 1000000) +
      (c : Real) * (1609438 / 1000000)) / s := by
  have hlog := log_nat_le_smooth_upper (pow_pos hn s) hbound
  rw [Nat.cast_pow, Real.log_pow] at hlog
  apply (le_div_iff₀ (by exact_mod_cast hs : (0 : Real) < s)).2
  nlinarith

end PrimeFactorUnimodality

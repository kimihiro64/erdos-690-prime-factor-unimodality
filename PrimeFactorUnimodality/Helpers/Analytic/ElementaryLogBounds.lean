import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

/-!
# Logarithm bounds for the elementary Chebyshev argument

These compact aliases and consequences of Mathlib's certified decimal bounds
replace the interval-arithmetic table imported by the source development.
-/

namespace LogTables

open Real

theorem log_2_gt : (0.693147 : Real) < log 2 :=
  (by norm_num : (0.693147 : Real) < 0.6931471803).trans Real.log_two_gt_d9

theorem log_2_lt : log 2 < (0.693148 : Real) :=
  Real.log_two_lt_d9.trans (by norm_num)

theorem log_3_gt : (1.098612 : Real) < log 3 :=
  (by norm_num : (1.098612 : Real) < 1.0986122885).trans Real.log_three_gt_d9

theorem log_3_lt : log 3 < (1.098613 : Real) :=
  Real.log_three_lt_d9.trans (by norm_num)

theorem log_5_gt : (1.609437 : Real) < log 5 :=
  (by norm_num : (1.609437 : Real) < 1.6094379123).trans Real.log_five_gt_d9

theorem log_5_lt : log 5 < (1.609438 : Real) :=
  Real.log_five_lt_d9.trans (by norm_num)

-- The finite `psi` check only needs comfortable upper bounds.  Expressing
-- each prime below 30 under a nearby 2–3–5-smooth integer keeps this file
-- independent of external interval-arithmetic tactics.
theorem log_7_lt : log 7 < (1.946044 : Real) := by
  have h := Real.log_lt_log (by positivity : (0 : Real) < 7 ^ (14 : Nat))
    (by norm_num : (7 : Real) ^ (14 : Nat) < 2 ^ (26 : Nat) * 3 ^ (4 : Nat) * 5 ^ (3 : Nat))
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  norm_num at h ⊢
  nlinarith [log_2_lt, log_3_lt, log_5_lt]

theorem log_11_lt : log 11 < (2.397932 : Real) := by
  have h := Real.log_lt_log (by positivity : (0 : Real) < 11 ^ (15 : Nat))
    (by norm_num : (11 : Real) ^ (15 : Nat) < 2 ^ (22 : Nat) * 3 ^ (13 : Nat) * 5 ^ (4 : Nat))
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  norm_num at h ⊢
  nlinarith [log_2_lt, log_3_lt, log_5_lt]

theorem log_13_lt : log 13 < (2.564970 : Real) := by
  have h := Real.log_lt_log (by positivity : (0 : Real) < 13 ^ (15 : Nat))
    (by norm_num : (13 : Real) ^ (15 : Nat) < 2 ^ (23 : Nat) * 5 ^ (14 : Nat))
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at h
  norm_num at h ⊢
  nlinarith [log_2_lt, log_5_lt]

theorem log_17_lt : log 17 < (2.833233 : Real) := by
  have h := Real.log_lt_log (by positivity : (0 : Real) < 17 ^ (13 : Nat))
    (by norm_num : (17 : Real) ^ (13 : Nat) < 2 ^ (28 : Nat) * 3 ^ (10 : Nat) * 5 ^ (4 : Nat))
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  norm_num at h ⊢
  nlinarith [log_2_lt, log_3_lt, log_5_lt]

theorem log_19_lt : log 19 < (2.944467 : Real) := by
  have h := Real.log_lt_log (by positivity : (0 : Real) < 19 ^ (8 : Nat))
    (by norm_num : (19 : Real) ^ (8 : Nat) < 2 ^ (23 : Nat) * 3 ^ (4 : Nat) * 5 ^ (2 : Nat))
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  norm_num at h ⊢
  nlinarith [log_2_lt, log_3_lt, log_5_lt]

theorem log_23_lt : log 23 < (3.135519 : Real) := by
  have h := Real.log_lt_log (by positivity : (0 : Real) < 23 ^ (14 : Nat))
    (by norm_num : (23 : Real) ^ (14 : Nat) < 2 ^ (40 : Nat) * 3 ^ (3 : Nat) * 5 ^ (8 : Nat))
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  norm_num at h ⊢
  nlinarith [log_2_lt, log_3_lt, log_5_lt]

theorem log_29_lt : log 29 < (3.367302 : Real) := by
  have h := Real.log_lt_log (by positivity : (0 : Real) < 29 ^ (11 : Nat))
    (by norm_num : (29 : Real) ^ (11 : Nat) < 2 ^ (6 : Nat) * 3 ^ (27 : Nat) * 5 ^ (2 : Nat))
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  norm_num at h ⊢
  nlinarith [log_2_lt, log_3_lt, log_5_lt]

theorem log_30_gt : (3.401197 : Real) < log 30 := by
  rw [show (30 : Real) = 2 * (3 * 5) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9,
    Real.log_five_gt_d9]

/-! Smooth-number envelopes let finite certificates prove logarithm bounds
without introducing a separate opaque logarithm evaluator for every row. -/
theorem log_le_smooth {x : Real} {a b c : Nat} (hx : 0 < x)
    (hbound : x ≤ (2 : Real) ^ a * (3 : Real) ^ b * (5 : Real) ^ c) :
    log x ≤ (a : Real) * log 2 + (b : Real) * log 3 +
      (c : Real) * log 5 := by
  have h := Real.log_le_log hx hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem log_le_smooth_with_seven {x : Real} {a b c d : Nat} (hx : 0 < x)
    (hbound : x ≤ (2 : Real) ^ a * (3 : Real) ^ b *
      (5 : Real) ^ c * (7 : Real) ^ d) :
    log x ≤ (a : Real) * log 2 + (b : Real) * log 3 +
      (c : Real) * log 5 + (d : Real) * log 7 := by
  have h := Real.log_le_log hx hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem smooth_log_le {x : Real} {a b c : Nat} (hx : 0 < x)
    (hbound : (2 : Real) ^ a * (3 : Real) ^ b * (5 : Real) ^ c ≤ x) :
    (a : Real) * log 2 + (b : Real) * log 3 +
      (c : Real) * log 5 ≤ log x := by
  have h := Real.log_le_log (by positivity) hbound
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem log_nat_ge_smooth_lower {n a b c : Nat} (hn : 0 < n)
    (hbound : (2 : Nat) ^ a * 3 ^ b * 5 ^ c ≤ n) :
    (a : Real) * (693147 / 1000000 : Real) +
      (b : Real) * (1098612 / 1000000 : Real) +
      (c : Real) * (1609437 / 1000000 : Real) ≤ Real.log n := by
  have h := smooth_log_le (x := (n : Real)) (by exact_mod_cast hn) (by
    exact_mod_cast hbound)
  have h2 := mul_le_mul_of_nonneg_left log_2_gt.le (by positivity : (0 : Real) ≤ (a : Real))
  have h3 := mul_le_mul_of_nonneg_left log_3_gt.le (by positivity : (0 : Real) ≤ (b : Real))
  have h5 := mul_le_mul_of_nonneg_left log_5_gt.le (by positivity : (0 : Real) ≤ (c : Real))
  nlinarith

end LogTables

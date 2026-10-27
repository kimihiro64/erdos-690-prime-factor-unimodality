/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.SharpElementaryChebyshev

/-!
# A half-logarithm elementary upper bound for Chebyshev's psi function

The five-term factorial identity is telescoped while retaining the decreasing
logarithm in each summand. Completing the square bounds the accumulated error.
-/

set_option autoImplicit false

namespace Chebyshev

open Real

private theorem le_div_pos_iff (a b c : Real) (hc : 0 < c) :
    Iff (a <= b / c) (a * c <= b) := by
  have heq : b / c * c = b := by field_simp
  constructor
  case mp =>
    intro h
    have hm := mul_le_mul_of_nonneg_right h hc.le
    rwa [heq] at hm
  case mpr =>
    intro h
    exact le_of_mul_le_mul_right (by rw [heq]; exact h) hc

private theorem sum_real_indices (n : Nat) :
    (Finset.range n).sum (fun i => (i : Real)) = (n : Real) * ((n : Real) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem psi_error_sum (v l : Real) (n : Nat) :
    (Finset.range n).sum (fun i => (5 : Real) / 2 * (v - (i : Real) * l) - 1) =
      (5 : Real) / 2 * ((n : Real) * v - (n : Real) * ((n : Real) - 1) / 2 * l) - n := by
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum, Finset.sum_sub_distrib,
    <- Finset.sum_mul, sum_real_indices]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

private theorem psi_error_sum_le (v l : Real) (hl : 0 < l) (hl2 : l <= 2) (n : Nat) :
    (5 : Real) / 2 * ((n : Real) * v - (n : Real) * ((n : Real) - 1) / 2 * l) - n <=
      5 / (4 * l) * v ^ 2 + 5 / 4 * v + 1 := by
  have hsq := sq_nonneg (l * (n : Real) - v - l / 2)
  have hn : (0 : Real) <= n := by positivity
  have hnl := mul_nonneg hl.le hn
  have hreserve := mul_nonneg hl.le (show 0 <= 1 - 5 * l / 16 by linarith)
  have hscaled :
      ((5 : Real) / 2 * ((n : Real) * v - (n : Real) * ((n : Real) - 1) / 2 * l) - n) * l <=
        5 / 4 * v ^ 2 + 5 / 4 * v * l + l := by
    nlinarith only [hsq, hnl, hreserve]
  have heq : (5 / (4 * l) * v ^ 2 + 5 / 4 * v + 1) * l =
      5 / 4 * v ^ 2 + 5 / 4 * v * l + l := by
    field_simp
  exact le_of_mul_le_mul_right (by rw [heq]; exact hscaled) hl

theorem psi_half_upper (x : Real) (hx : 30 <= x) :
    psi x <= 6 * a * x / 5 +
      5 / (4 * log 6) * (log x) ^ 2 + 5 / 4 * log x + 1 := by
  have hxpos : 0 < x := by linarith
  have hl : 0 < log (6 : Real) := log_pos (by norm_num)
  have hl2 : log (6 : Real) <= 2 := by
    rw [show (6 : Real) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
    linarith [LogTables.log_2_lt, LogTables.log_3_lt]
  have rpow_key : (30 : Real) * 6 ^ (log (x / 5) / log 6 - 1) = x := by
    rw [rpow_def_of_pos (by norm_num)]
    field_simp
    rw [exp_sub, exp_log, exp_log] <;> linarith
  let n : Nat := Nat.floor (log (x / 5) / log 6)
  have hn : 1 <= n := by
    apply Nat.le_floor
    norm_cast
    apply (le_div_pos_iff _ _ _ hl).2
    rw [one_mul]
    exact log_le_log (by norm_num) (by linarith)
  have hfloor : (n : Real) <= log (x / 5) / log 6 :=
    Nat.floor_le (div_nonneg (log_nonneg (by linarith)) hl.le)
  have domain (i : Nat) (hi : i < n) : 30 <= x / (6 : Real) ^ i := by
    apply (le_div_pos_iff _ _ _ (by positivity)).2
    calc
      30 * (6 : Real) ^ i <= 30 * 6 ^ (n - 1) := by gcongr <;> grind
      _ <= 30 * 6 ^ (log (x / 5) / log 6 - 1) := by
        rw [<- rpow_natCast, Nat.cast_sub hn]
        gcongr <;> first | exact hfloor | norm_num
      _ = x := rpow_key
  have telescope (m : Nat) :
      psi x - psi (x / (6 : Real) ^ m) =
        (Finset.range m).sum (fun i =>
          psi (x / (6 : Real) ^ i) - psi (x / (6 : Real) ^ (i + 1))) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, <- ih]
      ring
  have bound (m : Nat) (hm : forall i, i < m -> 30 <= x / (6 : Real) ^ i) :
      psi x - psi (x / (6 : Real) ^ m) <=
        (Finset.range m).sum (fun i => a * x / (6 : Real) ^ i) +
        (Finset.range m).sum (fun i => (5 : Real) / 2 * (log x - (i : Real) * log 6) - 1) := by
    rw [<- Finset.sum_add_distrib, telescope]
    apply Finset.sum_le_sum
    intro i hi
    have h := psi_diff_half_upper (x / (6 : Real) ^ i) (hm i (Finset.mem_range.mp hi))
    rw [log_div hxpos.ne' (by positivity), log_pow] at h
    have hd : x / (6 : Real) ^ i / 6 = x / (6 : Real) ^ (i + 1) := by
      rw [pow_succ]
      field_simp
    rw [hd] at h
    convert h using 1 <;> ring
  have hgeom :
      (Finset.range n).sum (fun i => a * x / (6 : Real) ^ i) =
        6 * a * x / 5 - (6 * a * x / 5) * ((1 : Real) / 6) ^ n := by
    have hterm (i : Nat) : a * x / (6 : Real) ^ i = a * x * ((1 : Real) / 6) ^ i := by
      rw [one_div_pow]
      ring
    simp_rw [hterm]
    rw [<- Finset.mul_sum, geom_sum_eq (by norm_num)]
    norm_num
    ring
  have hpower : x <= 30 * (6 : Real) ^ n := by
    calc
      x = 30 * (6 : Real) ^ (log (x / 5) / log 6 - 1) := rpow_key.symm
      _ <= 30 * (6 : Real) ^ n := by
        rw [<- rpow_natCast]
        gcongr
        norm_num
        exact (Nat.sub_one_lt_floor _).le
  have hyEq : x / (6 : Real) ^ n * (6 : Real) ^ n = x := by field_simp
  have hy : x / (6 : Real) ^ n <= 30 :=
    le_of_mul_le_mul_right (by rw [hyEq]; exact hpower) (by positivity)
  have hsmall := psi_num (x / (6 : Real) ^ n) (by positivity) hy
  have hrecip : x / (6 : Real) ^ n = x * ((1 : Real) / 6) ^ n := by
    rw [one_div_pow]
    ring
  rw [hrecip] at hsmall
  have hb := bound n domain
  rw [hgeom, psi_error_sum, hrecip] at hb
  have he := psi_error_sum_le (log x) (log 6) hl hl2 n
  have ha : 0 <= 6 * a / 5 - (1015 : Real) / 1000 := by
    have ha0 := a_bound.1
    norm_num at ha0
    linarith
  have hpositive := mul_nonneg
    (mul_nonneg hxpos.le (pow_nonneg (show (0 : Real) <= 1 / 6 by norm_num) n)) ha
  nlinarith only [hb, he, hsmall, hpositive]

end Chebyshev

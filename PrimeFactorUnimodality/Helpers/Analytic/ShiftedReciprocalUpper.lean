/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PrimeFactorUnimodality.Helpers.Analytic.MertensConstantUpper
import PrimeFactorUnimodality.Helpers.Analytic.PrimeReciprocalCorrection
import PrimeFactorUnimodality.Helpers.Analytic.SharpReciprocalMertens

/-!
# An elementary upper bound for the shifted reciprocal-prime sum

For every real x >= 1000, the sum of 1/(p-1) over primes p <= x is
less than log(log x) + 11/10 + 11/(5 log x).
-/

set_option autoImplicit false

namespace Mertens

open Real Finset

noncomputable def primeShiftedReciprocalSum (x : Real) : Real :=
  (Finset.Icc 0 (Nat.floor x)).sum (fun p =>
    if p.Prime then 1 / ((p : Real) - 1) else 0)

theorem primeShiftedReciprocalSum_le_reciprocal_add_correction (x : Real) :
    primeShiftedReciprocalSum x <= primeReciprocalSum x + primeReciprocalCorrection := by
  have hterm (p : Nat) :
      (if p.Prime then (1 : Real) / ((p : Real) - 1) else 0) =
        (if p.Prime then (1 : Real) / p else 0) +
          (if p.Prime then (1 : Real) / ((p : Real) * ((p : Real) - 1)) else 0) := by
    split_ifs with hp
    case pos =>
      have hp2 : (2 : Real) <= p := by exact_mod_cast hp.two_le
      have hp0 : Not ((p : Real) = 0) := by linarith
      have hp1 : Not ((p : Real) - 1 = 0) := by linarith
      field_simp <;> ring
    case neg => ring
  unfold primeShiftedReciprocalSum
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  apply add_le_add (le_refl _)
  apply primeReciprocalCorrection_summable.sum_le_tsum
  intro p hp
  split_ifs with hprime
  case pos =>
    have hp2 : (2 : Real) <= p := by exact_mod_cast hprime.two_le
    exact div_nonneg (by norm_num)
      (mul_nonneg (Nat.cast_nonneg p) (by linarith))
  case neg => rfl

theorem primeShiftedReciprocalSum_upper (x : Real) (hx : 1000 <= x) :
    primeShiftedReciprocalSum x <
      log (log x) + (11 : Real) / 10 + (11 / 5 : Real) / log x := by
  have h := primeShiftedReciprocalSum_le_reciprocal_add_correction x
  have hr := (abs_le.mp (primeReciprocalSum_error_abs_le x hx)).2
  linarith [M_lt_029, primeReciprocalCorrection_lt_081]

theorem primeShiftedReciprocalSum_upper_four (x : Real) (hx : 1000 <= x) :
    primeShiftedReciprocalSum x <
      log (log x) + (11 : Real) / 10 + (4 : Real) / log x := by
  have h := primeShiftedReciprocalSum_upper x hx
  have he := div_le_div_of_nonneg_right (show (11 / 5 : Real) <= 4 by norm_num)
    (log_nonneg (by linarith : 1 <= x))
  linarith

end Mertens

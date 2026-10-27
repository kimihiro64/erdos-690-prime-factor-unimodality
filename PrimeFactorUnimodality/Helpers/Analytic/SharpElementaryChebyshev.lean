/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.FactorialFloor
import VendorPrimeNumberTheoremAnd.ElementaryChebyshev

set_option autoImplicit false

/-! # Half-logarithm errors in the elementary Chebyshev argument

The uniform factorial sandwich sharpens the existing five-term weighted
factorial argument. The resulting error is `(5/2) * log x - 1`, uniformly
for real x at least 30. This supplies the lower psi bound and the difference
bound used by the sharper elementary upper estimates.
-/

namespace Chebyshev

open Real

private theorem sum_log_Icc_eq_log_factorial (n : Nat) :
    (Finset.Icc 1 n).sum (fun i => log (i : Real)) = log (n.factorial : Real) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ]
    push_cast
    rw [log_mul (by positivity) (by positivity)]
    ring

theorem T_eq_log_floor_factorial (x : Real) :
    T x = log ((Nat.floor x).factorial : Real) := by
  exact sum_log_Icc_eq_log_factorial (Nat.floor x)

theorem T_half_bounds (x : Real) (hx : 1 <= x) :
    And (x * log x - x - log x / 2 + 1 / 3 <= T x)
      (T x <= x * log x - x + log x / 2 + 1) := by
  rw [T_eq_log_floor_factorial]
  exact log_factorial_floor_half_bounds x hx

theorem U_eq_five_T (x : Real) :
    U x = T x - T (x / 2) - T (x / 3) - T (x / 5) + T (x / 30) := by
  let c : Finsupp Nat Real :=
    Finsupp.single 1 1 - Finsupp.single 2 1 - Finsupp.single 3 1 -
      Finsupp.single 5 1 + Finsupp.single 30 1
  have expand (f : Nat -> Real) :
      c.sum (fun m w => w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
    dsimp only [c]
    rw [Finsupp.sum_add_index (by simp) (by intros; ring)]
    grind only [Finsupp.sum_single_index, Finsupp.sum_sub_index]
  change c.sum (fun m w => w * T (x / m)) = _
  simpa only [Nat.cast_ofNat, Nat.cast_one, div_one] using expand (fun m => T (x / m))

private theorem log_thirty_eq : log (30 : Real) = log 2 + log 3 + log 5 := by
  rw [show (30 : Real) = 2 * 3 * 5 by norm_num,
    log_mul (by norm_num) (by norm_num), log_mul (by norm_num) (by norm_num)]

private theorem main_five (x : Real) (hx : 0 < x) :
    (x * log x - x) - ((x / 2) * log (x / 2) - x / 2) -
      ((x / 3) * log (x / 3) - x / 3) -
      ((x / 5) * log (x / 5) - x / 5) +
      ((x / 30) * log (x / 30) - x / 30) = a * x := by
  rw [a_simpl, log_div hx.ne' (by norm_num : Not ((2 : Real) = 0)),
    log_div hx.ne' (by norm_num : Not ((3 : Real) = 0)),
    log_div hx.ne' (by norm_num : Not ((5 : Real) = 0)),
    log_div hx.ne' (by norm_num : Not ((30 : Real) = 0)), log_thirty_eq]
  ring

theorem U_half_bound (x : Real) (hx : 30 <= x) :
    abs (U x - a * x) <= (5 : Real) / 2 * log x - 1 := by
  have hxpos : 0 < x := by linarith
  have h1 := T_half_bounds x (by linarith)
  have h2 := T_half_bounds (x / 2) (by linarith)
  have h3 := T_half_bounds (x / 3) (by linarith)
  have h5 := T_half_bounds (x / 5) (by linarith)
  have h30 := T_half_bounds (x / 30) (by linarith)
  have hlogs : (log x + log (x / 2) + log (x / 3) + log (x / 5) + log (x / 30)) / 2 =
      (5 : Real) / 2 * log x - log 30 := by
    rw [log_div hxpos.ne' (by norm_num : Not ((2 : Real) = 0)),
      log_div hxpos.ne' (by norm_num : Not ((3 : Real) = 0)),
      log_div hxpos.ne' (by norm_num : Not ((5 : Real) = 0)),
      log_div hxpos.ne' (by norm_num : Not ((30 : Real) = 0)), log_thirty_eq]
    ring
  have hm := main_five x hxpos
  have hlog30 : (10 : Real) / 3 < log 30 := by linarith [LogTables.log_30_gt]
  rw [U_eq_five_T, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h5.1, h5.2,
    h30.1, h30.2]

theorem psi_half_lower (x : Real) (hx : 30 <= x) :
    a * x - (5 : Real) / 2 * log x + 1 <= psi x := by
  have h := (abs_le.mp (U_half_bound x hx)).1
  have hw := psi_ge_weighted x (by linarith)
  linarith

theorem psi_diff_half_upper (x : Real) (hx : 30 <= x) :
    psi x - psi (x / 6) <= a * x + (5 : Real) / 2 * log x - 1 := by
  have h := (abs_le.mp (U_half_bound x hx)).2
  have hw := psi_diff_le_weighted x (by linarith)
  linarith

end Chebyshev

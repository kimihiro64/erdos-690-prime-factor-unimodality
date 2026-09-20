import LeanCert.Tactic.IntervalAuto
import PrimeFactorUnimodality.Helpers.Analytic.DusartFiniteRows
import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33ThetaData
import PrimeFactorUnimodality.Helpers.Analytic.DusartProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! # Endpoint proofs for Dusart's Lemma 3.3

This module proves the integer endpoint inequalities consumed by the midrange
row assembler. -/

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_2402_2808 :
    Chebyshev.psi (2808 : Real) - Chebyshev.theta 2808 -
        Chebyshev.theta (Real.sqrt (2808 : Real)) <
      (1777745 : Real) / 1000000 * (2402 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2808 : Real) / Real.log 2⌋₊ ≤ 11 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2808 : Real) < Real.log ((2 : Real) ^ 12) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 2) (r := 52) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2808 : Real) ^ (1 / (2 : Real))⌋₊ = 52 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2808 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (52 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 3) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2808 : Real) ^ (1 / (3 : Real))⌋₊ = 14 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2808 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 4) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2808 : Real) ^ (1 / (4 : Real))⌋₊ = 7 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2808 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 5) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2808 : Real) ^ (1 / (5 : Real))⌋₊ = 4 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2808 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 6) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2808 : Real) ^ (1 / (6 : Real))⌋₊ = 3 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2808 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2808 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2808 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2808 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2808 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2808 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2808 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2808 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2808 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2808) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2808 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2808 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2808 : Real)) =
      Chebyshev.theta (52 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2808 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, hsqrt]
  rw [dusart_theta_nat_52, dusart_theta_nat_14, dusart_theta_nat_7, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2809_3124 :
    Chebyshev.psi (3124 : Real) - Chebyshev.theta 3124 -
        Chebyshev.theta (Real.sqrt (3124 : Real)) <
      (1777745 : Real) / 1000000 * (2809 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (3124 : Real) / Real.log 2⌋₊ ≤ 11 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (3124 : Real) < Real.log ((2 : Real) ^ 12) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 2) (r := 55) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(3124 : Real) ^ (1 / (2 : Real))⌋₊ = 55 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((3124 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (55 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 3) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(3124 : Real) ^ (1 / (3 : Real))⌋₊ = 14 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((3124 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 4) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(3124 : Real) ^ (1 / (4 : Real))⌋₊ = 7 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((3124 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 5) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(3124 : Real) ^ (1 / (5 : Real))⌋₊ = 4 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((3124 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 6) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(3124 : Real) ^ (1 / (6 : Real))⌋₊ = 3 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((3124 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(3124 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((3124 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(3124 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((3124 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(3124 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((3124 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(3124 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((3124 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3124) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(3124 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((3124 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (3124 : Real)) =
      Chebyshev.theta (55 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (3124 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, hsqrt]
  rw [dusart_theta_nat_55, dusart_theta_nat_14, dusart_theta_nat_7, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_3125_3480 :
    Chebyshev.psi (3480 : Real) - Chebyshev.theta 3480 -
        Chebyshev.theta (Real.sqrt (3480 : Real)) <
      (1777745 : Real) / 1000000 * (3125 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (3480 : Real) / Real.log 2⌋₊ ≤ 11 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (3480 : Real) < Real.log ((2 : Real) ^ 12) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 2) (r := 58) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(3480 : Real) ^ (1 / (2 : Real))⌋₊ = 58 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((3480 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (58 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 3) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(3480 : Real) ^ (1 / (3 : Real))⌋₊ = 15 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((3480 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 4) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(3480 : Real) ^ (1 / (4 : Real))⌋₊ = 7 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((3480 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(3480 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((3480 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 6) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(3480 : Real) ^ (1 / (6 : Real))⌋₊ = 3 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((3480 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(3480 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((3480 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(3480 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((3480 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(3480 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((3480 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(3480 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((3480 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3480) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(3480 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((3480 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (3480 : Real)) =
      Chebyshev.theta (58 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (3480 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, hsqrt]
  rw [dusart_theta_nat_58, dusart_theta_nat_15, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_3481_3720 :
    Chebyshev.psi (3720 : Real) - Chebyshev.theta 3720 -
        Chebyshev.theta (Real.sqrt (3720 : Real)) <
      (1777745 : Real) / 1000000 * (3481 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (3720 : Real) / Real.log 2⌋₊ ≤ 11 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (3720 : Real) < Real.log ((2 : Real) ^ 12) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 2) (r := 60) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(3720 : Real) ^ (1 / (2 : Real))⌋₊ = 60 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((3720 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (60 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 3) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(3720 : Real) ^ (1 / (3 : Real))⌋₊ = 15 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((3720 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 4) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(3720 : Real) ^ (1 / (4 : Real))⌋₊ = 7 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((3720 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(3720 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((3720 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 6) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(3720 : Real) ^ (1 / (6 : Real))⌋₊ = 3 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((3720 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(3720 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((3720 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(3720 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((3720 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(3720 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((3720 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(3720 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((3720 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3720) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(3720 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((3720 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (3720 : Real)) =
      Chebyshev.theta (60 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (3720 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, hsqrt]
  rw [dusart_theta_nat_60, dusart_theta_nat_15, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_3721_4488 :
    Chebyshev.psi (4488 : Real) - Chebyshev.theta 4488 -
        Chebyshev.theta (Real.sqrt (4488 : Real)) <
      (1777745 : Real) / 1000000 * (3721 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (4488 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (4488 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 2) (r := 66) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(4488 : Real) ^ (1 / (2 : Real))⌋₊ = 66 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((4488 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (66 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 3) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(4488 : Real) ^ (1 / (3 : Real))⌋₊ = 16 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((4488 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(4488 : Real) ^ (1 / (4 : Real))⌋₊ = 8 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((4488 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(4488 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((4488 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(4488 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((4488 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(4488 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((4488 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(4488 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((4488 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(4488 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((4488 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(4488 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((4488 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(4488 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((4488 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(4488 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((4488 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (4488 : Real)) =
      Chebyshev.theta (66 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (4488 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_66, dusart_theta_nat_16, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_4489_5040 :
    Chebyshev.psi (5040 : Real) - Chebyshev.theta 5040 -
        Chebyshev.theta (Real.sqrt (5040 : Real)) <
      (1777745 : Real) / 1000000 * (4489 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (5040 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (5040 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 2) (r := 70) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(5040 : Real) ^ (1 / (2 : Real))⌋₊ = 70 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((5040 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (70 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 3) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(5040 : Real) ^ (1 / (3 : Real))⌋₊ = 17 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((5040 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(5040 : Real) ^ (1 / (4 : Real))⌋₊ = 8 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((5040 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(5040 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((5040 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(5040 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((5040 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(5040 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((5040 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(5040 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((5040 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(5040 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((5040 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(5040 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((5040 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(5040 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((5040 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(5040 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((5040 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (5040 : Real)) =
      Chebyshev.theta (70 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (5040 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_70, dusart_theta_nat_17, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_5041_5328 :
    Chebyshev.psi (5328 : Real) - Chebyshev.theta 5328 -
        Chebyshev.theta (Real.sqrt (5328 : Real)) <
      (1777745 : Real) / 1000000 * (5041 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (5328 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (5328 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 2) (r := 72) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(5328 : Real) ^ (1 / (2 : Real))⌋₊ = 72 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((5328 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (72 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 3) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(5328 : Real) ^ (1 / (3 : Real))⌋₊ = 17 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((5328 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(5328 : Real) ^ (1 / (4 : Real))⌋₊ = 8 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((5328 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(5328 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((5328 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(5328 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((5328 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(5328 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((5328 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(5328 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((5328 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(5328 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((5328 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(5328 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((5328 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(5328 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((5328 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(5328 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((5328 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (5328 : Real)) =
      Chebyshev.theta (72 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (5328 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_72, dusart_theta_nat_17, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_5329_6240 :
    Chebyshev.psi (6240 : Real) - Chebyshev.theta 6240 -
        Chebyshev.theta (Real.sqrt (6240 : Real)) <
      (1777745 : Real) / 1000000 * (5329 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6240 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6240 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 2) (r := 78) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6240 : Real) ^ (1 / (2 : Real))⌋₊ = 78 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6240 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (78 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 3) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6240 : Real) ^ (1 / (3 : Real))⌋₊ = 18 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6240 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6240 : Real) ^ (1 / (4 : Real))⌋₊ = 8 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6240 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6240 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6240 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6240 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6240 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6240 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6240 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6240 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6240 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6240 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6240 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6240 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6240 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6240 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6240 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6240 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6240 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6240 : Real)) =
      Chebyshev.theta (78 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6240 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_78, dusart_theta_nat_18, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_6241_6858 :
    Chebyshev.psi (6858 : Real) - Chebyshev.theta 6858 -
        Chebyshev.theta (Real.sqrt (6858 : Real)) <
      (1777745 : Real) / 1000000 * (6241 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6858 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6858 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 2) (r := 82) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6858 : Real) ^ (1 / (2 : Real))⌋₊ = 82 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6858 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (82 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 3) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6858 : Real) ^ (1 / (3 : Real))⌋₊ = 18 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6858 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 4) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6858 : Real) ^ (1 / (4 : Real))⌋₊ = 9 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6858 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6858 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6858 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6858 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6858 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6858 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6858 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6858 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6858 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6858 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6858 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6858 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6858 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6858 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6858 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6858 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6858 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6858 : Real)) =
      Chebyshev.theta (82 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6858 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_82, dusart_theta_nat_18, dusart_theta_nat_9, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_6859_6888 :
    Chebyshev.psi (6888 : Real) - Chebyshev.theta 6888 -
        Chebyshev.theta (Real.sqrt (6888 : Real)) <
      (1777745 : Real) / 1000000 * (6859 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6888 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6888 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 2) (r := 82) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6888 : Real) ^ (1 / (2 : Real))⌋₊ = 82 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6888 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (82 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 3) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6888 : Real) ^ (1 / (3 : Real))⌋₊ = 19 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6888 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 4) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6888 : Real) ^ (1 / (4 : Real))⌋₊ = 9 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6888 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6888 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6888 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6888 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6888 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6888 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6888 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6888 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6888 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6888 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6888 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6888 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6888 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6888 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6888 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6888 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6888 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6888 : Real)) =
      Chebyshev.theta (82 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6888 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_82, dusart_theta_nat_19, dusart_theta_nat_9, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_6889_7920 :
    Chebyshev.psi (7920 : Real) - Chebyshev.theta 7920 -
        Chebyshev.theta (Real.sqrt (7920 : Real)) <
      (1777745 : Real) / 1000000 * (6889 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (7920 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (7920 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 2) (r := 88) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(7920 : Real) ^ (1 / (2 : Real))⌋₊ = 88 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((7920 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (88 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 3) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(7920 : Real) ^ (1 / (3 : Real))⌋₊ = 19 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((7920 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 4) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(7920 : Real) ^ (1 / (4 : Real))⌋₊ = 9 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((7920 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(7920 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((7920 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(7920 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((7920 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(7920 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((7920 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(7920 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((7920 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(7920 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((7920 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(7920 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((7920 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(7920 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((7920 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(7920 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((7920 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (7920 : Real)) =
      Chebyshev.theta (88 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (7920 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_88, dusart_theta_nat_19, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_7921_9408 :
    Chebyshev.psi (9408 : Real) - Chebyshev.theta 9408 -
        Chebyshev.theta (Real.sqrt (9408 : Real)) <
      (1777745 : Real) / 1000000 * (7921 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (9408 : Real) / Real.log 2⌋₊ ≤ 13 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (9408 : Real) < Real.log ((2 : Real) ^ 14) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 2) (r := 96) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(9408 : Real) ^ (1 / (2 : Real))⌋₊ = 96 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((9408 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (96 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 3) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(9408 : Real) ^ (1 / (3 : Real))⌋₊ = 21 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((9408 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 4) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(9408 : Real) ^ (1 / (4 : Real))⌋₊ = 9 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((9408 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(9408 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((9408 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(9408 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((9408 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(9408 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((9408 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(9408 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((9408 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(9408 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((9408 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(9408 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((9408 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(9408 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((9408 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(9408 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((9408 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(9408 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((9408 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (9408 : Real)) =
      Chebyshev.theta (96 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (9408 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, hsqrt]
  rw [dusart_theta_nat_96, dusart_theta_nat_21, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_9409_10200 :
    Chebyshev.psi (10200 : Real) - Chebyshev.theta 10200 -
        Chebyshev.theta (Real.sqrt (10200 : Real)) <
      (1777745 : Real) / 1000000 * (9409 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (10200 : Real) / Real.log 2⌋₊ ≤ 13 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (10200 : Real) < Real.log ((2 : Real) ^ 14) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 2) (r := 100) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(10200 : Real) ^ (1 / (2 : Real))⌋₊ = 100 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((10200 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (100 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 3) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(10200 : Real) ^ (1 / (3 : Real))⌋₊ = 21 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((10200 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 4) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(10200 : Real) ^ (1 / (4 : Real))⌋₊ = 10 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((10200 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(10200 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((10200 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(10200 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((10200 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(10200 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((10200 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(10200 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((10200 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(10200 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((10200 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(10200 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((10200 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(10200 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((10200 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(10200 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((10200 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10200) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(10200 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((10200 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (10200 : Real)) =
      Chebyshev.theta (100 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (10200 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, hsqrt]
  rw [dusart_theta_nat_100, dusart_theta_nat_21, dusart_theta_nat_10, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_10201_11448 :
    Chebyshev.psi (11448 : Real) - Chebyshev.theta 11448 -
        Chebyshev.theta (Real.sqrt (11448 : Real)) <
      (1777745 : Real) / 1000000 * (10201 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (11448 : Real) / Real.log 2⌋₊ ≤ 13 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (11448 : Real) < Real.log ((2 : Real) ^ 14) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 2) (r := 106) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(11448 : Real) ^ (1 / (2 : Real))⌋₊ = 106 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((11448 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (106 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 3) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(11448 : Real) ^ (1 / (3 : Real))⌋₊ = 22 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((11448 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 4) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(11448 : Real) ^ (1 / (4 : Real))⌋₊ = 10 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((11448 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(11448 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((11448 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(11448 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((11448 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(11448 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((11448 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(11448 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((11448 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(11448 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((11448 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(11448 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((11448 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(11448 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((11448 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(11448 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((11448 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 11448) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(11448 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((11448 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (11448 : Real)) =
      Chebyshev.theta (106 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (11448 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, hsqrt]
  rw [dusart_theta_nat_106, dusart_theta_nat_22, dusart_theta_nat_10, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_11449_12166 :
    Chebyshev.psi (12166 : Real) - Chebyshev.theta 12166 -
        Chebyshev.theta (Real.sqrt (12166 : Real)) <
      (1777745 : Real) / 1000000 * (11449 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (12166 : Real) / Real.log 2⌋₊ ≤ 13 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (12166 : Real) < Real.log ((2 : Real) ^ 14) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 2) (r := 110) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(12166 : Real) ^ (1 / (2 : Real))⌋₊ = 110 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((12166 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (110 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 3) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(12166 : Real) ^ (1 / (3 : Real))⌋₊ = 22 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((12166 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 4) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(12166 : Real) ^ (1 / (4 : Real))⌋₊ = 10 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((12166 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(12166 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((12166 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(12166 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((12166 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(12166 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((12166 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(12166 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((12166 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(12166 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((12166 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(12166 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((12166 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(12166 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((12166 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(12166 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((12166 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12166) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(12166 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((12166 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (12166 : Real)) =
      Chebyshev.theta (110 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (12166 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, hsqrt]
  rw [dusart_theta_nat_110, dusart_theta_nat_22, dusart_theta_nat_10, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_12167_12768 :
    Chebyshev.psi (12768 : Real) - Chebyshev.theta 12768 -
        Chebyshev.theta (Real.sqrt (12768 : Real)) <
      (1777745 : Real) / 1000000 * (12167 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (12768 : Real) / Real.log 2⌋₊ ≤ 13 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (12768 : Real) < Real.log ((2 : Real) ^ 14) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 2) (r := 112) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(12768 : Real) ^ (1 / (2 : Real))⌋₊ = 112 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((12768 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (112 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 3) (r := 23) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(12768 : Real) ^ (1 / (3 : Real))⌋₊ = 23 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((12768 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (23 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 4) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(12768 : Real) ^ (1 / (4 : Real))⌋₊ = 10 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((12768 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(12768 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((12768 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(12768 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((12768 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(12768 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((12768 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(12768 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((12768 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(12768 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((12768 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(12768 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((12768 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(12768 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((12768 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(12768 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((12768 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 12768) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(12768 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((12768 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (12768 : Real)) =
      Chebyshev.theta (112 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (12768 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, hsqrt]
  rw [dusart_theta_nat_112, dusart_theta_nat_23, dusart_theta_nat_10, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_12769_16128 :
    Chebyshev.psi (16128 : Real) - Chebyshev.theta 16128 -
        Chebyshev.theta (Real.sqrt (16128 : Real)) <
      (1777745 : Real) / 1000000 * (12769 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (16128 : Real) / Real.log 2⌋₊ ≤ 13 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (16128 : Real) < Real.log ((2 : Real) ^ 14) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 2) (r := 126) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(16128 : Real) ^ (1 / (2 : Real))⌋₊ = 126 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((16128 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (126 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 3) (r := 25) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(16128 : Real) ^ (1 / (3 : Real))⌋₊ = 25 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((16128 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (25 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 4) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(16128 : Real) ^ (1 / (4 : Real))⌋₊ = 11 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((16128 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(16128 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((16128 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(16128 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((16128 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(16128 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((16128 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(16128 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((16128 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(16128 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((16128 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(16128 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((16128 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(16128 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((16128 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(16128 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((16128 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 16128) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(16128 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((16128 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (16128 : Real)) =
      Chebyshev.theta (126 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (16128 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, hsqrt]
  rw [dusart_theta_nat_126, dusart_theta_nat_25, dusart_theta_nat_11, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_16129_17160 :
    Chebyshev.psi (17160 : Real) - Chebyshev.theta 17160 -
        Chebyshev.theta (Real.sqrt (17160 : Real)) <
      (1777745 : Real) / 1000000 * (16129 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (17160 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (17160 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 2) (r := 130) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(17160 : Real) ^ (1 / (2 : Real))⌋₊ = 130 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((17160 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (130 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 3) (r := 25) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(17160 : Real) ^ (1 / (3 : Real))⌋₊ = 25 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((17160 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (25 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 4) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(17160 : Real) ^ (1 / (4 : Real))⌋₊ = 11 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((17160 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(17160 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((17160 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(17160 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((17160 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(17160 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((17160 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(17160 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((17160 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(17160 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((17160 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(17160 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((17160 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(17160 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((17160 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(17160 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((17160 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(17160 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((17160 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 17160) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(17160 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((17160 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (17160 : Real)) =
      Chebyshev.theta (130 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (17160 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_130, dusart_theta_nat_25, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_17161_18768 :
    Chebyshev.psi (18768 : Real) - Chebyshev.theta 18768 -
        Chebyshev.theta (Real.sqrt (18768 : Real)) <
      (1777745 : Real) / 1000000 * (17161 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (18768 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (18768 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 2) (r := 136) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(18768 : Real) ^ (1 / (2 : Real))⌋₊ = 136 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((18768 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (136 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 3) (r := 26) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(18768 : Real) ^ (1 / (3 : Real))⌋₊ = 26 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((18768 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (26 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 4) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(18768 : Real) ^ (1 / (4 : Real))⌋₊ = 11 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((18768 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(18768 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((18768 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(18768 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((18768 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(18768 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((18768 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(18768 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((18768 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(18768 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((18768 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(18768 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((18768 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(18768 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((18768 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(18768 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((18768 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(18768 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((18768 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 18768) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(18768 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((18768 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (18768 : Real)) =
      Chebyshev.theta (136 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (18768 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_136, dusart_theta_nat_26, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_18769_19320 :
    Chebyshev.psi (19320 : Real) - Chebyshev.theta 19320 -
        Chebyshev.theta (Real.sqrt (19320 : Real)) <
      (1777745 : Real) / 1000000 * (18769 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (19320 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (19320 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 2) (r := 138) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(19320 : Real) ^ (1 / (2 : Real))⌋₊ = 138 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((19320 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (138 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 3) (r := 26) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(19320 : Real) ^ (1 / (3 : Real))⌋₊ = 26 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((19320 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (26 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 4) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(19320 : Real) ^ (1 / (4 : Real))⌋₊ = 11 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((19320 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(19320 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((19320 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(19320 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((19320 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(19320 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((19320 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(19320 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((19320 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(19320 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((19320 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(19320 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((19320 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(19320 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((19320 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(19320 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((19320 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(19320 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((19320 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 19320) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(19320 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((19320 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (19320 : Real)) =
      Chebyshev.theta (138 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (19320 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_138, dusart_theta_nat_26, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_19321_22200 :
    Chebyshev.psi (22200 : Real) - Chebyshev.theta 22200 -
        Chebyshev.theta (Real.sqrt (22200 : Real)) <
      (1777745 : Real) / 1000000 * (19321 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (22200 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (22200 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 2) (r := 148) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(22200 : Real) ^ (1 / (2 : Real))⌋₊ = 148 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((22200 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (148 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 3) (r := 28) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(22200 : Real) ^ (1 / (3 : Real))⌋₊ = 28 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((22200 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (28 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(22200 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((22200 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(22200 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((22200 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(22200 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((22200 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(22200 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((22200 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(22200 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((22200 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(22200 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((22200 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(22200 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((22200 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(22200 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((22200 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(22200 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((22200 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(22200 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((22200 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(22200 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((22200 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (22200 : Real)) =
      Chebyshev.theta (148 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (22200 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_148, dusart_theta_nat_28, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_22201_24388 :
    Chebyshev.psi (24388 : Real) - Chebyshev.theta 24388 -
        Chebyshev.theta (Real.sqrt (24388 : Real)) <
      (1777745 : Real) / 1000000 * (22201 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (24388 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (24388 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 2) (r := 156) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(24388 : Real) ^ (1 / (2 : Real))⌋₊ = 156 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((24388 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (156 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 3) (r := 28) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(24388 : Real) ^ (1 / (3 : Real))⌋₊ = 28 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((24388 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (28 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(24388 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((24388 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(24388 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((24388 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(24388 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((24388 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(24388 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((24388 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(24388 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((24388 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(24388 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((24388 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(24388 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((24388 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(24388 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((24388 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(24388 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((24388 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(24388 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((24388 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(24388 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((24388 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (24388 : Real)) =
      Chebyshev.theta (156 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (24388 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_156, dusart_theta_nat_28, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_24389_24648 :
    Chebyshev.psi (24648 : Real) - Chebyshev.theta 24648 -
        Chebyshev.theta (Real.sqrt (24648 : Real)) <
      (1777745 : Real) / 1000000 * (24389 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (24648 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (24648 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 2) (r := 156) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(24648 : Real) ^ (1 / (2 : Real))⌋₊ = 156 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((24648 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (156 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 3) (r := 29) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(24648 : Real) ^ (1 / (3 : Real))⌋₊ = 29 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((24648 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (29 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(24648 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((24648 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(24648 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((24648 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(24648 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((24648 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(24648 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((24648 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(24648 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((24648 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(24648 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((24648 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(24648 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((24648 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(24648 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((24648 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(24648 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((24648 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(24648 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((24648 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(24648 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((24648 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (24648 : Real)) =
      Chebyshev.theta (156 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (24648 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_156, dusart_theta_nat_29, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_24649_26568 :
    Chebyshev.psi (26568 : Real) - Chebyshev.theta 26568 -
        Chebyshev.theta (Real.sqrt (26568 : Real)) <
      (1777745 : Real) / 1000000 * (24649 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (26568 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (26568 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 2) (r := 162) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(26568 : Real) ^ (1 / (2 : Real))⌋₊ = 162 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((26568 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (162 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 3) (r := 29) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(26568 : Real) ^ (1 / (3 : Real))⌋₊ = 29 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((26568 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (29 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(26568 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((26568 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(26568 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((26568 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(26568 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((26568 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(26568 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((26568 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(26568 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((26568 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(26568 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((26568 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(26568 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((26568 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(26568 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((26568 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(26568 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((26568 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(26568 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((26568 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(26568 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((26568 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (26568 : Real)) =
      Chebyshev.theta (162 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (26568 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_162, dusart_theta_nat_29, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_26569_28560 :
    Chebyshev.psi (28560 : Real) - Chebyshev.theta 28560 -
        Chebyshev.theta (Real.sqrt (28560 : Real)) <
      (1777745 : Real) / 1000000 * (26569 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (28560 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (28560 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 2) (r := 168) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(28560 : Real) ^ (1 / (2 : Real))⌋₊ = 168 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((28560 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (168 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 3) (r := 30) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(28560 : Real) ^ (1 / (3 : Real))⌋₊ = 30 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((28560 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (30 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(28560 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((28560 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(28560 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((28560 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(28560 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((28560 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(28560 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((28560 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(28560 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((28560 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(28560 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((28560 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(28560 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((28560 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(28560 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((28560 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(28560 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((28560 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(28560 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((28560 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 28560) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(28560 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((28560 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (28560 : Real)) =
      Chebyshev.theta (168 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (28560 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_168, dusart_theta_nat_30, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_28561_29928 :
    Chebyshev.psi (29928 : Real) - Chebyshev.theta 29928 -
        Chebyshev.theta (Real.sqrt (29928 : Real)) <
      (1777745 : Real) / 1000000 * (28561 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (29928 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (29928 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 2) (r := 172) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(29928 : Real) ^ (1 / (2 : Real))⌋₊ = 172 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((29928 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (172 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 3) (r := 31) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(29928 : Real) ^ (1 / (3 : Real))⌋₊ = 31 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((29928 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (31 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 4) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(29928 : Real) ^ (1 / (4 : Real))⌋₊ = 13 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((29928 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(29928 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((29928 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(29928 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((29928 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(29928 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((29928 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(29928 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((29928 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(29928 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((29928 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(29928 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((29928 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(29928 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((29928 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(29928 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((29928 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(29928 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((29928 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 29928) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(29928 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((29928 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (29928 : Real)) =
      Chebyshev.theta (172 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (29928 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_172, dusart_theta_nat_31, dusart_theta_nat_13, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_29929_32040 :
    Chebyshev.psi (32040 : Real) - Chebyshev.theta 32040 -
        Chebyshev.theta (Real.sqrt (32040 : Real)) <
      (1777745 : Real) / 1000000 * (29929 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (32040 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (32040 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 2) (r := 178) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(32040 : Real) ^ (1 / (2 : Real))⌋₊ = 178 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((32040 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (178 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 3) (r := 31) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(32040 : Real) ^ (1 / (3 : Real))⌋₊ = 31 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((32040 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (31 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 4) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(32040 : Real) ^ (1 / (4 : Real))⌋₊ = 13 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((32040 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(32040 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((32040 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(32040 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((32040 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(32040 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((32040 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(32040 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((32040 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(32040 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((32040 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(32040 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((32040 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(32040 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((32040 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(32040 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((32040 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(32040 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((32040 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32040) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(32040 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((32040 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (32040 : Real)) =
      Chebyshev.theta (178 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (32040 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_178, dusart_theta_nat_31, dusart_theta_nat_13, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_32041_32760 :
    Chebyshev.psi (32760 : Real) - Chebyshev.theta 32760 -
        Chebyshev.theta (Real.sqrt (32760 : Real)) <
      (1777745 : Real) / 1000000 * (32041 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (32760 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (32760 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 2) (r := 180) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(32760 : Real) ^ (1 / (2 : Real))⌋₊ = 180 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((32760 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (180 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 3) (r := 31) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(32760 : Real) ^ (1 / (3 : Real))⌋₊ = 31 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((32760 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (31 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 4) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(32760 : Real) ^ (1 / (4 : Real))⌋₊ = 13 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((32760 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(32760 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((32760 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(32760 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((32760 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(32760 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((32760 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(32760 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((32760 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(32760 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((32760 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(32760 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((32760 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(32760 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((32760 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(32760 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((32760 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(32760 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((32760 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 32760) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(32760 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((32760 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (32760 : Real)) =
      Chebyshev.theta (180 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (32760 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_180, dusart_theta_nat_31, dusart_theta_nat_13, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_32761_36480 :
    Chebyshev.psi (36480 : Real) - Chebyshev.theta 36480 -
        Chebyshev.theta (Real.sqrt (36480 : Real)) <
      (1777745 : Real) / 1000000 * (32761 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (36480 : Real) / Real.log 2⌋₊ ≤ 15 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (36480 : Real) < Real.log ((2 : Real) ^ 16) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 2) (r := 190) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(36480 : Real) ^ (1 / (2 : Real))⌋₊ = 190 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((36480 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (190 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 3) (r := 33) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(36480 : Real) ^ (1 / (3 : Real))⌋₊ = 33 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((36480 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (33 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 4) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(36480 : Real) ^ (1 / (4 : Real))⌋₊ = 13 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((36480 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 5) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(36480 : Real) ^ (1 / (5 : Real))⌋₊ = 8 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((36480 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(36480 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((36480 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(36480 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((36480 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(36480 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((36480 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(36480 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((36480 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(36480 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((36480 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(36480 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((36480 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(36480 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((36480 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(36480 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((36480 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(36480 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((36480 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 36480) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(36480 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((36480 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (36480 : Real)) =
      Chebyshev.theta (190 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (36480 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, hsqrt]
  rw [dusart_theta_nat_190, dusart_theta_nat_33, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_36481_37248 :
    Chebyshev.psi (37248 : Real) - Chebyshev.theta 37248 -
        Chebyshev.theta (Real.sqrt (37248 : Real)) <
      (1777745 : Real) / 1000000 * (36481 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (37248 : Real) / Real.log 2⌋₊ ≤ 15 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (37248 : Real) < Real.log ((2 : Real) ^ 16) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 2) (r := 192) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(37248 : Real) ^ (1 / (2 : Real))⌋₊ = 192 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((37248 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (192 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 3) (r := 33) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(37248 : Real) ^ (1 / (3 : Real))⌋₊ = 33 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((37248 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (33 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 4) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(37248 : Real) ^ (1 / (4 : Real))⌋₊ = 13 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((37248 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 5) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(37248 : Real) ^ (1 / (5 : Real))⌋₊ = 8 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((37248 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(37248 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((37248 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(37248 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((37248 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(37248 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((37248 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(37248 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((37248 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(37248 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((37248 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(37248 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((37248 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(37248 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((37248 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(37248 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((37248 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(37248 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((37248 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 37248) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(37248 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((37248 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (37248 : Real)) =
      Chebyshev.theta (192 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (37248 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, hsqrt]
  rw [dusart_theta_nat_192, dusart_theta_nat_33, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_37249_38808 :
    Chebyshev.psi (38808 : Real) - Chebyshev.theta 38808 -
        Chebyshev.theta (Real.sqrt (38808 : Real)) <
      (1777745 : Real) / 1000000 * (37249 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (38808 : Real) / Real.log 2⌋₊ ≤ 15 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (38808 : Real) < Real.log ((2 : Real) ^ 16) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 2) (r := 196) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(38808 : Real) ^ (1 / (2 : Real))⌋₊ = 196 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((38808 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (196 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 3) (r := 33) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(38808 : Real) ^ (1 / (3 : Real))⌋₊ = 33 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((38808 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (33 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 4) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(38808 : Real) ^ (1 / (4 : Real))⌋₊ = 14 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((38808 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 5) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(38808 : Real) ^ (1 / (5 : Real))⌋₊ = 8 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((38808 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(38808 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((38808 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(38808 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((38808 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(38808 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((38808 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(38808 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((38808 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(38808 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((38808 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(38808 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((38808 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(38808 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((38808 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(38808 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((38808 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(38808 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((38808 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 38808) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(38808 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((38808 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (38808 : Real)) =
      Chebyshev.theta (196 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (38808 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, hsqrt]
  rw [dusart_theta_nat_196, dusart_theta_nat_33, dusart_theta_nat_14, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_38809_44520 :
    Chebyshev.psi (44520 : Real) - Chebyshev.theta 44520 -
        Chebyshev.theta (Real.sqrt (44520 : Real)) <
      (1777745 : Real) / 1000000 * (38809 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (44520 : Real) / Real.log 2⌋₊ ≤ 15 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (44520 : Real) < Real.log ((2 : Real) ^ 16) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 2) (r := 210) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(44520 : Real) ^ (1 / (2 : Real))⌋₊ = 210 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((44520 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (210 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 3) (r := 35) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(44520 : Real) ^ (1 / (3 : Real))⌋₊ = 35 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((44520 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (35 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 4) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(44520 : Real) ^ (1 / (4 : Real))⌋₊ = 14 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((44520 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 5) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(44520 : Real) ^ (1 / (5 : Real))⌋₊ = 8 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((44520 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(44520 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((44520 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(44520 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((44520 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(44520 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((44520 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(44520 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((44520 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(44520 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((44520 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(44520 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((44520 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(44520 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((44520 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(44520 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((44520 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(44520 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((44520 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 44520) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(44520 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((44520 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (44520 : Real)) =
      Chebyshev.theta (210 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (44520 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, hsqrt]
  rw [dusart_theta_nat_210, dusart_theta_nat_35, dusart_theta_nat_14, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_44521_50652 :
    Chebyshev.psi (50652 : Real) - Chebyshev.theta 50652 -
        Chebyshev.theta (Real.sqrt (50652 : Real)) <
      (1777745 : Real) / 1000000 * (44521 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (50652 : Real) / Real.log 2⌋₊ ≤ 15 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (50652 : Real) < Real.log ((2 : Real) ^ 16) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 2) (r := 225) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(50652 : Real) ^ (1 / (2 : Real))⌋₊ = 225 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((50652 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (225 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 3) (r := 36) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(50652 : Real) ^ (1 / (3 : Real))⌋₊ = 36 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((50652 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (36 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 4) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(50652 : Real) ^ (1 / (4 : Real))⌋₊ = 15 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((50652 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 5) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(50652 : Real) ^ (1 / (5 : Real))⌋₊ = 8 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((50652 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(50652 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((50652 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(50652 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((50652 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(50652 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((50652 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(50652 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((50652 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(50652 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((50652 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(50652 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((50652 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(50652 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((50652 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(50652 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((50652 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(50652 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((50652 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 50652) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(50652 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((50652 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (50652 : Real)) =
      Chebyshev.theta (225 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (50652 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, hsqrt]
  rw [dusart_theta_nat_225, dusart_theta_nat_36, dusart_theta_nat_15, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_50653_52440 :
    Chebyshev.psi (52440 : Real) - Chebyshev.theta 52440 -
        Chebyshev.theta (Real.sqrt (52440 : Real)) <
      (1777745 : Real) / 1000000 * (50653 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (52440 : Real) / Real.log 2⌋₊ ≤ 15 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (52440 : Real) < Real.log ((2 : Real) ^ 16) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 2) (r := 228) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(52440 : Real) ^ (1 / (2 : Real))⌋₊ = 228 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((52440 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (228 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 3) (r := 37) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(52440 : Real) ^ (1 / (3 : Real))⌋₊ = 37 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((52440 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (37 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 4) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(52440 : Real) ^ (1 / (4 : Real))⌋₊ = 15 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((52440 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 5) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(52440 : Real) ^ (1 / (5 : Real))⌋₊ = 8 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((52440 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(52440 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((52440 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(52440 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((52440 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(52440 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((52440 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(52440 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((52440 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(52440 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((52440 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(52440 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((52440 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(52440 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((52440 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(52440 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((52440 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(52440 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((52440 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 52440) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(52440 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((52440 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (52440 : Real)) =
      Chebyshev.theta (228 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (52440 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, hsqrt]
  rw [dusart_theta_nat_228, dusart_theta_nat_37, dusart_theta_nat_15, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_52441_57120 :
    Chebyshev.psi (57120 : Real) - Chebyshev.theta 57120 -
        Chebyshev.theta (Real.sqrt (57120 : Real)) <
      (1777745 : Real) / 1000000 * (52441 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (57120 : Real) / Real.log 2⌋₊ ≤ 15 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (57120 : Real) < Real.log ((2 : Real) ^ 16) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 2) (r := 238) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(57120 : Real) ^ (1 / (2 : Real))⌋₊ = 238 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((57120 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (238 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 3) (r := 38) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(57120 : Real) ^ (1 / (3 : Real))⌋₊ = 38 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((57120 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (38 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 4) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(57120 : Real) ^ (1 / (4 : Real))⌋₊ = 15 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((57120 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 5) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(57120 : Real) ^ (1 / (5 : Real))⌋₊ = 8 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((57120 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(57120 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((57120 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(57120 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((57120 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(57120 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((57120 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(57120 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((57120 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(57120 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((57120 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(57120 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((57120 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(57120 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((57120 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(57120 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((57120 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(57120 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((57120 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 57120) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(57120 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((57120 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (57120 : Real)) =
      Chebyshev.theta (238 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (57120 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, hsqrt]
  rw [dusart_theta_nat_238, dusart_theta_nat_38, dusart_theta_nat_15, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_57121_63000 :
    Chebyshev.psi (63000 : Real) - Chebyshev.theta 63000 -
        Chebyshev.theta (Real.sqrt (63000 : Real)) <
      (1777745 : Real) / 1000000 * (57121 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (63000 : Real) / Real.log 2⌋₊ ≤ 15 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (63000 : Real) < Real.log ((2 : Real) ^ 16) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 2) (r := 250) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(63000 : Real) ^ (1 / (2 : Real))⌋₊ = 250 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((63000 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (250 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 3) (r := 39) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(63000 : Real) ^ (1 / (3 : Real))⌋₊ = 39 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((63000 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (39 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 4) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(63000 : Real) ^ (1 / (4 : Real))⌋₊ = 15 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((63000 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(63000 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((63000 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(63000 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((63000 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(63000 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((63000 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(63000 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((63000 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(63000 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((63000 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(63000 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((63000 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(63000 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((63000 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(63000 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((63000 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(63000 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((63000 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(63000 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((63000 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 63000) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(63000 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((63000 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (63000 : Real)) =
      Chebyshev.theta (250 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (63000 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, hsqrt]
  rw [dusart_theta_nat_250, dusart_theta_nat_39, dusart_theta_nat_15, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_63001_69168 :
    Chebyshev.psi (69168 : Real) - Chebyshev.theta 69168 -
        Chebyshev.theta (Real.sqrt (69168 : Real)) <
      (1777745 : Real) / 1000000 * (63001 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (69168 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (69168 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 2) (r := 262) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(69168 : Real) ^ (1 / (2 : Real))⌋₊ = 262 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((69168 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (262 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 3) (r := 41) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(69168 : Real) ^ (1 / (3 : Real))⌋₊ = 41 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((69168 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (41 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 4) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(69168 : Real) ^ (1 / (4 : Real))⌋₊ = 16 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((69168 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(69168 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((69168 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(69168 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((69168 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(69168 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((69168 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(69168 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((69168 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(69168 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((69168 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(69168 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((69168 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(69168 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((69168 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(69168 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((69168 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(69168 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((69168 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(69168 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((69168 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(69168 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((69168 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 69168) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(69168 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((69168 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (69168 : Real)) =
      Chebyshev.theta (262 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (69168 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_262, dusart_theta_nat_41, dusart_theta_nat_16, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_69169_73440 :
    Chebyshev.psi (73440 : Real) - Chebyshev.theta 73440 -
        Chebyshev.theta (Real.sqrt (73440 : Real)) <
      (1777745 : Real) / 1000000 * (69169 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (73440 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (73440 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 2) (r := 270) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(73440 : Real) ^ (1 / (2 : Real))⌋₊ = 270 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((73440 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (270 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 3) (r := 41) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(73440 : Real) ^ (1 / (3 : Real))⌋₊ = 41 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((73440 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (41 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 4) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(73440 : Real) ^ (1 / (4 : Real))⌋₊ = 16 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((73440 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(73440 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((73440 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(73440 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((73440 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(73440 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((73440 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(73440 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((73440 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(73440 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((73440 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(73440 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((73440 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(73440 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((73440 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(73440 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((73440 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(73440 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((73440 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(73440 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((73440 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(73440 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((73440 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 73440) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(73440 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((73440 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (73440 : Real)) =
      Chebyshev.theta (270 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (73440 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_270, dusart_theta_nat_41, dusart_theta_nat_16, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_73441_78960 :
    Chebyshev.psi (78960 : Real) - Chebyshev.theta 78960 -
        Chebyshev.theta (Real.sqrt (78960 : Real)) <
      (1777745 : Real) / 1000000 * (73441 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (78960 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (78960 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 2) (r := 280) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(78960 : Real) ^ (1 / (2 : Real))⌋₊ = 280 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((78960 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (280 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 3) (r := 42) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(78960 : Real) ^ (1 / (3 : Real))⌋₊ = 42 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((78960 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (42 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 4) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(78960 : Real) ^ (1 / (4 : Real))⌋₊ = 16 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((78960 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(78960 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((78960 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(78960 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((78960 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(78960 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((78960 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(78960 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((78960 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(78960 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((78960 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(78960 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((78960 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(78960 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((78960 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(78960 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((78960 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(78960 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((78960 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(78960 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((78960 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(78960 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((78960 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 78960) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(78960 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((78960 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (78960 : Real)) =
      Chebyshev.theta (280 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (78960 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_280, dusart_theta_nat_42, dusart_theta_nat_16, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_78961_83520 :
    Chebyshev.psi (83520 : Real) - Chebyshev.theta 83520 -
        Chebyshev.theta (Real.sqrt (83520 : Real)) <
      (1777745 : Real) / 1000000 * (78961 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (83520 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (83520 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 2) (r := 288) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(83520 : Real) ^ (1 / (2 : Real))⌋₊ = 288 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((83520 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (288 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 3) (r := 43) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(83520 : Real) ^ (1 / (3 : Real))⌋₊ = 43 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((83520 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (43 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 4) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(83520 : Real) ^ (1 / (4 : Real))⌋₊ = 16 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((83520 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(83520 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((83520 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(83520 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((83520 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(83520 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((83520 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(83520 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((83520 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(83520 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((83520 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(83520 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((83520 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(83520 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((83520 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(83520 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((83520 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(83520 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((83520 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(83520 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((83520 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(83520 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((83520 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 83520) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(83520 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((83520 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (83520 : Real)) =
      Chebyshev.theta (288 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (83520 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_288, dusart_theta_nat_43, dusart_theta_nat_16, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_83521_94248 :
    Chebyshev.psi (94248 : Real) - Chebyshev.theta 94248 -
        Chebyshev.theta (Real.sqrt (94248 : Real)) <
      (1777745 : Real) / 1000000 * (83521 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (94248 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (94248 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 2) (r := 306) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(94248 : Real) ^ (1 / (2 : Real))⌋₊ = 306 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((94248 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (306 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 3) (r := 45) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(94248 : Real) ^ (1 / (3 : Real))⌋₊ = 45 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((94248 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (45 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 4) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(94248 : Real) ^ (1 / (4 : Real))⌋₊ = 17 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((94248 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(94248 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((94248 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(94248 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((94248 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(94248 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((94248 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(94248 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((94248 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(94248 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((94248 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(94248 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((94248 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(94248 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((94248 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(94248 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((94248 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(94248 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((94248 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(94248 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((94248 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(94248 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((94248 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(94248 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((94248 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (94248 : Real)) =
      Chebyshev.theta (306 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (94248 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_306, dusart_theta_nat_45, dusart_theta_nat_17, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_94249_97968 :
    Chebyshev.psi (97968 : Real) - Chebyshev.theta 97968 -
        Chebyshev.theta (Real.sqrt (97968 : Real)) <
      (1777745 : Real) / 1000000 * (94249 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (97968 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (97968 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 2) (r := 312) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(97968 : Real) ^ (1 / (2 : Real))⌋₊ = 312 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((97968 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (312 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 3) (r := 46) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(97968 : Real) ^ (1 / (3 : Real))⌋₊ = 46 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((97968 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (46 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 4) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(97968 : Real) ^ (1 / (4 : Real))⌋₊ = 17 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((97968 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(97968 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((97968 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(97968 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((97968 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(97968 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((97968 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(97968 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((97968 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(97968 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((97968 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(97968 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((97968 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(97968 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((97968 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(97968 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((97968 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(97968 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((97968 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(97968 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((97968 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(97968 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((97968 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(97968 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((97968 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (97968 : Real)) =
      Chebyshev.theta (312 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (97968 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_312, dusart_theta_nat_46, dusart_theta_nat_17, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_97969_109560 :
    Chebyshev.psi (109560 : Real) - Chebyshev.theta 109560 -
        Chebyshev.theta (Real.sqrt (109560 : Real)) <
      (1777745 : Real) / 1000000 * (97969 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (109560 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (109560 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 2) (r := 330) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(109560 : Real) ^ (1 / (2 : Real))⌋₊ = 330 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((109560 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (330 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 3) (r := 47) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(109560 : Real) ^ (1 / (3 : Real))⌋₊ = 47 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((109560 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (47 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 4) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(109560 : Real) ^ (1 / (4 : Real))⌋₊ = 18 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((109560 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(109560 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((109560 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(109560 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((109560 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(109560 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((109560 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(109560 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((109560 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(109560 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((109560 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(109560 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((109560 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(109560 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((109560 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(109560 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((109560 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(109560 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((109560 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(109560 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((109560 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(109560 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((109560 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(109560 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((109560 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (109560 : Real)) =
      Chebyshev.theta (330 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (109560 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_330, dusart_theta_nat_47, dusart_theta_nat_18, dusart_theta_nat_10, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_109561_120408 :
    Chebyshev.psi (120408 : Real) - Chebyshev.theta 120408 -
        Chebyshev.theta (Real.sqrt (120408 : Real)) <
      (1777745 : Real) / 1000000 * (109561 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (120408 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (120408 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 2) (r := 346) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(120408 : Real) ^ (1 / (2 : Real))⌋₊ = 346 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((120408 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (346 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 3) (r := 49) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(120408 : Real) ^ (1 / (3 : Real))⌋₊ = 49 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((120408 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (49 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 4) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(120408 : Real) ^ (1 / (4 : Real))⌋₊ = 18 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((120408 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(120408 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((120408 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(120408 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((120408 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(120408 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((120408 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(120408 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((120408 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(120408 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((120408 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(120408 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((120408 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(120408 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((120408 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(120408 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((120408 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(120408 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((120408 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(120408 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((120408 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(120408 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((120408 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(120408 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((120408 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (120408 : Real)) =
      Chebyshev.theta (346 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (120408 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_346, dusart_theta_nat_49, dusart_theta_nat_18, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_120409_124608 :
    Chebyshev.psi (124608 : Real) - Chebyshev.theta 124608 -
        Chebyshev.theta (Real.sqrt (124608 : Real)) <
      (1777745 : Real) / 1000000 * (120409 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (124608 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (124608 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 2) (r := 352) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(124608 : Real) ^ (1 / (2 : Real))⌋₊ = 352 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((124608 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (352 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 3) (r := 49) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(124608 : Real) ^ (1 / (3 : Real))⌋₊ = 49 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((124608 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (49 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 4) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(124608 : Real) ^ (1 / (4 : Real))⌋₊ = 18 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((124608 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(124608 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((124608 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(124608 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((124608 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(124608 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((124608 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(124608 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((124608 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(124608 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((124608 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(124608 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((124608 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(124608 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((124608 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(124608 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((124608 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(124608 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((124608 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(124608 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((124608 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(124608 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((124608 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 124608) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(124608 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((124608 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (124608 : Real)) =
      Chebyshev.theta (352 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (124608 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_352, dusart_theta_nat_49, dusart_theta_nat_18, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_124609_134688 :
    Chebyshev.psi (134688 : Real) - Chebyshev.theta 134688 -
        Chebyshev.theta (Real.sqrt (134688 : Real)) <
      (1777745 : Real) / 1000000 * (124609 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (134688 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (134688 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 2) (r := 366) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(134688 : Real) ^ (1 / (2 : Real))⌋₊ = 366 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((134688 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (366 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 3) (r := 51) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(134688 : Real) ^ (1 / (3 : Real))⌋₊ = 51 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((134688 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (51 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 4) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(134688 : Real) ^ (1 / (4 : Real))⌋₊ = 19 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((134688 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(134688 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((134688 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(134688 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((134688 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(134688 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((134688 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(134688 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((134688 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(134688 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((134688 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(134688 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((134688 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(134688 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((134688 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(134688 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((134688 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(134688 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((134688 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(134688 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((134688 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(134688 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((134688 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(134688 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((134688 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 134688) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(134688 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((134688 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (134688 : Real)) =
      Chebyshev.theta (366 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (134688 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_366, dusart_theta_nat_51, dusart_theta_nat_19, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_134689_143640 :
    Chebyshev.psi (143640 : Real) - Chebyshev.theta 143640 -
        Chebyshev.theta (Real.sqrt (143640 : Real)) <
      (1777745 : Real) / 1000000 * (134689 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (143640 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (143640 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 2) (r := 378) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(143640 : Real) ^ (1 / (2 : Real))⌋₊ = 378 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((143640 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (378 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 3) (r := 52) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(143640 : Real) ^ (1 / (3 : Real))⌋₊ = 52 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((143640 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (52 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 4) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(143640 : Real) ^ (1 / (4 : Real))⌋₊ = 19 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((143640 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(143640 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((143640 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(143640 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((143640 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(143640 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((143640 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(143640 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((143640 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(143640 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((143640 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(143640 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((143640 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(143640 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((143640 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(143640 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((143640 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(143640 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((143640 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(143640 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((143640 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(143640 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((143640 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(143640 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((143640 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 143640) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(143640 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((143640 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (143640 : Real)) =
      Chebyshev.theta (378 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (143640 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_378, dusart_theta_nat_52, dusart_theta_nat_19, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_143641_151320 :
    Chebyshev.psi (151320 : Real) - Chebyshev.theta 151320 -
        Chebyshev.theta (Real.sqrt (151320 : Real)) <
      (1777745 : Real) / 1000000 * (143641 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (151320 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (151320 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 2) (r := 388) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(151320 : Real) ^ (1 / (2 : Real))⌋₊ = 388 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((151320 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (388 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 3) (r := 53) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(151320 : Real) ^ (1 / (3 : Real))⌋₊ = 53 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((151320 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (53 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 4) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(151320 : Real) ^ (1 / (4 : Real))⌋₊ = 19 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((151320 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(151320 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((151320 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(151320 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((151320 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(151320 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((151320 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(151320 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((151320 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(151320 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((151320 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(151320 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((151320 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(151320 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((151320 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(151320 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((151320 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(151320 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((151320 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(151320 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((151320 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(151320 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((151320 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(151320 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((151320 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 151320) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(151320 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((151320 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (151320 : Real)) =
      Chebyshev.theta (388 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (151320 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_388, dusart_theta_nat_53, dusart_theta_nat_19, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_151321_160800 :
    Chebyshev.psi (160800 : Real) - Chebyshev.theta 160800 -
        Chebyshev.theta (Real.sqrt (160800 : Real)) <
      (1777745 : Real) / 1000000 * (151321 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (160800 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (160800 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 2) (r := 400) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(160800 : Real) ^ (1 / (2 : Real))⌋₊ = 400 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((160800 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (400 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 3) (r := 54) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(160800 : Real) ^ (1 / (3 : Real))⌋₊ = 54 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((160800 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (54 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 4) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(160800 : Real) ^ (1 / (4 : Real))⌋₊ = 20 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((160800 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(160800 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((160800 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(160800 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((160800 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(160800 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((160800 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(160800 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((160800 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(160800 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((160800 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(160800 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((160800 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(160800 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((160800 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(160800 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((160800 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(160800 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((160800 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(160800 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((160800 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(160800 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((160800 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(160800 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((160800 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(160800 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((160800 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (160800 : Real)) =
      Chebyshev.theta (400 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (160800 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_400, dusart_theta_nat_54, dusart_theta_nat_20, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_160801_175560 :
    Chebyshev.psi (175560 : Real) - Chebyshev.theta 175560 -
        Chebyshev.theta (Real.sqrt (175560 : Real)) <
      (1777745 : Real) / 1000000 * (160801 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (175560 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (175560 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 2) (r := 418) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(175560 : Real) ^ (1 / (2 : Real))⌋₊ = 418 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((175560 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (418 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 3) (r := 55) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(175560 : Real) ^ (1 / (3 : Real))⌋₊ = 55 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((175560 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (55 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 4) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(175560 : Real) ^ (1 / (4 : Real))⌋₊ = 20 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((175560 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(175560 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((175560 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(175560 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((175560 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(175560 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((175560 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(175560 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((175560 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(175560 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((175560 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(175560 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((175560 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(175560 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((175560 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(175560 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((175560 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(175560 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((175560 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(175560 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((175560 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(175560 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((175560 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(175560 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((175560 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(175560 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((175560 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (175560 : Real)) =
      Chebyshev.theta (418 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (175560 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_418, dusart_theta_nat_55, dusart_theta_nat_20, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_175561_185760 :
    Chebyshev.psi (185760 : Real) - Chebyshev.theta 185760 -
        Chebyshev.theta (Real.sqrt (185760 : Real)) <
      (1777745 : Real) / 1000000 * (175561 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (185760 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (185760 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 2) (r := 430) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(185760 : Real) ^ (1 / (2 : Real))⌋₊ = 430 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((185760 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (430 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 3) (r := 57) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(185760 : Real) ^ (1 / (3 : Real))⌋₊ = 57 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((185760 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (57 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 4) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(185760 : Real) ^ (1 / (4 : Real))⌋₊ = 20 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((185760 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(185760 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((185760 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(185760 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((185760 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(185760 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((185760 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(185760 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((185760 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(185760 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((185760 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(185760 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((185760 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(185760 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((185760 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(185760 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((185760 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(185760 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((185760 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(185760 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((185760 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(185760 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((185760 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(185760 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((185760 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(185760 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((185760 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (185760 : Real)) =
      Chebyshev.theta (430 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (185760 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_430, dusart_theta_nat_57, dusart_theta_nat_20, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_185761_196248 :
    Chebyshev.psi (196248 : Real) - Chebyshev.theta 196248 -
        Chebyshev.theta (Real.sqrt (196248 : Real)) <
      (1777745 : Real) / 1000000 * (185761 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (196248 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (196248 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 2) (r := 442) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(196248 : Real) ^ (1 / (2 : Real))⌋₊ = 442 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((196248 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (442 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 3) (r := 58) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(196248 : Real) ^ (1 / (3 : Real))⌋₊ = 58 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((196248 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (58 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 4) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(196248 : Real) ^ (1 / (4 : Real))⌋₊ = 21 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((196248 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(196248 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((196248 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(196248 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((196248 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(196248 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((196248 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(196248 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((196248 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(196248 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((196248 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(196248 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((196248 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(196248 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((196248 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(196248 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((196248 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(196248 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((196248 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(196248 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((196248 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(196248 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((196248 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(196248 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((196248 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(196248 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((196248 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (196248 : Real)) =
      Chebyshev.theta (442 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (196248 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_442, dusart_theta_nat_58, dusart_theta_nat_21, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_196249_208848 :
    Chebyshev.psi (208848 : Real) - Chebyshev.theta 208848 -
        Chebyshev.theta (Real.sqrt (208848 : Real)) <
      (1777745 : Real) / 1000000 * (196249 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (208848 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (208848 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 2) (r := 456) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(208848 : Real) ^ (1 / (2 : Real))⌋₊ = 456 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((208848 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (456 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 3) (r := 59) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(208848 : Real) ^ (1 / (3 : Real))⌋₊ = 59 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((208848 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (59 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 4) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(208848 : Real) ^ (1 / (4 : Real))⌋₊ = 21 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((208848 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(208848 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((208848 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(208848 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((208848 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(208848 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((208848 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(208848 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((208848 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(208848 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((208848 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(208848 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((208848 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(208848 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((208848 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(208848 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((208848 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(208848 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((208848 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(208848 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((208848 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(208848 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((208848 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(208848 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((208848 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 208848) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(208848 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((208848 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (208848 : Real)) =
      Chebyshev.theta (456 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (208848 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_456, dusart_theta_nat_59, dusart_theta_nat_21, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_208849_218088 :
    Chebyshev.psi (218088 : Real) - Chebyshev.theta 218088 -
        Chebyshev.theta (Real.sqrt (218088 : Real)) <
      (1777745 : Real) / 1000000 * (208849 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (218088 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (218088 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 2) (r := 466) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(218088 : Real) ^ (1 / (2 : Real))⌋₊ = 466 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((218088 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (466 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 3) (r := 60) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(218088 : Real) ^ (1 / (3 : Real))⌋₊ = 60 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((218088 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (60 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 4) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(218088 : Real) ^ (1 / (4 : Real))⌋₊ = 21 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((218088 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(218088 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((218088 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(218088 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((218088 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(218088 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((218088 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(218088 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((218088 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(218088 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((218088 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(218088 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((218088 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(218088 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((218088 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(218088 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((218088 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(218088 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((218088 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(218088 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((218088 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(218088 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((218088 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(218088 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((218088 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 218088) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(218088 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((218088 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (218088 : Real)) =
      Chebyshev.theta (466 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (218088 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_466, dusart_theta_nat_60, dusart_theta_nat_21, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_218089_237168 :
    Chebyshev.psi (237168 : Real) - Chebyshev.theta 237168 -
        Chebyshev.theta (Real.sqrt (237168 : Real)) <
      (1777745 : Real) / 1000000 * (218089 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (237168 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (237168 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 2) (r := 486) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(237168 : Real) ^ (1 / (2 : Real))⌋₊ = 486 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((237168 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (486 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 3) (r := 61) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(237168 : Real) ^ (1 / (3 : Real))⌋₊ = 61 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((237168 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (61 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 4) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(237168 : Real) ^ (1 / (4 : Real))⌋₊ = 22 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((237168 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(237168 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((237168 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(237168 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((237168 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(237168 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((237168 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(237168 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((237168 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(237168 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((237168 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(237168 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((237168 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(237168 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((237168 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(237168 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((237168 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(237168 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((237168 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(237168 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((237168 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(237168 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((237168 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(237168 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((237168 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 237168) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(237168 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((237168 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (237168 : Real)) =
      Chebyshev.theta (486 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (237168 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_486, dusart_theta_nat_61, dusart_theta_nat_22, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_237169_253008 :
    Chebyshev.psi (253008 : Real) - Chebyshev.theta 253008 -
        Chebyshev.theta (Real.sqrt (253008 : Real)) <
      (1777745 : Real) / 1000000 * (237169 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (253008 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (253008 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 2) (r := 502) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(253008 : Real) ^ (1 / (2 : Real))⌋₊ = 502 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((253008 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (502 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 3) (r := 63) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(253008 : Real) ^ (1 / (3 : Real))⌋₊ = 63 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((253008 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (63 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 4) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(253008 : Real) ^ (1 / (4 : Real))⌋₊ = 22 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((253008 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 5) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(253008 : Real) ^ (1 / (5 : Real))⌋₊ = 12 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((253008 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(253008 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((253008 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(253008 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((253008 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(253008 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((253008 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(253008 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((253008 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(253008 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((253008 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(253008 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((253008 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(253008 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((253008 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(253008 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((253008 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(253008 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((253008 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(253008 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((253008 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(253008 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((253008 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 253008) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(253008 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((253008 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (253008 : Real)) =
      Chebyshev.theta (502 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (253008 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_502, dusart_theta_nat_63, dusart_theta_nat_22, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_253009_273528 :
    Chebyshev.psi (273528 : Real) - Chebyshev.theta 273528 -
        Chebyshev.theta (Real.sqrt (273528 : Real)) <
      (1777745 : Real) / 1000000 * (253009 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (273528 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (273528 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 2) (r := 522) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(273528 : Real) ^ (1 / (2 : Real))⌋₊ = 522 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((273528 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (522 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 3) (r := 64) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(273528 : Real) ^ (1 / (3 : Real))⌋₊ = 64 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((273528 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (64 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 4) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(273528 : Real) ^ (1 / (4 : Real))⌋₊ = 22 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((273528 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 5) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(273528 : Real) ^ (1 / (5 : Real))⌋₊ = 12 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((273528 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(273528 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((273528 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(273528 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((273528 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(273528 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((273528 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(273528 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((273528 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(273528 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((273528 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(273528 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((273528 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(273528 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((273528 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(273528 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((273528 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(273528 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((273528 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(273528 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((273528 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(273528 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((273528 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(273528 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((273528 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 273528) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(273528 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((273528 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (273528 : Real)) =
      Chebyshev.theta (522 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (273528 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_522, dusart_theta_nat_64, dusart_theta_nat_22, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_273529_300762 :
    Chebyshev.psi (300762 : Real) - Chebyshev.theta 300762 -
        Chebyshev.theta (Real.sqrt (300762 : Real)) <
      (1777745 : Real) / 1000000 * (273529 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (300762 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (300762 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 2) (r := 548) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(300762 : Real) ^ (1 / (2 : Real))⌋₊ = 548 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((300762 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (548 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 3) (r := 66) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(300762 : Real) ^ (1 / (3 : Real))⌋₊ = 66 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((300762 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (66 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 4) (r := 23) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(300762 : Real) ^ (1 / (4 : Real))⌋₊ = 23 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((300762 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (23 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 5) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(300762 : Real) ^ (1 / (5 : Real))⌋₊ = 12 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((300762 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(300762 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((300762 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(300762 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((300762 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(300762 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((300762 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(300762 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((300762 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(300762 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((300762 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(300762 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((300762 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(300762 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((300762 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(300762 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((300762 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(300762 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((300762 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(300762 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((300762 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(300762 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((300762 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(300762 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((300762 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 300762) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(300762 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((300762 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (300762 : Real)) =
      Chebyshev.theta (548 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (300762 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_548, dusart_theta_nat_66, dusart_theta_nat_23, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_300763_323760 :
    Chebyshev.psi (323760 : Real) - Chebyshev.theta 323760 -
        Chebyshev.theta (Real.sqrt (323760 : Real)) <
      (1777745 : Real) / 1000000 * (300763 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (323760 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (323760 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 2) (r := 568) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(323760 : Real) ^ (1 / (2 : Real))⌋₊ = 568 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((323760 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (568 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 3) (r := 68) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(323760 : Real) ^ (1 / (3 : Real))⌋₊ = 68 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((323760 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (68 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 4) (r := 23) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(323760 : Real) ^ (1 / (4 : Real))⌋₊ = 23 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((323760 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (23 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 5) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(323760 : Real) ^ (1 / (5 : Real))⌋₊ = 12 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((323760 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(323760 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((323760 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(323760 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((323760 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(323760 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((323760 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(323760 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((323760 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(323760 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((323760 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(323760 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((323760 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(323760 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((323760 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(323760 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((323760 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(323760 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((323760 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(323760 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((323760 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(323760 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((323760 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(323760 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((323760 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 323760) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(323760 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((323760 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (323760 : Real)) =
      Chebyshev.theta (568 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (323760 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_568, dusart_theta_nat_68, dusart_theta_nat_23, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_323761_344568 :
    Chebyshev.psi (344568 : Real) - Chebyshev.theta 344568 -
        Chebyshev.theta (Real.sqrt (344568 : Real)) <
      (1777745 : Real) / 1000000 * (323761 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (344568 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (344568 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 2) (r := 586) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(344568 : Real) ^ (1 / (2 : Real))⌋₊ = 586 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((344568 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (586 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 3) (r := 70) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(344568 : Real) ^ (1 / (3 : Real))⌋₊ = 70 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((344568 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (70 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 4) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(344568 : Real) ^ (1 / (4 : Real))⌋₊ = 24 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((344568 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 5) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(344568 : Real) ^ (1 / (5 : Real))⌋₊ = 12 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((344568 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(344568 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((344568 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(344568 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((344568 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(344568 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((344568 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(344568 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((344568 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(344568 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((344568 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(344568 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((344568 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(344568 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((344568 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(344568 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((344568 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(344568 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((344568 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(344568 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((344568 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(344568 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((344568 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(344568 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((344568 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 344568) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(344568 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((344568 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (344568 : Real)) =
      Chebyshev.theta (586 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (344568 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_586, dusart_theta_nat_70, dusart_theta_nat_24, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_344569_361200 :
    Chebyshev.psi (361200 : Real) - Chebyshev.theta 361200 -
        Chebyshev.theta (Real.sqrt (361200 : Real)) <
      (1777745 : Real) / 1000000 * (344569 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (361200 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (361200 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 2) (r := 600) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(361200 : Real) ^ (1 / (2 : Real))⌋₊ = 600 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((361200 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (600 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 3) (r := 71) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(361200 : Real) ^ (1 / (3 : Real))⌋₊ = 71 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((361200 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (71 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 4) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(361200 : Real) ^ (1 / (4 : Real))⌋₊ = 24 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((361200 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 5) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(361200 : Real) ^ (1 / (5 : Real))⌋₊ = 12 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((361200 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(361200 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((361200 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(361200 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((361200 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(361200 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((361200 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(361200 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((361200 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(361200 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((361200 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(361200 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((361200 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(361200 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((361200 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(361200 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((361200 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(361200 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((361200 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(361200 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((361200 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(361200 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((361200 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(361200 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((361200 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(361200 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((361200 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (361200 : Real)) =
      Chebyshev.theta (600 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (361200 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_600, dusart_theta_nat_71, dusart_theta_nat_24, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_361201_380688 :
    Chebyshev.psi (380688 : Real) - Chebyshev.theta 380688 -
        Chebyshev.theta (Real.sqrt (380688 : Real)) <
      (1777745 : Real) / 1000000 * (361201 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (380688 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (380688 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 2) (r := 616) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(380688 : Real) ^ (1 / (2 : Real))⌋₊ = 616 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((380688 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (616 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 3) (r := 72) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(380688 : Real) ^ (1 / (3 : Real))⌋₊ = 72 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((380688 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (72 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 4) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(380688 : Real) ^ (1 / (4 : Real))⌋₊ = 24 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((380688 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(380688 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((380688 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(380688 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((380688 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(380688 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((380688 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(380688 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((380688 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(380688 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((380688 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(380688 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((380688 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(380688 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((380688 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(380688 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((380688 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(380688 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((380688 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(380688 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((380688 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(380688 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((380688 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(380688 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((380688 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(380688 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((380688 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(380688 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((380688 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (380688 : Real)) =
      Chebyshev.theta (616 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (380688 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_616, dusart_theta_nat_72, dusart_theta_nat_24, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_380689_398160 :
    Chebyshev.psi (398160 : Real) - Chebyshev.theta 398160 -
        Chebyshev.theta (Real.sqrt (398160 : Real)) <
      (1777745 : Real) / 1000000 * (380689 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (398160 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (398160 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 2) (r := 630) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(398160 : Real) ^ (1 / (2 : Real))⌋₊ = 630 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((398160 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (630 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 3) (r := 73) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(398160 : Real) ^ (1 / (3 : Real))⌋₊ = 73 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((398160 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (73 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 4) (r := 25) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(398160 : Real) ^ (1 / (4 : Real))⌋₊ = 25 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((398160 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (25 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(398160 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((398160 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(398160 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((398160 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(398160 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((398160 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(398160 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((398160 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(398160 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((398160 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(398160 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((398160 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(398160 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((398160 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(398160 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((398160 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(398160 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((398160 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(398160 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((398160 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(398160 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((398160 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(398160 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((398160 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(398160 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((398160 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(398160 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((398160 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (398160 : Real)) =
      Chebyshev.theta (630 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (398160 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_630, dusart_theta_nat_73, dusart_theta_nat_25, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_398161_418608 :
    Chebyshev.psi (418608 : Real) - Chebyshev.theta 418608 -
        Chebyshev.theta (Real.sqrt (418608 : Real)) <
      (1777745 : Real) / 1000000 * (398161 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (418608 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (418608 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 2) (r := 646) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(418608 : Real) ^ (1 / (2 : Real))⌋₊ = 646 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((418608 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (646 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 3) (r := 74) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(418608 : Real) ^ (1 / (3 : Real))⌋₊ = 74 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((418608 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (74 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 4) (r := 25) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(418608 : Real) ^ (1 / (4 : Real))⌋₊ = 25 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((418608 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (25 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(418608 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((418608 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(418608 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((418608 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(418608 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((418608 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(418608 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((418608 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(418608 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((418608 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(418608 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((418608 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(418608 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((418608 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(418608 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((418608 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(418608 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((418608 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(418608 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((418608 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(418608 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((418608 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(418608 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((418608 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(418608 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((418608 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(418608 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((418608 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (418608 : Real)) =
      Chebyshev.theta (646 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (418608 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_646, dusart_theta_nat_74, dusart_theta_nat_25, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_418609_436920 :
    Chebyshev.psi (436920 : Real) - Chebyshev.theta 436920 -
        Chebyshev.theta (Real.sqrt (436920 : Real)) <
      (1777745 : Real) / 1000000 * (418609 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (436920 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (436920 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 2) (r := 660) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(436920 : Real) ^ (1 / (2 : Real))⌋₊ = 660 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((436920 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (660 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 3) (r := 75) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(436920 : Real) ^ (1 / (3 : Real))⌋₊ = 75 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((436920 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (75 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 4) (r := 25) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(436920 : Real) ^ (1 / (4 : Real))⌋₊ = 25 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((436920 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (25 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(436920 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((436920 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(436920 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((436920 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(436920 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((436920 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(436920 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((436920 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(436920 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((436920 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(436920 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((436920 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(436920 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((436920 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(436920 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((436920 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(436920 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((436920 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(436920 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((436920 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(436920 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((436920 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(436920 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((436920 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(436920 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((436920 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 436920) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(436920 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((436920 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (436920 : Real)) =
      Chebyshev.theta (660 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (436920 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_660, dusart_theta_nat_75, dusart_theta_nat_25, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_436921_466488 :
    Chebyshev.psi (466488 : Real) - Chebyshev.theta 466488 -
        Chebyshev.theta (Real.sqrt (466488 : Real)) <
      (1777745 : Real) / 1000000 * (436921 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (466488 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (466488 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 2) (r := 682) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(466488 : Real) ^ (1 / (2 : Real))⌋₊ = 682 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((466488 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (682 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 3) (r := 77) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(466488 : Real) ^ (1 / (3 : Real))⌋₊ = 77 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((466488 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (77 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 4) (r := 26) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(466488 : Real) ^ (1 / (4 : Real))⌋₊ = 26 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((466488 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (26 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(466488 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((466488 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(466488 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((466488 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(466488 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((466488 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(466488 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((466488 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(466488 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((466488 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(466488 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((466488 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(466488 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((466488 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(466488 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((466488 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(466488 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((466488 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(466488 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((466488 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(466488 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((466488 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(466488 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((466488 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(466488 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((466488 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 466488) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(466488 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((466488 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (466488 : Real)) =
      Chebyshev.theta (682 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (466488 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_682, dusart_theta_nat_77, dusart_theta_nat_26, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_466489_502680 :
    Chebyshev.psi (502680 : Real) - Chebyshev.theta 502680 -
        Chebyshev.theta (Real.sqrt (502680 : Real)) <
      (1777745 : Real) / 1000000 * (466489 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (502680 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (502680 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 2) (r := 708) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(502680 : Real) ^ (1 / (2 : Real))⌋₊ = 708 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((502680 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (708 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 3) (r := 79) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(502680 : Real) ^ (1 / (3 : Real))⌋₊ = 79 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((502680 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (79 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 4) (r := 26) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(502680 : Real) ^ (1 / (4 : Real))⌋₊ = 26 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((502680 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (26 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(502680 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((502680 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(502680 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((502680 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(502680 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((502680 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(502680 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((502680 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(502680 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((502680 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(502680 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((502680 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(502680 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((502680 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(502680 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((502680 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(502680 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((502680 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(502680 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((502680 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(502680 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((502680 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(502680 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((502680 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(502680 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((502680 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 502680) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(502680 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((502680 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (502680 : Real)) =
      Chebyshev.theta (708 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (502680 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_708, dusart_theta_nat_79, dusart_theta_nat_26, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_502681_537288 :
    Chebyshev.psi (537288 : Real) - Chebyshev.theta 537288 -
        Chebyshev.theta (Real.sqrt (537288 : Real)) <
      (1777745 : Real) / 1000000 * (502681 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (537288 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (537288 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 2) (r := 732) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(537288 : Real) ^ (1 / (2 : Real))⌋₊ = 732 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((537288 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (732 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 3) (r := 81) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(537288 : Real) ^ (1 / (3 : Real))⌋₊ = 81 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((537288 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (81 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 4) (r := 27) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(537288 : Real) ^ (1 / (4 : Real))⌋₊ = 27 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((537288 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (27 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(537288 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((537288 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(537288 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((537288 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(537288 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((537288 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(537288 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((537288 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(537288 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((537288 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(537288 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((537288 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(537288 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((537288 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(537288 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((537288 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(537288 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((537288 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(537288 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((537288 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(537288 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((537288 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(537288 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((537288 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(537288 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((537288 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(537288 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((537288 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 537288) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(537288 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((537288 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (537288 : Real)) =
      Chebyshev.theta (732 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (537288 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_732, dusart_theta_nat_81, dusart_theta_nat_27, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_537289_571786 :
    Chebyshev.psi (571786 : Real) - Chebyshev.theta 571786 -
        Chebyshev.theta (Real.sqrt (571786 : Real)) <
      (1777745 : Real) / 1000000 * (537289 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (571786 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (571786 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 2) (r := 756) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(571786 : Real) ^ (1 / (2 : Real))⌋₊ = 756 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((571786 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (756 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 3) (r := 82) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(571786 : Real) ^ (1 / (3 : Real))⌋₊ = 82 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((571786 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (82 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 4) (r := 27) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(571786 : Real) ^ (1 / (4 : Real))⌋₊ = 27 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((571786 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (27 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(571786 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((571786 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(571786 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((571786 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(571786 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((571786 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(571786 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((571786 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(571786 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((571786 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(571786 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((571786 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(571786 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((571786 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(571786 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((571786 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(571786 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((571786 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(571786 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((571786 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(571786 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((571786 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(571786 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((571786 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(571786 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((571786 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(571786 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((571786 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(571786 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((571786 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (571786 : Real)) =
      Chebyshev.theta (756 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (571786 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_756, dusart_theta_nat_82, dusart_theta_nat_27, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_571787_591360 :
    Chebyshev.psi (591360 : Real) - Chebyshev.theta 591360 -
        Chebyshev.theta (Real.sqrt (591360 : Real)) <
      (1777745 : Real) / 1000000 * (571787 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (591360 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (591360 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 2) (r := 768) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(591360 : Real) ^ (1 / (2 : Real))⌋₊ = 768 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((591360 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (768 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 3) (r := 83) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(591360 : Real) ^ (1 / (3 : Real))⌋₊ = 83 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((591360 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (83 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 4) (r := 27) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(591360 : Real) ^ (1 / (4 : Real))⌋₊ = 27 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((591360 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (27 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(591360 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((591360 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(591360 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((591360 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(591360 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((591360 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(591360 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((591360 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(591360 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((591360 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(591360 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((591360 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(591360 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((591360 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(591360 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((591360 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(591360 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((591360 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(591360 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((591360 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(591360 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((591360 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(591360 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((591360 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(591360 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((591360 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(591360 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((591360 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(591360 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((591360 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (591360 : Real)) =
      Chebyshev.theta (768 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (591360 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_768, dusart_theta_nat_83, dusart_theta_nat_27, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_591361_654480 :
    Chebyshev.psi (654480 : Real) - Chebyshev.theta 654480 -
        Chebyshev.theta (Real.sqrt (654480 : Real)) <
      (1777745 : Real) / 1000000 * (591361 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (654480 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (654480 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 2) (r := 808) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(654480 : Real) ^ (1 / (2 : Real))⌋₊ = 808 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((654480 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (808 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 3) (r := 86) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(654480 : Real) ^ (1 / (3 : Real))⌋₊ = 86 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((654480 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (86 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 4) (r := 28) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(654480 : Real) ^ (1 / (4 : Real))⌋₊ = 28 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((654480 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (28 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(654480 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((654480 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(654480 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((654480 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(654480 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((654480 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(654480 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((654480 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(654480 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((654480 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(654480 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((654480 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(654480 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((654480 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(654480 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((654480 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(654480 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((654480 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(654480 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((654480 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(654480 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((654480 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(654480 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((654480 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(654480 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((654480 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(654480 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((654480 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(654480 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((654480 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (654480 : Real)) =
      Chebyshev.theta (808 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (654480 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_808, dusart_theta_nat_86, dusart_theta_nat_28, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_654481_683928 :
    Chebyshev.psi (683928 : Real) - Chebyshev.theta 683928 -
        Chebyshev.theta (Real.sqrt (683928 : Real)) <
      (1777745 : Real) / 1000000 * (654481 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (683928 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (683928 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 2) (r := 826) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(683928 : Real) ^ (1 / (2 : Real))⌋₊ = 826 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((683928 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (826 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 3) (r := 88) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(683928 : Real) ^ (1 / (3 : Real))⌋₊ = 88 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((683928 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (88 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 4) (r := 28) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(683928 : Real) ^ (1 / (4 : Real))⌋₊ = 28 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((683928 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (28 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(683928 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((683928 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(683928 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((683928 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(683928 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((683928 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(683928 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((683928 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(683928 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((683928 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(683928 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((683928 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(683928 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((683928 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(683928 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((683928 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(683928 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((683928 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(683928 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((683928 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(683928 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((683928 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(683928 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((683928 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(683928 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((683928 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(683928 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((683928 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(683928 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((683928 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (683928 : Real)) =
      Chebyshev.theta (826 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (683928 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_826, dusart_theta_nat_88, dusart_theta_nat_28, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_683929_734448 :
    Chebyshev.psi (734448 : Real) - Chebyshev.theta 734448 -
        Chebyshev.theta (Real.sqrt (734448 : Real)) <
      (1777745 : Real) / 1000000 * (683929 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (734448 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (734448 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 2) (r := 856) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(734448 : Real) ^ (1 / (2 : Real))⌋₊ = 856 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((734448 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (856 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 3) (r := 90) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(734448 : Real) ^ (1 / (3 : Real))⌋₊ = 90 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((734448 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (90 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 4) (r := 29) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(734448 : Real) ^ (1 / (4 : Real))⌋₊ = 29 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((734448 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (29 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(734448 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((734448 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(734448 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((734448 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(734448 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((734448 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(734448 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((734448 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(734448 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((734448 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(734448 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((734448 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(734448 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((734448 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(734448 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((734448 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(734448 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((734448 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(734448 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((734448 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(734448 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((734448 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(734448 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((734448 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(734448 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((734448 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(734448 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((734448 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 734448) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(734448 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((734448 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (734448 : Real)) =
      Chebyshev.theta (856 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (734448 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_856, dusart_theta_nat_90, dusart_theta_nat_29, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_734449_776160 :
    Chebyshev.psi (776160 : Real) - Chebyshev.theta 776160 -
        Chebyshev.theta (Real.sqrt (776160 : Real)) <
      (1777745 : Real) / 1000000 * (734449 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (776160 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (776160 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 2) (r := 880) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(776160 : Real) ^ (1 / (2 : Real))⌋₊ = 880 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((776160 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (880 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 3) (r := 91) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(776160 : Real) ^ (1 / (3 : Real))⌋₊ = 91 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((776160 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (91 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 4) (r := 29) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(776160 : Real) ^ (1 / (4 : Real))⌋₊ = 29 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((776160 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (29 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 5) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(776160 : Real) ^ (1 / (5 : Real))⌋₊ = 15 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((776160 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(776160 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((776160 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(776160 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((776160 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(776160 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((776160 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(776160 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((776160 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(776160 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((776160 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(776160 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((776160 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(776160 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((776160 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(776160 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((776160 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(776160 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((776160 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(776160 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((776160 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(776160 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((776160 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(776160 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((776160 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(776160 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((776160 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 776160) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(776160 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((776160 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (776160 : Real)) =
      Chebyshev.theta (880 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (776160 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_880, dusart_theta_nat_91, dusart_theta_nat_29, dusart_theta_nat_15, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_776161_829920 :
    Chebyshev.psi (829920 : Real) - Chebyshev.theta 829920 -
        Chebyshev.theta (Real.sqrt (829920 : Real)) <
      (1777745 : Real) / 1000000 * (776161 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (829920 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (829920 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 2) (r := 910) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(829920 : Real) ^ (1 / (2 : Real))⌋₊ = 910 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((829920 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (910 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 3) (r := 93) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(829920 : Real) ^ (1 / (3 : Real))⌋₊ = 93 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((829920 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (93 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 4) (r := 30) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(829920 : Real) ^ (1 / (4 : Real))⌋₊ = 30 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((829920 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (30 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 5) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(829920 : Real) ^ (1 / (5 : Real))⌋₊ = 15 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((829920 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(829920 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((829920 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(829920 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((829920 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(829920 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((829920 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(829920 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((829920 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(829920 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((829920 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(829920 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((829920 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(829920 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((829920 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(829920 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((829920 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(829920 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((829920 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(829920 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((829920 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(829920 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((829920 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(829920 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((829920 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(829920 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((829920 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 829920) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(829920 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((829920 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (829920 : Real)) =
      Chebyshev.theta (910 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (829920 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_910, dusart_theta_nat_93, dusart_theta_nat_30, dusart_theta_nat_15, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_829921_896808 :
    Chebyshev.psi (896808 : Real) - Chebyshev.theta 896808 -
        Chebyshev.theta (Real.sqrt (896808 : Real)) <
      (1777745 : Real) / 1000000 * (829921 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (896808 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (896808 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 2) (r := 946) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(896808 : Real) ^ (1 / (2 : Real))⌋₊ = 946 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((896808 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (946 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 3) (r := 96) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(896808 : Real) ^ (1 / (3 : Real))⌋₊ = 96 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((896808 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (96 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 4) (r := 30) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(896808 : Real) ^ (1 / (4 : Real))⌋₊ = 30 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((896808 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (30 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 5) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(896808 : Real) ^ (1 / (5 : Real))⌋₊ = 15 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((896808 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(896808 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((896808 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(896808 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((896808 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(896808 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((896808 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(896808 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((896808 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(896808 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((896808 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(896808 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((896808 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(896808 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((896808 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(896808 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((896808 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(896808 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((896808 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(896808 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((896808 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(896808 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((896808 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(896808 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((896808 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(896808 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((896808 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 896808) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(896808 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((896808 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (896808 : Real)) =
      Chebyshev.theta (946 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (896808 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_946, dusart_theta_nat_96, dusart_theta_nat_30, dusart_theta_nat_15, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_896809_954528 :
    Chebyshev.psi (954528 : Real) - Chebyshev.theta 954528 -
        Chebyshev.theta (Real.sqrt (954528 : Real)) <
      (1777745 : Real) / 1000000 * (896809 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (954528 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (954528 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 2) (r := 976) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(954528 : Real) ^ (1 / (2 : Real))⌋₊ = 976 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((954528 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (976 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 3) (r := 98) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(954528 : Real) ^ (1 / (3 : Real))⌋₊ = 98 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((954528 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (98 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 4) (r := 31) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(954528 : Real) ^ (1 / (4 : Real))⌋₊ = 31 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((954528 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (31 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 5) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(954528 : Real) ^ (1 / (5 : Real))⌋₊ = 15 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((954528 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(954528 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((954528 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(954528 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((954528 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(954528 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((954528 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(954528 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((954528 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(954528 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((954528 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(954528 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((954528 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(954528 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((954528 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(954528 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((954528 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(954528 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((954528 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(954528 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((954528 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(954528 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((954528 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(954528 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((954528 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(954528 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((954528 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 954528) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(954528 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((954528 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (954528 : Real)) =
      Chebyshev.theta (976 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (954528 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_976, dusart_theta_nat_98, dusart_theta_nat_31, dusart_theta_nat_15, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_954529_1026168 :
    Chebyshev.psi (1026168 : Real) - Chebyshev.theta 1026168 -
        Chebyshev.theta (Real.sqrt (1026168 : Real)) <
      (1777745 : Real) / 1000000 * (954529 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1026168 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1026168 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 2) (r := 1012) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1026168 : Real) ^ (1 / (2 : Real))⌋₊ = 1012 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1026168 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1012 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 3) (r := 100) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1026168 : Real) ^ (1 / (3 : Real))⌋₊ = 100 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1026168 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (100 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 4) (r := 31) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1026168 : Real) ^ (1 / (4 : Real))⌋₊ = 31 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1026168 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (31 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 5) (r := 15) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1026168 : Real) ^ (1 / (5 : Real))⌋₊ = 15 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1026168 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (15 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1026168 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1026168 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1026168 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1026168 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1026168 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1026168 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1026168 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1026168 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1026168 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1026168 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1026168 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1026168 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1026168 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1026168 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1026168 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1026168 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1026168 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1026168 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1026168 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1026168 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1026168 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1026168 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1026168 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1026168 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1026168 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1026168 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1026168) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1026168 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1026168 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1026168 : Real)) =
      Chebyshev.theta (1012 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1026168 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_1012, dusart_theta_nat_100, dusart_theta_nat_31, dusart_theta_nat_15, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1026169_1079520 :
    Chebyshev.psi (1079520 : Real) - Chebyshev.theta 1079520 -
        Chebyshev.theta (Real.sqrt (1079520 : Real)) <
      (1777745 : Real) / 1000000 * (1026169 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1079520 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1079520 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 2) (r := 1038) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1079520 : Real) ^ (1 / (2 : Real))⌋₊ = 1038 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1079520 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1038 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 3) (r := 102) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1079520 : Real) ^ (1 / (3 : Real))⌋₊ = 102 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1079520 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (102 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 4) (r := 32) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1079520 : Real) ^ (1 / (4 : Real))⌋₊ = 32 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1079520 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (32 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 5) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1079520 : Real) ^ (1 / (5 : Real))⌋₊ = 16 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1079520 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1079520 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1079520 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1079520 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1079520 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1079520 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1079520 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1079520 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1079520 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1079520 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1079520 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1079520 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1079520 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1079520 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1079520 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1079520 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1079520 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1079520 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1079520 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1079520 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1079520 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1079520 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1079520 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1079520 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1079520 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1079520 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1079520 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1079520 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1079520 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1079520) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1079520 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1079520 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1079520 : Real)) =
      Chebyshev.theta (1038 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1079520 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1038, dusart_theta_nat_102, dusart_theta_nat_32, dusart_theta_nat_16, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1079521_1129968 :
    Chebyshev.psi (1129968 : Real) - Chebyshev.theta 1129968 -
        Chebyshev.theta (Real.sqrt (1129968 : Real)) <
      (1777745 : Real) / 1000000 * (1079521 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1129968 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1129968 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 2) (r := 1062) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1129968 : Real) ^ (1 / (2 : Real))⌋₊ = 1062 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1129968 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1062 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 3) (r := 104) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1129968 : Real) ^ (1 / (3 : Real))⌋₊ = 104 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1129968 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (104 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 4) (r := 32) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1129968 : Real) ^ (1 / (4 : Real))⌋₊ = 32 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1129968 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (32 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 5) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1129968 : Real) ^ (1 / (5 : Real))⌋₊ = 16 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1129968 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1129968 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1129968 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1129968 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1129968 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1129968 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1129968 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1129968 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1129968 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1129968 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1129968 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1129968 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1129968 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1129968 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1129968 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1129968 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1129968 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1129968 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1129968 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1129968 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1129968 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1129968 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1129968 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1129968 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1129968 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1129968 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1129968 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1129968 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1129968 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1129968) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1129968 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1129968 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1129968 : Real)) =
      Chebyshev.theta (1062 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1129968 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1062, dusart_theta_nat_104, dusart_theta_nat_32, dusart_theta_nat_16, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1129969_1203408 :
    Chebyshev.psi (1203408 : Real) - Chebyshev.theta 1203408 -
        Chebyshev.theta (Real.sqrt (1203408 : Real)) <
      (1777745 : Real) / 1000000 * (1129969 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1203408 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1203408 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 2) (r := 1096) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1203408 : Real) ^ (1 / (2 : Real))⌋₊ = 1096 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1203408 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1096 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 3) (r := 106) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1203408 : Real) ^ (1 / (3 : Real))⌋₊ = 106 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1203408 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (106 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 4) (r := 33) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1203408 : Real) ^ (1 / (4 : Real))⌋₊ = 33 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1203408 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (33 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 5) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1203408 : Real) ^ (1 / (5 : Real))⌋₊ = 16 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1203408 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1203408 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1203408 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1203408 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1203408 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1203408 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1203408 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1203408 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1203408 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1203408 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1203408 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1203408 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1203408 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1203408 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1203408 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1203408 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1203408 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1203408 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1203408 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1203408 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1203408 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1203408 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1203408 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1203408 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1203408 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1203408 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1203408 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1203408 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1203408 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1203408) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1203408 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1203408 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1203408 : Real)) =
      Chebyshev.theta (1096 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1203408 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1096, dusart_theta_nat_106, dusart_theta_nat_33, dusart_theta_nat_16, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1203409_1274640 :
    Chebyshev.psi (1274640 : Real) - Chebyshev.theta 1274640 -
        Chebyshev.theta (Real.sqrt (1274640 : Real)) <
      (1777745 : Real) / 1000000 * (1203409 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1274640 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1274640 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 2) (r := 1128) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1274640 : Real) ^ (1 / (2 : Real))⌋₊ = 1128 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1274640 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1128 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 3) (r := 108) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1274640 : Real) ^ (1 / (3 : Real))⌋₊ = 108 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1274640 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (108 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 4) (r := 33) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1274640 : Real) ^ (1 / (4 : Real))⌋₊ = 33 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1274640 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (33 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 5) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1274640 : Real) ^ (1 / (5 : Real))⌋₊ = 16 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1274640 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1274640 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1274640 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1274640 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1274640 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1274640 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1274640 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1274640 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1274640 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1274640 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1274640 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1274640 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1274640 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1274640 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1274640 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1274640 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1274640 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1274640 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1274640 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1274640 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1274640 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1274640 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1274640 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1274640 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1274640 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1274640 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1274640 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1274640 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1274640 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1274640) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1274640 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1274640 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1274640 : Real)) =
      Chebyshev.theta (1128 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1274640 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1128, dusart_theta_nat_108, dusart_theta_nat_33, dusart_theta_nat_16, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1274641_1371240 :
    Chebyshev.psi (1371240 : Real) - Chebyshev.theta 1371240 -
        Chebyshev.theta (Real.sqrt (1371240 : Real)) <
      (1777745 : Real) / 1000000 * (1274641 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1371240 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1371240 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 2) (r := 1170) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1371240 : Real) ^ (1 / (2 : Real))⌋₊ = 1170 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1371240 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1170 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 3) (r := 111) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1371240 : Real) ^ (1 / (3 : Real))⌋₊ = 111 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1371240 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (111 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 4) (r := 34) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1371240 : Real) ^ (1 / (4 : Real))⌋₊ = 34 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1371240 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (34 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 5) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1371240 : Real) ^ (1 / (5 : Real))⌋₊ = 16 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1371240 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1371240 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1371240 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1371240 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1371240 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1371240 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1371240 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1371240 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1371240 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1371240 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1371240 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1371240 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1371240 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1371240 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1371240 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1371240 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1371240 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1371240 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1371240 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1371240 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1371240 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1371240 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1371240 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1371240 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1371240 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1371240 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1371240 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1371240 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1371240 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1371240) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1371240 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1371240 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1371240 : Real)) =
      Chebyshev.theta (1170 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1371240 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1170, dusart_theta_nat_111, dusart_theta_nat_34, dusart_theta_nat_16, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1371241_1442896 :
    Chebyshev.psi (1442896 : Real) - Chebyshev.theta 1442896 -
        Chebyshev.theta (Real.sqrt (1442896 : Real)) <
      (1777745 : Real) / 1000000 * (1371241 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1442896 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1442896 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 2) (r := 1201) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1442896 : Real) ^ (1 / (2 : Real))⌋₊ = 1201 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1442896 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1201 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 3) (r := 112) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1442896 : Real) ^ (1 / (3 : Real))⌋₊ = 112 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1442896 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (112 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 4) (r := 34) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1442896 : Real) ^ (1 / (4 : Real))⌋₊ = 34 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1442896 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (34 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1442896 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1442896 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1442896 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1442896 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1442896 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1442896 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1442896 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1442896 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1442896 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1442896 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1442896 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1442896 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1442896 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1442896 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1442896 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1442896 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1442896 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1442896 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1442896 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1442896 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1442896 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1442896 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1442896 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1442896 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1442896 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1442896 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1442896 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1442896 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1442896 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1442896 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1442896) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1442896 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1442896 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1442896 : Real)) =
      Chebyshev.theta (1201 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1442896 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1201, dusart_theta_nat_112, dusart_theta_nat_34, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1442897_1510440 :
    Chebyshev.psi (1510440 : Real) - Chebyshev.theta 1510440 -
        Chebyshev.theta (Real.sqrt (1510440 : Real)) <
      (1777745 : Real) / 1000000 * (1442897 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1510440 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1510440 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 2) (r := 1228) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1510440 : Real) ^ (1 / (2 : Real))⌋₊ = 1228 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1510440 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1228 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 3) (r := 114) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1510440 : Real) ^ (1 / (3 : Real))⌋₊ = 114 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1510440 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (114 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 4) (r := 35) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1510440 : Real) ^ (1 / (4 : Real))⌋₊ = 35 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1510440 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (35 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1510440 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1510440 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1510440 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1510440 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1510440 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1510440 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1510440 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1510440 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1510440 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1510440 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1510440 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1510440 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1510440 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1510440 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1510440 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1510440 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1510440 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1510440 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1510440 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1510440 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1510440 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1510440 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1510440 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1510440 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1510440 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1510440 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1510440 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1510440 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1510440 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1510440 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1510440 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1510440 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1510440 : Real)) =
      Chebyshev.theta (1228 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1510440 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1228, dusart_theta_nat_114, dusart_theta_nat_35, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1510441_1630728 :
    Chebyshev.psi (1630728 : Real) - Chebyshev.theta 1630728 -
        Chebyshev.theta (Real.sqrt (1630728 : Real)) <
      (1777745 : Real) / 1000000 * (1510441 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1630728 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1630728 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 2) (r := 1276) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1630728 : Real) ^ (1 / (2 : Real))⌋₊ = 1276 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1630728 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1276 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 3) (r := 117) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1630728 : Real) ^ (1 / (3 : Real))⌋₊ = 117 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1630728 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (117 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 4) (r := 35) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1630728 : Real) ^ (1 / (4 : Real))⌋₊ = 35 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1630728 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (35 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1630728 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1630728 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1630728 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1630728 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1630728 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1630728 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1630728 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1630728 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1630728 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1630728 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1630728 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1630728 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1630728 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1630728 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1630728 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1630728 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1630728 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1630728 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1630728 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1630728 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1630728 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1630728 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1630728 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1630728 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1630728 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1630728 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1630728 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1630728 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1630728 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1630728 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1630728 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1630728 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1630728 : Real)) =
      Chebyshev.theta (1276 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1630728 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1276, dusart_theta_nat_117, dusart_theta_nat_35, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1630729_1682208 :
    Chebyshev.psi (1682208 : Real) - Chebyshev.theta 1682208 -
        Chebyshev.theta (Real.sqrt (1682208 : Real)) <
      (1777745 : Real) / 1000000 * (1630729 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1682208 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1682208 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 2) (r := 1296) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1682208 : Real) ^ (1 / (2 : Real))⌋₊ = 1296 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1682208 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1296 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 3) (r := 118) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1682208 : Real) ^ (1 / (3 : Real))⌋₊ = 118 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1682208 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (118 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 4) (r := 36) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1682208 : Real) ^ (1 / (4 : Real))⌋₊ = 36 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1682208 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (36 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1682208 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1682208 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1682208 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1682208 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1682208 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1682208 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1682208 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1682208 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1682208 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1682208 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1682208 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1682208 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1682208 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1682208 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1682208 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1682208 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1682208 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1682208 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1682208 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1682208 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1682208 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1682208 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1682208 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1682208 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1682208 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1682208 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1682208 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1682208 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1682208 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1682208 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1682208 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1682208 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1682208 : Real)) =
      Chebyshev.theta (1296 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1682208 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1296, dusart_theta_nat_118, dusart_theta_nat_36, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1682209_1760928 :
    Chebyshev.psi (1760928 : Real) - Chebyshev.theta 1760928 -
        Chebyshev.theta (Real.sqrt (1760928 : Real)) <
      (1777745 : Real) / 1000000 * (1682209 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1760928 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1760928 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 2) (r := 1326) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1760928 : Real) ^ (1 / (2 : Real))⌋₊ = 1326 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1760928 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1326 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 3) (r := 120) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1760928 : Real) ^ (1 / (3 : Real))⌋₊ = 120 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1760928 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (120 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 4) (r := 36) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1760928 : Real) ^ (1 / (4 : Real))⌋₊ = 36 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1760928 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (36 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1760928 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1760928 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1760928 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1760928 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1760928 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1760928 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1760928 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1760928 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1760928 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1760928 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1760928 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1760928 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1760928 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1760928 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1760928 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1760928 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1760928 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1760928 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1760928 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1760928 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1760928 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1760928 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1760928 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1760928 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1760928 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1760928 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1760928 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1760928 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1760928 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1760928 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1760928 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1760928 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1760928 : Real)) =
      Chebyshev.theta (1326 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1760928 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1326, dusart_theta_nat_120, dusart_theta_nat_36, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1760929_1957200 :
    Chebyshev.psi (1957200 : Real) - Chebyshev.theta 1957200 -
        Chebyshev.theta (Real.sqrt (1957200 : Real)) <
      (1777745 : Real) / 1000000 * (1760929 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1957200 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1957200 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 2) (r := 1398) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1957200 : Real) ^ (1 / (2 : Real))⌋₊ = 1398 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1957200 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1398 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 3) (r := 125) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1957200 : Real) ^ (1 / (3 : Real))⌋₊ = 125 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1957200 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (125 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 4) (r := 37) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1957200 : Real) ^ (1 / (4 : Real))⌋₊ = 37 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1957200 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (37 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 5) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1957200 : Real) ^ (1 / (5 : Real))⌋₊ = 18 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1957200 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1957200 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1957200 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1957200 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1957200 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1957200 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1957200 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1957200 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1957200 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1957200 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1957200 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1957200 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1957200 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1957200 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1957200 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1957200 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1957200 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1957200 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1957200 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1957200 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1957200 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1957200 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1957200 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1957200 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1957200 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1957200 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1957200 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1957200 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1957200 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1957200) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1957200 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1957200 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1957200 : Real)) =
      Chebyshev.theta (1398 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1957200 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1398, dusart_theta_nat_125, dusart_theta_nat_37, dusart_theta_nat_18, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1957201_2053488 :
    Chebyshev.psi (2053488 : Real) - Chebyshev.theta 2053488 -
        Chebyshev.theta (Real.sqrt (2053488 : Real)) <
      (1777745 : Real) / 1000000 * (1957201 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2053488 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2053488 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 2) (r := 1432) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2053488 : Real) ^ (1 / (2 : Real))⌋₊ = 1432 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2053488 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1432 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 3) (r := 127) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2053488 : Real) ^ (1 / (3 : Real))⌋₊ = 127 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2053488 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (127 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 4) (r := 37) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2053488 : Real) ^ (1 / (4 : Real))⌋₊ = 37 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2053488 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (37 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 5) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2053488 : Real) ^ (1 / (5 : Real))⌋₊ = 18 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2053488 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2053488 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2053488 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2053488 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2053488 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2053488 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2053488 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2053488 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2053488 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2053488 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2053488 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2053488 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2053488 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(2053488 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((2053488 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(2053488 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((2053488 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(2053488 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((2053488 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(2053488 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((2053488 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(2053488 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((2053488 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(2053488 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((2053488 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(2053488 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((2053488 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(2053488 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((2053488 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2053488) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(2053488 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((2053488 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2053488 : Real)) =
      Chebyshev.theta (1432 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2053488 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1432, dusart_theta_nat_127, dusart_theta_nat_37, dusart_theta_nat_18, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2053489_2163840 :
    Chebyshev.psi (2163840 : Real) - Chebyshev.theta 2163840 -
        Chebyshev.theta (Real.sqrt (2163840 : Real)) <
      (1777745 : Real) / 1000000 * (2053489 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2163840 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2163840 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 2) (r := 1470) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2163840 : Real) ^ (1 / (2 : Real))⌋₊ = 1470 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2163840 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1470 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 3) (r := 129) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2163840 : Real) ^ (1 / (3 : Real))⌋₊ = 129 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2163840 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (129 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 4) (r := 38) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2163840 : Real) ^ (1 / (4 : Real))⌋₊ = 38 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2163840 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (38 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 5) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2163840 : Real) ^ (1 / (5 : Real))⌋₊ = 18 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2163840 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2163840 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2163840 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2163840 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2163840 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2163840 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2163840 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2163840 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2163840 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2163840 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2163840 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2163840 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2163840 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(2163840 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((2163840 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(2163840 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((2163840 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(2163840 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((2163840 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(2163840 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((2163840 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(2163840 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((2163840 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(2163840 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((2163840 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(2163840 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((2163840 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(2163840 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((2163840 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(2163840 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((2163840 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2163840) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(2163840 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((2163840 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2163840 : Real)) =
      Chebyshev.theta (1470 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2163840 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1470, dusart_theta_nat_129, dusart_theta_nat_38, dusart_theta_nat_18, dusart_theta_nat_11, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2163841_2247000 :
    Chebyshev.psi (2247000 : Real) - Chebyshev.theta 2247000 -
        Chebyshev.theta (Real.sqrt (2247000 : Real)) <
      (1777745 : Real) / 1000000 * (2163841 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2247000 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2247000 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 2) (r := 1498) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2247000 : Real) ^ (1 / (2 : Real))⌋₊ = 1498 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2247000 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1498 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 3) (r := 130) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2247000 : Real) ^ (1 / (3 : Real))⌋₊ = 130 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2247000 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (130 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 4) (r := 38) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2247000 : Real) ^ (1 / (4 : Real))⌋₊ = 38 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2247000 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (38 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 5) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2247000 : Real) ^ (1 / (5 : Real))⌋₊ = 18 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2247000 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2247000 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2247000 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2247000 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2247000 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2247000 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2247000 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2247000 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2247000 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2247000 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2247000 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2247000 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2247000 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(2247000 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((2247000 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(2247000 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((2247000 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(2247000 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((2247000 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(2247000 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((2247000 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(2247000 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((2247000 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(2247000 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((2247000 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(2247000 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((2247000 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(2247000 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((2247000 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(2247000 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((2247000 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2247000) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(2247000 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((2247000 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2247000 : Real)) =
      Chebyshev.theta (1498 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2247000 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1498, dusart_theta_nat_130, dusart_theta_nat_38, dusart_theta_nat_18, dusart_theta_nat_11, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2247001_2411808 :
    Chebyshev.psi (2411808 : Real) - Chebyshev.theta 2411808 -
        Chebyshev.theta (Real.sqrt (2411808 : Real)) <
      (1777745 : Real) / 1000000 * (2247001 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2411808 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2411808 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 2) (r := 1552) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2411808 : Real) ^ (1 / (2 : Real))⌋₊ = 1552 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2411808 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1552 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 3) (r := 134) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2411808 : Real) ^ (1 / (3 : Real))⌋₊ = 134 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2411808 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (134 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 4) (r := 39) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2411808 : Real) ^ (1 / (4 : Real))⌋₊ = 39 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2411808 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (39 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 5) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2411808 : Real) ^ (1 / (5 : Real))⌋₊ = 18 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2411808 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2411808 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2411808 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2411808 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2411808 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2411808 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2411808 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2411808 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2411808 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2411808 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2411808 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2411808 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2411808 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(2411808 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((2411808 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(2411808 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((2411808 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(2411808 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((2411808 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(2411808 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((2411808 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(2411808 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((2411808 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(2411808 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((2411808 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(2411808 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((2411808 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(2411808 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((2411808 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(2411808 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((2411808 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2411808) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(2411808 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((2411808 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2411808 : Real)) =
      Chebyshev.theta (1552 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2411808 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1552, dusart_theta_nat_134, dusart_theta_nat_39, dusart_theta_nat_18, dusart_theta_nat_11, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2411809_2550408 :
    Chebyshev.psi (2550408 : Real) - Chebyshev.theta 2550408 -
        Chebyshev.theta (Real.sqrt (2550408 : Real)) <
      (1777745 : Real) / 1000000 * (2411809 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2550408 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2550408 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 2) (r := 1596) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2550408 : Real) ^ (1 / (2 : Real))⌋₊ = 1596 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2550408 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1596 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 3) (r := 136) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2550408 : Real) ^ (1 / (3 : Real))⌋₊ = 136 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2550408 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (136 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 4) (r := 39) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2550408 : Real) ^ (1 / (4 : Real))⌋₊ = 39 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2550408 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (39 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 5) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2550408 : Real) ^ (1 / (5 : Real))⌋₊ = 19 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2550408 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2550408 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2550408 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2550408 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2550408 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2550408 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2550408 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2550408 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2550408 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2550408 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2550408 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2550408 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2550408 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(2550408 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((2550408 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(2550408 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((2550408 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(2550408 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((2550408 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(2550408 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((2550408 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(2550408 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((2550408 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(2550408 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((2550408 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(2550408 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((2550408 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(2550408 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((2550408 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(2550408 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((2550408 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2550408) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(2550408 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((2550408 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2550408 : Real)) =
      Chebyshev.theta (1596 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2550408 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1596, dusart_theta_nat_136, dusart_theta_nat_39, dusart_theta_nat_19, dusart_theta_nat_11, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2550409_2627640 :
    Chebyshev.psi (2627640 : Real) - Chebyshev.theta 2627640 -
        Chebyshev.theta (Real.sqrt (2627640 : Real)) <
      (1777745 : Real) / 1000000 * (2550409 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2627640 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2627640 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 2) (r := 1620) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2627640 : Real) ^ (1 / (2 : Real))⌋₊ = 1620 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2627640 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1620 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 3) (r := 137) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2627640 : Real) ^ (1 / (3 : Real))⌋₊ = 137 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2627640 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (137 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 4) (r := 40) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2627640 : Real) ^ (1 / (4 : Real))⌋₊ = 40 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2627640 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (40 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 5) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2627640 : Real) ^ (1 / (5 : Real))⌋₊ = 19 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2627640 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2627640 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2627640 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2627640 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2627640 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2627640 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2627640 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2627640 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2627640 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2627640 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2627640 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2627640 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2627640 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(2627640 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((2627640 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(2627640 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((2627640 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(2627640 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((2627640 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(2627640 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((2627640 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(2627640 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((2627640 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(2627640 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((2627640 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(2627640 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((2627640 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(2627640 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((2627640 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(2627640 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((2627640 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2627640) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(2627640 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((2627640 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2627640 : Real)) =
      Chebyshev.theta (1620 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2627640 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1620, dusart_theta_nat_137, dusart_theta_nat_40, dusart_theta_nat_19, dusart_theta_nat_11, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2627641_2785560 :
    Chebyshev.psi (2785560 : Real) - Chebyshev.theta 2785560 -
        Chebyshev.theta (Real.sqrt (2785560 : Real)) <
      (1777745 : Real) / 1000000 * (2627641 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2785560 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2785560 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 2) (r := 1668) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2785560 : Real) ^ (1 / (2 : Real))⌋₊ = 1668 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2785560 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1668 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 3) (r := 140) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2785560 : Real) ^ (1 / (3 : Real))⌋₊ = 140 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2785560 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (140 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 4) (r := 40) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2785560 : Real) ^ (1 / (4 : Real))⌋₊ = 40 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2785560 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (40 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 5) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2785560 : Real) ^ (1 / (5 : Real))⌋₊ = 19 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2785560 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2785560 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2785560 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2785560 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2785560 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2785560 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2785560 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2785560 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2785560 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2785560 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2785560 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2785560 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2785560 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(2785560 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((2785560 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(2785560 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((2785560 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(2785560 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((2785560 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(2785560 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((2785560 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(2785560 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((2785560 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(2785560 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((2785560 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(2785560 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((2785560 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(2785560 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((2785560 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(2785560 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((2785560 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2785560) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(2785560 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((2785560 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2785560 : Real)) =
      Chebyshev.theta (1668 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2785560 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1668, dusart_theta_nat_140, dusart_theta_nat_40, dusart_theta_nat_19, dusart_theta_nat_11, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2785561_2968728 :
    Chebyshev.psi (2968728 : Real) - Chebyshev.theta 2968728 -
        Chebyshev.theta (Real.sqrt (2968728 : Real)) <
      (1777745 : Real) / 1000000 * (2785561 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (2968728 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (2968728 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 2) (r := 1722) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(2968728 : Real) ^ (1 / (2 : Real))⌋₊ = 1722 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((2968728 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1722 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 3) (r := 143) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(2968728 : Real) ^ (1 / (3 : Real))⌋₊ = 143 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((2968728 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (143 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 4) (r := 41) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(2968728 : Real) ^ (1 / (4 : Real))⌋₊ = 41 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((2968728 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (41 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 5) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(2968728 : Real) ^ (1 / (5 : Real))⌋₊ = 19 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((2968728 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 6) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(2968728 : Real) ^ (1 / (6 : Real))⌋₊ = 11 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((2968728 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(2968728 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((2968728 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(2968728 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((2968728 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(2968728 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((2968728 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(2968728 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((2968728 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(2968728 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((2968728 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(2968728 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((2968728 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(2968728 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((2968728 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(2968728 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((2968728 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(2968728 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((2968728 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(2968728 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((2968728 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(2968728 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((2968728 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(2968728 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((2968728 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(2968728 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((2968728 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(2968728 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((2968728 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 2968728) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(2968728 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((2968728 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (2968728 : Real)) =
      Chebyshev.theta (1722 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (2968728 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1722, dusart_theta_nat_143, dusart_theta_nat_41, dusart_theta_nat_19, dusart_theta_nat_11, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_2968729_3179088 :
    Chebyshev.psi (3179088 : Real) - Chebyshev.theta 3179088 -
        Chebyshev.theta (Real.sqrt (3179088 : Real)) <
      (1777745 : Real) / 1000000 * (2968729 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (3179088 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (3179088 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 2) (r := 1782) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(3179088 : Real) ^ (1 / (2 : Real))⌋₊ = 1782 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((3179088 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1782 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 3) (r := 147) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(3179088 : Real) ^ (1 / (3 : Real))⌋₊ = 147 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((3179088 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (147 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 4) (r := 42) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(3179088 : Real) ^ (1 / (4 : Real))⌋₊ = 42 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((3179088 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (42 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 5) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(3179088 : Real) ^ (1 / (5 : Real))⌋₊ = 19 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((3179088 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 6) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(3179088 : Real) ^ (1 / (6 : Real))⌋₊ = 12 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((3179088 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(3179088 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((3179088 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(3179088 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((3179088 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(3179088 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((3179088 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(3179088 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((3179088 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(3179088 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((3179088 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(3179088 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((3179088 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(3179088 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((3179088 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(3179088 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((3179088 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(3179088 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((3179088 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(3179088 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((3179088 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(3179088 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((3179088 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(3179088 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((3179088 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(3179088 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((3179088 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(3179088 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((3179088 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3179088) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(3179088 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((3179088 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (3179088 : Real)) =
      Chebyshev.theta (1782 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (3179088 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1782, dusart_theta_nat_147, dusart_theta_nat_42, dusart_theta_nat_19, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_3179089_3411408 :
    Chebyshev.psi (3411408 : Real) - Chebyshev.theta 3411408 -
        Chebyshev.theta (Real.sqrt (3411408 : Real)) <
      (1777745 : Real) / 1000000 * (3179089 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (3411408 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (3411408 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 2) (r := 1846) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(3411408 : Real) ^ (1 / (2 : Real))⌋₊ = 1846 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((3411408 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1846 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 3) (r := 150) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(3411408 : Real) ^ (1 / (3 : Real))⌋₊ = 150 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((3411408 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (150 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 4) (r := 42) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(3411408 : Real) ^ (1 / (4 : Real))⌋₊ = 42 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((3411408 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (42 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 5) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(3411408 : Real) ^ (1 / (5 : Real))⌋₊ = 20 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((3411408 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 6) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(3411408 : Real) ^ (1 / (6 : Real))⌋₊ = 12 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((3411408 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(3411408 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((3411408 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(3411408 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((3411408 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(3411408 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((3411408 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(3411408 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((3411408 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(3411408 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((3411408 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(3411408 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((3411408 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(3411408 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((3411408 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(3411408 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((3411408 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(3411408 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((3411408 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(3411408 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((3411408 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(3411408 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((3411408 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(3411408 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((3411408 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(3411408 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((3411408 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(3411408 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((3411408 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3411408) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(3411408 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((3411408 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (3411408 : Real)) =
      Chebyshev.theta (1846 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (3411408 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1846, dusart_theta_nat_150, dusart_theta_nat_42, dusart_theta_nat_20, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_3411409_3530640 :
    Chebyshev.psi (3530640 : Real) - Chebyshev.theta 3530640 -
        Chebyshev.theta (Real.sqrt (3530640 : Real)) <
      (1777745 : Real) / 1000000 * (3411409 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (3530640 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (3530640 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 2) (r := 1878) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(3530640 : Real) ^ (1 / (2 : Real))⌋₊ = 1878 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((3530640 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1878 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 3) (r := 152) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(3530640 : Real) ^ (1 / (3 : Real))⌋₊ = 152 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((3530640 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (152 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 4) (r := 43) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(3530640 : Real) ^ (1 / (4 : Real))⌋₊ = 43 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((3530640 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (43 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 5) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(3530640 : Real) ^ (1 / (5 : Real))⌋₊ = 20 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((3530640 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 6) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(3530640 : Real) ^ (1 / (6 : Real))⌋₊ = 12 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((3530640 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(3530640 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((3530640 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(3530640 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((3530640 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(3530640 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((3530640 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(3530640 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((3530640 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(3530640 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((3530640 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(3530640 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((3530640 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(3530640 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((3530640 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(3530640 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((3530640 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(3530640 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((3530640 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(3530640 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((3530640 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(3530640 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((3530640 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(3530640 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((3530640 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(3530640 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((3530640 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(3530640 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((3530640 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3530640) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(3530640 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((3530640 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (3530640 : Real)) =
      Chebyshev.theta (1878 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (3530640 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1878, dusart_theta_nat_152, dusart_theta_nat_43, dusart_theta_nat_20, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_3530641_3798600 :
    Chebyshev.psi (3798600 : Real) - Chebyshev.theta 3798600 -
        Chebyshev.theta (Real.sqrt (3798600 : Real)) <
      (1777745 : Real) / 1000000 * (3530641 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (3798600 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (3798600 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 2) (r := 1948) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(3798600 : Real) ^ (1 / (2 : Real))⌋₊ = 1948 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((3798600 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1948 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 3) (r := 156) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(3798600 : Real) ^ (1 / (3 : Real))⌋₊ = 156 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((3798600 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (156 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 4) (r := 44) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(3798600 : Real) ^ (1 / (4 : Real))⌋₊ = 44 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((3798600 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (44 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 5) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(3798600 : Real) ^ (1 / (5 : Real))⌋₊ = 20 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((3798600 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 6) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(3798600 : Real) ^ (1 / (6 : Real))⌋₊ = 12 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((3798600 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(3798600 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((3798600 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(3798600 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((3798600 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(3798600 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((3798600 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(3798600 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((3798600 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(3798600 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((3798600 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(3798600 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((3798600 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(3798600 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((3798600 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(3798600 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((3798600 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(3798600 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((3798600 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(3798600 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((3798600 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(3798600 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((3798600 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(3798600 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((3798600 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(3798600 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((3798600 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(3798600 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((3798600 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3798600) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(3798600 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((3798600 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (3798600 : Real)) =
      Chebyshev.theta (1948 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (3798600 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1948, dusart_theta_nat_156, dusart_theta_nat_44, dusart_theta_nat_20, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_3798601_3996000 :
    Chebyshev.psi (3996000 : Real) - Chebyshev.theta 3996000 -
        Chebyshev.theta (Real.sqrt (3996000 : Real)) <
      (1777745 : Real) / 1000000 * (3798601 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (3996000 : Real) / Real.log 2⌋₊ ≤ 21 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (3996000 : Real) < Real.log ((2 : Real) ^ 22) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 2) (r := 1998) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(3996000 : Real) ^ (1 / (2 : Real))⌋₊ = 1998 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((3996000 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1998 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 3) (r := 158) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(3996000 : Real) ^ (1 / (3 : Real))⌋₊ = 158 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((3996000 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (158 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 4) (r := 44) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(3996000 : Real) ^ (1 / (4 : Real))⌋₊ = 44 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((3996000 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (44 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 5) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(3996000 : Real) ^ (1 / (5 : Real))⌋₊ = 20 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((3996000 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 6) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(3996000 : Real) ^ (1 / (6 : Real))⌋₊ = 12 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((3996000 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(3996000 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((3996000 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(3996000 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((3996000 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(3996000 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((3996000 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(3996000 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((3996000 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(3996000 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((3996000 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(3996000 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((3996000 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(3996000 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((3996000 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(3996000 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((3996000 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(3996000 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((3996000 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(3996000 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((3996000 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(3996000 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((3996000 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(3996000 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((3996000 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(3996000 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((3996000 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(3996000 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((3996000 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 3996000) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(3996000 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((3996000 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (3996000 : Real)) =
      Chebyshev.theta (1998 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (3996000 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, hsqrt]
  rw [dusart_theta_nat_1998, dusart_theta_nat_158, dusart_theta_nat_44, dusart_theta_nat_20, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_3996001_4255968 :
    Chebyshev.psi (4255968 : Real) - Chebyshev.theta 4255968 -
        Chebyshev.theta (Real.sqrt (4255968 : Real)) <
      (1777745 : Real) / 1000000 * (3996001 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (4255968 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (4255968 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 2) (r := 2062) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(4255968 : Real) ^ (1 / (2 : Real))⌋₊ = 2062 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((4255968 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2062 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 3) (r := 162) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(4255968 : Real) ^ (1 / (3 : Real))⌋₊ = 162 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((4255968 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (162 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 4) (r := 45) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(4255968 : Real) ^ (1 / (4 : Real))⌋₊ = 45 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((4255968 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (45 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 5) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(4255968 : Real) ^ (1 / (5 : Real))⌋₊ = 21 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((4255968 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 6) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(4255968 : Real) ^ (1 / (6 : Real))⌋₊ = 12 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((4255968 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(4255968 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((4255968 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(4255968 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((4255968 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(4255968 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((4255968 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(4255968 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((4255968 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(4255968 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((4255968 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(4255968 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((4255968 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(4255968 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((4255968 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(4255968 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((4255968 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(4255968 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((4255968 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(4255968 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((4255968 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(4255968 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((4255968 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(4255968 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((4255968 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(4255968 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((4255968 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(4255968 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((4255968 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(4255968 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((4255968 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4255968) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(4255968 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((4255968 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (4255968 : Real)) =
      Chebyshev.theta (2062 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (4255968 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2062, dusart_theta_nat_162, dusart_theta_nat_45, dusart_theta_nat_21, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_4255969_4464768 :
    Chebyshev.psi (4464768 : Real) - Chebyshev.theta 4464768 -
        Chebyshev.theta (Real.sqrt (4464768 : Real)) <
      (1777745 : Real) / 1000000 * (4255969 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (4464768 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (4464768 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 2) (r := 2112) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(4464768 : Real) ^ (1 / (2 : Real))⌋₊ = 2112 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((4464768 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2112 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 3) (r := 164) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(4464768 : Real) ^ (1 / (3 : Real))⌋₊ = 164 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((4464768 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (164 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 4) (r := 45) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(4464768 : Real) ^ (1 / (4 : Real))⌋₊ = 45 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((4464768 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (45 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 5) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(4464768 : Real) ^ (1 / (5 : Real))⌋₊ = 21 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((4464768 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 6) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(4464768 : Real) ^ (1 / (6 : Real))⌋₊ = 12 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((4464768 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(4464768 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((4464768 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(4464768 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((4464768 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(4464768 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((4464768 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(4464768 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((4464768 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(4464768 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((4464768 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(4464768 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((4464768 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(4464768 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((4464768 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(4464768 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((4464768 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(4464768 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((4464768 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(4464768 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((4464768 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(4464768 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((4464768 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(4464768 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((4464768 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(4464768 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((4464768 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(4464768 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((4464768 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(4464768 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((4464768 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4464768) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(4464768 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((4464768 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (4464768 : Real)) =
      Chebyshev.theta (2112 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (4464768 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2112, dusart_theta_nat_164, dusart_theta_nat_45, dusart_theta_nat_21, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_4464769_4748040 :
    Chebyshev.psi (4748040 : Real) - Chebyshev.theta 4748040 -
        Chebyshev.theta (Real.sqrt (4748040 : Real)) <
      (1777745 : Real) / 1000000 * (4464769 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (4748040 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (4748040 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 2) (r := 2178) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(4748040 : Real) ^ (1 / (2 : Real))⌋₊ = 2178 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((4748040 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2178 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 3) (r := 168) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(4748040 : Real) ^ (1 / (3 : Real))⌋₊ = 168 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((4748040 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (168 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 4) (r := 46) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(4748040 : Real) ^ (1 / (4 : Real))⌋₊ = 46 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((4748040 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (46 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 5) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(4748040 : Real) ^ (1 / (5 : Real))⌋₊ = 21 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((4748040 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 6) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(4748040 : Real) ^ (1 / (6 : Real))⌋₊ = 12 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((4748040 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 7) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(4748040 : Real) ^ (1 / (7 : Real))⌋₊ = 8 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((4748040 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(4748040 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((4748040 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(4748040 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((4748040 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(4748040 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((4748040 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(4748040 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((4748040 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(4748040 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((4748040 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(4748040 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((4748040 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(4748040 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((4748040 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(4748040 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((4748040 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(4748040 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((4748040 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(4748040 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((4748040 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(4748040 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((4748040 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(4748040 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((4748040 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(4748040 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((4748040 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(4748040 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((4748040 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4748040) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(4748040 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((4748040 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (4748040 : Real)) =
      Chebyshev.theta (2178 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (4748040 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2178, dusart_theta_nat_168, dusart_theta_nat_46, dusart_theta_nat_21, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_4748041_5031048 :
    Chebyshev.psi (5031048 : Real) - Chebyshev.theta 5031048 -
        Chebyshev.theta (Real.sqrt (5031048 : Real)) <
      (1777745 : Real) / 1000000 * (4748041 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (5031048 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (5031048 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 2) (r := 2242) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(5031048 : Real) ^ (1 / (2 : Real))⌋₊ = 2242 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((5031048 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2242 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 3) (r := 171) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(5031048 : Real) ^ (1 / (3 : Real))⌋₊ = 171 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((5031048 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (171 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 4) (r := 47) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(5031048 : Real) ^ (1 / (4 : Real))⌋₊ = 47 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((5031048 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (47 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 5) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(5031048 : Real) ^ (1 / (5 : Real))⌋₊ = 21 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((5031048 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(5031048 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((5031048 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(5031048 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((5031048 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(5031048 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((5031048 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(5031048 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((5031048 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(5031048 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((5031048 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(5031048 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((5031048 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(5031048 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((5031048 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(5031048 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((5031048 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(5031048 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((5031048 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(5031048 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((5031048 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(5031048 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((5031048 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(5031048 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((5031048 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(5031048 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((5031048 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(5031048 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((5031048 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(5031048 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((5031048 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(5031048 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((5031048 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5031048) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(5031048 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((5031048 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (5031048 : Real)) =
      Chebyshev.theta (2242 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (5031048 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2242, dusart_theta_nat_171, dusart_theta_nat_47, dusart_theta_nat_21, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_5031049_5257848 :
    Chebyshev.psi (5257848 : Real) - Chebyshev.theta 5257848 -
        Chebyshev.theta (Real.sqrt (5257848 : Real)) <
      (1777745 : Real) / 1000000 * (5031049 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (5257848 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (5257848 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 2) (r := 2292) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(5257848 : Real) ^ (1 / (2 : Real))⌋₊ = 2292 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((5257848 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2292 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 3) (r := 173) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(5257848 : Real) ^ (1 / (3 : Real))⌋₊ = 173 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((5257848 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (173 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 4) (r := 47) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(5257848 : Real) ^ (1 / (4 : Real))⌋₊ = 47 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((5257848 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (47 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 5) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(5257848 : Real) ^ (1 / (5 : Real))⌋₊ = 22 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((5257848 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(5257848 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((5257848 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(5257848 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((5257848 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(5257848 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((5257848 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(5257848 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((5257848 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(5257848 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((5257848 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(5257848 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((5257848 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(5257848 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((5257848 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(5257848 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((5257848 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(5257848 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((5257848 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(5257848 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((5257848 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(5257848 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((5257848 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(5257848 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((5257848 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(5257848 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((5257848 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(5257848 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((5257848 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(5257848 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((5257848 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(5257848 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((5257848 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5257848) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(5257848 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((5257848 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (5257848 : Real)) =
      Chebyshev.theta (2292 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (5257848 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2292, dusart_theta_nat_173, dusart_theta_nat_47, dusart_theta_nat_22, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_5257849_5527200 :
    Chebyshev.psi (5527200 : Real) - Chebyshev.theta 5527200 -
        Chebyshev.theta (Real.sqrt (5527200 : Real)) <
      (1777745 : Real) / 1000000 * (5257849 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (5527200 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (5527200 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 2) (r := 2350) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(5527200 : Real) ^ (1 / (2 : Real))⌋₊ = 2350 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((5527200 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2350 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 3) (r := 176) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(5527200 : Real) ^ (1 / (3 : Real))⌋₊ = 176 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((5527200 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (176 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 4) (r := 48) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(5527200 : Real) ^ (1 / (4 : Real))⌋₊ = 48 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((5527200 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (48 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 5) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(5527200 : Real) ^ (1 / (5 : Real))⌋₊ = 22 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((5527200 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(5527200 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((5527200 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(5527200 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((5527200 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(5527200 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((5527200 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(5527200 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((5527200 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(5527200 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((5527200 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(5527200 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((5527200 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(5527200 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((5527200 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(5527200 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((5527200 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(5527200 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((5527200 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(5527200 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((5527200 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(5527200 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((5527200 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(5527200 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((5527200 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(5527200 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((5527200 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(5527200 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((5527200 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(5527200 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((5527200 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(5527200 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((5527200 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5527200) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(5527200 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((5527200 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (5527200 : Real)) =
      Chebyshev.theta (2350 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (5527200 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2350, dusart_theta_nat_176, dusart_theta_nat_48, dusart_theta_nat_22, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_5527201_5755200 :
    Chebyshev.psi (5755200 : Real) - Chebyshev.theta 5755200 -
        Chebyshev.theta (Real.sqrt (5755200 : Real)) <
      (1777745 : Real) / 1000000 * (5527201 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (5755200 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (5755200 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 2) (r := 2398) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(5755200 : Real) ^ (1 / (2 : Real))⌋₊ = 2398 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((5755200 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2398 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 3) (r := 179) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(5755200 : Real) ^ (1 / (3 : Real))⌋₊ = 179 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((5755200 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (179 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 4) (r := 48) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(5755200 : Real) ^ (1 / (4 : Real))⌋₊ = 48 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((5755200 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (48 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 5) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(5755200 : Real) ^ (1 / (5 : Real))⌋₊ = 22 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((5755200 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(5755200 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((5755200 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(5755200 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((5755200 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(5755200 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((5755200 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(5755200 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((5755200 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(5755200 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((5755200 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(5755200 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((5755200 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(5755200 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((5755200 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(5755200 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((5755200 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(5755200 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((5755200 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(5755200 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((5755200 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(5755200 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((5755200 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(5755200 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((5755200 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(5755200 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((5755200 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(5755200 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((5755200 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(5755200 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((5755200 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(5755200 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((5755200 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5755200) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(5755200 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((5755200 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (5755200 : Real)) =
      Chebyshev.theta (2398 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (5755200 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2398, dusart_theta_nat_179, dusart_theta_nat_48, dusart_theta_nat_22, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_5755201_6086088 :
    Chebyshev.psi (6086088 : Real) - Chebyshev.theta 6086088 -
        Chebyshev.theta (Real.sqrt (6086088 : Real)) <
      (1777745 : Real) / 1000000 * (5755201 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6086088 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6086088 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 2) (r := 2466) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6086088 : Real) ^ (1 / (2 : Real))⌋₊ = 2466 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6086088 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2466 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 3) (r := 182) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6086088 : Real) ^ (1 / (3 : Real))⌋₊ = 182 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6086088 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (182 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 4) (r := 49) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6086088 : Real) ^ (1 / (4 : Real))⌋₊ = 49 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6086088 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (49 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 5) (r := 22) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6086088 : Real) ^ (1 / (5 : Real))⌋₊ = 22 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6086088 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (22 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6086088 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6086088 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6086088 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6086088 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6086088 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6086088 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6086088 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6086088 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6086088 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6086088 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6086088 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6086088 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6086088 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6086088 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(6086088 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((6086088 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(6086088 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((6086088 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(6086088 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((6086088 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(6086088 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((6086088 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(6086088 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((6086088 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(6086088 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((6086088 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(6086088 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((6086088 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(6086088 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((6086088 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(6086088 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((6086088 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6086088) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(6086088 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((6086088 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6086088 : Real)) =
      Chebyshev.theta (2466 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6086088 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2466, dusart_theta_nat_182, dusart_theta_nat_49, dusart_theta_nat_22, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_6086089_6497400 :
    Chebyshev.psi (6497400 : Real) - Chebyshev.theta 6497400 -
        Chebyshev.theta (Real.sqrt (6497400 : Real)) <
      (1777745 : Real) / 1000000 * (6086089 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6497400 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6497400 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 2) (r := 2548) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6497400 : Real) ^ (1 / (2 : Real))⌋₊ = 2548 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6497400 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2548 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 3) (r := 186) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6497400 : Real) ^ (1 / (3 : Real))⌋₊ = 186 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6497400 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (186 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 4) (r := 50) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6497400 : Real) ^ (1 / (4 : Real))⌋₊ = 50 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6497400 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (50 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 5) (r := 23) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6497400 : Real) ^ (1 / (5 : Real))⌋₊ = 23 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6497400 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (23 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6497400 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6497400 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6497400 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6497400 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6497400 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6497400 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6497400 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6497400 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6497400 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6497400 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6497400 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6497400 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6497400 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6497400 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(6497400 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((6497400 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(6497400 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((6497400 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(6497400 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((6497400 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(6497400 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((6497400 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(6497400 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((6497400 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(6497400 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((6497400 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(6497400 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((6497400 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(6497400 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((6497400 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(6497400 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((6497400 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6497400) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(6497400 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((6497400 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6497400 : Real)) =
      Chebyshev.theta (2548 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6497400 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2548, dusart_theta_nat_186, dusart_theta_nat_50, dusart_theta_nat_23, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_6497401_6932688 :
    Chebyshev.psi (6932688 : Real) - Chebyshev.theta 6932688 -
        Chebyshev.theta (Real.sqrt (6932688 : Real)) <
      (1777745 : Real) / 1000000 * (6497401 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6932688 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6932688 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 2) (r := 2632) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6932688 : Real) ^ (1 / (2 : Real))⌋₊ = 2632 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6932688 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2632 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 3) (r := 190) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6932688 : Real) ^ (1 / (3 : Real))⌋₊ = 190 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6932688 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (190 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 4) (r := 51) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6932688 : Real) ^ (1 / (4 : Real))⌋₊ = 51 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6932688 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (51 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 5) (r := 23) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6932688 : Real) ^ (1 / (5 : Real))⌋₊ = 23 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6932688 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (23 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6932688 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6932688 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6932688 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6932688 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6932688 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6932688 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6932688 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6932688 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6932688 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6932688 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6932688 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6932688 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6932688 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6932688 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(6932688 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((6932688 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(6932688 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((6932688 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(6932688 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((6932688 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(6932688 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((6932688 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(6932688 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((6932688 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(6932688 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((6932688 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(6932688 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((6932688 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(6932688 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((6932688 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(6932688 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((6932688 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6932688) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(6932688 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((6932688 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6932688 : Real)) =
      Chebyshev.theta (2632 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6932688 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2632, dusart_theta_nat_190, dusart_theta_nat_51, dusart_theta_nat_23, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_6932689_7219968 :
    Chebyshev.psi (7219968 : Real) - Chebyshev.theta 7219968 -
        Chebyshev.theta (Real.sqrt (7219968 : Real)) <
      (1777745 : Real) / 1000000 * (6932689 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (7219968 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (7219968 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 2) (r := 2686) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(7219968 : Real) ^ (1 / (2 : Real))⌋₊ = 2686 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((7219968 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2686 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 3) (r := 193) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(7219968 : Real) ^ (1 / (3 : Real))⌋₊ = 193 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((7219968 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (193 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 4) (r := 51) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(7219968 : Real) ^ (1 / (4 : Real))⌋₊ = 51 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((7219968 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (51 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 5) (r := 23) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(7219968 : Real) ^ (1 / (5 : Real))⌋₊ = 23 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((7219968 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (23 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(7219968 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((7219968 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(7219968 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((7219968 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(7219968 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((7219968 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(7219968 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((7219968 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(7219968 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((7219968 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(7219968 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((7219968 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(7219968 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((7219968 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(7219968 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((7219968 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(7219968 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((7219968 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(7219968 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((7219968 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(7219968 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((7219968 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(7219968 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((7219968 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(7219968 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((7219968 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(7219968 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((7219968 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(7219968 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((7219968 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(7219968 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((7219968 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7219968) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(7219968 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((7219968 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (7219968 : Real)) =
      Chebyshev.theta (2686 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (7219968 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2686, dusart_theta_nat_193, dusart_theta_nat_51, dusart_theta_nat_23, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_7219969_7458360 :
    Chebyshev.psi (7458360 : Real) - Chebyshev.theta 7458360 -
        Chebyshev.theta (Real.sqrt (7458360 : Real)) <
      (1777745 : Real) / 1000000 * (7219969 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (7458360 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (7458360 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 2) (r := 2730) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(7458360 : Real) ^ (1 / (2 : Real))⌋₊ = 2730 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((7458360 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2730 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 3) (r := 195) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(7458360 : Real) ^ (1 / (3 : Real))⌋₊ = 195 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((7458360 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (195 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 4) (r := 52) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(7458360 : Real) ^ (1 / (4 : Real))⌋₊ = 52 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((7458360 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (52 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 5) (r := 23) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(7458360 : Real) ^ (1 / (5 : Real))⌋₊ = 23 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((7458360 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (23 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 6) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(7458360 : Real) ^ (1 / (6 : Real))⌋₊ = 13 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((7458360 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(7458360 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((7458360 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(7458360 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((7458360 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(7458360 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((7458360 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(7458360 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((7458360 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(7458360 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((7458360 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(7458360 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((7458360 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(7458360 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((7458360 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(7458360 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((7458360 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(7458360 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((7458360 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(7458360 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((7458360 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(7458360 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((7458360 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(7458360 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((7458360 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(7458360 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((7458360 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(7458360 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((7458360 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(7458360 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((7458360 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7458360) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(7458360 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((7458360 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (7458360 : Real)) =
      Chebyshev.theta (2730 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (7458360 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2730, dusart_theta_nat_195, dusart_theta_nat_52, dusart_theta_nat_23, dusart_theta_nat_13, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_7458361_7845600 :
    Chebyshev.psi (7845600 : Real) - Chebyshev.theta 7845600 -
        Chebyshev.theta (Real.sqrt (7845600 : Real)) <
      (1777745 : Real) / 1000000 * (7458361 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (7845600 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (7845600 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 2) (r := 2800) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(7845600 : Real) ^ (1 / (2 : Real))⌋₊ = 2800 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((7845600 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2800 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 3) (r := 198) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(7845600 : Real) ^ (1 / (3 : Real))⌋₊ = 198 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((7845600 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (198 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 4) (r := 52) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(7845600 : Real) ^ (1 / (4 : Real))⌋₊ = 52 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((7845600 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (52 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 5) (r := 23) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(7845600 : Real) ^ (1 / (5 : Real))⌋₊ = 23 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((7845600 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (23 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 6) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(7845600 : Real) ^ (1 / (6 : Real))⌋₊ = 14 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((7845600 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(7845600 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((7845600 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(7845600 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((7845600 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(7845600 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((7845600 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(7845600 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((7845600 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(7845600 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((7845600 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(7845600 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((7845600 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(7845600 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((7845600 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(7845600 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((7845600 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(7845600 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((7845600 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(7845600 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((7845600 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(7845600 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((7845600 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(7845600 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((7845600 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(7845600 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((7845600 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(7845600 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((7845600 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(7845600 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((7845600 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7845600) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(7845600 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((7845600 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (7845600 : Real)) =
      Chebyshev.theta (2800 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (7845600 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2800, dusart_theta_nat_198, dusart_theta_nat_52, dusart_theta_nat_23, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_7845601_8185320 :
    Chebyshev.psi (8185320 : Real) - Chebyshev.theta 8185320 -
        Chebyshev.theta (Real.sqrt (8185320 : Real)) <
      (1777745 : Real) / 1000000 * (7845601 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (8185320 : Real) / Real.log 2⌋₊ ≤ 22 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (8185320 : Real) < Real.log ((2 : Real) ^ 23) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 2) (r := 2860) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(8185320 : Real) ^ (1 / (2 : Real))⌋₊ = 2860 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((8185320 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2860 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 3) (r := 201) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(8185320 : Real) ^ (1 / (3 : Real))⌋₊ = 201 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((8185320 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (201 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 4) (r := 53) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(8185320 : Real) ^ (1 / (4 : Real))⌋₊ = 53 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((8185320 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (53 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 5) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(8185320 : Real) ^ (1 / (5 : Real))⌋₊ = 24 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((8185320 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 6) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(8185320 : Real) ^ (1 / (6 : Real))⌋₊ = 14 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((8185320 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(8185320 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((8185320 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(8185320 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((8185320 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(8185320 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((8185320 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(8185320 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((8185320 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(8185320 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((8185320 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(8185320 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((8185320 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(8185320 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((8185320 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(8185320 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((8185320 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(8185320 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((8185320 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(8185320 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((8185320 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(8185320 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((8185320 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(8185320 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((8185320 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(8185320 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((8185320 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(8185320 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((8185320 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(8185320 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((8185320 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8185320) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(8185320 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((8185320 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (8185320 : Real)) =
      Chebyshev.theta (2860 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (8185320 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, hsqrt]
  rw [dusart_theta_nat_2860, dusart_theta_nat_201, dusart_theta_nat_53, dusart_theta_nat_24, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_8185321_8720208 :
    Chebyshev.psi (8720208 : Real) - Chebyshev.theta 8720208 -
        Chebyshev.theta (Real.sqrt (8720208 : Real)) <
      (1777745 : Real) / 1000000 * (8185321 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (8720208 : Real) / Real.log 2⌋₊ ≤ 23 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (8720208 : Real) < Real.log ((2 : Real) ^ 24) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 2) (r := 2952) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(8720208 : Real) ^ (1 / (2 : Real))⌋₊ = 2952 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((8720208 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (2952 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 3) (r := 205) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(8720208 : Real) ^ (1 / (3 : Real))⌋₊ = 205 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((8720208 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (205 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 4) (r := 54) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(8720208 : Real) ^ (1 / (4 : Real))⌋₊ = 54 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((8720208 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (54 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 5) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(8720208 : Real) ^ (1 / (5 : Real))⌋₊ = 24 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((8720208 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 6) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(8720208 : Real) ^ (1 / (6 : Real))⌋₊ = 14 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((8720208 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(8720208 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((8720208 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(8720208 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((8720208 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(8720208 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((8720208 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(8720208 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((8720208 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(8720208 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((8720208 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(8720208 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((8720208 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(8720208 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((8720208 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(8720208 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((8720208 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(8720208 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((8720208 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(8720208 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((8720208 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(8720208 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((8720208 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(8720208 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((8720208 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(8720208 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((8720208 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(8720208 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((8720208 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(8720208 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((8720208 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(8720208 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((8720208 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hroot_23 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 8720208) (k := 23) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_23' : ⌊(8720208 : Real) ^ (1 / (23 : Real))⌋₊ = 2 := by
    simpa using hroot_23
  have htheta_23 : Chebyshev.theta ((8720208 : Real) ^ (1 / (23 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_23']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (8720208 : Real)) =
      Chebyshev.theta (2952 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (8720208 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, htheta_23, hsqrt]
  rw [dusart_theta_nat_2952, dusart_theta_nat_205, dusart_theta_nat_54, dusart_theta_nat_24, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_8720209_9223368 :
    Chebyshev.psi (9223368 : Real) - Chebyshev.theta 9223368 -
        Chebyshev.theta (Real.sqrt (9223368 : Real)) <
      (1777745 : Real) / 1000000 * (8720209 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (9223368 : Real) / Real.log 2⌋₊ ≤ 23 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (9223368 : Real) < Real.log ((2 : Real) ^ 24) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 2) (r := 3036) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(9223368 : Real) ^ (1 / (2 : Real))⌋₊ = 3036 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((9223368 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (3036 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 3) (r := 209) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(9223368 : Real) ^ (1 / (3 : Real))⌋₊ = 209 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((9223368 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (209 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 4) (r := 55) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(9223368 : Real) ^ (1 / (4 : Real))⌋₊ = 55 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((9223368 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (55 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 5) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(9223368 : Real) ^ (1 / (5 : Real))⌋₊ = 24 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((9223368 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 6) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(9223368 : Real) ^ (1 / (6 : Real))⌋₊ = 14 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((9223368 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(9223368 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((9223368 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(9223368 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((9223368 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(9223368 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((9223368 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(9223368 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((9223368 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(9223368 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((9223368 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(9223368 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((9223368 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(9223368 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((9223368 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(9223368 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((9223368 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(9223368 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((9223368 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(9223368 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((9223368 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(9223368 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((9223368 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(9223368 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((9223368 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(9223368 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((9223368 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(9223368 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((9223368 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(9223368 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((9223368 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(9223368 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((9223368 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hroot_23 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9223368) (k := 23) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_23' : ⌊(9223368 : Real) ^ (1 / (23 : Real))⌋₊ = 2 := by
    simpa using hroot_23
  have htheta_23 : Chebyshev.theta ((9223368 : Real) ^ (1 / (23 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_23']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (9223368 : Real)) =
      Chebyshev.theta (3036 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (9223368 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, htheta_23, hsqrt]
  rw [dusart_theta_nat_3036, dusart_theta_nat_209, dusart_theta_nat_55, dusart_theta_nat_24, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_9223369_9740640 :
    Chebyshev.psi (9740640 : Real) - Chebyshev.theta 9740640 -
        Chebyshev.theta (Real.sqrt (9740640 : Real)) <
      (1777745 : Real) / 1000000 * (9223369 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (9740640 : Real) / Real.log 2⌋₊ ≤ 23 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (9740640 : Real) < Real.log ((2 : Real) ^ 24) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 2) (r := 3120) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(9740640 : Real) ^ (1 / (2 : Real))⌋₊ = 3120 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((9740640 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (3120 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 3) (r := 213) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(9740640 : Real) ^ (1 / (3 : Real))⌋₊ = 213 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((9740640 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (213 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 4) (r := 55) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(9740640 : Real) ^ (1 / (4 : Real))⌋₊ = 55 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((9740640 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (55 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 5) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(9740640 : Real) ^ (1 / (5 : Real))⌋₊ = 24 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((9740640 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 6) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(9740640 : Real) ^ (1 / (6 : Real))⌋₊ = 14 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((9740640 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 7) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(9740640 : Real) ^ (1 / (7 : Real))⌋₊ = 9 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((9740640 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(9740640 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((9740640 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(9740640 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((9740640 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(9740640 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((9740640 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(9740640 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((9740640 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(9740640 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((9740640 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(9740640 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((9740640 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(9740640 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((9740640 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(9740640 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((9740640 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(9740640 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((9740640 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(9740640 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((9740640 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(9740640 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((9740640 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(9740640 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((9740640 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(9740640 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((9740640 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(9740640 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((9740640 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(9740640 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((9740640 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hroot_23 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9740640) (k := 23) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_23' : ⌊(9740640 : Real) ^ (1 / (23 : Real))⌋₊ = 2 := by
    simpa using hroot_23
  have htheta_23 : Chebyshev.theta ((9740640 : Real) ^ (1 / (23 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_23']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (9740640 : Real)) =
      Chebyshev.theta (3120 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (9740640 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, htheta_23, hsqrt]
  rw [dusart_theta_nat_3120, dusart_theta_nat_213, dusart_theta_nat_55, dusart_theta_nat_24, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_9740641_10000000 :
    Chebyshev.psi (10000000 : Real) - Chebyshev.theta 10000000 -
        Chebyshev.theta (Real.sqrt (10000000 : Real)) <
      (1777745 : Real) / 1000000 * (9740641 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (10000000 : Real) / Real.log 2⌋₊ ≤ 23 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (10000000 : Real) < Real.log ((2 : Real) ^ 24) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 2) (r := 3162) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(10000000 : Real) ^ (1 / (2 : Real))⌋₊ = 3162 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((10000000 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (3162 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 3) (r := 215) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(10000000 : Real) ^ (1 / (3 : Real))⌋₊ = 215 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((10000000 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (215 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 4) (r := 56) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(10000000 : Real) ^ (1 / (4 : Real))⌋₊ = 56 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((10000000 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (56 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 5) (r := 25) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(10000000 : Real) ^ (1 / (5 : Real))⌋₊ = 25 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((10000000 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (25 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 6) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(10000000 : Real) ^ (1 / (6 : Real))⌋₊ = 14 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((10000000 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 7) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(10000000 : Real) ^ (1 / (7 : Real))⌋₊ = 10 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((10000000 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(10000000 : Real) ^ (1 / (8 : Real))⌋₊ = 7 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((10000000 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 9) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(10000000 : Real) ^ (1 / (9 : Real))⌋₊ = 5 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((10000000 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 10) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(10000000 : Real) ^ (1 / (10 : Real))⌋₊ = 5 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((10000000 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 11) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(10000000 : Real) ^ (1 / (11 : Real))⌋₊ = 4 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((10000000 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(10000000 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((10000000 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(10000000 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((10000000 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 14) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(10000000 : Real) ^ (1 / (14 : Real))⌋₊ = 3 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((10000000 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(10000000 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((10000000 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(10000000 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((10000000 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(10000000 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((10000000 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(10000000 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((10000000 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(10000000 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((10000000 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(10000000 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((10000000 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hroot_21 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 21) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_21' : ⌊(10000000 : Real) ^ (1 / (21 : Real))⌋₊ = 2 := by
    simpa using hroot_21
  have htheta_21 : Chebyshev.theta ((10000000 : Real) ^ (1 / (21 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_21']
    norm_num
  have hroot_22 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 22) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_22' : ⌊(10000000 : Real) ^ (1 / (22 : Real))⌋₊ = 2 := by
    simpa using hroot_22
  have htheta_22 : Chebyshev.theta ((10000000 : Real) ^ (1 / (22 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_22']
    norm_num
  have hroot_23 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 10000000) (k := 23) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_23' : ⌊(10000000 : Real) ^ (1 / (23 : Real))⌋₊ = 2 := by
    simpa using hroot_23
  have htheta_23 : Chebyshev.theta ((10000000 : Real) ^ (1 / (23 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_23']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (10000000 : Real)) =
      Chebyshev.theta (3162 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (10000000 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, htheta_21, htheta_22, htheta_23, hsqrt]
  rw [dusart_theta_nat_3162, dusart_theta_nat_215, dusart_theta_nat_56, dusart_theta_nat_25, dusart_theta_nat_14, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality

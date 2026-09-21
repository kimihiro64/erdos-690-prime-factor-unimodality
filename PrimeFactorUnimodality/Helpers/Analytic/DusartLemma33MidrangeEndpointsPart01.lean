import LeanCert.Tactic.IntervalAuto
import PrimeFactorUnimodality.Helpers.Analytic.DusartFiniteRows
import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33ThetaData

/-! Generated endpoint proof shard 01 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

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

end

end PrimeFactorUnimodality

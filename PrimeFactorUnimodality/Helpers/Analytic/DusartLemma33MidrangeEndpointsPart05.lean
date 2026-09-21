import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart04

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

end

end PrimeFactorUnimodality

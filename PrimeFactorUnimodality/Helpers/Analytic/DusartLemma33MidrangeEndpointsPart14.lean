import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart13

/-! Generated endpoint proof shard 14 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

end

end PrimeFactorUnimodality

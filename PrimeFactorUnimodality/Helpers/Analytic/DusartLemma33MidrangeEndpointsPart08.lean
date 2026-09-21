import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart07

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

end

end PrimeFactorUnimodality

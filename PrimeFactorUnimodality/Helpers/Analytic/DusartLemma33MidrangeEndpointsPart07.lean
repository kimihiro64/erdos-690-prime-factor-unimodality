import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart06

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

end

end PrimeFactorUnimodality

import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart24

/-! Generated endpoint proof shard 25 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

end

end PrimeFactorUnimodality

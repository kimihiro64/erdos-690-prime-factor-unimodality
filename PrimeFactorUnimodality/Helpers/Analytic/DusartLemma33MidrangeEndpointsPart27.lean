import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart26

/-! Generated endpoint proof shard 27 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

end

end PrimeFactorUnimodality

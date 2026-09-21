import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart28

/-! Generated endpoint proof shard 29 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

end

end PrimeFactorUnimodality

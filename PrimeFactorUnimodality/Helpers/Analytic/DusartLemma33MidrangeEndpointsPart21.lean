import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart20

/-! Generated endpoint proof shard 21 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

end

end PrimeFactorUnimodality

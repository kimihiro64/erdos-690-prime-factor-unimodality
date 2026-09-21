import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart29

/-! Generated endpoint proof shard 30 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
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

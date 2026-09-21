import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart12

/-! Generated endpoint proof shard 13 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_151321_160800 :
    Chebyshev.psi (160800 : Real) - Chebyshev.theta 160800 -
        Chebyshev.theta (Real.sqrt (160800 : Real)) <
      (1777745 : Real) / 1000000 * (151321 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (160800 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (160800 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 2) (r := 400) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(160800 : Real) ^ (1 / (2 : Real))⌋₊ = 400 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((160800 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (400 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 3) (r := 54) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(160800 : Real) ^ (1 / (3 : Real))⌋₊ = 54 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((160800 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (54 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 4) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(160800 : Real) ^ (1 / (4 : Real))⌋₊ = 20 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((160800 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(160800 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((160800 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(160800 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((160800 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(160800 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((160800 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(160800 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((160800 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(160800 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((160800 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(160800 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((160800 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(160800 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((160800 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(160800 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((160800 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(160800 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((160800 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(160800 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((160800 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(160800 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((160800 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(160800 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((160800 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 160800) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(160800 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((160800 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (160800 : Real)) =
      Chebyshev.theta (400 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (160800 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_400, dusart_theta_nat_54, dusart_theta_nat_20, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_160801_175560 :
    Chebyshev.psi (175560 : Real) - Chebyshev.theta 175560 -
        Chebyshev.theta (Real.sqrt (175560 : Real)) <
      (1777745 : Real) / 1000000 * (160801 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (175560 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (175560 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 2) (r := 418) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(175560 : Real) ^ (1 / (2 : Real))⌋₊ = 418 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((175560 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (418 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 3) (r := 55) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(175560 : Real) ^ (1 / (3 : Real))⌋₊ = 55 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((175560 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (55 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 4) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(175560 : Real) ^ (1 / (4 : Real))⌋₊ = 20 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((175560 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(175560 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((175560 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(175560 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((175560 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(175560 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((175560 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(175560 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((175560 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(175560 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((175560 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(175560 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((175560 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(175560 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((175560 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(175560 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((175560 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(175560 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((175560 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(175560 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((175560 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(175560 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((175560 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(175560 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((175560 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 175560) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(175560 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((175560 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (175560 : Real)) =
      Chebyshev.theta (418 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (175560 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_418, dusart_theta_nat_55, dusart_theta_nat_20, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_175561_185760 :
    Chebyshev.psi (185760 : Real) - Chebyshev.theta 185760 -
        Chebyshev.theta (Real.sqrt (185760 : Real)) <
      (1777745 : Real) / 1000000 * (175561 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (185760 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (185760 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 2) (r := 430) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(185760 : Real) ^ (1 / (2 : Real))⌋₊ = 430 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((185760 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (430 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 3) (r := 57) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(185760 : Real) ^ (1 / (3 : Real))⌋₊ = 57 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((185760 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (57 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 4) (r := 20) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(185760 : Real) ^ (1 / (4 : Real))⌋₊ = 20 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((185760 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (20 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(185760 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((185760 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(185760 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((185760 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(185760 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((185760 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(185760 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((185760 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(185760 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((185760 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(185760 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((185760 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(185760 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((185760 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(185760 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((185760 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(185760 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((185760 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(185760 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((185760 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(185760 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((185760 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(185760 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((185760 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 185760) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(185760 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((185760 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (185760 : Real)) =
      Chebyshev.theta (430 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (185760 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_430, dusart_theta_nat_57, dusart_theta_nat_20, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_185761_196248 :
    Chebyshev.psi (196248 : Real) - Chebyshev.theta 196248 -
        Chebyshev.theta (Real.sqrt (196248 : Real)) <
      (1777745 : Real) / 1000000 * (185761 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (196248 : Real) / Real.log 2⌋₊ ≤ 17 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (196248 : Real) < Real.log ((2 : Real) ^ 18) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 2) (r := 442) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(196248 : Real) ^ (1 / (2 : Real))⌋₊ = 442 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((196248 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (442 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 3) (r := 58) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(196248 : Real) ^ (1 / (3 : Real))⌋₊ = 58 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((196248 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (58 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 4) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(196248 : Real) ^ (1 / (4 : Real))⌋₊ = 21 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((196248 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 5) (r := 11) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(196248 : Real) ^ (1 / (5 : Real))⌋₊ = 11 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((196248 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (11 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(196248 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((196248 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(196248 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((196248 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(196248 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((196248 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(196248 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((196248 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(196248 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((196248 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(196248 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((196248 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(196248 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((196248 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(196248 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((196248 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(196248 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((196248 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(196248 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((196248 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(196248 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((196248 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 196248) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(196248 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((196248 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (196248 : Real)) =
      Chebyshev.theta (442 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (196248 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, hsqrt]
  rw [dusart_theta_nat_442, dusart_theta_nat_58, dusart_theta_nat_21, dusart_theta_nat_11, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality

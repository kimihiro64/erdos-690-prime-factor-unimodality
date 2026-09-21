import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart21

/-! Generated endpoint proof shard 22 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_1442897_1510440 :
    Chebyshev.psi (1510440 : Real) - Chebyshev.theta 1510440 -
        Chebyshev.theta (Real.sqrt (1510440 : Real)) <
      (1777745 : Real) / 1000000 * (1442897 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1510440 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1510440 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 2) (r := 1228) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1510440 : Real) ^ (1 / (2 : Real))⌋₊ = 1228 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1510440 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1228 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 3) (r := 114) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1510440 : Real) ^ (1 / (3 : Real))⌋₊ = 114 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1510440 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (114 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 4) (r := 35) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1510440 : Real) ^ (1 / (4 : Real))⌋₊ = 35 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1510440 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (35 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1510440 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1510440 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1510440 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1510440 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1510440 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1510440 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1510440 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1510440 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1510440 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1510440 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1510440 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1510440 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1510440 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1510440 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1510440 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1510440 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1510440 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1510440 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1510440 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1510440 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1510440 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1510440 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1510440 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1510440 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1510440 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1510440 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1510440 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1510440 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1510440 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1510440 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1510440) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1510440 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1510440 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1510440 : Real)) =
      Chebyshev.theta (1228 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1510440 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1228, dusart_theta_nat_114, dusart_theta_nat_35, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1510441_1630728 :
    Chebyshev.psi (1630728 : Real) - Chebyshev.theta 1630728 -
        Chebyshev.theta (Real.sqrt (1630728 : Real)) <
      (1777745 : Real) / 1000000 * (1510441 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1630728 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1630728 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 2) (r := 1276) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1630728 : Real) ^ (1 / (2 : Real))⌋₊ = 1276 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1630728 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1276 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 3) (r := 117) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1630728 : Real) ^ (1 / (3 : Real))⌋₊ = 117 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1630728 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (117 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 4) (r := 35) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1630728 : Real) ^ (1 / (4 : Real))⌋₊ = 35 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1630728 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (35 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1630728 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1630728 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1630728 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1630728 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1630728 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1630728 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1630728 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1630728 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1630728 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1630728 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1630728 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1630728 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1630728 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1630728 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1630728 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1630728 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1630728 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1630728 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1630728 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1630728 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1630728 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1630728 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1630728 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1630728 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1630728 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1630728 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1630728 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1630728 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1630728 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1630728 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1630728) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1630728 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1630728 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1630728 : Real)) =
      Chebyshev.theta (1276 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1630728 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1276, dusart_theta_nat_117, dusart_theta_nat_35, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1630729_1682208 :
    Chebyshev.psi (1682208 : Real) - Chebyshev.theta 1682208 -
        Chebyshev.theta (Real.sqrt (1682208 : Real)) <
      (1777745 : Real) / 1000000 * (1630729 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1682208 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1682208 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 2) (r := 1296) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1682208 : Real) ^ (1 / (2 : Real))⌋₊ = 1296 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1682208 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1296 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 3) (r := 118) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1682208 : Real) ^ (1 / (3 : Real))⌋₊ = 118 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1682208 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (118 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 4) (r := 36) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1682208 : Real) ^ (1 / (4 : Real))⌋₊ = 36 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1682208 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (36 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1682208 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1682208 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1682208 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1682208 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1682208 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1682208 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1682208 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1682208 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1682208 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1682208 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1682208 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1682208 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1682208 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1682208 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1682208 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1682208 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1682208 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1682208 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1682208 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1682208 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1682208 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1682208 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1682208 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1682208 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1682208 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1682208 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1682208 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1682208 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1682208 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1682208 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1682208) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1682208 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1682208 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1682208 : Real)) =
      Chebyshev.theta (1296 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1682208 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1296, dusart_theta_nat_118, dusart_theta_nat_36, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_1682209_1760928 :
    Chebyshev.psi (1760928 : Real) - Chebyshev.theta 1760928 -
        Chebyshev.theta (Real.sqrt (1760928 : Real)) <
      (1777745 : Real) / 1000000 * (1682209 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (1760928 : Real) / Real.log 2⌋₊ ≤ 20 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (1760928 : Real) < Real.log ((2 : Real) ^ 21) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 2) (r := 1326) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(1760928 : Real) ^ (1 / (2 : Real))⌋₊ = 1326 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((1760928 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (1326 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 3) (r := 120) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(1760928 : Real) ^ (1 / (3 : Real))⌋₊ = 120 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((1760928 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (120 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 4) (r := 36) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(1760928 : Real) ^ (1 / (4 : Real))⌋₊ = 36 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((1760928 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (36 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 5) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(1760928 : Real) ^ (1 / (5 : Real))⌋₊ = 17 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((1760928 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 6) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(1760928 : Real) ^ (1 / (6 : Real))⌋₊ = 10 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((1760928 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 7) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(1760928 : Real) ^ (1 / (7 : Real))⌋₊ = 7 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((1760928 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 8) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(1760928 : Real) ^ (1 / (8 : Real))⌋₊ = 6 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((1760928 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(1760928 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((1760928 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 10) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(1760928 : Real) ^ (1 / (10 : Real))⌋₊ = 4 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((1760928 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(1760928 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((1760928 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(1760928 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((1760928 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 13) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(1760928 : Real) ^ (1 / (13 : Real))⌋₊ = 3 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((1760928 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(1760928 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((1760928 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(1760928 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((1760928 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(1760928 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((1760928 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(1760928 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((1760928 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(1760928 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((1760928 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(1760928 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((1760928 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hroot_20 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 1760928) (k := 20) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_20' : ⌊(1760928 : Real) ^ (1 / (20 : Real))⌋₊ = 2 := by
    simpa using hroot_20
  have htheta_20 : Chebyshev.theta ((1760928 : Real) ^ (1 / (20 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_20']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (1760928 : Real)) =
      Chebyshev.theta (1326 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (1760928 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, htheta_20, hsqrt]
  rw [dusart_theta_nat_1326, dusart_theta_nat_120, dusart_theta_nat_36, dusart_theta_nat_17, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality

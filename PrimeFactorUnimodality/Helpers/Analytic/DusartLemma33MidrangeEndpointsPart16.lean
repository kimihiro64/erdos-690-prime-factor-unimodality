import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart15

/-! Generated endpoint proof shard 16 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_344569_361200 :
    Chebyshev.psi (361200 : Real) - Chebyshev.theta 361200 -
        Chebyshev.theta (Real.sqrt (361200 : Real)) <
      (1777745 : Real) / 1000000 * (344569 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (361200 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (361200 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 2) (r := 600) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(361200 : Real) ^ (1 / (2 : Real))⌋₊ = 600 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((361200 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (600 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 3) (r := 71) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(361200 : Real) ^ (1 / (3 : Real))⌋₊ = 71 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((361200 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (71 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 4) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(361200 : Real) ^ (1 / (4 : Real))⌋₊ = 24 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((361200 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 5) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(361200 : Real) ^ (1 / (5 : Real))⌋₊ = 12 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((361200 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(361200 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((361200 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(361200 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((361200 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(361200 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((361200 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(361200 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((361200 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(361200 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((361200 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(361200 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((361200 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(361200 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((361200 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(361200 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((361200 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(361200 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((361200 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(361200 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((361200 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(361200 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((361200 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(361200 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((361200 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 361200) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(361200 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((361200 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (361200 : Real)) =
      Chebyshev.theta (600 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (361200 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_600, dusart_theta_nat_71, dusart_theta_nat_24, dusart_theta_nat_12, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_361201_380688 :
    Chebyshev.psi (380688 : Real) - Chebyshev.theta 380688 -
        Chebyshev.theta (Real.sqrt (380688 : Real)) <
      (1777745 : Real) / 1000000 * (361201 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (380688 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (380688 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 2) (r := 616) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(380688 : Real) ^ (1 / (2 : Real))⌋₊ = 616 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((380688 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (616 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 3) (r := 72) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(380688 : Real) ^ (1 / (3 : Real))⌋₊ = 72 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((380688 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (72 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 4) (r := 24) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(380688 : Real) ^ (1 / (4 : Real))⌋₊ = 24 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((380688 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (24 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(380688 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((380688 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(380688 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((380688 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(380688 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((380688 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(380688 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((380688 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(380688 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((380688 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(380688 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((380688 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(380688 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((380688 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(380688 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((380688 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(380688 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((380688 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(380688 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((380688 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(380688 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((380688 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(380688 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((380688 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(380688 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((380688 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 380688) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(380688 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((380688 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (380688 : Real)) =
      Chebyshev.theta (616 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (380688 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_616, dusart_theta_nat_72, dusart_theta_nat_24, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_380689_398160 :
    Chebyshev.psi (398160 : Real) - Chebyshev.theta 398160 -
        Chebyshev.theta (Real.sqrt (398160 : Real)) <
      (1777745 : Real) / 1000000 * (380689 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (398160 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (398160 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 2) (r := 630) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(398160 : Real) ^ (1 / (2 : Real))⌋₊ = 630 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((398160 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (630 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 3) (r := 73) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(398160 : Real) ^ (1 / (3 : Real))⌋₊ = 73 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((398160 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (73 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 4) (r := 25) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(398160 : Real) ^ (1 / (4 : Real))⌋₊ = 25 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((398160 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (25 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(398160 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((398160 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(398160 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((398160 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(398160 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((398160 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(398160 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((398160 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(398160 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((398160 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(398160 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((398160 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(398160 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((398160 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(398160 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((398160 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(398160 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((398160 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(398160 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((398160 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(398160 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((398160 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(398160 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((398160 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(398160 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((398160 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 398160) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(398160 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((398160 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (398160 : Real)) =
      Chebyshev.theta (630 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (398160 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_630, dusart_theta_nat_73, dusart_theta_nat_25, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_398161_418608 :
    Chebyshev.psi (418608 : Real) - Chebyshev.theta 418608 -
        Chebyshev.theta (Real.sqrt (418608 : Real)) <
      (1777745 : Real) / 1000000 * (398161 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (418608 : Real) / Real.log 2⌋₊ ≤ 18 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (418608 : Real) < Real.log ((2 : Real) ^ 19) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 2) (r := 646) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(418608 : Real) ^ (1 / (2 : Real))⌋₊ = 646 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((418608 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (646 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 3) (r := 74) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(418608 : Real) ^ (1 / (3 : Real))⌋₊ = 74 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((418608 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (74 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 4) (r := 25) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(418608 : Real) ^ (1 / (4 : Real))⌋₊ = 25 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((418608 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (25 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 5) (r := 13) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(418608 : Real) ^ (1 / (5 : Real))⌋₊ = 13 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((418608 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (13 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 6) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(418608 : Real) ^ (1 / (6 : Real))⌋₊ = 8 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((418608 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(418608 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((418608 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(418608 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((418608 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(418608 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((418608 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(418608 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((418608 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(418608 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((418608 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(418608 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((418608 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(418608 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((418608 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(418608 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((418608 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(418608 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((418608 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(418608 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((418608 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(418608 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((418608 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 418608) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(418608 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((418608 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (418608 : Real)) =
      Chebyshev.theta (646 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (418608 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, hsqrt]
  rw [dusart_theta_nat_646, dusart_theta_nat_74, dusart_theta_nat_25, dusart_theta_nat_13, dusart_theta_nat_8, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality
